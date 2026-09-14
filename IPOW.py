#!/usr/bin/env python3
"""iPoW.ai 安卓专版 (全套功能：自动注册钱包 + 全网节点拉取 + 429换号续传)

【专为 Android (Termux) 深度定制】
1. **100% 纯 Python 3 标准库实现**：
   - 零外部依赖！无需 `pip install`，无需编译 Rust，无需 C 编译器（clang/gcc）。
   - 内置纯 Python Keccak-256、Secp256k1 椭圆曲线签名、AES-256-GCM 解密与 urllib 网络请求。
   - 手机只要装了 Termux + Python (`pkg install python`)，单文件拷贝进去直接跑！
2. **完整自动化流程**：
   - 自动获取全网 62 个节点目录；
   - 自动生成 Web3 钱包并完成 SIWE 注册与会话建立；
   - 逐个拉取并解密 VLESS-Reality 节点；
   - 遇到 HTTP 429 限流或 402 配额耗尽时，**自动光速注册新钱包并无缝续传**；
   - 自动智能跳过不可用死节点，避免换号后死循环；
3. **输出配置文件**（支持一键导入安卓各代理客户端）：
   - `all_nodes_vless.txt`：每行一条标准 vless:// 链接，直接批量复制导入 **v2rayNG** / **Shadowrocket**；
   - `clash_proxies.yaml`：Clash Meta / Mihomo 格式，导入 **Clash Verge** / **Clash Meta for Android**；
   - `singbox_outbounds.json`：Sing-box 出站配置；
   - `all_nodes.json`：节点全量元数据。

用法示例：
    python auto_register_android.py                       # 拉取全部节点
    python auto_register_android.py --limit 3             # 快速测试前 3 个节点
    python auto_register_android.py --wallets 5           # 最多使用 5 个钱包
    python auto_register_android.py --interval 2.0        # 请求间隔 2 秒
    python auto_register_android.py -o /sdcard/Download   # 直接输出到手机下载目录
    python auto_register_android.py -v                    # 详细日志
"""

import argparse
import base64
import json
import os
import random
import re
import ssl
import sys
import time
import urllib.error
import urllib.request

# ---------------------------------------------------------------------------
# 可选硬件加速检测（若装了库自动启用加速，若没装则完全走内置纯 Python 引擎）
# ---------------------------------------------------------------------------
try:
    import requests
    _HAS_REQUESTS = True
except ImportError:
    _HAS_REQUESTS = False

try:
    from eth_account import Account
    from eth_account.messages import encode_defunct
    _HAS_ETH_ACCOUNT = True
except ImportError:
    _HAS_ETH_ACCOUNT = False

try:
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    _HAS_CRYPTOGRAPHY = True
except ImportError:
    _HAS_CRYPTOGRAPHY = False

# ---------------------------------------------------------------------------
# 常量配置
# ---------------------------------------------------------------------------
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
API_BASE = 'https://ipow.ai'
USER_AGENT = 'Dart/3.10 (dart:io)'
CLIENT_TYPE = 'android'
CLIENT_VERSION = '4.3.4'
CAPABILITY = 'vless-reality:no-flow'
DEFAULT_SNI = 'www.cloudflare.com'
DEFAULT_FINGERPRINT = 'chrome'
MERGED_NODES_FILE = 'all_nodes.json'
WALLETS_FILE = 'auto_wallets.json'

# ---------------------------------------------------------------------------
# 异常定义
# ---------------------------------------------------------------------------
class IpowError(RuntimeError):
    def __init__(self, message, code=None):
        super().__init__(message)
        self.code = code

class QuotaExhausted(IpowError):
    def __init__(self, detail=''):
        super().__init__(
            '配额已耗尽 (402)' + ('：' + detail if detail else ''),
            code='quota_exhausted')

class RateLimited(IpowError):
    def __init__(self, retry_after, detail=''):
        self.retry_after = max(int(retry_after or 0), 1)
        super().__init__('服务端限流 (429)，需等待 {} 秒{}'.format(
            self.retry_after, '：' + detail if detail else ''))

# ---------------------------------------------------------------------------
# 内置纯 Python 密码学模块 (100% 标准库)
# ---------------------------------------------------------------------------

# 1. Keccak-256
def _keccak_256(data: bytes) -> bytes:
    state = [[0] * 5 for _ in range(5)]
    RC = [
        0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
        0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
        0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
        0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
        0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
        0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
    ]
    r_rot = [
        [0, 36, 3, 41, 18],
        [1, 44, 10, 45, 2],
        [62, 6, 43, 15, 61],
        [28, 55, 25, 21, 56],
        [27, 20, 39, 8, 14],
    ]
    rate = 136
    pad_len = rate - (len(data) % rate)
    padded = data + (b'\x81' if pad_len == 1 else b'\x01' + b'\x00' * (pad_len - 2) + b'\x80')

    def rotl64(x, n):
        return ((x << (n % 64)) | (x >> (64 - (n % 64)))) & 0xFFFFFFFFFFFFFFFF

    for offset in range(0, len(padded), rate):
        block = padded[offset:offset + rate]
        for i in range(17):
            val = int.from_bytes(block[i * 8:(i + 1) * 8], 'little')
            state[i % 5][i // 5] ^= val

        for round_idx in range(24):
            C = [state[x][0] ^ state[x][1] ^ state[x][2] ^ state[x][3] ^ state[x][4] for x in range(5)]
            D = [C[(x + 4) % 5] ^ rotl64(C[(x + 1) % 5], 1) for x in range(5)]
            for x in range(5):
                for y in range(5):
                    state[x][y] ^= D[x]

            B = [[0] * 5 for _ in range(5)]
            for x in range(5):
                for y in range(5):
                    B[y][(2 * x + 3 * y) % 5] = rotl64(state[x][y], r_rot[x][y])

            for x in range(5):
                for y in range(5):
                    state[x][y] = B[x][y] ^ ((~B[(x + 1) % 5][y]) & B[(x + 2) % 5][y])

            state[0][0] ^= RC[round_idx]

    out = bytearray()
    for y in range(5):
        for x in range(5):
            out.extend(state[x][y].to_bytes(8, 'little'))
            if len(out) >= 32:
                return bytes(out[:32])

# 2. Secp256k1 椭圆曲线与以太坊地址/签名
_SECP_P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
_SECP_Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
_SECP_Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
_SECP_G = (_SECP_Gx, _SECP_Gy)
_SECP_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

def _secp_inv(k, p):
    return pow(k, p - 2, p)

def _secp_point_add(p1, p2):
    if p1 is None: return p2
    if p2 is None: return p1
    x1, y1 = p1
    x2, y2 = p2
    if x1 == x2 and y1 != y2: return None
    if x1 == x2:
        m = (3 * x1 * x1) * _secp_inv(2 * y1, _SECP_P) % _SECP_P
    else:
        m = (y2 - y1) * _secp_inv(x2 - x1, _SECP_P) % _SECP_P
    x3 = (m * m - x1 - x2) % _SECP_P
    y3 = (m * (x1 - x3) - y1) % _SECP_P
    return (x3, y3)

def _secp_point_mul(k, p):
    res = None
    cur = p
    while k > 0:
        if k & 1: res = _secp_point_add(res, cur)
        cur = _secp_point_add(cur, cur)
        k >>= 1
    return res

def _pure_private_key_to_address(privkey_bytes: bytes) -> str:
    d = int.from_bytes(privkey_bytes, 'big')
    pub = _secp_point_mul(d, _SECP_G)
    pub_bytes = pub[0].to_bytes(32, 'big') + pub[1].to_bytes(32, 'big')
    addr_hex = _keccak_256(pub_bytes)[12:].hex().lower()
    h = _keccak_256(addr_hex.encode('ascii')).hex()
    res = [c.upper() if int(h[i], 16) >= 8 else c for i, c in enumerate(addr_hex)]
    return '0x' + ''.join(res)

def _pure_sign_personal_message(privkey_hex: str, message_str: str) -> str:
    raw_hex = privkey_hex[2:] if privkey_hex.startswith('0x') else privkey_hex
    privkey_bytes = bytes.fromhex(raw_hex)
    msg_bytes = message_str.encode('utf-8')
    prefix = f'\x19Ethereum Signed Message:\n{len(msg_bytes)}'.encode('ascii')
    z = int.from_bytes(_keccak_256(prefix + msg_bytes), 'big')
    d = int.from_bytes(privkey_bytes, 'big')

    while True:
        k = random.SystemRandom().randint(1, _SECP_N - 1)
        r_point = _secp_point_mul(k, _SECP_G)
        r = r_point[0] % _SECP_N
        if r == 0: continue
        s = (_secp_inv(k, _SECP_N) * (z + r * d)) % _SECP_N
        if s == 0: continue
        v = 27 + (r_point[1] % 2)
        if s > _SECP_N // 2:
            s = _SECP_N - s
            v = 27 + (1 - (r_point[1] % 2))
        break

    return '0x' + r.to_bytes(32, 'big').hex() + s.to_bytes(32, 'big').hex() + bytes([v]).hex()

# 3. 纯 Python AES-256-GCM 解密
_AES_SBOX = [
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16
]
_AES_RCON = [0x00, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36]

def _aes_key_expansion(key: bytes):
    nk = len(key) // 4
    nr = nk + 6
    w = [[key[4*i], key[4*i+1], key[4*i+2], key[4*i+3]] for i in range(nk)]
    for i in range(nk, 4 * (nr + 1)):
        temp = list(w[i - 1])
        if i % nk == 0:
            temp = temp[1:] + temp[:1]
            temp = [_AES_SBOX[b] for b in temp]
            temp[0] ^= _AES_RCON[i // nk]
        elif nk > 6 and (i % nk == 4):
            temp = [_AES_SBOX[b] for b in temp]
        w.append([a ^ b for a, b in zip(w[i - nk], temp)])
    return w, nr

def _aes_xtime(a):
    return ((a << 1) ^ 0x1B) & 0xFF if (a & 0x80) else (a << 1)

def _aes_encrypt_block(block: bytes, w, nr: int) -> bytes:
    state = [[block[r + 4*c] for c in range(4)] for r in range(4)]
    for c in range(4):
        for r in range(4):
            state[r][c] ^= w[c][r]

    for round_num in range(1, nr):
        for r in range(4):
            for c in range(4):
                state[r][c] = _AES_SBOX[state[r][c]]
        state[1] = state[1][1:] + state[1][:1]
        state[2] = state[2][2:] + state[2][:2]
        state[3] = state[3][3:] + state[3][:3]
        for c in range(4):
            s0, s1, s2, s3 = state[0][c], state[1][c], state[2][c], state[3][c]
            state[0][c] = _aes_xtime(s0 ^ s1) ^ s1 ^ s2 ^ s3
            state[1][c] = _aes_xtime(s1 ^ s2) ^ s2 ^ s3 ^ s0
            state[2][c] = _aes_xtime(s2 ^ s3) ^ s3 ^ s0 ^ s1
            state[3][c] = _aes_xtime(s3 ^ s0) ^ s0 ^ s1 ^ s2
        for c in range(4):
            for r in range(4):
                state[r][c] ^= w[round_num * 4 + c][r]

    for r in range(4):
        for c in range(4):
            state[r][c] = _AES_SBOX[state[r][c]]
    state[1] = state[1][1:] + state[1][:1]
    state[2] = state[2][2:] + state[2][:2]
    state[3] = state[3][3:] + state[3][:3]
    for c in range(4):
        for r in range(4):
            state[r][c] ^= w[nr * 4 + c][r]

    out = bytearray(16)
    for c in range(4):
        for r in range(4):
            out[r + 4*c] = state[r][c]
    return bytes(out)

def _ghash(h_bytes, data):
    h = int.from_bytes(h_bytes, 'big')
    r = 0xE1000000000000000000000000000000
    y = 0
    for i in range(0, len(data), 16):
        x = int.from_bytes(data[i:i+16], 'big')
        v = y ^ x
        z = 0
        for bit in range(128):
            if (h >> (127 - bit)) & 1:
                z ^= v
            if v & 1:
                v = (v >> 1) ^ r
            else:
                v >>= 1
        y = z
    return y.to_bytes(16, 'big')

def _pure_aes_gcm_decrypt(key: bytes, nonce: bytes, ct_and_tag: bytes, aad: bytes = b'') -> bytes:
    if len(nonce) != 12:
        raise ValueError('Nonce 长度必须为 12 字节')
    if len(ct_and_tag) < 16:
        raise ValueError('密文长度不足（缺少 Tag）')
    ct = ct_and_tag[:-16]
    expected_tag = ct_and_tag[-16:]

    w, nr = _aes_key_expansion(key)
    h_bytes = _aes_encrypt_block(b'\x00' * 16, w, nr)

    j0 = nonce + b'\x00\x00\x00\x01'
    j0_enc = _aes_encrypt_block(j0, w, nr)

    pad_aad = aad + b'\x00' * (-len(aad) % 16)
    pad_ct = ct + b'\x00' * (-len(ct) % 16)
    len_blk = (len(aad) * 8).to_bytes(8, 'big') + (len(ct) * 8).to_bytes(8, 'big')
    ghash_data = pad_aad + pad_ct + len_blk

    ghash_out = _ghash(h_bytes, ghash_data)
    computed_tag = bytes(a ^ b for a, b in zip(ghash_out, j0_enc))
    if computed_tag != expected_tag:
        raise ValueError('GCM 校验标签不匹配')

    counter = 2
    pt = bytearray()
    for i in range(0, len(ct), 16):
        cb = nonce + counter.to_bytes(4, 'big')
        ks = _aes_encrypt_block(cb, w, nr)
        block = ct[i:i+16]
        pt.extend(bytes(a ^ b for a, b in zip(block, ks[:len(block)])))
        counter += 1
    return bytes(pt)

# ---------------------------------------------------------------------------
# 基础工具函数
# ---------------------------------------------------------------------------

def b64d(s):
    s = s.replace('-', '+').replace('_', '/')
    return base64.b64decode(s + '=' * (-len(s) % 4))


def country_code_from_node_id(node_id):
    m = re.search(r'-([a-z]{2})-\d+$', node_id or '')
    return m.group(1).upper() if m else None


def get_default_download_dir():
    """获取系统默认下载目录（安卓上自动使用 /sdcard/Download，电脑上使用用户下载文件夹）"""
    # 1. Windows 平台
    if os.name == 'nt':
        win_dl = os.path.join(os.path.expanduser('~'), 'Downloads')
        if os.path.isdir(win_dl):
            return win_dl
        return BASE_DIR

    # 2. Android (Termux) 平台优先检测
    android_paths = [
        '/sdcard/Download',
        '/storage/emulated/0/Download',
        os.path.expanduser('~/storage/downloads'),
    ]
    for p in android_paths:
        if os.path.isdir(p) and os.access(p, os.W_OK):
            return p

    # 尝试创建 /sdcard/Download
    for parent in ['/sdcard', '/storage/emulated/0']:
        if os.path.isdir(parent):
            target = os.path.join(parent, 'Download')
            try:
                os.makedirs(target, exist_ok=True)
                if os.access(target, os.W_OK):
                    return target
            except Exception:
                pass

    # 3. Linux / macOS 桌面平台
    user_dl = os.path.join(os.path.expanduser('~'), 'Downloads')
    if os.path.isdir(user_dl) and os.access(user_dl, os.W_OK):
        return user_dl

    # 4. 回退到脚本自身所在目录
    return BASE_DIR


def write_json(path, obj):
    os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
    tmp = path + '.tmp'
    with open(tmp, 'w', encoding='utf-8', newline='\n') as f:
        json.dump(obj, f, indent=2, ensure_ascii=False)
        f.write('\n')
    os.replace(tmp, path)

# ---------------------------------------------------------------------------
# 网络客户端
# ---------------------------------------------------------------------------

class IpowClient:
    def __init__(self, base=API_BASE, timeout=20, verbose=False):
        self.base = base.rstrip('/')
        self.timeout = timeout
        self.verbose = verbose
        if _HAS_REQUESTS:
            self.session = requests.Session()
            self.session.headers.update({
                'User-Agent': USER_AGENT,
                'Content-Type': 'application/json',
                'Accept': 'application/json',
            })
        else:
            self.session = None
            try:
                self.ssl_ctx = ssl.create_default_context()
            except Exception:
                self.ssl_ctx = ssl._create_unverified_context()

    def _request(self, method, path, body=None, token=None):
        url = self.base + path
        if self.verbose:
            shown = json.dumps(body, ensure_ascii=False)[:160] if body else ''
            print('  -> {} {} {}'.format(method, path, shown))

        if self.session is not None:
            headers = {'Authorization': 'Bearer ' + token} if token else {}
            r = self.session.request(method, url, json=body, headers=headers,
                                     timeout=self.timeout)
            status_code = r.status_code
            resp_headers = r.headers
            resp_text = r.text
        else:
            headers = {
                'User-Agent': USER_AGENT,
                'Content-Type': 'application/json',
                'Accept': 'application/json',
            }
            if token:
                headers['Authorization'] = 'Bearer ' + token
            data = json.dumps(body).encode('utf-8') if body is not None else None
            req = urllib.request.Request(url, data=data, headers=headers, method=method)
            try:
                with urllib.request.urlopen(req, timeout=self.timeout, context=self.ssl_ctx) as resp:
                    status_code = resp.status
                    resp_headers = resp.headers
                    resp_text = resp.read().decode('utf-8', errors='replace')
            except urllib.error.HTTPError as err:
                status_code = err.code
                resp_headers = err.headers
                resp_text = err.read().decode('utf-8', errors='replace')
            except Exception as err:
                raise IpowError(f'网络请求失败 ({method} {path}): {err}')

        if self.verbose:
            print('  <- {} {}'.format(status_code, resp_text[:160]))

        if status_code == 429:
            raw = resp_headers.get('Retry-After') or resp_headers.get('retry-after')
            try:
                retry_after = int(float(raw))
            except (TypeError, ValueError):
                retry_after = 30
            raise RateLimited(retry_after, resp_text[:120])
        if status_code == 401:
            raise IpowError('JWT 已失效 (401)')
        if status_code == 402:
            raise QuotaExhausted(resp_text[:160])
        if status_code >= 400:
            code = None
            try:
                code = (json.loads(resp_text).get('error') or {}).get('code')
            except Exception:
                pass
            raise IpowError('HTTP {} {}: {}'.format(
                status_code, path, resp_text[:300]), code=code)

        try:
            return json.loads(resp_text)
        except Exception:
            raise IpowError('响应不是 JSON: ' + resp_text[:200])

    def challenge(self, address):
        return self._request('POST', '/v1/auth/wallet/challenge',
                             {'address': address})

    def verify(self, address, signature, nonce, device_id, device_name):
        return self._request('POST', '/v1/auth/wallet/verify', {
            'address': address,
            'signature': signature,
            'nonce': nonce,
            'device_id': device_id,
            'device_name': device_name,
            'client_type': CLIENT_TYPE,
        })

    def session_start(self, token, device_id, device_name):
        return self._request('POST', '/p2p-lite/v2/vpn/sessions/start', {
            'client_type': CLIENT_TYPE,
            'device_id': device_id,
            'device_name': device_name,
            'client_version': CLIENT_VERSION,
            'preferred_country': 'AUTO',
        }, token=token)

    def capability(self, token, session_id, country, subscription_token,
                   device_id, node_id=None):
        body = {
            'session_id': session_id,
            'client_type': CLIENT_TYPE,
            'device_id': device_id,
            'country': country,
            'capabilities': [CAPABILITY],
            'subscription_token': subscription_token,
            'allow_country_switch': True,
        }
        if node_id:
            body['node_id'] = node_id
        return self._request('POST', '/p2p-lite/v2/dht/capability',
                             body, token=token)

# ---------------------------------------------------------------------------
# 解密与配置生成
# ---------------------------------------------------------------------------

def node_name(node):
    return "iPoW-{}-{}".format(node.get('country_code', 'XX'), node['node_id'])


def build_vless_url(node):
    name = node_name(node)
    fp = node.get('fingerprint') or DEFAULT_FINGERPRINT
    parts = [
        'encryption=none',
        'flow=',
        'security=reality',
        'sni={}'.format(node.get('sni') or DEFAULT_SNI),
        'fp={}'.format(fp),
        'pbk={}'.format(node['public_key']),
        'sid={}'.format(node['short_id']),
        'type=tcp',
    ]
    return 'vless://{}@{}:{}?{}#{}'.format(
        node['uuid'], node['server'], node['port'], '&'.join(parts), name)


def build_clash_yaml(nodes):
    lines = [
        '# Clash Meta / Mihomo Proxies Configuration',
        'proxies:',
    ]
    for n in nodes:
        lines.append("  - name: '{}'".format(node_name(n)))
        lines.append('    type: vless')
        lines.append('    server: {}'.format(n['server']))
        lines.append('    port: {}'.format(n['port']))
        lines.append('    uuid: {}'.format(n['uuid']))
        lines.append('    network: tcp')
        lines.append('    tls: true')
        lines.append('    udp: true')
        lines.append('    servername: {}'.format(n.get('sni') or DEFAULT_SNI))
        lines.append('    client-fingerprint: {}'.format(
            n.get('fingerprint') or DEFAULT_FINGERPRINT))
        lines.append('    reality-opts:')
        lines.append("      public-key: '{}'".format(n['public_key']))
        lines.append("      short-id: '{}'".format(n['short_id']))
    return '\n'.join(lines)


def build_singbox_json(nodes):
    outbounds = []
    for n in nodes:
        outbounds.append({
            'type': 'vless',
            'tag': node_name(n),
            'server': n['server'],
            'server_port': n['port'],
            'uuid': n['uuid'],
            'packet_encoding': 'xudp',
            'tls': {
                'enabled': True,
                'server_name': n.get('sni') or DEFAULT_SNI,
                'utls': {
                    'enabled': True,
                    'fingerprint': n.get('fingerprint') or DEFAULT_FINGERPRINT,
                },
                'reality': {
                    'enabled': True,
                    'public_key': n['public_key'],
                    'short_id': n['short_id'],
                },
            },
        })
    return {'outbounds': outbounds}


def write_configs(nodes, work_dir, quiet=False):
    os.makedirs(work_dir, exist_ok=True)
    nodes = [
        dict(n, vless_url=n.get('vless_url') or build_vless_url(n))
        for n in nodes
    ]
    paths = {
        'json': os.path.join(work_dir, MERGED_NODES_FILE),
        'vless': os.path.join(work_dir, 'all_nodes_vless.txt'),
        'clash': os.path.join(work_dir, 'clash_proxies.yaml'),
        'singbox': os.path.join(work_dir, 'singbox_outbounds.json'),
    }
    with open(paths['json'], 'w', encoding='utf-8', newline='\n') as f:
        f.write(json.dumps(nodes, indent=2, ensure_ascii=False) + '\n')
    with open(paths['vless'], 'w', encoding='utf-8', newline='\n') as f:
        f.write('\n'.join(n['vless_url'] for n in nodes) + '\n')
    with open(paths['clash'], 'w', encoding='utf-8', newline='\n') as f:
        f.write(build_clash_yaml(nodes) + '\n')
    with open(paths['singbox'], 'w', encoding='utf-8', newline='\n') as f:
        f.write(json.dumps(build_singbox_json(nodes), indent=2,
                            ensure_ascii=False) + '\n')
    if not quiet:
        print('\n' + '=' * 60)
        print('🎉 节点配置已成功生成到:')
        for k, p in paths.items():
            print('  {:8s} -> {}'.format(k.upper(), p))
        print('=' * 60)
    return paths


def decrypt_profile(resp):
    ep = resp.get('encrypted_profile')
    if not ep:
        raise IpowError('响应里没有 encrypted_profile')
    keys = {k.get('key_id'): k.get('key')
            for k in (resp.get('profile_decryption_keys') or [])}
    key_str = keys.get(ep.get('key_id')) or resp.get('profile_decryption_key')
    if not key_str:
        raise IpowError('响应里没有可用的 profile 解密密钥')

    key_bytes = b64d(key_str)
    nonce_bytes = b64d(ep['nonce'])
    ct_bytes = b64d(ep['ciphertext'])

    if _HAS_CRYPTOGRAPHY:
        plaintext = AESGCM(key_bytes).decrypt(nonce_bytes, ct_bytes, None)
    else:
        plaintext = _pure_aes_gcm_decrypt(key_bytes, nonce_bytes, ct_bytes, b'')

    return json.loads(plaintext.decode('utf-8', errors='replace'))


def node_from_capability(resp):
    profile = decrypt_profile(resp)
    payload = (resp.get('signed_record') or {}).get('payload') or {}
    tls = profile.get('tls') or {}
    reality = tls.get('reality') or {}
    node_id = (resp.get('selected_node_id') or resp.get('node_id')
               or payload.get('node_id'))
    node = {
        'node_id': node_id,
        'country': resp.get('selected_country_name') or payload.get('country'),
        'country_code': (resp.get('selected_country_code')
                         or country_code_from_node_id(node_id)),
        'city': payload.get('city'),
        'server': profile.get('server'),
        'port': profile.get('server_port'),
        'uuid': profile.get('uuid'),
        'sni': tls.get('server_name'),
        'public_key': reality.get('public_key'),
        'short_id': reality.get('short_id'),
        'vless_url': None,
        'region': payload.get('region'),
        'latency_ms': payload.get('latency_ms'),
    }
    for field in ('node_id', 'server', 'port', 'uuid', 'public_key', 'short_id'):
        if not node.get(field):
            raise IpowError('解出的节点缺少字段 {}: {}'.format(field, node))
    node['vless_url'] = build_vless_url(node)
    return node

# ---------------------------------------------------------------------------
# 钱包生成与注册
# ---------------------------------------------------------------------------

def generate_wallet():
    if _HAS_ETH_ACCOUNT:
        account = Account.create()
        return '0x' + account.key.hex(), account.address
    priv = os.urandom(32)
    address = _pure_private_key_to_address(priv)
    return '0x' + priv.hex(), address


def sign_login_message(pk, message):
    if _HAS_ETH_ACCOUNT:
        account = Account.from_key(pk)
        signed = account.sign_message(encode_defunct(text=message))
        return '0x' + bytes(signed.signature).hex()
    return _pure_sign_personal_message(pk, message)


def random_device_id():
    return ''.join(random.choices('0123456789abcdef', k=16))


def random_device_name():
    brands = ['Xiaomi', 'Redmi', 'Huawei', 'Honor', 'Samsung', 'Vivo', 'iQOO', 'Oppo', 'OnePlus']
    return '{} {}'.format(random.choice(brands), random.randint(1000, 9999))


def register_new_wallet(client, verbose=False):
    pk, address = generate_wallet()
    device_id = random_device_id()
    device_name = random_device_name()

    if verbose:
        print(f'  新钱包: {address}')
        print(f'  设备ID: {device_id} ({device_name})')

    ch = client.challenge(address)
    message = ch.get('message') or ch.get('nonce')
    if not message:
        raise IpowError(f'challenge 缺少 message: {ch}')

    signature = sign_login_message(pk, message)

    res = client.verify(address, signature, ch.get('nonce'),
                        device_id, device_name)

    sub = res.get('subscription') or {}
    state = {
        'private_key': pk,
        'address': address.lower(),
        'jwt': res.get('token'),
        'user_id': sub.get('user_id'),
        'subscription_token': sub.get('token'),
        'subscription_url': sub.get('url'),
        'plan_id': sub.get('plan_id'),
        'expires_at': sub.get('expires_at'),
        'device_id': device_id,
        'device_name': device_name,
    }

    if res.get('is_new_user'):
        if verbose:
            print('  ✅ 新账号已创建')
    else:
        if verbose:
            print('  ⚡ 已有钱包，复用登录')

    return state

# ---------------------------------------------------------------------------
# 从单个钱包拉取节点
# ---------------------------------------------------------------------------

def pull_with_wallet(client, state, session_id, device_id, args, remaining_ids):
    nodes = []
    pulled = []
    unusable = set()
    token = state['jwt']
    sub_token = state.get('subscription_token')

    batch = remaining_ids[:args.batch_size]
    total = len(batch)
    print(f'  逐个拉取 {total} 个节点...')

    for idx, (node_id, country) in enumerate(batch):
        if idx:
            time.sleep(args.interval)

        print(f'    [{idx+1}/{total}] {node_id} ...', end=' ', flush=True)

        try:
            resp = client.capability(
                token, session_id, country, sub_token, device_id,
                node_id=node_id)
        except RateLimited as exc:
            print(f'429 限流! (需等待 {exc.retry_after}s) → 自动换号')
            return nodes, True, pulled, unusable
        except QuotaExhausted:
            print('402 配额耗尽! → 自动换号')
            return nodes, True, pulled, unusable
        except IpowError as exc:
            code = getattr(exc, 'code', None)
            if code in ('p2p_dht_capability_unavailable',
                        'p2p_lite_country_mismatch'):
                print('暂不可用（跳过）')
                unusable.add(node_id)
            else:
                print(f'失败: {exc}')
                unusable.add(node_id)
            continue

        got = resp.get('selected_node_id') or resp.get('node_id')
        if got != node_id:
            print(f'未命中({got})')
            unusable.add(node_id)
            continue

        try:
            node = node_from_capability(resp)
        except IpowError as exc:
            print(f'解密失败: {exc}')
            unusable.add(node_id)
            continue

        nodes.append(node)
        pulled.append((node_id, country))
        print(f'{node["server"]} | {node.get("latency_ms", "-")}ms')

    return nodes, False, pulled, unusable

# ---------------------------------------------------------------------------
# 合并去重
# ---------------------------------------------------------------------------

def merge_nodes(existing, new_nodes):
    by_id = {n['node_id']: n for n in existing}
    added = 0
    for n in new_nodes:
        nid = n.get('node_id')
        if nid and nid not in by_id:
            added += 1
        if nid:
            by_id[nid] = n
    return list(by_id.values()), added

# ---------------------------------------------------------------------------
# 主流程入口
# ---------------------------------------------------------------------------

def main(argv=None):
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, 'reconfigure'):
            stream.reconfigure(encoding='utf-8', errors='replace')

    default_dir = get_default_download_dir()

    ap = argparse.ArgumentParser(
        prog='auto_register_android.py',
        description='iPoW.ai 安卓专版：自动注册 + 全网节点拉取 + 429换号续传')
    ap.add_argument('--interval', type=float, default=2.0,
                    help='每次请求间隔秒数，默认 %(default)s')
    ap.add_argument('--wallets', type=int, default=10,
                    help='最多使用多少个钱包，默认 %(default)s')
    ap.add_argument('--limit', type=int, default=None,
                    help='限制总拉取节点数（默认全部）')
    ap.add_argument('--batch-size', type=int, default=62,
                    help='每个钱包拉取的最大节点数，默认 %(default)s')
    ap.add_argument('--base-url', default=API_BASE,
                    help='接口地址，默认 %(default)s')
    ap.add_argument('-o', '--out-dir', default=default_dir,
                    help='输出文件目录，默认保存在系统下载目录: %(default)s')
    ap.add_argument('-v', '--verbose', action='store_true',
                    help='详细输出')
    ap.add_argument('--quiet', action='store_true',
                    help='只输出最终结果')
    args = ap.parse_args(argv)

    out_dir = os.path.abspath(args.out_dir) if args.out_dir else default_dir

    # 检查并测试输出目录写入权限
    try:
        os.makedirs(out_dir, exist_ok=True)
        test_perm_file = os.path.join(out_dir, '.perm_test')
        with open(test_perm_file, 'w') as f:
            f.write('ok')
        os.remove(test_perm_file)
    except Exception as exc:
        print(f'⚠️ 提示: 默认输出目录不可写: {out_dir}')
        if '/sdcard' in out_dir or 'storage' in out_dir:
            print('💡 安卓 Termux 提示: 访问系统下载目录需要授权，可在 Termux 终端运行:')
            print('   termux-setup-storage')
            print('   并在系统弹窗中点击“允许”。')
        out_dir = os.getcwd()
        print(f'   已自动改用当前脚本工作目录: {out_dir}')

    if not args.quiet:
        print('=' * 60)
        print('  iPoW.ai 全网节点自动拉取 (Android 独立单文件版)')
        print('=' * 60)
        engine_str = "内置纯 Python 引擎 (Termux 零依赖)" if not (_HAS_ETH_ACCOUNT and _HAS_CRYPTOGRAPHY) else "硬件加速引擎"
        print(f'运行环境: {engine_str}')
        print(f'保存目录: {out_dir}')
        print('=' * 60)

    client = IpowClient(base=args.base_url, verbose=args.verbose)

    all_nodes = []
    seen_ids = set()
    unusable_ids = set()

    # 从 API 获取全网节点目录
    print('正在获取全网节点目录...')
    try:
        cat_body = client._request('GET', '/p2p-lite/v1/nodes?redacted=1')
    except IpowError:
        cat_body = client._request('GET', '/p2p-lite/v1/nodes')

    entries = cat_body.get('nodes') or cat_body.get('entries') or []
    if not entries:
        print('错误: 服务端未返回任何节点')
        return 1

    all_ids = [(e.get('id') or e.get('node_id'), e.get('country_code', 'AUTO'))
               for e in entries if e.get('id') or e.get('node_id')]
    target = args.limit or len(all_ids)
    remaining = all_ids[:target]

    print(f'目标节点: {target} 个')

    wallets_used = []

    while remaining:
        wallet_idx = len(wallets_used) + 1
        print(f'\n{"─" * 50}')
        print(f'钱包 #{wallet_idx} | 待拉取 {len(remaining)} 个节点')

        # 1) 自动注册新钱包
        try:
            state = register_new_wallet(client, verbose=args.verbose)
            wallets_used.append({
                'address': state['address'],
                'user_id': state['user_id'],
                'plan_id': state['plan_id'],
            })
            print(f'  新钱包: {state["address"]} (用户: {state["user_id"]})')
        except IpowError as exc:
            print(f'  ❌ 注册失败: {exc}')
            break
        except Exception as exc:
            print(f'  ❌ 注册异常: {exc}')
            break

        if len(wallets_used) > args.wallets:
            print(f'\n已达钱包上限 {args.wallets}')
            break

        # 2) 开启会话
        try:
            token = state['jwt']
            device_id = state['device_id']
            device_name = state['device_name']
            session = client.session_start(token, device_id, device_name)
            session_id = (session.get('session') or {}).get('id')
            if not session_id:
                print('  ❌ sessions/start 无 session_id')
                continue
            if not args.quiet:
                print(f'  建立会话: {session_id}')
        except IpowError as exc:
            print(f'  ❌ 开启会话失败: {exc}')
            continue

        # 3) 拉取节点
        try:
            nodes, rate_limited, pulled, new_unusable = pull_with_wallet(
                client, state, session_id, device_id, args, remaining)
            unusable_ids.update(new_unusable)
        except Exception as exc:
            print(f'  ❌ 拉取异常: {exc}')
            continue

        # 4) 合并去重与实时落盘
        if nodes:
            all_nodes, added = merge_nodes(all_nodes, nodes)
            for n in nodes:
                nid = n.get('node_id')
                if nid:
                    seen_ids.add(nid)

            print(f'  ✅ 本批拉到 {len(nodes)} 个（总累计 {len(all_nodes)} 个）')
            write_json(os.path.join(out_dir, MERGED_NODES_FILE), all_nodes)
        else:
            print('  ⚠️  本批未拉到可用节点')

        # 过滤剩余节点（排除已成功的和已确认不可用的节点）
        remaining = [(nid, cc) for nid, cc in remaining
                     if nid not in seen_ids and nid not in unusable_ids]

        # 5) 429 限流或 402 配额耗尽时自动换钱包继续
        if rate_limited:
            if remaining:
                print(f'  🔄 触发换号 → 自动注册新钱包继续拉取剩余 {len(remaining)} 个')
                time.sleep(1)
                continue
            else:
                break

        if remaining:
            time.sleep(args.interval)

    # 保存钱包记录
    write_json(os.path.join(out_dir, WALLETS_FILE), wallets_used)

    # 写出全部配置文件
    if all_nodes:
        write_configs(all_nodes, out_dir, quiet=args.quiet)

    # 汇总输出
    print(f'\n{"=" * 60}')
    print('【全网节点拉取汇总】')
    print(f'  使用钱包数: {len(wallets_used)} 个')
    print(f'  有效节点数: {len(all_nodes)} 个')

    countries = {}
    for n in all_nodes:
        cc = n.get('country_code', '?')
        countries[cc] = countries.get(cc, 0) + 1
    if countries:
        print(f'  覆盖国家/地区: {len(countries)} 个')
        for cc in sorted(countries):
            print(f'    - {cc}: {countries[cc]} 个节点')

    print('=' * 60)
    print(f'💡 安卓导入提示:')
    print(f'  - v2rayNG: 复制 {os.path.join(out_dir, "all_nodes_vless.txt")} 内容，打开 App 选择“从剪贴板导入”')
    print(f'  - Clash Meta: 打开 App 配置页面，直接选择导入本地文件 {os.path.join(out_dir, "clash_proxies.yaml")}')
    print('=' * 60)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
