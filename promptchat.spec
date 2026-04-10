# -*- mode: python ; coding: utf-8 -*-

import sys
import os
import certifi
from PyInstaller.utils.hooks import collect_all

block_cipher = None

cert_path = certifi.where()

# --- Resolve OpenCL.dll path ---
opencl_candidates = [
    os.path.join(os.environ.get("WINDIR", r"C:\Windows"), "System32", "OpenCL.dll"),
    os.path.join(os.environ.get("WINDIR", r"C:\Windows"), "SysWOW64", "OpenCL.dll"),
    os.path.join(os.getcwd(), "OpenCL.dll"),
]

opencl_path = None
for candidate in opencl_candidates:
    if os.path.exists(candidate):
        opencl_path = candidate
        break

if opencl_path is None:
    raise FileNotFoundError(
        "Could not find OpenCL.dll. Checked:\n" + "\n".join(opencl_candidates)
    )

datas = [
    ('blocknet_client.py', '.'),
    ('gui_presets.json', '.'),
    ('.env', '.'),
    ('blocks.py', '.'),
    ('gui_elements.py', '.'),
    ('main.py', '.'),
    ('models.py', '.'),
    ('pipeline.py', '.'),
    ('registry.py', '.'),
    ('subblocks.py', '.'),
    ('submanagers.py', '.'),
    ('stores.py', '.'),
    ('loggers.py', '.'),
    ('libpcap_backend.py', '.'),
    (cert_path, 'certifi'),
]

binaries = [
    (opencl_path, '.'),
]

hiddenimports = [
    'PyQt5.sip',
    'requests',
    'aiohttp',
    'bs4',
    'feedparser',
    'trafilatura',
    'duckduckgo_search',
    'curl_cffi',
    'googletrans',
    'playwright',
    'playwright.async_api',
    'playwright.sync_api',
    'numpy',
    'sqlite3',
    'certifi',
    'json',
    'logging',
]

# Collect Playwright (Node drivers)
tmp_ret = collect_all('playwright')
datas += tmp_ret[0]
binaries += tmp_ret[1]
hiddenimports += tmp_ret[2]

# Collect DuckDuckGo Search
tmp_ret = collect_all('ddgs')
datas += tmp_ret[0]
binaries += tmp_ret[1]
hiddenimports += tmp_ret[2]

# Collect curl_cffi
tmp_ret = collect_all('curl_cffi')
datas += tmp_ret[0]
binaries += tmp_ret[1]
hiddenimports += tmp_ret[2]

# Collect Certifi
tmp_ret = collect_all('certifi')
datas += tmp_ret[0]
binaries += tmp_ret[1]
hiddenimports += tmp_ret[2]

# Collect Trafilatura
tmp_ret = collect_all('trafilatura')
datas += tmp_ret[0]
binaries += tmp_ret[1]
hiddenimports += tmp_ret[2]

# --- Bundle browserforge, language_tags, camoufox data ---
bf_datas, bf_binaries, bf_hidden = collect_all("browserforge")
lt_datas, lt_binaries, lt_hidden = collect_all("language_tags")
cf_datas, cf_binaries, cf_hidden = collect_all("camoufox")

datas += bf_datas + lt_datas + cf_datas
binaries += bf_binaries + lt_binaries + cf_binaries
hiddenimports += bf_hidden + lt_hidden + cf_hidden

a = Analysis(
    ['gui.py'],
    pathex=[],
    binaries=binaries,
    datas=datas,
    hiddenimports=hiddenimports,
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=[],
    win_no_prefer_redirects=False,
    win_private_assemblies=False,
    cipher=block_cipher,
    noarchive=False,
)

pyz = PYZ(a.pure, a.zipped_data, cipher=block_cipher)

exe = EXE(
    pyz,
    a.scripts,
    a.binaries,
    a.zipfiles,
    a.datas,
    [],
    name='PromptChat',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    console=True,
    disable_windowed_traceback=False,
    argv_emulation=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
    exclude_binaries=False,
)