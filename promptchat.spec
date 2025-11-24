# -*- mode: python ; coding: utf-8 -*-
import sys
import os
import certifi
from PyInstaller.utils.hooks import collect_all

block_cipher = None

# --- 1. Setup SSL Certificates ---
# We bundle this into 'certifi' directory so it matches standard python pathing
cert_path = certifi.where()

# --- 2. Define Data Files ---
datas = [
    # Configuration & Databases
    ('gui_presets.json', '.'),
    ('.env', '.'),
    ('code_corpus.db', '.'),
    ('link_corpus.db', '.'),
    ('webcorpus.db', '.'),

    # Bundle Source Files (Required because your app reads them as text/AST)
    ('blocks.py', '.'),
    ('gui_elements.py', '.'),
    ('main.py', '.'),
    ('models.py', '.'),
    ('pipeline.py', '.'),
    ('registry.py', '.'),
    ('subblocks.py', '.'),
    ('submanagers.py', '.'),

    # Bundle SSL Certs into 'certifi' folder
    (cert_path, 'certifi'),
]

binaries = []

# --- 3. Define Hidden Imports ---
hiddenimports = [
    'PyQt5.sip',
    'requests',
    'aiohttp',
    'bs4',
    'feedparser',
    'trafilatura',
    'duckduckgo_search',
    'curl_cffi',        # Engine for DDGS
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

# --- 4. Collect Complex Libraries ---

# Collect Playwright (Node drivers)
tmp_ret = collect_all('playwright')
datas += tmp_ret[0]; binaries += tmp_ret[1]; hiddenimports += tmp_ret[2]

# Collect DuckDuckGo Search
tmp_ret = collect_all('ddgs')
datas += tmp_ret[0]; binaries += tmp_ret[1]; hiddenimports += tmp_ret[2]

# Collect curl_cffi (CRITICAL: Has binaries)
tmp_ret = collect_all('curl_cffi')
datas += tmp_ret[0]; binaries += tmp_ret[1]; hiddenimports += tmp_ret[2]

# Collect Certifi (Ensures internal logic finds certs)
tmp_ret = collect_all('certifi')
datas += tmp_ret[0]; binaries += tmp_ret[1]; hiddenimports += tmp_ret[2]

# Collect Trafilatura (Data files)
tmp_ret = collect_all('trafilatura')
datas += tmp_ret[0]; binaries += tmp_ret[1]; hiddenimports += tmp_ret[2]

# --- 5. Analysis ---
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
    [],
    exclude_binaries=True,
    name='PromptChat',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    console=True, # KEEP TRUE for debugging!
    disable_windowed_traceback=False,
    argv_emulation=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
)

coll = COLLECT(
    exe,
    a.binaries,
    a.zipfiles,
    a.datas,
    strip=False,
    upx=True,
    upx_exclude=[],
    name='PromptChat',
)