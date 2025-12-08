# ========================================================
# ================  gui.py  (Thread Fix) =================
# ========================================================


from __future__ import annotations

import asyncio
import glob
import json
import os
import pathlib
import platform
import sys
import traceback
from pathlib import Path
from typing import Any, Dict, List, Optional
import threading

from PyQt5.QtGui import QTextCursor

import blocks
import pipeline
from gui_elements import DatabasePane
from loggers import DEBUG_LOGGER
from registry import BLOCKS
import models

if getattr(sys, 'frozen', False):
    # 1. FIX SSL CERTIFICATES (For DuckDuckGo & Requests)
    # We force the app to use the certificate bundle packed inside the exe
    cert_path = os.path.join(sys._MEIPASS, 'certifi', 'cacert.pem')
    if os.path.exists(cert_path):
        os.environ['REQUESTS_CA_BUNDLE'] = cert_path
        os.environ['SSL_CERT_FILE'] = cert_path

    # 2. FORCE PLAYWRIGHT TO USE GLOBAL BROWSERS
    # By default, frozen Playwright only looks in local folders. We point it back to global.
    if "PLAYWRIGHT_BROWSERS_PATH" not in os.environ:
        if sys.platform == 'win32':
            # Windows Default: %LOCALAPPDATA%\ms-playwright
            base = os.environ.get('LOCALAPPDATA')
            if base:
                os.environ["PLAYWRIGHT_BROWSERS_PATH"] = os.path.join(base, "ms-playwright")

try:
    from models import _MODELS, get_chat_model
except ImportError:
    print("WARNING: Could not import _MODELS from models.py. Using fallback.", file=sys.stderr)
    _MODELS = {"lexicon": None, "lexicon-adv": None}  # Fallback

    def get_chat_model(name, **kwargs):
        raise ImportError("Could not load get_chat_model")

from PyQt5.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QListWidget, QPushButton, QCheckBox, QPlainTextEdit, QTabWidget,
    QStatusBar, QAction, QFileDialog, QListWidgetItem, QAbstractItemView,
    QGroupBox, QSplitter, QLabel, QMessageBox, QComboBox, QInputDialog, QLineEdit  # <-- QInputDialog added
)
from PyQt5.QtCore import QObject, pyqtSignal, QThread, pyqtSlot, Qt


# --- PATH HELPERS FOR PYINSTALLER ---
def get_base_path():
    """ Returns the path to bundled resources (temp folder if frozen). """
    if getattr(sys, 'frozen', False):
        return Path(sys._MEIPASS)
    return Path(__file__).parent

def get_user_dir():
    """ Returns the directory where the executable lives (for saving data). """
    if getattr(sys, 'frozen', False):
        return Path(sys.executable).parent
    return Path(__file__).parent



# Define paths
BUNDLED_PRESET_FILE = get_base_path() / "gui_presets.json"
USER_PRESET_FILE = get_user_dir() / "gui_presets.json"
STATE_FILE = get_user_dir() / ".promptchat_gui_state.json"

APP_TITLE = "PromptChat GUI"

# DARK_STYLESHEET (omitted for brevity)
DARK_STYLESHEET = """
    QMainWindow, QTabWidget, QWidget {
        background-color: #2b2b2b;
        color: #dcdcdc;
    }
    QTabWidget::pane {
        border-top: 2px solid #4f4f4f;4
    }
    QTabBar::tab {
        background: #4a4a4a;
        color: #dcdcdc;
        padding: 8px 20px;
        border: 1px solid #5a5a5a;
        border-bottom: none;
        border-top-left-radius: 4px;
        border-top-right-radius: 4px;
    }
    QTabBar::tab:selected, QTabBar::tab:hover {
        background: #5a5a5a;
    }
    QPlainTextEdit {
        background-color: #212121;
        color: #dcdcdc;
        border: 1px solid #4f4f4f;
        font-family: Consolas, Courier New, monospace;
        font-size: 12px;
    }
    QPushButton {
        background-color: #4a4a4a;
        color: #dcdcdc;
        border: 1px solid #5a5a5a;
        padding: 5px 15px;
        border-radius: 3px;
        font-size: 13px;
        font-weight: bold;
    }
    QPushButton:hover {
        background-color: #5a5a5a;
        border-color: #6a6a6a;
    }
    QPushButton:pressed {
        background-color: #3a3a3a;
    }
    QPushButton:disabled {
        background-color: #333333;
        color: #777777;
        border-color: #444444;
    }
    QListWidget, QComboBox {
        background-color: #212121;
        border: 1px solid #4f4f4f;
    }
    QComboBox::drop-down {
        border: none;
        background-color: #4a4a4a;
    }
    QComboBox QAbstractItemView {
        background-color: #212121;
        color: #dcdcdc;
        selection-background-color: #5a5a5a;
    }
    QGroupBox {
        color: #dcdcdc;
        font-weight: bold;
    }
    QStatusBar {
        color: #dcdcdc;
    }
    QMenuBar {
        background-color: #4a4a4a;
        color: #dcdcdc;
    }
    QMenuBar::item:selected {
        background-color: #5a5a5a;
    }
    QMenu {
        background-color: #4a4a4a;
        color: #dcdcdc;
    }
    QMenu::item:selected {
        background-color: #5a5a5a;
    }
"""


# ======================= PRESETS =========================================

def load_presets() -> List[Dict[str, Any]]:
    # Start with the placeholder
    presets = [
        {
            "name": "--- Select a Preset ---",
            "blocks": [],
            "extras": "",
            "model": "lexicon",
        }
    ]

    # Helper: find index of existing preset by name
    def get_index_by_name(name: str) -> int:
        for i, p in enumerate(presets):
            if p.get("name") == name:
                return i
        return -1

    # 1. Load Bundled Presets (Base layer) - Preserves File Order
    if BUNDLED_PRESET_FILE.exists():
        try:
            with open(BUNDLED_PRESET_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
                if isinstance(data, list):
                    for entry in data:
                        if isinstance(entry, dict) and entry.get("name"):
                            idx = get_index_by_name(entry["name"])
                            if idx != -1:
                                presets[idx] = entry  # Overwrite existing
                            else:
                                presets.append(entry) # Add new
        except Exception as e:
            print(f"Error loading bundled presets: {e}", file=sys.stderr)

    # 2. Load User Presets (Overlay layer) - Preserves File Order
    if USER_PRESET_FILE.exists():
        try:
            with open(USER_PRESET_FILE, "r", encoding="utf-8") as f:
                raw = json.load(f)
            if isinstance(raw, list):
                for entry in raw:
                    if isinstance(entry, dict) and entry.get("name"):
                        idx = get_index_by_name(entry["name"])
                        if idx != -1:
                            # Update existing slot (maintaining original order)
                            presets[idx] = entry
                        else:
                            # Append new user preset (maintaining user file order)
                            presets.append(entry)
        except Exception as e:
            print(f"Error loading user presets: {e}", file=sys.stderr)

    return presets


GUI_PRESETS: List[Dict[str, Any]] = load_presets()


def save_presets_to_disk() -> None:
    """
    Writes all current presets (excluding the placeholder) to the user's local file.
    This effectively snapshots the current configuration.
    """
    try:
        # Skip index 0 (Placeholder)
        data_to_save = GUI_PRESETS[1:]
        with open(USER_PRESET_FILE, "w", encoding="utf-8") as f:
            json.dump(data_to_save, f, indent=2, ensure_ascii=False)
    except Exception as e:
        print(f"Error saving gui_presets.json: {e}", file=sys.stderr)


# ======================= WORKER THREAD ===================================

# Safety caps to keep GUI from blowing RAM
MAX_FINAL_PAYLOAD_CHARS   = 200_000   # ~200 KB of final text
MAX_BLOCK_SNIPPET_CHARS   = 80_000    # per-block snippet in RUN LOG
MAX_RUN_LOG_TOTAL_CHARS   = 800_000   # total joined RUN LOG size
def clamp_head_tail(text: str, max_chars: int, head_ratio: float = 0.6) -> str:
    """
    Keep the beginning and end of a long string, drop the middle.

    head_ratio = fraction of max_chars reserved for the beginning.
    """
    if len(text) <= max_chars:
        return text

    head_len = int(max_chars * head_ratio)
    tail_len = max_chars - head_len
    head = text[:head_len]
    tail = text[-tail_len:]
    return head + "\n\n[… middle truncated …]\n\n" + tail

class Worker(QObject):
    finished = pyqtSignal(bool, str, dict)
    status_update = pyqtSignal(str)

    def __init__(
        self,
        blocks_sel: List[str],
        prompt: str,
        extras_raw: str,
        print_json: bool,
        stop_event: threading.Event,
        model_name: str,
    ):
        super().__init__()
        self.blocks_sel = blocks_sel
        self.prompt = prompt
        self.extras_raw = extras_raw
        self.print_json = print_json
        self.stop_event = stop_event
        self.model_name = model_name

    @pyqtSlot()
    def run(self):
        try:
            import blocks
            blocks.ensure_app_dirs()
            prompt_str = self.prompt or ""
            payload_word_len = len(prompt_str.split()) if prompt_str.strip() else 0
            payload_char_len = len(prompt_str)

            extras_raw_substituted = (
                self.extras_raw
                .replace("{payload}", prompt_str)
                .replace("{payload.length}", str(payload_word_len))
                .replace("{payload.char_length}", str(payload_char_len))
            )
            extras_list = [ln.strip() for ln in extras_raw_substituted.splitlines() if ln.strip()]
            extras = blocks.parse_extras(extras_list)

            # Inject selected model into chat/code + pipeline.chat/pipeline.code
            if self.model_name:
                extras.setdefault("chat", {})["model"] = self.model_name
                extras.setdefault("code", {})["model"] = self.model_name

                pipe_extras = extras.setdefault("pipeline", {})
                pipe_extras.setdefault("chat.model", self.model_name)
                pipe_extras.setdefault("code.model", self.model_name)

            # NEW: model-specific params via "modelname.param" extras section
            model_key = (self.model_name or "").strip().lower()
            model_params: Dict[str, Any] = {}

            if model_key:
                for section_name, section_dict in extras.items():
                    if section_name.lower() == model_key and isinstance(section_dict, dict):
                        model_params = section_dict
                        break

            if model_params:
                chat_ex = extras.setdefault("chat", {})
                code_ex = extras.setdefault("code", {})
                pipe_ex = extras.setdefault("pipeline", {})

                for k, v in model_params.items():
                    chat_ex.setdefault(k, v)
                    code_ex.setdefault(k, v)
                    pipe_ex.setdefault(f"chat.{k}", v)
                    pipe_ex.setdefault(f"code.{k}", v)

            results_md: List[str] = []
            results_json: List[Dict[str, Any]] = []
            combined_meta: Dict[str, Any] = {"runs": []}

            root_payload = self.prompt
            current_payload = self.prompt or ""

            for idx, block_name in enumerate(self.blocks_sel, 1):
                if self.stop_event.is_set():
                    self.status_update.emit("Cancelled.")
                    break

                self.status_update.emit(f"Running {idx}/{len(self.blocks_sel)}: {block_name}")

                block_key = block_name.lower()
                params: Dict[str, Any] = {}
                params.update(extras.get(block_key, {}))
                params.update(extras.get("all", {}))

                params['stop_event'] = self.stop_event

                if block_name == "pipeline" or block_name == "concat":
                    params["_gui_extras_passthrough"] = extras

                payload_source = params.pop("_payload_source", "chain")
                payload_to_use = root_payload if payload_source == "root" else current_payload

                blk = BLOCKS.create(block_name)
                try:
                    result, meta = blk.execute(payload_to_use, params=params)

                    # --------- Update current_payload (with clamp) ---------
                    if payload_source == "root":
                        if result.startswith(root_payload):
                            additive_result = result[len(root_payload):].strip()
                            if additive_result:
                                current_payload = current_payload + "\n\n" + additive_result
                        else:
                            current_payload = current_payload + "\n\n" + result
                    else:
                        current_payload = result

                    if len(current_payload) > MAX_FINAL_PAYLOAD_CHARS:
                        # Keep the *start* of the final output so you see the actual answer.
                        current_payload = (
                                current_payload[:MAX_FINAL_PAYLOAD_CHARS]
                                + "\n\n[… output truncated for GUI; see logs/file for full text …]"
                        )
                    # --------- Per-block log snippet (with clamp) ----------
                    snippet = result or ""
                    if len(snippet) > MAX_BLOCK_SNIPPET_CHARS:
                        snippet = (
                            snippet[:MAX_BLOCK_SNIPPET_CHARS]
                            + "\n\n[… block output truncated …]"
                        )

                    results_md.append(
                        f"\n\n# ── {block_name} ─────────────────────────────────────\n{snippet}"
                    )
                    # Store preview instead of full result to save memory
                    results_json.append(
                        {"block": block_name, "metadata": meta, "result_preview": snippet}
                    )
                    combined_meta["runs"].append({"block": block_name, "metadata": meta})

                except Exception as e:
                    import traceback
                    tb = traceback.format_exc()
                    err_blob = f"[{block_name}] ERROR: {e}\n{tb}"

                    # Clamp error blob too, just in case
                    if len(err_blob) > MAX_BLOCK_SNIPPET_CHARS:
                        err_blob = (
                            err_blob[:MAX_BLOCK_SNIPPET_CHARS]
                            + "\n\n[… error log truncated …]"
                        )

                    results_md.append(
                        f"\n\n# ── {block_name} (ERROR) ───────────────────────────\n{err_blob}"
                    )
                    results_json.append(
                        {"block": block_name, "error": str(e), "traceback_preview": err_blob}
                    )
                    combined_meta["runs"].append({"block": block_name, "error": str(e)})
                    self.status_update.emit(f"Failed on block '{block_name}'. Stopping pipeline.")
                    break

            # ------------- Final output building (with clamps) -------------
            if self.print_json:
                out = json.dumps(results_json, indent=2, ensure_ascii=False)
            else:
                total_log = "".join(results_md)
                if len(total_log) > MAX_RUN_LOG_TOTAL_CHARS:
                    # Keep both the start of the log (early blocks / context)
                    # and the end (final blocks) so you can see what actually happened.
                    total_log = clamp_head_tail(total_log, MAX_RUN_LOG_TOTAL_CHARS)
                    total_log += "\n\n[… RUN LOG truncated due to size …]"

                try:
                    out = (
                        f"--- FINAL OUTPUT ---\n{current_payload}\n\n"
                        f"--- RUN LOG ---\n" + total_log.lstrip()
                    )
                except MemoryError:
                    # Brutal fallback if even that fails
                    safe_payload = current_payload[-MAX_FINAL_PAYLOAD_CHARS:]
                    safe_log = total_log[:MAX_RUN_LOG_TOTAL_CHARS]
                    out = (
                        "--- FINAL OUTPUT (TRUNCATED DUE TO MEMORY) ---\n"
                        + safe_payload
                        + "\n\n--- RUN LOG (TRUNCATED DUE TO MEMORY) ---\n"
                        + safe_log
                    )

            self.finished.emit(True, out, combined_meta)

        except Exception as e:
            import traceback
            tb = traceback.format_exc()
            self.finished.emit(False, f"WORKER FAILED:\n{e}\n\n{tb}", {})


# ======================= MAIN GUI CLASS ==================================

class PromptChatGUI(QMainWindow):
    def __init__(self) -> None:
        super().__init__()

        self.setWindowTitle(APP_TITLE)
        self.setGeometry(100, 100, 1200, 800)
        self.setMinimumSize(950, 640)
        self.setStyleSheet(DARK_STYLESHEET)

        self.run_thread: Optional[QThread] = None
        self.worker: Optional[Worker] = None
        self._stop_event = threading.Event()

        # NEW: reference to the database pane
        self.db_pane: Optional[DatabasePane] = None
        # NEW: top-level tab widget switching between Prompt Chat and Database
        self.main_tabs: Optional[QTabWidget] = None
        self.main_ui_widget: Optional[QWidget] = None

        self._build_menu()
        self._build_body()
        self._refresh_block_list()
        self._load_state()
        self._show_main_ui()  # Start on Prompt Chat tab
        # NEW: Store all log lines in memory so we can filter them later
        self.all_log_lines: List[str] = []
        DEBUG_LOGGER.message_signal.connect(self._append_debug_message)
        DEBUG_LOGGER.log_message("[Debug] Debug logger initialized.")
    # ---------------- UI building ----------------
    def _build_menu(self) -> None:
        menu = self.menuBar()

        file_menu = menu.addMenu("File")
        save_action = QAction("Save Result As…", self)
        save_action.triggered.connect(self._save_result_as)
        file_menu.addAction(save_action)
        file_menu.addSeparator()
        exit_action = QAction("Exit", self)
        exit_action.triggered.connect(self.close)
        file_menu.addAction(exit_action)

        run_menu = menu.addMenu("Run")
        run_action = QAction("Run (Ctrl+Enter)", self)
        run_action.setShortcut("Ctrl+Return")
        run_action.triggered.connect(self._on_run_clicked)
        run_menu.addAction(run_action)

        cancel_action = QAction("Cancel Run", self)
        cancel_action.triggered.connect(self._cancel_run)
        run_menu.addAction(cancel_action)

        database_menu = menu.addMenu("Database")
        open_db_action = QAction("Open Database", self)
        open_db_action.triggered.connect(self._open_database)
        database_menu.addAction(open_db_action)

        help_menu = menu.addMenu("Help")
        about_action = QAction("About", self)
        about_action.triggered.connect(self._show_about)
        help_menu.addAction(about_action)

    def _build_body(self) -> None:
        self.main_widget = QWidget()
        self.setCentralWidget(self.main_widget)
        self.root_layout = QVBoxLayout(self.main_widget)

        # 🔹 Instead of a stacked layout, use a tab widget at the top
        self.main_tabs = QTabWidget()
        self.root_layout.addWidget(self.main_tabs)

        # Build both panes and add them as tabs
        self._build_main_ui()
        self._build_database_ui()

    def _build_main_ui(self) -> None:
        """Builds the main UI for prompt/pipeline management."""
        self.main_ui_widget = QWidget()
        self.main_ui_layout = QVBoxLayout(self.main_ui_widget)

        top_level_splitter = QSplitter(Qt.Vertical)
        self.main_ui_layout.addWidget(top_level_splitter, 1)

        # ---- Top: block list / pipeline / presets / model ----
        top = QGroupBox("Build Pipeline")
        top_layout = QHBoxLayout(top)
        top_level_splitter.addWidget(top)

        # Left: Available blocks
        available_layout = QVBoxLayout()
        available_layout.addWidget(QLabel("Available Blocks"))

        self.blocks_list = QListWidget()
        self.blocks_list.setSelectionMode(QAbstractItemView.SingleSelection)
        self.blocks_list.itemDoubleClicked.connect(self._add_block_to_pipeline)
        self.blocks_list.currentItemChanged.connect(self._on_block_selected)
        available_layout.addWidget(self.blocks_list)

        top_layout.addLayout(available_layout, 1)

        # Middle: pipeline + up/down
        mid_buttons_layout = QVBoxLayout()
        mid_buttons_layout.addStretch(1)

        btn_add = QPushButton("Add ->")
        btn_add.clicked.connect(self._add_block_to_pipeline)
        mid_buttons_layout.addWidget(btn_add)

        btn_remove = QPushButton("<- Remove")
        btn_remove.clicked.connect(self._remove_block_from_pipeline)
        mid_buttons_layout.addWidget(btn_remove)

        mid_buttons_layout.addStretch(1)
        top_layout.addLayout(mid_buttons_layout)

        # Pipeline list
        pipeline_layout = QVBoxLayout()
        pipeline_layout.addWidget(QLabel("Pipeline Stages (Run in Order)"))

        self.pipeline_list = QListWidget()
        self.pipeline_list.setSelectionMode(QAbstractItemView.ExtendedSelection)
        pipeline_layout.addWidget(self.pipeline_list)

        pipeline_btns = QWidget()
        pipeline_btns_layout = QHBoxLayout(pipeline_btns)
        pipeline_btns_layout.setContentsMargins(0, 0, 0, 0)

        btn_up = QPushButton("Move Up")
        btn_up.clicked.connect(self._move_up)
        btn_down = QPushButton("Move Down")
        btn_down.clicked.connect(self._move_down)
        pipeline_btns_layout.addWidget(btn_up)
        pipeline_btns_layout.addWidget(btn_down)
        pipeline_btns_layout.addStretch(1)

        pipeline_layout.addWidget(pipeline_btns)
        top_layout.addLayout(pipeline_layout, 1)

        # Right: presets + model + params + run controls
        right_controls_layout = QVBoxLayout()

        right_controls_layout.addWidget(QLabel("Presets"))
        self.preset_combo = QComboBox()
        self._populate_presets_combo()
        self.preset_combo.currentIndexChanged.connect(self._on_preset_selected)
        right_controls_layout.addWidget(self.preset_combo)

        preset_btns = QWidget()
        preset_btns_layout = QHBoxLayout(preset_btns)
        preset_btns_layout.setContentsMargins(0, 0, 0, 0)

        self.save_preset_btn = QPushButton("Save Preset…")
        self.save_preset_btn.clicked.connect(self._save_preset)

        self.delete_preset_btn = QPushButton("Delete Preset")
        self.delete_preset_btn.clicked.connect(self._delete_preset)

        preset_btns_layout.addWidget(self.save_preset_btn)
        preset_btns_layout.addWidget(self.delete_preset_btn)
        right_controls_layout.addWidget(preset_btns)

        right_controls_layout.addWidget(QLabel("Chat Model (Select to see params)"))
        self.model_combo = QComboBox()
        self.model_combo.addItems(sorted(_MODELS.keys()))
        self.model_combo.currentTextChanged.connect(self._on_model_selected)
        right_controls_layout.addWidget(self.model_combo)

        right_controls_layout.addWidget(QLabel("Block/Model Parameters (Double-click to add)"))
        self.block_params_list = QListWidget()
        self.block_params_list.itemDoubleClicked.connect(self._add_param_to_extras)
        right_controls_layout.addWidget(self.block_params_list, 1)

        run_controls_widget = QWidget()
        run_controls_hbox = QHBoxLayout(run_controls_widget)
        run_controls_hbox.setContentsMargins(0, 0, 0, 0)

        self.json_var = QCheckBox("Print JSON")
        self.run_btn = QPushButton("Run")
        self.run_btn.clicked.connect(self._on_run_clicked)

        run_controls_hbox.addWidget(self.json_var)
        run_controls_hbox.addStretch(1)
        run_controls_hbox.addWidget(self.run_btn)
        right_controls_layout.addWidget(run_controls_widget, 0, Qt.AlignBottom)

        top_layout.addLayout(right_controls_layout, 1)

        # ---- Bottom: prompt / extras / result tabs ----
        bottom_widget = QWidget()
        bottom_layout = QVBoxLayout(bottom_widget)
        bottom_layout.setContentsMargins(0, 0, 0, 0)
        top_level_splitter.addWidget(bottom_widget)

        prompt_output_splitter = QSplitter(Qt.Vertical)
        bottom_layout.addWidget(prompt_output_splitter, 1)

        mid = QSplitter(Qt.Horizontal)
        prompt_output_splitter.addWidget(mid)

        prompt_frame = QGroupBox("Prompt (use {payload} in extras to reference this)")
        prompt_layout = QVBoxLayout(prompt_frame)
        self.prompt_text = QPlainTextEdit()
        prompt_layout.addWidget(self.prompt_text)
        mid.addWidget(prompt_frame)

        extras_frame = QGroupBox("--extra (key=val, one per line)")
        extras_layout = QVBoxLayout(extras_frame)
        self.extras_text = QPlainTextEdit()
        extras_layout.addWidget(self.extras_text)
        mid.addWidget(extras_frame)

        mid.setSizes([700, 300])

        tabs = QTabWidget()
        prompt_output_splitter.addWidget(tabs)
        prompt_output_splitter.setSizes([300, 500])

        self.result_text = QPlainTextEdit()
        self.result_text.setReadOnly(True)
        tabs.addTab(self.result_text, "Result")

        self.meta_text = QPlainTextEdit()
        self.meta_text.setReadOnly(True)
        self.meta_text.setLineWrapMode(QPlainTextEdit.NoWrap)
        tabs.addTab(self.meta_text, "Metadata")

        # 🔹 Add this whole Prompt Chat pane as a tab
        self.main_tabs.addTab(self.main_ui_widget, "Prompt Chat")
        # =========================================================
        # NEW: Log Tab with Search Bar
        # =========================================================
        log_tab_widget = QWidget()
        log_tab_layout = QVBoxLayout(log_tab_widget)
        log_tab_layout.setContentsMargins(5, 5, 5, 5)

        # Search Bar
        self.log_search_bar = QLineEdit()
        self.log_search_bar.setPlaceholderText("Search logs... (filters automatically)")
        self.log_search_bar.setStyleSheet("""
                QLineEdit {
                    background-color: #212121;
                    color: #dcdcdc;
                    border: 1px solid #4f4f4f;
                    padding: 4px;
                    border-radius: 4px;
                }
            """)
        self.log_search_bar.textChanged.connect(self._filter_logs)
        log_tab_layout.addWidget(self.log_search_bar)

        # Log Text Area
        self.debug_text = QPlainTextEdit()
        self.debug_text.setReadOnly(True)
        self.debug_text.setLineWrapMode(QPlainTextEdit.NoWrap)
        log_tab_layout.addWidget(self.debug_text)

        tabs.addTab(log_tab_widget, "Log")
        # =========================================================
    def _build_database_ui(self) -> None:
        """Build the database pane UI as a tab, using DatabasePane."""
        self.db_pane = DatabasePane(APP_TITLE, self)
        self.main_tabs.addTab(self.db_pane, "Database")

    @pyqtSlot(str)
    def _append_debug_message(self, msg: str) -> None:
        """
        Slot that appends debug messages to the Debug Log pane.
        Stores all logs in memory, but only displays them if they match the filter.
        """
        # 1. Always store the full log
        self.all_log_lines.append(msg)

        # 2. Check current filter
        filter_text = self.log_search_bar.text().strip().lower()

        # 3. If no filter, or if filter matches, append to GUI immediately
        if not filter_text or filter_text in msg.lower():
            self.debug_text.appendPlainText(msg)
            # Optional: Scroll to bottom only if user was already at bottom or mostly there
            self.debug_text.moveCursor(QTextCursor.End)
    # ---------------- Database Helpers ----------------
    @pyqtSlot(str)
    def _filter_logs(self, text: str) -> None:
        """
        Re-renders the log window based on the search query.
        """
        query = text.strip().lower()
        self.debug_text.clear()

        if not query:
            # If search is empty, dump everything back in
            # Joining is faster than calling appendPlainText thousands of times
            full_log = "\n".join(self.all_log_lines)
            self.debug_text.setPlainText(full_log)
        else:
            # Filter lines
            matching_lines = [
                line for line in self.all_log_lines
                if query in line.lower()
            ]
            self.debug_text.setPlainText("\n".join(matching_lines))

        # Scroll to bottom after filtering
        self.debug_text.moveCursor(QTextCursor.End)
    def _open_database(self) -> None:
        """Opens a file dialog to select an SQLite database and displays its contents."""
        file_path, _ = QFileDialog.getOpenFileName(
            self,
            "Open SQLite Database",
            "",
            "SQLite Files (*.db *.sqlite *.sqlite3)",
        )
        if file_path and self.db_pane:
            ok = self.db_pane.load_database(file_path)
            if ok:
                self._show_database_ui()

    def _show_main_ui(self) -> None:
        """Select the Prompt Chat tab."""
        if self.main_tabs and self.main_ui_widget:
            self.main_tabs.setCurrentWidget(self.main_ui_widget)

    def _show_database_ui(self) -> None:
        """Select the Database tab."""
        if self.main_tabs and self.db_pane:
            self.main_tabs.setCurrentWidget(self.db_pane)

    def _populate_presets_combo(self, select_index: Optional[int] = None) -> None:
        """Refresh the presets combo from GUI_PRESETS."""
        self.preset_combo.blockSignals(True)
        self.preset_combo.clear()
        for preset in GUI_PRESETS:
            self.preset_combo.addItem(preset.get("name", ""))
        # Default selection
        if select_index is not None and 0 <= select_index < self.preset_combo.count():
            self.preset_combo.setCurrentIndex(select_index)
        else:
            self.preset_combo.setCurrentIndex(0)
        self.preset_combo.blockSignals(False)

    def _refresh_block_list(self) -> None:
        names = BLOCKS.names()
        self.blocks_list.clear()
        self.blocks_list.addItems(names)
        if not names:
            self.statusBar().showMessage("No blocks registered. Check console for import errors.")
        else:
            self.blocks_list.setCurrentRow(0)

    # ---------------- Pipeline List helpers ----------------
    def _add_block_to_pipeline(self) -> None:
        selected_item = self.blocks_list.currentItem()
        if selected_item:
            self.pipeline_list.addItem(selected_item.text())

    def _remove_block_from_pipeline(self) -> None:
        selected_items = self.pipeline_list.selectedItems()
        if not selected_items:
            count = self.pipeline_list.count()
            if count > 0:
                self.pipeline_list.takeItem(count - 1)
            return
        for item in selected_items:
            self.pipeline_list.takeItem(self.pipeline_list.row(item))

    def _get_pipeline_blocks(self) -> List[str]:
        return [self.pipeline_list.item(i).text() for i in range(self.pipeline_list.count())]

    def _move_up(self) -> None:
        selected_rows = sorted([self.pipeline_list.row(item) for item in self.pipeline_list.selectedItems()])
        if not selected_rows:
            row = self.pipeline_list.count() - 1
            if row <= 0:
                return
            selected_rows = [row]
        if selected_rows[0] == 0:
            return
        for row in selected_rows:
            item = self.pipeline_list.takeItem(row)
            self.pipeline_list.insertItem(row - 1, item)
            item.setSelected(True)
        if self.pipeline_list.selectedItems():
            self.pipeline_list.scrollToItem(self.pipeline_list.selectedItems()[0])

    def _move_down(self) -> None:
        selected_rows = sorted(
            [self.pipeline_list.row(item) for item in self.pipeline_list.selectedItems()],
            reverse=True,
        )
        if not selected_rows:
            row = self.pipeline_list.count() - 1
            if row < 0 or row == self.pipeline_list.count() - 1:
                return
            selected_rows = [row]
        if selected_rows[0] == self.pipeline_list.count() - 1:
            return
        for row in selected_rows:
            item = self.pipeline_list.takeItem(row)
            self.pipeline_list.insertItem(row + 1, item)
            item.setSelected(True)
        if self.pipeline_list.selectedItems():
            self.pipeline_list.scrollToItem(self.pipeline_list.selectedItems()[-1])

    # ---------------- Block / Model params ----------------
    @pyqtSlot(QListWidgetItem, QListWidgetItem)
    def _on_block_selected(self, current_item: QListWidgetItem, previous_item: QListWidgetItem):
        """Called when the user clicks a block in the 'Available Blocks' list."""
        self.block_params_list.clear()

        if not current_item:
            self.block_params_list.addItem("Select a block or model to see params.")
            return

        block_name = current_item.text()

        try:
            block_instance = BLOCKS.create(block_name)
            params_info = block_instance.get_params_info()

            if not params_info:
                self.block_params_list.addItem(f"No parameters for {block_name}")
                return

            self.block_params_list.addItem(f"--- ({block_name} Block Parameters) ---")
            if block_name == "pipeline":
                self.block_params_list.addItem("--- (Use 'pipeline.block.param=val') ---")

            for key, value in params_info.items():
                item_str = f"{key}={json.dumps(value)}"
                self.block_params_list.addItem(item_str)

            if block_name.lower() == "chat":
                self.block_params_list.addItem("")  # spacer
                self._load_model_params(self.model_combo.currentText())

        except Exception as e:
            self.block_params_list.addItem(f"Error loading block params:\n{e}")

    @pyqtSlot(str)
    def _on_model_selected(self, model_name: str):
        """Called when the model_combo changes."""
        current_block_item = self.blocks_list.currentItem()
        if current_block_item and current_block_item.text().lower() == "chat":
            self._on_block_selected(current_block_item, None)
        else:
            # Show model params even if chat block isn't selected
            self.block_params_list.clear()
            self._load_model_params(model_name)

    def _load_model_params(self, model_name: str):
        """Helper to load a model's params into the list widget."""
        if not model_name:
            return

        try:
            model_instance = get_chat_model(model_name)
            params_info = model_instance.get_params_info()

            if not params_info:
                self.block_params_list.addItem(f"No parameters for model {model_name}")
                return

            self.block_params_list.addItem(f"--- ({model_name} Model Parameters) ---")

            for key, value in params_info.items():
                if key == "model_name":
                    continue
                item_str = f"{key}={json.dumps(value)}"
                self.block_params_list.addItem(item_str)

        except Exception as e:
            self.block_params_list.addItem(f"Error loading model params:\n{e}")

    @pyqtSlot()
    def _add_param_to_extras(self):
        """Adds the selected param to the --extra text box."""
        selected_item = self.block_params_list.currentItem()
        if not selected_item:
            return

        item_str = selected_item.text()
        if "---" in item_str or "=" not in item_str:
            return

        block_name = ""
        current_block_item = self.blocks_list.currentItem()
        if current_block_item:
            block_name = current_block_item.text().lower()

        text_to_add = ""
        is_pipeline_mode = "pipeline" in self._get_pipeline_blocks()

        # Check if the selected param is a model param
        is_model_param = False
        try:
            key, val = item_str.split("=", 1)
            model_instance = get_chat_model(self.model_combo.currentText())
            if key in model_instance.get_params_info():
                is_model_param = True
        except Exception:
            pass  # Not a model param

        if block_name == "chat" or is_model_param:
            if is_pipeline_mode:
                text_to_add = f"pipeline.chat.{item_str}"
            else:
                text_to_add = f"chat.{item_str}"
        elif block_name:
            if is_pipeline_mode:
                text_to_add = f"pipeline.{block_name}.{item_str}"
            else:
                text_to_add = f"{block_name}.{item_str}"
        else:
            text_to_add = item_str

        if text_to_add:
            current_extras = self.extras_text.toPlainText()
            if current_extras and not current_extras.endswith("\n"):
                self.extras_text.appendPlainText("\n")
            self.extras_text.appendPlainText(text_to_add)
            self.extras_text.centerCursor()

    # ---------------- Presets: load / save / delete ----------------
    @pyqtSlot(int)
    def _on_preset_selected(self, index: int):
        """
        When user selects a preset:
          - index 0 → clear pipeline + extras (placeholder)
          - index > 0 → load preset blocks, extras, model
        """
        if index < 0 or index >= len(GUI_PRESETS):
            return

        if index == 0:
            # Placeholder: clear current config
            if self.pipeline_list.count() > 0 or self.extras_text.toPlainText():
                self.pipeline_list.clear()
                self.extras_text.clear()
                self.statusBar().showMessage("Cleared pipeline and extras.")
            return

        preset = GUI_PRESETS[index]
        blocks = preset.get("blocks", [])
        extras_text = preset.get("extras", "") or ""
        model_name = preset.get("model", "")

        self.pipeline_list.clear()
        if isinstance(blocks, list):
            self.pipeline_list.addItems(blocks)

        self.extras_text.setPlainText(extras_text)

        if model_name and self.model_combo.findText(model_name) != -1:
            self.model_combo.setCurrentText(model_name)

        # Return combo to placeholder (optional UX choice)
        self.preset_combo.blockSignals(True)
        self.preset_combo.setCurrentIndex(0)
        self.preset_combo.blockSignals(False)
        self.statusBar().showMessage(f"Loaded preset: {preset.get('name', '')}")

    def _save_preset(self) -> None:
        """
        Save the current pipeline, extras, and model as a named preset.

        - Prompts for name.
        - If a preset with that name exists (index > 0), ask to overwrite.
        - Writes GUI_PRESETS[1:] to gui_presets.json.
        """
        name, ok = QInputDialog.getText(
            self,
            "Save Preset",
            "Preset name:",
        )
        if not ok:
            return

        name = name.strip()
        if not name:
            QMessageBox.warning(self, APP_TITLE, "Preset name cannot be empty.")
            return

        if name == GUI_PRESETS[0]["name"]:
            QMessageBox.warning(self, APP_TITLE, "This name is reserved. Choose another.")
            return

        # Determine if we're overwriting an existing preset
        existing_index = -1
        for idx in range(1, len(GUI_PRESETS)):
            if GUI_PRESETS[idx].get("name") == name:
                existing_index = idx
                break

        if existing_index != -1:
            reply = QMessageBox.question(
                self,
                APP_TITLE,
                f"A preset named '{name}' already exists.\nOverwrite it?",
                QMessageBox.Yes | QMessageBox.No,
                QMessageBox.No,
            )
            if reply != QMessageBox.Yes:
                return
            target_index = existing_index
        else:
            target_index = len(GUI_PRESETS)
            GUI_PRESETS.append({})

        # Build preset from current GUI state
        preset = {
            "name": name,
            "blocks": self._get_pipeline_blocks(),
            "extras": self.extras_text.toPlainText(),
            "model": self.model_combo.currentText() or "lexicon",
        }
        GUI_PRESETS[target_index] = preset

        save_presets_to_disk()
        self._populate_presets_combo(select_index=0)
        self.statusBar().showMessage(f"Preset saved: {name}")

    def _delete_preset(self) -> None:
        """
        Delete the currently selected preset (index > 0).
        """
        index = self.preset_combo.currentIndex()
        if index <= 0:
            QMessageBox.information(
                self,
                APP_TITLE,
                "Select a user preset (not the placeholder) to delete.",
            )
            return

        if index >= len(GUI_PRESETS):
            return

        name = GUI_PRESETS[index].get("name", "")
        reply = QMessageBox.question(
            self,
            APP_TITLE,
            f"Delete preset '{name}'?",
            QMessageBox.Yes | QMessageBox.No,
            QMessageBox.No,
        )
        if reply != QMessageBox.Yes:
            return

        GUI_PRESETS.pop(index)
        save_presets_to_disk()
        self._populate_presets_combo(select_index=0)
        self.statusBar().showMessage(f"Preset deleted: {name}")

    # ---------------- persistence ----------------
    def _load_state(self) -> None:
        try:
            if STATE_FILE.exists():
                data = json.loads(STATE_FILE.read_text(encoding="utf-8"))
                pipeline_blocks = data.get("pipeline_blocks", [])
                if isinstance(pipeline_blocks, list):
                    self.pipeline_list.addItems(pipeline_blocks)
                self.prompt_text.setPlainText(data.get("prompt", ""))
                self.extras_text.setPlainText(data.get("extras", ""))
                self.json_var.setChecked(bool(data.get("print_json", False)))
                model_name = data.get("model_name", "lexicon")
                if self.model_combo.findText(model_name) != -1:
                    self.model_combo.setCurrentText(model_name)
        except Exception:
            pass

    def _save_state(self) -> None:
        try:
            data = {
                "pipeline_blocks": self._get_pipeline_blocks(),
                "prompt": self.prompt_text.toPlainText(),
                "extras": self.extras_text.toPlainText(),
                "print_json": self.json_var.isChecked(),
                "model_name": self.model_combo.currentText(),
            }
            STATE_FILE.write_text(json.dumps(data, indent=2), encoding="utf-8")
        except Exception:
            pass

    # ---------------- run/cancel ----------------
    def _on_run_clicked(self) -> None:
        if self.run_thread and self.run_thread.isRunning():
            QMessageBox.information(self, APP_TITLE, "A run is already in progress.")
            return

        blocks_sel = self._get_pipeline_blocks()
        prompt = self.prompt_text.toPlainText()
        extras_raw = self.extras_text.toPlainText()
        print_json = self.json_var.isChecked()
        model_name = self.model_combo.currentText()

        if not blocks_sel:
            QMessageBox.critical(self, APP_TITLE, "Pipeline is empty. Add blocks to run.")
            return
        if not prompt.strip():
            reply = QMessageBox.question(
                self,
                APP_TITLE,
                "Prompt is empty. Continue?",
                QMessageBox.Yes | QMessageBox.No,
                QMessageBox.No,
            )
            if reply == QMessageBox.No:
                return

        self._stop_event.clear()
        self._set_running(True)
        self._clear_outputs()
        self.statusBar().showMessage(f"Running {len(blocks_sel)} block(s)…")

        self.run_thread = QThread(self)
        self.worker = Worker(
            blocks_sel,
            prompt,
            extras_raw,
            print_json,
            self._stop_event,
            model_name,
        )
        self.worker.moveToThread(self.run_thread)

        self.run_thread.started.connect(self.worker.run)
        self.worker.status_update.connect(self.statusBar().showMessage)
        self.worker.finished.connect(self._display_run, Qt.QueuedConnection)

        self.worker.finished.connect(self.run_thread.quit)
        self.worker.finished.connect(self.worker.deleteLater)
        self.run_thread.finished.connect(self._on_thread_finished)
        self.run_thread.finished.connect(self.run_thread.deleteLater)

        self.run_thread.start()

    def _cancel_run(self) -> None:
        if self.run_thread and self.run_thread.isRunning():
            # If we already requested a cancel, try to terminate forcefullly
            if self._stop_event.is_set():
                reply = QMessageBox.question(
                    self,
                    "Force Stop?",
                    "The process is taking time to cancel gracefully. Force stop? (Data may be lost)",
                    QMessageBox.Yes | QMessageBox.No
                )
                if reply == QMessageBox.Yes:
                    self.run_thread.terminate()
                    self.run_thread.wait()
                    self._set_running(False)
                    self.statusBar().showMessage("Run forcibly terminated.")
                    self.result_text.appendPlainText("\n[System] Run forcibly terminated by user.")
                return

            # Standard Graceful Cancel
            self._stop_event.set()
            self.statusBar().showMessage("Stopping after current step finishes...")
            self.result_text.appendPlainText("\n[System] Cancellation requested. Finishing current batch...")

            # Optional: In newer Qt, this helps interrupt wait conditions
            self.run_thread.requestInterruption()
        else:
            self.statusBar().showMessage("Nothing to cancel.")

    def _set_running(self, running: bool) -> None:
        self.run_btn.setEnabled(not running)
        self.blocks_list.setEnabled(not running)
        self.pipeline_list.setEnabled(not running)
        self.preset_combo.setEnabled(not running)
        self.model_combo.setEnabled(not running)
        self.block_params_list.setEnabled(not running)
        self.prompt_text.setReadOnly(running)
        self.extras_text.setReadOnly(running)
        self.json_var.setEnabled(not running)
        self.save_preset_btn.setEnabled(not running)
        self.delete_preset_btn.setEnabled(not running)

    def _clear_outputs(self) -> None:
        self.result_text.clear()
        self.meta_text.clear()
        self.debug_text.clear()
        self.all_log_lines.clear()
    @pyqtSlot()
    def _on_thread_finished(self):
        self.run_thread = None
        self.worker = None

    @pyqtSlot(bool, str, dict)
    def _display_run(self, ok: bool, result: str, meta: Dict[str, Any]) -> None:
        self._set_running(False)
        self._save_state()
        self.statusBar().showMessage("Done" if ok else "Failed")
        self.result_text.setPlainText(result or "")
        try:
            meta_str = json.dumps(meta, indent=2, ensure_ascii=False)
            self.meta_text.setPlainText(meta_str)
        except Exception:
            self.meta_text.setPlainText("(no metadata)")
        if not ok:
            QMessageBox.critical(self, APP_TITLE, "Run failed — see Result tab for details.")

    # ---------------- misc ----------------
    def _save_result_as(self) -> None:
        content = self.result_text.toPlainText()
        if not content.strip():
            QMessageBox.information(self, APP_TITLE, "Nothing to save.")
            return
        path, _ = QFileDialog.getSaveFileName(
            self,
            "Save Result As…",
            "",
            "Text (*.txt);;Markdown (*.md);;JSON (*.json);;All files (*.*)",
        )
        if not path:
            return
        try:
            Path(path).write_text(content, encoding="utf-8")
            self.statusBar().showMessage(f"Saved: {path}")
        except Exception as e:
            QMessageBox.critical(self, APP_TITLE, f"Failed to save: {e}")

    def _show_about(self) -> None:
        QMessageBox.information(
            self,
            APP_TITLE,
            "PromptChat GUI (Pipeline Builder)\n\n"
            "- Use Presets dropdown for quickstarts.\n"
            "- Add blocks from 'Available' to 'Pipeline Stages'.\n"
            "- Reorder the pipeline with Up/Down.\n"
            "- Click a block to see its params.\n"
            "- Select a model in the dropdown to see its params.\n"
            "- Double-click a param to add it to the --extra box.\n"
            "- Use 'Save Preset…' to store your current pipeline/model/extras.\n"
            "- Use 'Delete Preset' to remove a saved preset.",
        )

    def closeEvent(self, event):
        if self.run_thread and self.run_thread.isRunning():
            self._stop_event.set()
            self.run_thread.requestInterruption()
            self.run_thread.quit()
            if not self.run_thread.wait(5000):
                self.run_thread.terminate()
                self.run_thread.wait(1000)
        event.accept()


def main() -> int:
    QApplication.setAttribute(Qt.AA_EnableHighDpiScaling, True)
    QApplication.setAttribute(Qt.AA_UseHighDpiPixmaps, True)

    app = QApplication(sys.argv)

    # 🔹 Make sure our global logger lives in the Qt main thread
    DEBUG_LOGGER.moveToThread(app.thread())

    window = PromptChatGUI()
    window.show()
    return app.exec_()

if __name__ == "__main__":
    project_root = Path(__file__).resolve().parent
    if str(project_root) not in sys.path:
        sys.path.insert(0, str(project_root))

    try:
        import blocks
        import pipeline
        from registry import BLOCKS
        import models
        from models import _MODELS, get_chat_model
    except ImportError as e:
        print(f"CRITICAL ERROR: Could not import project files: {e}", file=sys.stderr)
        print("Please ensure gui.py is in the same directory as blocks.py and registry.py.", file=sys.stderr)
        print("You may need to run: pip install -r requirements.txt", file=sys.stderr)
        sys.exit(1)

    raise SystemExit(main())
