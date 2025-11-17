# ========================================================
# ================  gui.py  (Thread Fix) =================
# ========================================================
from __future__ import annotations

import glob
import json
import os
import pathlib
import sys
import traceback
from pathlib import Path
from typing import Any, Dict, List, Optional
import threading
# Import ALL blocks eagerly in the main thread.
import blocks
import pipeline  # Ensure pipeline is also registered
from registry import BLOCKS

# [MODIFIED] Import models and _MODELS directly
import models
try:
    # This is what you requested: import the dictionary directly
    from models import _MODELS
except ImportError:
    print("WARNING: Could not import _MODELS from models.py. Using fallback.", file=sys.stderr)
    _MODELS = {"lexicon": None, "lexicon-adv": None} # Fallback

from PyQt5.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QListWidget, QPushButton, QCheckBox, QPlainTextEdit, QTabWidget,
    QStatusBar, QAction, QFileDialog, QListWidgetItem, QAbstractItemView,
    QGroupBox, QSplitter, QLabel, QMessageBox, QComboBox
)
from PyQt5.QtCore import QObject, pyqtSignal, QThread, pyqtSlot, Qt

APP_TITLE = "PromptChat GUI"
STATE_FILE = Path(".promptchat_gui_state.json")

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
# These are global presets that set the pipeline AND extras.
# ======================= PRESETS =========================================
def load_presets() -> List[Dict[str, Any]]:
    """
    Loads presets from 'presets.json' in the same directory.
    Returns a default empty preset if the file is missing or invalid.
    """
    default_preset = [{"name": "--- Select a Preset ---", "blocks": [], "extras": ""}]

    # Locate the JSON file relative to this script
    preset_path = Path(__file__).parent / "gui_presets.json"

    if preset_path.exists():
        try:
            with open(preset_path, "r", encoding="utf-8") as f:
                data = json.load(f)
                if isinstance(data, list):
                    return data
                else:
                    print("Warning: presets.json must contain a list.")
        except Exception as e:
            print(f"Error loading presets.json: {e}")
    else:
        print(f"Notice: presets.json not found at {preset_path}. Using default.")

    return default_preset


GUI_PRESETS = load_presets()


# ======================= WORKER THREAD ===================================

class Worker(QObject):
    finished = pyqtSignal(bool, str, dict)
    status_update = pyqtSignal(str)

    def __init__(self, blocks_sel: List[str], prompt: str, extras_raw: str, print_json: bool,
                 stop_event: threading.Event, model_name: str):
        super().__init__()
        self.blocks_sel = blocks_sel
        self.prompt = prompt
        self.extras_raw = extras_raw
        self.print_json = print_json
        self.stop_event = stop_event
        self.model_name = model_name  # Store the model name

    @pyqtSlot()
    def run(self):
        try:
            import blocks  # safe here too
            blocks.ensure_app_dirs()
            # --- New: payload-derived variables for presets ---
            prompt_str = self.prompt or ""
            # word-based length (for min_term_overlap, etc.)
            payload_word_len = len(prompt_str.split()) if prompt_str.strip() else 0
            # raw character length if you ever want it
            payload_char_len = len(prompt_str)

            extras_raw_substituted = (
                self.extras_raw
                # original behaviour
                .replace("{payload}", prompt_str)
                # NEW: word-count length (for min_term_overlap)
                .replace("{payload.length}", str(payload_word_len))
                .replace("{payload_len}", str(payload_word_len))  # alias, optional
                # Optional: expose char length too if you want later
                .replace("{payload.char_length}", str(payload_char_len))
            )
            extras_list = [ln.strip() for ln in extras_raw_substituted.splitlines() if ln.strip()]
            extras = blocks.parse_extras(extras_list)

            if self.model_name:
                extras.setdefault("chat", {})["model"] = self.model_name
                extras.setdefault("pipeline", {})["chat.model"] = self.model_name

            results_md: List[str] = []
            results_json: List[Dict[str, Any]] = []
            combined_meta: Dict[str, Any] = {"runs": []}

            # [NEW] We now track both the root and the chained payload
            root_payload = self.prompt
            current_payload = self.prompt

            for idx, block_name in enumerate(self.blocks_sel, 1):
                if self.stop_event.is_set():
                    self.status_update.emit("Cancelled.")
                    break

                self.status_update.emit(f"Running {idx}/{len(self.blocks_sel)}: {block_name}")

                # --- [NEW] Smart Parameter and Payload Logic ---
                block_key = block_name.lower()
                params: Dict[str, Any] = {}
                params.update(extras.get(block_key, {}))
                params.update(extras.get("all", {}))

                if block_name == "pipeline":
                    params["_gui_extras_passthrough"] = extras

                # Check for our new 'magic' parameter
                # Default behavior is 'chain'
                payload_source = params.pop("_payload_source", "chain")

                payload_to_use = root_payload if payload_source == "root" else current_payload
                # --- [END NEW] ---

                blk = BLOCKS.create(block_name)
                try:
                    # Use the payload we selected (root or chain)
                    result, meta = blk.execute(payload_to_use, params=params)

                    # --- [NEW] Smart Chaining Logic ---
                    if payload_source == "root":
                        # This block ran on the root payload.
                        # We assume its result is *additive* and should be appended.
                        # We must strip the root payload from its result to avoid duplication.
                        if result.startswith(root_payload):
                            additive_result = result[len(root_payload):].strip()
                            if additive_result:
                                current_payload = current_payload + "\n\n" + additive_result
                        else:
                            # Fallback: just append the whole thing if it didn't include the payload
                            # This happens if the block has inject_context=false
                            current_payload = current_payload + "\n\n" + result
                    else:
                        # This is the original behavior: replace the payload
                        current_payload = result
                    # --- [END NEW] ---

                    # The rest of the logging is the same, but we log the 'result'
                    # which may be different from the 'current_payload'
                    results_md.append(f"\n\n# ── {block_name} ─────────────────────────────────────\n{result}")
                    results_json.append({"block": block_name, "metadata": meta, "result": result})
                    combined_meta["runs"].append({"block": block_name, "metadata": meta})

                except Exception as e:
                    import traceback
                    tb = traceback.format_exc()
                    err_blob = f"[{block_name}] ERROR: {e}\n{tb}"
                    results_md.append(f"\n\n# ── {block_name} (ERROR) ───────────────────────────\n{err_blob}")
                    results_json.append({"block": block_name, "error": str(e), "traceback": tb})
                    combined_meta["runs"].append({"block": block_name, "error": str(e)})
                    self.status_update.emit(f"Failed on block '{block_name}'. Stopping pipeline.")
                    break

            # --- [NEW] FINAL OUTPUT FORMATTING LOGIC ---

            # Check for the new magic flag in the "all" section of extras
            final_output_only = extras.get("all", {}).get("final_output_only", False)

            if self.print_json:
                out = json.dumps(results_json, indent=2, ensure_ascii=False)
            elif final_output_only:
                # User *only* wants the final, clean payload
                out = current_payload
            else:
                # This is the original behavior (full log)
                out = f"--- FINAL OUTPUT ---\n{current_payload}\n\n--- RUN LOG ---\n" + "".join(
                    results_md).lstrip()
            # --- [END NEW] ---
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

        self._build_menu()
        self._build_body()
        self._refresh_block_list()
        self._load_state()

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

        help_menu = menu.addMenu("Help")
        about_action = QAction("About", self)
        about_action.triggered.connect(self._show_about)
        help_menu.addAction(about_action)

    def _build_body(self) -> None:
        main_widget = QWidget()
        self.setCentralWidget(main_widget)
        root_layout = QVBoxLayout(main_widget)

        # --- Top-level Vertical Splitter ---
        top_level_splitter = QSplitter(Qt.Vertical)
        root_layout.addWidget(top_level_splitter, 1)

        # --- Top Section: Block Selection ---
        top = QGroupBox("Build Pipeline")
        top_layout = QHBoxLayout(top)
        top_level_splitter.addWidget(top)

        # Left: Available Blocks
        available_layout = QVBoxLayout()
        available_layout.addWidget(QLabel("Available Blocks"))
        self.blocks_list = QListWidget()
        self.blocks_list.setSelectionMode(QAbstractItemView.SingleSelection)
        self.blocks_list.itemDoubleClicked.connect(self._add_block_to_pipeline)
        self.blocks_list.currentItemChanged.connect(self._on_block_selected)
        available_layout.addWidget(self.blocks_list)
        top_layout.addLayout(available_layout, 1)

        # Middle: Add/Remove Buttons
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

        # Right: Pipeline Stages
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

        # Right-most: Parameter Info Box & Run Controls
        right_controls_layout = QVBoxLayout()

        right_controls_layout.addWidget(QLabel("Presets"))
        self.preset_combo = QComboBox()
        for preset in GUI_PRESETS:
            self.preset_combo.addItem(preset["name"])
        self.preset_combo.currentIndexChanged.connect(self._on_preset_selected)
        right_controls_layout.addWidget(self.preset_combo)

        # Chat Model Selector
        right_controls_layout.addWidget(QLabel("Chat Model (for 'chat' block)"))
        self.model_combo = QComboBox()
        self.model_combo.addItems(sorted(_MODELS.keys()))
        right_controls_layout.addWidget(self.model_combo)

        right_controls_layout.addWidget(QLabel("Block Parameters (Double-click to add)"))
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

        # --- Bottom Widget (to hold the other splitters) ---
        bottom_widget = QWidget()
        bottom_layout = QVBoxLayout(bottom_widget)
        bottom_layout.setContentsMargins(0, 0, 0, 0)
        top_level_splitter.addWidget(bottom_widget)

        # --- Middle Section: Prompt + Extras ---
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

        # --- Bottom Section: Output Tabs ---
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

        top_level_splitter.setSizes([250, 550])

        # --- Status Bar ---
        self.setStatusBar(QStatusBar())
        self.statusBar().showMessage("Ready")

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
            if row <= 0: return
            selected_rows = [row]

        if selected_rows[0] == 0: return

        for row in selected_rows:
            item = self.pipeline_list.takeItem(row)
            self.pipeline_list.insertItem(row - 1, item)
            item.setSelected(True)
        if self.pipeline_list.selectedItems():
            self.pipeline_list.scrollToItem(self.pipeline_list.selectedItems()[0])

    def _move_down(self) -> None:
        selected_rows = sorted([self.pipeline_list.row(item) for item in self.pipeline_list.selectedItems()],
                               reverse=True)
        if not selected_rows:
            row = self.pipeline_list.count() - 1
            if row < 0 or row == self.pipeline_list.count() - 1: return
            selected_rows = [row]

        if selected_rows[0] == self.pipeline_list.count() - 1: return

        for row in selected_rows:
            item = self.pipeline_list.takeItem(row)
            self.pipeline_list.insertItem(row + 1, item)
            item.setSelected(True)
        if self.pipeline_list.selectedItems():
            self.pipeline_list.scrollToItem(self.pipeline_list.selectedItems()[-1])

    @pyqtSlot(QListWidgetItem, QListWidgetItem)
    def _on_block_selected(self, current_item: QListWidgetItem, previous_item: QListWidgetItem):
        """Called when the user clicks a block in the 'Available Blocks' list."""
        self.block_params_list.clear()

        if not current_item:
            self.block_params_list.addItem("Select a block to see params.")
            return

        block_name = current_item.text()
        try:
            block_instance = BLOCKS.create(block_name)
            params_info = block_instance.get_params_info()

            if not params_info:
                self.block_params_list.addItem(f"No parameters for {block_name}")
                return

            # [MODIFIED] Add hint for pipeline delegation
            if block_name == "pipeline":
                self.block_params_list.addItem("--- (Use 'pipeline.block.param=val') ---")

            for key, value in params_info.items():
                item_str = f"{key}={json.dumps(value)}"
                self.block_params_list.addItem(item_str)

        except Exception as e:
            self.block_params_list.addItem(f"Error loading params:\n{e}")

    @pyqtSlot()
    def _add_param_to_extras(self):
        """Adds the selected param to the --extra text box."""
        block_name = ""
        current_block_item = self.blocks_list.currentItem()
        if current_block_item:
            block_name = current_block_item.text().lower()

        selected_item = self.block_params_list.currentItem()
        if not selected_item:
            return

        item_str = selected_item.text()
        text_to_add = ""

        if "=" in item_str and " " not in item_str:
            # [MODIFIED] Check if we are adding a param for a block *inside* a pipeline
            current_pipeline = self._get_pipeline_blocks()
            if len(current_pipeline) == 1 and current_pipeline[0] == "pipeline":
                # We are in pipeline mode, so prefix the param
                text_to_add = f"pipeline.{block_name}.{item_str}"
            else:
                # We are in manual block mode
                text_to_add = f"{block_name}.{item_str}"

        if text_to_add:
            current_extras = self.extras_text.toPlainText()
            if current_extras and not current_extras.endswith("\n"):
                self.extras_text.appendPlainText("\n")
            self.extras_text.appendPlainText(text_to_add)
            self.extras_text.centerCursor()

    @pyqtSlot(int)
    def _on_preset_selected(self, index: int):
        """Called when the user selects a preset from the main dropdown."""
        # [FIX] Clear the form if user selects index 0
        if index == 0:
            # Check if the list is already clear to prevent needless signals
            if self.pipeline_list.count() > 0 or self.extras_text.toPlainText():
                self.pipeline_list.clear()
                self.extras_text.clear()
                self.statusBar().showMessage("Cleared pipeline and extras.")
            return

        preset = GUI_PRESETS[index]

        self.pipeline_list.clear()
        self.pipeline_list.addItems(preset["blocks"])

        extras_text = (preset["extras"] or "").strip()
        self.extras_text.setPlainText(extras_text)

        # [FIX] Block signals while resetting the index to prevent re-triggering
        self.preset_combo.blockSignals(True)
        self.preset_combo.setCurrentIndex(0)
        self.preset_combo.blockSignals(False)

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

                # Load model selection
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
                "model_name": self.model_combo.currentText(),  # Save model
            }
            STATE_FILE.write_text(json.dumps(data, indent=2), encoding="utf-8")
        except Exception:
            pass

    # ---------------- run/cancel ----------------
    def _on_run_clicked(self) -> None:
        # If a previous run is still alive, don’t start a new one
        if self.run_thread and self.run_thread.isRunning():
            QMessageBox.information(self, APP_TITLE, "A run is already in progress.")
            return

        blocks_sel = self._get_pipeline_blocks()
        prompt = self.prompt_text.toPlainText()
        extras_raw = self.extras_text.toPlainText()
        print_json = self.json_var.isChecked()
        model_name = self.model_combo.currentText()  # Get model

        if not blocks_sel:
            QMessageBox.critical(self, APP_TITLE, "Pipeline is empty. Add blocks to run.")
            return
        if not prompt.strip():
            reply = QMessageBox.question(self, APP_TITLE, "Prompt is empty. Continue?",
                                         QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
            if reply == QMessageBox.No:
                return

        # Reset stop flag and UI
        self._stop_event.clear()
        self._set_running(True)
        self._clear_outputs()
        self.statusBar().showMessage(f"Running {len(blocks_sel)} block(s)…")

        # Create thread WITH PARENT so Qt manages lifetime safely
        self.run_thread = QThread(self)
        self.worker = Worker(blocks_sel, prompt, extras_raw, print_json, self._stop_event, model_name)  # Pass model
        self.worker.moveToThread(self.run_thread)

        # Wire signals
        self.run_thread.started.connect(self.worker.run)
        self.worker.status_update.connect(self.statusBar().showMessage)
        self.worker.finished.connect(self._display_run, Qt.QueuedConnection)

        # Proper shutdown: when worker is done, stop the thread event loop,
        # delete worker, THEN when the thread actually finishes, clean references
        self.worker.finished.connect(self.run_thread.quit)
        self.worker.finished.connect(self.worker.deleteLater)
        self.run_thread.finished.connect(self._on_thread_finished)
        self.run_thread.finished.connect(self.run_thread.deleteLater)

        self.run_thread.start()

    def _cancel_run(self) -> None:
        if self.run_thread and self.run_thread.isRunning():
            self._stop_event.set()  # ask worker to stop between blocks
            self.statusBar().showMessage("Cancel requested…")
            # Also ask the thread event loop to quit once the current slot returns
            self.run_thread.requestInterruption()
            # We DO NOT quit() here; worker.finished will quit() after run() returns
        else:
            self.statusBar().showMessage("Nothing to cancel.")

    def _set_running(self, running: bool) -> None:
        self.run_btn.setEnabled(not running)
        self.blocks_list.setEnabled(not running)
        self.pipeline_list.setEnabled(not running)
        self.preset_combo.setEnabled(not running)
        self.model_combo.setEnabled(not running)  # Disable model combo
        self.block_params_list.setEnabled(not running)
        self.prompt_text.setReadOnly(running)
        self.extras_text.setReadOnly(running)
        self.json_var.setEnabled(not running)

    def _clear_outputs(self) -> None:
        self.result_text.clear()
        self.meta_text.clear()

    @pyqtSlot()
    def _on_thread_finished(self):
        # Now the thread has fully stopped; safe to clear references
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
            self, "Save Result As…", "",
            "Text (*.txt);;Markdown (*.md);;JSON (*.json);;All files (*.*)"
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
            "- Click a block to see params; double-click to add.\n"
            "- Output of one block is the input for the next."
        )

    def closeEvent(self, event):
        if self.run_thread and self.run_thread.isRunning():
            self._stop_event.set()
            self.run_thread.requestInterruption()
            self.run_thread.quit()
            # Wait a bit longer to avoid the fatal
            if not self.run_thread.wait(5000):
                # Last resort (not ideal, but prevents fatal on exit)
                self.run_thread.terminate()
                self.run_thread.wait(1000)
        event.accept()


def main() -> int:
    QApplication.setAttribute(Qt.AA_EnableHighDpiScaling, True)
    QApplication.setAttribute(Qt.AA_UseHighDpiPixmaps, True)

    app = QApplication(sys.argv)
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
        import models  # Import models
        from models import _MODELS  # [MODIFIED] Import _MODELS directly
    except ImportError as e:
        print(f"CRITICAL ERROR: Could not import project files: {e}", file=sys.stderr)
        print("Please ensure gui.py is in the same directory as blocks.py and registry.py.", file=sys.stderr)
        print("You may need to run: pip install -r requirements.txt", file=sys.stderr)
        sys.exit(1)

    raise SystemExit(main())