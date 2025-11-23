# ========================================================
# ============ gui_elements.py (Database Pane) ===========
# ========================================================
from __future__ import annotations

from typing import List, Any

import sqlite3

from PyQt5.QtWidgets import (
    QWidget,
    QVBoxLayout,
    QHBoxLayout,
    QTableView,
    QHeaderView,
    QAbstractScrollArea,
    QMessageBox,
    QLineEdit,
    QComboBox,
    QLabel,
    QPushButton,
    QApplication,
    QAbstractItemView,
)
from PyQt5.QtCore import (
    Qt,
    QAbstractTableModel,
    QModelIndex,
)


class SQLiteTableModel(QAbstractTableModel):
    """
    A TableModel that uses an SQLite database as its data source.
    Supports sorting, filtering, and row deletion.
    """

    def __init__(self, db_path: str, table_name: str):
        super().__init__()
        self.db_path = db_path
        self.table_name = table_name
        self.headers: List[str] = []
        self.data_rows: List[List[Any]] = []

        # Underlying row IDs (SQLite rowid)
        self.rowids: List[int] = []

        # Filtering
        self.filtered_rows: List[List[Any]] = []
        self.filtered_rowids: List[int] = []
        self.current_filter: str = ""

        self._load_data()

    def _load_data(self):
        """Loads the data from the SQLite database."""
        try:
            conn = sqlite3.connect(self.db_path)
            cursor = conn.cursor()

            # Fetch column names (ignore rowid)
            cursor.execute(f"PRAGMA table_info({self.table_name})")
            self.headers = [row[1] for row in cursor.fetchall()]

            # Fetch rowid + all data
            cursor.execute(f"SELECT rowid, * FROM {self.table_name}")
            rows = cursor.fetchall()
            conn.close()

            self.rowids = [r[0] for r in rows]
            # Strip rowid column from displayed data
            self.data_rows = [list(r[1:]) for r in rows]

            # Start with unfiltered rows
            self.filtered_rows = self.data_rows[:]
            self.filtered_rowids = self.rowids[:]

        except Exception as e:
            print(f"Error loading data from SQLite: {e}")
            self.headers = ["Error"]
            self.data_rows = [[str(e)]]
            self.rowids = []
            self.filtered_rows = self.data_rows[:]
            self.filtered_rowids = self.rowids[:]

    # ---------- Qt Model API ----------

    def rowCount(self, parent=QModelIndex()) -> int:
        return len(self.filtered_rows)

    def columnCount(self, parent=QModelIndex()) -> int:
        return len(self.headers)

    def data(self, index, role=Qt.DisplayRole):
        if not index.isValid():
            return None
        if role == Qt.DisplayRole:
            return str(self.filtered_rows[index.row()][index.column()])
        return None

    def headerData(self, section, orientation, role=Qt.DisplayRole):
        if orientation == Qt.Horizontal and role == Qt.DisplayRole:
            return self.headers[section]
        return None

    # ---------- Sorting ----------
    def sort(self, column: int, order: Qt.SortOrder):
        self.layoutAboutToBeChanged.emit()
        reverse = order == Qt.DescendingOrder
        # sort rows and rowids in lockstep
        combined = list(zip(self.filtered_rows, self.filtered_rowids))
        combined.sort(key=lambda pair: pair[0][column], reverse=reverse)
        self.filtered_rows, self.filtered_rowids = map(list, zip(*combined)) if combined else ([], [])
        self.layoutChanged.emit()

    def flags(self, index):
        # read-only table, but selectable
        return Qt.ItemIsSelectable | Qt.ItemIsEnabled

    # ---------- Filtering ----------
    def apply_filter(self, text: str):
        """Filters rows by substring match across all columns (incl. url)."""
        needle = (text or "").strip().lower()
        self.current_filter = needle

        self.layoutAboutToBeChanged.emit()
        if not needle:
            self.filtered_rows = self.data_rows[:]
            self.filtered_rowids = self.rowids[:]
        else:
            new_rows: List[List[Any]] = []
            new_rowids: List[int] = []
            for row, rid in zip(self.data_rows, self.rowids):
                # case-insensitive match across ALL columns including 'url'
                if any(needle in str(cell).lower() for cell in row):
                    new_rows.append(row)
                    new_rowids.append(rid)

            self.filtered_rows = new_rows
            self.filtered_rowids = new_rowids

        self.layoutChanged.emit()

    # ---------- Deletion ----------
    def delete_rows(self, view_rows: List[int]) -> None:
        """
        Delete the given view row indices from the underlying SQLite table.
        view_rows are indices into filtered_rows.
        """
        if not view_rows:
            return

        # Map view rows -> rowids
        unique_rows = sorted(set(view_rows))
        rowids_to_delete = []
        for r in unique_rows:
            if 0 <= r < len(self.filtered_rowids):
                rowids_to_delete.append(self.filtered_rowids[r])

        if not rowids_to_delete:
            return

        try:
            conn = sqlite3.connect(self.db_path)
            cur = conn.cursor()
            placeholders = ",".join("?" for _ in rowids_to_delete)
            cur.execute(
                f"DELETE FROM {self.table_name} WHERE rowid IN ({placeholders})",
                rowids_to_delete,
            )
            conn.commit()
            conn.close()
        except Exception as e:
            print(f"Error deleting rows from SQLite: {e}")
            return

        # Reload data and reapply filter
        self.beginResetModel()
        self._load_data()
        self.endResetModel()

        if self.current_filter:
            # this will emit layout signals
            self.apply_filter(self.current_filter)


class DatabasePane(QWidget):
    """
    Reusable database pane widget with:
    - Table selector (shows ALL tables in the DB)
    - Sorting (via header + dropdowns)
    - Searching (filter)
    - Resizable columns
    - Delete selected entries
    - Copy URL(s) from selected rows
    """

    def __init__(self, app_title: str = "Database Viewer", parent=None):
        super().__init__(parent)
        self.app_title = app_title

        self.db_model: SQLiteTableModel | None = None
        self.db_path_loaded: str | None = None
        self.tables_loaded: List[str] = []

        layout = QVBoxLayout(self)

        # ---------- Table Selector ----------
        table_row = QHBoxLayout()
        table_label = QLabel("Table:")
        self.table_combo = QComboBox()
        self.table_combo.currentIndexChanged.connect(self._switch_table)

        table_row.addWidget(table_label)
        table_row.addWidget(self.table_combo)
        table_row.addStretch()
        layout.addLayout(table_row)

        # ---------- Search Bar ----------
        self.search_bar = QLineEdit()
        self.search_bar.setPlaceholderText("Search...")
        self.search_bar.textChanged.connect(self._apply_search_filter)
        layout.addWidget(self.search_bar)

        # ---------- Sort Controls Row ----------
        sort_row = QHBoxLayout()

        sort_label = QLabel("Sort by:")
        self.sort_column_combo = QComboBox()
        self.sort_column_combo.currentIndexChanged.connect(self._apply_sort)

        order_label = QLabel("Order:")
        self.sort_order_combo = QComboBox()
        self.sort_order_combo.addItem("Ascending", Qt.AscendingOrder)
        self.sort_order_combo.addItem("Descending", Qt.DescendingOrder)
        self.sort_order_combo.currentIndexChanged.connect(self._apply_sort)

        sort_row.addWidget(sort_label)
        sort_row.addWidget(self.sort_column_combo)
        sort_row.addSpacing(16)
        sort_row.addWidget(order_label)
        sort_row.addWidget(self.sort_order_combo)
        sort_row.addStretch()

        layout.addLayout(sort_row)

        # ---------- Table View ----------
        self.table_view = QTableView()
        self.table_view.setSortingEnabled(True)
        self.table_view.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.table_view.setSelectionMode(QAbstractItemView.ExtendedSelection)

        # --- Smooth scrolling + better long-URL viewing ---
        # Per-pixel scroll feels "smooth" on wheels/trackpads
        self.table_view.setVerticalScrollMode(QAbstractItemView.ScrollPerPixel)
        self.table_view.setHorizontalScrollMode(QAbstractItemView.ScrollPerPixel)

        # Increase scroll step a bit so it doesn't feel sluggish
        self.table_view.verticalScrollBar().setSingleStep(24)
        self.table_view.horizontalScrollBar().setSingleStep(24)

        # Don't wrap cells; keep URLs on one line
        self.table_view.setWordWrap(False)

        # Don't truncate with "..."; allow horizontal scroll to reveal full text
        self.table_view.setTextElideMode(Qt.ElideNone)

        layout.addWidget(self.table_view)

        header = self.table_view.horizontalHeader()
        header.setSectionResizeMode(QHeaderView.Interactive)
        header.setStretchLastSection(False)
        self.table_view.setSizeAdjustPolicy(QAbstractScrollArea.AdjustToContents)

        # ---------- Action Buttons ----------
        buttons_row = QHBoxLayout()

        self.copy_url_button = QPushButton("Copy URL")
        self.copy_url_button.clicked.connect(self._copy_selected_urls)

        self.delete_button = QPushButton("Delete Selected")
        self.delete_button.clicked.connect(self._delete_selected_rows)

        buttons_row.addStretch()
        buttons_row.addWidget(self.copy_url_button)
        buttons_row.addWidget(self.delete_button)
        layout.addLayout(buttons_row)

    # ------------------------------------------------------------------
    # Internal helpers
    # ------------------------------------------------------------------

    def _fetch_tables(self, db_path: str) -> List[str]:
        """Return all table names in the SQLite database."""
        try:
            conn = sqlite3.connect(db_path)
            cur = conn.cursor()
            cur.execute("SELECT name FROM sqlite_master WHERE type='table';")
            tables = [t[0] for t in cur.fetchall()]
            conn.close()
            return tables
        except Exception as e:
            print(f"Error fetching tables: {e}")
            return []

    def _populate_table_list(self, tables: List[str]):
        """Fill the table selector dropdown with all tables."""
        self.table_combo.blockSignals(True)
        self.table_combo.clear()
        for t in tables:
            self.table_combo.addItem(t)
        self.table_combo.blockSignals(False)

    def _load_table(self, table_name: str):
        """Build and attach a model for table_name."""
        if not self.db_path_loaded:
            return
        if not table_name:
            return

        self.db_model = SQLiteTableModel(self.db_path_loaded, table_name)
        self.table_view.setModel(self.db_model)

        # refresh sort columns dropdown
        self._populate_sort_columns()

        # reset search box (optional, feels cleaner on table swap)
        self.search_bar.blockSignals(True)
        self.search_bar.setText("")
        self.search_bar.blockSignals(False)

        # initial sort + resize
        if self.db_model.headers:
            self.table_view.sortByColumn(0, Qt.AscendingOrder)
        self.table_view.resizeColumnsToContents()

    def _switch_table(self):
        """Triggered when table dropdown changes."""
        if not self.table_combo.count():
            return
        table_name = self.table_combo.currentText()
        self._load_table(table_name)

    # ------------------------------------------------------------------
    # Search / Sort
    # ------------------------------------------------------------------

    def _apply_search_filter(self, text: str):
        if self.db_model:
            self.db_model.apply_filter(text)
            self._apply_sort()

    def _apply_sort(self):
        if not self.db_model:
            return
        col_index = self.sort_column_combo.currentData()
        if col_index is None:
            return
        order = self.sort_order_combo.currentData()
        if order is None:
            order = Qt.AscendingOrder
        self.table_view.sortByColumn(col_index, order)

    def _populate_sort_columns(self):
        """Populate sort dropdown with current model headers."""
        self.sort_column_combo.blockSignals(True)
        self.sort_column_combo.clear()

        if self.db_model and self.db_model.headers:
            for idx, name in enumerate(self.db_model.headers):
                self.sort_column_combo.addItem(name, idx)
            self.sort_column_combo.setCurrentIndex(0)

        self.sort_column_combo.blockSignals(False)

    # ------------------------------------------------------------------
    # URL column helper
    # ------------------------------------------------------------------

    def _url_column_index(self) -> int:
        """Find 'url' column index (case-insensitive); -1 if missing."""
        if not self.db_model or not self.db_model.headers:
            return -1
        for i, h in enumerate(self.db_model.headers):
            if str(h).lower() == "url":
                return i
        return -1

    # ------------------------------------------------------------------
    # Copy URL(s)
    # ------------------------------------------------------------------

    def _copy_selected_urls(self):
        if not self.db_model:
            return

        url_col = self._url_column_index()
        if url_col >= 0:
            self.table_view.setColumnWidth(url_col, 520)
        if url_col < 0:
            QMessageBox.warning(self, self.app_title, "No 'url' column found in this table.")
            return

        selection_model = self.table_view.selectionModel()
        if not selection_model:
            return

        selected_rows = sorted({idx.row() for idx in selection_model.selectedRows()})
        if not selected_rows:
            indexes = selection_model.selectedIndexes()
            if not indexes:
                return
            selected_rows = sorted({idx.row() for idx in indexes})

        urls: List[str] = []
        for row in selected_rows:
            idx = self.db_model.index(row, url_col)
            val = self.db_model.data(idx, Qt.DisplayRole)
            if val:
                urls.append(str(val))

        if not urls:
            QMessageBox.information(self, self.app_title, "No URLs found in selected rows.")
            return

        QApplication.clipboard().setText("\n".join(urls))

        QMessageBox.information(
            self,
            self.app_title,
            f"Copied {len(urls)} URL{'s' if len(urls) != 1 else ''} to clipboard.",
        )

    # ------------------------------------------------------------------
    # Delete selected rows
    # ------------------------------------------------------------------

    def _delete_selected_rows(self):
        if not self.db_model:
            return

        selection_model = self.table_view.selectionModel()
        if not selection_model:
            return

        selected_indexes = selection_model.selectedIndexes()
        if not selected_indexes:
            return

        rows = sorted({idx.row() for idx in selected_indexes})

        reply = QMessageBox.question(
            self,
            self.app_title,
            f"Delete {len(rows)} selected entr{'y' if len(rows) == 1 else 'ies'}?",
            QMessageBox.Yes | QMessageBox.No,
            QMessageBox.No,
        )
        if reply != QMessageBox.Yes:
            return

        self.db_model.delete_rows(rows)

        self._apply_sort()
        self.table_view.resizeColumnsToContents()

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def load_database(self, file_path: str) -> bool:
        """
        Loads the database, populates the table dropdown,
        and loads the first table by default.
        """
        tables = self._fetch_tables(file_path)
        if not tables:
            QMessageBox.warning(self, self.app_title, "No tables found in the database.")
            return False

        self.db_path_loaded = file_path
        self.tables_loaded = tables

        self._populate_table_list(tables)

        # Load first table
        self._load_table(tables[0])
        return True