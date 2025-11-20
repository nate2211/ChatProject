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
        """Filters rows by substring match across all columns."""
        self.current_filter = text.lower()

        self.layoutAboutToBeChanged.emit()
        if not text:
            self.filtered_rows = self.data_rows[:]
            self.filtered_rowids = self.rowids[:]
        else:
            new_rows: List[List[Any]] = []
            new_rowids: List[int] = []
            for row, rid in zip(self.data_rows, self.rowids):
                if any(text in str(cell).lower() for cell in row):
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

        layout = QVBoxLayout(self)

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
        self.table_view.setSortingEnabled(True)  # enable column sorting
        # Row-based selection, multi-select
        self.table_view.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.table_view.setSelectionMode(QAbstractItemView.ExtendedSelection)
        layout.addWidget(self.table_view)

        # Resize behavior
        header = self.table_view.horizontalHeader()
        header.setSectionResizeMode(QHeaderView.Interactive)  # manual resizing
        header.setStretchLastSection(True)

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

    # --- Search ---
    def _apply_search_filter(self, text: str):
        if self.db_model:
            self.db_model.apply_filter(text)
            # re-apply current sort after filter change
            self._apply_sort()

    # --- Sort via dropdowns ---
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
        """
        Populate the 'Sort by' combo with column headers from the model.
        """
        self.sort_column_combo.blockSignals(True)
        self.sort_column_combo.clear()

        if self.db_model and self.db_model.headers:
            for idx, name in enumerate(self.db_model.headers):
                self.sort_column_combo.addItem(name, idx)
            self.sort_column_combo.setCurrentIndex(0)
        self.sort_column_combo.blockSignals(False)

    # --- Helper: find URL column ---
    def _url_column_index(self) -> int:
        """
        Return the column index for the 'url' column (case-insensitive),
        or -1 if not found.
        """
        if not self.db_model or not self.db_model.headers:
            return -1
        for i, h in enumerate(self.db_model.headers):
            if str(h).lower() == "url":
                return i
        return -1

    # --- Copy URL(s) ---
    def _copy_selected_urls(self):
        if not self.db_model:
            return

        url_col = self._url_column_index()
        if url_col < 0:
            QMessageBox.warning(
                self,
                self.app_title,
                "No 'url' column found in this table.",
            )
            return

        selection_model = self.table_view.selectionModel()
        if not selection_model:
            return

        # Collect unique selected row indices in view coords
        selected_rows = sorted({idx.row() for idx in selection_model.selectedRows()})
        if not selected_rows:
            # if user has cells selected but not whole row, fallback to all indexes
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
            QMessageBox.information(
                self,
                self.app_title,
                "No URLs found in selected rows.",
            )
            return

        clip = QApplication.clipboard()
        clip.setText("\n".join(urls))

        QMessageBox.information(
            self,
            self.app_title,
            f"Copied {len(urls)} URL{'s' if len(urls) != 1 else ''} to clipboard.",
        )

    # --- Delete ---
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

        # Re-apply sort so the view stays consistent with dropdown
        self._apply_sort()
        # Resize columns again if you like
        self.table_view.resizeColumnsToContents()

    # --- Public API ---
    def load_database(self, file_path: str) -> bool:
        """
        Loads the database and displays the first table in the DB.
        """
        try:
            conn = sqlite3.connect(file_path)
            cursor = conn.cursor()

            cursor.execute("SELECT name FROM sqlite_master WHERE type='table';")
            tables = cursor.fetchall()
            conn.close()

            if not tables:
                QMessageBox.warning(self, self.app_title, "No tables found in the database.")
                return False

            table_name = tables[0][0]  # load first table

            # Build the model
            self.db_model = SQLiteTableModel(file_path, table_name)
            self.table_view.setModel(self.db_model)

            # Populate sort dropdown with column names
            self._populate_sort_columns()

            # Initial sort: first column ascending
            if self.db_model.headers:
                self.table_view.sortByColumn(0, Qt.AscendingOrder)

            # Resize to content once
            self.table_view.resizeColumnsToContents()

            return True

        except Exception as e:
            QMessageBox.critical(self, self.app_title, f"Error loading database: {e}")
            return False
