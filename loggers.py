from PyQt5.QtCore import pyqtSignal, QObject


class DebugLogger(QObject):
    """
    Global Qt-based debug logger.

    Usage (anywhere in your code, including blocks.py):

        from debug_logger import get_debug_logger

        log = get_debug_logger()
        if log:
            log.log_message("[LinkTracker] starting crawl...")

    The GUI will hook this logger to a Debug Log pane.
    """
    message_signal = pyqtSignal(str)

    def __init__(self):
        super().__init__()

    def log_message(self, msg: str):
        self.message_signal.emit(str(msg).rstrip())


DEBUG_LOGGER = DebugLogger()

