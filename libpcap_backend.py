import ctypes
import os
import time
from dataclasses import dataclass
from typing import Any, Optional, Dict, List


@dataclass
class   LibpcapCtypesBackend:
    """
    Minimal ctypes-backed libpcap wrapper for passive capture.

    Supported modes:
      - live capture from interface via open_live(...)
      - offline capture from .pcap/.pcapng via open_offline(...)

    Exposes normalized packet dictionaries to NetworkTrackerBlock.
    """

    timeout_ms: int = 250
    snaplen: int = 65535
    promisc: bool = True
    logger: Any = None

    def __post_init__(self) -> None:
        self.lib = None
        self.handle = None
        self._errbuf = ctypes.create_string_buffer(256)
        self._load_library()

    def _log(self, msg: str) -> None:
        try:
            if self.logger is not None:
                self.logger.log_message(f"[LibpcapBackend] {msg}")
        except Exception:
            pass

    def _load_library(self) -> None:
        candidates: List[str] = []

        try:
            for name in ("pcap", "wpcap"):
                libname = ctypes.util.find_library(name)
                if libname:
                    candidates.append(libname)
        except Exception:
            pass

        # Windows / Npcap / WinPcap common names and locations
        candidates.extend([
            "wpcap.dll",
            "Packet.dll",
            os.path.join(os.environ.get("SystemRoot", r"C:\Windows"), "System32", "Npcap", "wpcap.dll"),
            os.path.join(os.environ.get("SystemRoot", r"C:\Windows"), "System32", "wpcap.dll"),

            # Linux/macOS fallbacks
            "libpcap.so",
            "libpcap.so.1",
            "/usr/lib/libpcap.so",
            "/usr/lib/x86_64-linux-gnu/libpcap.so",
            "/usr/local/lib/libpcap.so",
            "libpcap.dylib",
        ])

        # de-dupe while preserving order
        seen = set()
        ordered: List[str] = []
        for c in candidates:
            s = str(c or "").strip()
            if not s or s in seen:
                continue
            seen.add(s)
            ordered.append(s)

        last_err: Optional[Exception] = None
        for candidate in ordered:
            try:
                self.lib = ctypes.CDLL(candidate)
                self._bind()
                self._log(f"Loaded libpcap library: {candidate}")
                return
            except Exception as e:
                last_err = e
                continue

        raise RuntimeError(f"Unable to load libpcap/wpcap via ctypes: {last_err}")

        raise RuntimeError(f"Unable to load libpcap/wpcap via ctypes: {last_err}")

    def _bind(self) -> None:
        class PcapPkthdr(ctypes.Structure):
            _fields_ = [
                ("ts_sec", ctypes.c_long),
                ("ts_usec", ctypes.c_long),
                ("caplen", ctypes.c_uint32),
                ("len", ctypes.c_uint32),
            ]

        self.PcapPkthdr = PcapPkthdr

        self.lib.pcap_open_live.argtypes = [
            ctypes.c_char_p,
            ctypes.c_int,
            ctypes.c_int,
            ctypes.c_int,
            ctypes.c_char_p,
        ]
        self.lib.pcap_open_live.restype = ctypes.c_void_p

        self.lib.pcap_open_offline.argtypes = [ctypes.c_char_p, ctypes.c_char_p]
        self.lib.pcap_open_offline.restype = ctypes.c_void_p

        self.lib.pcap_close.argtypes = [ctypes.c_void_p]
        self.lib.pcap_close.restype = None

        self.lib.pcap_datalink.argtypes = [ctypes.c_void_p]
        self.lib.pcap_datalink.restype = ctypes.c_int

        self.lib.pcap_next_ex.argtypes = [
            ctypes.c_void_p,
            ctypes.POINTER(ctypes.POINTER(PcapPkthdr)),
            ctypes.POINTER(ctypes.POINTER(ctypes.c_ubyte)),
        ]
        self.lib.pcap_next_ex.restype = ctypes.c_int

        if hasattr(self.lib, "pcap_geterr"):
            self.lib.pcap_geterr.argtypes = [ctypes.c_void_p]
            self.lib.pcap_geterr.restype = ctypes.c_char_p

    def open_live(self, iface: str) -> None:
        self.close()
        handle = self.lib.pcap_open_live(
            iface.encode("utf-8", "ignore"),
            int(self.snaplen),
            1 if self.promisc else 0,
            int(self.timeout_ms),
            self._errbuf,
        )
        if not handle:
            raise RuntimeError(self._errbuf.value.decode("utf-8", "ignore") or "pcap_open_live failed")
        self.handle = handle
        self._log(f"Opened live capture on iface={iface!r}")

    def open_offline(self, path: str) -> None:
        self.close()
        handle = self.lib.pcap_open_offline(path.encode("utf-8", "ignore"), self._errbuf)
        if not handle:
            raise RuntimeError(self._errbuf.value.decode("utf-8", "ignore") or "pcap_open_offline failed")
        self.handle = handle
        self._log(f"Opened offline capture path={path!r}")

    def datalink(self) -> Optional[int]:
        if not self.handle:
            return None
        try:
            return int(self.lib.pcap_datalink(self.handle))
        except Exception:
            return None

    def get_error(self) -> str:
        if not self.handle or not hasattr(self.lib, "pcap_geterr"):
            return ""
        try:
            p = self.lib.pcap_geterr(self.handle)
            return p.decode("utf-8", "ignore") if p else ""
        except Exception:
            return ""

    def next_packet(self) -> Optional[Dict[str, Any]]:
        if not self.handle:
            return None

        hdr_ptr = ctypes.POINTER(self.PcapPkthdr)()
        data_ptr = ctypes.POINTER(ctypes.c_ubyte)()
        rc = self.lib.pcap_next_ex(self.handle, ctypes.byref(hdr_ptr), ctypes.byref(data_ptr))

        if rc == 1 and hdr_ptr and data_ptr:
            hdr = hdr_ptr.contents
            raw = ctypes.string_at(data_ptr, int(hdr.caplen))
            ts = float(hdr.ts_sec) + (float(hdr.ts_usec) / 1_000_000.0)
            return {
                "timestamp": ts,
                "caplen": int(hdr.caplen),
                "wirelen": int(hdr.len),
                "raw_bytes": raw,
                "datalink": self.datalink(),
            }
        if rc in (0, -2):
            return None
        if rc == -1:
            raise RuntimeError(self.get_error() or "pcap_next_ex failed")
        return None

    def collect(self, *, max_packets: int = 128, budget_s: float = 2.0) -> List[Dict[str, Any]]:
        out: List[Dict[str, Any]] = []
        deadline = time.time() + max(0.05, float(budget_s))
        while len(out) < int(max_packets) and time.time() < deadline:
            pkt = self.next_packet()
            if pkt is None:
                continue
            out.append(pkt)
        self._log(f"Collected {len(out)} packets from libpcap backend")
        return out

    def close(self) -> None:
        if self.handle:
            try:
                self.lib.pcap_close(self.handle)
            except Exception:
                pass
            self.handle = None