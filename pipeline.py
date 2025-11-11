# ========================================================
# ================  pipeline.py  =========================
# ========================================================
from __future__ import annotations
from dataclasses import dataclass, field
from typing import Any, Dict, Tuple, List
import sys as _sys

from registry import BLOCKS
import blocks  # for parse_extras


@dataclass
class ChatPipelineBlock(blocks.BaseBlock):
    _meta_chain: List[Dict[str, Any]] = field(default_factory=list)

    def _all_extras(self) -> Dict[str, Dict[str, Any]]:
        extras_raw: List[str] = []
        argv = _sys.argv[1:]
        i = 0
        while i < len(argv):
            tok = argv[i]
            if tok == "--extra" and i + 1 < len(argv):
                extras_raw.append(argv[i + 1])
                i += 2
            else:
                i += 1
        return blocks.parse_extras(extras_raw)

    def _stage_params(self, stage: str, global_extras: Dict[str, Dict[str, Any]]) -> Dict[str, Any]:
        merged: Dict[str, Any] = {}
        merged.update(global_extras.get("all", {}))
        merged.update(global_extras.get(stage.lower(), {}))
        return merged

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        stages_str = params.get("stages") or params.get("pipeline") or params.get("pipe")
        if not isinstance(stages_str, str) or not stages_str.strip():
            raise ValueError("Missing pipeline.stages. Example: --extra pipeline.stages='corpus|chat'")
        stages = [s for s in stages_str.split("|") if s.strip()]
        if not stages:
            raise ValueError("Empty pipeline.stages.")

        all_extras = self._all_extras()
        current = payload
        self._meta_chain.clear()
        for s in stages:
            blk = BLOCKS.create(s)
            stage_params = self._stage_params(s, all_extras)
            current, meta = blk.execute(current, params=stage_params)
            self._meta_chain.append({"stage": s, **(meta or {})})

        out = current if isinstance(current, str) else str(current)
        return out, {"type": "chat-pipeline", "stages": stages, "chain": self._meta_chain}


BLOCKS.register("pipeline", ChatPipelineBlock)
