# ========================================================
# ================  pipeline.py  =========================
# ========================================================
from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from typing import Any, Dict, Tuple, List
import sys as _sys
import time

from registry import BLOCKS
import blocks  # for parse_extras


@dataclass
class ChatPipelineBlock(blocks.BaseBlock):
    """
    Orchestrates a sequence of registered blocks.

    - Stages are defined as a '|' separated string: "guard|tools|chat".
    - Per-stage params come from:
        1) global 'all' extras (all.*)
        2) stage-specific extras (e.g., pipeline.webcorpus.query=...)
    - Pipeline-level options (from 'pipeline' extras or direct params):
        * stages / pipeline / pipe : the stage string
        * stop_on_error (bool)    : stop when a stage raises or reports error
        * debug (bool)            : record in/out snippets in meta_chain
    """

    _meta_chain: List[Dict[str, Any]] = field(default_factory=list)

    # ---- extras helpers -------------------------------------------------

    def _get_all_extras(self, params: Dict[str, Any]) -> Dict[str, Dict[str, Any]]:
        """
        Gets the 'all_extras' dict.
        In GUI mode, it's passed via '_gui_extras_passthrough'.
        In CLI mode (fallback), it re-parses sys.argv.
        """
        if "_gui_extras_passthrough" in params:
            # GUI mode: The worker passed us the full extras dict
            return params["_gui_extras_passthrough"]

        # Fallback for CLI execution
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

    def _pipeline_params(self, global_extras: Dict[str, Dict[str, Any]], params: Dict[str, Any]) -> Dict[str, Any]:
        """
        Pipeline-level params are taken from:
        1) extras['pipeline'] (if present)
        2) direct params (override extras)
        """
        merged: Dict[str, Any] = {}
        # This will grab 'pipeline.stages', 'pipeline.debug',
        # AND 'pipeline.webcorpus.query', 'pipeline.chat.style' etc.
        merged.update(global_extras.get("pipeline", {}))
        merged.update(params or {})
        return merged

    def _resolve_stages(self, params: Dict[str, Any], global_extras: Dict[str, Dict[str, Any]]) -> List[str]:
        """
        Determine the pipeline stage string from:
        - params["stages"] / params["pipeline"] / params["pipe"]
        - OR extras["pipeline"]["stages"] / ["pipe"] as a fallback
        """
        # 1) explicit params take precedence
        stages_str = params.get("stages") or params.get("pipeline") or params.get("pipe")

        # 2) fallback to extras if not provided in params
        if not stages_str:
            pipe_extras = global_extras.get("pipeline", {})
            stages_str = pipe_extras.get("stages") or pipe_extras.get("pipeline") or pipe_extras.get("pipe")

        if not isinstance(stages_str, str) or not stages_str.strip():
            raise ValueError(
                "Missing pipeline.stages. Example: "
                "--extra pipeline.stages='corpus|chat'"
            )

        stages = [s.strip() for s in stages_str.split("|") if s.strip()]
        if not stages:
            raise ValueError("Empty pipeline.stages.")
        return stages

    def _stage_params(self, stage: str, global_extras: Dict[str, Dict[str, Any]], pipe_params: Dict[str, Any]) -> Dict[
        str, Any]:
        """
        Merge parameters for a stage.

        Order (lowest → highest precedence):
          1) extras['all'].* (applies to every block)
          2) extras[stage].* (legacy, non-namespaced params, e.g., webcorpus.query)
          3) pipeline-delegated params (e.g., pipeline.webcorpus.query)
        """
        merged: Dict[str, Any] = {}

        # 1. Apply global 'all' defaults first
        merged.update(global_extras.get("all", {}))

        # 2. [NEW] Apply legacy, non-pipeline-prefixed params
        #    (e.g., --extra webcorpus.query=...)
        merged.update(global_extras.get(stage.lower(), {}))

        # 3. Extract and apply pipeline-delegated params
        #    (e.g., --extra pipeline.webcorpus.query=...)
        #    This will OVERWRITE legacy params if they conflict.
        prefix = f"{stage}."
        for k, v in pipe_params.items():
            if k.startswith(prefix):
                # 'pipeline.webcorpus.query' becomes 'query'
                sub_key = k[len(prefix):]
                merged[sub_key] = v

        return merged

    # ---- main execute ---------------------------------------------------
    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        # Get all extras, either from GUI or CLI
        all_extras = self._get_all_extras(params or {})

        # Get all parameters prefixed with 'pipeline.'
        pipe_params = self._pipeline_params(all_extras, params or {})

        # Find the 'stages' list
        stages = self._resolve_stages(pipe_params, all_extras)

        stop_on_error = bool(pipe_params.get("stop_on_error", True))
        debug = bool(pipe_params.get("debug", False))

        current = payload
        self._meta_chain.clear()

        for s in stages:
            blk = BLOCKS.create(s)

            # Get params for this specific stage (e.g., 'webcorpus')
            # This will merge 'all.*' with 'pipeline.webcorpus.*'
            stage_params = self._stage_params(s, all_extras, pipe_params)

            stage_meta: Dict[str, Any] = {"stage": s}
            start = time.time()

            if debug:
                text = current if isinstance(current, str) else str(current)
                stage_meta["in_len"] = len(text)
                stage_meta["in_preview"] = text[:160]

            try:
                out, meta = blk.execute(current, params=stage_params)
                elapsed = time.time() - start
                stage_meta.update(meta or {})
                stage_meta["elapsed_sec"] = round(elapsed, 6)

                if debug:
                    out_text = out if isinstance(out, str) else str(out)
                    stage_meta["out_len"] = len(out_text)
                    stage_meta["out_preview"] = out_text[:200]

                self._meta_chain.append(stage_meta)

                if stop_on_error and stage_meta.get("error"):
                    current = out
                    break

                current = out

            except Exception as e:
                elapsed = time.time() - start
                stage_meta.update({
                    "error": "stage_failed",
                    "exception": repr(e),
                    "elapsed_sec": round(elapsed, 6),
                })
                self._meta_chain.append(stage_meta)

                if stop_on_error:
                    break

        out = current if isinstance(current, str) else str(current)
        return out, {
            "type": "chat-pipeline",
            "stages": stages,
            "chain": self._meta_chain,
            "stop_on_error": stop_on_error,
            "debug": debug,
        }

    def get_params_info(self) -> Dict[str, Any]:
        """Returns a dictionary of default parameters for the GUI."""
        return {
            "stages": "block1|block2",
            "pipe": "block1|block2",
            # Pipeline-level options (documented defaults)
            "stop_on_error": True,
            "debug": False,
            # Example of delegated params
            "block1.param_name": "value",
            "block2.foo": 123
        }


BLOCKS.register("pipeline", ChatPipelineBlock)


# ======================= ConcatBlock =======================================
@dataclass
class ConcatBlock(blocks.BaseBlock):  # Make sure to import blocks
    """
    Joins data from the current pipeline payload and Memory into a single string.
    Useful for pipelines where an intermediate block (like Chat) 'consumes'
    context you want to see in the final output.

    NEW: Now supports `clean_artifacts=True` to remove pipeline tags
    (e.g., [lexicon], [context]) before joining.

    Params:
    - parts: Comma-separated list of sources.
        - 'payload': The input text from the previous block.
        - 'memory:key': Data stored in memory.json (e.g., 'shopping_results').
        - 'text:string': Hardcoded text literals.
    - sep: Separator between parts (default: two newlines).
    - json_indent: If a memory item is a list/dict, indent level (default 2).
    - clean_artifacts: (bool) Strip [lexicon], [context], etc., from all inputs.
    """

    def _clean_artifacts(self, text: str) -> str:
        """Removes known pipeline artifact blocks from a string."""
        known_artifacts = [
            "[lexicon]\n", "[context]\n", "[tensor]\n",
            "[zero-shot-classification]\n", "[intel_analysis]\n",
            "[code_solution]\n", "[summary]\n"
        ]
        clean_text = str(text)

        # We rsplit to remove the *last* instance of each tag block,
        # which is the most common pattern of artifact accumulation.
        for artifact in known_artifacts:
            if artifact in clean_text:
                clean_text = clean_text.rsplit(artifact, 1)[0]

        # Also clean any *stray* tags that might be on their own
        clean_text = re.sub(r"^\s*\[[a-z0-9_\-]+\]\s*$", "", clean_text, flags=re.MULTILINE)

        return clean_text.strip()

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        parts_def = str(params.get("parts", "payload"))
        sep = str(params.get("sep", "\n\n"))
        indent = int(params.get("json_indent", 2))
        clean_artifacts = bool(params.get("clean_artifacts", True))  # Default to ON

        sep = sep.replace("\\n", "\n").replace("\\t", "\t")

        store = blocks.Memory.load()
        output_segments = []
        sources_used = []

        definitions = [x.strip() for x in parts_def.split(",")]

        for d in definitions:
            content = ""

            if d == "payload":
                content = str(payload)
                if clean_artifacts:
                    content = self._clean_artifacts(content)
                sources_used.append("payload")

            elif d.lower().startswith("memory:"):
                key = d.split(":", 1)[1].strip()
                data = store.get(key)

                if data is None:
                    content = f"_(Memory key '{key}' is empty)_"
                elif isinstance(data, (dict, list)):
                    # We don't clean JSON, as it's structured data
                    content = json.dumps(data, indent=indent, ensure_ascii=False)
                else:
                    content = str(data)
                    if clean_artifacts:
                        content = self._clean_artifacts(content)

                sources_used.append(f"memory:{key}")

            elif d.lower().startswith("text:"):
                content = d.split(":", 1)[1]
                sources_used.append("text")

            if content:
                output_segments.append(content)

        final_output = sep.join(output_segments)

        return final_output, {
            "parts_count": len(output_segments),
            "sources": sources_used,
            "length": len(final_output),
            "cleaned_artifacts": clean_artifacts
        }

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "parts": "payload, text:--- ANALYSIS ---, memory:web_context",
            "sep": "\\n\\n",
            "json_indent": 2,
            "clean_artifacts": True
        }


BLOCKS.register("concat", ConcatBlock)