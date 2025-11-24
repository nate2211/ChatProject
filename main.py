# ========================================================
# ================  main.py  =============================
# ========================================================
from __future__ import annotations
import argparse
import json
import os
import sys
from typing import Any, Dict, Optional

import blocks  # registers blocks
from registry import BLOCKS
import pipeline  # registers pipeline


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(prog="promptchat", description="Modular prompt-chat CLI.")
    available = ", ".join(BLOCKS.names()) or "(none)"
    p.add_argument("block", help=f"Block to run (or 'pipeline'). Available: {available}")
    p.add_argument("prompt", nargs="?", default=None, help="Input message (reads stdin if omitted)")
    p.add_argument("--extra", action="append", default=[], help="key=val (supports name.key=val, all.key=val)")
    p.add_argument("--json", action="store_true", help="Print JSON with metadata")
    return p


def _read_payload(arg: Optional[str]) -> str:
    if arg is not None:
        return arg
    if sys.stdin.isatty():
        eof_hint = "Ctrl+D" if os.name != "nt" else "Ctrl+Z then Enter"
        print(f"Enter message then {eof_hint}:", file=sys.stderr)
    return sys.stdin.read()


def main(argv: Optional[list[str]] = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)

    try:
        extras = blocks.parse_extras(args.extra)
    except Exception as e:
        parser.error(f"Failed to parse --extra: {e}")
        return 2

    payload = _read_payload(args.prompt)
    if not payload and args.prompt is None:
        parser.error("No prompt provided via arg or stdin.")
        return 1

    blocks.ensure_app_dirs()

    try:
        blk = BLOCKS.create(args.block)
        params: Dict[str, Any] = {}
        params.update(extras.get("all", {}))
        params.update(extras.get(args.block.lower(), {}))
        result, meta = blk.execute(payload, params=params)
        if args.json:
            print(json.dumps({"block": args.block, "metadata": meta, "result": result}, indent=2, ensure_ascii=False))
        else:
            print(result, end="")
        return 0
    except KeyError as e:
        print(f"Error: {e}", file=sys.stderr); return 1
    except NotImplementedError:
        print(f"Error: Block '{args.block}' is missing an 'execute' implementation.", file=sys.stderr); return 1
    except Exception as e:
        print(f"Unexpected error in block '{args.block}': {e}", file=sys.stderr); return 1


if __name__ == "__main__":

    raise SystemExit(main())
