from dataclasses import dataclass
from typing import Dict, Any, List

from registry import SUB_BLOCKS
from blocks import _STOPWORDS

def _tokenize_text(text: str) -> List[str]:
    """
    Light tokenization: lowercased, alnum + internal -/' preserved.
    """
    tokens: List[str] = []
    for raw in (text or "").split():
        # Basic normalization
        w = "".join(ch.lower() for ch in raw if ch.isalnum() or ch in "'-")
        w = w.strip("'-")
        if w:
            tokens.append(w)
    return tokens

@dataclass
class BaseSubBlock:
    """Base class for sub-blocks that are called by main blocks."""
    def execute(self, value: Any, *, params: Dict[str, Any]) -> Any:
        """Sub-blocks transform a value, not a whole payload."""
        raise NotImplementedError

    def get_params_info(self) -> Dict[str, Any]:
        return {}

@dataclass
class PromptQuerySubBlock(BaseSubBlock):
    def _clean_tokens(self, tokens: List[str]) -> List[str]:
        return [t for t in tokens if t not in _STOPWORDS]

    def _segment_query(
        self,
        query: str,
        tokens: List[str],
        clean_tokens: List[str]
    ) -> List[str]:
        """
        Heuristic splitter for queries like:
          'raf simons ss15 ss16 ss17 sterling ruby his work at prada'

        Produces anchored, natural queries like:
          'raf simons ss15'
          'raf simons ss16'
          'raf simons ss17'
          'raf simons sterling ruby'
          'raf simons his work at prada'
          'raf simons prada'
        """
        import re

        if len(tokens) < 3:
            return []

        lower_tokens = [t.lower() for t in tokens]

        # Anchor: usually a name/brand at the front (first 1–2 tokens)
        anchor_tokens = tokens[:2] if len(tokens) >= 2 else tokens[:1]
        anchor = " ".join(anchor_tokens).strip()
        if not anchor:
            return []

        segments: List[str] = []

        # --- Seasons: ss15 / fw14 / aw13 / ss2015 etc. ---
        season_re = re.compile(r"^(ss\d{2,4}|fw\d{2,4}|aw\d{2,4})$", re.IGNORECASE)
        for i, tok in enumerate(lower_tokens):
            if season_re.match(tok):
                seg = f"{anchor} {tokens[i]}"
                segments.append(seg.strip())

        # --- Collab: 'sterling ruby' ---
        for i in range(len(lower_tokens) - 1):
            if lower_tokens[i] == "sterling" and lower_tokens[i + 1] == "ruby":
                seg = f"{anchor} sterling ruby"
                segments.append(seg.strip())
                break

        # --- Work at/with brand: '* work at prada' / '* work with prada' / '* prada' ---
        if "prada" in lower_tokens:
            idx = lower_tokens.index("prada")
            start = max(0, idx - 3)
            phrase = " ".join(tokens[start:idx + 1]).strip()  # e.g. 'his work at prada'
            if phrase:
                seg = f"{anchor} {phrase}"
                segments.append(seg.strip())

            # Also a simpler 'anchor prada' query
            seg2 = f"{anchor} prada"
            segments.append(seg2.strip())

        # Dedup while preserving order
        out: List[str] = []
        seen = set()
        for s in segments:
            if s and s not in seen:
                seen.add(s)
                out.append(s)
        return out

    def _post_filter_queries(self, queries: List[str], original_tokens: List[str]) -> List[str]:
        """
        Drop weird fragments and anything that is basically the whole prompt.

        Rules:
          - Hard cap on max length (e.g. 6 tokens).
          - If a candidate has length >= original_len - 1 (for long prompts),
            drop it as "too close" to the original.
          - Keep only queries with enough non-stopword content.
        """
        out: List[str] = []
        seen = set()

        orig_len = len(original_tokens)
        max_tokens = 6  # global max length for any query

        for q in queries:
            q = q.strip()
            if not q or q in seen:
                continue

            toks = _tokenize_text(q)
            if not toks:
                continue

            # Drop very long queries
            if len(toks) > max_tokens:
                continue

            # If original prompt is long (>=5 tokens), drop queries that are
            # almost as long as the original (e.g. len >= orig_len - 1)
            if orig_len >= 5 and len(toks) >= max(orig_len - 1, 4):
                continue

            lower = [t.lower() for t in toks]
            non_stop = [t for t in lower if t not in _STOPWORDS]

            # Allow important single-term queries like 'prada'
            if len(toks) == 1:
                if lower[0] not in {"raf", "simons", "sterling", "ruby", "prada"}:
                    continue

            # For 2-token queries, require at least 1 non-stopword
            if len(toks) == 2 and len(non_stop) == 0:
                continue

            # For longer queries, require at least 2 non-stopwords
            if len(toks) > 2 and len(non_stop) < 2:
                continue

            seen.add(q)
            out.append(q)

        return out

    def _hf_rewrite_queries(self, queries: List[str], params: Dict[str, Any]) -> List[str]:
        """
        HF pass that takes already-processed queries and lets
        a small model polish them into nicer web search queries.

        This does NOT change the earlier segmentation logic; it's a
        final, best-effort rewrite layer.
        """
        if not queries:
            return queries

        try:
            from blocks import _get_hf_pipeline
        except ImportError:
            print("[PromptQuerySubBlock] Could not import _get_hf_pipeline; skipping HF rewrite.")
            return queries

        model_name = str(params.get("hf_model", "google/flan-t5-small"))
        pipe = _get_hf_pipeline(
            "text2text-generation",
            model_name,
            device=params.get("hf_device", "auto"),
            verbose=params.get("hf_verbose", False),
        )
        if pipe is None:
            print(f"[PromptQuerySubBlock] Failed to load HF model '{model_name}', skipping HF rewrite.")
            return queries

        max_new_tokens = int(params.get("hf_max_new_tokens", 32))
        temperature = float(params.get("hf_temperature", 0.3))
        top_p = float(params.get("hf_top_p", 0.9))

        rewritten: List[str] = []

        for q in queries:
            prompt = (
                "Rewrite this into a concise, high-quality web search query. "
                "Preserve all important names, brands, and years. "
                "Prefer noun phrases over full questions. "
                "Keep it under 10 words and avoid quotes or extra punctuation.\n"
                f"Query: {q}"
            )
            try:
                pred = pipe(
                    prompt,
                    max_new_tokens=max_new_tokens,
                    temperature=temperature,
                    top_p=top_p,
                    do_sample=True,
                )
                text = (pred[0].get("generated_text") or "").strip()
                if text:
                    rewritten.append(text)
                else:
                    rewritten.append(q)
            except Exception as e:
                print(f"[PromptQuerySubBlock] HF rewrite error on '{q}': {e}")
                rewritten.append(q)

        # light dedupe after rewrite
        out: List[str] = []
        seen = set()
        for r in rewritten:
            r = r.strip()
            if r and r not in seen:
                seen.add(r)
                out.append(r)
        return out

    def execute(self, value: Any, *, params: Dict[str, Any]) -> List[str]:
        query = str(value or "")
        if not query:
            return []

        op = str(params.get("op", "clean_permutate")).lower()

        tokens = _tokenize_text(query)
        clean_tokens = self._clean_tokens(tokens)
        if not clean_tokens:
            clean_tokens = tokens  # fallback

        if op == "clean":
            q = " ".join(clean_tokens).strip()
            return [q] if q else []

        if op == "clean_permutate":
            queries: List[str] = []

            # NOTE: we DO NOT append the full original query anymore.
            # NOTE: we DO NOT append a full cleaned version either if it's long.

            # 1. First 2–3 terms as core topic (usually 'raf simons' / 'raf simons ss15')
            if len(clean_tokens) > 1:
                q2 = " ".join(clean_tokens[:2]).strip()
                if q2:
                    queries.append(q2)
            if len(clean_tokens) > 2:
                q3 = " ".join(clean_tokens[:3]).strip()
                if q3:
                    queries.append(q3)

            # 2. Heuristic segments (seasons, collabs, work-at-brand)
            segments = self._segment_query(query, tokens, clean_tokens)
            queries.extend(segments)

            # 3. Dedup + natural-language filter + "no-whole-prompt" filter
            final = self._post_filter_queries(queries, clean_tokens)

            # 4. HF rewrite to polish final queries for web search (always on if model available)
            final = self._hf_rewrite_queries(final, params)

            return final

        # Default/passthrough
        q = query.strip()
        return [q] if q else []

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "op": "clean_permutate",
            # HF rewrite options (always used when possible)
            "hf_model": "google/flan-t5-small",
            "hf_max_new_tokens": 32,
            "hf_temperature": 0.3,
            "hf_top_p": 0.9,
            "hf_device": "auto",
            "hf_verbose": False,
        }



# Register in the SUB_BLOCKS registry
SUB_BLOCKS.register("prompt_query", PromptQuerySubBlock)

# ======================= NEW ENGLISH SUB-BLOCK ==========================
@dataclass
class EnglishChatSubBlock(BaseSubBlock):
    """
    A sub-block that uses an HF model to rewrite text.
    Designed to be called via `run_sub_pipeline` from a parent block.

    Operations (op=):
    - "fix_grammar": Corrects spelling and grammar.
    - "simplify": Rewrites text to be simple and easy to understand.
    - "professional": Rewrites text in a more formal, professional tone.
    - "casual": Rewrites text in a casual, friendly tone.
    - "passthrough": Returns the text unchanged (default).

    Extra handling for marketplace-style ads / listings:
    - ad_mode = "skip"    → detect listing-like blobs and return as-is (no HF).
    - ad_mode = "shorten" → detect listing-like blobs and return a short title only.
    - ad_mode = "rewrite" → detect listing-like blobs, shorten them, then send
                             that cleaned string through the HF model.
    """

    # --------- Heuristics to detect listing / ad blobs ---------
    @staticmethod
    def _is_listing_snippet(text: str) -> bool:
        """
        Very lightweight check to see if this looks like a resale / marketplace
        listing blob, e.g. Depop / Grailed / eBay style text or generic
        catalog/filter UI like "Sort By: - Size: Various".

        Heuristics:
          - Contains known marketplace keywords (depop, grailed, ebay, poshmark, etc.).
          - Contains "other shirts you may like" / "you may also like".
          - Contains multiple prices or explicit currency with symbols.
          - Lots of hyphen / ' - - ' style separators.
          - Filter UI phrases like "Sort By:" + "Size:".
        """
        import re

        t = (text or "").lower()
        if not t:
            return False

        # --- 1) Marketplace / shop / catalog phrases ---
        marketplace_keywords = [
            "depop", "grailed", "poshmark", "ebay", "vinted",
            "etsy", "stockx", "farfetch", "ssense",
            "add to bundle", "add to cart", "add to bag",
            "other shirts you may like",
            "you may also like",
            "shop now",
            "view all",
        ]
        if any(k in t for k in marketplace_keywords):
            return True

        # Filter / catalog UI patterns like your example:
        # "Raf Simons Women Sort By: - Size: Various Raf Simons $479 ..."
        if "sort by" in t and "size" in t:
            return True

        # Generic "Size: S M L" pattern (size filter)
        if "size:" in t or "sizes:" in t:
            # If we see size plus at least one price, it's almost certainly a listing
            if "$" in t or "£" in t or "€" in t:
                return True

        # --- 2) Currency + multiple prices ---
        if "$" in t or "£" in t or "€" in t:
            price_hits = re.findall(r"[$£€]\s?\d+", t)
            if len(price_hits) >= 2:
                return True

        # --- 3) Hyphen-heavy, scraped layout ---
        if t.count(" - ") >= 3 or " - - " in t:
            return True

        # --- 4) Extreme repetition (same tokens over and over) ---
        tokens = [tok for tok in re.split(r"\s+", t) if tok]
        if len(tokens) > 30:
            uniq = set(tokens)
            if len(uniq) < len(tokens) * 0.5:  # >50% repetition
                return True

        return False

    @staticmethod
    def _shorten_listing(text: str) -> str:
        """
        Try to compress a messy listing blob down to a concise product title.

        Strategy:
          - Take the first line or chunk before obvious site markers (e.g. ' - Depop').
          - Remove trailing site names / boilerplate fragments.
          - Collapse repeated whitespace and hyphens.
        """
        import re

        if not text:
            return ""

        # First, break on newlines to get the first non-empty line.
        lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
        if lines:
            text = lines[0]

        # Then, cut off at obvious site markers.
        cut_markers = [" - depop", " | depop", "| grailed", "- grailed", "| ebay", " - ebay"]
        lower = text.lower()
        cut_idx = None
        for m in cut_markers:
            idx = lower.find(m)
            if idx != -1:
                cut_idx = idx
                break
        if cut_idx is not None:
            text = text[:cut_idx]

        # Remove repeated marketplace boilerplate phrases that survive
        boilerplate_patterns = [
            r"other shirts you may like.*",
            r"you may also like.*",
            r"add to bundle.*",
        ]
        for pat in boilerplate_patterns:
            text = re.sub(pat, "", text, flags=re.IGNORECASE)

        # Collapse repeated spaces and hyphens
        text = re.sub(r"\s*-\s*", " - ", text)
        text = re.sub(r"\s+", " ", text)

        return text.strip()

    def execute(self, value: Any, *, params: Dict[str, Any]) -> Any:
        # --- Local import to avoid circular dependency ---
        try:
            # This import happens at runtime, not module load time
            from blocks import _get_hf_pipeline
        except ImportError:
            print("[EnglishChatSubBlock] CRITICAL: Failed to import _get_hf_pipeline.")
            return value
        # --- End local import ---

        text = str(value or "")
        op = str(params.get("op", "passthrough")).lower()

        # If no operation, just pass the value through
        if op == "passthrough" or not text:
            return text

        # --------- NEW: pre-process listing-like blobs ---------
        ad_mode = str(params.get("ad_mode", "skip")).lower()  # skip | shorten | rewrite

        is_listing = self._is_listing_snippet(text)
        if is_listing:
            if ad_mode == "skip":
                # Detected as a marketplace ad; do not send to HF at all.
                # Caller can decide to ignore these upstream.
                return text

            cleaned = self._shorten_listing(text)

            if ad_mode == "shorten":
                # Return the cleaned product title only, no HF.
                return cleaned or text

            if ad_mode == "rewrite":
                # Use cleaned title (if any) as the basis for the HF rewrite
                if cleaned:
                    text = cleaned

        # --------- Normal HF rewrite path ---------
        model = str(params.get("model", "google/flan-t5-small"))

        pipe = _get_hf_pipeline(
            "text2text-generation",
            model,
            device=params.get("device", "auto"),
            verbose=params.get("verbose", False)
        )
        if pipe is None:
            print(f"[EnglishChatSubBlock] Failed to load model '{model}', returning original text.")
            return text  # Failed to load, return original

        # Define the instruction-prompt for the model
        templates = {
            "fix_grammar": f"Correct the spelling and grammar of the following text: {text}",
            "simplify": f"Rewrite the following text to be simple and easy to understand: {text}",
            "professional": f"Rewrite the following text in a formal, professional business tone: {text}",
            "casual": f"Rewrite the following text in a casual, friendly, and informal tone: {text}"
        }

        prompt = templates.get(op)
        if not prompt:
            print(f"[EnglishChatSubBlock] Unknown op '{op}', returning original text.")
            return text  # Unknown op

        try:
            # Set reasonable generation parameters
            gen_kwargs = {
                "max_new_tokens": int(params.get("max_new_tokens", len(text.split()) + 50)),
                "min_length": int(params.get("min_length", 5)),
                "temperature": float(params.get("temperature", 0.7)),
                "top_p": float(params.get("top_p", 0.95)),
                "do_sample": True
            }

            pred = pipe(prompt, **gen_kwargs)
            generated_text = pred[0]["generated_text"].strip()

            return generated_text if generated_text else text

        except Exception as e:
            print(f"[EnglishChatSubBlock] Error during generation: {e}")
            return text  # Return original on failure

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "op": "passthrough",          # fix_grammar | simplify | professional | casual
            "model": "google/flan-t5-small",
            "max_new_tokens": 128,
            "temperature": 0.7,
            "top_p": 0.95,
            # New ad-handling knob
            "ad_mode": "skip",           # skip | shorten | rewrite
        }

# Register the new sub-block
SUB_BLOCKS.register("english_chat", EnglishChatSubBlock)

# ======================= NEW CODE SUB-BLOCK ==========================
@dataclass
class CodeChatSubBlock(BaseSubBlock):
    """
    A sub-block that uses an HF model to rewrite or explain code.
    Designed to be called via `run_sub_pipeline` from a parent block.

    Operations (op=):
      - "refactor"     : Refactor code for clarity & maintainability.
      - "add_comments" : Add concise, helpful comments without changing logic.
      - "docstring"    : Add or improve docstrings for functions/classes.
      - "fix"          : Fix syntax/logic errors and return valid code.
      - "explain"      : Explain what the code does in natural language.
      - "passthrough"  : Return the code unchanged (default).
    """

    def execute(self, value: Any, *, params: Dict[str, Any]) -> Any:
        # --- Local import to avoid circular dependency ---
        try:
            from blocks import _get_hf_pipeline
        except ImportError:
            print("[CodeChatSubBlock] CRITICAL: Failed to import _get_hf_pipeline.")
            return value
        # --- End local import ---

        code = str(value or "")
        if not code.strip():
            return code

        op = str(params.get("op", "passthrough")).lower()
        if op == "passthrough":
            return code

        model = str(params.get("model", "google/flan-t5-small"))
        lang = str(params.get("lang", "python")).strip().lower() or "python"

        pipe = _get_hf_pipeline(
            "text2text-generation",
            model,
            device=params.get("device", "auto"),
            verbose=params.get("verbose", False),
        )
        if pipe is None:
            print(f"[CodeChatSubBlock] Failed to load model '{model}', returning original code.")
            return code

        # Instruction-style prompts for different operations
        base_intro = f"The following is {lang} code.\n\n"
        templates = {
            "refactor": (
                base_intro
                + "Refactor this code to improve readability and maintainability, "
                  "while preserving its behavior. Return only the refactored code.\n\n"
                  "Code:\n"
                + code
            ),
            "add_comments": (
                base_intro
                + "Add concise, helpful comments to this code without changing its behavior. "
                  "Return only the commented code.\n\n"
                  "Code:\n"
                + code
            ),
            "docstring": (
                base_intro
                + "Add or improve docstrings for all public functions, methods, and classes. "
                  "Return only the updated code with docstrings.\n\n"
                  "Code:\n"
                + code
            ),
            "fix": (
                base_intro
                + "Fix any syntax or obvious logic errors in this code and return valid, "
                  "runnable code. Preserve the original intent as much as possible.\n\n"
                  "Code:\n"
                + code
            ),
            "explain": (
                base_intro
                + "Explain clearly and concisely what this code does, step by step. "
                  "Return only the explanation in English.\n\n"
                  "Code:\n"
                + code
            ),
        }

        prompt = templates.get(op)
        if not prompt:
            print(f"[CodeChatSubBlock] Unknown op '{op}', returning original code.")
            return code

        try:
            gen_kwargs = {
                "max_new_tokens": int(params.get("max_new_tokens", max(64, len(code.split()) + 50))),
                "min_length": int(params.get("min_length", 5)),
                "temperature": float(params.get("temperature", 0.3 if op != "explain" else 0.7)),
                "top_p": float(params.get("top_p", 0.95)),
                "do_sample": bool(params.get("do_sample", op == "explain")),
            }

            pred = pipe(prompt, **gen_kwargs)
            generated_text = (pred[0].get("generated_text") or "").strip()

            # If the op returns code, fall back to the original on empty
            if not generated_text:
                return code

            return generated_text

        except Exception as e:
            print(f"[CodeChatSubBlock] Error during generation: {e}")
            return code  # Return original on failure

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "op": "passthrough",        # refactor | add_comments | docstring | fix | explain | passthrough
            "model": "google/flan-t5-small",
            "lang": "python",
            "max_new_tokens": 256,
            "min_length": 5,
            "temperature": 0.3,
            "top_p": 0.95,
            "do_sample": False,
        }


# Register the new sub-block
SUB_BLOCKS.register("code_chat", CodeChatSubBlock)