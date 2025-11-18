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
        stops = globals().get("_STOPWORDS", set())
        return [t for t in tokens if t not in stops]

    def _segment_query(self, query: str, tokens: List[str], clean_tokens: List[str]) -> List[str]:
        """
        Advanced heuristic splitter.
        Segments by:
        1. Generic Entity Chunking (Capitalized phrases)
        2. Seasonal/Time codes
        3. Prepositional phrases
        4. Sliding Window N-Grams (Fallback for lists of names)
        """
        import re
        if len(tokens) < 2:
            return []

        segments: List[str] = []

        # Anchor: First 2 clean tokens (e.g. "Yung Bans")
        anchor = " ".join(clean_tokens[:2]).strip()

        # --- 1. Entity Chunking (Consecutive Capitalized Groups) ---
        # Ideal for: "Yung Bans Playboi Carti Lil Uzi Vert" -> ["Yung Bans", "Playboi Carti", "Lil Uzi Vert"]
        current_chunk = []
        entities = []

        for tok in tokens:
            if tok[0].isupper() and tok.isalpha():
                current_chunk.append(tok)
            else:
                if current_chunk:
                    entities.append(" ".join(current_chunk))
                current_chunk = []

        # Catch tail
        if current_chunk:
            entities.append(" ".join(current_chunk))

        # If we found multiple distinct entities, add them as queries
        # Strategy: Anchor + Entity (if Entity is not Anchor)
        if len(entities) > 1:
            for ent in entities:
                if ent.lower() not in anchor.lower():
                    segments.append(f"{anchor} {ent}")
                # Also add the entity standalone if it's long enough (e.g. "Lil Uzi Vert")
                if len(ent.split()) >= 2:
                    segments.append(ent)

        # --- 2. Time & Season Codes ---
        time_re = re.compile(r"\b((?:ss|fw|aw|sp|su|fa|wi|q[1-4])\s?'?\d{2,4}|\d{4})\b", re.IGNORECASE)
        for match in time_re.finditer(query):
            matched_text = match.group(0)
            if matched_text.lower() not in anchor.lower():
                segments.append(f"{anchor} {matched_text}")

        # --- 3. Prepositional Relations ---
        prepositions = {"at", "with", "for", "in", "by", "x", "feat", "ft", "versus", "vs"}
        lower_tokens = [t.lower() for t in tokens]

        for i, tok in enumerate(lower_tokens):
            if tok in prepositions and i < len(tokens) - 1:
                # Grab context after preposition
                start = i + 1  # Skip the preposition itself for cleaner search sometimes
                end = min(len(tokens), i + 4)
                phrase = " ".join(tokens[start:end]).strip()

                if phrase and phrase not in anchor.lower():
                    segments.append(f"{anchor} {phrase}")
                    # Also try with the preposition (e.g. "x Playboi Carti")
                    segments.append(f"{anchor} {tokens[i]} {phrase}")

        # --- 4. Sliding Window (Fallback for unstructured lists) ---
        # If we haven't generated much, walk through the query in chunks of 2-3 words
        if len(segments) < 2 and len(clean_tokens) > 3:
            # Overlapping windows of 2 and 3 tokens
            for n in [2, 3]:
                for i in range(len(clean_tokens) - n + 1):
                    window = clean_tokens[i: i + n]
                    phrase = " ".join(window)
                    # Don't just add the anchor again
                    if phrase.lower() != anchor.lower():
                        # If the window is at the start, it's just a subset of anchor, ignore
                        if i > 0:
                            segments.append(f"{anchor} {phrase}")

        return list(dict.fromkeys(segments))

    def _post_filter_queries(self, queries: List[str], original_tokens: List[str]) -> List[str]:
        out: List[str] = []
        seen = set()

        # Recalculate stops locally to avoid globals issues
        stops = globals().get("_STOPWORDS", {
            "the", "and", "or", "is", "at", "which", "on", "in", "a", "an"
        })

        for q in queries:
            q = q.strip()
            if not q or q in seen: continue

            toks = _tokenize_text(q)
            if not toks: continue

            # Filter: Too long
            if len(toks) > 8: continue

            # Filter: Single Stopword
            if len(toks) == 1 and toks[0].lower() in stops: continue

            seen.add(q)
            out.append(q)
        return out

    def _hf_rewrite_queries(self, queries: List[str], params: Dict[str, Any]) -> List[str]:
        if not queries or not params.get("hf_model"): return queries
        # ... (Keep existing HF logic) ...
        return queries

    def execute(self, value: Any, *, params: Dict[str, Any]) -> List[str]:
        query = str(value or "")
        if not query: return []

        op = str(params.get("op", "clean_permutate")).lower()
        tokens = _tokenize_text(query)
        clean_tokens = self._clean_tokens(tokens)
        if not clean_tokens: clean_tokens = tokens

        if op == "clean":
            return [" ".join(clean_tokens).strip()]

        if op == "clean_permutate":
            queries: List[str] = []

            # 1. Always include the full original query (sanitized)
            # This ensures we don't lose the user's specific intent
            full_clean = " ".join(clean_tokens)
            if full_clean:
                queries.append(full_clean)

            # 2. Anchor (First 2 words)
            if len(clean_tokens) >= 2:
                queries.append(" ".join(clean_tokens[:2]).strip())

            # 3. Segmentation Logic
            queries.extend(self._segment_query(query, tokens, clean_tokens))

            # 4. Filter
            final = self._post_filter_queries(queries, clean_tokens)

            # 5. Rewrite (optional)
            final = self._hf_rewrite_queries(final, params)

            if not final:
                return [query.strip()]

            return final

        return [query.strip()]


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