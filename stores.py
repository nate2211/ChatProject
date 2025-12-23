# ======================= stores.py =======================
from __future__ import annotations

import collections
import random
import sqlite3
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple, Set, Callable, ClassVar
from urllib.parse import urlparse
import time
from submanagers import DatabaseSubmanager


@dataclass
class BaseStore:
    """
    Thin base class for typed stores.
    """
    db: DatabaseSubmanager

# ======================================================================
# CorpusStore  (place with your other Stores, e.g. in submanagers.py)
# ======================================================================

class CorpusStore(BaseStore):
    """
    Store for CorpusBlock.

    Owns schema + all Corpus/FTS-specific queries.
    """

    CORPUS_DDL = """
    CREATE TABLE IF NOT EXISTS corpus_docs
    (
        id INTEGER PRIMARY KEY,
        title   TEXT NOT NULL,
        content TEXT NOT NULL,
        config  TEXT NOT NULL,       -- '20231101.en', 'wiki_api', etc.
        fetched_at DATETIME DEFAULT CURRENT_TIMESTAMP,
        UNIQUE(title, config)
    );
    """

    FTS_DDL = """
    CREATE VIRTUAL TABLE IF NOT EXISTS corpus_fts USING fts5(
        content='corpus_docs',        -- Link to main table
        content_rowid='id',           -- Link to rowid
        tokenize='porter unicode61',
        title,
        content
    );
    """

    TRIGGERS_DDL = [
        # AFTER INSERT → add row to FTS
        """
        CREATE TRIGGER IF NOT EXISTS corpus_docs_ai
        AFTER INSERT ON corpus_docs
        BEGIN
            INSERT INTO corpus_fts(rowid, title, content)
            VALUES (new.id, new.title, new.content);
        END;
        """,
        # AFTER DELETE → delete from FTS
        """
        CREATE TRIGGER IF NOT EXISTS corpus_docs_ad
        AFTER DELETE ON corpus_docs
        BEGIN
            INSERT INTO corpus_fts(corpus_fts, rowid, title, content)
            VALUES ('delete', old.id, old.title, old.content);
        END;
        """,
        # AFTER UPDATE → delete old + insert new into FTS
        """
        CREATE TRIGGER IF NOT EXISTS corpus_docs_au
        AFTER UPDATE ON corpus_docs
        BEGIN
            INSERT INTO corpus_fts(corpus_fts, rowid, title, content)
            VALUES ('delete', old.id, old.title, old.content);
            INSERT INTO corpus_fts(rowid, title, content)
            VALUES (new.id, new.title, new.content);
        END;
        """,
    ]

    def ensure_schema(self) -> None:
        """
        Install corpus_docs + FTS + triggers (idempotent).
        """
        self.db.ensure_schema([self.CORPUS_DDL, self.FTS_DDL, *self.TRIGGERS_DDL])

    # -------------------- Writes -------------------- #
    def save_many(self, docs: list[dict[str, str]], config_key: str) -> None:
        """
        Bulk insert docs; ignores duplicates by (title, config).
        """
        if not docs:
            return
        rows = []
        for d in docs:
            title = (d.get("title") or "").strip()
            text = (d.get("text") or "").strip()
            if not title or not text:
                continue
            rows.append((title, text, config_key))

        if not rows:
            return

        try:
            self.db.executemany(
                """
                INSERT OR IGNORE INTO corpus_docs (title, content, config)
                VALUES (?, ?, ?)
                """,
                rows,
            )
        except Exception as e:
            # Keep failures non-fatal
            print(f"[CorpusStore] save_many failed: {e}")

    # -------------------- Reads -------------------- #
    def search_fts(
        self,
        query: str,
        config_key: str,
        fetch_limit: int,
    ) -> list[dict[str, str]]:
        """
        FTS lookup by query for a given config (or 'wiki_api'),
        returning up to fetch_limit docs as {title, text}.
        """
        import re

        if not query:
            return []

        # Very simple sanitization → remove weird operators that might break MATCH
        fts_query = " ".join(re.findall(r"[A-Za-z0-9]+", query))
        if not fts_query:
            return []

        try:
            rows = self.db.fetchall(
                """
                SELECT T.title, T.content
                FROM corpus_docs AS T
                JOIN corpus_fts AS F ON T.id = F.rowid
                WHERE F.corpus_fts MATCH ?
                  AND (T.config = ? OR T.config = 'wiki_api')
                LIMIT ?
                """,
                (fts_query, config_key, int(fetch_limit)),
            )
        except Exception as e:
            print(f"[CorpusStore] search_fts failed: {e}")
            return []

        out: list[dict[str, str]] = []
        for r in rows:
            out.append({"title": r["title"], "text": r["content"]})
        return out

# ======================================================================
# LinkTrackerStore  (place with your other Stores, e.g. in submanagers.py)
# ======================================================================


class LinkTrackerStore(BaseStore):
    """
    Store for LinkTrackerBlock.

    Owns schema + all LinkTracker-specific queries.
    """

    ASSETS_DDL = """
    CREATE TABLE IF NOT EXISTS assets
    (
        url TEXT PRIMARY KEY,
        text TEXT,
        source TEXT,
        size TEXT,
        status TEXT,
        first_seen TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        last_checked TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    )
    """

    PAGES_DDL = """
    CREATE TABLE IF NOT EXISTS pages
    (
        url TEXT PRIMARY KEY,
        last_scanned TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    )
    """

    INDEXES_DDL = [
        "CREATE INDEX IF NOT EXISTS idx_assets_source ON assets (source)",
        "CREATE INDEX IF NOT EXISTS idx_assets_last_checked ON assets (last_checked)",
        "CREATE INDEX IF NOT EXISTS idx_pages_last_scanned ON pages (last_scanned)",
    ]

    def ensure_schema(self) -> None:
        self.db.ensure_schema([self.ASSETS_DDL, self.PAGES_DDL, *self.INDEXES_DDL])

        # Example micro-migrations you might add later:
        # self.db.ensure_columns("assets", {"tag": "TEXT DEFAULT ''"})
        # self.db.ensure_columns("pages", {"seed_ok": "INTEGER DEFAULT 0"})

    # -------------------- Assets -------------------- #
    def asset_exists(self, url: str) -> bool:
        r = self.db.fetchone("SELECT 1 FROM assets WHERE url = ?", (url,))
        return r is not None

    def upsert_asset(self, asset: Dict[str, Any]) -> None:
        """
        Preserves first_seen on existing rows.
        """
        url = asset.get("url", "")
        if not url:
            return

        exists = self.asset_exists(url)
        if exists:
            self.db.execute(
                """
                UPDATE assets
                SET status = ?, last_checked = CURRENT_TIMESTAMP, size = ?, source = ?, text = ?
                WHERE url = ?
                """,
                (
                    asset.get("status", ""),
                    asset.get("size", ""),
                    asset.get("source", ""),
                    asset.get("text", ""),
                    url,
                ),
            )
        else:
            self.db.execute(
                """
                INSERT INTO assets (url, text, source, size, status, last_checked)
                VALUES (?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
                """,
                (
                    url,
                    asset.get("text", ""),
                    asset.get("source", ""),
                    asset.get("size", ""),
                    asset.get("status", ""),
                ),
            )

    def fetch_db_seed_assets(
        self,
        limit: int = 200,
        require_keywords: Optional[List[str]] = None,
        required_sites: Optional[List[str]] = None,
        max_age_days: Optional[int] = None,
    ) -> List[Dict[str, Any]]:
        require_keywords = [k.lower() for k in (require_keywords or []) if k]
        required_sites = [s.lower() for s in (required_sites or []) if s]

        where = []
        args: list[Any] = []

        if max_age_days is not None:
            where.append("last_checked >= datetime('now', ?)")
            args.append(f"-{int(max_age_days)} days")

        if require_keywords:
            kw = []
            for k in require_keywords:
                like = f"%{k}%"
                kw.append("(url LIKE ? OR text LIKE ? OR source LIKE ?)")
                args.extend([like, like, like])
            where.append("(" + " OR ".join(kw) + ")")

        if required_sites:
            sc = []
            for s in required_sites:
                sc.append("url LIKE ?")
                args.append(f"%{s}%")
            where.append("(" + " OR ".join(sc) + ")")

        where_sql = ("WHERE " + " AND ".join(where)) if where else ""
        q = f"""
            SELECT url, text, source, last_checked
            FROM assets
            {where_sql}
            ORDER BY last_checked DESC
            LIMIT ?
        """
        args.append(int(limit))

        rows = self.db.fetchall(q, args)
        out = []
        for r in rows:
            out.append({
                "url": r["url"],
                "text": r["text"] or "",
                "source": r["source"] or "",
                "last_checked": r["last_checked"],
            })
        return out

    def fetch_proven_hubs(self, required_sites: List[str], min_hits: int = 1) -> List[str]:
        site_clause = ""
        args: list[Any] = []

        if required_sites:
            clauses = []
            for s in required_sites:
                clauses.append("source LIKE ?")
                args.append(f"%{s}%")
            site_clause = "AND (" + " OR ".join(clauses) + ")"

        q = f"""
            SELECT source, COUNT(*) as hit_count
            FROM assets
            WHERE status = '200 OK'
            AND source LIKE 'http%'
            {site_clause}
            GROUP BY source
            HAVING hit_count >= ?
            ORDER BY hit_count DESC
            LIMIT 50
        """
        args.append(min_hits)

        rows = self.db.fetchall(q, args)
        return [r["source"] for r in rows if r["source"]]

    def seed_pages_from_database(
            self,
            db_assets: List[Dict[str, Any]],
            targets: set[str],
            max_pages_total: int,
            required_sites: List[str],
            keywords: List[str],
            min_term_overlap: int,
    ) -> Tuple[List[str], List[str]]:
        candidate_pages: List[str] = []
        direct_asset_urls: List[str] = []

        def _allowed(u: str) -> bool:
            if not required_sites:
                return True
            try:
                d = urlparse(u).netloc.lower().split(":")[0]
            except Exception:
                return False
            return any(req in d for req in required_sites)

        def _term_ok(h: str) -> bool:
            if not keywords:
                return True
            hlow = h.lower()
            hits = sum(1 for k in keywords if k and k in hlow)
            return hits >= min_term_overlap

        for row in db_assets:
            u = (row.get("url") or "").strip()
            src = (row.get("source") or "").strip()

            if not u:
                continue

            upath = urlparse(u).path.lower()
            if any(upath.endswith(ext) for ext in targets):
                if _allowed(u) and _term_ok(u + " " + (row.get("text") or "")):
                    direct_asset_urls.append(u)

            if src.startswith("http") and _allowed(src) and _term_ok(src):
                candidate_pages.append(src)

            try:
                parsed = urlparse(u)
                parent_path = (parsed.path or "/").rsplit("/", 1)[0] + "/"
                parent_url = f"{parsed.scheme}://{parsed.netloc}{parent_path}"
                if _allowed(parent_url) and _term_ok(parent_url):
                    candidate_pages.append(parent_url)
            except Exception:
                pass

            try:
                host = urlparse(u).netloc.lower()
                if "archive.org" in host:
                    parts = urlparse(u).path.split("/")
                    if len(parts) >= 3:
                        ident = parts[2]
                        for au in self._archive_ident_to_downloads(ident):
                            if _allowed(au) and _term_ok(au):
                                candidate_pages.append(au)
            except Exception:
                pass

        def _dedupe(seq: List[str]) -> List[str]:
            seen = set()
            out = []
            for s in seq:
                if s and s not in seen:
                    seen.add(s)
                    out.append(s)
            return out

        candidate_pages = _dedupe(candidate_pages)[:max_pages_total]
        direct_asset_urls = _dedupe(direct_asset_urls)
        return candidate_pages, direct_asset_urls
    # -------------------- Pages -------------------- #
    def page_scanned(self, url: str) -> bool:
        r = self.db.fetchone("SELECT 1 FROM pages WHERE url = ?", (url,))
        return r is not None

    def mark_page_scanned(self, url: str) -> None:
        if not url:
            return
        self.db.execute(
            """
            INSERT OR REPLACE INTO pages (url, last_scanned)
            VALUES (?, CURRENT_TIMESTAMP)
            """,
            (url,),
        )

# ======================================================================
# VideoTrackerStore  (place with your other Stores, e.g. in submanagers.py)
# ======================================================================


class VideoTrackerStore(BaseStore):
    """
    Store for VideoLinkTrackerBlock.
    Owns schema + all SQL + DB seeding/expansion + cooldown ops.

    Block should not touch sqlite directly.
    """

    # -------------------- schema -------------------- #

    ASSETS_DDL = """
    CREATE TABLE IF NOT EXISTS assets
    (
        url TEXT PRIMARY KEY,
        canonical_url TEXT,
        content_id TEXT,
        text TEXT,
        source TEXT,
        size TEXT,
        status TEXT,
        first_seen TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        last_checked TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        seed_ok INTEGER DEFAULT 1,
        synthetic INTEGER DEFAULT 0
    )
    """

    PAGES_DDL = """
    CREATE TABLE IF NOT EXISTS pages
    (
        url TEXT PRIMARY KEY,
        last_scanned TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    )
    """

    RECENT_RETURNS_DDL = """
    CREATE TABLE IF NOT EXISTS recent_returns
    (
        identifier TEXT PRIMARY KEY,
        returned_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    )
    """

    INDEXES_DDL = [
        "CREATE INDEX IF NOT EXISTS idx_assets_source ON assets (source)",
        "CREATE INDEX IF NOT EXISTS idx_assets_seed_ok ON assets (seed_ok)",
        "CREATE INDEX IF NOT EXISTS idx_assets_last_checked ON assets (last_checked)",
        "CREATE INDEX IF NOT EXISTS idx_assets_canonical ON assets (canonical_url)",
        "CREATE INDEX IF NOT EXISTS idx_assets_content_id ON assets (content_id)",
        "CREATE INDEX IF NOT EXISTS idx_pages_last_scanned ON pages (last_scanned)",
        "CREATE INDEX IF NOT EXISTS idx_recent_returns_at ON recent_returns(returned_at)",
    ]

    def ensure_schema(self) -> None:
        self.db.ensure_schema([self.ASSETS_DDL, self.PAGES_DDL, self.RECENT_RETURNS_DDL, *self.INDEXES_DDL])

        # light migrations if older DBs exist
        self.db.ensure_columns("assets", {
            "seed_ok": "INTEGER DEFAULT 1",
            "synthetic": "INTEGER DEFAULT 0",
            "canonical_url": "TEXT",
            "content_id": "TEXT",
        })

    # -------------------- assets -------------------- #

    def asset_exists_by_canon_or_cid(self, canonical_url: str, content_id: str) -> bool:
        r = self.db.fetchone(
            """
            SELECT status
            FROM assets
            WHERE canonical_url = ? OR content_id = ?
            ORDER BY last_checked DESC
            LIMIT 1
            """,
            (canonical_url, content_id),
        )
        if not r:
            return False
        status = (r["status"] or "").lower()
        # suppress only if previously good-ish
        if "200 ok" in status or "sniffed" in status or "mega" in status:
            return True
        return False

    def upsert_asset(
        self,
        asset: Dict[str, Any],
        *,
        canonical_url: str,
        content_id: str,
        synthetic_tags: Set[str],
    ) -> None:
        """
        Inserts or replaces, preserving first_seen.
        synthetic_tags decides synthetic and seed_ok fields.
        """
        raw_url = asset.get("url") or ""
        if not raw_url:
            return

        tag = (asset.get("tag") or "").lower()
        synthetic = 1 if tag in synthetic_tags else 0
        seed_ok = 0 if synthetic else 1

        exists = self.db.fetchone("SELECT 1 FROM assets WHERE url = ?", (raw_url,)) is not None
        if exists:
            self.db.execute(
                """
                UPDATE assets
                SET canonical_url=?, content_id=?, text=?, source=?, size=?, status=?,
                    last_checked=CURRENT_TIMESTAMP, seed_ok=?, synthetic=?
                WHERE url=?
                """,
                (
                    canonical_url,
                    content_id,
                    asset.get("text", ""),
                    asset.get("source_page", "") or asset.get("source", ""),
                    asset.get("size", ""),
                    asset.get("status", ""),
                    seed_ok,
                    synthetic,
                    raw_url,
                ),
            )
        else:
            self.db.execute(
                """
                INSERT INTO assets
                    (url, canonical_url, content_id, text, source, size, status,
                     last_checked, seed_ok, synthetic)
                VALUES (?, ?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP, ?, ?)
                """,
                (
                    raw_url,
                    canonical_url,
                    content_id,
                    asset.get("text", ""),
                    asset.get("source_page", "") or asset.get("source", ""),
                    asset.get("size", ""),
                    asset.get("status", ""),
                    seed_ok,
                    synthetic,
                ),
            )

    def fetch_recent_good_asset_urls(self, limit: int = 100) -> List[str]:
        rows = self.db.fetchall(
            """
            SELECT url FROM assets
            WHERE status LIKE '%OK%'
            ORDER BY last_checked DESC
            LIMIT ?
            """,
            (int(limit),),
        )
        return [r["url"] for r in rows if r["url"]]

    # -------------------- pages -------------------- #

    def page_scanned(self, url: str) -> bool:
        r = self.db.fetchone("SELECT 1 FROM pages WHERE url = ?", (url,))
        return r is not None

    def mark_page_scanned(self, url: str) -> None:
        if not url:
            return
        self.db.execute(
            """
            INSERT OR REPLACE INTO pages (url, last_scanned)
            VALUES (?, CURRENT_TIMESTAMP)
            """,
            (url,),
        )

    # ---------------- cooldown ---------------- #

    def get_recently_returned(self, cooldown_hours: int) -> Set[str]:
        rows = self.db.fetchall(
            """
            SELECT identifier
            FROM recent_returns
            WHERE returned_at >= datetime('now', ?)
            """,
            (f"-{int(cooldown_hours)} hours",),
        )
        return {r["identifier"] for r in rows if r["identifier"]}

    def mark_returned_identifier(self, ident: str) -> None:
        if not ident:
            return
        self.db.execute(
            """
            INSERT OR REPLACE INTO recent_returns(identifier, returned_at)
            VALUES (?, CURRENT_TIMESTAMP)
            """,
            (ident,),
        )

    # ---------------- advanced db intelligence ---------------- #

    def fetch_proven_hubs(self, required_sites: List[str], min_hits: int = 1) -> List[str]:
        site_clause = ""
        args: list[Any] = []

        if required_sites and required_sites != ["*"]:
            clauses = []
            for s in required_sites:
                clauses.append("source LIKE ?")
                args.append(f"%{s}%")
            site_clause = "AND (" + " OR ".join(clauses) + ")"

        q = f"""
            SELECT source, COUNT(*) as hit_count
            FROM assets
            WHERE (status LIKE '%200 OK%' OR status = 'sniffed' OR status LIKE 'MEGA%')
              AND source LIKE 'http%'
              {site_clause}
            GROUP BY source
            HAVING hit_count >= ?
            ORDER BY hit_count DESC
            LIMIT 50
        """
        args.append(int(min_hits))

        rows = self.db.fetchall(q, args)
        return [r["source"] for r in rows if r["source"]]

    def load_database_seeds(
        self,
        *,
        sources: str = "pages",
        limit: int = 400,
        max_age_days: int = 14,
        include_synthetic: bool = False,
        per_domain_cap: int = 8,
    ) -> List[Dict[str, Any]]:
        sources = (sources or "pages").lower().strip()
        limit = max(1, min(int(limit), 10_000))
        max_age_days = max(1, min(int(max_age_days), 3650))

        out: List[Dict[str, Any]] = []

        age_clause_assets = "last_checked >= datetime('now', ?)"
        age_clause_pages  = "last_scanned >= datetime('now', ?)"

        if sources in ("assets", "both"):
            if include_synthetic:
                rows = self.db.fetchall(
                    f"""
                    SELECT url, source
                    FROM assets
                    WHERE {age_clause_assets}
                    ORDER BY last_checked DESC
                    LIMIT ?
                    """,
                    (f"-{max_age_days} days", limit),
                )
            else:
                rows = self.db.fetchall(
                    f"""
                    SELECT url, source
                    FROM assets
                    WHERE seed_ok=1 AND synthetic=0 AND {age_clause_assets}
                    ORDER BY last_checked DESC
                    LIMIT ?
                    """,
                    (f"-{max_age_days} days", limit),
                )
            for r in rows:
                u = r["url"]
                if u:
                    out.append({"url": u, "kind": "asset", "source": r["source"] or "", "tag": "db_seed"})

        if sources in ("pages", "both"):
            rows = self.db.fetchall(
                f"""
                SELECT url
                FROM pages
                WHERE {age_clause_pages}
                ORDER BY last_scanned DESC
                LIMIT ?
                """,
                (f"-{max_age_days} days", limit),
            )
            for r in rows:
                u = r["url"]
                if u:
                    out.append({"url": u, "kind": "page", "source": "", "tag": "db_seed"})

        # dedupe
        seen = set()
        deduped = []
        for s in out:
            u = s["url"]
            if u in seen:
                continue
            seen.add(u)
            deduped.append(s)

        # diversify domains
        by_domain = collections.defaultdict(list)
        for s in deduped:
            d = (urlparse(s["url"]).netloc or "").lower().split(":")[0]
            by_domain[d].append(s)

        domains = list(by_domain.keys())
        random.shuffle(domains)

        diverse: List[Dict[str, Any]] = []
        for d in domains:
            diverse.extend(by_domain[d][:per_domain_cap])

        return diverse[:limit]

    def expand_db_seed_urls(
        self,
        seeds: List[Dict[str, Any]],
        *,
        max_per_seed: int,
        ladder_depth: int,
        per_domain_cap: int,
        max_pages_out: int,
        max_assets_out: int,
        known_url_fn: Callable[[str], bool],
        clean_domain_fn: Callable[[str], str],
        clean_path_fn: Callable[[str], str],
        is_probable_video_url_fn: Callable[[str, str, str], bool],
        archive_ident_to_downloads_fn: Callable[[str], List[str]],
    ) -> Tuple[List[str], List[str]]:
        """
        Store-owned expansion. Block supplies URL heuristics as callables.
        """
        candidate_pages: List[str] = []
        direct_assets: List[str] = []

        domain_counts_pages = collections.Counter()
        domain_counts_assets = collections.Counter()

        def add_page(u: str):
            if not u or u in candidate_pages:
                return
            if known_url_fn(u):
                return
            d = clean_domain_fn(u)
            if d and domain_counts_pages[d] >= per_domain_cap:
                return
            domain_counts_pages[d] += 1
            candidate_pages.append(u)

        def add_asset(u: str):
            if not u or u in direct_assets:
                return
            if known_url_fn(u):
                return
            d = clean_domain_fn(u)
            if d and domain_counts_assets[d] >= per_domain_cap:
                return
            domain_counts_assets[d] += 1
            direct_assets.append(u)

        if not seeds:
            return [], []

        from urllib.parse import urlparse

        def ladder_up(u: str, depth: int) -> List[str]:
            out = []
            try:
                pu = urlparse(u)
                base = f"{pu.scheme}://{pu.netloc}"
                path = pu.path or "/"
                if not path.endswith("/"):
                    path = path.rsplit("/", 1)[0] + "/"
                parts = [p for p in path.split("/") if p]
                for k in range(min(depth, len(parts)), 0, -1):
                    parent = base + "/" + "/".join(parts[:k]) + "/"
                    out.append(parent)
                out.append(base + "/")
            except Exception:
                return []
            return list(dict.fromkeys(out))

        def archive_expansions(u: str) -> List[str]:
            out = []
            try:
                pu = urlparse(u)
                host = pu.netloc.lower()
                if "archive.org" not in host:
                    return []
                path = pu.path.strip("/")
                ident = ""
                parts = path.split("/")
                if parts:
                    if parts[0] in ("details", "download") and len(parts) >= 2:
                        ident = parts[1]
                    elif len(parts) == 1:
                        ident = parts[0]
                if ident:
                    out.extend(archive_ident_to_downloads_fn(ident))
            except Exception:
                return []
            return list(dict.fromkeys(out))

        for s in seeds:
            if len(candidate_pages) >= max_pages_out and len(direct_assets) >= max_assets_out:
                break

            seed_url = (s.get("url") or "").strip()
            if not seed_url:
                continue

            added_for_seed = 0

            spath = clean_path_fn(seed_url)
            if is_probable_video_url_fn(seed_url, spath, seed_url.lower()):
                add_asset(seed_url)
                added_for_seed += 1
                if added_for_seed >= max_per_seed:
                    continue

            for au in archive_expansions(seed_url):
                if added_for_seed >= max_per_seed:
                    break
                apath = clean_path_fn(au)
                if is_probable_video_url_fn(au, apath, au.lower()):
                    add_asset(au)
                else:
                    add_page(au)
                added_for_seed += 1

            for pu in ladder_up(seed_url, ladder_depth):
                if added_for_seed >= max_per_seed:
                    break
                add_page(pu)
                added_for_seed += 1

        return (
            list(dict.fromkeys(candidate_pages))[:max_pages_out],
            list(dict.fromkeys(direct_assets))[:max_assets_out],
        )

    def extract_urls_from_db_text(
        self,
        *,
        limit_rows: int,
        max_urls: int,
        include_synthetic: bool,
        url_regex,
    ) -> List[str]:
        where = "text IS NOT NULL"
        if not include_synthetic:
            where += " AND seed_ok=1 AND synthetic=0"

        rows = self.db.fetchall(
            f"""
            SELECT text FROM assets
            WHERE {where}
            ORDER BY last_checked DESC
            LIMIT ?
            """,
            (int(limit_rows),),
        )

        out: List[str] = []
        for r in rows:
            txt = r["text"]
            if not txt:
                continue

            tl = txt.lstrip().lower()
            looks_manifest = "#extm3u" in tl or "m3u8" in tl or "dash" in tl
            looks_json = tl.startswith("{") or tl.startswith("[")
            if not (looks_manifest or looks_json):
                continue

            for m in url_regex.finditer(txt):
                u = m.group(0)
                if u:
                    out.append(u)
                    if len(out) >= max_urls:
                        break
            if len(out) >= max_urls:
                break

        return list(dict.fromkeys(out))


# ======================================================================
# PageTrackerStore (Add to submanagers.py or near LinkTrackerStore)
# ======================================================================

class PageTrackerStore(BaseStore):
    """
    Store specifically for PageTrackerBlock.
    Tracks discovered HTML pages, their titles, and scores to build a crawl frontier.
    """

    # We use a distinct table 'discovered_pages' to avoid polluting the 'assets' table
    # used by Link/Video trackers.
    PAGES_DDL = """
    CREATE TABLE IF NOT EXISTS discovered_pages
    (
        url TEXT PRIMARY KEY,
        title TEXT,
        source_url TEXT,
        depth INTEGER DEFAULT 0,
        score INTEGER DEFAULT 0,
        status TEXT,
        last_scanned TIMESTAMP,
        first_seen TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    )
    """

    # We still track visited history to prevent loops
    HISTORY_DDL = """
    CREATE TABLE IF NOT EXISTS scan_history
    (
        url TEXT PRIMARY KEY,
        last_checked TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    )
    """

    INDEXES_DDL = [
        "CREATE INDEX IF NOT EXISTS idx_dp_score ON discovered_pages (score)",
        "CREATE INDEX IF NOT EXISTS idx_dp_source ON discovered_pages (source_url)",
        "CREATE INDEX IF NOT EXISTS idx_sh_last ON scan_history (last_checked)",
    ]

    def ensure_schema(self) -> None:
        self.db.ensure_schema([self.PAGES_DDL, self.HISTORY_DDL, *self.INDEXES_DDL])

    # -------------------- Writing Data -------------------- #

    def upsert_page(self, page_data: Dict[str, Any]) -> None:
        """
        Save a discovered page. Updates score/title if found again.
        """
        url = page_data.get("url", "").strip()
        if not url:
            return

        # Simple check if exists
        exists = self.db.fetchone("SELECT 1 FROM discovered_pages WHERE url = ?", (url,))

        if exists:
            # Update meta if the new find has better data
            self.db.execute(
                """
                UPDATE discovered_pages
                SET title = coalesce(?, title),
                    score = max(score, ?),
                    depth = min(depth, ?),
                    status = ?
                WHERE url = ?
                """,
                (
                    page_data.get("title"),
                    int(page_data.get("score", 0)),
                    int(page_data.get("depth", 99)),
                    page_data.get("status", "found"),
                    url,
                ),
            )
        else:
            self.db.execute(
                """
                INSERT INTO discovered_pages (url, title, source_url, depth, score, status)
                VALUES (?, ?, ?, ?, ?, ?)
                """,
                (
                    url,
                    page_data.get("title", ""),
                    page_data.get("source", ""),
                    int(page_data.get("depth", 0)),
                    int(page_data.get("score", 0)),
                    page_data.get("status", "found"),
                ),
            )

    def mark_scan_complete(self, url: str) -> None:
        """Mark a page as 'visited' in the history table."""
        self.db.execute(
            "INSERT OR REPLACE INTO scan_history (url, last_checked) VALUES (?, CURRENT_TIMESTAMP)",
            (url,)
        )
        # Also update the main table to reflect recent scan
        self.db.execute(
            "UPDATE discovered_pages SET last_scanned = CURRENT_TIMESTAMP WHERE url = ?",
            (url,)
        )

    # -------------------- Reading Data (Engine=Database) -------------------- #

    def is_recently_scanned(self, url: str, days: Optional[int] = None) -> bool:
        if days is None:
            # Just check if it exists in history
            r = self.db.fetchone("SELECT 1 FROM scan_history WHERE url = ?", (url,))
            return r is not None

        # Check date
        q = f"SELECT 1 FROM scan_history WHERE url = ? AND last_checked >= datetime('now', '-{int(days)} days')"
        r = self.db.fetchone(q, (url,))
        return r is not None

    def fetch_seed_pages(
            self,
            limit: int = 200,
            required_sites: Optional[List[str]] = None,
            keywords: Optional[List[str]] = None,
            min_score: int = 0
    ) -> List[str]:
        """
        Intelligent fetch: Get pages that match site/keyword criteria,
        prioritizing high scores and those NOT scanned recently.
        """
        where_clauses = []
        args = []

        # Filter by site
        if required_sites:
            site_parts = []
            for s in required_sites:
                site_parts.append("url LIKE ?")
                args.append(f"%{s}%")
            where_clauses.append(f"({' OR '.join(site_parts)})")

        # Filter by keywords (in URL or Title)
        if keywords:
            kw_parts = []
            for k in keywords:
                term = f"%{k}%"
                kw_parts.append("(url LIKE ? OR title LIKE ?)")
                args.extend([term, term])
            where_clauses.append(f"({' OR '.join(kw_parts)})")

        # Filter by score
        where_clauses.append("score >= ?")
        args.append(min_score)

        # Construct SQL
        where_sql = "WHERE " + " AND ".join(where_clauses) if where_clauses else ""

        # Order by: Score (High) -> Depth (Low) -> Random
        query = f"""
            SELECT url 
            FROM discovered_pages
            {where_sql}
            ORDER BY score DESC, depth ASC
            LIMIT ?
        """
        args.append(limit)

        rows = self.db.fetchall(query, args)
        return [r["url"] for r in rows]

# ======================================================================
# WebCorpusStore  (place with your other Stores, e.g. in submanagers.py)
# ======================================================================

@dataclass
class WebPageRecord:
    url: str
    domain: str
    title: str
    content: str
    engine: str
    query: str
    fetched_at: str | None = None


class WebCorpusStore:
    """
    Persistent cache of fetched web pages.

    Responsibilities:
      • Own the schema for web corpus pages.
      • Provide URL-based load/save helpers.
      • Optionally expose recent pages (by engine/query) later if needed.
    """

    def __init__(self, db: "DatabaseSubmanager"):
        self.db = db
        self._schema_ready = False

    # ---------------- schema ---------------- #

    def ensure_schema(self) -> None:
        if self._schema_ready:
            return

        ddl = [
            """
            CREATE TABLE IF NOT EXISTS web_pages (
                id         INTEGER PRIMARY KEY AUTOINCREMENT,
                url        TEXT UNIQUE,
                domain     TEXT,
                title      TEXT,
                content    TEXT,
                engine     TEXT,
                query      TEXT,
                fetched_at DATETIME DEFAULT CURRENT_TIMESTAMP
            );
            """,
            """
            CREATE INDEX IF NOT EXISTS idx_web_pages_domain
                ON web_pages (domain);
            """,
            """
            CREATE INDEX IF NOT EXISTS idx_web_pages_engine_query
                ON web_pages (engine, query);
            """,
        ]
        self.db.ensure_schema(ddl)
        self._schema_ready = True

    # ---------------- helpers ---------------- #

    def _row_to_record(self, row: sqlite3.Row | None) -> WebPageRecord | None:
        if row is None:
            return None
        return WebPageRecord(
            url=row["url"],
            domain=row["domain"],
            title=row["title"],
            content=row["content"],
            engine=row["engine"],
            query=row["query"],
            fetched_at=row["fetched_at"],
        )

    def get_page(self, url: str) -> WebPageRecord | None:
        sql = """
        SELECT url, domain, title, content, engine, query, fetched_at
        FROM web_pages
        WHERE url = ?
        """
        row = self.db.fetchone(sql, (url,))
        return self._row_to_record(row)

    def save_page(
        self,
        *,
        url: str,
        title: str,
        content: str,
        engine: str,
        query: str,
    ) -> None:
        from urllib.parse import urlparse

        domain = ""
        try:
            domain = (urlparse(url).netloc or "").split(":")[0].lower()
        except Exception:
            pass

        sql = """
        INSERT OR REPLACE INTO web_pages
            (url, domain, title, content, engine, query, fetched_at)
        VALUES
            (?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
        """
        self.db.execute(sql, (url, domain, title, content, engine, query))

# ======================================================================
# PlaywrightCorpusStore
# ======================================================================

@dataclass
class PlaywrightCorpusStore:
    """
    Store for PlaywrightBlock:
      - Caches per-URL text/html + sniffed assets/links.
      - All DB access goes through DatabaseSubmanager.
    """

    db: DatabaseSubmanager
    logger: Any = None

    # Main table: one row per URL
    DDL: ClassVar[list[str]] = [
        """
        CREATE TABLE IF NOT EXISTS playwright_pages (
            url             TEXT PRIMARY KEY,
            title           TEXT,
            content         TEXT,
            html            TEXT,
            js_links_json   TEXT,
            net_items_json  TEXT,
            json_hits_json  TEXT,
            fetched_at      DATETIME DEFAULT CURRENT_TIMESTAMP
        );
        """
    ]

    def _log(self, msg: str) -> None:
        try:
            if self.logger is not None:
                self.logger.log_message(f"[PlaywrightCorpusStore] {msg}")
            else:
                print(f"[PlaywrightCorpusStore] {msg}")
        except Exception:
            pass

    def ensure_schema(self) -> None:
        self.db.ensure_schema(self.DDL)

    def load_page(self, url: str) -> Optional[dict]:
        row = self.db.fetchone(
            "SELECT url, title, content, html, js_links_json, net_items_json, json_hits_json, fetched_at "
            "FROM playwright_pages WHERE url = ?",
            [url],
        )
        if not row:
            return None

        import json

        def _maybe_json(x: str | None):
            if not x:
                return []
            try:
                return json.loads(x)
            except Exception:
                return []

        return {
            "url": row["url"],
            "title": row["title"] or "",
            "content": row["content"] or "",
            "html": row["html"] or "",
            "js_links": _maybe_json(row["js_links_json"]),
            "net_items": _maybe_json(row["net_items_json"]),
            "json_hits": _maybe_json(row["json_hits_json"]),
            "fetched_at": row["fetched_at"],
        }

    def save_page(
        self,
        url: str,
        title: str,
        content: str,
        html: str,
        *,
        js_links: Optional[list[dict]] = None,
        net_items: Optional[list[dict]] = None,
        json_hits: Optional[list[dict]] = None,
    ) -> None:
        import json

        js_links_json = json.dumps(js_links or [], ensure_ascii=False)
        net_items_json = json.dumps(net_items or [], ensure_ascii=False)
        json_hits_json = json.dumps(json_hits or [], ensure_ascii=False)

        self.db.execute(
            """
            INSERT OR REPLACE INTO playwright_pages
            (url, title, content, html, js_links_json, net_items_json, json_hits_json, fetched_at)
            VALUES (?, ?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
            """,
            [url, title, content, html, js_links_json, net_items_json, json_hits_json],
        )

# ======================================================================
# CodeCorpusStore
# ======================================================================

@dataclass
class CodeCorpusStore:
    """
    Store for code snippets + URL tracking, backed by DatabaseSubmanager.

    Tables:
      • code_docs
          id, url, title, content, kind, created_at, updated_at
      • code_indexed_urls
          url, last_scraped_time
    """

    dbm: DatabaseSubmanager
    logger: Any = None

    # ---------- logging helper ----------

    def log(self, msg: str) -> None:
        if self.logger:
            try:
                self.logger.log_message(f"[CodeCorpusStore] {msg}")
                return
            except Exception:
                pass
        print(f"[CodeCorpusStore] {msg}")

    # ---------- schema management ----------

    def ensure_schema(self) -> None:
        """
        Ensure all tables/indexes exist, using DatabaseSubmanager.ensure_schema().
        """
        ddl_statements: Sequence[str] = [
            # Core table for snippets
            """
            CREATE TABLE IF NOT EXISTS code_docs (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                url TEXT NOT NULL,
                title TEXT,
                content TEXT NOT NULL,
                kind TEXT NOT NULL DEFAULT 'code',
                created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                updated_at DATETIME DEFAULT CURRENT_TIMESTAMP
            );
            """,
            # Unique constraint to avoid duplicate snippets per URL/content
            """
            CREATE UNIQUE INDEX IF NOT EXISTS idx_code_docs_url_content
            ON code_docs (url, content);
            """,
            # Tracking table for scraping times
            """
            CREATE TABLE IF NOT EXISTS code_indexed_urls (
                url TEXT PRIMARY KEY,
                last_scraped_time REAL NOT NULL
            );
            """,
        ]
        self.dbm.ensure_schema(ddl_statements)

    # ---------- URL tracking helpers ----------

    def get_last_scraped_time(self, url: str) -> float:
        """
        Return last_scraped_time for URL, or 0.0 if not present.
        """
        ts = self.dbm.scalar(
            "SELECT last_scraped_time FROM code_indexed_urls WHERE url = ?",
            (url,),
        )
        if ts is None:
            return 0.0
        try:
            return float(ts)
        except Exception:
            return 0.0

    def mark_scraped(self, url: str, ts: float) -> None:
        """
        Upsert last_scraped_time for a URL.
        """
        self.dbm.execute(
            """
            INSERT OR REPLACE INTO code_indexed_urls (url, last_scraped_time)
            VALUES (?, ?);
            """,
            (url, ts),
        )

    def clear_for_domains(self, domains: List[str]) -> None:
        """
        Clears all docs + tracking rows for given domains.
        """
        clean = [d for d in {d.strip().lower() for d in domains} if d]
        if not clean:
            return

        patterns: List[str] = []
        for d in clean:
            patterns.append(f"https://{d}%")
            patterns.append(f"http://{d}%")

        if not patterns:
            return

        placeholders = " OR ".join(["url LIKE ?"] * len(patterns))

        # Delete from docs
        self.dbm.execute(
            f"DELETE FROM code_docs WHERE {placeholders};",
            tuple(patterns),
        )

        # Delete from tracking table
        self.dbm.execute(
            f"DELETE FROM code_indexed_urls WHERE {placeholders};",
            tuple(patterns),
        )

        self.log(f"Cleared docs + tracking for domains: {', '.join(clean)}")

    # ---------- snippet CRUD ----------

    def upsert_snippet(self, url: str, title: str, content: str, kind: str = "code") -> None:
        """
        Insert or update a code snippet for (url, content).

        Preserves original created_at if the row already exists,
        and bumps updated_at on each upsert.
        """
        self.dbm.execute(
            """
            INSERT OR REPLACE INTO code_docs (id, url, title, content, kind, created_at, updated_at)
            VALUES (
                COALESCE(
                    (SELECT id FROM code_docs WHERE url = ? AND content = ?),
                    NULL
                ),
                ?, ?, ?, ?,
                COALESCE(
                    (SELECT created_at FROM code_docs WHERE url = ? AND content = ?),
                    CURRENT_TIMESTAMP
                ),
                CURRENT_TIMESTAMP
            );
            """,
            (url, content, url, title, content, kind, url, content),
        )

# ======================================================================
# LinkCrawler
# ======================================================================

class LinkCrawlerStore(BaseStore):
    """
    Store for LinkCrawlerBlock.

    Responsibilities:
      - Persist "already emitted" URLs so subsequent runs won't re-feed them.
      - Persist seed fetch history so we can skip re-fetching pages too frequently.
    """

    EMITTED_DDL = """
    CREATE TABLE IF NOT EXISTS linkcrawler_emitted
    (
        url TEXT PRIMARY KEY,
        first_seen_ts REAL NOT NULL,
        last_seen_ts REAL NOT NULL,
        mode TEXT,
        query TEXT
    )
    """

    SEED_FETCH_DDL = """
    CREATE TABLE IF NOT EXISTS linkcrawler_seed_fetch
    (
        seed_url TEXT PRIMARY KEY,
        last_fetch_ts REAL NOT NULL,
        last_status INTEGER NOT NULL
    )
    """

    INDEXES_DDL = [
        "CREATE INDEX IF NOT EXISTS idx_lc_emitted_last_seen ON linkcrawler_emitted (last_seen_ts)",
        "CREATE INDEX IF NOT EXISTS idx_lc_seed_last_fetch ON linkcrawler_seed_fetch (last_fetch_ts)",
    ]

    def ensure_schema(self) -> None:
        self.db.ensure_schema([self.EMITTED_DDL, self.SEED_FETCH_DDL, *self.INDEXES_DDL])

    # -------------------- Emitted -------------------- #

    def has_emitted(self, url: str) -> bool:
        url = (url or "").strip()
        if not url:
            return False
        r = self.db.fetchone("SELECT 1 FROM linkcrawler_emitted WHERE url=? LIMIT 1", (url,))
        return r is not None

    def mark_emitted(self, url: str, *, mode: str, query: str, now_ts: Optional[float] = None) -> None:
        url = (url or "").strip()
        if not url:
            return
        ts = float(now_ts if now_ts is not None else time.time())
        self.db.execute(
            """
            INSERT INTO linkcrawler_emitted(url, first_seen_ts, last_seen_ts, mode, query)
            VALUES(?, ?, ?, ?, ?)
            ON CONFLICT(url) DO UPDATE SET
                last_seen_ts=excluded.last_seen_ts,
                mode=excluded.mode,
                query=excluded.query
            """,
            (url, ts, ts, mode or "", query or ""),
        )

    # -------------------- Seed fetch TTL -------------------- #

    def seed_should_fetch(self, seed_url: str, *, ttl_seconds: float, now_ts: Optional[float] = None) -> bool:
        seed_url = (seed_url or "").strip()
        if not seed_url:
            return False
        ts = float(now_ts if now_ts is not None else time.time())
        ttl = float(ttl_seconds)

        r = self.db.fetchone(
            "SELECT last_fetch_ts FROM linkcrawler_seed_fetch WHERE seed_url=? LIMIT 1",
            (seed_url,),
        )
        if not r:
            return True

        last_ts = float(r["last_fetch_ts"] or 0.0)
        return (ts - last_ts) >= ttl

    def seed_mark_fetched(self, seed_url: str, *, status: int, now_ts: Optional[float] = None) -> None:
        seed_url = (seed_url or "").strip()
        if not seed_url:
            return
        ts = float(now_ts if now_ts is not None else time.time())
        self.db.execute(
            """
            INSERT INTO linkcrawler_seed_fetch(seed_url, last_fetch_ts, last_status)
            VALUES(?, ?, ?)
            ON CONFLICT(seed_url) DO UPDATE SET
                last_fetch_ts=excluded.last_fetch_ts,
                last_status=excluded.last_status
            """,
            (seed_url, ts, int(status)),
        )

# ======================================================================
# Optional DB Store (small, self-contained)
# ======================================================================

class LinkContentCrawlerStore:
    """
    Very small store:
      - emitted(url): suppress cross-run duplicates
      - seed fetch TTL: avoid re-fetching the same seed URL too frequently
    """

    def __init__(self, db):
        self.db = db

    def ensure_schema(self):
        self.db.exec("""
        CREATE TABLE IF NOT EXISTS linkcontent_emitted (
            url TEXT PRIMARY KEY,
            first_seen REAL,
            source TEXT,
            kind TEXT,
            score INTEGER
        )
        """)
        self.db.exec("""
        CREATE TABLE IF NOT EXISTS linkcontent_seed_fetch (
            url TEXT PRIMARY KEY,
            last_fetch REAL,
            last_status INTEGER
        )
        """)
        self.db.exec("CREATE INDEX IF NOT EXISTS idx_lcc_seed_fetch_ts ON linkcontent_seed_fetch(last_fetch)")
        self.db.commit()

    def has_emitted(self, url: str) -> bool:
        row = self.db.one("SELECT 1 FROM linkcontent_emitted WHERE url=?", (url,))
        return bool(row)

    def mark_emitted(self, url: str, *, now_ts: float, source: str, kind: str, score: int):
        self.db.exec(
            "INSERT OR REPLACE INTO linkcontent_emitted(url, first_seen, source, kind, score) VALUES(?,?,?,?,?)",
            (url, float(now_ts), source or "", kind or "", int(score)),
        )
        self.db.commit()

    def seed_should_fetch(self, url: str, *, ttl_seconds: float, now_ts: float) -> bool:
        row = self.db.one("SELECT last_fetch FROM linkcontent_seed_fetch WHERE url=?", (url,))
        if not row:
            return True
        last = float(row[0] or 0.0)
        return (now_ts - last) >= float(ttl_seconds)

    def seed_mark_fetched(self, url: str, *, now_ts: float, status: int):
        self.db.exec(
            "INSERT OR REPLACE INTO linkcontent_seed_fetch(url, last_fetch, last_status) VALUES(?,?,?)",
            (url, float(now_ts), int(status)),
        )
        self.db.commit()

# ======================================================================
# Store (DB-backed) for CDNBlock
# ======================================================================

class CDNStore:
    """
    Stores:
      - cdn_emitted: suppresses already-emitted CDN urls across runs
      - cdn_seed_fetch: TTL gating for seed URL fetches
    """

    DDL: Sequence[str] = (
        """
        CREATE TABLE IF NOT EXISTS cdn_emitted (
            url TEXT PRIMARY KEY,
            host TEXT,
            kind TEXT,
            source_seed TEXT,
            first_seen REAL,
            last_seen REAL,
            score INTEGER
        );
        """,
        """
        CREATE TABLE IF NOT EXISTS cdn_seed_fetch (
            seed_url TEXT PRIMARY KEY,
            last_fetch_ts REAL,
            status INTEGER
        );
        """,
        "CREATE INDEX IF NOT EXISTS idx_cdn_emitted_host ON cdn_emitted(host);",
    )

    def __init__(self, db):
        self.db = db

    def ensure_schema(self) -> None:
        self.db.ensure_schema(self.DDL)
        # micro-migrations (safe no-ops if already present)
        try:
            self.db.ensure_columns("cdn_emitted", {
                "host": "TEXT",
                "kind": "TEXT",
                "source_seed": "TEXT",
                "first_seen": "REAL",
                "last_seen": "REAL",
                "score": "INTEGER",
            })
            self.db.ensure_columns("cdn_seed_fetch", {
                "last_fetch_ts": "REAL",
                "status": "INTEGER",
            })
        except Exception:
            pass

    # ---------------- TTL gating for seeds ----------------

    def seed_should_fetch(self, seed_url: str, *, ttl_seconds: float, now_ts: float) -> bool:
        if not seed_url:
            return False
        try:
            row = self.db.fetchone(
                "SELECT last_fetch_ts FROM cdn_seed_fetch WHERE seed_url=?",
                [seed_url],
            )
            if not row:
                return True
            last_ts = float(row["last_fetch_ts"] or 0.0)
            return (now_ts - last_ts) >= float(ttl_seconds)
        except Exception:
            return True

    def seed_mark_fetched(self, seed_url: str, *, now_ts: float, status: int) -> None:
        if not seed_url:
            return
        try:
            self.db.execute(
                """
                INSERT INTO cdn_seed_fetch(seed_url, last_fetch_ts, status)
                VALUES(?,?,?)
                ON CONFLICT(seed_url) DO UPDATE SET
                    last_fetch_ts=excluded.last_fetch_ts,
                    status=excluded.status
                """,
                [seed_url, float(now_ts), int(status)],
            )
        except Exception:
            pass

    # ---------------- emitted suppression ----------------

    def has_emitted(self, url: str) -> bool:
        if not url:
            return False
        try:
            row = self.db.fetchone("SELECT 1 FROM cdn_emitted WHERE url=? LIMIT 1", [url])
            return bool(row)
        except Exception:
            return False

    def mark_emitted(
        self,
        url: str,
        *,
        host: str,
        kind: str,
        source_seed: str,
        score: int,
        now_ts: float,
    ) -> None:
        if not url:
            return
        try:
            self.db.execute(
                """
                INSERT INTO cdn_emitted(url, host, kind, source_seed, first_seen, last_seen, score)
                VALUES(?,?,?,?,?,?,?)
                ON CONFLICT(url) DO UPDATE SET
                    last_seen=excluded.last_seen,
                    host=excluded.host,
                    kind=excluded.kind,
                    source_seed=excluded.source_seed,
                    score=excluded.score
                """,
                [url, host, kind, source_seed, float(now_ts), float(now_ts), int(score)],
            )
        except Exception:
            pass


# ======================================================================
# Store (DB-backed) for DirectLinkTracker
# ======================================================================

class DirectLinkTrackerStore:
    """
    SQLite-backed store for DirectLinkTracker.

    Schema matches your LinkTrackerBlock-style tables:
      - assets(url PK, text, source, size, status, first_seen, last_checked)
      - pages(url PK, last_scanned)
    """
    db_path: str = "link_corpus.db"

    def __post_init__(self) -> None:
        self._conn: Optional[sqlite3.Connection] = None

    # ---------------------------
    # lifecycle
    # ---------------------------
    def open(self) -> None:
        if self._conn:
            return
        db_path = str(self.db_path or "link_corpus.db")
        existed = Path(db_path).exists()

        self._conn = sqlite3.connect(db_path)
        cur = self._conn.cursor()

        cur.execute(
            """
            CREATE TABLE IF NOT EXISTS assets
            (
                url TEXT PRIMARY KEY,
                text TEXT,
                source TEXT,
                size TEXT,
                status TEXT,
                first_seen TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                last_checked TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """
        )
        cur.execute("CREATE INDEX IF NOT EXISTS idx_assets_source ON assets (source)")

        cur.execute(
            """
            CREATE TABLE IF NOT EXISTS pages
            (
                url TEXT PRIMARY KEY,
                last_scanned TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """
        )
        cur.execute("CREATE INDEX IF NOT EXISTS idx_pages_last_scanned ON pages (last_scanned)")
        self._conn.commit()

        print(f"[DirectLinkTrackerStore] {'Using existing' if existed else 'Database created'} at {db_path}")

    def close(self) -> None:
        if self._conn:
            try:
                self._conn.close()
            except Exception:
                pass
            self._conn = None

    def __enter__(self) -> "DirectLinkTrackerStore":
        self.open()
        return self

    def __exit__(self, exc_type, exc, tb) -> None:
        self.close()

    @property
    def conn(self) -> Optional[sqlite3.Connection]:
        return self._conn

    # ---------------------------
    # pages
    # ---------------------------
    def is_page_scanned(self, url: str) -> bool:
        if not self._conn:
            return False
        try:
            cur = self._conn.cursor()
            cur.execute("SELECT 1 FROM pages WHERE url = ?", (url,))
            return cur.fetchone() is not None
        except Exception:
            return False

    def mark_page_scanned(self, url: str) -> None:
        if not self._conn:
            return
        try:
            cur = self._conn.cursor()
            cur.execute(
                "INSERT OR REPLACE INTO pages (url, last_scanned) VALUES (?, CURRENT_TIMESTAMP)",
                (url,),
            )
            self._conn.commit()
        except Exception:
            pass

    # ---------------------------
    # assets
    # ---------------------------
    def is_asset_url(self, url: str) -> bool:
        if not self._conn:
            return False
        try:
            cur = self._conn.cursor()
            cur.execute("SELECT 1 FROM assets WHERE url = ?", (url,))
            return cur.fetchone() is not None
        except Exception:
            return False

    def upsert_asset(self, asset: Dict[str, Any]) -> None:
        if not self._conn:
            return
        u = (asset or {}).get("url", "") or ""
        if not u:
            return
        try:
            cur = self._conn.cursor()
            cur.execute("SELECT first_seen FROM assets WHERE url = ?", (u,))
            row = cur.fetchone()
            if row:
                cur.execute(
                    """
                    UPDATE assets
                    SET status=?, last_checked=CURRENT_TIMESTAMP, size=?, source=?, text=?
                    WHERE url=?
                    """,
                    (
                        asset.get("status", ""),
                        asset.get("size", ""),
                        asset.get("source", ""),
                        asset.get("text", ""),
                        u,
                    ),
                )
            else:
                cur.execute(
                    """
                    INSERT INTO assets(url,text,source,size,status,last_checked)
                    VALUES (?,?,?,?,?,CURRENT_TIMESTAMP)
                    """,
                    (
                        u,
                        asset.get("text", ""),
                        asset.get("source", ""),
                        asset.get("size", ""),
                        asset.get("status", ""),
                    ),
                )
            self._conn.commit()
        except Exception:
            pass