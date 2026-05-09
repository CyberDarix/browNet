"""
Secure SQL database manager for market signal storage.

Uses SQLite by default (zero-config) with a clean schema for all signal types.
Designed for easy migration to PostgreSQL or MySQL if needed.
"""

import json
import logging
import sqlite3
from typing import Dict, List, Any, Optional
from datetime import datetime, timezone

logger = logging.getLogger("market_signal_crawler.database")


# ============================================================================
# SQL Schema
# ============================================================================

SCHEMA_SQL = """
-- Crawl sessions tracking
CREATE TABLE IF NOT EXISTS crawl_sessions (
    id              INTEGER PRIMARY KEY AUTOINCREMENT,
    started_at      TEXT NOT NULL,
    finished_at     TEXT,
    status          TEXT DEFAULT 'running',
    pages_crawled   INTEGER DEFAULT 0,
    signals_stored  INTEGER DEFAULT 0,
    config_snapshot TEXT
);

-- Main signals table (all signal types)
CREATE TABLE IF NOT EXISTS market_signals (
    id                INTEGER PRIMARY KEY AUTOINCREMENT,
    session_id        INTEGER,
    source_url        TEXT NOT NULL,
    signal_type       TEXT NOT NULL,
    label             TEXT,
    value             TEXT,
    currency          TEXT,
    extraction_method TEXT,
    categories        TEXT,
    published_at      TEXT,
    extracted_at      TEXT NOT NULL,
    created_at        TEXT DEFAULT (datetime('now')),
    FOREIGN KEY (session_id) REFERENCES crawl_sessions(id)
);

-- RSS articles with richer structure
CREATE TABLE IF NOT EXISTS rss_articles (
    id              INTEGER PRIMARY KEY AUTOINCREMENT,
    session_id      INTEGER,
    feed_url        TEXT NOT NULL,
    title           TEXT NOT NULL,
    summary         TEXT,
    link            TEXT,
    published_at    TEXT,
    categories      TEXT,
    extracted_at    TEXT NOT NULL,
    created_at      TEXT DEFAULT (datetime('now')),
    FOREIGN KEY (session_id) REFERENCES crawl_sessions(id)
);

-- Crawled pages log (for deduplication and audit)
CREATE TABLE IF NOT EXISTS crawl_log (
    id              INTEGER PRIMARY KEY AUTOINCREMENT,
    session_id      INTEGER,
    url             TEXT NOT NULL,
    domain          TEXT NOT NULL,
    status_code     INTEGER,
    content_length  INTEGER,
    crawled_at      TEXT NOT NULL,
    robots_allowed  INTEGER DEFAULT 1,
    signals_found   INTEGER DEFAULT 0,
    FOREIGN KEY (session_id) REFERENCES crawl_sessions(id)
);

-- Indexes for common queries
CREATE INDEX IF NOT EXISTS idx_signals_type ON market_signals(signal_type);
CREATE INDEX IF NOT EXISTS idx_signals_source ON market_signals(source_url);
CREATE INDEX IF NOT EXISTS idx_signals_extracted ON market_signals(extracted_at);
CREATE INDEX IF NOT EXISTS idx_rss_feed ON rss_articles(feed_url);
CREATE INDEX IF NOT EXISTS idx_rss_published ON rss_articles(published_at);
CREATE INDEX IF NOT EXISTS idx_crawl_domain ON crawl_log(domain);
CREATE INDEX IF NOT EXISTS idx_crawl_url ON crawl_log(url);
""".strip()


class SignalDatabase:
    """Thread-safe SQLite database manager for market signals."""

    def __init__(self, db_path: str = "market_signals.db"):
        self.db_path = db_path
        self._conn: Optional[sqlite3.Connection] = None

    def connect(self) -> None:
        """Open database connection and initialize schema."""
        self._conn = sqlite3.connect(self.db_path, check_same_thread=False)
        self._conn.row_factory = sqlite3.Row
        self._conn.execute("PRAGMA journal_mode=WAL")
        self._conn.execute("PRAGMA foreign_keys=ON")
        self._conn.executescript(SCHEMA_SQL)
        self._conn.commit()
        logger.info("Database connected: %s", self.db_path)

    def close(self) -> None:
        if self._conn:
            self._conn.close()
            self._conn = None

    @property
    def conn(self) -> sqlite3.Connection:
        if self._conn is None:
            raise RuntimeError("Database not connected. Call connect() first.")
        return self._conn

    # --- Session management ---

    def start_session(self, config_snapshot: Optional[str] = None) -> int:
        cursor = self.conn.execute(
            "INSERT INTO crawl_sessions (started_at, config_snapshot) VALUES (?, ?)",
            (datetime.now(timezone.utc).isoformat(), config_snapshot),
        )
        self.conn.commit()
        session_id = cursor.lastrowid
        logger.info("Started crawl session #%d", session_id)
        return session_id

    def end_session(self, session_id: int, pages: int, signals: int) -> None:
        self.conn.execute(
            "UPDATE crawl_sessions SET finished_at=?, status='completed', "
            "pages_crawled=?, signals_stored=? WHERE id=?",
            (datetime.now(timezone.utc).isoformat(), pages, signals, session_id),
        )
        self.conn.commit()

    # --- Signal storage ---

    def store_signal(self, session_id: int, signal: Dict[str, Any]) -> int:
        cursor = self.conn.execute(
            "INSERT INTO market_signals "
            "(session_id, source_url, signal_type, label, value, currency, "
            "extraction_method, categories, published_at, extracted_at) "
            "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
            (
                session_id,
                signal.get("source_url", ""),
                signal.get("signal_type", "unknown"),
                signal.get("label", ""),
                signal.get("value", ""),
                signal.get("currency", ""),
                signal.get("extraction_method", ""),
                signal.get("categories", ""),
                signal.get("published_at", ""),
                signal.get("extracted_at", datetime.now(timezone.utc).isoformat()),
            ),
        )
        self.conn.commit()
        return cursor.lastrowid

    def store_signals_batch(self, session_id: int, signals: List[Dict[str, Any]]) -> int:
        """Store multiple signals in a single transaction."""
        count = 0
        with self.conn:
            for signal in signals:
                self.conn.execute(
                    "INSERT INTO market_signals "
                    "(session_id, source_url, signal_type, label, value, currency, "
                    "extraction_method, categories, published_at, extracted_at) "
                    "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
                    (
                        session_id,
                        signal.get("source_url", ""),
                        signal.get("signal_type", "unknown"),
                        signal.get("label", ""),
                        signal.get("value", ""),
                        signal.get("currency", ""),
                        signal.get("extraction_method", ""),
                        signal.get("categories", ""),
                        signal.get("published_at", ""),
                        signal.get("extracted_at", datetime.now(timezone.utc).isoformat()),
                    ),
                )
                count += 1
        return count

    def store_rss_article(self, session_id: int, article: Dict[str, Any]) -> int:
        cursor = self.conn.execute(
            "INSERT INTO rss_articles "
            "(session_id, feed_url, title, summary, link, published_at, categories, extracted_at) "
            "VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
            (
                session_id,
                article.get("source_url", ""),
                article.get("title", ""),
                article.get("summary", ""),
                article.get("link", ""),
                article.get("published_at", ""),
                article.get("categories", ""),
                article.get("extracted_at", datetime.now(timezone.utc).isoformat()),
            ),
        )
        self.conn.commit()
        return cursor.lastrowid

    def store_rss_articles_batch(self, session_id: int, articles: List[Dict[str, Any]]) -> int:
        count = 0
        with self.conn:
            for article in articles:
                self.conn.execute(
                    "INSERT INTO rss_articles "
                    "(session_id, feed_url, title, summary, link, published_at, categories, extracted_at) "
                    "VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                    (
                        session_id,
                        article.get("source_url", ""),
                        article.get("title", ""),
                        article.get("summary", ""),
                        article.get("link", ""),
                        article.get("published_at", ""),
                        article.get("categories", ""),
                        article.get("extracted_at", datetime.now(timezone.utc).isoformat()),
                    ),
                )
                count += 1
        return count

    def log_crawl(self, session_id: int, url: str, domain: str,
                  status_code: int, content_length: int,
                  robots_allowed: bool, signals_found: int) -> None:
        self.conn.execute(
            "INSERT INTO crawl_log "
            "(session_id, url, domain, status_code, content_length, crawled_at, "
            "robots_allowed, signals_found) VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
            (
                session_id, url, domain, status_code, content_length,
                datetime.now(timezone.utc).isoformat(),
                1 if robots_allowed else 0,
                signals_found,
            ),
        )
        self.conn.commit()

    def is_url_crawled(self, session_id: int, url: str) -> bool:
        row = self.conn.execute(
            "SELECT 1 FROM crawl_log WHERE session_id=? AND url=?",
            (session_id, url),
        ).fetchone()
        return row is not None

    # --- Query helpers ---

    def get_signals_by_type(self, signal_type: str, limit: int = 100) -> List[Dict]:
        rows = self.conn.execute(
            "SELECT * FROM market_signals WHERE signal_type=? ORDER BY extracted_at DESC LIMIT ?",
            (signal_type, limit),
        ).fetchall()
        return [dict(row) for row in rows]

    def get_session_summary(self, session_id: int) -> Optional[Dict]:
        row = self.conn.execute(
            "SELECT * FROM crawl_sessions WHERE id=?", (session_id,)
        ).fetchone()
        return dict(row) if row else None

    def get_signal_count_by_type(self) -> Dict[str, int]:
        rows = self.conn.execute(
            "SELECT signal_type, COUNT(*) as cnt FROM market_signals GROUP BY signal_type"
        ).fetchall()
        return {row["signal_type"]: row["cnt"] for row in rows}

    def get_recent_signals(self, limit: int = 50) -> List[Dict]:
        rows = self.conn.execute(
            "SELECT * FROM market_signals ORDER BY extracted_at DESC LIMIT ?",
            (limit,),
        ).fetchall()
        return [dict(row) for row in rows]
