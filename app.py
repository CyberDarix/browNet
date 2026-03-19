#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
browNet - Application de lancement unifiée avec anonymisation active
Fichier : app.py
Description : Lance l'écosystème browNet avec mode incognito permanent,
              suppression radicale des éléments de connexion Google,
              blocage réseau des requêtes vers accounts.google.com,
              MutationObserver permanent et intervalle de sécurité.
Version : Fusion totale (db_manager + search_engine intégrés)
"""

import asyncio
import aiohttp
import aiosqlite
import sqlite3
import json
import re
import hashlib
import time
import random
import logging
import pickle
import numpy as np
from collections import defaultdict, Counter
from datetime import datetime, timedelta
from urllib.parse import urlparse, urljoin, quote, unquote
from typing import List, Dict, Set, Tuple, Optional, Any, Union
from bs4 import BeautifulSoup
from lxml import html as lxml_html
import tldextract
import ssl
import certifi
import socket
import struct
import ipaddress
from asyncio import Semaphore, Queue, Task, PriorityQueue
from concurrent.futures import ThreadPoolExecutor
import aiohttp_socks
from aiohttp_socks import ProxyConnector, ProxyType
from sklearn.feature_extraction.text import TfidfVectorizer
from sklearn.ensemble import RandomForestRegressor
from sklearn.pipeline import make_pipeline
from sklearn.preprocessing import StandardScaler
import joblib
import nltk
from nltk.corpus import stopwords
import language_tool_python  # optionnel
import email.utils
import secrets
import aiofiles
import os
import sys
from cachetools import TTLCache
import re2
from aiohttp import web

import uvicorn
from fastapi import FastAPI
from fastapi.responses import HTMLResponse
import qasync
from PyQt6.QtWidgets import QApplication
from PyQt6.QtCore import QUrl
from PyQt6.QtWebEngineWidgets import QWebEngineView
from PyQt6.QtWebEngineCore import (
    QWebEngineProfile, QWebEnginePage, QWebEngineScript,
    QWebEngineUrlRequestInterceptor, QWebEngineUrlRequestInfo
)

# Configuration du chemin de base (pour PyInstaller)
BASE_PATH = getattr(sys, '_MEIPASS', os.path.dirname(os.path.abspath(__file__)))

# Configuration logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger("browNet.App")

# ==============================================================================
# CONSTANTES (complétées)
# ==============================================================================
DB_BASE_PATH = os.path.join(BASE_PATH, "data")  # les données seront créées dans le dossier de l'exe
SHARD_COUNT = 16
HOST = "127.0.0.1"
PORT = 8000
INDEX_HTML_PATH = os.path.join(BASE_PATH, "index.html")
RESULTS_HTML_PATH = os.path.join(BASE_PATH, "results.html")

# Constantes pour les modules intégrés
USER_AGENT = "Mozilla/5.0 (compatible; browNetBot/4.0; +https://brownet.net/bot)"
REQUEST_TIMEOUT = 10
MAX_CONCURRENT_REQUESTS = 50
CRAWL_DELAY = 0.5
MAX_RETRIES = 3
INDEX_BATCH_SIZE = 100
SECURITY_SCORE_THRESHOLD = 0.7
GOOGLE_SEARCH_API_KEY = None
GOOGLE_SEARCH_ENGINE_ID = None
USE_GOOGLE_API = False
SUGGEST_SERVER_HOST = '127.0.0.1'
SUGGEST_SERVER_PORT = 8080

# Listes noires et règles de sécurité
MALICIOUS_PATTERNS = [
    r'<script[^>]*>\s*eval\(.*\)\s*</script>',
    r'document\.write\(.*decodeURIComponent',
    r'atob\(.*\)',
    r'\.addEventListener\([\'"]mouseover[\'"]',
    r'window\.open\(\)',
    r'\\x[0-9a-fA-F]{2,}',
]
TRACKER_DOMAINS = {
    'google-analytics.com', 'facebook.net', 'facebook.com/tr',
    'doubleclick.net', 'googlesyndication.com', 'amazon-adsystem.com',
    'outbrain.com', 'taboola.com', 'scorecardresearch.com',
    'criteo.com', 'casalemedia.com', 'pubmatic.com', 'rubiconproject.com',
}
AD_KEYWORDS = ['ad', 'banner', 'sponsor', 'promo', 'popup', 'advertisement', 'advert']
TRUSTED_DOMAINS = {'wikipedia.org', 'github.com', 'stackoverflow.com', 'brownet.net'}

# ==============================================================================
# DÉBUT DE L'INTÉGRATION DE db_manager.py (HyperDatabaseManager et dépendances)
# ==============================================================================

# ------------------------------------------------------------------------------
# Classe de sécurité : analyse de dangerosité, sandboxing, injection de scripts
# ------------------------------------------------------------------------------
class SecurityAnalyzer:
    """Analyse les pages web pour détecter les menaces et attribuer un score de sécurité."""
    def __init__(self):
        self.malicious_patterns = [re.compile(p, re.IGNORECASE) for p in MALICIOUS_PATTERNS]
        self.tracker_domains = TRACKER_DOMAINS
        self.ad_keywords = AD_KEYWORDS
        self.trusted = TRUSTED_DOMAINS
        self.cache = TTLCache(maxsize=1000, ttl=3600)

    async def analyze(self, url: str, html: str, headers: Dict = None) -> Dict[str, Any]:
        cache_key = hashlib.md5(f"{url}_{len(html)}".encode()).hexdigest()
        if cache_key in self.cache:
            return self.cache[cache_key]

        result = {
            "url": url,
            "domain": urlparse(url).netloc,
            "score": 1.0,
            "threats": [],
            "trackers": [],
            "ads": [],
            "scripts": [],
            "sandbox_required": False,
            "injection_script": None,
        }

        domain = result["domain"]
        if any(domain.endswith(t) for t in self.trusted):
            result["score"] = 1.0
            result["threats"].append("trusted_domain")
            self.cache[cache_key] = result
            return result

        soup = BeautifulSoup(html, 'lxml')
        scripts = soup.find_all('script')
        iframes = soup.find_all('iframe')
        links = soup.find_all('a', href=True)
        imgs = soup.find_all('img', src=True)

        for script in scripts:
            script_content = script.string
            if script_content:
                for pattern in self.malicious_patterns:
                    if pattern.search(script_content):
                        result["threats"].append("malicious_script")
                        result["score"] *= 0.3
                        result["scripts"].append(str(script)[:100])
                        break

        all_src = [tag.get('src') for tag in scripts + iframes + imgs if tag.get('src')]
        all_href = [tag.get('href') for tag in links if tag.get('href')]
        all_urls = all_src + all_href

        for u in all_urls:
            if not u:
                continue
            parsed = urlparse(u)
            netloc = parsed.netloc
            if any(tracker in netloc for tracker in self.tracker_domains):
                result["trackers"].append(netloc)
                result["score"] *= 0.8
            if any(keyword in u.lower() for keyword in self.ad_keywords):
                result["ads"].append(u)
                result["score"] *= 0.9

        for script in scripts:
            src = script.get('src')
            if src and src.startswith('http:'):
                result["threats"].append("insecure_script")
                result["score"] *= 0.95

        if headers and 'strict-transport-security' in headers:
            result["score"] = min(1.0, result["score"] * 1.05)

        meta_refresh = soup.find('meta', attrs={'http-equiv': 'refresh'})
        if meta_refresh:
            result["threats"].append("meta_refresh")
            result["score"] *= 0.9

        if result["score"] < SECURITY_SCORE_THRESHOLD:
            result["sandbox_required"] = True
            result["injection_script"] = self._generate_sandbox_script()

        self.cache[cache_key] = result
        return result

    def _generate_sandbox_script(self) -> str:
        return """
        <script>
        (function() {
            const originalAddEventListener = window.addEventListener;
            window.addEventListener = function(type, listener, options) {
                if (type === 'mouseover' || type === 'mousemove') {
                    console.warn('[browNet Sandbox] Événement de tracking bloqué:', type);
                    return;
                }
                return originalAddEventListener.call(this, type, listener, options);
            };
            Object.defineProperty(window, 'localStorage', {
                get: function() { throw new Error('localStorage bloqué par browNet Sandbox'); }
            });
            Object.defineProperty(window, 'sessionStorage', {
                get: function() { throw new Error('sessionStorage bloqué par browNet Sandbox'); }
            });
            document.__defineGetter__('cookie', function() { return ''; });
            document.__defineSetter__('cookie', function() {});
            if (navigator.geolocation) {
                navigator.geolocation.getCurrentPosition = function(success, error) {
                    error({ code: 1, message: 'Géolocalisation désactivée par browNet' });
                };
            }
            if (navigator.clipboard) {
                navigator.clipboard.readText = function() { return Promise.reject('Bloqué'); };
                navigator.clipboard.writeText = function() { return Promise.reject('Bloqué'); };
            }
            if (window.RTCPeerConnection) {
                window.RTCPeerConnection = function() {
                    console.warn('WebRTC bloqué par browNet');
                };
            }
            console.log('[browNet Sandbox] Activé sur cette page pour votre sécurité');
        })();
        </script>
        """

# ------------------------------------------------------------------------------
# Classe de vision : extraction des médias (images, vidéos) depuis le DOM
# ------------------------------------------------------------------------------
class Vision:
    """Yeux du bot : analyse le DOM et extrait les métadonnées des médias."""
    @staticmethod
    def extract_media(soup: BeautifulSoup, base_url: str) -> Dict[str, List[Dict]]:
        """Extrait les URLs des images et vidéos avec leurs métadonnées."""
        images = []
        for img in soup.find_all('img', src=True):
            img_url = urljoin(base_url, img['src'])
            images.append({
                'url': img_url,
                'alt': img.get('alt', ''),
                'width': img.get('width'),
                'height': img.get('height'),
                'type': 'image'
            })
        videos = []
        for video in soup.find_all(['video', 'source']):
            src = video.get('src')
            if src:
                video_url = urljoin(base_url, src)
                videos.append({
                    'url': video_url,
                    'type': 'video',
                    'poster': video.get('poster') if video.name == 'video' else None
                })
        for iframe in soup.find_all('iframe', src=True):
            src = iframe['src']
            if 'youtube' in src or 'vimeo' in src or 'dailymotion' in src:
                videos.append({
                    'url': src,
                    'type': 'video',
                    'embed': True
                })
        return {'images': images, 'videos': videos}

# ------------------------------------------------------------------------------
# Classe de filtrage actif (mains) : injection de sécurité et suppression trackers
# ------------------------------------------------------------------------------
class ActiveFilter:
    """Mains du bot : modifie le HTML en temps réel pour la sécurité."""
    def __init__(self, security: SecurityAnalyzer):
        self.security = security

    async def filter(self, url: str, html: str, security_result: Dict) -> str:
        """Applique les filtres : suppression trackers, injection sandbox."""
        soup = BeautifulSoup(html, 'lxml')

        for tag in soup.find_all(['script', 'iframe', 'img', 'link']):
            src = tag.get('src') or tag.get('href')
            if src:
                parsed = urlparse(src)
                if any(tracker in parsed.netloc for tracker in TRACKER_DOMAINS):
                    tag.decompose()
                    continue
            if tag.get('class'):
                if any(ad_keyword in ' '.join(tag.get('class')).lower() for ad_keyword in AD_KEYWORDS):
                    tag.decompose()

        if security_result.get('sandbox_required'):
            sandbox_script = self.security._generate_sandbox_script()
            head = soup.find('head')
            if head:
                head.append(BeautifulSoup(sandbox_script, 'html.parser'))
            else:
                new_head = soup.new_tag('head')
                new_head.append(BeautifulSoup(sandbox_script, 'html.parser'))
                if soup.html:
                    soup.html.insert(0, new_head)

        return str(soup)

# ------------------------------------------------------------------------------
# Classe de cerveau : scoring IA pour la pertinence (modèle ML)
# ------------------------------------------------------------------------------
class Brain:
    """Cerveau du bot : évalue la pertinence d'une page par rapport à une requête."""
    def __init__(self):
        self.model = None
        self.vectorizer = TfidfVectorizer(max_features=10000, stop_words='english')
        self._load_or_train_model()

    def _load_or_train_model(self):
        model_path = os.path.join(BASE_PATH, 'ranking_model.pkl')
        if os.path.exists(model_path):
            self.model = joblib.load(model_path)
        else:
            self.model = RandomForestRegressor(n_estimators=100, random_state=42)
            logger.warning("Modèle de ranking non trouvé, utilisation du fallback")

    def extract_features(self, query: str, page_data: Dict) -> np.ndarray:
        # Pour l'instant, on renvoie un vecteur vide (à implémenter)
        return np.array([])

    def predict_score(self, features: np.ndarray) -> float:
        if self.model and features.size > 0:
            return self.model.predict([features])[0]
        return 0.5

# ------------------------------------------------------------------------------
# Classe représentant un bot individuel de l'essaim
# ------------------------------------------------------------------------------
class SwarmBot:
    """
    Un bot intelligent avec :
    - Yeux (Vision) pour analyser le DOM et les médias
    - Mains (ActiveFilter) pour filtrer et sécuriser
    - Cerveau (Brain) pour scorer la pertinence
    """
    def __init__(self, bot_id: int, db_path: str, queue: PriorityQueue, stats: Dict):
        self.bot_id = bot_id
        self.db_path = db_path
        self.queue = queue
        self.stats = stats
        self.security = SecurityAnalyzer()
        self.vision = Vision()
        self.filter = ActiveFilter(self.security)
        self.brain = Brain()
        self.session = None
        self.running = False
        self.task = None
        self.seen_urls = set()
        self.domain_delays = defaultdict(float)

    async def start(self):
        self.running = True
        self.session = aiohttp.ClientSession(
            headers={"User-Agent": USER_AGENT},
            timeout=aiohttp.ClientTimeout(total=REQUEST_TIMEOUT)
        )
        self.task = asyncio.create_task(self._run())
        logger.debug(f"Bot {self.bot_id} démarré")

    async def stop(self):
        self.running = False
        if self.task:
            self.task.cancel()
        if self.session:
            await self.session.close()
        logger.debug(f"Bot {self.bot_id} arrêté")

    async def _run(self):
        while self.running:
            try:
                priority, url = await self.queue.get()
                await self._process_url(url, priority)
                self.queue.task_done()
            except asyncio.CancelledError:
                break
            except Exception as e:
                logger.error(f"Bot {self.bot_id} - erreur: {e}")

    async def _process_url(self, url: str, priority: int):
        domain = urlparse(url).netloc
        last = self.domain_delays.get(domain, 0)
        now = time.time()
        if now - last < CRAWL_DELAY:
            await asyncio.sleep(CRAWL_DELAY - (now - last))

        try:
            async with self.session.get(url, ssl=False) as resp:
                if resp.status != 200:
                    return
                html = await resp.text()
                headers = resp.headers

                security_result = await self.security.analyze(url, html, headers)
                filtered_html = await self.filter.filter(url, html, security_result)
                soup = BeautifulSoup(filtered_html, 'lxml')
                media = self.vision.extract_media(soup, url)
                title = soup.title.string if soup.title else url
                text = self._extract_text(soup)

                async with aiosqlite.connect(self.db_path) as db:
                    await db.execute('''
                        INSERT OR REPLACE INTO crawled_pages
                        (url, title, content, html_hash, http_status, content_type,
                         word_count, security_score, is_dangerous, media_json)
                        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    ''', (url, title, text,
                          hashlib.sha256(html.encode()).hexdigest(),
                          resp.status, headers.get('content-type', ''),
                          len(text.split()), security_result['score'],
                          security_result['score'] < SECURITY_SCORE_THRESHOLD,
                          json.dumps(media)))
                    keywords = self._extract_keywords(title, text)
                    await db.execute('''
                        INSERT OR REPLACE INTO page_keywords (url, title, keywords, content)
                        VALUES (?, ?, ?, ?)
                    ''', (url, title, ' '.join(keywords), text))
                    await db.commit()

                if not security_result.get('sandbox_required'):
                    await self._extract_and_queue_links(url, soup)

                self.stats['pages_crawled'] = self.stats.get('pages_crawled', 0) + 1
                self.stats['domains'].add(domain)

        except Exception as e:
            logger.warning(f"Bot {self.bot_id} - échec {url}: {e}")
        finally:
            self.domain_delays[domain] = time.time()

    def _extract_text(self, soup):
        for script in soup(['script', 'style', 'nav', 'footer']):
            script.decompose()
        return soup.get_text(separator=' ', strip=True)

    def _extract_keywords(self, title, text, max_keywords=50):
        words = re.findall(r'\w{3,}', text.lower())
        stop_words = set(stopwords.words('french') + stopwords.words('english'))
        words = [w for w in words if w not in stop_words and len(w) > 2]
        counter = Counter(words)
        return [w for w, _ in counter.most_common(max_keywords)]

    async def _extract_and_queue_links(self, from_url: str, soup):
        links = set()
        for a in soup.find_all('a', href=True):
            href = a['href']
            absolute = urljoin(from_url, href)
            parsed = urlparse(absolute)
            if parsed.scheme in ('http', 'https') and parsed.netloc:
                links.add(absolute)

        async with aiosqlite.connect(self.db_path) as db:
            for to_url in links:
                try:
                    await db.execute('INSERT OR IGNORE INTO links (from_url, to_url) VALUES (?, ?)',
                                     (from_url, to_url))
                except:
                    pass
            await db.commit()

        for link in links:
            if link not in self.seen_urls:
                self.seen_urls.add(link)
                await self.queue.put((0, link))

# ------------------------------------------------------------------------------
# Gestionnaire d'essaim de bots (Swarm)
# ------------------------------------------------------------------------------
class BotSwarm:
    def __init__(self, db_path: str, num_bots: int = 50):
        self.db_path = db_path
        self.num_bots = num_bots
        self.queue = PriorityQueue()
        self.bots: List[SwarmBot] = []
        self.stats = {
            'pages_crawled': 0,
            'domains': set(),
            'start_time': None
        }
        self._init_db()

    def _init_db(self):
        asyncio.create_task(self._async_init_db())

    async def _async_init_db(self):
        async with aiosqlite.connect(self.db_path) as db:
            try:
                await db.execute('ALTER TABLE crawled_pages ADD COLUMN media_json TEXT')
            except:
                pass
            await db.commit()

    async def start(self):
        self.stats['start_time'] = datetime.now()
        for i in range(self.num_bots):
            bot = SwarmBot(i, self.db_path, self.queue, self.stats)
            self.bots.append(bot)
            await bot.start()
        logger.info(f"Essaim de {self.num_bots} bots démarré")

    async def stop(self):
        await asyncio.gather(*(bot.stop() for bot in self.bots))
        logger.info("Essaim arrêté")

    async def submit_url(self, url: str, priority: int = 1):
        await self.queue.put((priority, url))

    def get_stats(self):
        return {
            'pages_crawled': self.stats['pages_crawled'],
            'domains_count': len(self.stats['domains']),
            'uptime': (datetime.now() - self.stats['start_time']).total_seconds() if self.stats['start_time'] else 0,
            'queue_size': self.queue.qsize()
        }

# ------------------------------------------------------------------------------
# Classe de classement intelligent améliorée avec modèle ML
# ------------------------------------------------------------------------------
class RankingEngine:
    def __init__(self, db_path: str):
        self.db_path = db_path
        self.page_rank = {}
        self.tfidf_vectorizer = TfidfVectorizer(max_features=10000, stop_words='english')
        self.model = None
        self._load_model()
        self._load_page_rank()

    def _load_model(self):
        model_path = os.path.join(BASE_PATH, 'ranking_model.pkl')
        if os.path.exists(model_path):
            self.model = joblib.load(model_path)
        else:
            self.model = None

    def _load_page_rank(self):
        try:
            conn = sqlite3.connect(self.db_path)
            c = conn.cursor()
            c.execute('SELECT to_url, COUNT(*) FROM links GROUP BY to_url')
            rows = c.fetchall()
            total = sum(count for _, count in rows) or 1
            for to_url, count in rows:
                self.page_rank[to_url] = count / total
            conn.close()
        except:
            pass

    def _extract_features(self, query: str, result: Dict) -> np.ndarray:
        # À enrichir
        return np.array([0.0])

    async def rank(self, query: str, results: List[Dict]) -> List[Dict]:
        if not results:
            return results
        if self.model is None:
            return await self._fallback_rank(query, results)
        X = []
        for r in results:
            feats = self._extract_features(query, r)
            X.append(feats)
        scores = self.model.predict(X)
        for i, r in enumerate(results):
            r['_score'] = scores[i]
        results.sort(key=lambda x: x['_score'], reverse=True)
        return results

    async def _fallback_rank(self, query: str, results: List[Dict]) -> List[Dict]:
        corpus = [r.get('content', '') for r in results]
        if not any(corpus):
            corpus = [r.get('title', '') for r in results]
        try:
            tfidf_matrix = self.tfidf_vectorizer.fit_transform(corpus + [query])
            query_vector = tfidf_matrix[-1]
            doc_vectors = tfidf_matrix[:-1]
            similarities = cosine_similarity(doc_vectors, query_vector).flatten()
        except:
            query_words = set(query.lower().split())
            similarities = []
            for r in results:
                text = (r.get('title', '') + ' ' + r.get('content', '')).lower()
                score = sum(1 for w in query_words if w in text)
                similarities.append(score / max(1, len(query_words)))

        final_scores = []
        for i, r in enumerate(results):
            sim = similarities[i]
            pr = self.page_rank.get(r['url'], 0.0)
            freshness = 1.0
            if 'crawled_at' in r:
                days_old = (datetime.now() - datetime.fromisoformat(r['crawled_at'])).days
                freshness = max(0.5, 1.0 - days_old / 365.0)
            security = r.get('security_score', 1.0)
            composite = (0.5 * sim + 0.3 * pr + 0.1 * freshness + 0.1 * security)
            final_scores.append(composite)

        for i, r in enumerate(results):
            r['_score'] = final_scores[i]
        results.sort(key=lambda x: x['_score'], reverse=True)
        return results

# ------------------------------------------------------------------------------
# Classe de découverte via sitemaps
# ------------------------------------------------------------------------------
class SitemapFetcher:
    def __init__(self, swarm: BotSwarm):
        self.swarm = swarm
        self.seen_sitemaps = set()

    async def fetch_sitemap(self, base_url: str):
        parsed = urlparse(base_url)
        domain = f"{parsed.scheme}://{parsed.netloc}"
        sitemap_url = urljoin(domain, "/sitemap.xml")
        if sitemap_url in self.seen_sitemaps:
            return
        self.seen_sitemaps.add(sitemap_url)

        try:
            async with aiohttp.ClientSession() as session:
                async with session.get(sitemap_url, timeout=10) as resp:
                    if resp.status != 200:
                        sitemap_url = urljoin(domain, "/sitemap_index.xml")
                        async with session.get(sitemap_url, timeout=10) as resp2:
                            if resp2.status != 200:
                                return
                            content = await resp2.text()
                    else:
                        content = await resp.text()
            soup = BeautifulSoup(content, 'xml')
            locs = soup.find_all('loc')
            for loc in locs:
                url = loc.text.strip()
                if url.startswith('http'):
                    await self.swarm.submit_url(url, priority=0)
        except Exception as e:
            logger.debug(f"Sitemap non trouvé pour {domain}: {e}")

# ------------------------------------------------------------------------------
# Serveur de suggestions (API HTTP)
# ------------------------------------------------------------------------------
class SuggestionServer:
    def __init__(self, engine: 'SearchEngine', host=SUGGEST_SERVER_HOST, port=SUGGEST_SERVER_PORT):
        self.engine = engine
        self.host = host
        self.port = port
        self.app = web.Application()
        self.app.router.add_get('/suggest', self.handle_suggest)
        self.runner = None

    async def start(self):
        self.runner = web.AppRunner(self.app)
        await self.runner.setup()
        site = web.TCPSite(self.runner, self.host, self.port)
        await site.start()
        logger.info(f"Serveur de suggestions démarré sur http://{self.host}:{self.port}/suggest")

    async def stop(self):
        if self.runner:
            await self.runner.cleanup()

    async def handle_suggest(self, request):
        query = request.query.get('q', '')
        if len(query) < 2:
            return web.json_response([])
        async with aiosqlite.connect(self.engine.db_path) as db:
            cursor = await db.execute('''
                SELECT title, url FROM search_index
                WHERE search_index MATCH ? || '*'
                ORDER BY rank
                LIMIT 5
            ''', (query,))
            rows = await cursor.fetchall()
            suggestions = [{'title': r[0], 'url': r[1]} for r in rows]
        return web.json_response(suggestions)

# ------------------------------------------------------------------------------
# Classe principale de gestion de base de données hyper-scalable
# ------------------------------------------------------------------------------
class HyperDatabaseManager:
    """
    Point d'entrée unique pour toutes les opérations base de données.
    Intègre sharding, cache, compression, bots de maintenance, indexeur intelligent.
    """
    def __init__(self, base_path: str = "data", shard_count: int = SHARD_COUNT):
        self.base_path = base_path
        self.shard_manager = ShardManager(base_path, shard_count)
        self.cache = LRUCache(CACHE_SIZE)  # à définir plus haut? On va définir CACHE_SIZE ici.
        self.compression = CompressionEngine()
        self.index_optimizer = IndexOptimizer(self.shard_manager)
        self.maintenance_bots: List[MaintenanceBot] = []
        self._stopped = False
        self.stats_collector_task = None

    async def initialize(self):
        """Initialise tout le système."""
        await self.shard_manager.initialize()
        # Lancer les bots de maintenance (100 bots)
        for i in range(MAX_WORKERS):
            bot = MaintenanceBot(i, self.shard_manager)
            await bot.start()
            self.maintenance_bots.append(bot)
        # Lancer le collecteur de stats
        self.stats_collector_task = asyncio.create_task(self._collect_stats_loop())
        logger.info("HyperDatabaseManager initialisé avec {} bots.".format(MAX_WORKERS))

    async def close(self):
        """Arrêt propre de tout le système."""
        self._stopped = True
        for bot in self.maintenance_bots:
            await bot.stop()
        if self.stats_collector_task:
            self.stats_collector_task.cancel()
        await self.shard_manager.close()
        logger.info("HyperDatabaseManager fermé.")

    async def _collect_stats_loop(self):
        """Collecte périodique des statistiques globales."""
        while not self._stopped:
            stats = await self.get_stats()
            logger.info(f"STATS: {stats}")
            await asyncio.sleep(60)

    async def store_page(self, url: str, title: str, html: str, security_score: float, is_dangerous: bool, media_json: str = None):
        """
        Stocke une page crawlée avec compression du contenu.
        """
        # Compression du contenu HTML
        compressed_content = self.compression.compress(html)
        shard = self.shard_manager._get_shard_for_url(url)
        async with shard.pool.get_connection() as conn:
            try:
                await conn.execute("ALTER TABLE crawled_pages ADD COLUMN content_compressed BLOB")
            except:
                pass
            await conn.commit()

        data = {
            'url': url,
            'title': title,
            'content_compressed': compressed_content,
            'security_score': security_score,
            'is_dangerous': is_dangerous,
            'media_json': media_json,
            'domain': urlparse(url).netloc
        }
        await self.shard_manager.batch_insert('crawled_pages', [data], conflict="ON CONFLICT(url_hash) DO UPDATE SET title=excluded.title, content_compressed=excluded.content_compressed, security_score=excluded.security_score, crawled_at=CURRENT_TIMESTAMP")

    async def search(self, query: str, limit: int = 10) -> List[Dict]:
        """
        Effectue une recherche full-text sur tous les shards.
        """
        # Vérifier le cache
        cache_key = f"search:{query}:{limit}"
        cached = await self.cache.get(cache_key)
        if cached:
            return cached

        # Lancer des requêtes parallèles sur tous les shards
        tasks = []
        for shard in self.shard_manager.shards:
            tasks.append(self._search_shard(shard, query, limit))
        results_per_shard = await asyncio.gather(*tasks)

        # Fusionner et trier
        all_results = []
        for res in results_per_shard:
            all_results.extend(res)
        all_results.sort(key=lambda x: x.get('rank', 0), reverse=True)

        await self.cache.set(cache_key, all_results[:limit])
        return all_results[:limit]

    async def _search_shard(self, shard: 'Shard', query: str, limit: int) -> List[Dict]:
        try:
            async with shard.pool.get_connection() as conn:
                cursor = await conn.execute('''
                    SELECT url, title, snippet(page_keywords, 1, '<b>', '</b>', '...', 16) as excerpt
                    FROM page_keywords
                    WHERE page_keywords MATCH ?
                    ORDER BY rank
                    LIMIT ?
                ''', (query, limit))
                rows = await cursor.fetchall()
                return [{'url': r[0], 'title': r[1], 'excerpt': r[2]} for r in rows]
        except Exception as e:
            logger.error(f"Erreur recherche shard {shard.shard_id}: {e}")
            return []

    async def get_stats(self) -> Dict:
        shard_stats = await self.shard_manager.get_stats()
        cache_stats = self.cache.get_stats()
        return {
            'shards': shard_stats,
            'cache': cache_stats,
            'bots': [bot.stats for bot in self.maintenance_bots]
        }

# ==============================================================================
# FIN DE L'INTÉGRATION DE db_manager.py
# ==============================================================================

# ==============================================================================
# DÉBUT DE L'INTÉGRATION DE search_engine.py (SearchEngine et dépendances)
# ==============================================================================

# Note: Certaines classes comme SecurityAnalyzer, Vision, ActiveFilter, Brain,
# SwarmBot, BotSwarm, RankingEngine, SitemapFetcher, SuggestionServer sont déjà
# définies ci-dessus. Nous ne les redéfinissons pas. Nous allons maintenant
# définir la classe SearchEngine et ses dépendances manquantes (comme ShardManager,
# LRUCache, CompressionEngine, IndexOptimizer, MaintenanceBot, Shard, ConnectionPool).
# Mais ces classes sont déjà dans le code précédent ? En réalité, le db_manager.py
# complet incluait aussi des classes comme ShardManager, Shard, ConnectionPool, etc.
# Nous les avons déjà incluses ? Non, nous avons inclus seulement jusqu'à HyperDatabaseManager.
# Il manque les définitions de ShardManager, Shard, ConnectionPool, LRUCache, CompressionEngine,
# IndexOptimizer, MaintenanceBot. Pour que le code soit complet, nous devons aussi les ajouter.
# Je vais donc ajouter les classes manquantes issues de db_manager.py.

# ------------------------------------------------------------------------------
# Classes manquantes de db_manager.py
# ------------------------------------------------------------------------------

CACHE_SIZE = 10000
COMPRESSION_LEVEL = 6
ENABLE_SHARD_REBALANCE = True
HEALTH_CHECK_INTERVAL = 60
OPTIMIZE_INTERVAL = 3600
MAX_WORKERS = 100  # pour les bots de maintenance
CONNECTIONS_PER_SHARD = 10

class Shard:
    def __init__(self, shard_id: int, base_path: str):
        self.shard_id = shard_id
        self.db_path = os.path.join(base_path, f"browNet_shard_{shard_id}.db")
        self.pool = None
        self.size = 0
        self.last_optimized = datetime.now()
        self.is_healthy = True
        self.read_latency = 0.0
        self.write_latency = 0.0

    async def initialize(self):
        os.makedirs(os.path.dirname(self.db_path), exist_ok=True)
        async with aiosqlite.connect(self.db_path) as conn:
            await conn.execute("PRAGMA journal_mode=WAL")
            await conn.execute("PRAGMA synchronous=NORMAL")
            await conn.execute("PRAGMA cache_size=-200000")
            await conn.execute("PRAGMA mmap_size=30000000000")
            await conn.execute("PRAGMA page_size=8192")
            await conn.execute("PRAGMA temp_store=MEMORY")
            await self._create_tables(conn)
            await conn.commit()
        self.pool = ConnectionPool(self.db_path, CONNECTIONS_PER_SHARD)
        await self.pool.initialize()
        logger.info(f"Shard {self.shard_id} initialisé : {self.db_path}")

    async def _create_tables(self, conn):
        await conn.execute('''
            CREATE TABLE IF NOT EXISTS crawled_pages (
                url_hash TEXT PRIMARY KEY,
                url TEXT NOT NULL,
                title TEXT,
                content TEXT,
                html_hash TEXT,
                crawled_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                http_status INTEGER,
                content_type TEXT,
                word_count INTEGER,
                security_score REAL,
                is_dangerous BOOLEAN,
                media_json TEXT,
                domain TEXT,
                popularity INTEGER DEFAULT 0
            )
        ''')
        await conn.execute('CREATE INDEX IF NOT EXISTS idx_domain ON crawled_pages(domain)')
        await conn.execute('CREATE INDEX IF NOT EXISTS idx_popularity ON crawled_pages(popularity DESC)')
        await conn.execute('CREATE INDEX IF NOT EXISTS idx_crawled_at ON crawled_pages(crawled_at DESC)')
        await conn.execute('''
            CREATE TABLE IF NOT EXISTS links (
                from_hash TEXT,
                to_hash TEXT,
                PRIMARY KEY (from_hash, to_hash)
            )
        ''')
        await conn.execute('CREATE INDEX IF NOT EXISTS idx_links_to ON links(to_hash)')
        await conn.execute('''
            CREATE VIRTUAL TABLE IF NOT EXISTS page_keywords USING fts5(
                url_hash, title, keywords, content, tokenize='porter'
            )
        ''')
        await conn.execute('''
            CREATE TABLE IF NOT EXISTS search_cache (
                query_hash TEXT PRIMARY KEY,
                query TEXT,
                results TEXT,
                cached_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                hit_count INTEGER DEFAULT 0
            )
        ''')
        await conn.execute('''
            CREATE TABLE IF NOT EXISTS shard_stats (
                key TEXT PRIMARY KEY,
                value TEXT,
                updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        ''')

    async def get_stats(self) -> Dict:
        async with self.pool.get_connection() as conn:
            cursor = await conn.execute("SELECT COUNT(*) FROM crawled_pages")
            count = (await cursor.fetchone())[0]
            cursor = await conn.execute("SELECT COUNT(*) FROM links")
            links = (await cursor.fetchone())[0]
            cursor = await conn.execute("SELECT SUM(LENGTH(content)) FROM crawled_pages")
            total_size = (await cursor.fetchone())[0] or 0
        return {
            'id': self.shard_id,
            'pages': count,
            'links': links,
            'size_mb': total_size / (1024*1024),
            'healthy': self.is_healthy,
            'read_latency': self.read_latency,
            'write_latency': self.write_latency
        }

    async def optimize(self):
        logger.info(f"Optimisation du shard {self.shard_id}...")
        async with aiosqlite.connect(self.db_path) as conn:
            await conn.execute("VACUUM")
            await conn.execute("ANALYZE")
            await conn.execute("REINDEX")
            await conn.commit()
        self.last_optimized = datetime.now()
        logger.info(f"Shard {self.shard_id} optimisé.")

class ConnectionPool:
    def __init__(self, db_path: str, size: int):
        self.db_path = db_path
        self.size = size
        self._pool = deque()
        self._lock = asyncio.Lock()
        self._initialized = False

    async def initialize(self):
        async with self._lock:
            if self._initialized:
                return
            for _ in range(self.size):
                conn = await aiosqlite.connect(self.db_path)
                await conn.execute("PRAGMA journal_mode=WAL")
                await conn.execute("PRAGMA synchronous=NORMAL")
                await conn.execute("PRAGMA cache_size=-200000")
                await conn.execute("PRAGMA mmap_size=30000000000")
                self._pool.append(conn)
            self._initialized = True
            logger.debug(f"Pool de {self.size} connexions créé pour {self.db_path}")

    async def close(self):
        async with self._lock:
            while self._pool:
                conn = self._pool.popleft()
                await conn.close()

    @asynccontextmanager
    async def get_connection(self):
        async with self._lock:
            if not self._pool:
                conn = await aiosqlite.connect(self.db_path)
                try:
                    yield conn
                finally:
                    await conn.close()
            else:
                conn = self._pool.popleft()
                try:
                    yield conn
                finally:
                    async with self._lock:
                        self._pool.append(conn)

class ShardManager:
    def __init__(self, base_path: str = "data", shard_count: int = SHARD_COUNT):
        self.base_path = base_path
        self.shard_count = shard_count
        self.shards: List[Shard] = []
        self.lock = asyncio.Lock()
        self.stats = {
            'total_pages': 0,
            'total_links': 0,
            'total_size_mb': 0,
            'reads': 0,
            'writes': 0,
            'cache_hits': 0,
            'cache_misses': 0
        }
        self.health_check_task = None
        self.optimize_task = None
        self.rebalance_task = None
        self._stopped = False

    async def initialize(self):
        os.makedirs(self.base_path, exist_ok=True)
        for i in range(self.shard_count):
            shard = Shard(i, self.base_path)
            await shard.initialize()
            self.shards.append(shard)
        self.health_check_task = asyncio.create_task(self._health_check_loop())
        self.optimize_task = asyncio.create_task(self._optimize_loop())
        if ENABLE_SHARD_REBALANCE:
            self.rebalance_task = asyncio.create_task(self._rebalance_loop())
        logger.info(f"ShardManager initialisé avec {self.shard_count} shards.")

    async def close(self):
        self._stopped = True
        if self.health_check_task:
            self.health_check_task.cancel()
        if self.optimize_task:
            self.optimize_task.cancel()
        if self.rebalance_task:
            self.rebalance_task.cancel()
        for shard in self.shards:
            if shard.pool:
                await shard.pool.close()
        logger.info("ShardManager fermé.")

    def _get_shard_for_url(self, url: str) -> Shard:
        hash_hex = hashlib.sha256(url.encode('utf-8')).hexdigest()
        shard_id = int(hash_hex, 16) % self.shard_count
        return self.shards[shard_id]

    def _get_shard_for_hash(self, url_hash: str) -> Shard:
        shard_id = int(url_hash[:8], 16) % self.shard_count
        return self.shards[shard_id]

    async def execute_read(self, query: str, params: tuple = (), shard_hint: Optional[Shard] = None) -> List[tuple]:
        start = time.time()
        shard = shard_hint or self.shards[0]
        async with shard.pool.get_connection() as conn:
            cursor = await conn.execute(query, params)
            rows = await cursor.fetchall()
        latency = time.time() - start
        shard.read_latency = latency * 0.9 + shard.read_latency * 0.1
        self.stats['reads'] += 1
        return rows

    async def execute_write(self, query: str, params: tuple = (), shard_hint: Optional[Shard] = None):
        start = time.time()
        shard = shard_hint or self.shards[0]
        async with shard.pool.get_connection() as conn:
            await conn.execute(query, params)
            await conn.commit()
        latency = time.time() - start
        shard.write_latency = latency * 0.9 + shard.write_latency * 0.1
        self.stats['writes'] += 1

    async def batch_insert(self, table: str, data: List[Dict], conflict: str = ""):
        grouped = {}
        for item in data:
            url = item.get('url')
            if not url:
                continue
            shard = self._get_shard_for_url(url)
            url_hash = hashlib.sha256(url.encode()).hexdigest()
            item['url_hash'] = url_hash
            grouped.setdefault(shard, []).append(item)
        for shard, items in grouped.items():
            if not items:
                continue
            columns = list(items[0].keys())
            placeholders = ','.join(['?' for _ in columns])
            insert_sql = f"INSERT INTO {table} ({','.join(columns)}) VALUES ({placeholders}) {conflict}"
            queries = [(insert_sql, tuple(item[col] for col in columns)) for item in items]
            async with shard.pool.get_connection() as conn:
                async with conn.cursor() as cursor:
                    for sql, params in queries:
                        await cursor.execute(sql, params)
                    await conn.commit()

    async def get_stats(self) -> Dict:
        total_pages = 0
        total_links = 0
        total_size = 0
        for shard in self.shards:
            stats = await shard.get_stats()
            total_pages += stats['pages']
            total_links += stats['links']
            total_size += stats['size_mb']
        self.stats['total_pages'] = total_pages
        self.stats['total_links'] = total_links
        self.stats['total_size_mb'] = total_size
        return self.stats.copy()

    async def _health_check_loop(self):
        while not self._stopped:
            await asyncio.sleep(HEALTH_CHECK_INTERVAL)
            logger.info("Vérification de santé des shards...")
            for shard in self.shards:
                try:
                    async with shard.pool.get_connection() as conn:
                        await conn.execute("SELECT 1")
                    shard.is_healthy = True
                except Exception as e:
                    logger.error(f"Shard {shard.shard_id} défaillant : {e}")
                    shard.is_healthy = False
                    if shard.pool:
                        await shard.pool.close()
                    await shard.initialize()

    async def _optimize_loop(self):
        while not self._stopped:
            await asyncio.sleep(OPTIMIZE_INTERVAL)
            for shard in self.shards:
                await shard.optimize()

    async def _rebalance_loop(self):
        while not self._stopped:
            await asyncio.sleep(OPTIMIZE_INTERVAL * 2)
            stats = await self.get_stats()
            avg_pages = stats['total_pages'] / self.shard_count
            for shard in self.shards:
                s = await shard.get_stats()
                if s['pages'] > avg_pages * 1.5 or s['pages'] < avg_pages * 0.5:
                    logger.warning(f"Shard {shard.shard_id} déséquilibré : {s['pages']} pages (moyenne {avg_pages:.0f})")

class LRUCache:
    def __init__(self, capacity: int):
        self.cache = OrderedDict()
        self.capacity = capacity

    def get(self, key: str):
        if key not in self.cache:
            return None
        self.cache.move_to_end(key)
        return self.cache[key]

    def put(self, key: str, value: Any):
        if key in self.cache:
            self.cache.move_to_end(key)
        self.cache[key] = value
        if len(self.cache) > self.capacity:
            self.cache.popitem(last=False)

class CacheLayer:
    def __init__(self, capacity: int = CACHE_SIZE):
        self.l1 = LRUCache(capacity)
        self.hits = 0
        self.misses = 0

    async def get(self, key: str) -> Optional[Any]:
        val = self.l1.get(key)
        if val is not None:
            self.hits += 1
            return val
        self.misses += 1
        return None

    async def set(self, key: str, value: Any):
        self.l1.put(key, value)

    def get_stats(self):
        return {'hits': self.hits, 'misses': self.misses}

class CompressionEngine:
    @staticmethod
    def compress(data: str) -> bytes:
        return zlib.compress(data.encode('utf-8'), level=COMPRESSION_LEVEL)

    @staticmethod
    def decompress(data: bytes) -> str:
        return zlib.decompress(data).decode('utf-8')

class IndexOptimizer:
    def __init__(self, shard_manager: ShardManager):
        self.manager = shard_manager
        self.query_log = deque(maxlen=1000)
        self.lock = asyncio.Lock()

    async def log_query(self, query: str, params: tuple):
        async with self.lock:
            self.query_log.append((query, params, time.time()))

    async def analyze_and_optimize(self):
        for shard in self.manager.shards:
            async with shard.pool.get_connection() as conn:
                await conn.execute("ANALYZE")
                await conn.commit()
        logger.info("Analyse des index effectuée.")

class MaintenanceBot:
    def __init__(self, bot_id: int, shard_manager: ShardManager):
        self.bot_id = bot_id
        self.manager = shard_manager
        self.running = False
        self.task = None
        self.stats = {'actions': 0}

    async def start(self):
        self.running = True
        self.task = asyncio.create_task(self._run())
        logger.debug(f"MaintenanceBot {self.bot_id} démarré.")

    async def stop(self):
        self.running = False
        if self.task:
            self.task.cancel()

    async def _run(self):
        while self.running:
            stats = await self.manager.get_stats()
            for shard in self.manager.shards:
                s = await shard.get_stats()
                if s['read_latency'] > 0.1:
                    logger.info(f"Bot {self.bot_id} : shard {shard.shard_id} lent, optimisation recommandée.")
                    async with shard.pool.get_connection() as conn:
                        await conn.execute("ANALYZE")
                        await conn.commit()
                    self.stats['actions'] += 1
                statvfs = os.statvfs(shard.db_path)
                free_gb = statvfs.f_frsize * statvfs.f_bavail / (1024**3)
                if free_gb < 10:
                    logger.warning(f"Shard {shard.shard_id} espace faible ({free_gb:.1f} Go).")
                    async with shard.pool.get_connection() as conn:
                        await conn.execute("DELETE FROM search_cache WHERE julianday('now') - julianday(cached_at) > 30")
                        await conn.commit()
                    self.stats['actions'] += 1
            await asyncio.sleep(120)

# ------------------------------------------------------------------------------
# Classe SearchEngine (moteur de recherche principal)
# ------------------------------------------------------------------------------
class SearchEngine:
    """
    Moteur de recherche intelligent browNet, piloté par un essaim de bots.
    """
    def __init__(self, db_manager: HyperDatabaseManager):
        self.db_manager = db_manager
        self.swarm = BotSwarm(db_manager.base_path, num_bots=MAX_CONCURRENT_REQUESTS)  # utilise le chemin de la base
        self.security = SecurityAnalyzer()
        self.ranker = RankingEngine(db_manager.base_path)  # adapté
        self.sitemap_fetcher = None
        self.discovery_task = None
        self.suggest_server = None
        self.result_cache = TTLCache(maxsize=100, ttl=300)
        self.crawler = self.swarm  # pour compatibilité

    async def start(self):
        """Démarre l'essaim de bots et les services."""
        await self.swarm.start()
        self.sitemap_fetcher = SitemapFetcher(self.swarm)
        self.discovery_task = asyncio.create_task(self._discovery_worker())
        logger.info("Moteur de recherche démarré.")

    async def stop(self):
        """Arrête l'essaim."""
        if self.discovery_task:
            self.discovery_task.cancel()
        await self.swarm.stop()
        logger.info("Moteur de recherche arrêté.")

    async def _discovery_worker(self):
        """Tâche périodique de découverte via sitemaps."""
        while True:
            try:
                domains = list(self.swarm.stats['domains'])
                for domain in domains:
                    base_url = f"http://{domain}"
                    await self.sitemap_fetcher.fetch_sitemap(base_url)
                    await asyncio.sleep(1)
            except Exception as e:
                logger.error(f"Erreur dans discovery_worker: {e}")
            await asyncio.sleep(86400)

    async def index_page(self, url: str, title: str, html: str):
        """Indexe une page via le db_manager."""
        security_result = await self.security.analyze(url, html)
        soup = BeautifulSoup(html, 'lxml')
        for script in soup(['script', 'style']):
            script.decompose()
        text = soup.get_text(separator=' ', strip=True)

        # Stockage via db_manager
        await self.db_manager.store_page(url, title, html, security_result['score'], security_result['score'] < SECURITY_SCORE_THRESHOLD)
        # Soumettre l'URL à l'essaim
        await self.swarm.submit_url(url, priority=5)
        logger.info(f"Page indexée: {url}")

    async def search(self, query: str, page: int = 1, per_page: int = 10) -> List[Dict]:
        """Recherche locale via db_manager."""
        cache_key = f"local_{query}_{page}"
        if cache_key in self.result_cache:
            return self.result_cache[cache_key]

        # Utilise la méthode search du db_manager
        results = await self.db_manager.search(query, limit=per_page)
        # Ajouter des métadonnées
        for r in results:
            r['security_score'] = 1.0  # temporaire
        results = await self.ranker.rank(query, results)
        self.result_cache[cache_key] = results
        return results

    async def universal_search(self, query: str, page: int = 1, per_page: int = 10) -> List[Dict]:
        """Recherche universelle (simplifiée)."""
        return await self.search(query, page, per_page)

    async def _fetch_from_google(self, query: str, page: int, num: int) -> List[Dict]:
        return []  # simplification

    async def _estimate_security(self, url: str) -> float:
        return 0.9

    def get_swarm_stats(self) -> Dict:
        return self.swarm.get_stats()

    def generate_serp_html(self, query: str, results: List[Dict]) -> str:
        # Placeholder, à implémenter si besoin
        return "<html>..."

# ==============================================================================
# FIN DE L'INTÉGRATION DE search_engine.py
# ==============================================================================

# ==============================================================================
# INTERCEPTEUR DE REQUÊTES (déjà présent, mais on le conserve)
# ==============================================================================
class RequestInterceptor(QWebEngineUrlRequestInterceptor):
    def interceptRequest(self, info: QWebEngineUrlRequestInfo):
        url = info.requestUrl().toString()
        if any(domain in url for domain in [
            'accounts.google.com',
            'login.google.com',
            'signin.google.com',
            'accounts.youtube.com',
            'google.com/accounts',
            'google.com/signin'
        ]):
            logger.info(f"Requête bloquée : {url}")
            info.block(True)

# ==============================================================================
# SERVEUR FASTAPI (BACKEND)
# ==============================================================================
class BrowNetAPI:
    def __init__(self, db_manager: HyperDatabaseManager, search_engine: SearchEngine):
        self.db = db_manager
        self.engine = search_engine
        self.app = FastAPI(title="browNet API")
        self._setup_routes()

    def _setup_routes(self):
        @self.app.get("/")
        async def root():
            with open(INDEX_HTML_PATH, 'r', encoding='utf-8') as f:
                content = f.read()
            return HTMLResponse(content=content, status_code=200)

        @self.app.get("/api/search")
        async def search(q: str, cat: str = "all", page: int = 1):
            if not q:
                return {"error": "Missing query"}
            results = await self.engine.universal_search(q, page=page)
            return {"query": q, "category": cat, "page": page, "results": results}

        @self.app.get("/api/suggest")
        async def suggest(q: str):
            return []  # Placeholder

        @self.app.get("/api/stats")
        async def stats():
            db_stats = await self.db.get_stats()
            swarm_stats = self.engine.get_swarm_stats()
            return {"database": db_stats, "swarm": swarm_stats}

# ==============================================================================
# FENÊTRE PRINCIPALE (PYQT6) AVEC ANONYMISATION
# ==============================================================================
class BrowserWindow(QWebEngineView):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("browNet - Navigateur souverain")
        self.setMinimumSize(1200, 800)

        profile = QWebEngineProfile.defaultProfile()
        profile.setPersistentCookiesPolicy(QWebEngineProfile.NoPersistentCookies)
        profile.setHttpCacheType(QWebEngineProfile.MemoryHttpCache)
        profile.setCachePath("")
        profile.setPersistentStoragePath("")
        profile.setHttpUserAgent(
            "Mozilla/5.0 (compatible; Googlebot/2.1; +http://www.google.com/bot.html)"
        )

        interceptor = RequestInterceptor()
        profile.setUrlRequestInterceptor(interceptor)

        self.page().newWindowRequested.connect(self.on_new_window_requested)

        css_code = """
        #gb_70, .gb_1, a[href*='accounts.google.com'], .S96uS, .t789B,
        [aria-label*="Connexion"], [aria-label*="Sign in"], .gb_ya, .gb_Me, .gb_ve,
        div[role="dialog"], iframe[src*="accounts.google.com"], iframe[src*="google.com/accounts"],
        .gb_g, .gb_he, .gb_Df, .gb_ua, .gb_6d, [data-pid="signin"], .gb_Ve, .gb_We,
        [href*="ServiceLogin"], [href*="Logout"] {
            display: none !important;
            visibility: hidden !important;
            opacity: 0 !important;
            pointer-events: none !important;
            width: 0 !important;
            height: 0 !important;
            overflow: hidden !important;
            position: absolute !important;
            top: -9999px !important;
            left: -9999px !important;
        }
        """
        style_script = QWebEngineScript()
        style_script.setName("browNet_anti_login_css")
        style_script.setSourceCode(f"""
        (function() {{
            const style = document.createElement('style');
            style.textContent = `{css_code}`;
            document.documentElement.appendChild(style);
        }})();
        """)
        style_script.setInjectionPoint(QWebEngineScript.InjectionPoint.DocumentCreation)
        style_script.setWorldId(QWebEngineScript.ScriptWorldId.MainWorld)
        style_script.setRunsOnSubFrames(True)
        profile.scripts().insert(style_script)

        main_script = QWebEngineScript()
        main_script.setName("browNet_mutation_observer")
        main_script.setSourceCode("""
        (function() {
            const selectors = [
                '#gb_70', '.gb_1', 'a[href*="accounts.google.com"]',
                '.S96uS', '.t789B', '[aria-label*="Connexion"]',
                '[aria-label*="Sign in"]', '.gb_ya', '.gb_Me', '.gb_ve',
                'div[role="dialog"]', 'iframe[src*="accounts.google.com"]',
                '.gb_g', '.gb_he', '.gb_Df', '.gb_ua', '.gb_6d',
                '[data-pid="signin"]', '.gb_Ve', '.gb_We',
                '[href*="ServiceLogin"]', '[href*="Logout"]',
                '.gb_O', '.gb_P', '.gb_Q', '.gb_R',
                '[jsname="gXy3id"]', '[jscontroller="xz0jYc"]',
                '[jsaction*="signin"]', '[jsaction*="login"]'
            ];
            function removeLoginElements() {
                selectors.forEach(selector => {
                    document.querySelectorAll(selector).forEach(el => {
                        try { el.remove(); } catch(e) {}
                        if (el && el.parentNode) {
                            try {
                                el.style.setProperty('display', 'none', 'important');
                                el.style.setProperty('visibility', 'hidden', 'important');
                                el.style.setProperty('opacity', '0', 'important');
                                el.style.setProperty('pointer-events', 'none', 'important');
                            } catch(e) {}
                        }
                    });
                });
            }
            removeLoginElements();
            const observer = new MutationObserver(function(mutations) {
                let needsRemoval = false;
                mutations.forEach(mutation => {
                    if (mutation.addedNodes.length > 0) {
                        needsRemoval = true;
                    }
                });
                if (needsRemoval) {
                    removeLoginElements();
                }
            });
            observer.observe(document.documentElement, {
                childList: true,
                subtree: true,
                attributes: false,
                characterData: false
            });
            const intervalId = setInterval(removeLoginElements, 100);
            window.addEventListener('beforeunload', function() {
                clearInterval(intervalId);
                observer.disconnect();
            });
            const styleOverride = document.createElement('style');
            styleOverride.textContent = `
                ` + selectors.map(s => `${s} { display: none !important; }`).join(' ') + `
            `;
            document.documentElement.appendChild(styleOverride);
        })();
        """)
        main_script.setInjectionPoint(QWebEngineScript.InjectionPoint.DocumentReady)
        main_script.setWorldId(QWebEngineScript.ScriptWorldId.MainWorld)
        main_script.setRunsOnSubFrames(True)
        profile.scripts().insert(main_script)

        self.load(QUrl(f"http://{HOST}:{PORT}"))

    def on_new_window_requested(self, request):
        logger.info("Pop-up bloqué : %s", request.requestedUrl().toString())
        request.reject()

    def closeEvent(self, event):
        logger.info("Fermeture de la fenêtre browNet")
        QApplication.quit()
        event.accept()

# ==============================================================================
# ORCHESTRATEUR PRINCIPAL
# ==============================================================================
class BrowNetOrchestrator:
    def __init__(self):
        self.db: Optional[HyperDatabaseManager] = None
        self.engine: Optional[SearchEngine] = None
        self.api: Optional[BrowNetAPI] = None
        self.server_task: Optional[asyncio.Task] = None
        self.running = True
        self.loop: Optional[asyncio.AbstractEventLoop] = None

    async def start(self):
        logger.info("🚀 Démarrage de l'écosystème browNet...")

        logger.info("Initialisation de la base de données (16 shards)...")
        self.db = HyperDatabaseManager(DB_BASE_PATH, shard_count=SHARD_COUNT)
        await self.db.initialize()

        logger.info("Démarrage du moteur de recherche (essaim de 50 bots)...")
        self.engine = SearchEngine(db_manager=self.db)
        await self.engine.start()

        logger.info(f"Lancement du serveur API sur http://{HOST}:{PORT}")
        self.api = BrowNetAPI(self.db, self.engine)
        config = uvicorn.Config(
            self.api.app,
            host=HOST,
            port=PORT,
            log_level="warning",
            loop="asyncio"
        )
        server = uvicorn.Server(config)
        self.server_task = asyncio.create_task(server.serve())
        await asyncio.sleep(1)

        logger.info("✅ Tous les composants sont opérationnels.")

    async def stop(self):
        logger.info("🛑 Arrêt de l'écosystème browNet...")
        self.running = False
        if self.server_task:
            self.server_task.cancel()
            try:
                await self.server_task
            except asyncio.CancelledError:
                pass
        if self.engine:
            await self.engine.stop()
        if self.db:
            await self.db.close()
        logger.info("👋 Écosystème arrêté.")

    async def health_check_loop(self):
        while self.running:
            await asyncio.sleep(5)
            if self.server_task and self.server_task.done():
                exc = self.server_task.exception()
                logger.error(f"Le serveur API s'est arrêté : {exc}. Relance...")
                config = uvicorn.Config(self.api.app, host=HOST, port=PORT, log_level="warning", loop="asyncio")
                server = uvicorn.Server(config)
                self.server_task = asyncio.create_task(server.serve())
            if self.engine and not self.engine.crawler.running:
                logger.error("Le moteur de recherche s'est arrêté. Relance...")
                await self.engine.start()

# ==============================================================================
# INTÉGRATION AVEC PYQT
# ==============================================================================
def run_pyqt(orchestrator: BrowNetOrchestrator):
    app = QApplication(sys.argv)
    loop = qasync.QEventLoop(app)
    asyncio.set_event_loop(loop)

    window = BrowserWindow()
    window.show()

    asyncio.ensure_future(orchestrator.health_check_loop())

    with loop:
        loop.run_forever()

# ==============================================================================
# POINT D'ENTRÉE PRINCIPAL
# ==============================================================================
def main():
    if not os.path.exists(INDEX_HTML_PATH):
        logger.error(f"Fichier {INDEX_HTML_PATH} introuvable.")
        sys.exit(1)

    orchestrator = BrowNetOrchestrator()

    async def startup():
        try:
            await orchestrator.start()
        except Exception as e:
            logger.exception(f"Erreur fatale : {e}")
            sys.exit(1)

    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    loop.run_until_complete(startup())

    signal.signal(signal.SIGINT, lambda s, f: QApplication.quit())
    run_pyqt(orchestrator)

if __name__ == "__main__":
    main()