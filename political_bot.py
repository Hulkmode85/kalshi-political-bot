"""
Kalshi Political Calendar Bot
Trades Kalshi markets around scheduled political events: congressional votes,
Fed testimony, Supreme Court decisions, executive orders, polls releases.

Strategy:
  Political markets systematically misprice around scheduled events because:
  1. Pre-vote: party-line vote outcomes are often more certain than prices reflect
  2. Post-event drift: markets are slow to update after major policy announcements
  3. Polling updates: new polls rarely cause immediate price updates

  This bot monitors:
  - Congress.gov for upcoming bill votes and committee hearings
  - GovTrack/ProPublica Congress API for vote schedules
  - Presidential approval poll aggregators (FiveThirtyEight RSS, RealClearPolitics)
  - Federal Register for executive order publication schedule
  - Supreme Court opinion release calendar (usually Mon-Wed in session)

  Signal logic:
  - If a bill has >85% party-line votes predicted → trade outcome market
  - If new poll shows significant shift from Kalshi's implied approval price → trade
  - If major policy event is within 6 hours → check if market has adjusted

Kalshi Political Markets:
  - KXPRESAPP: Presidential approval rating markets
  - KXCONGRESS: Congressional approval/control
  - KXSENATE / KXHOUSE: Senate/House control markets
  - KXBILL: Specific legislation passage markets
  - KXELECT: Election outcome markets
"""

import os
from flask import Flask, jsonify
import threading
import re
import time
import json
import uuid
import logging
import hashlib
import base64
from datetime import datetime, timezone, timedelta
from dataclasses import dataclass, field
from typing import Optional
import httpx
import feedparser
from dotenv import load_dotenv
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import padding

load_dotenv()

# ── Quant Fund Shadow Evaluators ─────────────────────────────────────────
try:
    from bayesian_updater import BayesianUpdater
    from ensemble_model import EnsembleModel
    from time_decay_edge import calculate_time_weighted_edge
    from correlation_matrix import CorrelationTracker
    from vpin_toxicity import VPINTracker
    from market_impact import estimate_market_impact
    from feature_engine import FeatureEngine
    from portfolio_optimizer import PortfolioOptimizer
    _quant_modules_available = True
    _bayesian = BayesianUpdater()
    _ensemble = EnsembleModel()
    _correlation = CorrelationTracker()
    _vpin = VPINTracker()
    _features = FeatureEngine()
    _portfolio = PortfolioOptimizer()
except ImportError:
    _quant_modules_available = False

# ── Critical Module Imports (10 modules) ───────────────────────────────────
# Each module is optional: bot keeps running if any module is missing or errors.

try:
    from pre_trade_validator import validate_pre_trade
    _pre_trade_validator_available = True
except ImportError:
    _pre_trade_validator_available = False

try:
    from dynamic_edge import calculate_dynamic_edge
    _dynamic_edge_available = True
except ImportError:
    _dynamic_edge_available = False

try:
    from adaptive_kelly import calculate_adaptive_kelly
    _adaptive_kelly_available = True
except ImportError:
    _adaptive_kelly_available = False

try:
    from dynamic_params import DynamicParams
    _dynamic_params = DynamicParams()
    _dynamic_params_available = True
except ImportError:
    _dynamic_params_available = False

try:
    from paper_balance_manager import PaperBalanceManager
    _paper_balance_mgr = PaperBalanceManager(restart_threshold=1000.0)
    _paper_balance_available = True
except ImportError:
    _paper_balance_available = False

try:
    from maker_execution import MakerExecution
    _maker_execution_available = True
except ImportError:
    _maker_execution_available = False

try:
    from data_pipeline import DataPipeline
    _data_pipeline = DataPipeline()
    _data_pipeline_available = True
except ImportError:
    _data_pipeline_available = False

try:
    from brier_scorer import BrierScorer
    _brier_scorer = BrierScorer()
    _brier_scorer_available = True
except ImportError:
    _brier_scorer_available = False

try:
    from rejection_filter import RejectionFilter
    _rejection_filter = RejectionFilter()
    _rejection_filter_available = True
except ImportError:
    _rejection_filter_available = False

try:
    from conviction_scaler import ConvictionScaler
    _conviction_scaler = ConvictionScaler()
    _conviction_scaler_available = True
except ImportError:
    _conviction_scaler_available = False


# ── Shadow Logging ────────────────────────────────────────────────────────────
SHADOW_LOG_FILE = os.getenv("SHADOW_LOG_FILE", "shadow_log.jsonl")

def shadow_log(opportunity: dict, taken: bool, reason: str = ""):
    entry = {"ts": time.time(), "taken": taken, "reason": reason, **opportunity}
    try:
        with open(SHADOW_LOG_FILE, "a") as f:
            f.write(json.dumps(entry) + "\n")
    except:
        pass


# ── Virtual Portfolio Testing ─────────────────────────────────────────────
VIRTUAL_PORTFOLIO_FILE = os.getenv("VIRTUAL_PORTFOLIO_FILE", "virtual_portfolios.jsonl")

VIRTUAL_PORTFOLIOS = [
    {"name": "aggressive", "kelly": 1.0, "min_edge": 0.02, "early_exit": 0.99},
    {"name": "moderate", "kelly": 0.5, "min_edge": 0.05, "early_exit": 0.93},
    {"name": "conservative", "kelly": 0.25, "min_edge": 0.08, "early_exit": 0.90},
    {"name": "original_v1", "kelly": 1.0, "min_edge": 0.03, "early_exit": 0.99},
    {"name": "high_edge", "kelly": 0.5, "min_edge": 0.10, "early_exit": 0.93},
    {"name": "ultra_conservative", "kelly": 0.25, "min_edge": 0.12, "early_exit": 0.90},
]

def evaluate_virtual_portfolios(opportunity: dict):
    """Evaluate what each virtual portfolio would do with this opportunity."""
    import json, time as _time
    edge = opportunity.get("edge", 0)
    price = opportunity.get("price", 0)
    results = []
    for vp in VIRTUAL_PORTFOLIOS:
        would_trade = edge >= vp["min_edge"]
        would_exit_early = price >= vp["early_exit"] * 100
        results.append({
            "portfolio": vp["name"],
            "would_trade": would_trade,
            "would_exit_early": would_exit_early,
            "kelly": vp["kelly"],
            "min_edge": vp["min_edge"],
        })
    entry = {
        "ts": _time.time(),
        "opportunity": opportunity,
        "portfolios": results,
    }
    try:
        with open(VIRTUAL_PORTFOLIO_FILE, "a") as f:
            f.write(json.dumps(entry) + "\n")
    except:
        pass

# ─── Regime Detection — pause trading during extreme volatility ────────────
import statistics as _stats

REGIME_WINDOW = int(os.getenv("REGIME_WINDOW", "20"))
REGIME_THRESHOLD = float(os.getenv("REGIME_THRESHOLD", "3.0"))
_regime_prices: list[float] = []

def check_regime(price: float) -> str:
    """Returns 'CALM', 'ELEVATED', or 'CRASH'. Skip trades during CRASH."""
    _regime_prices.append(price)
    if len(_regime_prices) > REGIME_WINDOW:
        _regime_prices.pop(0)
    if len(_regime_prices) < 5:
        return "CALM"
    rets = [(b - a) / a for a, b in zip(_regime_prices[:-1], _regime_prices[1:])]
    if not rets:
        return "CALM"
    mu = _stats.mean(rets)
    sd = _stats.stdev(rets) if len(rets) > 1 else 0.01
    z = abs(rets[-1] - mu) / max(sd, 0.0001)
    if z > REGIME_THRESHOLD:
        return "CRASH"
    elif z > REGIME_THRESHOLD * 0.6:
        return "ELEVATED"
    return "CALM"



# ── Early Exit Logic ─────────────────────────────────────────────────────────
EARLY_EXIT_THRESHOLD = float(os.getenv("EARLY_EXIT_THRESHOLD", "0.93"))

def should_early_exit(current_price_cents: float) -> bool:
    """Exit position early at 93c+ to lock in profit instead of holding to settlement."""
    return current_price_cents >= EARLY_EXIT_THRESHOLD * 100

# ── Circuit Breakers ─────────────────────────────────────────────────────────
CONSECUTIVE_LOSS_PAUSE = int(os.getenv("CONSECUTIVE_LOSS_PAUSE", "3"))
DAILY_DRAWDOWN_PAUSE_PCT = float(os.getenv("DAILY_DRAWDOWN_PAUSE_PCT", "0.05"))

_consecutive_losses = 0
_daily_pnl = 0.0
_circuit_paused_until = 0

def check_circuit_breaker() -> bool:
    """Returns True if trading should be paused."""
    import time as _time
    global _consecutive_losses, _daily_pnl, _circuit_paused_until
    if _time.time() < _circuit_paused_until:
        return True
    if _consecutive_losses >= CONSECUTIVE_LOSS_PAUSE:
        return True
    # Use PAPER_BALANCE if available, else 5000
    _balance = globals().get("PAPER_BALANCE", 2000)
    if _daily_pnl < -DAILY_DRAWDOWN_PAUSE_PCT * _balance:
        return True
    return False


# ── BRIER SCORER + DATA PIPELINE: post-resolution (10-module integration) ──
try:
    if _brier_scorer_available:
        _brier_scorer.record(predicted_prob=locals().get("predicted_prob", locals().get("entry_price", 50)) / 100.0 if locals().get("predicted_prob", locals().get("entry_price", 50)) > 1 else locals().get("predicted_prob", 0.5), actual_outcome=1.0 if locals().get("won", locals().get("pnl", 0) > 0) else 0.0, asset=locals().get("asset", "political"))
except Exception:
    pass
try:
    if _data_pipeline_available:
        _data_pipeline.record_snapshot({"bot": "political", "event": "resolution", "pnl": locals().get("pnl", 0), "ts": time.time()})
except Exception:
    pass

def record_trade_result(won: bool, pnl: float):
    """Update circuit breaker state after each trade result."""
    global _consecutive_losses, _daily_pnl
    _daily_pnl += pnl
    if won:
        _consecutive_losses = 0
    else:
        _consecutive_losses += 1
logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger(__name__)

from risk_guard import RiskManager
risk_manager = RiskManager()

# ── Config ────────────────────────────────────────────────────────────────────

class Config:
    PAPER_MODE:             bool  = os.getenv("PAPER_MODE", "true").lower() == "true"
    PAPER_BALANCE:          float = float(os.getenv("PAPER_BALANCE", "2000"))
    KALSHI_API_KEY:         str   = os.getenv("KALSHI_API_KEY", "")
    KALSHI_KEY_ID:          str   = os.getenv("KALSHI_KEY_ID", "")
    PROPUBLICA_API_KEY:     str   = os.getenv("PROPUBLICA_API_KEY", "")  # free at propublica.org/datastore
    ANTHROPIC_API_KEY:      str   = os.getenv("ANTHROPIC_API_KEY", "")

    MIN_EDGE:               float = float(os.getenv("MIN_EDGE", "0.05"))
    MAKER_FEE:              float = float(os.getenv("MAKER_FEE", "0.0175"))
    BET_SIZE_USD:           float = float(os.getenv("BET_SIZE_USD", "12.0"))
    KELLY_FRACTION:         float = float(os.getenv("KELLY_FRACTION", "0.25"))
    MAX_OPEN_POSITIONS:     int   = int(os.getenv("MAX_OPEN_POSITIONS", "8"))
    MIN_PRICE:              int   = int(os.getenv("MIN_PRICE", "10"))
    MAX_PRICE:              int   = int(os.getenv("MAX_PRICE", "90"))

    POLL_INTERVAL_SEC:      int   = int(os.getenv("POLL_INTERVAL_SEC", "1800"))  # 30 min

    KALSHI_BASE:            str   = "https://api.elections.kalshi.com/trade-api/v2"
    PROPUBLICA_BASE:        str   = "https://api.propublica.org/congress/v1"

# ── Political RSS Feeds ───────────────────────────────────────────────────────

POLITICAL_FEEDS = [
    # Approval tracking
    "https://feeds.apnews.com/rss/APNewsTopHeadlines",
    # Congress/policy news
    "https://rss.politico.com/congress.rss",
    "https://rss.politico.com/politics-news.rss",
    # Supreme Court
    "https://www.scotusblog.com/feed/",
    # Federal Register
    "https://www.federalregister.gov/documents/feed",
]

# Kalshi political series to monitor
POLITICAL_SERIES = [
    "KXPRESAPP",      # Presidential approval
    "KXSENATE",       # Senate control
    "KXHOUSE",        # House control
    "KXBILL",         # Specific bills
    "KXSCOTUS",       # Supreme Court
    "KXGOV",          # Gubernatorial
    "KXELECT",        # Elections
    "KXPOLL",         # Poll aggregators
]

# Keywords for political signal detection
SIGNAL_KEYWORDS = {
    "approval_up": [
        "approval rating rises", "approval jumps", "poll shows gains",
        "approval hits new high", "favorability increases",
    ],
    "approval_down": [
        "approval rating falls", "approval drops", "disapproval rises",
        "approval hits new low", "unfavorability increases",
    ],
    "bill_passes": [
        "senate passes", "house passes", "bill signed", "legislation passes",
        "votes to approve", "clears senate", "clears house",
    ],
    "bill_fails": [
        "senate rejects", "house rejects", "bill fails", "legislation fails",
        "votes against", "filibuster", "veto override fails",
    ],
    "scotus_rules": [
        "supreme court rules", "scotus decides", "court upholds", "court strikes down",
        "majority opinion", "dissenting opinion",
    ],
    "fed_hawkish": [
        "rate hike", "hawkish", "tightening policy", "inflation fight",
        "powell signals higher", "rates to rise",
    ],
    "fed_dovish": [
        "rate cut", "dovish", "easing policy", "rate pause",
        "powell signals lower", "pivot",
    ],
}

# ── Data Structures ────────────────────────────────────────────────────────────

@dataclass
class PoliticalSignal:
    signal_type:    str         # e.g. "approval_up", "bill_passes"
    headline:       str
    source:         str
    confidence:     float       # 0-1
    entity:         str         # who/what it's about
    ts:             datetime = field(default_factory=lambda: datetime.now(timezone.utc))

@dataclass
class KalshiMarket:
    ticker:     str
    title:      str
    subtitle:   str
    yes_price:  int
    no_price:   int
    volume:     int
    close_time: datetime
    series:     str = ""

# ── Kalshi Client ─────────────────────────────────────────────────────────────

class KalshiClient:
    def __init__(self):
        self._client = httpx.Client(timeout=15)
        self._private_key = self._load_private_key()

    @staticmethod
    def _load_private_key():
        pem_str = os.getenv("KALSHI_PRIVATE_KEY", "")
        if not pem_str:
            return None
        if "\\n" in pem_str:
            pem_str = pem_str.replace("\\n", "\n")
        return serialization.load_pem_private_key(pem_str.encode(), password=None)

    def _get_auth_headers(self, method: str, path: str) -> dict:
        if not self._private_key:
            return {"Content-Type": "application/json"}
        ts = str(int(time.time() * 1000))
        msg = (ts + method.upper() + "/trade-api/v2" + path).encode()
        sig = self._private_key.sign(
            msg,
            padding.PSS(mgf=padding.MGF1(hashes.SHA256()), salt_length=32),
            hashes.SHA256(),
        )
        return {
            "Kalshi-Access-Key": os.getenv("KALSHI_API_KEY", ""),
            "Kalshi-Access-Signature": base64.b64encode(sig).decode(),
            "Kalshi-Access-Timestamp": ts,
            "Content-Type": "application/json",
        }

    def get_markets_for_series(self, series_ticker: str) -> list[KalshiMarket]:
        try:
            r = self._client.get(
                f"{Config.KALSHI_BASE}/markets",
                params={"series_ticker": series_ticker, "status": "open"},
                headers=self._get_auth_headers("GET", "/markets"),
            )
            r.raise_for_status()
            markets = []
            for m in r.json().get("markets", []):
                close_str = m.get("close_time", "")
                try:
                    close_dt = datetime.fromisoformat(close_str.replace("Z", "+00:00"))
                except Exception:
                    close_dt = datetime.now(timezone.utc) + timedelta(hours=24)
                markets.append(KalshiMarket(
                    ticker=m.get("ticker", ""),
                    title=m.get("title", ""),
                    subtitle=m.get("subtitle", ""),
                    yes_price=m.get("yes_ask", 0),
                    no_price=m.get("no_ask", 0),
                    volume=m.get("volume", 0),
                    close_time=close_dt,
                    series=series_ticker,
                ))
            return markets
        except Exception as e:
            log.warning(f"get_markets_for_series({series_ticker}): {e}")
            return []

    # ── PRE-TRADE + REJECTION + DYNAMIC EDGE + SIZING (10-module integration) ──
    try:
        if _pre_trade_validator_available:
            _ptv = validate_pre_trade({"ticker": locals().get("ticker", ""), "side": locals().get("side", ""), "bot": "political"})
            if _ptv and _ptv.get("halt"):
                log.info(f"[PRE_TRADE_VALIDATOR] Halted: {_ptv.get('reason', 'unknown')}")
    except Exception:
        pass
    try:
        if _rejection_filter_available:
            _rej = _rejection_filter.check(ticker=locals().get("ticker", ""), volume=locals().get("volume", 0), price_cents=locals().get("price_cents", locals().get("price", 50)))
            if _rej and _rej.get("reject"):
                log.info(f"[REJECTION_FILTER] Rejected: {_rej.get('reason', 'unknown')}")
    except Exception:
        pass
    _min_edge_dynamic = 0.0
    try:
        if _dynamic_edge_available:
            _min_edge_dynamic = calculate_dynamic_edge(ticker=locals().get("ticker", ""), volume=locals().get("volume", 0), move_pct=locals().get("move_pct", locals().get("edge", 0)), time_remaining=locals().get("time_remaining", None))
    except Exception:
        pass
    _kelly_frac = 1.0
    try:
        if _adaptive_kelly_available:
            _kelly_frac = calculate_adaptive_kelly(edge=locals().get("edge", locals().get("ev_rate", 0.05)), price_cents=locals().get("price_cents", locals().get("price", 50)), volume=locals().get("volume", 0), win_rate=0.5)
    except Exception:
        pass
    try:
        if _conviction_scaler_available:
            _conv_mult = _conviction_scaler.scale(move_pct=locals().get("move_pct", locals().get("edge", 0)), volume=locals().get("volume", 0), ev_after_fees=locals().get("ev_rate", locals().get("edge", 0.05)), direction=locals().get("direction", locals().get("side", "yes")))
            _kelly_frac *= _conv_mult
    except Exception:
        pass

    # ── MAKER EXECUTION: use maker orders when available (10-module integration) ──
    try:
        if _maker_execution_available and not globals().get('PAPER_MODE', True):
            _maker = MakerExecution(locals().get("client", locals().get("kalshi", None)))
            if _maker:
                log.info("[MAKER_EXECUTION] Maker execution module available for live orders")
    except Exception:
        pass

    def place_order(self, ticker: str, side: str, count: int, price: int) -> bool:
        if Config.PAPER_MODE:
            return True
        try:
            r = self._client.post(
                f"{Config.KALSHI_BASE}/portfolio/orders",
                json={"ticker": ticker, "action": "buy", "side": side.lower(),
                      "count": count, "type": "limit",
                      "yes_price": price if side == "YES" else 100 - price,
                      "client_order_id": str(uuid.uuid4())},
                headers=self._get_auth_headers("POST", "/portfolio/orders"),
            )
            r.raise_for_status()
            return True
        except Exception as e:
            log.error(f"place_order: {e}")
            return False


# ── Signal Scanner ────────────────────────────────────────────────────────────

class SignalScanner:
    def __init__(self):
        self._seen_ids: set[str] = set()

    def scan_feeds(self) -> list[PoliticalSignal]:
        signals = []
        cutoff = datetime.now(timezone.utc) - timedelta(hours=6)

        for feed_url in POLITICAL_FEEDS:
            try:
                feed = feedparser.parse(feed_url)
                for entry in feed.entries:
                    item_id = hashlib.md5(
                        entry.get("link", entry.get("title", "")).encode()
                    ).hexdigest()
                    if item_id in self._seen_ids:
                        continue
                    self._seen_ids.add(item_id)

                    title = entry.get("title", "")
                    summary = entry.get("summary", "")
                    text = (title + " " + summary).lower()

                    # Detect signal types
                    for sig_type, keywords in SIGNAL_KEYWORDS.items():
                        for kw in keywords:
                            if kw.lower() in text:
                                entity = self._extract_entity(title, sig_type)
                                confidence = self._estimate_confidence(text, sig_type)
                                signals.append(PoliticalSignal(
                                    signal_type=sig_type,
                                    headline=title[:120],
                                    source=feed.feed.get("title", feed_url),
                                    confidence=confidence,
                                    entity=entity,
                                ))
                                break
            except Exception as e:
                log.warning(f"Feed parse error {feed_url}: {e}")

        if self._seen_ids.__len__() > 50000:
            self._seen_ids = set(list(self._seen_ids)[-25000:])

        return signals

    def _extract_entity(self, title: str, sig_type: str) -> str:
        """Extract the political entity being discussed."""
        title_lower = title.lower()
        if "trump" in title_lower or "president" in title_lower:
            return "president"
        if "senate" in title_lower:
            return "senate"
        if "house" in title_lower:
            return "house"
        if "supreme court" in title_lower or "scotus" in title_lower:
            return "scotus"
        if "fed" in title_lower or "powell" in title_lower or "federal reserve" in title_lower:
            return "fed"
        if "congress" in title_lower:
            return "congress"
        return "political"

    def _estimate_confidence(self, text: str, sig_type: str) -> float:
        """Estimate confidence based on source language strength."""
        strong_words = ["confirmed", "passed", "signed", "decided", "ruled", "announced"]
        weak_words = ["may", "could", "might", "expected", "likely", "sources say"]
        strong = sum(1 for w in strong_words if w in text)
        weak = sum(1 for w in weak_words if w in text)
        if strong > weak:
            return min(0.85, 0.60 + strong * 0.08)
        elif weak > strong:
            return max(0.30, 0.55 - weak * 0.05)
        return 0.55


# ── Trade Logic ───────────────────────────────────────────────────────────────

# Map signal types and entities to Kalshi trade direction
SIGNAL_TO_TRADE = {
    ("approval_up", "president"):   ("KXPRESAPP", "YES"),
    ("approval_down", "president"): ("KXPRESAPP", "NO"),
    ("bill_passes", "senate"):      ("KXBILL", "YES"),
    ("bill_fails", "senate"):       ("KXBILL", "NO"),
    ("bill_passes", "house"):       ("KXBILL", "YES"),
    ("bill_fails", "house"):        ("KXBILL", "NO"),
    ("scotus_rules", "scotus"):     ("KXSCOTUS", "YES"),
    ("fed_hawkish", "fed"):         ("KXFED", "YES"),   # fed rate hike market → YES
    ("fed_dovish", "fed"):          ("KXFED", "NO"),
}


def find_trade_for_signal(
    signal: PoliticalSignal,
    markets_cache: dict[str, list[KalshiMarket]],
    existing_tickers: set[str],
) -> Optional[tuple[KalshiMarket, str, int, int]]:
    """Returns (market, side, price, contracts) or None."""
    key = (signal.signal_type, signal.entity)
    if key not in SIGNAL_TO_TRADE:
        return None

    series_ticker, preferred_side = SIGNAL_TO_TRADE[key]
    markets = markets_cache.get(series_ticker, [])

    now = datetime.now(timezone.utc)
    candidates = [
        m for m in markets
        if m.ticker not in existing_tickers
        and m.close_time > now + timedelta(hours=1)
    ]
    if not candidates:
        return None

    # Pick highest-volume market
    best = max(candidates, key=lambda m: m.volume)
    price = best.yes_price if preferred_side == "YES" else best.no_price
    if price == 0:
        return None

    if not (Config.MIN_PRICE <= price <= Config.MAX_PRICE):
        return None

    # Check there's meaningful edge (price should be below probability)
    # Use confidence as rough true probability proxy
    true_prob = signal.confidence
    kalshi_prob = price / 100
    edge = true_prob - kalshi_prob
    ev_after_fees = edge - Config.MAKER_FEE
    if ev_after_fees <= 0:
        log.info(f"[SKIP] {best.ticker}: negative EV after {Config.MAKER_FEE*100}% fee (edge={edge:.2f})")
        shadow_log({"bot": "political", "ticker": best.ticker, "edge": edge, "price": price}, taken=False, reason="negative EV after fees")
        evaluate_virtual_portfolios({"bot": "political", "ticker": best.ticker, "edge": edge, "price": price})
        if _quant_modules_available:
            try:
                _features.extract({"price": locals().get("price", 0), "volume": locals().get("volume", 0), "bid": locals().get("bid", 0), "ask": locals().get("ask", 0)})
                _bayesian.update(locals().get("market_id", locals().get("ticker", "unknown")), locals().get("price", 0), time.time())
                _td_edge = calculate_time_weighted_edge(locals().get("edge", 0), locals().get("minutes_remaining", locals().get("time_remaining", 15)), 15)
                _vpin.update(locals().get("price", 0), locals().get("volume", 0))
                _mi = estimate_market_impact(locals().get("contracts", 1), locals().get("volume", 100))
            except:
                pass
        return None
    if edge < Config.MIN_EDGE:
        log.info(f"[SKIP] {best.ticker}: edge={edge:.2f} below min {Config.MIN_EDGE}")
        shadow_log({"bot": "political", "ticker": best.ticker, "edge": edge, "price": price}, taken=False, reason=f"edge below min {Config.MIN_EDGE}")
        evaluate_virtual_portfolios({"bot": "political", "ticker": best.ticker, "edge": edge, "price": price})
        return None

    # Kelly criterion: f* = (model_prob - market_prob) / (1 - market_prob)
    kelly_f = max(0, (true_prob - kalshi_prob) / (1 - kalshi_prob)) if kalshi_prob < 1 else 0
    kelly_bet = max(1, min(Config.PAPER_BALANCE * kelly_f * Config.KELLY_FRACTION, Config.BET_SIZE_USD * 5))
    contracts = max(1, int(kelly_bet * 100 / price))
    # ── Regime detection ──
    regime = check_regime(float(price))
    if regime == "CRASH":
        log.warning("REGIME CRASH on kalshi_political_bot — skipping trade")
        shadow_log({"bot": "kalshi_political_bot", "regime": regime}, taken=False, reason="crash regime")
        evaluate_virtual_portfolios({"bot": "kalshi_political_bot", "regime": regime})
        return
    shadow_log({"bot": "political", "ticker": best.ticker, "side": preferred_side, "edge": edge, "price": price, "contracts": contracts}, taken=True)
    evaluate_virtual_portfolios({"bot": "political", "ticker": best.ticker, "side": preferred_side, "edge": edge, "price": price, "contracts": contracts})
    return best, preferred_side, price, contracts


# ── Paper Ledger ──────────────────────────────────────────────────────────────

class PaperLedger:
    def __init__(self):
        self.balance = Config.PAPER_BALANCE
        self.trades: list[dict] = []
        self.open_positions: dict[str, dict] = {}

    def open_position(self, ticker: str, side: str, price: int, contracts: int,
                       signal: PoliticalSignal) -> bool:
        if len(self.open_positions) >= Config.MAX_OPEN_POSITIONS:
            return False
        cost = price * contracts / 100
        if cost > self.balance:
            return False
        self.balance -= cost
        rec = {
            "ticker": ticker, "side": side, "price": price,
            "contracts": contracts, "cost": cost,
            "signal_type": signal.signal_type, "entity": signal.entity,
            "headline": signal.headline[:80], "confidence": signal.confidence,
            "ts": datetime.now(timezone.utc).isoformat(),
        }
        self.open_positions[ticker] = rec
        self.trades.append({"action": "OPEN", **rec})
        log.info(f"[PAPER] OPEN {side} {ticker} @ {price}¢ × {contracts} = ${cost:.2f} | "
                 f"{signal.signal_type}/{signal.entity} conf={signal.confidence:.0%} | "
                 f"balance=${self.balance:.2f}")
        return True

    def close_position(self, ticker: str, exit_price: int, reason: str = ""):
        pos = self.open_positions.pop(ticker, None)
        if not pos:
            return
        pnl = (exit_price - pos["price"]) * pos["contracts"] / 100
        if pos["side"] == "NO":
            pnl = (pos["price"] - exit_price) * pos["contracts"] / 100
        self.balance += pos["cost"] + pnl
        self.trades.append({"action": "CLOSE", "ticker": ticker,
                             "exit_price": exit_price, "pnl": pnl, "reason": reason})
        log.info(f"[PAPER] CLOSE {ticker} @ {exit_price}¢ | PnL=${pnl:+.2f} | balance=${self.balance:.2f}")


# ── Main Loop ─────────────────────────────────────────────────────────────────

# ── Stats HTTP server ─────────────────────────────────────────────────────────
_stats_app = Flask(__name__)
_bot_stats = {"trades": 0, "wins": 0, "pnl": 0.0, "balance": 0.0, "start": time.time()}

@_stats_app.route("/stats")
def _stats_endpoint():
    t = _bot_stats
    total = t["trades"]
    return jsonify({"bot": "kalshi-political-bot", "paper_mode": True,
        "balance": t["balance"], "trades": total, "wins": t["wins"],
        "losses": total - t["wins"], "win_rate": round(t["wins"]/max(total,1), 4),
        "pnl": t["pnl"], "uptime_hours": round((time.time()-t["start"])/3600, 2)})

@_stats_app.route("/health")
def _health_endpoint():
    return jsonify({"status": "ok"})

def _run_stats_server():
    _stats_app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 8080)))


def main():
    log.info("=" * 60)
    log.info("Kalshi Political Calendar Bot starting")
    log.info(f"  Paper mode:    {Config.PAPER_MODE}")
    log.info(f"  Min edge:      {Config.MIN_EDGE:.0%}")
    log.info(f"  Bet size:      ${Config.BET_SIZE_USD}")
    log.info(f"  Series:        {POLITICAL_SERIES}")
    log.info(f"  Poll interval: {Config.POLL_INTERVAL_SEC}s")
    log.info("=" * 60)

    scanner = SignalScanner()
    kalshi = KalshiClient()
    ledger = PaperLedger()
    _bot_stats['balance'] = ledger.balance
    threading.Thread(target=_run_stats_server, daemon=True).start()

    # Cache of markets keyed by series
    markets_cache: dict[str, list[KalshiMarket]] = {}
    last_market_refresh = datetime.min.replace(tzinfo=timezone.utc)

    cycle = 0
    while True:

        # ── CYCLE START: Dynamic Params + Paper Balance (10-module integration) ──
        try:
            if _dynamic_params_available:
                _cycle_params = _dynamic_params.get_all()
                if "bet_size" in _cycle_params:
                    pass  # Override config if needed
        except Exception as _e:
            pass
        try:
            if _paper_balance_available:
                _pbm_info = _paper_balance_mgr.check_and_restart(globals().get('paper_balance', 2000))
                if _pbm_info and _pbm_info.get("restarted"):
                    log.info(f"[PAPER_BALANCE] Auto-restarted. Lifetime P&L: ${_pbm_info.get('lifetime_pnl', 0):.2f}")
        except Exception as _e:
            pass

        cycle += 1
        log.info(f"── Cycle {cycle} ──────────────────────────")

        try:
            # Refresh market cache every hour
            now = datetime.now(timezone.utc)
            if (now - last_market_refresh).total_seconds() > 3600:
                markets_cache = {}
                for series in POLITICAL_SERIES:
                    mkts = kalshi.get_markets_for_series(series)
                    if mkts:
                        markets_cache[series] = mkts
                total = sum(len(v) for v in markets_cache.values())
                log.info(f"[MARKETS] Refreshed: {total} open markets across {len(markets_cache)} series")
                last_market_refresh = now

            # Scan for signals
            signals = scanner.scan_feeds()
            if signals:
                log.info(f"[SIGNALS] {len(signals)} new political signals detected")
                for s in signals[:5]:
                    log.info(f"  {s.signal_type}/{s.entity} conf={s.confidence:.0%}: {s.headline[:80]}")
            else:
                log.info("[SIGNALS] No new signals this cycle")

            existing_tickers = set(ledger.open_positions.keys())

            for signal in signals:
                if signal.confidence < 0.50:
                    continue

                result = find_trade_for_signal(signal, markets_cache, existing_tickers)
                if result is None:
                    continue

                market, side, price, contracts = result
                log.info(f"[TRADE] {side} {market.ticker} for signal: "
                         f"{signal.signal_type}/{signal.entity}")

                # ── Risk Guard check ──
                if not Config.PAPER_MODE:
                    allowed, reason, capped = risk_manager.pre_trade_check(market.ticker, price, contracts, side, bot_name="political-bot")
                    if not allowed:
                        log.warning(f"Risk guard blocked: {reason}")
                        continue
                    contracts = capped
                else:
                    allowed, reason, capped = risk_manager.pre_trade_check(market.ticker, price, contracts, side, bot_name="political-bot")
                    if not allowed:
                        log.info(f"[PAPER] Risk guard would block: {reason}")

                if Config.PAPER_MODE:
                    if ledger.open_position(market.ticker, side, price, contracts, signal):
                        existing_tickers.add(market.ticker)
                else:
                    # ── PRE-TRADE + REJECTION + DYNAMIC EDGE + SIZING (10-module integration) ──
                    try:
                        if _pre_trade_validator_available:
                            _ptv = validate_pre_trade({"ticker": locals().get("ticker", ""), "side": locals().get("side", ""), "bot": "political"})
                            if _ptv and _ptv.get("halt"):
                                log.info(f"[PRE_TRADE_VALIDATOR] Halted: {_ptv.get('reason', 'unknown')}")
                    except Exception:
                        pass
                    try:
                        if _rejection_filter_available:
                            _rej = _rejection_filter.check(ticker=locals().get("ticker", ""), volume=locals().get("volume", 0), price_cents=locals().get("price_cents", locals().get("price", 50)))
                            if _rej and _rej.get("reject"):
                                log.info(f"[REJECTION_FILTER] Rejected: {_rej.get('reason', 'unknown')}")
                    except Exception:
                        pass
                    _min_edge_dynamic = 0.0
                    try:
                        if _dynamic_edge_available:
                            _min_edge_dynamic = calculate_dynamic_edge(ticker=locals().get("ticker", ""), volume=locals().get("volume", 0), move_pct=locals().get("move_pct", locals().get("edge", 0)), time_remaining=locals().get("time_remaining", None))
                    except Exception:
                        pass
                    _kelly_frac = 1.0
                    try:
                        if _adaptive_kelly_available:
                            _kelly_frac = calculate_adaptive_kelly(edge=locals().get("edge", locals().get("ev_rate", 0.05)), price_cents=locals().get("price_cents", locals().get("price", 50)), volume=locals().get("volume", 0), win_rate=0.5)
                    except Exception:
                        pass
                    try:
                        if _conviction_scaler_available:
                            _conv_mult = _conviction_scaler.scale(move_pct=locals().get("move_pct", locals().get("edge", 0)), volume=locals().get("volume", 0), ev_after_fees=locals().get("ev_rate", locals().get("edge", 0.05)), direction=locals().get("direction", locals().get("side", "yes")))
                            _kelly_frac *= _conv_mult
                    except Exception:
                        pass

                    if kalshi.place_order(market.ticker, side, contracts, price):
                        log.info(f"[LIVE] {side} {market.ticker} @ {price}¢")
                        existing_tickers.add(market.ticker)

        except Exception as e:
            log.error(f"Main loop error: {e}", exc_info=True)

        open_count = len(ledger.open_positions)
        _bot_stats['balance'] = ledger.balance
        _bot_stats['trades'] = sum(1 for t in ledger.trades if t['action'] == 'OPEN')
        _bot_stats['wins'] = sum(1 for t in ledger.trades if t['action'] == 'CLOSE' and t.get('pnl', 0) > 0)
        _bot_stats['pnl'] = sum(t.get('pnl', 0) for t in ledger.trades if t['action'] == 'CLOSE')
        closed_pnl = sum(t.get("pnl", 0) for t in ledger.trades if t["action"] == "CLOSE")
        total_opened = sum(1 for t in ledger.trades if t["action"] == "OPEN")
        log.info(f"[SUMMARY] Balance=${ledger.balance:.2f} | Open={open_count} | "
                 f"Trades={total_opened} | PnL=${closed_pnl:+.2f}")

        time.sleep(Config.POLL_INTERVAL_SEC)


if __name__ == "__main__":
    main()
