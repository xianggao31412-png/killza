#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
═══════════════════════════════════════════════════════════════════
  SOVEREIGN PUT ROLLER · LIVE  v2.5                  BearStudio 出品
═══════════════════════════════════════════════════════════════════
  用法:   双击 RUN.bat   或   python sovereign_put_roller_live.py
          浏览器自动打开  http://127.0.0.1:7788

  你只需输入:
    ① 股票代码(任意美股)          ② 期权 Strike 价位 与 目标到期时间
    ③ 查询起算日(可选,该日SPY收盘价作为滚仓参考价)
    ④ 手动覆盖期权现价(可选,Yahoo盘后报价偏旧时使用)

  其余全部自动抓取 Yahoo Finance:
    SPY现价 / 期权 Bid·Ask·Last / 隐含波动率IV / 成交量·持仓量
    并用 Black-Scholes 补全 Δ Γ Θ Vega λ 等 Greeks。

  ── 防封号限流 ────────────────────────────────────────────────
    · 双引擎容错: yfinance失败自动切原生HTTP接口(cookie/crumb)
    · 任意两次 Yahoo 请求强制间隔 ≥ 2 秒          (串行节流)
    · 60秒滑动窗口内最多 8 次请求,超限直接拒绝     (硬上限)
    · TTL缓存: 现价15s / 期权链30s / 到期日与历史收盘1小时
    · 前端查询按钮自带 10 秒冷却
    → 正常使用一次完整查询仅产生 0~4 次真实请求
  ──────────────────────────────────────────────────────────────
  依赖:  pip install flask yfinance requests  (RUN.bat每次启动自动升级yfinance)
"""
import json
import math
import os
import re
import socket
import sys
import threading
import time
import webbrowser
from urllib.parse import quote
from collections import deque
from datetime import datetime, timedelta, timezone

import requests
import yfinance as yf
from flask import Flask, jsonify, request

# ════════════ 可调常量(策略参数) ════════════
PORT = int(os.environ.get("PORT", 7788))   # 云端部署时自动读取平台注入端口
RISK_FREE         = 0.04     # 无风险利率(年化)
DIV_YIELD         = 0.012    # 默认股息率(指数ETF≈1.2%; 个股可在页面可选参数覆盖)
DROP_STEP         = 0.025    # 滚仓触发跌幅: 每跌2.5%
IV_BUMP_PER_STEP  = 0.005    # 每跌一级,假设该strike的IV上升0.5个vol点
LADDER_STEPS      = 12       # 收益阶梯计算的级数
DELTA_LO, DELTA_HI = 0.40, 0.45   # 换仓目标|Δ|区间

# ════════════ 波动预警阈值(可按个人风格调整) ════════════
DELTA_ROLL_HI = 0.50   # |Δ|≥0.50: 过高·已偏实值 → 向下转仓落袋
DELTA_WARN_LO = 0.30   # |Δ|<0.30: 过低·弹性流失 → 向上转仓或减筹码
IV_HI         = 0.28   # LEAPS IV≥28%: 恐慌定价偏贵 → 收割/新仓减筹码
IV_LO         = 0.14   # LEAPS IV<14%: 平静期便宜 → 适合建仓加仓
LAM_LO        = 4.0    # λ<4: 弹性不足以支撑16%/滚目标 → 换更虚值
LAM_HI        = 9.0    # λ>9: 过度杠杆彩票化 → 降杠杆或减筹码
IV_LO_STK, IV_HI_STK = 0.22, 0.55      # 个股IV宽带(粗略): 个股LEAPS差异大
INDEX_ETFS = {"SPY", "QQQ", "IWM", "DIA", "VOO", "IVV", "VTI",
              "EFA", "EEM", "XLK", "XLF"}   # 用指数ETF常态带的代码集
IV_FALLBACK       = 0.20     # Yahoo返回脏IV时的兜底值

# ════════════ 限流参数(防封号) ════════════
MIN_INTERVAL      = 2.0      # 任意两次Yahoo请求最小间隔(秒)
MAX_CALLS_PER_MIN = 8        # 60秒滑动窗口内最大请求数
SPOT_TTL          = 15       # 现价缓存(秒)
CHAIN_TTL         = 30       # 期权链缓存(秒)
SLOW_TTL          = 3600     # 到期日列表/历史收盘缓存(秒)

_tickers = {}                          # 按代码缓存Ticker对象,复用会话减少握手


def get_ticker(symbol):
    """按股票代码缓存并复用yfinance Ticker对象。"""
    if symbol not in _tickers:
        _tickers[symbol] = yf.Ticker(symbol)
    return _tickers[symbol]


def norm_symbol(s):
    """清洗股票代码: 去空格转大写; 仅允许字母数字与 . - ^ (如 SPY/TSLA/BRK-B/^SPX)。"""
    s = (s or "").strip().upper()
    if not re.fullmatch(r"[A-Z0-9.\-^]{1,10}", s):
        raise ValueError("股票代码格式无效 — 仅限字母数字与 . - ^, 例如 SPY / QQQ / TSLA / BRK-B")
    return s
STATS  = {"yahoo_calls": 0, "cache_hits": 0}   # 单用户本地工具,按次重置


class RateLimitError(Exception):
    """限流异常:携带建议等待秒数,前端据此提示用户。"""
    def __init__(self, retry_after):
        super().__init__("rate limited")
        self.retry_after = retry_after


class YahooLimiter:
    """
    全局限流器 —— 防止过度抓取被Yahoo封禁的核心闸门。
    规则① 串行节流: 任意两次请求最小间隔 MIN_INTERVAL 秒(不足则sleep补齐);
    规则② 硬性上限: 60秒滑动窗口内最多 MAX_CALLS_PER_MIN 次,
           超限不排队、不轰炸,直接抛 RateLimitError 让前端等待。
    """
    def __init__(self):
        self._lock = threading.Lock()
        self._stamps = deque()       # 最近60秒内每次请求的时间戳
        self._last = 0.0

    def acquire(self):
        with self._lock:
            now = time.time()
            while self._stamps and now - self._stamps[0] > 60:
                self._stamps.popleft()
            if len(self._stamps) >= MAX_CALLS_PER_MIN:
                raise RateLimitError(int(61 - (now - self._stamps[0])))
            wait = self._last + MIN_INTERVAL - now
            if wait > 0:
                time.sleep(wait)
            self._last = time.time()
            self._stamps.append(self._last)

    def remaining(self):
        """返回当前60秒窗口内剩余可用请求配额(供前端展示)。"""
        with self._lock:
            now = time.time()
            while self._stamps and now - self._stamps[0] > 60:
                self._stamps.popleft()
            return MAX_CALLS_PER_MIN - len(self._stamps)


LIMITER = YahooLimiter()

_cache = {}
_cache_lock = threading.Lock()


def cached(key, ttl, producer):
    """
    TTL缓存 —— 限流的第二道防线。
    key命中且未过期 → 直接返回缓存(计一次cache_hit, 零网络请求);
    否则调用 producer() 真实抓取并写入缓存。
    """
    with _cache_lock:
        hit = _cache.get(key)
        if hit and time.time() - hit[0] < ttl:
            STATS["cache_hits"] += 1
            return hit[1]
    val = producer()
    with _cache_lock:
        _cache[key] = (time.time(), val)
    return val


def yahoo_call(fn):
    """所有真实Yahoo请求的唯一入口: 先过限流器闸门,再执行并计数。"""
    LIMITER.acquire()
    STATS["yahoo_calls"] += 1
    return fn()


# ════════════ 数学核心 ════════════
_SQRT2PI = math.sqrt(2 * math.pi)


def norm_pdf(x):
    """标准正态分布密度函数 φ(x)。"""
    return math.exp(-x * x / 2) / _SQRT2PI


def norm_cdf(x):
    """标准正态累计分布 N(x), Zelen–Severo多项式近似(误差<7.5e-8)。"""
    t = 1 / (1 + 0.2316419 * abs(x))
    p = norm_pdf(x) * t * (0.31938153 + t * (-0.356563782 + t * (
        1.781477937 + t * (-1.821255978 + t * 1.330274429))))
    return 1 - p if x >= 0 else p


def bs_put(S, K, T, r, q, sig):
    """
    Black-Scholes 欧式Put定价与全套Greeks。
    入参: S现价 K行权价 T年化剩余时间 r无风险利率 q股息率 sig波动率
    返回: price理论价 | delta(负) | gamma | vega(每1个vol点) | theta(每日)
    """
    v = sig * math.sqrt(T)
    d1 = (math.log(S / K) + (r - q + sig * sig / 2) * T) / v
    d2 = d1 - v
    eq, er = math.exp(-q * T), math.exp(-r * T)
    price = K * er * norm_cdf(-d2) - S * eq * norm_cdf(-d1)
    delta = eq * (norm_cdf(d1) - 1)
    gamma = eq * norm_pdf(d1) / (S * v)
    vega = S * eq * norm_pdf(d1) * math.sqrt(T) / 100
    theta = (-S * eq * norm_pdf(d1) * sig / (2 * math.sqrt(T))
             - r * K * er * norm_cdf(-d2)
             + q * S * eq * norm_cdf(-d1)) / 365.0
    return {"price": price, "delta": delta, "gamma": gamma,
            "vega": vega, "theta": theta}


def sanitize_iv(iv):
    """
    清洗Yahoo返回的隐含波动率。
    LEAPS深度合约上Yahoo偶尔返回 0 / 1e-5 / >300% 等脏数据;
    超出(3%, 200%)合理区间 → 视为脏数据,返回(兜底值, True标记)。
    """
    try:
        iv = float(iv)
    except (TypeError, ValueError):
        return IV_FALLBACK, True
    if math.isnan(iv) or not (0.03 < iv < 2.0):
        return IV_FALLBACK, True
    return iv, False


# ════════════ Yahoo 数据抓取层(双引擎容错) ════════════
ENGINE_LOG = {}   # 记录每类数据最终由哪个引擎取得: yfinance / raw


class DataSourceError(Exception):
    """两个引擎都失败时抛出, 携带逐引擎错误明细供前端展示。"""
    def __init__(self, label, errors):
        super().__init__(label + ": " + " | ".join(errors))
        self.label, self.errors = label, errors


class RawYahoo:
    """
    备用引擎 —— 完全不依赖yfinance, 直接请求Yahoo公开接口, 支持任意股票代码。
    · chart接口(现价/历史K线)无需crumb;
    · options接口需cookie+crumb认证: 先访问fc.yahoo.com种cookie
      (返回404属正常), 再GET getcrumb取crumb, 401/403时自动重新认证一次。
    带浏览器User-Agent; 空响应/429均转为明确中文错误。
    """
    def __init__(self):
        self.s = requests.Session()
        self.s.headers.update({
            "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                           "AppleWebKit/537.36 (KHTML, like Gecko) "
                           "Chrome/124.0.0.0 Safari/537.36"),
            "Accept": "application/json,text/plain,*/*"})
        self.crumb = None

    def _auth(self):
        """cookie+crumb认证(仅options接口需要)。"""
        try:
            self.s.get("https://fc.yahoo.com/", timeout=15)
        except requests.RequestException:
            pass
        c = self.s.get("https://query1.finance.yahoo.com/v1/test/getcrumb",
                       timeout=15)
        if c.status_code != 200 or not c.text.strip() or "Too Many" in c.text:
            raise RuntimeError("获取Yahoo crumb失败(网络可能无法访问Yahoo)")
        self.crumb = c.text.strip()

    def _json(self, url, params=None, need_crumb=False):
        """统一GET→JSON: 处理crumb注入、过期重认证、429与空响应。"""
        if need_crumb:
            if not self.crumb:
                self._auth()
            params = dict(params or {})
            params["crumb"] = self.crumb
        r = self.s.get(url, params=params, timeout=15)
        if r.status_code in (401, 403) and need_crumb:
            self.crumb = None
            self._auth()
            params["crumb"] = self.crumb
            r = self.s.get(url, params=params, timeout=15)
        if r.status_code == 429:
            raise RuntimeError("Yahoo返回429(请求过多), 请等1-2分钟")
        r.raise_for_status()
        if not r.text.strip():
            raise RuntimeError("Yahoo返回空响应(可能被临时封锁)")
        return r.json()

    def _chart(self, symbol, params):
        j = self._json("https://query1.finance.yahoo.com/v8/finance/chart/"
                       + quote(symbol, safe=""), params)
        return j["chart"]["result"][0]

    def spot(self, symbol):
        """现价+前收盘(chart meta, 无需crumb)。"""
        m = self._chart(symbol, {"range": "1d", "interval": "1d"})["meta"]
        prev = (m.get("chartPreviousClose") or m.get("previousClose")
                or m["regularMarketPrice"])
        return {"last": float(m["regularMarketPrice"]), "prev": float(prev)}

    def history_close(self, symbol, date_str):
        """起算日收盘价(chart K线, 无需crumb): 取±窗口内最贴近的交易日。"""
        st = datetime.strptime(date_str, "%Y-%m-%d").replace(tzinfo=timezone.utc)
        res = self._chart(symbol, {"period1": int((st - timedelta(days=10)).timestamp()),
                                   "period2": int((st + timedelta(days=7)).timestamp()),
                                   "interval": "1d"})
        closes = (res.get("indicators", {}).get("quote") or [{}])[0].get("close") or []
        candles = [(datetime.fromtimestamp(t, tz=timezone.utc).date(), c)
                   for t, c in zip(res.get("timestamp") or [], closes)]
        return _pick_close(candles, st.date())

    def _options(self, symbol, date_unix=None):
        params = {"date": date_unix} if date_unix else {}
        j = self._json("https://query2.finance.yahoo.com/v7/finance/options/"
                       + quote(symbol, safe=""), params, need_crumb=True)
        return j["optionChain"]["result"][0]

    def expiries(self, symbol):
        return tuple(datetime.fromtimestamp(d, tz=timezone.utc).strftime("%Y-%m-%d")
                     for d in self._options(symbol)["expirationDates"])

    def chain_puts(self, symbol, expiry):
        du = int(datetime.strptime(expiry, "%Y-%m-%d")
                 .replace(tzinfo=timezone.utc).timestamp())
        puts = self._options(symbol, du)["options"][0]["puts"]
        num = lambda p, k: float(p.get(k) or 0)
        return [{"strike": num(p, "strike"), "bid": num(p, "bid"),
                 "ask": num(p, "ask"), "lastPrice": num(p, "lastPrice"),
                 "impliedVolatility": num(p, "impliedVolatility"),
                 "volume": int(p.get("volume") or 0),
                 "openInterest": int(p.get("openInterest") or 0)} for p in puts]


RAW = RawYahoo()


def with_fallback(label, yf_fn, raw_fn):
    """
    双引擎容错: 先走yfinance, 失败退避1.5秒后切原生备用引擎。
    每次真实尝试都经过限流闸门计数; 'Expecting value'空响应被
    识别并标注; 业务性ValueError(如日期无数据)直接上抛不重试;
    两路都失败抛DataSourceError(携带逐引擎原因)。
    """
    errors = []
    for name, fn in (("yfinance", yf_fn), ("raw", raw_fn)):
        try:
            out = yahoo_call(fn)
            ENGINE_LOG[label] = name
            return out
        except RateLimitError:
            raise
        except json.JSONDecodeError as e:
            errors.append(f"{name}: Yahoo空响应({e})")
        except ValueError:
            raise
        except Exception as e:
            errors.append(f"{name}: {type(e).__name__}: {e}")
        if name == "yfinance":
            time.sleep(1.5)
    raise DataSourceError(label, errors)


def _pick_close(candles, want):
    """
    智能取参考收盘价: candles为[(日期,收盘)]升序。
    优先取请求日当天或之后第一个收盘(周末/节假日自动顺延);
    若请求日太新尚无收盘(如选了今天且未收盘), 自动回退其前最近一个收盘价。
    返回的used字段标明实际取用的日期, 前端会如实显示。
    """
    clean = [(d, float(c)) for d, c in candles
             if c is not None and c == c]          # 过滤None与NaN
    if not clean:
        raise RuntimeError("窗口内无任何SPY K线数据")
    after = [x for x in clean if x[0] >= want]
    d, px = after[0] if after else clean[-1]
    return {"close": px, "used": d.strftime("%Y-%m-%d")}


def fetch_spot(symbol):
    """标的现价与前收盘(双引擎), 15秒缓存(按代码)。"""
    def yf_hit():
        fi = get_ticker(symbol).fast_info
        return {"last": float(fi.last_price), "prev": float(fi.previous_close)}
    return cached(("spot", symbol), SPOT_TTL,
                  lambda: with_fallback("现价", yf_hit, lambda: RAW.spot(symbol)))


def fetch_expiries(symbol):
    """标的全部期权到期日(双引擎), 1小时缓存(按代码)。"""
    def yf_hit():
        ex = tuple(get_ticker(symbol).options)
        if not ex:
            raise RuntimeError("yfinance返回空到期日列表(该代码可能没有期权)")
        return ex
    return cached(("expiries", symbol), SLOW_TTL,
                  lambda: with_fallback("到期日", yf_hit,
                                        lambda: RAW.expiries(symbol)))


def fetch_chain(symbol, expiry):
    """指定到期日整条Put链(双引擎), 30秒缓存(按代码+到期日)。"""
    def yf_hit():
        puts = get_ticker(symbol).option_chain(expiry).puts
        cols = ["strike", "bid", "ask", "lastPrice",
                "impliedVolatility", "volume", "openInterest"]
        rec = puts[cols].fillna(0).to_dict("records")
        if not rec:
            raise RuntimeError("yfinance返回空期权链")
        return rec
    return cached(("chain", symbol, expiry), CHAIN_TTL,
                  lambda: with_fallback("期权链", yf_hit,
                                        lambda: RAW.chain_puts(symbol, expiry)))


def fetch_ref_close(symbol, date_str):
    """
    起算日标的收盘价(双引擎), 1小时缓存(按代码+日期)。
    窗口[起算日-10天, +7天]: 周末/节假日自动顺延, 选今天未收盘则回退最近收盘;
    yfinance空表视为引擎故障→自动切raw引擎。
    """
    def yf_hit():
        start = datetime.strptime(date_str, "%Y-%m-%d")
        hist = get_ticker(symbol).history(
            start=(start - timedelta(days=10)).strftime("%Y-%m-%d"),
            end=(start + timedelta(days=7)).strftime("%Y-%m-%d"),
            interval="1d", auto_adjust=False)
        if hist.empty:
            raise RuntimeError("yfinance返回空历史数据")
        candles = [(ts.date(), c) for ts, c in hist["Close"].items()]
        return _pick_close(candles, start.date())
    return cached(("ref", symbol, date_str), SLOW_TTL,
                  lambda: with_fallback("历史收盘", yf_hit,
                                        lambda: RAW.history_close(symbol, date_str)))

# ════════════ 分析层 ════════════
def year_frac(expiry):
    """到期日16:00(美东近似)距现在的年化时间T。"""
    exp = datetime.strptime(expiry, "%Y-%m-%d") + timedelta(hours=16)
    return max(1 / 365.25, (exp - datetime.now()).total_seconds() / 31557600)


def pick_row(chain, strike):
    """在期权链中找用户的strike: 精确命中或就近匹配(返回行,是否近似)。"""
    exact = [r for r in chain if abs(r["strike"] - strike) < 1e-6]
    if exact:
        return exact[0], False
    row = min(chain, key=lambda r: abs(r["strike"] - strike))
    return row, True


def mid_price(row):
    """市场价取法: bid/ask均>0取中间价, 否则退lastPrice, 再否则None。"""
    if row["bid"] > 0 and row["ask"] > 0:
        return (row["bid"] + row["ask"]) / 2, "中间价"
    if row["lastPrice"] > 0:
        return float(row["lastPrice"]), "最新成交"
    return None, None


def build_ladder(spot, K, T, iv, anchor, base_price, q=DIV_YIELD):
    """
    收益阶梯 —— 回答"每跌2.5%,这个价位的期权赚多少%"。
    第i级: SPY_i = 现价×(1−2.5%)^i, IV_i = IV+0.5vol点×i (sticky-strike),
    理论价×锚定系数anchor → 锚定价, 使第0级恰等于真实市价。
    本级收益% = 较上一级涨幅;  累计收益% = 较当前市价涨幅。
    """
    rows, prev = [], None
    for i in range(LADDER_STEPS + 1):
        s = spot * (1 - DROP_STEP) ** i
        px = bs_put(s, K, T, RISK_FREE, q,
                    iv + IV_BUMP_PER_STEP * i)["price"] * anchor
        rows.append({
            "level": i,
            "spy": round(s, 2),
            "cum_drop": round((1 - (1 - DROP_STEP) ** i) * 100, 2),
            "px": round(px, 2),
            "step_gain": None if prev is None else round((px / prev - 1) * 100, 1),
            "cum_gain": round((px / base_price - 1) * 100, 1),
        })
        prev = px
    return rows


def scan_roll(chain, spot, T, q=DIV_YIELD):
    """
    在真实期权链上扫描换仓候选(strike取整5档, 0.85~1.06×现价):
    · 用各合约自身的Yahoo IV算|Δ|与λ弹性;
    · 推荐 = |Δ|落在[0.40,0.45]且最接近中点者(无则取最近);
    · 同时标出 SPY×0.95 对照档;
    · "跌2.5%预计%"按该合约自身锚定后的重定价计算。
    """
    lo, hi = spot * 0.85, spot * 1.06
    mid_t = (DELTA_LO + DELTA_HI) / 2
    cands = []
    for r in sorted(chain, key=lambda x: x["strike"]):
        k = r["strike"]
        if not (lo <= k <= hi):
            continue
        iv, dirty = sanitize_iv(r["impliedVolatility"])
        g = bs_put(spot, k, T, RISK_FREE, q, iv)
        mkt, src = mid_price(r)
        base = mkt if mkt else g["price"]
        anchor = (mkt / g["price"]) if (mkt and g["price"] > 0.05) else 1.0
        nxt = bs_put(spot * (1 - DROP_STEP), k, T, RISK_FREE, q,
                     iv + IV_BUMP_PER_STEP)["price"] * anchor
        cands.append({
            "strike": k, "bid": round(r["bid"], 2), "ask": round(r["ask"], 2),
            "mid": round(base, 2), "iv": round(iv * 100, 1), "iv_dirty": dirty,
            "delta": round(abs(g["delta"]), 3),
            "lam": round(abs(g["delta"]) * spot / base, 2) if base > 0.05 else 0,
            "gain": round((nxt / base - 1) * 100, 1) if base > 0.05 else 0,
            "oi": int(r["openInterest"]),
        })
    if not cands:
        return [], None, None
    in_band = [c for c in cands if DELTA_LO <= c["delta"] <= DELTA_HI]
    pool = in_band if in_band else cands
    rec = min(pool, key=lambda c: abs(c["delta"] - mid_t))["strike"]
    k95 = min(cands, key=lambda c: abs(c["strike"] - spot * 0.95))["strike"]
    if len(cands) > 22:                 # 个股链strike很密时抽稀展示(保留推荐与0.95档)
        step = max(1, len(cands) // 20)
        keep = {rec, k95}
        cands = [c for i, c in enumerate(cands)
                 if i % step == 0 or c["strike"] in keep]
    return cands, rec, k95


def advise(iv, delta, lam, iv_dirty=False, iv_lo=IV_LO, iv_hi=IV_HI, band="指数ETF常态带"):
    """
    波动预警引擎: 对 IV / |Δ| / λ 三项核心指标分级评估并给出操作建议。
    level: ok=绿·正常持有 | warn=黄·关注准备 | act=红·应转仓或调整筹码
    全部阈值为.py顶部常量, 可自行修改。
    """
    A = []
    add = lambda **k: A.append(k)
    # ── |Δ| ──
    if delta >= DELTA_ROLL_HI:
        add(metric="|Δ|", value=f"{delta:.3f}", level="act", title="过高 · 已偏实值",
            advice=f"实值化使单位资金弹性下降、浮盈坐实风险升高 → 向下转仓: 卖出当前strike, "
                   f"换回 |Δ| {DELTA_LO:.2f}–{DELTA_HI:.2f}(见④金色推荐), 落袋本轮涨幅重置弹性。")
    elif delta > DELTA_HI:
        add(metric="|Δ|", value=f"{delta:.3f}", level="warn", title="接近上限",
            advice=f"已越过目标区上限 {DELTA_HI:.2f}, 距 {DELTA_ROLL_HI:.2f} 转仓线不远 — "
                   f"提前规划向下转仓的目标strike, 等价格或Delta触发即执行。")
    elif delta >= DELTA_LO:
        add(metric="|Δ|", value=f"{delta:.3f}", level="ok", title="目标区间内",
            advice=f"处于 {DELTA_LO:.2f}–{DELTA_HI:.2f} 策略区, 弹性与稳定兼顾 — 持有, "
                   f"等待跌2.5%或Delta越界触发下一次滚仓。")
    elif delta >= DELTA_WARN_LO:
        add(metric="|Δ|", value=f"{delta:.3f}", level="warn", title="低于目标区",
            advice=f"反弹或时间流逝在侵蚀Delta — 保持关注; 跌破 {DELTA_WARN_LO:.2f} "
                   f"应向上转仓(roll up)恢复弹性。")
    else:
        add(metric="|Δ|", value=f"{delta:.3f}", level="act", title="过低 · 弹性流失",
            advice="期权已深度虚值化, Γ/Δ弹性不足且θ损耗占比攀升 → 向上转仓恢复 "
                   "0.40–0.45, 或减少筹码控制时间损耗。")
    # ── IV ──
    if iv >= iv_hi:
        add(metric="IV", value=f"{iv*100:.1f}%", level="act", title="过高 · 恐慌定价",
            advice=f"高于{band}上限{iv_hi*100:.0f}%, 期权偏贵: 持仓有浮盈者正是转仓收割"
                   f"时点(高IV卖出更值钱); 新开/加仓性价比低, 应减少筹码或等IV回落再补。")
    elif iv <= iv_lo:
        add(metric="IV", value=f"{iv*100:.1f}%", level="warn", title="过低 · 平静便宜",
            advice=f"低于{band}下限{iv_lo*100:.0f}%, 权利金处于便宜区, 建仓/加仓性价比高; "
                   f"但暴跌时的Vega增益预期需相应调低, 已有持仓无需动作。")
    else:
        add(metric="IV", value=f"{iv*100:.1f}%", level="ok", title="正常区间",
            advice=f"处于{band} {iv_lo*100:.0f}–{iv_hi*100:.0f}% — 定价中性, "
                   f"维持既定滚仓纪律即可。")
    if iv_dirty:
        add(metric="IV", value="兜底20%", level="warn", title="数据清洗提示",
            advice="Yahoo对该合约返回异常IV, 已用20%兜底参与计算 — 本页Greeks仅供参考, "
                   "下单前以券商IV为准。")
    # ── λ ──
    if lam >= LAM_HI:
        add(metric="λ", value=f"{lam:.2f}×", level="act", title="过高 · 彩票化",
            advice="深度虚值高杠杆: θ损耗与滚仓摩擦占比大、胜率结构变差 → "
                   "换更接近现价的strike降杠杆, 或减少筹码压缩风险敞口。")
    elif lam < LAM_LO:
        add(metric="λ", value=f"{lam:.2f}×", level="act", title="过低 · 弹性不足",
            advice=f"跌2.5%基础收益仅≈{lam*2.5:.1f}%, 难以支撑16%/滚目标 → "
                   f"向更虚值strike转仓提升λ, 或接受较低单滚收益。")
    else:
        add(metric="λ", value=f"{lam:.2f}×", level="ok", title="符合策略区",
            advice=f"跌2.5%基础收益≈{lam*2.5:.1f}%, 叠加Γ/Vega增益可逼近16%目标 — 维持。")
    return A


def analyze(symbol, strike, expiry, ref_date, override_price, q=DIV_YIELD):
    """
    主编排: 校验到期日 → 抓现价/期权链/参考收盘 → 清洗IV →
    Greeks → 锚定 → 收益阶梯 → 滚仓判定 → 换仓扫描 → 打包JSON。
    """
    if ref_date:
        try:
            rd = datetime.strptime(ref_date, "%Y-%m-%d").date()
        except ValueError:
            raise ValueError("查询起算日格式应为 YYYY-MM-DD")
        if rd > datetime.now().date():
            raise ValueError("查询起算日不能晚于今天 — 它代表你上次滚仓/买入的那一天")

    expiries = fetch_expiries(symbol)
    if expiry not in expiries:
        near = [e for e in expiries if e[:4] >= "2027"] or list(expiries)[-12:]
        raise ValueError(f"{symbol} 无此到期日。可选到期日: " + ", ".join(near[:12]))

    sp = fetch_spot(symbol)
    spot, prev = sp["last"], sp["prev"]
    chain = fetch_chain(symbol, expiry)
    row, approx = pick_row(chain, strike)
    K = row["strike"]
    T = year_frac(expiry)

    iv, iv_dirty = sanitize_iv(row["impliedVolatility"])
    g = bs_put(spot, K, T, RISK_FREE, q, iv)

    mkt, mkt_src = mid_price(row)
    if override_price and override_price > 0:
        mkt, mkt_src = float(override_price), "手动覆盖"
    base = mkt if mkt else g["price"]
    anchor = (mkt / g["price"]) if (mkt and g["price"] > 0.05) else 1.0
    lam = round(abs(g["delta"]) * spot / base, 2) if base > 0.05 else 0.0

    ladder = build_ladder(spot, K, T, iv, anchor, base, q)
    cands, rec, k95 = scan_roll(chain, spot, T, q)

    ref = None
    if ref_date:
        rc = fetch_ref_close(symbol, ref_date)
        drop = (rc["close"] - spot) / rc["close"]
        ref = {"date": rc["used"], "close": round(rc["close"], 2),
               "drop": round(drop * 100, 2),
               "fired": drop >= DROP_STEP - 1e-9,
               "trig_px": round(rc["close"] * (1 - DROP_STEP), 2),
               "need": round(max(0.0, (spot - rc["close"] * (1 - DROP_STEP)) / spot * 100), 2)}

    if symbol in INDEX_ETFS:
        ivlo, ivhi, band = IV_LO, IV_HI, "指数ETF常态带"
    else:
        ivlo, ivhi, band = IV_LO_STK, IV_HI_STK, "个股宽带(粗略)"

    return {
        "ts": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        "symbol": symbol,
        "spot": round(spot, 2), "day_chg": round((spot / prev - 1) * 100, 2),
        "strike": K, "approx": approx, "expiry": expiry,
        "days": int(T * 365.25), "T": round(T, 3),
        "bid": round(row["bid"], 2), "ask": round(row["ask"], 2),
        "last": round(row["lastPrice"], 2),
        "mkt": round(mkt, 2) if mkt else None, "mkt_src": mkt_src,
        "iv": round(iv * 100, 2), "iv_dirty": iv_dirty,
        "theo": round(g["price"], 2), "anchor": round(anchor, 3),
        "delta": round(abs(g["delta"]), 3), "gamma": round(g["gamma"], 5),
        "vega": round(g["vega"], 2), "theta": round(g["theta"], 3),
        "lam": lam,
        "alerts": advise(iv, abs(g["delta"]), lam, iv_dirty, ivlo, ivhi, band),
        "oi": int(row["openInterest"]), "vol": int(row["volume"]),
        "ladder": ladder, "cands": cands, "rec": rec, "k95": k95, "ref": ref,
        "params": {"drop_step": DROP_STEP * 100, "iv_bump": IV_BUMP_PER_STEP * 100,
                   "r": RISK_FREE * 100, "q": round(q * 100, 2),
                   "d_lo": DELTA_LO, "d_hi": DELTA_HI},
        "stats": {"yahoo_calls": STATS["yahoo_calls"],
                  "cache_hits": STATS["cache_hits"],
                  "engines": dict(ENGINE_LOG),
                  "quota_left": LIMITER.remaining()},
    }


# ════════════ Flask 接口层 ════════════
app = Flask(__name__)


@app.route("/api/analyze")
def api_analyze():
    """HTTP主接口: 接收4个用户输入, 返回完整分析JSON; 统一异常处理。"""
    STATS["yahoo_calls"] = 0
    STATS["cache_hits"] = 0
    try:
        symbol = norm_symbol(request.args.get("symbol", "SPY"))
        strike = float(request.args.get("strike", "0"))
        expiry = request.args.get("expiry", "").strip()
        ref_date = request.args.get("ref", "").strip() or None
        op = request.args.get("override", "").strip()
        override = float(op) if op else None
        qs = request.args.get("q", "").strip()
        q = (float(qs) / 100) if qs else DIV_YIELD
        if strike <= 0 or not expiry:
            return jsonify({"error": "请填写 Strike 与到期日。"}), 400
        return jsonify(analyze(symbol, strike, expiry, ref_date, override, q))
    except RateLimitError as e:
        return jsonify({"error": f"已达限流上限(每分钟{MAX_CALLS_PER_MIN}次), "
                                 f"请 {e.retry_after} 秒后再试 —— 这是防封号保护。",
                        "retry_after": e.retry_after}), 429
    except DataSourceError as e:
        return jsonify({"error":
            "Yahoo数据抓取失败(双引擎均被拒): " + " ; ".join(e.errors)
            + " 。修复顺序 ① 命令行运行: pip install --upgrade yfinance "
              "(Yahoo接口常变, 旧版典型报'Expecting value: line 1 column 1'空响应) "
              "② 等1-2分钟再试(Yahoo临时限流) "
              "③ 确认浏览器能打开 finance.yahoo.com(中国大陆网络/部分VPN不可达需换网络)。"
              "也可点[🩺 诊断]逐层定位。"}), 502
    except json.JSONDecodeError:
        return jsonify({"error":
            "Yahoo返回空响应('Expecting value'…)。请先升级: "
            "pip install --upgrade yfinance; 仍失败则点[🩺 诊断]查看是哪一层出的问题。"}), 502
    except ValueError as e:
        return jsonify({"error": str(e)}), 400
    except Exception as e:
        return jsonify({"error": f"抓取失败: {type(e).__name__}: {e}"}), 502


@app.route("/api/expiries")
def api_expiries():
    """两步流程·第一步: 按用户目标时间返回最近的4个真实可选到期日。
    仅消耗0~1次真实请求(到期日列表有1小时缓存)。"""
    STATS["yahoo_calls"] = 0
    STATS["cache_hits"] = 0
    try:
        symbol = norm_symbol(request.args.get("symbol", "SPY"))
        want = datetime.strptime(request.args.get("date", "").strip(),
                                 "%Y-%m-%d").date()
        today = datetime.now().date()
        items = []
        for e in fetch_expiries(symbol):
            ed = datetime.strptime(e, "%Y-%m-%d").date()
            if ed <= today:
                continue
            items.append({"expiry": e, "days": (ed - today).days,
                          "dist": abs((ed - want).days)})
        items.sort(key=lambda x: x["dist"])
        pick = sorted(items[:4], key=lambda x: x["expiry"])
        for p in pick:
            p["leaps"] = p["days"] >= 365
            p.pop("dist")
        return jsonify({"symbol": symbol, "target": str(want), "choices": pick,
                        "stats": {"yahoo_calls": STATS["yahoo_calls"],
                                  "cache_hits": STATS["cache_hits"],
                                  "quota_left": LIMITER.remaining()}})
    except RateLimitError as e:
        return jsonify({"error": f"已达限流上限, 请 {e.retry_after} 秒后再试。",
                        "retry_after": e.retry_after}), 429
    except DataSourceError as e:
        return jsonify({"error": "到期日列表抓取失败: " + " ; ".join(e.errors)}), 502
    except ValueError as e:
        msg = str(e) if "代码" in str(e) else "请填写有效的目标到期时间(YYYY-MM-DD)。"
        return jsonify({"error": msg}), 400
    except Exception as e:
        return jsonify({"error": f"抓取失败: {type(e).__name__}: {e}"}), 502


@app.route("/api/diag")
def api_diag():
    """🩺 数据链路自检: 清缓存后逐层真实测试四类抓取, 标出所用引擎与失败原因。"""
    STATS["yahoo_calls"] = 0
    STATS["cache_hits"] = 0
    with _cache_lock:
        _cache.clear()
    import sys
    out = {"python": sys.version.split()[0],
           "yfinance": getattr(yf, "__version__", "?"), "steps": []}

    def step(name, label, fn, brief):
        try:
            v = fn()
            out["steps"].append({"name": name, "ok": True,
                                 "engine": ENGINE_LOG.get(label, ""),
                                 "info": brief(v)})
            return v
        except Exception as e:
            out["steps"].append({"name": name, "ok": False, "engine": "",
                                 "info": f"{type(e).__name__}: {e}"})
            return None

    step("SPY现价(基准)", "现价", lambda: fetch_spot("SPY"),
         lambda v: f"{v['last']:.2f}")
    ex = step("到期日列表", "到期日", lambda: fetch_expiries("SPY"),
              lambda v: f"共{len(v)}个 · 最远 {v[-1]}")
    if ex:
        leaps = next((d for d in ex if d >= "2027-06-01"), ex[-1])
        step(f"期权链 {leaps}", "期权链", lambda: fetch_chain("SPY", leaps),
             lambda v: f"{len(v)} 个strike")
    d30 = (datetime.now() - timedelta(days=30)).strftime("%Y-%m-%d")
    step(f"历史收盘 {d30}", "历史收盘", lambda: fetch_ref_close("SPY", d30),
         lambda v: f"{v['close']:.2f} (取 {v['used']})")
    out["calls"] = STATS["yahoo_calls"]
    out["quota_left"] = LIMITER.remaining()
    return jsonify(out)


# ════════════ 内嵌前端 UI ════════════
HTML = r"""<!DOCTYPE html>
<html lang="zh-CN"><head><meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1.0">
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-status-bar-style" content="black-translucent">
<meta name="apple-mobile-web-app-title" content="Put Roller">
<meta name="theme-color" content="#14141f">
<title>Sovereign Put Roller · LIVE</title>
<style>
:root{--base:#14141f;--panel:#1b1b2a;--ink:#cdd6f4;--sub:#8b91ad;--faint:#5c617a;
--line:#2c2c40;--line2:#3a3a52;--roll:#f38ba8;--hold:#a6e3a1;--gold:#f9e2af;
--blue:#89b4fa;--mauve:#cba6f7;--mono:"IBM Plex Mono",ui-monospace,Consolas,monospace;
--disp:"Space Grotesk",system-ui,sans-serif}
*{box-sizing:border-box;margin:0;padding:0}
body{background:var(--base);color:var(--ink);font-family:var(--disp);font-size:14px;line-height:1.55;padding:26px 14px 70px}
.wrap{max-width:1280px;margin:0 auto}
header{border-bottom:1px solid var(--line2);padding-bottom:16px;margin-bottom:18px}
.brand{font-family:var(--mono);font-size:10px;letter-spacing:.32em;color:var(--faint);text-transform:uppercase}
h1{font-size:clamp(24px,4.5vw,34px);font-weight:700}
h1 .cn{color:var(--sub);font-weight:400;font-size:.55em;margin-left:.5em;letter-spacing:.1em}
.tagline{font-family:var(--mono);font-size:11px;color:var(--sub);margin-top:5px}
.tagline b{color:var(--roll)}
.panel{background:var(--panel);border:1px solid var(--line);border-radius:6px;padding:16px 16px 18px;margin-bottom:14px}
.panel h2{font-size:11.5px;font-family:var(--mono);letter-spacing:.22em;color:var(--sub);text-transform:uppercase;margin-bottom:12px;display:flex;align-items:center;gap:10px}
.panel h2::after{content:"";flex:1;height:1px;background:var(--line)}
.panel h2 .step{color:var(--gold);font-size:14px}
.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(165px,1fr));gap:11px 13px}
.field label{display:block;font-size:10.5px;font-family:var(--mono);color:var(--sub);margin-bottom:4px;letter-spacing:.06em}
.field label em{color:var(--faint);font-style:normal}
.field input{width:100%;background:var(--base);border:1px solid var(--line2);border-radius:4px;color:var(--ink);font-family:var(--mono);font-size:14px;padding:7px 9px;outline:none}
.field input:focus{border-color:var(--blue)}
.btnrow{display:flex;gap:10px;margin-top:14px;flex-wrap:wrap}
.btnrow button{flex:1;min-width:160px;background:none;border:1px solid var(--gold);color:var(--gold);font-family:var(--mono);font-size:13px;letter-spacing:.15em;padding:11px;border-radius:4px;cursor:pointer}
#go{flex:2}
#diagBtn{border-color:var(--blue);color:var(--blue)}
#go:hover:not(:disabled){background:var(--gold);color:var(--base)}
#diagBtn:hover:not(:disabled){background:var(--blue);color:var(--base)}
.btnrow button:disabled{opacity:.45;cursor:wait}
.chips{display:none;gap:9px;flex-wrap:wrap;margin-top:12px}
.chip{background:var(--base);border:1px solid var(--line2);border-radius:5px;padding:8px 14px;cursor:pointer;font-family:var(--mono);font-size:13px;color:var(--ink);text-align:center}
.chip small{display:block;color:var(--faint);font-size:10px;margin-top:3px}
.chip:hover:not(:disabled){border-color:var(--gold)}
.chip.sel{border-color:var(--gold);background:rgba(249,226,175,.12);color:var(--gold)}
.chip .lp{color:var(--mauve);font-size:9px;letter-spacing:.12em;margin-left:5px}
.chip:disabled{opacity:.45;cursor:wait}
.err{display:none;margin-top:10px;color:var(--roll);font-family:var(--mono);font-size:12px}
.banner{border:1px solid var(--line);border-left:6px solid var(--faint);border-radius:6px;background:var(--panel);padding:14px 16px;margin-bottom:14px;display:none}
.banner.roll{border-left-color:var(--roll)} .banner.hold{border-left-color:var(--hold)}
.verdict{display:flex;align-items:baseline;gap:13px;flex-wrap:wrap}
.verdict .word{font-size:30px;font-weight:700}
.banner.roll .word{color:var(--roll)} .banner.hold .word{color:var(--hold)}
.verdict .why{font-family:var(--mono);font-size:12.5px;color:var(--sub)} .verdict .why b{color:var(--ink)}
.kpis{display:grid;grid-template-columns:repeat(auto-fit,minmax(128px,1fr));gap:9px}
.kpi{border:1px solid var(--line);border-radius:5px;padding:8px 11px}
.kpi .k{font-size:9.5px;font-family:var(--mono);color:var(--faint);letter-spacing:.08em}
.kpi .n{font-family:var(--mono);font-size:16.5px;font-weight:600;margin-top:2px}
.kpi .n small{font-size:10.5px;color:var(--sub);font-weight:400}
.n.pos{color:var(--roll)} .n.gold{color:var(--gold)} .n.dim{color:var(--sub)} .n.green{color:var(--hold)}
table{width:100%;border-collapse:collapse;font-family:var(--mono);font-size:12.5px}
th{font-size:9.5px;color:var(--faint);letter-spacing:.1em;text-transform:uppercase;font-weight:500;text-align:right;padding:6px 7px;border-bottom:1px solid var(--line2)}
th:first-child,td:first-child{text-align:left}
td{padding:6px 7px;text-align:right;border-bottom:1px solid var(--line)}
tr.rec td{background:rgba(249,226,175,.07)} tr.rec td:first-child{border-left:3px solid var(--gold)}
tr.r95 td:first-child{border-left:3px dashed var(--mauve)}
tr.lv0 td{color:var(--sub)}
td.hot{color:var(--roll);font-weight:600;background:rgba(243,139,168,.06)}
td .tag{font-size:9px;padding:1px 5px;border-radius:3px;margin-left:5px}
.tag.g{color:var(--base);background:var(--gold)} .tag.m{color:var(--base);background:var(--mauve)}
.tblWrap{overflow-x:auto}
.legend{margin-top:8px;font-family:var(--mono);font-size:10.5px;color:var(--faint)}
details{border:1px dashed var(--line2);border-radius:6px;padding:13px 15px;margin-bottom:14px;color:var(--sub);font-size:12.5px}
summary{cursor:pointer;font-family:var(--mono);font-size:11px;letter-spacing:.15em;color:var(--blue)}
details p{margin-top:7px} details b{color:var(--ink)} details code{color:var(--gold);font-family:var(--mono)}
.statline{font-family:var(--mono);font-size:10.5px;color:var(--faint);text-align:right;margin:-6px 0 12px}
.statline b{color:var(--hold)}
.layout{display:grid;grid-template-columns:minmax(0,1fr) 295px;gap:14px;align-items:start}
.side{position:sticky;top:14px}
@media(max-width:940px){.layout{grid-template-columns:1fr}.side{position:static}}
.def{margin-bottom:11px}
.def b{font-family:var(--mono);font-size:12.5px;color:var(--gold)}
.def p{font-size:11.5px;color:var(--sub);margin-top:3px;line-height:1.55}
.alert{border:1px solid var(--line);border-left:4px solid;border-radius:5px;padding:9px 11px;margin-bottom:9px}
.alert.ok{border-left-color:var(--hold)} .alert.warn{border-left-color:var(--gold)} .alert.act{border-left-color:var(--roll)}
.alert .h{font-family:var(--mono);font-size:12px;display:flex;justify-content:space-between;gap:8px}
.alert.ok .h{color:var(--hold)} .alert.warn .h{color:var(--gold)} .alert.act .h{color:var(--roll)}
.alert p{font-size:11.5px;color:var(--sub);margin-top:4px;line-height:1.55}
.out{display:none}
footer{margin-top:24px;font-family:var(--mono);font-size:10px;color:var(--faint);letter-spacing:.18em;text-align:center}
@media(max-width:560px){.verdict .word{font-size:25px}}
</style></head><body><div class="wrap">

<header>
  <div class="brand">BearStudio · Sovereign Series</div>
  <h1>PUT ROLLER · LIVE<span class="cn">滚仓引擎 实时版</span></h1>
  <div class="tagline">任意美股代码 · Yahoo双引擎容错 · 限流 ≤8次/分 · 本工具中 <b>↓下跌 = 收益</b></div>
</header>

<div class="layout">
<div class="main">

<section class="panel">
  <h2><span class="step">①</span>两步查询 · 输入价位与目标时间 → 点选真实到期日</h2>
  <div class="grid">
    <div class="field"><label>① 股票代码 <em>(任意美股: SPY/QQQ/TSLA…)</em></label><input id="symbol" type="text" value="SPY" maxlength="10" style="text-transform:uppercase"></div>
    <div class="field"><label>② 期权 Strike 价位</label><input id="strike" type="number" step="0.5" value="700"></div>
    <div class="field"><label>③ 目标到期时间 <em>(任意日期·自动匹配)</em></label><input id="target" type="date" value="2028-01-15"></div>
  </div>
  <div class="btnrow">
    <button id="findBtn">🔎 查找可选到期日</button>
    <button id="diagBtn">🩺 诊断数据链路</button>
  </div>
  <div class="chips" id="chips"></div>
  <details style="margin-top:12px">
    <summary>可选参数 — 滚仓参考 / 价格覆盖</summary>
    <div class="grid" style="margin-top:10px">
      <div class="field"><label>查询起算日 <em>(该日SPY收盘作滚仓参考)</em></label><input id="ref" type="date"></div>
      <div class="field"><label>覆盖期权现价 <em>(盘后报价偏旧时)</em></label><input id="override" type="number" step="0.01" placeholder="留空=用Yahoo报价"></div>
      <div class="field"><label>股息率 q% <em>(指数ETF≈1.2 · 多数个股填0)</em></label><input id="divq" type="number" step="0.1" value="1.2"></div>
    </div>
  </details>
  <div class="err" id="err"></div>
</section>

<div class="statline out" id="statline"></div>
<section class="banner" id="banner"></section>

<section class="panel out" id="quotePanel">
  <h2><span class="step">②</span>实时行情与 Greeks <span id="qts" style="color:var(--faint);letter-spacing:.05em"></span></h2>
  <div class="kpis" id="quoteBody"></div>
</section>

<section class="panel out" id="ladderPanel">
  <h2><span class="step">③</span>收益阶梯 · 每跌 2.5% 赚多少 %</h2>
  <div class="tblWrap" id="ladderBody"></div>
  <div class="legend">锚定价 = BS理论价 × (市价/理论价),第0级即当前真实市价 · ★<b style="color:var(--roll)">本级收益%</b> = 较上一级 · 假设每级该strike的IV +0.5vol点(sticky-strike)</div>
</section>

<section class="panel out" id="rollPanel">
  <h2><span class="step">④</span>换仓扫描 · 真实期权链</h2>
  <div class="tblWrap" id="rollBody"></div>
  <div class="legend">■金=|Δ|∈[0.40,0.45]推荐 · ▥紫=SPY×0.95对照 · λ=|Δ|·S/P弹性 · IV带*为Yahoo脏数据已兜底20% · 报价为延时数据</div>
</section>

<section class="panel" id="diagPanel" style="display:none">
  <h2><span class="step">🩺</span>数据链路诊断</h2>
  <div id="diagBody"></div>
</section>

<details class="out" id="docs"><summary>函数与限流策略说明(点开)</summary>
  <p><b>双引擎容错</b> — <code>with_fallback()</code> 先走yfinance,失败退避1.5秒自动切换 <code>RawYahoo</code> 原生备用引擎(自带浏览器UA与cookie/crumb认证,crumb过期自动重认证);两路都被拒才报错并附逐引擎原因与修复建议。"Expecting value: line 1 column 1"即Yahoo空响应的典型信号,通常=旧版yfinance或网络不可达,点🩺诊断可逐层定位。</p>
  <p><b>限流防封号</b> — <code>YahooLimiter.acquire()</code> 双重闸门: 任意两次请求间隔≥2秒;60秒滑动窗口≤8次,超限直接拒绝并提示等待秒数。<code>cached()</code> TTL缓存第二道防线: 现价15s/期权链30s/到期日与历史收盘1h,重复查询零请求。<code>yahoo_call()</code> 是所有真实请求的唯一入口,先过闸门再执行并计数。前端按钮另有10秒冷却。一次完整查询仅0~4次真实请求。</p>
  <p><b>抓取层</b> — <code>norm_symbol()/get_ticker()</code> 代码清洗校验与按代码复用会话; <code>fetch_spot()</code> 标的现价+前收盘; <code>fetch_expiries()</code> 全部到期日(供两步选择与校验); <code>fetch_chain()</code> 整条Put链(bid/ask/last/IV/量/持仓); <code>fetch_ref_close()</code> 起算日标的收盘价作滚仓参考(±10天窗口: 周末/节假日自动顺延, 选今天未收盘自动回退最近收盘, 实际取用日期如实显示)。</p>
  <p><b>数学层</b> — <code>norm_pdf/norm_cdf</code> 正态分布(Zelen–Severo近似); <code>bs_put()</code> Black-Scholes欧式Put: 理论价+Δ+Γ+Vega(每vol点)+Θ(每日); <code>sanitize_iv()</code> 清洗Yahoo脏IV(超出3%~200%即兜底20%并打*)。</p>
  <p><b>分析层</b> — <code>pick_row()</code> 在链上精确/就近匹配你的strike; <code>mid_price()</code> 市场价: bid·ask中间价→last→理论价; 锚定系数=市价/理论价,把BS校准到真实报价; <code>build_ladder()</code> 生成每跌2.5%的收益阶梯(逐级全量重定价,含Δ/Γ/Vega效应); <code>advise()</code> 波动预警引擎:按IV/|Δ|/λ阈值(Δ≥0.50或<0.30、IV带按标的自动切换:指数ETF 14–28%/其他个股 22–55%、λ≥9或<4,顶部常量可调)输出 正常/关注/行动 三级信号与转仓·筹码建议; <code>scan_roll()</code> 在真实链上按各合约自身IV算|Δ|,选[0.40,0.45]推荐档+0.95对照; <code>api_expiries()</code> 两步流程第一步:按目标时间返回最近4个真实到期日; <code>analyze()</code> 总编排; <code>api_analyze()</code> HTTP接口与统一异常处理。</p>
  <p><b>参数</b> — r=4%; 股息率q默认1.2%(指数ETF), 个股请在"可选参数"改为0或实际值; 触发跌幅2.5%、每级IV抬升0.5vol点等均在.py顶部常量区可改。理论模型≠成交价,下单以券商实际报价为准。</p>
</details>

</div><!-- /main -->

<aside class="side">
  <section class="panel">
    <h2><span class="step">ⓘ</span>指标注释</h2>
    <div class="def"><b>IV 隐含波动率</b><p>市场价反推的年化波动预期, 即期权贵贱的温度计。指数ETF(SPY/QQQ等)LEAPS常态带约14–28%, 个股普遍更高且差异大(常见25–60%), 预警阈值按标的类型自动切换。暴跌恐慌时抬升(Put更贵), 平静期回落。</p></div>
    <div class="def"><b>|Δ| Delta</b><p>标的每跌$1, 期权约涨$|Δ|; 也近似到期成实值的概率。本策略目标区 0.40–0.45: 弹性与稳定的平衡点, 越界即触发滚仓纪律。</p></div>
    <div class="def"><b>λ 弹性(杠杆)</b><p>= |Δ|×标的价÷期权价。标的每动1%, 期权约动λ%。跌2.5%×λ即单滚基础收益, 叠加Γ/Vega增益 → 16%目标约需λ 5–6×。</p></div>
  </section>
  <section class="panel">
    <h2><span class="step">⚡</span>波动预警</h2>
    <div id="alertBody"><div class="legend">查询后自动生成 — IV / |Δ| / λ 过高或过低时, 给出转仓或调整筹码的具体建议。</div></div>
  </section>
</aside>
</div><!-- /layout -->

<footer>SOVEREIGN PUT ROLLER LIVE v2.5 · 多标的 · 双引擎 · BEARSTUDIO · LOCALHOST</footer>
</div>

<script>
"use strict";
const $=id=>document.getElementById(id);
const fmt=(x,d=2)=>(x===null||x===undefined||!isFinite(x))?"—":Number(x).toLocaleString("en-US",{minimumFractionDigits:d,maximumFractionDigits:d});
let cooling=false,selExpiry=null;

async function findExp(){ /* 第一步: 按目标时间取最近4个真实到期日 */
  if(cooling)return;
  const err=$("err");err.style.display="none";
  const sym=$("symbol").value.trim().toUpperCase();
  if(!sym||!$("strike").value||!$("target").value){
    err.textContent="⚠ 请先填写 代码 / Strike / 目标到期时间";err.style.display="block";return;}
  const b=$("findBtn");b.disabled=true;b.textContent="🔎 查找中…";
  try{
    const r=await fetch("/api/expiries?symbol="+encodeURIComponent(sym)+"&date="+$("target").value);
    const d=await r.json();
    if(!r.ok)throw new Error(d.error||("HTTP "+r.status));
    const box=$("chips");box.innerHTML="";box.style.display="flex";selExpiry=null;
    d.choices.forEach(c=>{
      const el=document.createElement("button");
      el.className="chip";el.dataset.exp=c.expiry;
      el.innerHTML=`${c.expiry}${c.leaps?'<span class="lp">LEAPS</span>':''}<small>${c.days} 天后到期</small>`;
      el.addEventListener("click",()=>chipPick(el));
      box.appendChild(el);
    });
    if(!d.choices.length){err.textContent="⚠ 目标时间附近没有可选到期日";err.style.display="block";}
    const sl=$("statline");sl.style.display="block";
    sl.innerHTML=`✓ ${d.symbol} 真实到期日已取得 · <b>点选其一</b>即抓取该到期日全部期权信息 · 本分钟剩余配额 <b>${d.stats.quota_left}</b>/8`;
  }catch(e){err.textContent="⚠ "+e.message;err.style.display="block";}
  cooldown(3,b,"🔎 查找可选到期日");  /* 轻量操作短冷却 */
}

function chipPick(el){ /* 点选到期日 → 立即全量分析 */
  if(cooling){const err=$("err");err.textContent="⚠ 冷却中(防封号),几秒后再点";
    err.style.display="block";return;}
  document.querySelectorAll(".chip").forEach(c=>c.classList.remove("sel"));
  el.classList.add("sel");selExpiry=el.dataset.exp;
  runAnalyze();
}

async function runAnalyze(){ /* 第二步: 抓取所选到期日的全部期权信息 */
  const err=$("err");err.style.display="none";
  const b=$("findBtn");b.disabled=true;
  const p=new URLSearchParams({symbol:$("symbol").value.trim().toUpperCase(),
    strike:$("strike").value,expiry:selExpiry,
    ref:$("ref").value||"",override:$("override").value||"",q:$("divq").value||""});
  try{
    const r=await fetch("/api/analyze?"+p);
    const d=await r.json();
    if(!r.ok)throw new Error(d.error||("HTTP "+r.status));
    render(d);
  }catch(e){err.textContent="⚠ "+e.message;err.style.display="block";}
  cooldown(10,b,"🔎 查找可选到期日");
}

function cooldown(sec,btn,label){ /* 防封号冷却: 锁定全部操作 sec 秒 */
  cooling=true;let s=sec;
  const db=$("diagBtn");db.disabled=true;
  document.querySelectorAll(".chip").forEach(c=>c.disabled=true);
  btn.disabled=true;btn.textContent=`冷却 ${s}s(防封号)`;
  const t=setInterval(()=>{s--;
    if(s<=0){clearInterval(t);cooling=false;
      btn.disabled=db.disabled=false;btn.textContent=label;
      db.textContent="🩺 诊断数据链路";
      document.querySelectorAll(".chip").forEach(c=>c.disabled=false);}
    else btn.textContent=`冷却 ${s}s(防封号)`;},1000);
}
async function diag(){
  if(cooling)return;
  const err=$("err");err.style.display="none";
  const b=$("diagBtn");b.disabled=true;b.textContent="🩺 自检中…";
  try{
    const r=await fetch("/api/diag");const d=await r.json();
    const mark=s=>s.ok?'<span style="color:var(--hold)">✓</span>':'<span style="color:var(--roll)">✗</span>';
    let h=`<div class="legend">Python ${d.python} · yfinance ${d.yfinance} · 本次真实请求 ${d.calls} 次 · 剩余配额 ${d.quota_left}/8</div>`;
    h+=d.steps.map(s=>`<div style="font-family:var(--mono);font-size:12px;padding:6px 0;border-bottom:1px solid var(--line)">${mark(s)} ${s.name}${s.engine?` <span class="tag m">${s.engine}</span>`:""} <span style="color:var(--sub)">— ${s.info}</span></div>`).join("");
    if(d.steps.some(s=>!s.ok))h+=`<div class="legend" style="color:var(--gold)">修复顺序: ① pip install --upgrade yfinance ② 等1-2分钟再试(Yahoo临时限流) ③ 浏览器确认能打开 finance.yahoo.com(大陆网络/部分VPN不可达需换网络)</div>`;
    document.getElementById("diagPanel").style.display="block";
    document.getElementById("diagBody").innerHTML=h;
  }catch(e){err.textContent="⚠ 诊断失败: "+e.message;err.style.display="block";}
  cooldown(10,b,"🩺 诊断数据链路");
}

function render(d){
  document.querySelectorAll(".out").forEach(x=>x.style.display="block");
  const eng=d.stats.engines&&Object.keys(d.stats.engines).length?" · 引擎 "+Object.entries(d.stats.engines).map(([k,v])=>k+"→"+v).join(" "):"";
  $("statline").innerHTML=`限流状态: 本次Yahoo真实请求 <b>${d.stats.yahoo_calls}</b> 次 · 缓存命中 <b>${d.stats.cache_hits}</b> · 本分钟剩余配额 <b>${d.stats.quota_left}</b>/8${eng}`;

  /* 波动预警 */
  if(d.alerts){
    const nm={ok:"正常",warn:"关注",act:"行动"};
    $("alertBody").innerHTML=d.alerts.map(a=>`<div class="alert ${a.level}">
      <div class="h"><span>${a.metric} · ${a.title}</span><span>${a.value} · ${nm[a.level]}</span></div>
      <p>${a.advice}</p></div>`).join("");
  }

  /* 滚仓判定 */
  const b=$("banner");
  if(d.ref){
    b.style.display="block";
    b.classList.toggle("roll",d.ref.fired);b.classList.toggle("hold",!d.ref.fired);
    b.innerHTML=d.ref.fired
      ?`<div class="verdict"><span class="word">▼ 滚仓</span><span class="why">自 ${d.ref.date} 收盘 <b>${fmt(d.ref.close)}</b> 已跌 <b>${fmt(d.ref.drop)}%</b> ≥ ${d.params.drop_step}% — 触发,建议换至 <b>${d.rec}P</b></span></div>`
      :`<div class="verdict"><span class="word">● 持有</span><span class="why">自 ${d.ref.date} 收盘 <b>${fmt(d.ref.close)}</b> ${d.ref.drop>=0?"已跌":"反弹"} <b>${fmt(Math.abs(d.ref.drop))}%</b> · 触发价 <b>${fmt(d.ref.trig_px)}</b>,还需再跌 ${fmt(d.ref.need)}%</span></div>`;
  }else{
    b.style.display="block";b.classList.remove("roll");b.classList.add("hold");
    b.innerHTML=`<div class="verdict"><span class="word">● 行情</span><span class="why">未填查询起算日 — 仅展示行情/阶梯/扫描。填入上次买入日即可获得滚仓触发判定。</span></div>`;
  }

  /* 行情卡 */
  $("qts").textContent="— "+d.ts+(d.approx?" · ⚠链上无此strike,已就近取 "+d.strike:"");
  const ivLab=d.iv_dirty?fmt(d.iv,1)+"%*":fmt(d.iv,1)+"%";
  $("quoteBody").innerHTML=`
    <div class="kpi"><div class="k">${d.symbol} 现价</div><div class="n">${fmt(d.spot)} <small class="${d.day_chg<=0?'':''}">${d.day_chg>=0?"+":""}${fmt(d.day_chg)}%</small></div></div>
    <div class="kpi"><div class="k">${d.strike}P ${d.expiry}</div><div class="n gold">${fmt(d.mkt)} <small>${d.mkt_src||"理论"}</small></div></div>
    <div class="kpi"><div class="k">Bid / Ask</div><div class="n dim">${fmt(d.bid)} / ${fmt(d.ask)}</div></div>
    <div class="kpi"><div class="k">BS理论价·锚定</div><div class="n dim">${fmt(d.theo)} <small>×${fmt(d.anchor,3)}</small></div></div>
    <div class="kpi"><div class="k">隐含波动率 IV</div><div class="n">${ivLab}</div></div>
    <div class="kpi"><div class="k">|Δ| Delta</div><div class="n gold">${fmt(d.delta,3)}</div></div>
    <div class="kpi"><div class="k">Γ Gamma</div><div class="n dim">${fmt(d.gamma,5)}</div></div>
    <div class="kpi"><div class="k">Θ / 日</div><div class="n dim">${fmt(d.theta,3)}</div></div>
    <div class="kpi"><div class="k">Vega / vol点</div><div class="n dim">${fmt(d.vega)}</div></div>
    <div class="kpi"><div class="k">λ 弹性</div><div class="n">${fmt(d.lam)}×</div></div>
    <div class="kpi"><div class="k">持仓量 OI</div><div class="n dim">${d.oi.toLocaleString()}</div></div>
    <div class="kpi"><div class="k">剩余天数</div><div class="n dim">${d.days} <small>T=${d.T}y</small></div></div>`;

  /* 收益阶梯 */
  let lr="";
  for(const x of d.ladder){
    lr+=`<tr class="${x.level===0?'lv0':''}"><td>${x.level===0?"现在":"第 "+x.level+" 级"}</td>
      <td>${fmt(x.spy)}</td><td>−${fmt(x.cum_drop,1)}%</td><td>${fmt(x.px)}</td>
      <td class="${x.level>0?'hot':''}">${x.step_gain===null?"—":"+"+fmt(x.step_gain,1)+"%"}</td>
      <td>${x.cum_gain>=0?"+":""}${fmt(x.cum_gain,1)}%</td></tr>`;
  }
  $("ladderBody").innerHTML=`<table><thead><tr><th>级</th><th>${d.symbol} 到达</th><th>累计跌幅</th><th>期权价(锚定)</th><th>★ 本级收益% (每跌2.5%)</th><th>累计收益%</th></tr></thead><tbody>${lr}</tbody></table>`;

  /* 换仓扫描 */
  let cr="";
  for(const c of d.cands){
    const isRec=c.strike===d.rec,is95=c.strike===d.k95;
    cr+=`<tr class="${isRec?'rec':''}${!isRec&&is95?' r95':''}">
      <td>${c.strike}P${isRec?'<span class="tag g">推荐</span>':''}${is95?'<span class="tag m">×0.95</span>':''}</td>
      <td>${fmt(c.bid)}</td><td>${fmt(c.ask)}</td><td>${fmt(c.mid)}</td>
      <td>${fmt(c.iv,1)}%${c.iv_dirty?"*":""}</td><td>${fmt(c.delta,3)}</td>
      <td>${fmt(c.lam)}×</td><td style="color:var(--roll)">+${fmt(c.gain,1)}%</td>
      <td>${c.oi.toLocaleString()}</td></tr>`;
  }
  $("rollBody").innerHTML=`<table><thead><tr><th>Strike</th><th>Bid</th><th>Ask</th><th>Mid</th><th>IV</th><th>|Δ|</th><th>λ</th><th>跌2.5%预计</th><th>OI</th></tr></thead><tbody>${cr}</tbody></table>`;
}

$("findBtn").addEventListener("click",findExp);
$("symbol").addEventListener("input",()=>{const b=$("chips");b.style.display="none";b.innerHTML="";selExpiry=null;});
$("diagBtn").addEventListener("click",diag);
</script></body></html>"""


@app.route("/")
def index():
    """返回内嵌的单页UI。"""
    return HTML


def lan_ips():
    """探测本机局域网IP(供同一WiFi下的iPhone/iPad访问)。"""
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
        return [ip]
    except Exception:
        return []


def main():
    """启动入口。默认仅本机127.0.0.1可访问;
    加 --lan 参数绑定0.0.0.0 → 同一WiFi下的iPhone/iPad用打印出的地址访问,
    Safari打开后"添加到主屏幕"即可当全屏App使用(页面已内置Apple Web App标签)。"""
    lan = "--lan" in sys.argv
    host = "0.0.0.0" if lan else "127.0.0.1"
    print("═" * 56)
    print("  SOVEREIGN PUT ROLLER · LIVE v2.5   (BearStudio)")
    print(f"  本机地址: http://127.0.0.1:{PORT}   —  Ctrl+C 退出")
    if lan:
        for ip in lan_ips():
            print(f"  📱 手机/iPad(同WiFi): http://{ip}:{PORT}")
        print("     Safari打开 → 分享 → 添加到主屏幕 = 全屏App")
        print("  ⚠ --lan 模式无密码, 请只在可信的家庭WiFi使用")
    else:
        print("  提示: RUN_LAN.bat 或加 --lan 参数可让手机/iPad访问")
    print(f"  限流: 间隔≥{MIN_INTERVAL}s · ≤{MAX_CALLS_PER_MIN}次/分 · 多级缓存")
    print("  双引擎: yfinance ↔ 原生HTTP备用引擎 自动切换")
    print("═" * 56)
    threading.Timer(1.2, lambda: webbrowser.open(f"http://127.0.0.1:{PORT}")).start()
    app.run(host=host, port=PORT, debug=False)


if __name__ == "__main__":
    main()
