from __future__ import annotations

import time
import threading
import logging
import json
import os
import re
import base64
import hashlib
import hmac
from datetime import datetime, date, timedelta, timezone
from zoneinfo import ZoneInfo
from urllib.parse import urlencode
from urllib.request import Request, urlopen, build_opener, HTTPRedirectHandler
from http.cookiejar import CookieJar
from urllib.request import HTTPCookieProcessor
from urllib.error import HTTPError
from collections import deque
from flask import Flask, request, jsonify
from flask_cors import CORS
from flask_socketio import SocketIO
import pandas as pd
import numpy as np
import random
import math


FUSO_BRASILIA = ZoneInfo("America/Sao_Paulo")


def _agora_brasilia():
    """Retorna o horário atual oficial de Brasília com timezone explícito."""
    return datetime.now(FUSO_BRASILIA)


def _data_brasilia():
    return _agora_brasilia().date()


# ============================================================
# TRADER TIMER ZONE (TTZ) — compatibilidade com o Xbot
# ============================================================
TTZ_BASE_URL = "https://tradertimerzone.com"
TTZ_LOGIN_URL = f"{TTZ_BASE_URL}/login?callbackUrl=%2Fdashboard"
TTZ_CALENDAR_URL = f"{TTZ_BASE_URL}/dashboard"
TTZ_ZONE_DEFINITIONS = [
    {"name": "Blue Zone", "code": "B", "hex": "#01B0F1", "description": "Maior estabilidade com fluxo forte"},
    {"name": "Dark Green Zone", "code": "D", "hex": "#00B050", "description": "Liquidez equilibrada e leitura técnica mais confiável"},
    {"name": "Light Green Zone", "code": "L", "hex": "#A8CF45", "description": "Mercado mais leve e brando"},
    {"name": "Orange Zone", "code": "O", "hex": "#F59E0B", "description": "Liquidez irregular e maior risco de falso rompimento"},
    {"name": "Events Zone", "code": "R", "hex": "#ED3237", "description": "Evento econômico ativo ou muito próximo"},
    {"name": "Wine Zone", "code": "W", "hex": "#842D2F", "description": "Impacto máximo e perigo extremo"},
]
TTZ_ZONE_ALIASES = {
    "Zona Azul": "Blue Zone", "Blue Zone": "Blue Zone",
    "Zona Verde": "Dark Green Zone", "Dark Green Zone": "Dark Green Zone",
    "Zona Verde Clara": "Light Green Zone", "Light Green Zone": "Light Green Zone",
    "Zona Amarela": "Orange Zone", "Orange Zone": "Orange Zone",
    "Zona Vermelha": "Events Zone", "Events Zone": "Events Zone",
    "Zona Vinho": "Wine Zone", "Wine Zone": "Wine Zone",
}
TTZ_MARKET_CODE_TO_ZONE = {item["code"]: item["name"] for item in TTZ_ZONE_DEFINITIONS}
TTZ_ZONE_BY_NAME = {item["name"]: item for item in TTZ_ZONE_DEFINITIONS}
TTZ_ZONE_BY_HEX = {item["hex"].lower(): item["name"] for item in TTZ_ZONE_DEFINITIONS}
TTZ_ZONE_NAMES = [item["name"] for item in TTZ_ZONE_DEFINITIONS]
TTZ_COLOR_RE = re.compile(r"#[0-9a-fA-F]{6}")
TTZ_CURRENCY_RE = re.compile(r"\b[A-Z]{3}\b")


def _ttz_hex(value):
    match = TTZ_COLOR_RE.search(str(value or ""))
    return match.group(0).upper() if match else None


def _ttz_zone_from_value(value):
    if value in TTZ_ZONE_ALIASES:
        return TTZ_ZONE_ALIASES[value]
    if value in TTZ_ZONE_BY_NAME:
        return value
    code = str(value or "").strip().upper()
    if code in TTZ_MARKET_CODE_TO_ZONE:
        return TTZ_MARKET_CODE_TO_ZONE[code]
    hex_code = _ttz_hex(value)
    if hex_code and hex_code.lower() in TTZ_ZONE_BY_HEX:
        return TTZ_ZONE_BY_HEX[hex_code.lower()]
    normalized = str(value or "").strip().lower()
    for name in TTZ_ZONE_NAMES:
        if name.lower() == normalized:
            return name
    return None


def _ttz_parse_time(value):
    match = re.search(r"\b([01]?\d|2[0-3]):([0-5]\d)\b", str(value or ""))
    if not match:
        return None
    return f"{int(match.group(1)):02d}:{int(match.group(2)):02d}"


def _ttz_normalize_zone_list(value):
    if not isinstance(value, (list, tuple, set)):
        return []
    return list(dict.fromkeys(zone for zone in (_ttz_zone_from_value(item) for item in value) if zone))


def _ttz_normalize_schedule(value):
    """Normaliza intervalos editáveis pela aba TTZ."""
    if not isinstance(value, list):
        return []
    normalized = []
    for raw in value[:100]:
        if not isinstance(raw, dict):
            continue
        zone = _ttz_zone_from_value(raw.get("zone") or raw.get("zona") or raw.get("name"))
        start = _ttz_parse_time(raw.get("start") or raw.get("inicio"))
        end = _ttz_parse_time(raw.get("end") or raw.get("fim"))
        if not zone or not start or not end or start == end:
            continue
        days = raw.get("days", list(range(7)))
        if not isinstance(days, list):
            days = list(range(7))
        try:
            days = sorted({int(day) for day in days if 0 <= int(day) <= 6})
        except (TypeError, ValueError):
            days = list(range(7))
        currencies = raw.get("currencies", raw.get("moedas", []))
        if isinstance(currencies, str):
            currencies = [part.strip().upper() for part in currencies.split(",") if part.strip()]
        if not isinstance(currencies, list):
            currencies = []
        currencies = sorted({str(item).strip().upper() for item in currencies if str(item).strip()})
        normalized.append({"zone": zone, "start": start, "end": end, "days": days, "currencies": currencies})
    return normalized


def _ttz_event(zone, timestamp, source="schedule", currencies=None, start=None, end=None):
    definition = TTZ_ZONE_BY_NAME.get(zone, TTZ_ZONE_BY_NAME[TTZ_ZONE_NAMES[0]])
    return {
        "zone": zone,
        "zone_name": zone,
        "hex": definition["hex"],
        "description": definition["description"],
        "timestamp": float(timestamp),
        "time": datetime.fromtimestamp(float(timestamp), FUSO_BRASILIA).strftime("%H:%M"),
        "source": source,
        "currencies": sorted({str(item).upper() for item in (currencies or [])}),
        "start": start,
        "end": end,
    }


def _ttz_schedule_state(now=None):
    now = now or _agora_brasilia()
    current = []
    candidates = []
    schedule = _ttz_normalize_schedule(STATE.get("ttz_schedule", [])) if "STATE" in globals() else []
    for raw in schedule:
        for offset in (-1, 0, 1):
            base = now.date() + timedelta(days=offset)
            if base.weekday() not in raw["days"]:
                continue
            start_hour, start_minute = map(int, raw["start"].split(":"))
            end_hour, end_minute = map(int, raw["end"].split(":"))
            start_dt = datetime.combine(base, datetime.min.time(), tzinfo=FUSO_BRASILIA).replace(hour=start_hour, minute=start_minute)
            end_dt = datetime.combine(base, datetime.min.time(), tzinfo=FUSO_BRASILIA).replace(hour=end_hour, minute=end_minute)
            if end_dt <= start_dt:
                end_dt += timedelta(days=1)
            item = _ttz_event(raw["zone"], start_dt.timestamp(), currencies=raw["currencies"], start=start_dt.strftime("%H:%M"), end=end_dt.strftime("%H:%M"))
            item["end_timestamp"] = end_dt.timestamp()
            candidates.append(item)
            if start_dt.timestamp() <= now.timestamp() < end_dt.timestamp():
                current.append(item)
    current_item = max(current, key=lambda item: item["timestamp"]) if current else None
    future = sorted((item for item in candidates if item["timestamp"] > now.timestamp()), key=lambda item: item["timestamp"])
    return current_item, (future[0] if future else None)


def _ttz_html_events(html, now=None):
    """Extrai eventos do HTML do dashboard no mesmo formato observado no Xbot."""
    now = now or _agora_brasilia()
    try:
        from bs4 import BeautifulSoup
    except Exception:
        return []
    soup = BeautifulSoup(html, "html.parser")
    events = []
    for row in soup.select("section#hero tr"):
        text = row.get_text(" ", strip=True)
        time_text = _ttz_parse_time(text)
        if not time_text:
            continue
        styles = []
        for cell in row.find_all(["td", "div", "span"]):
            styles.append(str(cell.get("style", "")))
            styles.extend(str(item) for item in (cell.get("class") or []))
        zone = next((_ttz_zone_from_value(style) for style in styles if _ttz_zone_from_value(style)), None)
        if not zone:
            zone = _ttz_zone_from_value(row.get("style", ""))
        if not zone:
            continue
        hour, minute = map(int, time_text.split(":"))
        event_dt = now.replace(hour=hour, minute=minute, second=0, microsecond=0)
        if event_dt.timestamp() < now.timestamp() - 12 * 3600:
            event_dt += timedelta(days=1)
        currencies = sorted(set(TTZ_CURRENCY_RE.findall(text)))
        events.append(_ttz_event(zone, event_dt.timestamp(), source="dashboard", currencies=currencies))
    unique = {(item["timestamp"], item["zone"], tuple(item["currencies"])): item for item in events}
    return sorted(unique.values(), key=lambda item: item["timestamp"])


def _ttz_decode_market_token(token):
    if not token:
        return None
    try:
        padded = str(token).strip() + ("=" * (-len(str(token).strip()) % 4))
        raw = base64.b64decode(padded).decode("utf-8")
        payload = json.loads(raw)
        dates = payload.get("dates") or {}
        zones = payload.get("zones") or {}
        if payload.get("version") != 4 or not all(key in dates and key in zones for key in ("-1", "0", "1")):
            return None
        if not all(len(str(zones[key])) == 1440 for key in ("-1", "0", "1")):
            return None
        return payload
    except (ValueError, TypeError, json.JSONDecodeError, UnicodeDecodeError):
        return None


TTZ_MARKET_TOKEN_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".ttz_market_token")


def _ttz_persist_market_token(token):
    try:
        with open(TTZ_MARKET_TOKEN_FILE, "w", encoding="utf-8") as handle:
            handle.write(str(token).strip())
        try:
            os.chmod(TTZ_MARKET_TOKEN_FILE, 0o600)
        except OSError:
            pass
    except OSError:
        pass


def _ttz_clear_market_token():
    try:
        os.remove(TTZ_MARKET_TOKEN_FILE)
    except FileNotFoundError:
        pass
    except OSError:
        pass


def _ttz_load_cached_market():
    try:
        with open(TTZ_MARKET_TOKEN_FILE, "r", encoding="utf-8") as handle:
            token = handle.read().strip()
    except OSError:
        return
    payload = _ttz_decode_market_token(token)
    if payload:
        STATE["ttz_market_token"] = token
        STATE["ttz_market_payload"] = payload
        STATE["ttz_market_received_at"] = time.time()
        STATE["ttz_source"] = "dashboard-api"
        STATE["ttz_error"] = ""


def _ttz_market_state(payload, now=None):
    if not payload:
        return None, None
    now = now or _agora_brasilia()
    slots = []
    for key, date_text in (payload.get("dates") or {}).items():
        try:
            day = date.fromisoformat(str(date_text))
            encoded = str((payload.get("zones") or {}).get(str(key), ""))
            if len(encoded) != 1440:
                continue
            for minute, code in enumerate(encoded):
                zone = TTZ_MARKET_CODE_TO_ZONE.get(code)
                if not zone:
                    continue
                slot_dt = datetime.combine(day, datetime.min.time(), tzinfo=FUSO_BRASILIA) + timedelta(minutes=minute)
                slots.append((slot_dt, code, zone))
        except (TypeError, ValueError):
            continue
    slots.sort(key=lambda item: item[0])
    if not slots:
        return None, None
    current_index = next((i for i, item in enumerate(slots) if item[0] <= now < item[0] + timedelta(minutes=1)), None)
    if current_index is None:
        return None, None

    current_code = slots[current_index][1]
    start_index = current_index
    while start_index > 0 and slots[start_index - 1][1] == current_code and slots[start_index - 1][0] + timedelta(minutes=1) == slots[start_index][0]:
        start_index -= 1
    end_index = current_index
    while end_index + 1 < len(slots) and slots[end_index + 1][1] == current_code and slots[end_index][0] + timedelta(minutes=1) == slots[end_index + 1][0]:
        end_index += 1

    def run_item(first, last):
        start_dt = slots[first][0]
        end_dt = slots[last][0] + timedelta(minutes=1)
        item = _ttz_event(slots[first][2], start_dt.timestamp(), source="dashboard-api", start=start_dt.strftime("%H:%M"), end=end_dt.strftime("%H:%M"))
        item["code"] = slots[first][1]
        item["end_timestamp"] = end_dt.timestamp()
        return item

    current = run_item(start_index, end_index)
    next_index = end_index + 1
    if next_index >= len(slots):
        return current, None
    next_code = slots[next_index][1]
    next_end = next_index
    while next_end + 1 < len(slots) and slots[next_end + 1][1] == next_code and slots[next_end][0] + timedelta(minutes=1) == slots[next_end + 1][0]:
        next_end += 1
    return current, run_item(next_index, next_end)


def _ttz_cookie_header(jar):
    return "; ".join(f"{cookie.name}={cookie.value}" for cookie in jar)


def _ttz_extract_csrf(html):
    patterns = (
        r'<input[^>]+name=["\\\']csrfToken["\\\'][^>]+value=["\\\']([^"\\\']+)',
        r'<input[^>]+value=["\\\']([^"\\\']+)["\\\'][^>]+name=["\\\']csrfToken["\\\']',
    )
    for pattern in patterns:
        match = re.search(pattern, html, flags=re.IGNORECASE)
        if match:
            return match.group(1)
    return ""


def _ttz_login(email, password):
    """Autentica no TTZ e devolve apenas o cookie de sessão, nunca a senha."""
    jar = CookieJar()
    opener = build_opener(HTTPCookieProcessor(jar), HTTPRedirectHandler)
    common_headers = {
        "User-Agent": "MeuScript-TTZ/1.0",
        "Accept": "text/html,application/xhtml+xml,application/json",
    }
    # O dashboard TTZ é uma SPA (Next.js/NextAuth): a página /login não traz o
    # <input name="csrfToken"> no HTML cru (ele só existe depois do JS rodar
    # no navegador), por isso raspar a página de login nunca encontrava o
    # token. NextAuth expõe o token real via endpoint JSON dedicado — usamos
    # ele, e o cookie CSRF que a resposta define fica automaticamente no jar
    # para ser reenviado no POST de credenciais abaixo.
    csrf_request = Request(
        f"{TTZ_BASE_URL}/api/auth/csrf",
        headers={**common_headers, "Accept": "application/json"},
    )
    try:
        with opener.open(csrf_request, timeout=20) as response:
            csrf_payload = json.loads(response.read().decode("utf-8", errors="replace") or "{}")
    except Exception as exc:
        raise RuntimeError(f"Não foi possível obter o token CSRF do TTZ: {exc.__class__.__name__}") from exc
    csrf = str(csrf_payload.get("csrfToken") or "").strip()
    if not csrf:
        # Fallback legado, caso o site volte a servir a página renderizada no servidor.
        with opener.open(Request(TTZ_LOGIN_URL, headers=common_headers), timeout=20) as response:
            login_html = response.read().decode("utf-8", errors="replace")
        csrf = _ttz_extract_csrf(login_html)
    if not csrf:
        raise RuntimeError("Não foi possível obter o token CSRF do login TTZ")
    form = urlencode({
        "csrfToken": csrf,
        "callbackUrl": "/dashboard",
        "email": email,
        "password": password,
    }).encode("utf-8")
    callback_request = Request(
        f"{TTZ_BASE_URL}/api/auth/callback/credentials",
        data=form,
        headers={
            **common_headers,
            "Content-Type": "application/x-www-form-urlencoded",
            "Referer": TTZ_LOGIN_URL,
        },
        method="POST",
    )
    try:
        with opener.open(callback_request, timeout=25) as response:
            response.read(4096)
    except HTTPError as exc:
        detail = exc.read(1000).decode("utf-8", errors="replace")
        raise RuntimeError(f"Servidor TTZ recusou o login ({exc.code})") from exc
    cookie_header = _ttz_cookie_header(jar)
    if not cookie_header:
        raise RuntimeError("Login TTZ não retornou uma sessão válida")
    session_request = Request(f"{TTZ_BASE_URL}/api/auth/session", headers={**common_headers, "Cookie": cookie_header})
    try:
        with opener.open(session_request, timeout=15) as response:
            session_data = json.loads(response.read().decode("utf-8", errors="replace") or "{}")
    except Exception:
        session_data = {}
    if isinstance(session_data, dict) and session_data.get("user") is None:
        raise RuntimeError("E-mail ou senha TTZ inválidos")
    return cookie_header, session_data if isinstance(session_data, dict) else {}


def _ttz_auto_login_from_robot(email, password):
    """Tenta conectar o TTZ em segundo plano usando a mesma sessão do robô.

    A senha não é persistida nem enviada à interface; ela existe somente durante
    esta tentativa de autenticação no backend.
    """
    try:
        cookie_header, _session_data = _ttz_login(email, password)
        STATE["ttz_session_cookie"] = cookie_header
        STATE["ttz_session_email"] = email
        STATE["ttz_session_updated_at"] = time.time()
        STATE["ttz_source"] = "dashboard-api"
        STATE["ttz_last_update"] = 0
        STATE["ttz_error"] = ""
        _ttz_refresh(force=True)
        current, _next_item = _ttz_current_next()
        if current:
            _log_scan(f"✅ TTZ automático conectado — zona atual: {current.get('zone_name')}")
        else:
            _log_scan("✅ TTZ automático conectado — aguardando mapa oficial")
        _emit_status("ttz_auto_login_ok")
    except Exception as exc:
        # A conexão IQ Option não deve falhar apenas porque o TTZ bloqueou
        # a chamada; o cache oficial, se existente, continua sendo usado.
        if STATE.get("ttz_market_payload"):
            _log_scan(f"⚠️ TTZ automático indisponível: {exc.__class__.__name__}; mantendo cache oficial")
            STATE["ttz_error"] = ""
        else:
            _log_scan(f"⚠️ TTZ automático indisponível: {exc.__class__.__name__}")
            STATE["ttz_error"] = "Aguardando sincronização automática TTZ"
        _emit_status("ttz_auto_login_falhou")


def _ttz_refresh(force=False):
    """Atualiza o dashboard usando a sessão TTZ em memória ou um cookie legado."""
    if not STATE.get("ttz_ativo") and not force:
        return
    now_epoch = time.time()
    last = float(STATE.get("ttz_last_update", 0) or 0)
    refresh_seconds = max(15, int(STATE.get("ttz_refresh_seconds", 60) or 60))
    if not force and now_epoch - last < refresh_seconds:
        return
    STATE["ttz_last_update"] = now_epoch
    token = (STATE.get("ttz_market_token") or os.getenv("TTZ_MARKET_TOKEN", "")).strip()
    if token:
        market_payload = _ttz_decode_market_token(token)
        if market_payload:
            STATE["ttz_market_payload"] = market_payload
            STATE["ttz_market_received_at"] = now_epoch
            STATE["ttz_source"] = "dashboard-api"
            STATE["ttz_error"] = ""
            return
        STATE["ttz_error"] = "Token TTZ inválido ou expirado; usando os intervalos manuais da aba."
    cookie = (STATE.get("ttz_session_cookie") or os.getenv("TTZ_SESSION_COOKIE", "")).strip()
    if cookie:
        try:
            date_text = _data_brasilia().isoformat()
            api_url = f"{TTZ_BASE_URL}/api/integrations/market-zones?{urlencode({'date': date_text})}"
            req = Request(api_url, headers={
                "User-Agent": "MeuScript-TTZ/1.0",
                "Accept": "application/json",
                "x-ttz-dashboard-fetch": "market-zones-v1",
                "Cookie": cookie,
            }, method="GET")
            with urlopen(req, timeout=12) as response:
                data = json.loads(response.read().decode("utf-8", errors="replace") or "{}")
            market_token = str(data.get("token") or "").strip()
            market_payload = _ttz_decode_market_token(market_token)
            if data.get("success") and market_payload:
                STATE["ttz_market_payload"] = market_payload
                STATE["ttz_market_received_at"] = now_epoch
                STATE["ttz_source"] = "dashboard-api"
                STATE["ttz_error"] = ""
                return
            STATE["ttz_error"] = "A API oficial TTZ não retornou um mapa válido — sessão conectada, mas o endpoint /api/integrations/market-zones não é o real do dashboard atual (precisa capturar a chamada verdadeira do navegador). Usando a agenda manual da aba TTZ como fallback."
        except HTTPError as exc:
            detail = ""
            try:
                detail = exc.read(300).decode("utf-8", errors="replace")
            except Exception:
                pass
            STATE["ttz_error"] = f"Falha na API oficial TTZ: HTTP {exc.code} {exc.reason}" + (f" — {detail}" if detail else "") + " — sessão conectada, mas este endpoint não é o real do dashboard atual. Usando a agenda manual da aba TTZ como fallback."
        except Exception as exc:
            STATE["ttz_error"] = f"Falha na API oficial TTZ: {exc.__class__.__name__}: {exc} — usando a agenda manual da aba TTZ como fallback."
        # O endpoint acima ainda não foi confirmado contra o dashboard real (é uma
        # tentativa reversa-engenheirada, não documentação oficial). Não há um
        # segundo endpoint confiável para tentar: uma tentativa anterior de raspar
        # a página do dashboard via POST retornou 405 (Method Not Allowed), ou
        # seja, aquele endpoint estava errado e foi removido daqui. Enquanto o
        # endpoint real não for capturado do navegador, a agenda manual
        # (`ttz_schedule`) é a fonte de dados confiável.
        return
    if not cookie:
        # Sem credenciais TTZ na interface, o sistema segue automaticamente
        # com token/cookie de ambiente quando houver ou com a agenda manual.
        STATE["ttz_error"] = "" if STATE.get("ttz_schedule") else ""
        return


def _ttz_current_next():
    # O calendário visual deve continuar funcionando mesmo quando o filtro TTZ
    # estiver desligado. A flag `ttz_ativo` controla apenas a aplicação do
    # bloqueio/liberação de entradas; os intervalos manuais ainda precisam ser
    # calculados para alimentar o painel e o countdown.
    has_ttz_session = bool((STATE.get("ttz_session_cookie") or os.getenv("TTZ_SESSION_COOKIE", "") or os.getenv("TTZ_MARKET_TOKEN", "")).strip())
    if STATE.get("ttz_ativo") or has_ttz_session:
        _ttz_refresh()
    market_payload = STATE.get("ttz_market_payload")
    received_at = float(STATE.get("ttz_market_received_at", 0) or 0)
    max_age = max(180, int(STATE.get("ttz_refresh_seconds", 60) or 60) * 3)
    if market_payload and received_at and time.time() - received_at <= max_age:
        current, next_item = _ttz_market_state(market_payload)
        if current:
            return current, next_item
    elif market_payload and received_at:
        STATE["ttz_error"] = "Mapa TTZ desatualizado; aguardando a ponte do dashboard."
    events = STATE.get("ttz_events") or []
    now_epoch = time.time()
    if events:
        ordered = sorted(events, key=lambda item: float(item.get("timestamp", 0)))
        past = [item for item in ordered if float(item.get("timestamp", 0)) <= now_epoch]
        future = [item for item in ordered if float(item.get("timestamp", 0)) > now_epoch]
        return (past[-1] if past else None), (future[0] if future else None)
    return _ttz_schedule_state()


def _ttz_currency_matches(asset, currencies):
    if not asset or not currencies:
        return True
    symbol = re.sub(r"[^A-Z]", "", str(asset).upper())
    return any(currency in symbol for currency in currencies)


def _ttz_check_entry(asset=None):
    if not STATE.get("ttz_ativo"):
        return True, "TTZ desativado"
    blocked = set(STATE.get("ttz_blocked_zones") or STATE.get("ttz_selected_zones") or [])
    current, _ = _ttz_current_next()
    if not current:
        return False, "Dados TTZ indisponíveis — entrada bloqueada por segurança"
    if STATE.get("ttz_filter_by_currency") and asset and current.get("currencies"):
        if not _ttz_currency_matches(asset, current.get("currencies", [])):
            return True, "Filtro TTZ por moeda não se aplica a este ativo"
    zone_name = current.get("zone_name")
    if zone_name in blocked:
        return False, f"Zona atual: {zone_name} — COR BLOQUEADA"
    return True, f"Zona atual: {zone_name} — COR DESBLOQUEADA"


def _ttz_status():
    # Mantém a leitura visual do calendário independente do filtro operacional.
    # Quando o filtro está desligado, `_ttz_check_entry` continua liberando a
    # entrada e o frontend apenas marca a decisão como desativada.
    current, next_item = _ttz_current_next()
    session_cookie = (STATE.get("ttz_session_cookie") or os.getenv("TTZ_SESSION_COOKIE", "") or os.getenv("TTZ_MARKET_TOKEN", "")).strip()
    has_official_map = bool(STATE.get("ttz_market_payload"))
    allowed, reason = _ttz_check_entry()
    next_payload = None
    if next_item:
        next_payload = dict(next_item)
        next_payload["remaining_seconds"] = max(0, int(float(next_item["timestamp"]) - time.time()))
    return {
        "ativo": bool(STATE.get("ttz_ativo")),
        "acao": str(STATE.get("ttz_time_action", "PAUSE")).upper(),
        "filtro_moeda": bool(STATE.get("ttz_filter_by_currency")),
        "zonas_selecionadas": list(STATE.get("ttz_blocked_zones") or STATE.get("ttz_selected_zones") or []),
        "zonas_bloqueadas": list(STATE.get("ttz_blocked_zones") or STATE.get("ttz_selected_zones") or []),
        "todas_zonas_pausadas": set(TTZ_ZONE_NAMES).issubset(set(STATE.get("ttz_blocked_zones") or STATE.get("ttz_selected_zones") or [])),
        "zonas": TTZ_ZONE_DEFINITIONS,
        "schedule": list(STATE.get("ttz_schedule") or []),
        "current_zone": dict(current) if current else None,
        "next_zone": next_payload,
        "allowed": bool(allowed),
        "reason": reason,
        "last_update": STATE.get("ttz_last_update", 0),
        "error": STATE.get("ttz_error", ""),
        "source": STATE.get("ttz_source") or ("dashboard autenticado" if (STATE.get("ttz_session_cookie") or os.getenv("TTZ_SESSION_COOKIE", "").strip()) else ("dashboard-api" if os.getenv("TTZ_MARKET_TOKEN", "").strip() else ("intervalos manuais" if STATE.get("ttz_schedule") else "aguardando configuração TTZ"))),
        "session": {
            "conectado": bool(session_cookie or has_official_map),
            "automatico": True,
            "email": STATE.get("ttz_session_email", ""),
            "atualizado_em": STATE.get("ttz_session_updated_at", 0),
        },

    }


import logging
log_flask = logging.getLogger('werkzeug')
log_flask.setLevel(logging.ERROR)
logging.getLogger('iqoptionapi').setLevel(logging.CRITICAL)
logging.basicConfig(level=logging.CRITICAL)
logging.getLogger('engineio').setLevel(logging.CRITICAL)
logging.getLogger('socketio').setLevel(logging.CRITICAL)

from iqoptionapi.stable_api import IQ_Option
from iqoptionapi.expiration import get_expiration_time
from typing import Any, Dict, Iterable, List, Mapping, Optional

# ============================================================
# ESTRATEGIAS, INDICADORES E PRICE ACTION — INTEGRADOS NO BACKEND
# ============================================================
"""Estratégias de entrada inspiradas no catálogo de estratégias.

O módulo é deliberadamente puro: recebe uma lista de candles em ordem cronológica
(mais antigo primeiro) e devolve ``call``, ``put`` ou ``None``. A última vela é
tratada como possivelmente aberta e não é usada para confirmar o sinal.
"""



CATALOG_BASE_STRATEGIES = [
    "Milhão Maioria", "Milhão Minoria", "Padrão Ímpar", "Melhor de 3",
    "Padrão 23", "Gaba", "Torres Gêmeas", "Três Mosqueteiros",
    "Três Vizinhos", "Turn Over", "Seven Flip", "Reversão", "Five Flip", "MHI",
]

CATALOG_COMBINED_STRATEGIES = [
    "Torres Gêmeas / 3x1", "Triplicação / Torres Gêmeas",
    "Five Flip / Não Triplicação", "Five Flip / Torres Gêmeas",
    "Três Vizinhos / Torres Gêmeas",
]

CATALOG_STRATEGIES = list(dict.fromkeys(CATALOG_BASE_STRATEGIES + CATALOG_COMBINED_STRATEGIES))

# ============================================================
# CONFIGURAÇÃO INDIVIDUAL DE ESTRATÉGIAS (1ª leva: indicadores + candlestick + price action)
# ============================================================
# Padrões individuais que podem ser ligados/desligados na aba Gestão.
# Os IDs correspondem aos fatores calculados em _candlestick_35_scores().
CANDLESTICK_PATTERN_LABELS: Dict[str, str] = {
    "candlestick_martelo": "Martelo",
    "candlestick_estrela_manha": "Estrela da Manhã",
    "candlestick_estrela_doji_manha": "Estrela Doji da Manhã",
    "candlestick_perfurante": "Linha de Perfuração",
    "candlestick_bebe_abandonado": "Bebê Abandonado",
    "candlestick_fundo_pinca": "Fundo de Pinça",
    "candlestick_sombra_longa_baixa": "Sombra Longa Baixa",
    "candlestick_enforcado": "Enforcado",
    "candlestick_estrela_noite": "Estrela da Noite",
    "candlestick_estrela_doji_noite": "Estrela Doji da Noite",
    "candlestick_cobertura_nuvem": "Cobertura de Nuvem",
    "candlestick_estrela_cadente": "Estrela Cadente",
    "candlestick_martelo_invertido": "Martelo Invertido",
    "candlestick_topo_pinca": "Topo de Pinça",
    "candlestick_sombra_longa_alta": "Sombra Longa Alta",
    "candlestick_3_metodos_alta": "Três Métodos de Alta",
    "candlestick_3_metodos_baixa": "Três Métodos de Baixa",
    "candlestick_3_soldados_brancos": "Três Soldados Brancos",
    "candlestick_3_corvos_negros": "Três Corvos Negros",
    "candlestick_no_pescoco": "No Pescoço",
    "candlestick_pontape": "Pontapé",
    "candlestick_doji": "Doji",
    "candlestick_estrela_doji": "Estrela Doji",
    "candlestick_doji_libelula": "Doji Libélula",
    "candlestick_doji_lapide": "Doji Lápide",
    "candlestick_tri_estrela": "Tri-Estrela",
    "candlestick_harami": "Harami",
    "candlestick_harami_cruzado": "Harami Cruzado",
    "candlestick_piao": "Pião",
    "candlestick_marubozu": "Marubozu",
    "candlestick_engolfo": "Engolfo",
    "candlestick_lacuna_tasuki_alta": "Lacuna Tasuki de Alta",
    "candlestick_lacuna_tasuki_baixa": "Lacuna Tasuki de Baixa",
    "candlestick_janela_ascendente": "Janela Ascendente",
    "candlestick_janela_descendente": "Janela Descendente",
    "candlestick_3_por_dentro": "Três Por Dentro",
    "candlestick_3_por_fora": "Três Por Fora",
    "candlestick_mat_hold": "Mat Hold",
    "candlestick_linhas_separacao": "Linhas de Separação",
    "candlestick_avanco_bloqueado": "Avanço Bloqueado",
    "candlestick_deliberacao": "Deliberação",
    "candlestick_encontro": "Encontro",
    "candlestick_pombo_voltando": "Pombo Voltando",
    "candlestick_dois_corvos": "Dois Corvos",
    "candlestick_queda_3_metodos": "Queda de Três Métodos",
    "candlestick_torre": "Torre",
    "candlestick_chute": "Chute",
    "candlestick_contra_ataque": "Contra-Ataque",
}
CANDLESTICK_PATTERN_DEFAULTS: Dict[str, bool] = {nome: True for nome in CANDLESTICK_PATTERN_LABELS}
CANDLESTICK_PATTERN_DETECTOR_KEYS: Dict[str, str] = {
    "Bebê Abandonado": "candlestick_bebe_abandonado",
    "Perfurante": "candlestick_perfurante",
    "Cobertura de Nuvem": "candlestick_cobertura_nuvem",
    "Doji": "candlestick_doji",
    "Estrela Doji": "candlestick_estrela_doji",
    "Lacuna Tasuki Alta": "candlestick_lacuna_tasuki_alta",
    "Lacuna Tasuki Baixa": "candlestick_lacuna_tasuki_baixa",
    "Doji Libélula": "candlestick_doji_libelula",
    "Engolfo Bullish": "candlestick_engolfo",
    "Engolfo Bearish": "candlestick_engolfo",
    "Estrela Doji Manhã": "candlestick_estrela_doji_manha",
    "Estrela Doji Noite": "candlestick_estrela_doji_noite",
    "Estrela da Manhã": "candlestick_estrela_manha",
    "Estrela da Noite": "candlestick_estrela_noite",
    "3 Métodos Alta": "candlestick_3_metodos_alta",
    "3 Métodos Baixa": "candlestick_3_metodos_baixa",
    "Janela Ascendente": "candlestick_janela_ascendente",
    "Janela Descendente": "candlestick_janela_descendente",
    "Doji Lápide": "candlestick_doji_lapide",
    "Martelo": "candlestick_martelo",
    "Martelo Invertido": "candlestick_martelo_invertido",
    "Estrela Cadente": "candlestick_estrela_cadente",
    "Enforcado": "candlestick_enforcado",
    "Harami Bullish": "candlestick_harami",
    "Harami Bearish": "candlestick_harami",
    "Marubozu": "candlestick_marubozu",
    "3 Soldados": "candlestick_3_soldados_brancos",
    "3 Corvos": "candlestick_3_corvos_negros",
    "Pinça Fundo": "candlestick_fundo_pinca",
    "Pinça Topo": "candlestick_topo_pinca",
    "Chute Bullish": "candlestick_chute",
    "Chute Bearish": "candlestick_chute",
    "3 Por Dentro": "candlestick_3_por_dentro",
    "3 Por Fora": "candlestick_3_por_fora",
    "Mat Hold": "candlestick_mat_hold",
    "Linhas Separação": "candlestick_linhas_separacao",
    "Avanço Bloqueado": "candlestick_avanco_bloqueado",
    "Deliberação": "candlestick_deliberacao",
    "Encontro Bullish": "candlestick_encontro",
    "Encontro Bearish": "candlestick_encontro",
    "Pescoço": "candlestick_no_pescoco",
    "Pombo Voltando": "candlestick_pombo_voltando",
    "Dois Corvos": "candlestick_dois_corvos",
    "Queda 3 Métodos": "candlestick_queda_3_metodos",
    "Torre Bullish": "candlestick_torre",
    "Torre Bearish": "candlestick_torre",
    "Contra-Ataque": "candlestick_contra_ataque",
}

# Cada estratégia abaixo tem configuração própria (ativo/desativado, peso,
# timeframe permitido, candles mínimos, força mínima, confirmações mínimas,
# direção permitida e validade do sinal), aplicada de fato na função de
# detecção correspondente — não são apenas flags decorativas.
ESTRATEGIA_CONFIG_DEFAULTS: Dict[str, Dict[str, Any]] = {
    "candlestick": {
        "ativo": True, "peso": 1.0, "direcao": "ambos", "timeframes": [1, 5, 15],
        "periodo": 20, "min_candles": 20, "forca_minima": 60, "confirmacoes_minimas": 1,
        "validade_segundos": 30,
        "padroes": dict(CANDLESTICK_PATTERN_DEFAULTS),
        "confirmar_candle_seguinte": True, "detectar_reversao": True,
        "detectar_continuacao": True, "detectar_indecisao": True,
        "filtrar_contra_tendencia": True,
    },
    "price_action": {
        "ativo": True, "peso": 1.0, "direcao": "ambos", "timeframes": [1, 5, 15],
        "periodo": 30, "min_candles": 30, "forca_minima": 65, "confirmacoes_minimas": 2,
        "validade_segundos": 30,
        "detectar_tendencia": True, "detectar_rompimento": True,
        "detectar_rejeicao": True, "detectar_pullback": True, "detectar_extremos": True,
    },
    "rsi": {
        "ativo": True, "peso": 0.75, "direcao": "ambos", "timeframes": [1, 5, 15],
        "periodo": 14, "min_candles": 16, "forca_minima": 60, "confirmacoes_minimas": 2,
        "validade_segundos": 30,
        "sobrecompra": 70, "sobrevenda": 30, "zona_extrema_sup": 80, "zona_extrema_inf": 20,
        "detectar_divergencia": True, "detectar_cruzamento": True,
    },
    "aroon": {
        "ativo": True, "peso": 0.75, "direcao": "ambos", "timeframes": [1, 5, 15],
        "periodo": 14, "min_candles": 15, "forca_minima": 70, "confirmacoes_minimas": 1,
        "validade_segundos": 30, "aroon_minimo": 70, "detectar_cruzamento": True,
    },
    "darvas": {
        "ativo": True, "peso": 0.75, "direcao": "ambos", "timeframes": [1, 5, 15],
        "periodo": 20, "min_candles": 22, "forca_minima": 65, "confirmacoes_minimas": 1,
        "validade_segundos": 30,
        "distancia_maxima_rompimento": 0.20, "confirmar_reteste": False,
    },
    "suporte_resistencia": {
        "ativo": True, "peso": 0.75, "direcao": "ambos", "timeframes": [1, 5, 15],
        "periodo": 50, "min_candles": 52, "forca_minima": 60, "confirmacoes_minimas": 1,
        "validade_segundos": 30, "min_toques": 2, "zona_tolerancia": 0.10,
    },
    "fibonacci": {
        "ativo": True, "peso": 0.75, "direcao": "ambos", "timeframes": [1, 5, 15],
        "periodo": 100, "min_candles": 100, "forca_minima": 60, "confirmacoes_minimas": 1,
        "validade_segundos": 30, "tolerancia_toque": 0.10,
    },
    "efectiv": {
        "ativo": True, "peso": 1.0, "direcao": "ambos", "timeframes": [1, 5, 15],
        "periodo": 20, "min_candles": 25, "forca_minima": 70, "confirmacoes_minimas": 3,
        "validade_segundos": 30, "sensibilidade": "media", "multiplicador": 2.0,
    },
    # Estratégias dos scripts anexados. O campo `ativo` é controlado na aba Gestão.
    "codigo_cores_pro": {
        "ativo": True, "peso": 1.0, "direcao": "ambos", "timeframes": [1, 5, 15],
        "min_candles": 5, "forca_minima": 0, "validade_segundos": 30,
    },
    "ax1_rt": {
        "ativo": True, "peso": 1.0, "direcao": "ambos", "timeframes": [1, 5, 15],
        "min_candles": 7, "forca_minima": 0, "validade_segundos": 30,
    },
    # Cinco estratégias portadas dos fontes MQL4 analisados. Elas são avaliadas
    # somente com candles fechados e não dependem de DLL, EX4 ou iCustom.
    "precision_trend": {
        "ativo": True, "peso": 1.0, "direcao": "ambos", "timeframes": [1, 5, 15],
        "periodo": 30, "sensibilidade": 2.0, "periodo_media": 14,
        "metodo_media": "tema", "preco_media": "heiken_extremo",
        "exigir_concordancia": True, "min_candles": 55, "forca_minima": 70,
        "validade_segundos": 30,
    },
    "ddfx_bbstop": {
        "ativo": True, "peso": 1.0, "direcao": "ambos", "timeframes": [1, 5, 15],
        "periodo": 14, "desvio": 2.0, "risco": 1.0,
        "min_candles": 30, "forca_minima": 70, "validade_segundos": 30,
    },
    "double_zigzag": {
        "ativo": True, "peso": 1.0, "direcao": "ambos", "timeframes": [1, 5, 15],
        "profundidade_rapida": 6, "profundidade_lenta": 24,
        "confirmacao_fractal": 2, "min_candles": 35, "forca_minima": 80,
        "validade_segundos": 30,
    },
    "parabolic_sar": {
        "ativo": True, "peso": 0.75, "direcao": "ambos", "timeframes": [1, 5, 15],
        "passo": 0.02, "maximo": 0.20, "min_candles": 25,
        "forca_minima": 70, "validade_segundos": 30,
    },
    "forex_guru_cloud": {
        "ativo": True, "peso": 1.0, "direcao": "ambos", "timeframes": [1, 5, 15],
        "tenkan": 8, "kijun": 29, "senkou": 34, "min_candles": 45,
        "forca_minima": 70, "validade_segundos": 30,
    },
}

_SENSIBILIDADE_MULTIPLICADOR = {"baixa": 1.5, "media": 2.0, "alta": 2.6}


def _clonar_config_estrategias() -> Dict[str, Dict[str, Any]]:
    return {nome: dict(cfg) for nome, cfg in ESTRATEGIA_CONFIG_DEFAULTS.items()}


def _cfg_estrategia(nome: str) -> Dict[str, Any]:
    """Config efetiva da estratégia: defaults + overrides salvos em STATE."""
    base = dict(ESTRATEGIA_CONFIG_DEFAULTS.get(nome, {}))
    override = STATE.get("config_estrategias", {}).get(nome, {}) if isinstance(STATE.get("config_estrategias"), dict) else {}
    base.update(override or {})
    return base


def _estrategia_timeframe_ok(cfg: Dict[str, Any]) -> bool:
    tf_atual = STATE.get("expiracao", 1)
    tfs = cfg.get("timeframes") or [1, 5, 15]
    try:
        return int(tf_atual) in [int(x) for x in tfs]
    except (TypeError, ValueError):
        return True


def _estrategia_direcao_ok(cfg: Dict[str, Any], direcao: Optional[str]) -> bool:
    permitido = cfg.get("direcao", "ambos")
    if permitido == "ambos" or not direcao:
        return True
    return permitido == direcao


def _registrar_sinal_estrategia(nome: str, sinal: Optional[str], forca: float = 0.0) -> None:
    """Guarda o último sinal + timestamp de cada estratégia configurável, para
    exibição no painel e para o cálculo de validade do sinal."""
    registro = STATE.setdefault("ultimo_sinal_estrategia", {})
    registro[nome] = {"sinal": sinal, "forca": round(float(forca or 0), 1), "ts": time.time()}


def _sinal_estrategia_valido(nome: str) -> bool:
    registro = STATE.get("ultimo_sinal_estrategia", {}).get(nome)
    if not registro:
        return False
    cfg = _cfg_estrategia(nome)
    validade = float(cfg.get("validade_segundos", 30) or 30)
    return (time.time() - registro.get("ts", 0)) <= validade

# Os quinze padrões nomeados no módulo de reversão do executável analisado.
CATALOG_CANDLE_PATTERNS = [
    "Estrela da Manhã", "Martelo", "Martelo Invertido", "Linha de Perfuração",
    "Três Soldados Brancos", "Harami de Alta", "Engolfo de Alta", "Dragonfly Doji",
    "Estrela da Noite", "Enforcado", "Nuvem Negra", "Três Corvos Negros",
    "Harami de Baixa", "Engolfo de Baixa", "Gravestone Doji",
]


def _num(candle: Mapping[str, Any], key: str) -> float:
    return float(candle.get(key, 0.0))


def _closed(candles: Iterable[Mapping[str, Any]]) -> List[Mapping[str, Any]]:
    """Retorna candles fechados; a última vela é reservada como vela em formação."""
    data = list(candles or [])
    return data[:-1] if len(data) > 1 else []


def _colour(candle: Mapping[str, Any]) -> int:
    op, cl = _num(candle, "open"), _num(candle, "close")
    if cl > op:
        return 1
    if cl < op:
        return -1
    return 0


def _eh_doji(candle: Mapping[str, Any]) -> bool:
    """Retorna True quando abertura e fechamento da vela são iguais."""
    try:
        return bool(np.isclose(_num(candle, "open"), _num(candle, "close"), rtol=0.0, atol=1e-12))
    except (TypeError, ValueError, KeyError):
        return False


def _janela_tem_doji(candles: Iterable[Mapping[str, Any]], tamanho: int = 5) -> bool:
    """Indica se há Doji nas últimas velas fechadas de confirmação."""
    data = list(candles or [])
    if len(data) > 1:
        data = data[:-1]  # a última vela pode estar em formação
    try:
        tamanho = max(1, int(tamanho))
    except (TypeError, ValueError):
        tamanho = 5
    return any(_eh_doji(candle) for candle in data[-tamanho:])


def _colours(candles: List[Mapping[str, Any]]) -> List[int]:
    return [_colour(c) for c in candles]


def _body(c: Mapping[str, Any]) -> float:
    return abs(_num(c, "close") - _num(c, "open"))


def _range(c: Mapping[str, Any]) -> float:
    return max(0.0, _num(c, "high") - _num(c, "low"))


def _majority(values: List[int], minority: bool = False) -> Optional[str]:
    values = [v for v in values if v]
    if not values:
        return None
    pos, neg = values.count(1), values.count(-1)
    if pos == neg:
        return None
    direction = 1 if pos > neg else -1
    if minority:
        direction = -direction
    return "call" if direction > 0 else "put"


def _same(values: List[int], minimum: int) -> Optional[int]:
    values = [v for v in values if v]
    if len(values) < minimum or not values:
        return None
    if all(v == 1 for v in values):
        return 1
    if all(v == -1 for v in values):
        return -1
    return None


def _opposite(direction: int) -> Optional[str]:
    if direction > 0:
        return "put"
    if direction < 0:
        return "call"
    return None


def _to_signal(direction: Optional[int]) -> Optional[str]:
    if direction is None or direction == 0:
        return None
    return "call" if direction > 0 else "put"


def _milhao(closed: List[Mapping[str, Any]], minority: bool) -> Optional[str]:
    # O catálogo expõe Maioria/Minoria; usa cinco velas fechadas para reduzir
    # sinais baseados em uma única vela e manter a decisão reproduzível.
    if len(closed) < 5:
        return None
    sample = closed[-5:]
    if any(_colour(c) == 0 for c in sample):
        return None
    return _majority(_colours(sample), minority=minority)


def _padrao_impar(closed: List[Mapping[str, Any]]) -> Optional[str]:
    if len(closed) < 5:
        return None
    seq = _colours(closed[-5:])
    if 0 in seq:
        return None
    # Alternância ímpar: a próxima direção é a inversão da última cor.
    if all(seq[i] != seq[i - 1] for i in range(1, len(seq))):
        return _to_signal(-seq[-1])
    return None


def _melhor_de_3(closed: List[Mapping[str, Any]]) -> Optional[str]:
    if len(closed) < 3:
        return None
    return _majority(_colours(closed[-3:]))


def _padrao_23(closed: List[Mapping[str, Any]]) -> Optional[str]:
    if len(closed) < 5:
        return None
    a, b, c = [_colour(x) for x in closed[-3:]]
    if 0 in (a, b, c):
        return None
    # Dois candles contra um movimento recente: busca a confirmação do terceiro.
    if a == b and c == -a:
        return _to_signal(c)
    if a == -b and b == c:
        return _to_signal(c)
    return None


def _gaba(closed: List[Mapping[str, Any]]) -> Optional[str]:
    if len(closed) < 4:
        return None
    seq = _colours(closed[-4:])
    if 0 in seq:
        return None
    if seq[-1] == seq[-2] and seq[-3] == seq[-4] and seq[-1] != seq[-3]:
        return _to_signal(seq[-1])
    return None


def _torres_gemeas(closed: List[Mapping[str, Any]]) -> Optional[str]:
    if len(closed) < 2:
        return None
    a, b = closed[-2], closed[-1]
    ca, cb = _colour(a), _colour(b)
    if ca == 0 or cb == 0 or ca != cb:
        return None
    ra, rb = _range(a), _range(b)
    if ra <= 0 or rb <= 0:
        return None
    # Duas velas vizinhas de mesma direção e amplitude próxima.
    if abs(ra - rb) / max(ra, rb) <= 0.35:
        return _to_signal(cb)
    return None


def _tres_mosqueteiros(closed: List[Mapping[str, Any]]) -> Optional[str]:
    if len(closed) < 3:
        return None
    sample = closed[-3:]
    direction = _same(_colours(sample), 3)
    if direction is None:
        return None
    closes = [_num(c, "close") for c in sample]
    if direction == 1 and closes[0] < closes[1] < closes[2]:
        return "call"
    if direction == -1 and closes[0] > closes[1] > closes[2]:
        return "put"
    return None


def _tres_vizinhos(closed: List[Mapping[str, Any]]) -> Optional[str]:
    if len(closed) < 3:
        return None
    sample = closed[-3:]
    direction = _same(_colours(sample), 3)
    if direction is None:
        return None
    bodies = [_body(c) for c in sample]
    if bodies[0] <= bodies[1] <= bodies[2] and bodies[2] > 0:
        return _to_signal(direction)
    return None


def _turn_over(closed: List[Mapping[str, Any]]) -> Optional[str]:
    if len(closed) < 4:
        return None
    prior = _same(_colours(closed[-4:-1]), 3)
    latest = _colour(closed[-1])
    if prior is not None and latest == -prior and _body(closed[-1]) >= _body(closed[-2]):
        return _to_signal(latest)
    return None


def _flip(closed: List[Mapping[str, Any]], window: int) -> Optional[str]:
    if len(closed) < window:
        return None
    direction = _same(_colours(closed[-window:]), window)
    return _opposite(direction) if direction is not None else None


def _reversao(closed: List[Mapping[str, Any]]) -> Optional[str]:
    if len(closed) < 3:
        return None
    prior = _colour(closed[-2])
    latest = _colour(closed[-1])
    if prior == 0 or latest == 0 or prior == latest:
        return None
    last = closed[-1]
    body = _body(last)
    lower = min(_num(last, "open"), _num(last, "close")) - _num(last, "low")
    upper = _num(last, "high") - max(_num(last, "open"), _num(last, "close"))
    if latest == 1 and lower >= max(body * 1.5, upper):
        return "call"
    if latest == -1 and upper >= max(body * 1.5, lower):
        return "put"
    return _to_signal(latest)


def _r7(closed: List[Mapping[str, Any]]) -> Optional[str]:
    if len(closed) < 7:
        return None
    return _majority(_colours(closed[-7:]))


def _triplicacao(closed: List[Mapping[str, Any]]) -> Optional[str]:
    if len(closed) < 6:
        return None
    seq = _colours(closed[-6:])
    if any(v == 0 for v in seq):
        return None
    if seq[-1] == seq[-2] == seq[-3] and seq[-4] == seq[-5] == seq[-6] and seq[-1] != seq[-4]:
        return _to_signal(seq[-1])
    return None


def _rsi_series(closes: List[float], period: int) -> List[float]:
    """Série de RSI (não só o último valor) para permitir checar cruzamento/reação."""
    if len(closes) < period + 2:
        return []
    deltas = [closes[i] - closes[i - 1] for i in range(1, len(closes))]
    serie = []
    for fim in range(period, len(deltas) + 1):
        janela = deltas[fim - period:fim]
        ganhos = sum(max(d, 0.0) for d in janela) / period
        perdas = sum(max(-d, 0.0) for d in janela) / period
        if perdas == 0:
            rsi = 100.0 if ganhos > 0 else 50.0
        else:
            rs = ganhos / perdas
            rsi = 100.0 - (100.0 / (1.0 + rs))
        serie.append(rsi)
    return serie


def _rsi_signal(closed: List[Mapping[str, Any]], cfg: Optional[Dict[str, Any]] = None) -> Optional[str]:
    cfg = cfg or _cfg_estrategia("rsi")
    if not cfg.get("ativo", True) or not _estrategia_timeframe_ok(cfg):
        return None
    period = int(cfg.get("periodo", 14) or 14)
    if len(closed) < max(int(cfg.get("min_candles", period + 2) or 0), period + 2):
        return None
    closes = [_num(c, "close") for c in closed]
    serie = _rsi_series(closes, period)
    if len(serie) < 2:
        return None
    rsi_atual, rsi_anterior = serie[-1], serie[-2]
    sobrecompra = float(cfg.get("sobrecompra", 70))
    sobrevenda = float(cfg.get("sobrevenda", 30))
    zona_ext_sup = float(cfg.get("zona_extrema_sup", 80))
    zona_ext_inf = float(cfg.get("zona_extrema_inf", 20))
    candle_verde = _colour(closed[-1]) > 0
    candle_vermelho = _colour(closed[-1]) < 0

    condicoes_call = 0
    condicoes_put = 0
    # Condição 1: RSI em sobrevenda/sobrecompra
    if rsi_anterior <= sobrevenda or rsi_atual <= sobrevenda:
        condicoes_call += 1
    if rsi_anterior >= sobrecompra or rsi_atual >= sobrecompra:
        condicoes_put += 1
    # Condição 2 (reação/rompimento da região): RSI subindo de volta pela zona, com candle confirmando
    if cfg.get("detectar_cruzamento", True):
        if rsi_atual > rsi_anterior and rsi_anterior <= sobrevenda and candle_verde:
            condicoes_call += 1
        if rsi_atual < rsi_anterior and rsi_anterior >= sobrecompra and candle_vermelho:
            condicoes_put += 1

    minimo = int(cfg.get("confirmacoes_minimas", 2) or 2)
    direcao = None
    if condicoes_call >= minimo and condicoes_call > condicoes_put:
        direcao = "call"
    elif condicoes_put >= minimo and condicoes_put > condicoes_call:
        direcao = "put"
    if not direcao:
        return None

    # Força: distância até a zona extrema (quanto mais fundo na zona extrema, mais forte)
    if direcao == "call":
        forca = 50.0 + max(0.0, (sobrevenda - min(rsi_atual, rsi_anterior))) / max(1.0, (sobrevenda - zona_ext_inf)) * 50.0
    else:
        forca = 50.0 + max(0.0, (max(rsi_atual, rsi_anterior) - sobrecompra)) / max(1.0, (zona_ext_sup - sobrecompra)) * 50.0
    forca = max(0.0, min(100.0, forca))
    if forca < float(cfg.get("forca_minima", 60) or 0):
        return None
    if not _estrategia_direcao_ok(cfg, direcao):
        return None
    return direcao, forca


def _aroon_signal(closed: List[Mapping[str, Any]], cfg: Optional[Dict[str, Any]] = None):
    cfg = cfg or _cfg_estrategia("aroon")
    if not cfg.get("ativo", True) or not _estrategia_timeframe_ok(cfg):
        return None
    period = int(cfg.get("periodo", 14) or 14)
    if len(closed) < max(int(cfg.get("min_candles", period + 1) or 0), period + 1):
        return None
    window = closed[-period:]
    highs = [_num(c, "high") for c in window]
    lows = [_num(c, "low") for c in window]
    dias_desde_topo = period - 1 - max(range(period), key=lambda i: highs[i])
    dias_desde_fundo = period - 1 - min(range(period), key=lambda i: lows[i])
    aroon_up = 100.0 * (period - dias_desde_topo) / period
    aroon_down = 100.0 * (period - dias_desde_fundo) / period
    minimo = float(cfg.get("aroon_minimo", 70))
    direcao = None
    if aroon_up >= minimo and aroon_up > aroon_down:
        direcao = "call"
    elif aroon_down >= minimo and aroon_down > aroon_up:
        direcao = "put"
    if not direcao:
        return None
    forca = max(aroon_up, aroon_down)
    if forca < float(cfg.get("forca_minima", 70) or 0):
        return None
    if not _estrategia_direcao_ok(cfg, direcao):
        return None
    return direcao, forca


def _darvas_signal(closed: List[Mapping[str, Any]], cfg: Optional[Dict[str, Any]] = None):
    cfg = cfg or _cfg_estrategia("darvas")
    if not cfg.get("ativo", True) or not _estrategia_timeframe_ok(cfg):
        return None
    period = int(cfg.get("periodo", 20) or 20)
    if len(closed) < max(int(cfg.get("min_candles", period + 2) or 0), period + 2):
        return None
    anterior = closed[-period - 1:-1]
    ultimo = closed[-1]
    topo = max(_num(c, "high") for c in anterior)
    fundo = min(_num(c, "low") for c in anterior)
    close = _num(ultimo, "close")
    if topo <= 0:
        return None
    distancia_max = float(cfg.get("distancia_maxima_rompimento", 0.20)) / 100.0
    direcao = None
    dist_pct = 0.0
    if close > topo and _colour(ultimo) > 0:
        dist_pct = (close - topo) / topo
        if dist_pct <= distancia_max:
            direcao = "call"
    elif close < fundo and _colour(ultimo) < 0 and fundo > 0:
        dist_pct = (fundo - close) / fundo
        if dist_pct <= distancia_max:
            direcao = "put"
    if not direcao:
        return None
    forca = 50.0 + min(1.0, dist_pct / max(distancia_max, 1e-6)) * 50.0
    if forca < float(cfg.get("forca_minima", 65) or 0):
        return None
    if not _estrategia_direcao_ok(cfg, direcao):
        return None
    return direcao, forca


def _support_resistance_signal(closed: List[Mapping[str, Any]], cfg: Optional[Dict[str, Any]] = None):
    cfg = cfg or _cfg_estrategia("suporte_resistencia")
    if not cfg.get("ativo", True) or not _estrategia_timeframe_ok(cfg):
        return None
    period = int(cfg.get("periodo", 50) or 50)
    if len(closed) < max(int(cfg.get("min_candles", period + 2) or 0), period + 2):
        return None
    anterior = closed[-period - 1:-1]
    ultimo = closed[-1]
    resistencia = max(_num(c, "high") for c in anterior)
    suporte = min(_num(c, "low") for c in anterior)
    close = _num(ultimo, "close")
    tolerancia = float(cfg.get("zona_tolerancia", 0.10)) / 100.0
    # Mínimo de toques: quantas vezes o preço chegou perto do nível na janela
    toques_resist = sum(1 for c in anterior if resistencia > 0 and abs(_num(c, "high") - resistencia) / resistencia <= tolerancia)
    toques_suporte = sum(1 for c in anterior if suporte > 0 and abs(_num(c, "low") - suporte) / suporte <= tolerancia)
    min_toques = int(cfg.get("min_toques", 2) or 1)
    direcao = None
    if close > resistencia and _colour(ultimo) > 0 and toques_resist >= min_toques:
        direcao = "call"
    elif close < suporte and _colour(ultimo) < 0 and toques_suporte >= min_toques:
        direcao = "put"
    if not direcao:
        return None
    toques = toques_resist if direcao == "call" else toques_suporte
    forca = min(100.0, 50.0 + toques * 12.5)
    if forca < float(cfg.get("forca_minima", 60) or 0):
        return None
    if not _estrategia_direcao_ok(cfg, direcao):
        return None
    return direcao, forca


def _fibonacci_signal(closed: List[Mapping[str, Any]], cfg: Optional[Dict[str, Any]] = None):
    cfg = cfg or _cfg_estrategia("fibonacci")
    if not cfg.get("ativo", True) or not _estrategia_timeframe_ok(cfg):
        return None
    period = int(cfg.get("periodo", 20) or 20)
    if len(closed) < max(int(cfg.get("min_candles", period + 2) or 0), period + 2):
        return None
    janela = closed[-period - 1:-1]
    high = max(_num(c, "high") for c in janela)
    low = min(_num(c, "low") for c in janela)
    amplitude = high - low
    if amplitude <= 0:
        return None
    ultimo = closed[-1]
    close = _num(ultimo, "close")
    tolerancia = amplitude * float(cfg.get("tolerancia_toque", 0.10)) / 100.0
    nivel_382 = high - amplitude * 0.382
    nivel_50 = high - amplitude * 0.50
    nivel_618 = high - amplitude * 0.618
    niveis_prioritarios = (nivel_382, nivel_50, nivel_618)
    distancia_min = min(abs(close - n) for n in niveis_prioritarios)
    perto_de_nivel = distancia_min <= max(tolerancia, amplitude * 0.03)
    direcao = None
    if _colour(ultimo) > 0 and close >= nivel_618 and close <= nivel_382 and perto_de_nivel:
        direcao = "call"
    elif _colour(ultimo) < 0 and close <= nivel_382 and close >= nivel_618 and perto_de_nivel:
        direcao = "put"
    if not direcao:
        return None
    forca = max(0.0, 100.0 - (distancia_min / amplitude) * 200.0)
    forca = max(0.0, min(100.0, forca))
    if forca < float(cfg.get("forca_minima", 60) or 0):
        return None
    if not _estrategia_direcao_ok(cfg, direcao):
        return None
    return direcao, forca


def price_action_indicadores(candles: Iterable[Mapping[str, Any]]) -> Dict[str, Optional[str]]:
    """Sinais técnicos complementares do robô Price Action/Indicadores.

    Cada indicador usa sua própria configuração (config_estrategias em STATE):
    período, força mínima, confirmações mínimas, timeframe permitido, direção
    permitida e candles mínimos. Guarda também o último sinal+força de cada um
    para o painel e para o cálculo de validade do sinal.
    """
    closed = _closed(candles)
    resultado: Dict[str, Optional[str]] = {}
    mapa = {
        "RSI": ("rsi", _rsi_signal),
        "Aroon": ("aroon", _aroon_signal),
        "Darvas": ("darvas", _darvas_signal),
        "Suporte/Resistência": ("suporte_resistencia", _support_resistance_signal),
        "Fibonacci": ("fibonacci", _fibonacci_signal),
    }
    if any(_eh_doji(candle) for candle in closed[-5:]):
        for nome_exibicao, (chave_cfg, _func) in mapa.items():
            resultado[nome_exibicao] = None
            _registrar_sinal_estrategia(chave_cfg, None, 0)
        return resultado
    for nome_exibicao, (chave_cfg, func) in mapa.items():
        cfg = _cfg_estrategia(chave_cfg)
        try:
            saida = func(closed, cfg)
        except Exception:
            saida = None
        if isinstance(saida, tuple):
            sinal, forca = saida
        else:
            sinal, forca = saida, 0.0
        resultado[nome_exibicao] = sinal
        _registrar_sinal_estrategia(chave_cfg, sinal, forca)
    return resultado


def _price_action_signal(candles: Iterable[Mapping[str, Any]]) -> Optional[str]:
    """Estratégia Price Action própria (seção 2 da config): tendência, rompimento,
    rejeição, pullback e máximas/mínimas — combinadas com confirmação mínima e
    força mínima configuráveis. Antes disso o robô só tinha os 5 indicadores
    técnicos rotulados de "Price Action"; esta função é a detecção real."""
    cfg = _cfg_estrategia("price_action")
    if not cfg.get("ativo", True) or not _estrategia_timeframe_ok(cfg):
        _registrar_sinal_estrategia("price_action", None, 0)
        return None
    closed = _closed(candles)
    period = int(cfg.get("periodo", 30) or 30)
    if len(closed) < max(int(cfg.get("min_candles", period + 2) or 0), period + 2):
        _registrar_sinal_estrategia("price_action", None, 0)
        return None

    janela = closed[-period - 1:-1]
    ultimo = closed[-1]
    close = _num(ultimo, "close")
    high_janela = max(_num(c, "high") for c in janela)
    low_janela = min(_num(c, "low") for c in janela)

    condicoes_call = 0
    condicoes_put = 0

    # 1) Tendência: metade final da janela com máximas/mínimas mais altas (alta) ou mais baixas (baixa)
    if cfg.get("detectar_tendencia", True) and len(janela) >= 6:
        metade = len(janela) // 2
        primeira, segunda = janela[:metade], janela[metade:]
        topo1 = max(_num(c, "high") for c in primeira)
        topo2 = max(_num(c, "high") for c in segunda)
        fundo1 = min(_num(c, "low") for c in primeira)
        fundo2 = min(_num(c, "low") for c in segunda)
        if topo2 > topo1 and fundo2 > fundo1:
            condicoes_call += 1
        elif topo2 < topo1 and fundo2 < fundo1:
            condicoes_put += 1

    # 2) Rompimento de máxima/mínima da janela
    if cfg.get("detectar_rompimento", True):
        if close > high_janela and _colour(ultimo) > 0:
            condicoes_call += 1
        elif close < low_janela and _colour(ultimo) < 0:
            condicoes_put += 1

    # 3) Rejeição: pavio longo contra a direção do fechamento, tocando extremo da janela
    if cfg.get("detectar_rejeicao", True):
        corpo = _body(ultimo)
        rng = _range(ultimo) or 1e-9
        pavio_inferior = min(_num(ultimo, "open"), close) - _num(ultimo, "low")
        pavio_superior = _num(ultimo, "high") - max(_num(ultimo, "open"), close)
        if pavio_inferior > 2 * corpo and pavio_inferior / rng > 0.4 and _num(ultimo, "low") <= low_janela * 1.0005:
            condicoes_call += 1
        if pavio_superior > 2 * corpo and pavio_superior / rng > 0.4 and _num(ultimo, "high") >= high_janela * 0.9995:
            condicoes_put += 1

    # 4) Pullback: correção contra a tendência recente seguida de retomada
    if cfg.get("detectar_pullback", True) and len(closed) >= 4:
        anteultimo = closed[-2]
        if (_colour(closed[-3]) > 0 and _colour(anteultimo) < 0 and _colour(ultimo) > 0
                and close > _num(closed[-3], "close")):
            condicoes_call += 1
        if (_colour(closed[-3]) < 0 and _colour(anteultimo) > 0 and _colour(ultimo) < 0
                and close < _num(closed[-3], "close")):
            condicoes_put += 1

    # 5) Máximas/mínimas: fechamento fazendo nova máxima/mínima da janela
    if cfg.get("detectar_extremos", True):
        if close >= high_janela:
            condicoes_call += 1
        if close <= low_janela:
            condicoes_put += 1

    minimo = int(cfg.get("confirmacoes_minimas", 2) or 2)
    direcao = None
    if condicoes_call >= minimo and condicoes_call > condicoes_put:
        direcao = "call"
    elif condicoes_put >= minimo and condicoes_put > condicoes_call:
        direcao = "put"
    if not direcao:
        _registrar_sinal_estrategia("price_action", None, 0)
        return None

    total_condicoes = 5
    confirmadas = condicoes_call if direcao == "call" else condicoes_put
    forca = min(100.0, (confirmadas / total_condicoes) * 100.0 + 20.0)
    if forca < float(cfg.get("forca_minima", 65) or 0) or not _estrategia_direcao_ok(cfg, direcao):
        _registrar_sinal_estrategia("price_action", None, forca)
        return None
    _registrar_sinal_estrategia("price_action", direcao, forca)
    return direcao


_CANDLESTICK_REVERSAO = {
    "candlestick_martelo", "candlestick_estrela_manha", "candlestick_estrela_doji_manha",
    "candlestick_perfurante", "candlestick_bebe_abandonado", "candlestick_fundo_pinca",
    "candlestick_enforcado", "candlestick_estrela_noite", "candlestick_estrela_doji_noite",
    "candlestick_cobertura_nuvem", "candlestick_estrela_cadente", "candlestick_martelo_invertido",
    "candlestick_topo_pinca", "candlestick_no_pescoco", "candlestick_pontape",
    "candlestick_harami", "candlestick_harami_cruzado", "candlestick_engolfo",
    "candlestick_3_soldados_brancos", "candlestick_3_corvos_negros",
}
_CANDLESTICK_CONTINUACAO = {
    "candlestick_3_metodos_alta", "candlestick_3_metodos_baixa",
    "candlestick_lacuna_tasuki_alta", "candlestick_lacuna_tasuki_baixa",
    "candlestick_janela_ascendente", "candlestick_janela_descendente",
    "candlestick_sombra_longa_baixa", "candlestick_sombra_longa_alta", "candlestick_marubozu",
}
_CANDLESTICK_INDECISAO = {
    "candlestick_doji", "candlestick_estrela_doji", "candlestick_doji_libelula",
    "candlestick_doji_lapide", "candlestick_tri_estrela", "candlestick_piao",
}

_estado_candlestick_pendente: Dict[str, Any] = {"direcao": None, "ts_vela": None}


def _candlestick_estrategia_signal(candles: Iterable[Mapping[str, Any]]) -> Optional[str]:
    """Camada de configuração real sobre os 35 padrões de candlestick: aplica
    período/janela, grupos habilitados (reversão/continuação/indecisão),
    força mínima (% de padrões concordando), filtro contra tendência e
    exigência de confirmação no candle seguinte."""
    cfg = _cfg_estrategia("candlestick")
    if not _estrategia_timeframe_ok(cfg):
        return None
    closed = _closed(candles)
    if closed and _eh_doji(closed[-1]):
        _registrar_sinal_estrategia("candlestick", None, 0)
        return None
    period = int(cfg.get("periodo", 20) or 20)
    if len(closed) < max(int(cfg.get("min_candles", period) or 0), 5):
        return None

    janela = closed[-period:] if len(closed) >= period else closed
    if any(_eh_doji(candle) for candle in janela):
        _registrar_sinal_estrategia("candlestick", None, 0)
        return None
    scores = _candlestick_35_scores(janela)

    grupos_ativos = set()
    if cfg.get("detectar_reversao", True):
        grupos_ativos |= _CANDLESTICK_REVERSAO
    if cfg.get("detectar_continuacao", True):
        grupos_ativos |= _CANDLESTICK_CONTINUACAO
    if cfg.get("detectar_indecisao", True):
        grupos_ativos |= _CANDLESTICK_INDECISAO

    ativos = {nome: val for nome, val in scores.items() if val != 0 and nome in grupos_ativos}
    if not ativos:
        _registrar_sinal_estrategia("candlestick", None, 0)
        return None
    calls = sum(1 for v in ativos.values() if v > 0)
    puts = sum(1 for v in ativos.values() if v < 0)
    total = calls + puts
    direcao = "call" if calls > puts else ("put" if puts > calls else None)
    if not direcao:
        _registrar_sinal_estrategia("candlestick", None, 0)
        return None
    confirmados = calls if direcao == "call" else puts
    if confirmados < int(cfg.get("confirmacoes_minimas", 1) or 1):
        _registrar_sinal_estrategia("candlestick", None, 0)
        return None
    forca = (confirmados / total) * 100.0

    # Filtro contra tendência: bloqueia padrão de continuação que aponta contra a tendência da janela
    if cfg.get("filtrar_contra_tendencia", True) and len(janela) >= 6:
        closes = [_num(c, "close") for c in janela]
        tendencia = "call" if closes[-1] > closes[0] else ("put" if closes[-1] < closes[0] else None)
        eh_continuacao = any(nome in _CANDLESTICK_CONTINUACAO for nome, v in ativos.items()
                              if (v > 0) == (direcao == "call"))
        if eh_continuacao and tendencia and tendencia != direcao:
            _registrar_sinal_estrategia("candlestick", None, forca)
            return None

    if forca < float(cfg.get("forca_minima", 60) or 0) or not _estrategia_direcao_ok(cfg, direcao):
        _registrar_sinal_estrategia("candlestick", None, forca)
        return None

    # Exigir confirmação do candle seguinte: só libera o sinal depois que a
    # MESMA direção apareceu no candle fechado anterior também.
    if cfg.get("confirmar_candle_seguinte", True):
        vela_atual_ts = closed[-1].get("from") or closed[-1].get("id") or len(closed)
        pendente = _estado_candlestick_pendente
        if pendente.get("direcao") == direcao:
            pendente["direcao"] = None
            pendente["ts_vela"] = None
        else:
            pendente["direcao"] = direcao
            pendente["ts_vela"] = vela_atual_ts
            _registrar_sinal_estrategia("candlestick", None, forca)
            return None

    _registrar_sinal_estrategia("candlestick", direcao, forca)
    return direcao


def _resolve_combined(name: str, signals: Dict[str, Optional[str]]) -> Optional[str]:
    def agree(names: List[str], minimum: int = 2) -> Optional[str]:
        vals = [signals.get(n) for n in names]
        vals = [v for v in vals if v]
        if len(vals) < minimum:
            return None
        calls, puts = vals.count("call"), vals.count("put")
        if calls == puts:
            return None
        return "call" if calls > puts else "put"

    if name == "Torres Gêmeas / 3x1":
        return agree(["Torres Gêmeas", "Três Vizinhos"], 2)
    if name == "Triplicação / Torres Gêmeas":
        return agree(["Torres Gêmeas", "Três Vizinhos"], 2)
    if name == "Five Flip / Não Triplicação":
        five = signals.get("Five Flip")
        return five if five and not signals.get("Três Vizinhos") else None
    if name == "Five Flip / Torres Gêmeas":
        return agree(["Five Flip", "Torres Gêmeas"], 2)
    if name == "Três Vizinhos / Torres Gêmeas":
        return agree(["Três Vizinhos", "Torres Gêmeas"], 2)
    return None


def _mhi_sinal(candles: Iterable[Mapping[str, Any]]) -> Optional[str]:
    """Implementa o MHI do aula5.py usando os três últimos candles fechados.

    Se houver Doji, a entrada é abortada. Caso contrário, a direção é contrária
    à maioria: maioria verde gera PUT e maioria vermelha gera CALL.
    """
    data = list(candles or [])
    if len(data) < 3:
        return None
    ultimas = data[-3:]
    verdes = 0
    vermelhas = 0
    for vela in ultimas:
        try:
            abertura = float(vela.get("open", 0.0))
            fechamento = float(vela.get("close", 0.0))
        except (AttributeError, TypeError, ValueError):
            return None
        if fechamento > abertura:
            verdes += 1
        elif fechamento < abertura:
            vermelhas += 1
        else:
            return None
    if verdes > vermelhas:
        return "put"
    if vermelhas > verdes:
        return "call"
    return None


class CatalogoEstrategias:
    """Implementa o catálogo de estratégias e a camada de seleção."""

    @staticmethod
    def sinal(nome: str, candles: Iterable[Mapping[str, Any]]) -> Optional[str]:
        closed = _closed(candles)
        # Um Doji em qualquer uma das cinco velas fechadas de confirmação
        # invalida a estratégia, e não apenas um Doji na vela final.
        if any(_eh_doji(candle) for candle in closed[-5:]):
            return None
        if nome == "Milhão Maioria": return _milhao(closed, False)
        if nome == "Milhão Minoria": return _milhao(closed, True)
        if nome == "R7": return _majority(_colours(closed[-7:])) if len(closed) >= 7 else None
        if nome == "Padrão Ímpar": return _padrao_impar(closed)
        if nome == "Melhor de 3": return _melhor_de_3(closed)
        if nome == "Padrão 23": return _padrao_23(closed)
        if nome == "Gaba": return _gaba(closed)
        if nome == "Torres Gêmeas": return _torres_gemeas(closed)
        if nome == "Três Mosqueteiros": return _tres_mosqueteiros(closed)
        if nome == "Três Vizinhos": return _tres_vizinhos(closed)
        if nome == "Turn Over": return _turn_over(closed)
        if nome == "Seven Flip": return _flip(closed, 7)
        if nome == "Reversão": return _reversao(closed)
        if nome == "Five Flip": return _flip(closed, 5)
        if nome == "MHI": return _mhi_sinal(closed)
        if nome in CATALOG_COMBINED_STRATEGIES:
            signals = CatalogoEstrategias.gerar_sinais(candles, CATALOG_BASE_STRATEGIES)
            return _resolve_combined(nome, signals)
        return None

    @staticmethod
    def gerar_sinais(candles: Iterable[Mapping[str, Any]], selecionadas: Optional[Iterable[str]] = None) -> Dict[str, str]:
        nomes = list(selecionadas) if selecionadas is not None else list(CATALOG_STRATEGIES)
        nomes = list(dict.fromkeys(nomes))
        # Estratégias combinadas dependem de bases que podem não estar marcadas
        # individualmente na interface. Calculamos as dependências em separado,
        # mas devolvemos somente as estratégias solicitadas pelo usuário.
        dependencias = {
            "Torres Gêmeas / 3x1": ["Torres Gêmeas", "Três Vizinhos"],
            "Triplicação / Torres Gêmeas": ["Torres Gêmeas", "Três Vizinhos"],
            "Five Flip / Não Triplicação": ["Five Flip", "Três Vizinhos"],
            "Five Flip / Torres Gêmeas": ["Five Flip", "Torres Gêmeas"],
            "Três Vizinhos / Torres Gêmeas": ["Três Vizinhos", "Torres Gêmeas"],
        }
        nomes_calculo = list(nomes)
        for nome in nomes:
            for dep in dependencias.get(nome, []):
                if dep not in nomes_calculo:
                    nomes_calculo.append(dep)
        base_sinais: Dict[str, str] = {}
        for nome in nomes_calculo:
            if nome in CATALOG_BASE_STRATEGIES or nome == "R7":
                sig = CatalogoEstrategias.sinal(nome, candles)
                if sig:
                    base_sinais[nome] = sig
        saida: Dict[str, str] = {nome: base_sinais[nome] for nome in nomes if nome in base_sinais}
        for nome in nomes:
            if nome in CATALOG_COMBINED_STRATEGIES:
                sig = _resolve_combined(nome, base_sinais)
                if sig:
                    saida[nome] = sig
        return saida

    @staticmethod
    def voto(candles: Iterable[Mapping[str, Any]], selecionadas: Optional[Iterable[str]] = None) -> Dict[str, Any]:
        sinais = CatalogoEstrategias.gerar_sinais(candles, selecionadas)
        calls = [n for n, s in sinais.items() if s == "call"]
        puts = [n for n, s in sinais.items() if s == "put"]
        if len(calls) > len(puts):
            direcao = "call"
        elif len(puts) > len(calls):
            direcao = "put"
        else:
            direcao = None
        return {
            "sinais": sinais,
            "calls": calls,
            "puts": puts,
            "direcao": direcao,
            "confluencias": max(len(calls), len(puts)),
            "total": len(sinais),
        }

    @staticmethod
    def catalogar(candles: Iterable[Mapping[str, Any]], selecionadas: Optional[Iterable[str]] = None) -> Dict[str, int]:
        """Calcula uma assertividade histórica simples sem acessar a corretora."""
        data = list(candles or [])
        nomes = list(selecionadas) if selecionadas is not None else CATALOG_STRATEGIES
        acertos = {n: 0 for n in nomes}
        tentativas = {n: 0 for n in nomes}
        for i in range(8, len(data) - 1):
            janela = data[:i]
            sinais = CatalogoEstrategias.gerar_sinais(janela, nomes)
            resultado = _colour(data[i])
            if resultado == 0:
                continue
            for nome, sinal in sinais.items():
                tentativas[nome] += 1
                if (sinal == "call" and resultado > 0) or (sinal == "put" and resultado < 0):
                    acertos[nome] += 1
        return {n: round(100 * acertos[n] / tentativas[n]) if tentativas[n] else 0 for n in nomes}

# ============================================================
# NOTÍCIAS E GERENCIAMENTO SOROS — INTEGRADOS NO BACKEND
# ============================================================
class GerenciadorNoticias:
    """Gerencia notícias econômicas em tempo real"""
    
    def __init__(self):
        self.noticias = []
        self.ultima_atualizacao = 0
        self.intervalo_atualizacao = 60  # segundos
        
        # Notícias simuladas baseadas em eventos reais para demonstração
        # Em um cenário real, isso viria de um scraper ou API de notícias (Investing.com etc.)
        self.noticias_base = [
            {"moeda": "USD", "titulo": "Dados de Emprego nos EUA", "impacto": "Alto", "horario": "15:30"},
            {"moeda": "EUR", "titulo": "Discurso do Presidente do BCE", "impacto": "Alto", "horario": "16:00"},
            {"moeda": "GBP", "titulo": "PIB Trimestral", "impacto": "Alto", "horario": "10:30"},
            {"moeda": "JPY", "titulo": "Decisão de Taxa de Juros", "impacto": "Alto", "horario": "04:00"},
            {"moeda": "AUD", "titulo": "Vendas no Varejo", "impacto": "Médio", "horario": "02:30"},
            {"moeda": "CAD", "titulo": "Taxa de Desemprego", "impacto": "Médio", "horario": "15:30"},
            {"moeda": "CHF", "titulo": "Inflação CPI", "impacto": "Baixo", "horario": "08:00"},
            {"moeda": "NZD", "titulo": "Confiança do Consumidor", "impacto": "Baixo", "horario": "21:00"},
        ]
        self.atualizar_lista_fake()

    def atualizar_lista_fake(self):
        """Gera notícias dinâmicas para o dia atual"""
        agora = _agora_brasilia()
        self.noticias = []
        for i, base in enumerate(self.noticias_base):
            h, m = map(int, base["horario"].split(":"))
            horario_dt = agora.replace(hour=h, minute=m, second=0, microsecond=0)
            
            # Se a notícia já passou há muito tempo, move para amanhã ou ajusta
            if (agora - horario_dt).total_seconds() > 3600 * 4:
                horario_dt += timedelta(days=1)
            
            tempo_restante_seg = (horario_dt - agora).total_seconds()
            
            status = "Em breve"
            if tempo_restante_seg < 0 and tempo_restante_seg > -600:
                status = "Ao vivo"
            elif tempo_restante_seg <= -600:
                status = "Finalizada"
                
            self.noticias.append({
                "id": i + 1,
                "moeda": base["moeda"],
                "titulo": base["titulo"],
                "impacto": base["impacto"],
                "horario": horario_dt.strftime("%H:%M"),
                "hora": horario_dt.strftime("%H:%M"),
                "status": status,
                "tempo_restante": max(0, int(tempo_restante_seg)),
                "timestamp": horario_dt.timestamp()
            })

    def get_status(self) -> Dict:
        self.atualizar_lista_fake()
        proximas = [n for n in self.noticias if n["status"] == "Em breve"]
        em_andamento = [n for n in self.noticias if n["status"] == "Ao vivo"]
        finalizadas = [n for n in self.noticias if n["status"] == "Finalizada"]
        
        return {
            "proximas": sorted(proximas, key=lambda x: x["tempo_restante"]),
            "em_andamento": em_andamento,
            "finalizadas": sorted(finalizadas, key=lambda x: x["timestamp"], reverse=True),
            "total": len(self.noticias)
        }

    def verificar_bloqueio(self, ativo: str, tempo_antes: int = 15, tempo_depois: int = 15) -> (bool, str):
        """Verifica se deve bloquear operações para o ativo devido a notícias de alto impacto"""
        moeda = ativo[:3].upper()
        agora = time.time()
        
        for n in self.noticias:
            if n["impacto"] == "Alto" and n["moeda"] == moeda:
                inicio = n["timestamp"] - (tempo_antes * 60)
                fim = n["timestamp"] + (tempo_depois * 60)
                
                if inicio <= agora <= fim:
                    return True, n["titulo"]
        return False, ""

class GerenciadorSoros:
    """Mantém o estado Soros independente do estado Martingale.

    ``nivel_atual`` é o nível da próxima entrada: zero é a entrada base e os
    níveis de 1 até ``niveis`` são as entradas Soros. O último nível é
    considerado concluído somente depois que a entrada daquele nível vence.
    """

    def __init__(self):
        self.ativo = False
        self.niveis = 3
        self.reinvestimento = 100
        self.nivel_atual = 0
        self.lucro_sequencia = 0.0
        self.lucro_acumulado = 0.0
        self.total_sequencias = 0
        self.historico = []
        self.ultimo_valor_utilizado = None
        self.ultima_porcentagem = None
        self.ultimo_resultado = None
        self._operacoes_processadas = set()
        self._lock = threading.RLock()

    def configurar(self, ativo: bool, niveis: int, reinvestimento: int):
        ativo = bool(ativo)
        niveis = max(1, min(int(niveis), 10))
        reinvestimento = max(0, min(int(reinvestimento), 100))
        with self._lock:
            mudou = (self.ativo != ativo or self.niveis != niveis or self.reinvestimento != reinvestimento)
            self.ativo = ativo
            self.niveis = niveis
            self.reinvestimento = reinvestimento
            if mudou:
                self.resetar_sequencia()
            if not self.ativo:
                self.resetar_sequencia()

    def ativar_soros(self, niveis: int, reinvestimento: int):
        self.configurar(True, niveis, reinvestimento)

    def calcular_valor_entrada(self, valor_base: float) -> float:
        with self._lock:
            if not self.ativo or self.nivel_atual <= 0:
                valor = round(float(valor_base), 2)
                pct_aplicado = 0
            else:
                adicional = self.lucro_sequencia * (self.reinvestimento / 100.0)
                valor = round(float(valor_base) + adicional, 2)
                pct_aplicado = self.reinvestimento
            self.ultimo_valor_utilizado = valor
            self.ultima_porcentagem = pct_aplicado
            return valor

    def registrar_resultado(self, ganhou: bool, lucro: float, operacao_id=None, nivel_executado=None):
        """Processa exatamente uma vez o resultado de uma operação.

        O Soros avança em qualquer WIN, inclusive WIN de uma entrada
        Martingale. Em qualquer LOSS ele volta ao nível zero. A decisão de
        qual valor enviar continua sendo feita separadamente pelo Martingale.
        """
        with self._lock:
            chave = str(operacao_id) if operacao_id is not None else None
            if chave and chave in self._operacoes_processadas:
                return False
            if chave:
                self._operacoes_processadas.add(chave)
            self.ultimo_resultado = "win" if ganhou else "loss"
            if not self.ativo:
                return True
            nivel = self.nivel_atual if nivel_executado is None else max(0, int(nivel_executado))
            lucro = float(lucro or 0.0)
            if ganhou:
                self.lucro_sequencia += lucro
                self.lucro_acumulado += lucro
                if nivel >= self.niveis:
                    self.finalizar_sequencia("Sucesso", nivel)
                else:
                    self.nivel_atual = nivel + 1
            else:
                self.finalizar_sequencia("Derrota", nivel)
            return True

    def finalizar_sequencia(self, status: str, nivel_final=None):
        nivel_registrado = self.nivel_atual if nivel_final is None else int(nivel_final)
        self.historico.append({
            "sequencia": self.total_sequencias + 1,
            "niveis": nivel_registrado,
            "lucro": round(self.lucro_sequencia, 2),
            "porcentagem": self.reinvestimento,
            "status": status,
            "timestamp": _agora_brasilia().strftime("%H:%M:%S")
        })
        self.total_sequencias += 1
        self.resetar_sequencia()

    def resetar_sequencia(self):
        self.nivel_atual = 0
        self.lucro_sequencia = 0.0
        self.ultimo_valor_utilizado = None
        self.ultima_porcentagem = None

    def get_status(self) -> Dict:
        with self._lock:
            return {
                "ativo": self.ativo,
                "nivel_atual": self.nivel_atual,
                "niveis_totais": self.niveis,
                "reinvestimento": self.reinvestimento,
                "lucro_sequencia": round(self.lucro_sequencia, 2),
                "lucro_acumulado": round(self.lucro_acumulado, 2),
                "total_sequencias": self.total_sequencias,
                "ultimo_valor_utilizado": self.ultimo_valor_utilizado,
                "ultima_porcentagem": self.ultima_porcentagem,
                "ultimo_resultado": self.ultimo_resultado,
                "historico": self.historico[-5:]
            }


class GerenciadorMartingale:
    """Máquina de estados do Martingale, separada do Soros.

    O nível só muda quando o resultado de uma operação LOSS é confirmado. O
    valor do próximo nível é calculado a partir do valor efetivamente perdido,
    impedindo saltos, duplicações ou divergência entre tela e ordem enviada.
    """

    def __init__(self):
        self.ativo = False
        self.valor_inicial = 5.0
        self.valor_atual = 5.0
        self.nivel_atual = 0
        self.niveis_maximos = 2
        self.fator = 2.2
        self.modo = "proxima_vela"
        self.ultimo_resultado = None
        self.ultima_operacao_id = None
        self.ultima_operacao_em = None
        self.proxima_entrada_autorizada = None
        self.ativo_origem = None
        self.direcao_origem = None
        self.tf_origem = None
        self.vela_origem = None
        self._operacoes_processadas = set()
        self._lock = threading.RLock()

    def configurar(self, ativo, valor_inicial, fator, niveis, modo):
        ativo = bool(ativo)
        valor_inicial = max(0.01, float(valor_inicial or 0.01))
        fator = max(1.0, float(fator or 1.0))
        niveis = max(0, min(int(niveis or 0), 10))
        modo = modo if modo in ("proxima_vela", "proximo_sinal") else "proxima_vela"
        with self._lock:
            mudou = (self.ativo != ativo or self.valor_inicial != valor_inicial or
                     self.fator != fator or self.niveis_maximos != niveis or self.modo != modo)
            self.ativo = ativo
            self.valor_inicial = valor_inicial
            self.fator = fator
            self.niveis_maximos = niveis
            self.modo = modo
            if mudou or not ativo:
                self.resetar()

    def resetar(self):
        self.valor_atual = self.valor_inicial
        self.nivel_atual = 0
        self.ultimo_resultado = None
        self.ultima_operacao_id = None
        self.ultima_operacao_em = None
        self.proxima_entrada_autorizada = None
        self.ativo_origem = None
        self.direcao_origem = None
        self.tf_origem = None
        self.vela_origem = None

    def registrar_entrada(self, operacao_id, valor, ativo, direcao, tf_seg, vela_entrada):
        with self._lock:
            self.ultima_operacao_id = str(operacao_id) if operacao_id is not None else None
            self.ultima_operacao_em = time.time()
            self.valor_atual = round(float(valor), 2)
            self.ativo_origem = ativo
            self.direcao_origem = str(direcao or "").lower()
            self.tf_origem = int(tf_seg or 60)
            self.vela_origem = int(vela_entrada or 0)
            self.proxima_entrada_autorizada = "resultado_confirmado"

    def registrar_resultado(self, ganhou, lucro, operacao_id, valor_utilizado, ativo, direcao, tf_seg, vela_entrada):
        with self._lock:
            chave = str(operacao_id) if operacao_id is not None else None
            if chave and chave in self._operacoes_processadas:
                return {"duplicado": True, "nivel": self.nivel_atual}
            if chave:
                self._operacoes_processadas.add(chave)
            self.ultimo_resultado = "win" if ganhou else ("loss" if float(lucro or 0) < 0 else "empate")
            self.ultima_operacao_id = chave
            self.ultima_operacao_em = time.time()
            if not self.ativo or self.niveis_maximos <= 0:
                self.resetar()
                return {"duplicado": False, "acao": "reset", "nivel": 0}
            if ganhou:
                self.resetar()
                return {"duplicado": False, "acao": "reset", "nivel": 0}
            if self.ultimo_resultado != "loss":
                return {"duplicado": False, "acao": "aguardar", "nivel": self.nivel_atual}
            if self.nivel_atual >= self.niveis_maximos:
                self.resetar()
                return {"duplicado": False, "acao": "limite_atingido", "nivel": 0}
            self.nivel_atual += 1
            self.valor_atual = round(max(0.01, float(valor_utilizado)) * self.fator, 2)
            self.ativo_origem = ativo
            self.direcao_origem = str(direcao or "").lower()
            self.tf_origem = int(tf_seg or 60)
            self.vela_origem = int(vela_entrada or 0)
            self.proxima_entrada_autorizada = self.modo
            return {
                "duplicado": False,
                "acao": "aguardar_sinal" if self.modo == "proximo_sinal" else "proxima_vela",
                "nivel": self.nivel_atual,
                "valor": self.valor_atual,
            }

    def get_status(self):
        with self._lock:
            return {
                "ativo": self.ativo,
                "valor_inicial": round(self.valor_inicial, 2),
                "valor_atual": round(self.valor_atual, 2),
                "nivel_atual": self.nivel_atual,
                "niveis_maximos": self.niveis_maximos,
                "fator": self.fator,
                "modo": self.modo,
                "ultimo_resultado": self.ultimo_resultado,
                "ultima_operacao_id": self.ultima_operacao_id,
                "ultima_operacao_em": self.ultima_operacao_em,
                "proxima_entrada_autorizada": self.proxima_entrada_autorizada,
                "ativo_origem": self.ativo_origem,
                "direcao_origem": self.direcao_origem,
                "tf_origem": self.tf_origem,
                "vela_origem": self.vela_origem,
            }


# Instâncias globais — Soros e Martingale são independentes e podem operar juntos.
gerenciador_noticias = GerenciadorNoticias()
gerenciador_soros = GerenciadorSoros()
gerenciador_martingale = GerenciadorMartingale()

# ============================================================
# NÚCLEO DO ROBÔ E ROTAS DA API
# ============================================================

app = Flask(__name__)
app.logger.disabled = True

# Proteção opcional da API do Backend. As credenciais da IQ Option continuam
# sendo recebidas pelo endpoint /api/login e não são armazenadas nesta camada.
# O campo do Backend é opcional: sem valor, a API funciona normalmente. Quando
# preenchido, o valor precisa corresponder ao resumo abaixo.
_BACKEND_PASSWORD_DIGEST = "bf78c5d8612b1ce0eee3a6e5125ecf4cfc5e0d09006c188b742140107ef4350c"


def _backend_access_authorized(provided=None):
    candidate = request.headers.get("X-Backend-Password", "") if provided is None else str(provided)
    candidate = candidate.strip()
    if not candidate:
        return True
    digest = hashlib.sha256(candidate.encode("utf-8")).hexdigest()
    return hmac.compare_digest(digest, _BACKEND_PASSWORD_DIGEST)


@app.before_request
def _require_backend_access():
    if request.path.startswith("/api/") and not _backend_access_authorized():
        return jsonify({
            "ok": False,
            "msg": "Senha do Backend ausente ou inválida",
            "backend_password_required": True,
        }), 401
    return None


CORS(app, origins="*")
socketio = SocketIO(app, cors_allowed_origins="*", async_mode="threading", logger=False, engineio_logger=False)

@app.errorhandler(Exception)
def _tratar_erro_global(e):
    """Garante que QUALQUER exceção não tratada num endpoint /api/* devolva JSON
    em vez da página HTML padrão do Flask — evita que o frontend receba um 500
    HTML, falhe o .json() e mostre o "Erro de conexão" genérico sem pista nenhuma
    do motivo real. Registra o erro no log do scanner para diagnóstico."""
    try:
        _log_scan(f"⚠️ Erro não tratado em {request.path}: {e}")
    except Exception:
        pass
    return jsonify({"ok": False, "erro": str(e), "msg": str(e)}), 500

STATE = {
    "api": None,
    "conectado": False,
    "tipo_conta": "PRACTICE",
    "email": "",
    "saldo": 0.0,
    "saldo_inicial": 0.0,
    "running": False,
    "wins": 0,
    "losses": 0,
    "empates": 0,
    "saldo_acumulado": 0.0,
    "lucro_bruto": 0.0,
    "prejuizo_bruto": 0.0,
    "data_operacoes": str(_data_brasilia()),
    "historico": [],
    "ultima_operacao": None,
    "operacao_atual": None,
    "gale_atual": {},
    "direcao_gale": {},
    "tf_gale": {},
    "gale_pendente": None,
    "martingale_state": None,
    "valor_gale_base": {},
    "cooldown": {},
    "scan_log": [],
    "ciclo_ativos": [],
    # Par canônico compartilhado entre scanner, sentimento e painel de confluência.
    "ativo_em_foco": None,
    "inicio_sessao": None,
    "ativos_abertos": {},
    "ultimo_refresh_ativos": 0,
    "modo_otc": False,
    "valor_entrada": 5.0,
    "usar_gale": True,
    "niveis_gale": 2,
    "fator_gale": 2.2,
    "atraso_martingale_segundos": 0,
    "martingale_modo": "proxima_vela",
    "stop_win": 100.0,
    "stop_loss": 100.0,
    # Pausa por losses seguidos: após N ciclos encerrados em LOSS (contando
    # o ciclo completo, não cada perna do Gale), o scanner para de abrir
    # novas entradas por M minutos — padrão comum de gestão de risco para
    # evitar "revenge trade" após sequência negativa. 0 desativa a pausa.
    "losses_seguidos_limite": 3,
    "losses_seguidos_pausa_min": 30,
    "losses_seguidos_atual": 0,
    "pausa_losses_ate": 0.0,
    "limite_diario": 1000,
    "expiracao": 1,  # timeframe selecionado para candles e expiração (1, 5 ou 15)
    "ativo_manual": "EURUSD",
    "modo_auto": True,
    # Modo exclusivo: nenhuma estratégia embutida é consultada.
    "script_lua": "",
    "script_lua_autorizado": False,
    "script_lua_erro": "Nenhum script Lua Quadcode autorizado.",
    "modalidade": "ambas",
    "horario_inicio": "00:00",
    "horario_fim": "23:59",
    # TTZ segue o modelo do Xbot: zonas por cor, ação PAUSE/ALLOW e filtro opcional por moeda.
    "ttz_ativo": False,
    "ttz_time_action": "PAUSE",
    "ttz_filter_by_currency": False,
    "ttz_selected_zones": ["Events Zone", "Wine Zone"],
    "ttz_blocked_zones": ["Events Zone", "Wine Zone"],
    "ttz_schedule": [],
    "ttz_events": [],
    "ttz_last_update": 0,
    "ttz_market_token": "",
    "ttz_market_payload": None,
    "ttz_market_received_at": 0,
    "ttz_refresh_seconds": 60,
    "ttz_error": "",
    "ttz_session_cookie": "",
    "ttz_session_email": "",
    "ttz_session_updated_at": 0,
    "ttz_source": "",
    "max_gale": 2,
    "total_operacoes": 0,
    "pares_scan": 0,
    "cache_ativos": None,
    "session_id": 0,
    "usar_soros": False,
    "niveis_soros": 3,
    "reinvestimento_soros": 100,
    "soros_status": None,
    "usar_price_action": True,
    "usar_indicadores": True,
    "usar_top5_indicadores": True,
    "min_indicadores_confluencia": 10,
    "usar_rsi": True,
    "usar_aroon": True,
    "usar_darvas": True,
    "usar_suporte_resistencia": True,
    "usar_fibonacci": True,
    "usar_fluxo": True,
    "usar_efectiv": True,
    "usar_lta_ltb": True,
    "usar_order_flow": True,
    "usar_persistencia": True,
    "usar_vacuo": True,
    "usar_sentimento": False,
    "sentimento_traders": {
        "ativo": None, "call_pct": None, "put_pct": None, "sinal": 0,
        "forca": 0.0, "direcao": None, "status": "aguardando conexão",
        "atualizado_em": 0.0,
    },
    "sentimento_traders_ultimo_refresh": 0.0,
    "usar_filtros_pro": True,
    "usar_exaustao": True,
    "usar_ruido": True,
    "bloquear_por_noticias": True,
    "noticias_ativas": True,
    "tempo_antes_noticia": 5,
    "tempo_depois_noticia": 5,
    # Catálogo de estratégias: todas as estratégias de sequências e combinações ficam
    # ativas por padrão; a interface pode enviar uma seleção reduzida.
    "usar_catalogo": True,
    "catalogo_estrategias": list(CATALOG_STRATEGIES),
    "catalogo_ultimo_voto": {},
    # Configuração individual por estratégia (1ª leva: candlestick, price action
    # e os 5 indicadores técnicos + Efectiv V2). Cada chave é o id da estratégia
    # e o valor um dict que sobrescreve ESTRATEGIA_CONFIG_DEFAULTS.
    "config_estrategias": {},
    "ultimo_sinal_estrategia": {},
    "confluencia_estrategias": {
        "ativo": None, "timeframe": "", "direcao": None,
        "estrategias": [], "call": [], "put": [], "total": 0,
        "minimo": 5, "aprovada": False, "atualizado_em": 0.0,
    },
}

_ttz_load_cached_market()

_historico_ia: dict = {}
_JANELA_IA = 50
_pesos_ia: dict = {}

def ia_registrar(estado, ganhou):
    if estado not in _historico_ia:
        _historico_ia[estado] = deque(maxlen=_JANELA_IA)
    _historico_ia[estado].append(1 if ganhou else 0)

def ia_confianca(estado):
    hist = _historico_ia.get(estado)
    if not hist or len(hist) < 3:
        return 0.5
    return sum(hist) / len(hist)

def _atualizar_pesos_ia(estado, ganhou, fatores_scores):
    if estado not in _pesos_ia:
        _pesos_ia[estado] = {k: 1.0 for k in fatores_scores.keys()}
    
    for fator, score in fatores_scores.items():
        if fator not in _pesos_ia[estado]:
            _pesos_ia[estado][fator] = 1.0
        
        if ganhou and score > 0:
            _pesos_ia[estado][fator] = min(3.0, _pesos_ia[estado][fator] + 0.15)
        elif not ganhou and score > 0:
            _pesos_ia[estado][fator] = max(0.2, _pesos_ia[estado][fator] - 0.10)
        elif ganhou and score < 0:
            _pesos_ia[estado][fator] = max(0.2, _pesos_ia[estado][fator] - 0.05)
        elif not ganhou and score < 0:
            _pesos_ia[estado][fator] = min(3.0, _pesos_ia[estado][fator] + 0.05)

def _calcular_score_ia(estado, fatores_scores):
    confianca = ia_confianca(estado)
    pesos = _pesos_ia.get(estado, {k: 1.0 for k in fatores_scores.keys()})

    votos_call = 0.0
    votos_put = 0.0
    score_total = 0.0
    for fator, score in fatores_scores.items():
        peso = pesos.get(fator, 1.0)
        contrib = score * peso
        score_total += contrib
        if contrib > 0:
            votos_call += contrib
        elif contrib < 0:
            votos_put += abs(contrib)

    if confianca >= 0.60:
        score_total += 2.0
    elif confianca >= 0.50:
        score_total += 0.5

    if votos_call > votos_put:
        direcao = 'call'
    elif votos_put > votos_call:
        direcao = 'put'
    else:
        direcao = None

    return score_total, confianca, direcao

def _log_scan(msg):
    ts = _agora_brasilia().strftime("%H:%M:%S")
    entrada = f"[{ts}] {msg}"
    STATE["scan_log"].insert(0, entrada)
    STATE["scan_log"] = STATE["scan_log"][:200]
    print(entrada)

def _verificar_reset_diario():
    hoje = str(_data_brasilia())
    if STATE.get("data_operacoes") != hoje:
        STATE["data_operacoes"] = hoje
        STATE["total_operacoes"] = 0
        _log_scan("🔄 Novo dia detectado — limite diário de operações resetado.")

def _parse_binary_cache(data):
    """Converte o retorno de inicialização em um mapa completo Binary/Turbo.

    O mapa preserva ativos fechados, pois a interface precisa mostrar todo o
    catálogo e informar separadamente se cada modalidade está aberta.
    """
    open_time = {}
    if not isinstance(data, dict):
        return open_time
    raiz = data.get("result") if isinstance(data.get("result"), dict) else data
    for modalidade in ("binary", "turbo"):
        secao = raiz.get(modalidade, {}) if isinstance(raiz, dict) else {}
        ativos = secao.get("actives", {}) if isinstance(secao, dict) else {}
        if not isinstance(ativos, dict):
            continue
        for ativo_id, ativo in ativos.items():
            if not isinstance(ativo, dict):
                continue
            bruto = str(ativo.get("name") or "").strip()
            nome = bruto.split(".", 1)[1] if "." in bruto else bruto
            if not nome:
                continue
            aberto = bool(ativo.get("enabled")) and not bool(ativo.get("is_suspended", False))
            open_time.setdefault(modalidade, {})[nome] = {
                "open": aberto,
                "active_id": int(ativo_id) if str(ativo_id).isdigit() else None,
            }
    return open_time

def _get_cache_from_library(api):
    ws = getattr(api, 'api', None)
    if not ws:
        return {}
    try:
        data = getattr(ws, 'api_option_init_all_result_v2', None)
        if isinstance(data, dict) and len(data) > 0:
            return _parse_binary_cache(data)
    except Exception:
        pass
    try:
        data = getattr(ws, 'api_option_init_all_result', None)
        if isinstance(data, dict):
            return _parse_binary_cache(data)
    except Exception:
        pass
    return {}

def safe_get_all_open_time(api):
    cached = STATE.get("ativos_abertos")
    if cached and isinstance(cached, dict):
        has_data = any(
            isinstance(cached.get(cat, {}), dict) and len(cached.get(cat, {})) > 0
            for cat in ('turbo', 'binary', 'digital')
        )
        if has_data:
            return cached
    return _get_cache_from_library(api)

_CACHE_ABERTOS_TTL = 60

def _refresh_ativos_abertos(api, force=False):
    agora = time.time()
    cache_valido = (agora - STATE.get("ultimo_refresh_ativos", 0) < _CACHE_ABERTOS_TTL)
    if not force and cache_valido and STATE.get("ativos_abertos"):
        return STATE["ativos_abertos"]
    dados = safe_get_all_open_time(api)
    if dados and isinstance(dados, dict) and any(v for v in dados.values() if isinstance(v, dict)):
        STATE["ativos_abertos"] = dados
        STATE["ultimo_refresh_ativos"] = agora
        total = sum(len(v) for v in dados.values() if isinstance(v, dict))
        _log_scan(f"📡 Cache de ativos abertos atualizado: {total} ativos")
    return STATE.get("ativos_abertos", {})

def _resolver_active_id(ativo, modalidade=None):
    """Resolve o ID dinâmico do ativo; evita depender apenas de constantes antigas."""
    alvo = str(ativo or "").strip()
    if not alvo:
        return None
    try:
        if alvo.isdigit():
            return int(alvo)
    except Exception:
        pass
    dados = STATE.get("ativos_abertos") or {}
    base = alvo.upper()
    for sufixo in ("-OP", ":N", "-Z", "_OTC", "-OTC"):
        base = base.replace(sufixo, "")
    nomes = [alvo, alvo.upper(), base, f"{base}-OTC", f"{base}_OTC", f"{base}-OP"]
    categorias = _categorias_da_modalidade(modalidade) if modalidade else ("binary", "turbo")
    for categoria in categorias:
        secao = dados.get(categoria, {})
        if not isinstance(secao, dict):
            continue
        for nome in nomes:
            detalhe = secao.get(nome)
            if isinstance(detalhe, dict) and detalhe.get("active_id") is not None:
                try:
                    return int(detalhe["active_id"])
                except (TypeError, ValueError):
                    pass
    # O método get_all_open_time() pode devolver somente open/closed, sem ID.
    # Nesse caso, consulta o payload bruto já recebido no login, sem fazer uma
    # nova requisição por ativo.
    try:
        api = STATE.get("api")
        ws = getattr(api, "api", None)
        for atributo in ("api_option_init_all_result_v2", "api_option_init_all_result"):
            bruto = getattr(ws, atributo, None) if ws else None
            raiz = bruto.get("result") if isinstance(bruto, dict) and isinstance(bruto.get("result"), dict) else bruto
            for categoria in categorias:
                secao = raiz.get(categoria, {}) if isinstance(raiz, dict) else {}
                ativos = secao.get("actives", {}) if isinstance(secao, dict) else {}
                if not isinstance(ativos, dict):
                    continue
                for ativo_id, detalhe in ativos.items():
                    if not isinstance(detalhe, dict):
                        continue
                    bruto_nome = str(detalhe.get("name") or "").strip()
                    nome = bruto_nome.split(".", 1)[1] if "." in bruto_nome else bruto_nome
                    if nome in nomes or nome.upper() in {item.upper() for item in nomes}:
                        if str(ativo_id).isdigit():
                            return int(ativo_id)
    except Exception:
        pass
    try:
        from iqoptionapi.constants import ACTIVES
        # A biblioteca pode registrar o mesmo ativo com capitalização diferente
        # após uma reconexão (por exemplo, EURUSD-op versus EURUSD-OP).
        valor = ACTIVES.get(alvo)
        if valor is None:
            valor = ACTIVES.get(alvo.upper())
        if valor is None:
            alvo_cf = alvo.casefold()
            for nome_const, id_const in ACTIVES.items():
                if str(nome_const).strip().casefold() == alvo_cf:
                    valor = id_const
                    break
        return int(valor) if valor is not None else None
    except Exception:
        return None

def _catalogo_binario_turbo(dados=None):
    """Retorna todos os ativos conhecidos, com disponibilidade por modalidade."""
    dados = dados if isinstance(dados, dict) else STATE.get("ativos_abertos") or {}
    catalogo = {}
    for modalidade in ("binary", "turbo"):
        secao = dados.get(modalidade, {})
        if not isinstance(secao, dict):
            continue
        for nome, detalhe in secao.items():
            nome = str(nome or "").strip()
            if not nome:
                continue
            item = catalogo.setdefault(nome, {
                "ativo": nome,
                "modalidades": set(),
                "abertas": {},
            })
            item["modalidades"].add(modalidade)
            item["abertas"][modalidade] = bool(isinstance(detalhe, dict) and detalhe.get("open"))
    return [
        {
            "ativo": item["ativo"],
            "modalidades": sorted(item["modalidades"]),
            "abertas": dict(sorted(item["abertas"].items())),
            "aberto": any(item["abertas"].values()),
        }
        for item in sorted(catalogo.values(), key=lambda valor: valor["ativo"].upper())
    ]

def _ativos_binarios_turbo(api=None):
    """Lista a união completa das categorias Binary e Turbo, sem filtro Forex."""
    dados = STATE.get("ativos_abertos") or {}
    if api:
        dados = _refresh_ativos_abertos(api)
        # Após reconexão, o catálogo de abertura pode vir sem IDs. Mantém o
        # payload bruto do WebSocket como fonte de fallback para o resolvedor.
        if not dados or not any(
            isinstance(detalhe, dict) and detalhe.get("active_id") is not None
            for secao in dados.values() if isinstance(dados, dict) and isinstance(secao, dict)
            for detalhe in secao.values()
        ):
            bruto = _get_cache_from_library(api)
            if bruto:
                dados = bruto
    catalogo = _catalogo_binario_turbo(dados)
    if not catalogo and api:
        dados = _get_cache_from_library(api)
        catalogo = _catalogo_binario_turbo(dados)
    return [item["ativo"] for item in catalogo]

def _ativo_binario_turbo_existe(ativo):
    alvo = str(ativo or "").strip().upper()
    if not alvo:
        return False
    if any(str(nome).upper() == alvo for nome in _ativos_binarios_turbo(STATE.get("api"))):
        return True
    return _ativo_existe(ativo)

def _normalizar_modalidade(modalidade):
    """Normaliza a preferência operacional para Binary, Turbo ou ambas."""
    valor = str(modalidade or "ambas").strip().lower()
    aliases = {
        "both": "ambas", "all": "ambas", "todas": "ambas", "binarias": "binary", "binario": "binary",
        "binária": "binary", "binárias": "binary", "turbo-option": "turbo",
    }
    valor = aliases.get(valor, valor)
    return valor if valor in ("binary", "turbo", "ambas") else "ambas"

def _categorias_da_modalidade(modalidade):
    """Devolve as categorias da corretora que podem ser consultadas."""
    modalidade = _normalizar_modalidade(modalidade)
    return ("binary", "turbo") if modalidade == "ambas" else (modalidade,)

def _modalidade_compativel_com_expiracao(modalidade, expiracao_min):
    """Mantém o mesmo timeframe de Gestão para Binária e Turbo.

    A disponibilidade real do ativo/modalidade continua sendo validada por
    verificar_ativo_aberto(); esta função apenas garante que M1, M5 e M15
    sejam aceitos de forma uniforme nas duas modalidades.
    """
    try:
        expiracao = int(expiracao_min)
    except (TypeError, ValueError):
        return False
    modalidade = _normalizar_modalidade(modalidade)
    return modalidade in ("turbo", "binary") and expiracao in (1, 5, 15)

def verificar_ativo_aberto(ativo, modalidade, exigir_confirmacao=False):
    api = STATE.get("api")
    if not api:
        return not exigir_confirmacao
    dados = _refresh_ativos_abertos(api)
    if not dados:
        return not exigir_confirmacao
    if exigir_confirmacao and time.time() - STATE.get("ultimo_refresh_ativos", 0) > 300:
        dados = _refresh_ativos_abertos(api, force=True)
    try:
        ativo_base = str(ativo).upper()
        for suffix in ('-OP', ':N', '-Z', '_OTC', '-OTC'):
            ativo_base = ativo_base.replace(suffix, '')
        nomes_busca = {
            str(ativo), str(ativo).upper(), ativo_base,
            f"{ativo_base}-OTC", f"{ativo_base}_OTC", f"{ativo_base}-op",
        }
        for categoria in _categorias_da_modalidade(modalidade):
            info_modalidade = dados.get(categoria, {})
            if isinstance(info_modalidade, dict):
                for nome in nomes_busca:
                    detalhe = info_modalidade.get(nome, {})
                    if isinstance(detalhe, dict) and detalhe.get("open"):
                        return True
        return False
    except Exception:
        return False

def _modalidade_disponivel_para_tf(ativo, modalidade, expiracao_min):
    try:
        expiracao = int(expiracao_min)
    except (TypeError, ValueError):
        return False
    if expiracao < 1:
        return False
    modalidade = _normalizar_modalidade(modalidade)
    if modalidade == "ambas":
        return any(
            _modalidade_compativel_com_expiracao(mod, expiracao)
            and verificar_ativo_aberto(ativo, mod, exigir_confirmacao=True)
            for mod in ("turbo", "binary")
        )
    return (
        _modalidade_compativel_com_expiracao(modalidade, expiracao)
        and verificar_ativo_aberto(ativo, modalidade, exigir_confirmacao=True)
    )

def _mercado_aberto_horario():
    agora = _agora_brasilia()
    dia_semana = agora.weekday()
    hora = agora.hour
    minuto = agora.minute
    hora_decimal = hora + minuto / 60.0
    if dia_semana == 5:
        return False
    if dia_semana == 6:
        return hora_decimal >= 23.0
    if dia_semana == 4:
        return hora_decimal < 17.0
    if dia_semana in (0, 1, 2, 3):
        return hora_decimal < 17.0 or hora_decimal >= 23.0
    return False

def _ativo_e_otc(ativo):
    valor = str(ativo or "").upper()
    return "-OTC" in valor or "_OTC" in valor

def _identificar_mercado_ativo(ativo):
    return "OTC" if _ativo_e_otc(ativo) else "Mercado Aberto"

def mercado_em_otc():
    api = STATE.get("api")
    horario_aberto = _mercado_aberto_horario()
    if not api:
        novo_estado = not horario_aberto
        STATE["modo_otc"] = novo_estado
        return novo_estado
    dados = _refresh_ativos_abertos(api)
    abertos_normais = 0
    abertos_otc = 0
    if dados:
        for cat_key, info in dados.items():
            if isinstance(info, dict):
                for nome, v in info.items():
                    if isinstance(v, dict) and v.get('open'):
                        if _ativo_e_otc(nome):
                            abertos_otc += 1
                        else:
                            abertos_normais += 1
    if not horario_aberto:
        novo_estado = True
    else:
        if dados and abertos_normais == 0 and abertos_otc > 0:
            novo_estado = True
        else:
            novo_estado = False
    if novo_estado != STATE.get("modo_otc", False):
        if novo_estado:
            _log_scan("🌙 [MERCADO] Modo OTC ativado — Mercado Aberto fechado.")
        else:
            _log_scan("☀️ [MERCADO] Mercado Aberto disponível — priorizando pares Forex normais.")
        STATE["modo_otc"] = novo_estado
        _emit_status("mudança de modo OTC")
    return novo_estado

def _ativo_existe(ativo):
    try:
        from iqoptionapi.constants import ACTIVES
        return ativo in ACTIVES
    except Exception:
        return True

def _obter_payout(api, ativo, modalidade, expiracao_min):
    try:
        modalidades = _categorias_da_modalidade(modalidade)
        for mod in modalidades:
            if _modalidade_compativel_com_expiracao(mod, expiracao_min) and verificar_ativo_aberto(ativo, mod, exigir_confirmacao=True):
                return 0.82
        return 0.0
    except Exception:
        return 0.0

def detectar_melhor_modalidade(ativo, modalidade_preferida=None, expiracao_min=1):
    """Escolhe uma modalidade aberta e compatível com o vencimento configurado."""
    try:
        expiracao = int(expiracao_min)
    except (TypeError, ValueError):
        expiracao = 1
    expiracao = expiracao if expiracao in (1, 5, 15) else 1
    preferida = _normalizar_modalidade(
        modalidade_preferida if modalidade_preferida is not None else STATE.get("modalidade", "ambas")
    )
    if preferida == "ambas":
        candidatas = ("turbo", "binary") if expiracao <= 5 else ("binary", "turbo")
    else:
        candidatas = (preferida,)
    for modalidade in candidatas:
        if not _modalidade_compativel_com_expiracao(modalidade, expiracao):
            continue
        if _modalidade_disponivel_para_tf(ativo, modalidade, expiracao):
            _log_scan(f"  📊 [MODALIDADE] {ativo}: {modalidade.upper()} | M{expiracao}")
            return modalidade, True
    _log_scan(
        f"  ⏭ [MODALIDADE] {ativo}: nenhuma modalidade aberta/compatível "
        f"com M{expiracao} (preferência: {preferida.upper()})"
    )
    return candidatas[0], False

_CRYPTO_PREFIXES = (
    'BTC', 'ETH', 'XRP', 'LTC', 'BCH', 'DSH', 'ZEC', 'EOS',
    'TRX', 'XMR', 'ADA', 'XLM', 'NEO', 'ONT', 'OMG', 'BTG',
    'ETC', 'QTM', 'DOGE', 'BNB', 'SOL', 'AVAX', 'MATIC',
)
_FOREX_MAJORS = frozenset({
    'EURUSD', 'GBPUSD', 'USDJPY', 'AUDUSD', 'USDCAD', 'USDCHF', 'EURGBP', 'EURJPY',
    'NZDUSD', 'GBPJPY', 'EURCAD', 'EURAUD', 'GBPCAD', 'AUDJPY', 'CADJPY', 'CHFJPY'
})
_EXCLUIR_ACTIVES = frozenset({
    'AMAZON', 'GOOGLE', 'YANDEX', 'ALIBABA', 'TWITTER', 'FERRARI',
    'TESLA',  'APPLE',  'YAHOO',  'BAIDU',   'CISCO',   'FACEBOOK',
    'INTEL',  'MSFT',   'AIG',    'CITI',    'COKE',    'GE',
    'GM',     'GS',     'JPM',    'MCDON',   'MORSTAN', 'NIKE',
    'XAUUSD', 'XAGUSD', 'XPTUSD', 'UKOUSD', 'USOUSD',
    'FTSE',   'DAX',    'CAC',    'NIKKEI',  'SP500',   'NASDAQ',
    'DJI',    'ASX',    'IBOV',
})

def _is_forex(nome):
    nome_original = str(nome or "").strip().upper()
    # O robô deve trabalhar exclusivamente com ativos identificados pelos
    # sufixos -OP ou -OTC. Pares normais como EURUSD ficam fora da lista.
    if not (nome_original.endswith("-OP") or nome_original.endswith("-OTC")):
        return False
    base = nome_original
    for suffix in ('-OTC', '_OTC', '-OP', ':N', '-Z'):
        base = base.replace(suffix, '')
    if len(base) != 6 or not base.isalpha():
        return False
    if base in _EXCLUIR_ACTIVES:
        return False
    if any(base.startswith(p) for p in _CRYPTO_PREFIXES):
        return False
    return base in _FOREX_MAJORS

def _is_forex_otc(nome):
    return _is_forex(nome) and ("-OTC" in nome.upper() or "_OTC" in nome.upper())

def _pares_forex_apenas():
    try:
        from iqoptionapi.constants import ACTIVES
        pares = []
        for k in ACTIVES.keys():
            if not isinstance(k, str):
                continue
            if _is_forex(k):
                pares.append(k)
        return sorted(set(pares))
    except Exception as e:
        _log_scan(f"⚠️ Erro ao carregar ACTIVES: {e}")
        return []

def _pares_do_actives():
    return _pares_forex_apenas()

def _obter_todos_pares(api):
    pares = _pares_forex_apenas()
    _log_scan(f"🔍 {len(pares)} pares Forex carregados.")
    return pares

def _candles_para_df(velas_raw):
    if not velas_raw:
        return pd.DataFrame()
    if isinstance(velas_raw, dict):
        registros = list(velas_raw.values())
    elif isinstance(velas_raw, list):
        registros = velas_raw
    else:
        return pd.DataFrame()
    if not registros:
        return pd.DataFrame()
    df = pd.DataFrame(registros)
    rename = {}
    if 'min' in df.columns and 'low' not in df.columns:
        rename['min'] = 'low'
    if 'max' in df.columns and 'high' not in df.columns:
        rename['max'] = 'high'
    if rename:
        df.rename(columns=rename, inplace=True)
    for col in ('open', 'close', 'high', 'low'):
        if col not in df.columns:
            return pd.DataFrame()
    for col in ('open', 'close', 'high', 'low'):
        df[col] = pd.to_numeric(df[col], errors='coerce')
    df.dropna(subset=['open', 'close', 'high', 'low'], inplace=True)
    if 'from' in df.columns:
        df.sort_values('from', inplace=True)
    elif 'id' in df.columns:
        df.sort_values('id', inplace=True)
    df.reset_index(drop=True, inplace=True)
    return df


def _janela_busca_sinais(tf_seg):
    """Retorna a janela máxima para procurar novos sinais no candle atual.

    A busca termina 30 segundos antes do fechamento do candle:
    M1 = 30s, M5 = 270s (4min30s) e M15 = 870s (14min30s).
    """
    try:
        tf = max(60, int(tf_seg))
    except (TypeError, ValueError):
        tf = 60
    return {60: 30, 300: 270, 900: 870}.get(tf, max(30, tf - 30))


def _inicio_vela_atual(df, tf_seg, instante=None):
    """Obtém o timestamp Unix do início da vela mais recente do DataFrame."""
    if df is None or df.empty:
        raise ValueError("velas ausentes")
    vela = df.iloc[-1]
    inicio = vela.get("from") if hasattr(vela, "get") else None
    try:
        inicio = float(inicio)
        if not np.isfinite(inicio):
            raise ValueError("timestamp inválido")
        if inicio > 100_000_000_000:
            inicio /= 1000.0
        return inicio
    except (TypeError, ValueError):
        # Fallback somente quando a resposta da corretora não traz ``from``.
        agora = time.time() if instante is None else instante
        return float(_horario_do_sinal(tf_seg, agora))


def _obter_cotacao_ao_vivo(api, ativo, tf_seg, df=None):
    """Obtém o último preço disponível do ativo, sem usar STR/strike Digital.

    Quando o stream de candles em tempo real está ativo, usa o último ``close``
    recebido para o ativo e timeframe. Caso a biblioteca ainda não tenha um
    stream preenchido, usa o ``close`` da vela atual retornada por get_candles,
    que é a cotação mais recente disponível nessa mesma resposta.
    """
    try:
        realtime = api.get_realtime_candles(ativo, int(tf_seg)) if api else None
        if isinstance(realtime, dict) and realtime:
            chave = max(realtime, key=lambda valor: float(valor))
            registro = realtime[chave]
            for campo in ("close", "price", "ask", "bid"):
                try:
                    cotacao = float(registro.get(campo))
                    if np.isfinite(cotacao) and cotacao > 0:
                        return cotacao, "stream_realtime"
                except (AttributeError, TypeError, ValueError):
                    continue
    except Exception:
        pass

    try:
        cotacao = float(df.iloc[-1]["close"]) if df is not None and not df.empty else None
        if cotacao is not None and np.isfinite(cotacao) and cotacao > 0:
            return cotacao, "candle_atual"
    except (IndexError, KeyError, TypeError, ValueError):
        pass

    # Fallback para uma leitura fresca quando ainda não há stream em memória.
    try:
        if api:
            velas_frescas = _api_call_com_timeout(api.get_candles, 3, ativo, int(tf_seg), 1, time.time())
            df_fresco = _candles_para_df(velas_frescas)
            if not df_fresco.empty:
                cotacao = float(df_fresco.iloc[-1]["close"])
                if np.isfinite(cotacao) and cotacao > 0:
                    return cotacao, "candle_fresco"
    except Exception:
        pass
    return None, "indisponivel"


def _aguardar_retorno_a_abertura(
    api,
    ativo,
    tf_seg,
    inicio_vela,
    abertura,
    cotacao_inicial=None,
    maxima_inicial=None,
    minima_inicial=None,
    direcao=None,
):
    """Confirma um sinal já encontrado dentro da janela do timeframe.

    A regra direcional é:
    - CALL acima da abertura: aguarda a cotação descer até a abertura;
    - PUT abaixo da abertura: aguarda a cotação subir até a abertura;
    - CALL abaixo, PUT acima ou cotação já na abertura: libera a entrada;
    - se a condição esperada não ocorrer antes do limite, cancela o sinal.
    """
    try:
        inicio = float(inicio_vela)
        abertura = float(abertura)
    except (TypeError, ValueError):
        return False, "abertura da vela indisponível"

    tolerancia = max(1e-6, abs(abertura) * 1e-7)
    janela_segundos = _janela_busca_sinais(tf_seg)
    limite = inicio + janela_segundos
    direcao_normalizada = str(direcao or "").lower().strip()
    agora_inicial = time.time()
    if agora_inicial > limite:
        return False, (
            f"sinal detectado após os primeiros {janela_segundos}s "
            f"da vela (abertura={abertura:.8f})"
        )

    try:
        cotacao = float(cotacao_inicial)
    except (TypeError, ValueError):
        cotacao = None
    if cotacao is not None and not np.isfinite(cotacao):
        cotacao = None

    def _confirmar(cotacao_atual, fonte, agora):
        if cotacao_atual is None:
            return None
        idade = agora - inicio
        if abs(cotacao_atual - abertura) <= tolerancia:
            return True, (
                f"retorno à abertura confirmado aos {idade:.1f}s da vela "
                f"(abertura={abertura:.8f}, cotação={cotacao_atual:.8f}, fonte={fonte})"
            )
        if direcao_normalizada == "call" and cotacao_atual < abertura - tolerancia:
            return True, (
                f"CALL confirmado aos {idade:.1f}s: cotação abaixo da abertura "
                f"(abertura={abertura:.8f}, cotação={cotacao_atual:.8f}, fonte={fonte})"
            )
        if direcao_normalizada == "put" and cotacao_atual > abertura + tolerancia:
            return True, (
                f"PUT confirmado aos {idade:.1f}s: cotação acima da abertura "
                f"(abertura={abertura:.8f}, cotação={cotacao_atual:.8f}, fonte={fonte})"
            )
        return None

    inicial = _confirmar(cotacao, "cotação_inicial", agora_inicial)
    if inicial is not None:
        return inicial

    # Só há espera quando CALL está acima ou PUT está abaixo da abertura.
    deve_aguardar_queda = direcao_normalizada == "call" and cotacao is not None and cotacao > abertura + tolerancia
    deve_aguardar_alta = direcao_normalizada == "put" and cotacao is not None and cotacao < abertura - tolerancia
    deve_aguardar = deve_aguardar_queda or deve_aguardar_alta

    if not deve_aguardar:
        return False, (
                f"cotação não confirmou {direcao_normalizada.upper()} nos primeiros "
                f"{janela_segundos}s"
        )

    while True:
        agora = time.time()
        if agora > limite:
            acao = "queda" if deve_aguardar_queda else "alta"
            return False, (
                f"{acao} até a abertura não ocorreu nos primeiros "
                f"{janela_segundos}s "
                f"(abertura={abertura:.8f})"
            )

        cotacao, fonte = _obter_cotacao_ao_vivo(api, ativo, tf_seg)
        if cotacao is not None:
            try:
                cotacao = float(cotacao)
            except (TypeError, ValueError):
                cotacao = None
        if cotacao is not None and np.isfinite(cotacao):
            if deve_aguardar_queda and cotacao <= abertura + tolerancia:
                idade = agora - inicio
                return True, (
                    f"CALL confirmado após queda aos {idade:.1f}s da vela "
                    f"(abertura={abertura:.8f}, cotação={cotacao:.8f}, fonte={fonte})"
                )
            if deve_aguardar_alta and cotacao >= abertura - tolerancia:
                idade = agora - inicio
                return True, (
                    f"PUT confirmado após alta aos {idade:.1f}s da vela "
                    f"(abertura={abertura:.8f}, cotação={cotacao:.8f}, fonte={fonte})"
                )
        time.sleep(0.20)


def _vela_retorno_a_abertura(df, tf_seg, instante=None, cotacao_atual=None):
    """Valida retorno da cotação atual ao preço de abertura da vela.

    A regra exige que a vela atual esteja dentro da janela de busca do timeframe,
    tenha se afastado do preço de abertura para cima ou para baixo e depois tenha
    retornado a esse preço. A abertura é o preço do ativo
    registrado no campo ``open`` da vela; a confirmação usa a cotação atual
    recebida da API, não o STR/strike da Digital.
    """
    if df is None or df.empty:
        return False, "vela ausente"

    try:
        vela = df.iloc[-1]
        abertura = float(vela["open"])
        fechamento_candle = float(vela["close"])
        fechamento = float(cotacao_atual) if cotacao_atual is not None else fechamento_candle
        maxima = float(vela["high"])
        minima = float(vela["low"])
    except (IndexError, KeyError, TypeError, ValueError):
        return False, "dados OHLC inválidos"

    valores = (abertura, fechamento, maxima, minima)
    if not all(np.isfinite(valor) for valor in valores) or fechamento <= 0:
        return False, "dados OHLC não finitos"

    agora = float(time.time() if instante is None else instante)
    inicio = vela.get("from") if hasattr(vela, "get") else None
    try:
        inicio = float(inicio)
        if not np.isfinite(inicio):
            raise ValueError("timestamp inválido")
        # Algumas fontes entregam epoch em milissegundos.
        if inicio > 100_000_000_000:
            inicio /= 1000.0
    except (TypeError, ValueError):
        try:
            inicio = float(_horario_do_sinal(tf_seg, agora))
        except (TypeError, ValueError):
            return False, "início da vela indisponível"

    segundos_desde_abertura = agora - inicio
    janela_segundos = _janela_busca_sinais(tf_seg)
    if segundos_desde_abertura < 0 or segundos_desde_abertura > janela_segundos:
        return False, f"fora da janela de {janela_segundos}s"

    # Pequena tolerância para diferenças de arredondamento do preço recebido.
    tolerancia = max(1e-6, abs(abertura) * 1e-7)
    subiu = maxima > abertura + tolerancia
    caiu = minima < abertura - tolerancia
    if not (subiu or caiu):
        return False, "a vela ainda não se afastou da abertura"

    preco_atual_na_abertura = abs(fechamento - abertura) <= tolerancia
    cruzou_a_abertura = subiu and caiu
    if not (preco_atual_na_abertura or cruzou_a_abertura):
        return False, "a vela ainda não retornou à abertura"

    return True, (
        f"retorno confirmado aos {segundos_desde_abertura:.1f}s da vela "
        f"(abertura={abertura:.8f}, preço_atual={fechamento:.8f})"
    )


def _ema_numpy(valores, periodo):
    return pd.Series(valores, dtype="float64").ewm(span=periodo, adjust=False).mean().to_numpy()


def _cor_codigo_das_cores(ema, hist, indice):
    """Replica cor_da_vela(i), onde i=0 é a vela mais recente."""
    anterior = indice - 1
    if anterior < 0:
        return None
    if np.isnan(ema[indice]) or np.isnan(ema[anterior]) or np.isnan(hist[indice]) or np.isnan(hist[anterior]):
        return None
    if ema[indice] > ema[anterior] and hist[indice] > hist[anterior]:
        return "verde"
    if ema[indice] < ema[anterior] and hist[indice] < hist[anterior]:
        return "vermelha"
    return "branca"


def _sinal_codigo_das_cores_pro(candles):
    """Sinal da estratégia SCRIPT CÓDIGO DAS CORES Pro na mesma vela."""
    cfg = _cfg_estrategia("codigo_cores_pro")
    if not cfg.get("ativo", True) or not _estrategia_timeframe_ok(cfg):
        _registrar_sinal_estrategia("codigo_cores_pro", None, 0)
        return None
    minimo_candles = max(5, int(cfg.get("min_candles", 30) or 5))
    if not candles or len(candles) < minimo_candles:
        _registrar_sinal_estrategia("codigo_cores_pro", None, 0)
        return None

    try:
        closes = np.asarray([float(x["close"]) for x in candles], dtype=float)
        highs = np.asarray([float(x["high"]) for x in candles], dtype=float)
        lows = np.asarray([float(x["low"]) for x in candles], dtype=float)
        opens = np.asarray([float(x["open"]) for x in candles], dtype=float)
        fast_ma = _ema_numpy(closes, 12)
        slow_ma = _ema_numpy(closes, 26)
        macd = fast_ma - slow_ma
        signal = pd.Series(macd).rolling(window=9, min_periods=9).mean().to_numpy()
        hist = macd - signal
        ema13 = _ema_numpy(closes, 13)

        cor_atual = _cor_codigo_das_cores(ema13, hist, len(candles) - 1)
        cor_anterior = _cor_codigo_das_cores(ema13, hist, len(candles) - 2)
        cor_2antes = _cor_codigo_das_cores(ema13, hist, len(candles) - 3)
        if not cor_atual or not cor_anterior or not cor_2antes:
            return None

        # A condição usa close[1] e high/low[2], exatamente como no script.
        rompeu_alta = closes[-2] > highs[-3]
        rompeu_baixa = closes[-2] < lows[-3]
        ema_subindo = ema13[-1] > ema13[-2]
        ema_descendo = ema13[-1] < ema13[-2]
        hist_subindo = hist[-1] > hist[-2]
        hist_descendo = hist[-1] < hist[-2]

        if cor_2antes == "branca" and cor_anterior == "verde" and cor_atual == "verde":
            if rompeu_alta and ema_subindo and hist_subindo and _estrategia_direcao_ok(cfg, "call"):
                _registrar_sinal_estrategia("codigo_cores_pro", "call", 100)
                return "call"
        if cor_2antes == "branca" and cor_anterior == "vermelha" and cor_atual == "vermelha":
            if rompeu_baixa and ema_descendo and hist_descendo and _estrategia_direcao_ok(cfg, "put"):
                _registrar_sinal_estrategia("codigo_cores_pro", "put", 100)
                return "put"
    except (KeyError, TypeError, ValueError, IndexError, FloatingPointError):
        _registrar_sinal_estrategia("codigo_cores_pro", None, 0)
        return None
    _registrar_sinal_estrategia("codigo_cores_pro", None, 0)
    return None


def _sinal_ax1_rt(candles):
    """Sinal AX1_RT com entrada na segunda vela após o sinal."""
    cfg = _cfg_estrategia("ax1_rt")
    if not cfg.get("ativo", True) or not _estrategia_timeframe_ok(cfg):
        _registrar_sinal_estrategia("ax1_rt", None, 0)
        return None
    # A vela -3 é o sinal; -2 e -1 são as duas velas que devem sair depois.
    minimo_candles = max(7, int(cfg.get("min_candles", 10) or 7))
    if not candles or len(candles) < minimo_candles:
        _registrar_sinal_estrategia("ax1_rt", None, 0)
        return None

    try:
        closes = np.asarray([float(x["close"]) for x in candles], dtype=float)
        opens = np.asarray([float(x["open"]) for x in candles], dtype=float)
        highs = np.asarray([float(x["high"]) for x in candles], dtype=float)
        lows = np.asarray([float(x["low"]) for x in candles], dtype=float)
        ema = _ema_numpy(closes, 10)
        sinal = len(candles) - 3

        alta3 = all(closes[i] > opens[i] for i in range(sinal - 3, sinal))
        baixa3 = all(closes[i] < opens[i] for i in range(sinal - 3, sinal))
        vela_baixa = closes[sinal] < opens[sinal]
        vela_alta = closes[sinal] > opens[sinal]
        acima_ema = closes[sinal] > ema[sinal]
        abaixo_ema = closes[sinal] < ema[sinal]
        ema_na_vela = lows[sinal] <= ema[sinal] <= highs[sinal]

        if alta3 and vela_baixa and acima_ema and not ema_na_vela and _estrategia_direcao_ok(cfg, "call"):
            _registrar_sinal_estrategia("ax1_rt", "call", 100)
            return "call"
        if baixa3 and vela_alta and abaixo_ema and not ema_na_vela and _estrategia_direcao_ok(cfg, "put"):
            _registrar_sinal_estrategia("ax1_rt", "put", 100)
            return "put"
    except (KeyError, TypeError, ValueError, IndexError, FloatingPointError):
        _registrar_sinal_estrategia("ax1_rt", None, 0)
        return None
    _registrar_sinal_estrategia("ax1_rt", None, 0)
    return None


def _candlestick_35_scores(candles):
    """Calcula os 35 padrões do anexo como fatores independentes.

    Cada fator retorna 1 para sinal de alta, -1 para sinal de baixa e 0
    quando não há sinal ou quando as duas leituras entram em conflito.
    """
    nomes = (
        "candlestick_martelo", "candlestick_estrela_manha",
        "candlestick_estrela_doji_manha", "candlestick_perfurante",
        "candlestick_bebe_abandonado", "candlestick_fundo_pinca",
        "candlestick_sombra_longa_baixa", "candlestick_enforcado",
        "candlestick_estrela_noite", "candlestick_estrela_doji_noite",
        "candlestick_cobertura_nuvem", "candlestick_estrela_cadente",
        "candlestick_martelo_invertido", "candlestick_topo_pinca",
        "candlestick_sombra_longa_alta", "candlestick_3_metodos_alta",
        "candlestick_3_metodos_baixa", "candlestick_3_soldados_brancos",
        "candlestick_3_corvos_negros", "candlestick_no_pescoco",
        "candlestick_pontape", "candlestick_doji",
        "candlestick_estrela_doji", "candlestick_doji_libelula",
        "candlestick_doji_lapide", "candlestick_tri_estrela",
        "candlestick_harami", "candlestick_harami_cruzado",
        "candlestick_piao", "candlestick_marubozu", "candlestick_engolfo",
        "candlestick_lacuna_tasuki_alta", "candlestick_lacuna_tasuki_baixa",
        "candlestick_janela_ascendente", "candlestick_janela_descendente",
    )
    scores = {nome: 0 for nome in nomes}
    if not candles or len(candles) < 5:
        return scores

    try:
        o = np.asarray([float(x["open"]) for x in candles], dtype=float)
        c = np.asarray([float(x["close"]) for x in candles], dtype=float)
        h = np.asarray([float(x["high"]) for x in candles], dtype=float)
        l = np.asarray([float(x["low"]) for x in candles], dtype=float)

        def body(i):
            return abs(o[i] - c[i])

        def rng(i):
            return h[i] - l[i]

        def upper_shadow(i):
            return h[i] - max(o[i], c[i])

        def lower_shadow(i):
            return min(o[i], c[i]) - l[i]

        def is_bull(i):
            return c[i] > o[i]

        def is_bear(i):
            return o[i] > c[i]

        def is_doji(i):
            return np.isclose(o[i], c[i], rtol=0.0, atol=1e-12)

        def approx_eq(a, b):
            return np.isclose(a, b, rtol=1e-9, atol=1e-12)

        def context_bull(i=-2, fallback=-3):
            return is_bull(fallback) if is_doji(i) else is_bull(i)

        def context_bear(i=-2, fallback=-3):
            return is_bear(fallback) if is_doji(i) else is_bear(i)

        padroes_config = _cfg_estrategia("candlestick").get("padroes") or {}

        def add(nome, bullish, bearish):
            if not bool(padroes_config.get(nome, True)):
                scores[nome] = 0
            elif bullish and not bearish:
                scores[nome] = 1
            elif bearish and not bullish:
                scores[nome] = -1
            else:
                scores[nome] = 0

        # 1. Martelo
        martelo_bull = (
            is_bull(-1) and upper_shadow(-1) < 0.3 * lower_shadow(-1)
            and lower_shadow(-1) > 3 * body(-1) and context_bull()
        )
        martelo_bear = (
            is_bull(-1) and upper_shadow(-1) < 0.3 * lower_shadow(-1)
            and lower_shadow(-1) > 3 * body(-1) and context_bear()
        )
        add("candlestick_martelo", martelo_bull, martelo_bear)

        # 2. Estrela da Manhã / 3. Estrela Doji Manhã
        estrela_manha = (
            is_bear(-3) and not is_doji(-2)
            and body(-2) < 0.3 * body(-1) and body(-2) < 0.3 * body(-3)
            and is_bull(-1) and c[-1] > 0.5 * (h[-1] + l[-1])
        )
        estrela_doji_manha = (
            is_bear(-3) and is_doji(-2) and is_bull(-1)
            and c[-1] > 0.5 * (h[-1] + l[-1])
        )
        add("candlestick_estrela_manha", estrela_manha, False)
        add("candlestick_estrela_doji_manha", estrela_doji_manha, False)

        # 4. Perfurante / 5. Bebê Abandonado
        perfurante = (
            is_bear(-2) and is_bull(-1)
            and c[-1] > 0.5 * (h[-2] + l[-2])
            and c[-2] < 0.5 * (h[-1] + l[-1])
            and o[-1] <= c[-2] and l[-1] <= l[-2]
        )
        bebe_bull = (
            is_doji(-2) and is_bear(-3) and is_bull(-1)
            and c[-1] > 0.5 * (h[-3] + l[-3])
            and c[-3] < 0.5 * (h[-1] + l[-1])
        )
        bebe_bear = (
            is_doji(-2) and is_bull(-3) and is_bear(-1)
            and c[-1] < 0.5 * (h[-3] + l[-3])
            and c[-3] > 0.5 * (h[-1] + l[-1])
        )
        add("candlestick_perfurante", perfurante, False)
        add("candlestick_bebe_abandonado", bebe_bull, bebe_bear)

        # 6. Fundo Pinça / 7. Sombra Longa Baixa
        fundo_pinca_bull = (
            is_bear(-2) and body(-2) >= 0.62 * rng(-2)
            and approx_eq(l[-2], l[-1]) and c[-1] >= l[-2]
        )
        fundo_pinca_bear = (
            is_bull(-2) and body(-2) >= 0.62 * rng(-2)
            and approx_eq(l[-2], l[-1]) and c[-1] >= l[-2]
            and is_bear(-1)
        )
        sombra_baixa_bull = (
            is_bull(-1) and upper_shadow(-1) < 0.3 * lower_shadow(-1)
            and lower_shadow(-1) > 5 * body(-1)
        )
        sombra_baixa_bear = (
            is_bear(-1) and upper_shadow(-1) < 0.3 * lower_shadow(-1)
            and lower_shadow(-1) > 5 * body(-1)
        )
        add("candlestick_fundo_pinca", fundo_pinca_bull, fundo_pinca_bear)
        add("candlestick_sombra_longa_baixa", sombra_baixa_bull, sombra_baixa_bear)

        # 8. Enforcado / 9. Estrela da Noite / 10. Estrela Doji Noite
        enforcado_bull = (
            is_bear(-1) and upper_shadow(-1) < 0.3 * lower_shadow(-1)
            and lower_shadow(-1) > 3 * body(-1) and context_bull()
        )
        enforcado_bear = (
            is_bear(-1) and upper_shadow(-1) < 0.3 * lower_shadow(-1)
            and lower_shadow(-1) > 3 * body(-1) and context_bear()
        )
        estrela_noite = (
            is_bull(-3) and not is_doji(-2)
            and body(-2) < 0.3 * body(-1) and body(-2) < 0.3 * body(-3)
            and is_bear(-1) and c[-1] < 0.5 * (h[-1] + l[-1])
        )
        estrela_doji_noite = (
            is_bull(-3) and is_doji(-2) and is_bear(-1)
            and c[-1] < 0.5 * (h[-1] + l[-1])
        )
        add("candlestick_enforcado", enforcado_bull, enforcado_bear)
        add("candlestick_estrela_noite", False, estrela_noite)
        add("candlestick_estrela_doji_noite", False, estrela_doji_noite)

        # 11. Cobertura de Nuvem / 12. Estrela Cadente
        cobertura_nuvem = (
            is_bull(-2) and is_bear(-1)
            and c[-1] < 0.5 * (h[-2] + l[-2])
            and c[-2] > 0.5 * (h[-1] + l[-1])
            and o[-1] >= c[-2] and l[-1] >= l[-2]
        )
        estrela_cadente = (
            is_bear(-1) and lower_shadow(-1) < 0.3 * upper_shadow(-1)
            and upper_shadow(-1) > 3 * body(-1) and context_bull()
            and body(-2) > 0.5 * rng(-2)
        )
        estrela_cadente_bear = (
            is_bear(-1) and lower_shadow(-1) < 0.3 * upper_shadow(-1)
            and upper_shadow(-1) > 3 * body(-1) and context_bear()
            and body(-2) > 0.5 * rng(-2)
        )
        add("candlestick_cobertura_nuvem", False, cobertura_nuvem)
        add("candlestick_estrela_cadente", estrela_cadente, estrela_cadente_bear)

        # 13. Martelo Invertido / 14. Topo Pinça / 15. Sombra Longa Alta
        martelo_invertido_bull = (
            is_bull(-1) and lower_shadow(-1) < 0.3 * upper_shadow(-1)
            and upper_shadow(-1) > 3 * body(-1) and context_bear()
            and body(-2) > 0.5 * rng(-2)
        )
        martelo_invertido_bear = (
            is_bull(-1) and lower_shadow(-1) < 0.3 * upper_shadow(-1)
            and upper_shadow(-1) > 3 * body(-1) and context_bull()
            and body(-2) > 0.5 * rng(-2)
        )
        topo_pinca_bull = (
            is_bear(-2) and body(-2) >= 0.62 * rng(-2)
            and approx_eq(h[-2], h[-1]) and c[-1] <= h[-2]
        )
        topo_pinca_bear = (
            is_bull(-2) and body(-2) >= 0.62 * rng(-2)
            and approx_eq(h[-2], h[-1]) and c[-1] <= h[-2]
        )
        sombra_alta_bull = (
            is_bull(-1) and lower_shadow(-1) < 0.3 * upper_shadow(-1)
            and upper_shadow(-1) > 5 * body(-1)
        )
        sombra_alta_bear = (
            is_bear(-1) and lower_shadow(-1) < 0.3 * upper_shadow(-1)
            and upper_shadow(-1) > 5 * body(-1)
        )
        add("candlestick_martelo_invertido", martelo_invertido_bull, martelo_invertido_bear)
        add("candlestick_topo_pinca", topo_pinca_bull, topo_pinca_bear)
        add("candlestick_sombra_longa_alta", sombra_alta_bull, sombra_alta_bear)

        # 16/17. Três Métodos
        tres_metodos_alta = (
            is_bull(-5) and is_bull(-1) and c[-1] > c[-5]
            and body(-1) > body(-2) and body(-2) > body(-3)
            and body(-3) > body(-4) and body(-5) > body(-2)
        )
        tres_metodos_baixa = (
            is_bear(-5) and is_bear(-1) and c[-1] < c[-5]
            and body(-1) > body(-2) and body(-2) > body(-3)
            and body(-3) > body(-4) and body(-5) > body(-2)
        )
        add("candlestick_3_metodos_alta", tres_metodos_alta, False)
        add("candlestick_3_metodos_baixa", False, tres_metodos_baixa)

        # 18/19. Três Soldados Brancos / Três Corvos Negros
        tres_soldados = (
            is_bull(-3) and is_bull(-2) and is_bull(-1)
            and c[-1] > c[-2] > c[-3]
        )
        tres_corvos = (
            is_bear(-3) and is_bear(-2) and is_bear(-1)
            and c[-1] < c[-2] < c[-3]
        )
        add("candlestick_3_soldados_brancos", tres_soldados, False)
        add("candlestick_3_corvos_negros", False, tres_corvos)

        # 20. No Pescoço / 21. Pontapé
        no_pescoco_bull = (
            is_bull(-2) and is_bear(-1) and approx_eq(c[-2], c[-1])
            and body(-2) >= 0.5 * rng(-2) and body(-1) >= 0.5 * rng(-1)
        )
        no_pescoco_bear = (
            is_bear(-2) and is_bull(-1) and approx_eq(c[-2], c[-1])
            and body(-2) >= 0.5 * rng(-2) and body(-1) >= 0.5 * rng(-1)
        )
        pontape_bull = (
            is_bear(-2) and is_bull(-1)
            and o[-1] > o[-2] + 0.5 * body(-2)
            and body(-1) >= 0.7 * rng(-1)
        )
        pontape_bear = (
            is_bull(-2) and is_bear(-1)
            and o[-1] < o[-2] - 0.5 * body(-2)
            and body(-1) >= 0.7 * rng(-1)
        )
        add("candlestick_no_pescoco", no_pescoco_bull, no_pescoco_bear)
        add("candlestick_pontape", pontape_bull, pontape_bear)

        # 22-26. Dojis e Tri-Estrela
        doji_bull = is_doji(-1) and context_bear()
        doji_bear = is_doji(-1) and context_bull()
        estrela_doji_bull = (
            is_doji(-1)
            and approx_eq(upper_shadow(-1), lower_shadow(-1))
            and context_bear()
        )
        estrela_doji_bear = (
            is_doji(-1)
            and approx_eq(upper_shadow(-1), lower_shadow(-1))
            and context_bull()
        )
        doji_libelula_bull = (
            is_doji(-1) and upper_shadow(-1) < 0.3 * lower_shadow(-1)
            and context_bear()
        )
        doji_libelula_bear = (
            is_doji(-1) and upper_shadow(-1) < 0.3 * lower_shadow(-1)
            and context_bull()
        )
        doji_lapide_bull = (
            is_doji(-1) and lower_shadow(-1) < 0.3 * upper_shadow(-1)
            and context_bear()
        )
        doji_lapide_bear = (
            is_doji(-1) and lower_shadow(-1) < 0.3 * upper_shadow(-1)
            and context_bull()
        )
        tri_estrela_bull = (
            is_doji(-3) and is_doji(-2) and is_doji(-1) and is_bear(-4)
        )
        tri_estrela_bear = (
            is_doji(-3) and is_doji(-2) and is_doji(-1) and is_bull(-4)
        )
        add("candlestick_doji", doji_bull, doji_bear)
        add("candlestick_estrela_doji", estrela_doji_bull, estrela_doji_bear)
        add("candlestick_doji_libelula", doji_libelula_bull, doji_libelula_bear)
        add("candlestick_doji_lapide", doji_lapide_bull, doji_lapide_bear)
        add("candlestick_tri_estrela", tri_estrela_bull, tri_estrela_bear)

        # 27. Harami / 28. Harami Cruzado
        harami_bull = (
            is_bear(-2) and body(-1) <= 0.3 * body(-2)
            and c[-1] > c[-2] and c[-1] < o[-2] and rng(-1) < rng(-2)
        )
        harami_bear = (
            is_bull(-2) and body(-1) <= 0.3 * body(-2)
            and c[-1] < c[-2] and c[-1] > o[-2] and rng(-1) < rng(-2)
        )
        harami_cruzado_bull = (
            is_bear(-2) and is_doji(-1) and c[-1] > c[-2]
            and c[-1] < o[-2] and rng(-1) < rng(-2)
        )
        harami_cruzado_bear = (
            is_bull(-2) and is_doji(-1) and c[-1] < c[-2]
            and c[-1] > o[-2] and rng(-1) < rng(-2)
        )
        add("candlestick_harami", harami_bull, harami_bear)
        add("candlestick_harami_cruzado", harami_cruzado_bull, harami_cruzado_bear)

        # 29. Pião / 30. Marubozu / 31. Engolfo
        piao_bull = (
            body(-1) < (2 / 3) * rng(-1)
            and upper_shadow(-1) > 3 * body(-1)
            and lower_shadow(-1) > 3 * body(-1)
            and is_bear(-2) and is_bull(-1)
        )
        piao_bear = (
            body(-1) < (2 / 3) * rng(-1)
            and upper_shadow(-1) > 3 * body(-1)
            and lower_shadow(-1) > 3 * body(-1)
            and is_bear(-2) and is_bear(-1)
        )
        marubozu_bull = body(-1) >= 0.9 * rng(-1) and is_bull(-1)
        marubozu_bear = body(-1) >= 0.9 * rng(-1) and is_bear(-1)
        engolfo_bull = (
            is_bear(-2) and is_bull(-1) and c[-1] > o[-2]
            and o[-1] < c[-2] and body(-1) > body(-2)
        )
        engolfo_bear = (
            is_bull(-2) and is_bear(-1) and c[-1] < o[-2]
            and o[-1] > c[-2] and body(-1) > body(-2)
        )
        add("candlestick_piao", piao_bull, piao_bear)
        add("candlestick_marubozu", marubozu_bull, marubozu_bear)
        add("candlestick_engolfo", engolfo_bull, engolfo_bear)

        # 32/33. Lacuna Tasuki / 34/35. Janelas
        tasuki_alta = (
            is_bull(-3) and is_bull(-2) and is_bear(-1)
            and l[-2] > h[-3] + 0.3 * body(-3) and l[-1] >= h[-3]
        )
        tasuki_baixa = (
            is_bear(-3) and is_bear(-2) and is_bull(-1)
            and h[-2] < l[-3] - 0.3 * body(-3) and h[-1] <= l[-3]
        )
        janela_alta = (
            is_bull(-2) and is_bull(-1)
            and l[-1] > h[-2] + 0.3 * body(-2)
        )
        janela_baixa = (
            is_bear(-2) and is_bear(-1)
            and h[-1] < l[-2] - 0.3 * body(-2)
        )
        add("candlestick_lacuna_tasuki_alta", tasuki_alta, False)
        add("candlestick_lacuna_tasuki_baixa", False, tasuki_baixa)
        add("candlestick_janela_ascendente", janela_alta, False)
        add("candlestick_janela_descendente", False, janela_baixa)
    except (KeyError, TypeError, ValueError, IndexError, FloatingPointError):
        return scores

    return scores


class Motor:
    
    @staticmethod
    def analisar_sinal_unico(est, c):
        try:
            if len(c) < 3:
                return None
            
            cor_list = [x for x in c]
            close_list = [x['close'] for x in c]
            
            if est == 'P23':
                if len(c) < 4:
                    return None
                v3 = [x['close'] > x['open'] for x in c[-3:]]
                v5 = [x['close'] > x['open'] for x in c[-5:]] if len(c) >= 5 else v3
                if sum(v3) == 3:
                    return 'put'
                if sum(v3) == 0:
                    return 'call'
                if sum(v3) >= 2 and c[-1]['close'] > c[-2]['close']:
                    return 'call'
                if sum(v3) <= 1 and c[-1]['close'] < c[-2]['close']:
                    return 'put'
                return None
            
            if est == 'REV':
                if len(c) < 4:
                    return None
                reversoes = 0
                for i in range(1, len(c)):
                    if (c[i]['close'] > c[i]['open']) != (c[i-1]['close'] > c[i-1]['open']):
                        reversoes += 1
                if reversoes > len(c) * 0.5:
                    return None
                if c[-1]['close'] > c[-2]['close']:
                    return 'call'
                return 'put'
            
            if est == 'EX4':
                if len(c) < 5:
                    return None
                v = [1 if x['close'] > x['open'] else 0 for x in c[-4:]]
                if sum(v) >= 3:
                    return 'call'
                if sum(v) <= 1:
                    return 'put'
                return None
            
            if est == 'TRI':
                if len(c) < 3:
                    return None
                v3 = [x['close'] > x['open'] for x in c[-3:]]
                if all(v3):
                    return 'call'
                if not any(v3):
                    return 'put'
                return None
            
            if est == '5VELA':
                if len(c) < 5:
                    return None
                v5 = [x['close'] > x['open'] for x in c[-5:]]
                u = [x['close'] > x['open'] for x in c[-4:]]
                if sum(v5) >= 4:
                    return 'put'
                if sum(v5) <= 1:
                    return 'call'
                if sum(u) >= 4:
                    return 'put'
                if sum(u) <= 1:
                    return 'call'
                return None

            
            return None
        except Exception:
            return None

class MotorIA:
    
    @staticmethod
    def calcular_filtros_pro(cand):
        if not cand or len(cand) < 20:
            return {"tendencia": "neutro", "sequencia_ok": True}
        
        p = [x for x in cand]
        sma20 = sum(x['close'] for x in p[-20:]) / 20
        
        if p[-1]['close'] > sma20:
            tendencia = 'call'
        else:
            tendencia = 'put'
        
        v = [1 if x['close'] > x['open'] else 0 for x in cand]
        reversoes = sum(1 for i in range(-4, 0) if v[i] != v[i-1])
        sequencia_ok = reversoes < 4
        
        return {"tendencia": tendencia, "sequencia_ok": sequencia_ok}
    
    @staticmethod
    def detectar_mercado(cand):
        if not cand or len(cand) < 20:
            return 'lateral'
        p = [x for x in cand]
        sma5 = sum(x['close'] for x in p[-5:]) / 5
        sma20 = sum(x['close'] for x in p[-20:]) / 20
        diff = abs(sma5 - sma20) / sma20 if sma20 != 0 else 0
        if diff < 0.0003:
            return 'lateral'
        return 'tendencia'
    
    @staticmethod
    def filtrar_volatilidade(cand):
        if not cand or len(cand) < 5:
            return True
        ranges = [abs(x['high'] - x['low']) for x in cand]
        avg = sum(ranges) / len(ranges)
        if avg == 0:
            return True
        ratio = ranges[-1] / avg if avg > 0 else 0
        return ratio < 3.0
    
    @staticmethod
    def filtrar_pavio(cand, max_pavio_percent=5):
        if not cand or len(cand) < 5:
            return True
        velas_ruins = 0
        try:
            for vela in cand[-5:]:
                corpo = abs(vela['close'] - vela['open'])
                tamanho_total = vela['high'] - vela['low']
                if tamanho_total <= 0:
                    continue
                pavio_percent = ((tamanho_total - corpo) / tamanho_total) * 100
                if pavio_percent > max_pavio_percent:
                    velas_ruins += 1
            pode_operar = velas_ruins < 3
            return pode_operar
        except Exception as e:
            print(f"Erro filtrar pavio: {e}")
            return True
    
    @staticmethod
    def catalogar_v36(api, par, estrategias_ativas):
        try:
            candles = _api_call_com_timeout(api.get_candles, 15, par, 60, 40, time.time())
            if not candles or len(candles) < 40:
                return {}
            cand = candles
            rank = {}
            for e in estrategias_ativas:
                hits = 0
                for i in range(15, 39):
                    s = Motor.analisar_sinal_unico(e, cand[:i])
                    if s is None:
                        continue
                    cor = 'call' if cand[i]['close'] > cand[i]['open'] else 'put'
                    if s == cor:
                        hits += 1
                rank[e] = int(hits / 24 * 100)
            return rank
        except Exception:
            return {}

def calcular_order_flow(df):
    if len(df) < 6:
        return 0, 0.0
    c = df['close'].values
    o = df['open'].values
    h = df['high'].values
    l = df['low'].values
    rng = h - l
    vel_recente  = np.mean(rng[-3:])
    vel_anterior = np.mean(rng[-6:-3])
    aceleracao   = (vel_recente - vel_anterior) / (vel_anterior + 1e-9)
    corpo        = np.abs(c - o)
    ag_recente   = np.mean(corpo[-3:] / (rng[-3:] + 1e-9))
    bull_vol = sum(1 for i in range(-5, 0) if c[i] > o[i])
    bear_vol = 5 - bull_vol
    
    vacuo = aceleracao > 0.3 and ag_recente > 0.6
    
    ag_anterior = np.mean(corpo[-6:-3] / (rng[-6:-3] + 1e-9))
    exaustao    = aceleracao > 0.2 and ag_recente < ag_anterior * 0.7
    
    ruido = vel_recente < np.mean(rng[-15:]) * 0.15 and abs(bull_vol - bear_vol) <= 1
    
    if ruido:
        return 0, 0.0
    if exaustao:
        return 0, ag_recente
    sinal = 0
    if bull_vol > bear_vol:
        sinal = 1 if (vacuo or ag_recente > 0.55) else 0
    elif bear_vol > bull_vol:
        sinal = -1 if (vacuo or ag_recente > 0.55) else 0
    return sinal, float(ag_recente)

def calcular_persistencia(df):
    if len(df) < 8:
        return 0
    c = df['close'].values[-8:]
    moves = np.diff(c)
    bull = int(np.sum(moves > 0))
    bear = int(np.sum(moves < 0))
    if bull >= 5: return 1
    if bear >= 5: return -1
    return 0

def calcular_vacuo_liquidez(df):
    if len(df) < 10:
        return 0
    c = df['close'].values
    o = df['open'].values
    h = df['high'].values
    l = df['low'].values
    rng = h - l
    vel_recente = np.mean(rng[-3:])
    vel_anterior = np.mean(rng[-10:-3])
    if vel_anterior == 0:
        return 0
    aceleracao = vel_recente / vel_anterior
    corpo_recente = np.mean(np.abs(c[-3:] - o[-3:]))
    range_recente = np.mean(rng[-3:])
    if range_recente == 0:
        return 0
    agressao = corpo_recente / range_recente
    if aceleracao > 1.5 and agressao > 0.6:
        if c[-1] > o[-1]:
            return 1
        return -1
    return 0

def calcular_exaustao_fluxo(df):
    if len(df) < 8:
        return False
    h = df['high'].values
    l = df['low'].values
    rng = h - l
    range_medio = np.mean(rng[-8:-3])
    range_recente = np.mean(rng[-3:])
    if range_medio == 0:
        return False
    ratio = range_recente / range_medio
    return ratio < 0.4

def calcular_ruido_estatistico(df):
    if len(df) < 10:
        return True
    c = df['close'].values
    h = df['high'].values
    l = df['low'].values
    rng = h - l
    vel_recente = np.mean(rng[-5:])
    vel_media = np.mean(rng[-15:])
    if vel_media == 0:
        return True
    bull = sum(1 for i in range(-8, 0) if c[i] > df['open'].values[i])
    bear = 8 - bull
    return vel_recente < vel_media * 0.15 and abs(bull - bear) <= 1

def _sentimento_indisponivel(status="dados indisponíveis"):
    """Retorna um estado explícito para ausência de sentimento.

    50/50 é um valor válido de mercado e não pode ser usado como fallback:
    quando a corretora ainda não enviou o dado, os percentuais permanecem
    nulos para que o painel e o filtro não confundam ausência com neutralidade.
    """
    return {
        'call_pct': None,
        'put_pct': None,
        'sinal': 0,
        'forca': 0.0,
        'status': status,
    }


def _normalizar_mood_value(valor):
    """Converte o valor cru da corretora em percentual de CALL.

    A IQ Option normalmente envia uma razão entre 0 e 1, mas versões e mocks
    diferentes podem devolver número inteiro, string ou percentual entre 0 e
    100. Aceitamos esses formatos sem restringir a conversão a ``float`` puro.
    """
    if isinstance(valor, dict):
        valor = valor.get("value", valor.get("call_pct", valor.get("call")))
    if isinstance(valor, bool) or valor is None:
        return None
    try:
        texto = str(valor).strip().replace(",", ".")
        percentual_explicito = texto.endswith("%")
        if percentual_explicito:
            texto = texto[:-1].strip()
        numero = float(texto)
    except (TypeError, ValueError):
        return None
    if not math.isfinite(numero):
        return None
    if not percentual_explicito and 0.0 <= numero <= 1.0:
        numero *= 100.0
    if not 0.0 <= numero <= 100.0:
        return None
    return numero


def obter_sentimento_traders(ativo):
    api = STATE.get("api")
    if not api:
        return _sentimento_indisponivel("aguardando conexão")
    try:
        active_id = _resolver_active_id(ativo)
        if active_id is None:
            return _sentimento_indisponivel("active_id não encontrado")

        try:
            api.start_mood_stream(active_id, timeout=8)
        except TypeError:
            try:
                api.start_mood_stream(active_id)
            except Exception:
                pass
        except Exception:
            pass

        mood_data = None
        # A assinatura pode confirmar antes de o valor chegar ao dicionário.
        # Aguarda alguns segundos e tenta também o mapa bruto por ID/string.
        limite_mood = time.monotonic() + 8.0
        while time.monotonic() < limite_mood and mood_data is None:
            try:
                mood_data = api.get_traders_mood(active_id)
            except Exception:
                try:
                    mapa_mood = api.get_all_traders_mood()
                    if isinstance(mapa_mood, dict):
                        mood_data = mapa_mood.get(active_id, mapa_mood.get(str(active_id)))
                except Exception:
                    pass
            if mood_data is None:
                time.sleep(0.25)

        call_pct = _normalizar_mood_value(mood_data)
        if call_pct is None:
            return _sentimento_indisponivel("dados ainda não recebidos para o active_id")
        put_pct = 100.0 - call_pct

        forca = abs(call_pct - put_pct)
        if forca < 5:
            sinal = 0
        elif call_pct > put_pct:
            sinal = 1
        else:
            sinal = -1

        return {
            'call_pct': round(call_pct, 4),
            'put_pct': round(put_pct, 4),
            'sinal': sinal,
            'forca': round(forca, 4),
            'status': 'dados recebidos',
        }
    except Exception:
        logging.exception("Falha ao obter sentimento dos traders")
        return _sentimento_indisponivel("erro ao consultar a corretora")

def _sentimento_favoravel_para_direcao(sentimento, direcao):
    """Exige que o sentimento confirmado esteja alinhado com a direção da entrada.

    Quando o filtro de sentimento está habilitado, dados ausentes, neutros ou
    inconsistentes não autorizam uma operação. A opção pode ser desligada pelo
    controle existente ``usar_sentimento`` para preservar o comportamento
    anterior quando o usuário não quiser aplicar esse filtro.
    """
    if not STATE.get("usar_sentimento", True):
        return True
    if not isinstance(sentimento, dict):
        return False
    direcao = str(direcao or "").lower().strip()
    try:
        call_pct = float(sentimento.get("call_pct"))
        put_pct = float(sentimento.get("put_pct"))
    except (TypeError, ValueError):
        return False
    if not (math.isfinite(call_pct) and math.isfinite(put_pct)):
        return False
    if call_pct == put_pct:
        return False
    sinal = int(sentimento.get("sinal", 0) or 0)
    if sinal == 0:
        return False
    if direcao == "call":
        return sinal == 1 and call_pct > put_pct
    if direcao == "put":
        return sinal == -1 and put_pct > call_pct
    return False

def _descricao_sentimento(sentimento):
    if not isinstance(sentimento, dict):
        return "dados indisponíveis"
    try:
        return (
            f"CALL {float(sentimento.get('call_pct', 0.0)):.1f}% / "
            f"PUT {float(sentimento.get('put_pct', 0.0)):.1f}%"
        )
    except (TypeError, ValueError):
        return "dados inválidos"

_SENTIMENTO_STATUS_INTERVALO = 2.0
_sentimento_refresh_lock = threading.Lock()


def _definir_ativo_em_foco(ativo, limpar_confluencia=False):
    """Define o único par refletido em todos os blocos do Bot.

    O scanner analisa vários pares em sequência. Sem um foco explícito, o painel
    podia consultar o sentimento do primeiro item de ``ciclo_ativos`` enquanto a
    confluência ainda pertencia ao último par analisado. Quando o foco muda,
    limpamos a confluência anterior para não exibir estratégias de outro ativo.
    """
    ativo_normalizado = str(ativo or "").strip().upper()
    if not ativo_normalizado:
        return None
    anterior = str(STATE.get("ativo_em_foco") or "").strip().upper()
    STATE["ativo_em_foco"] = ativo_normalizado
    if limpar_confluencia and anterior != ativo_normalizado:
        try:
            expiracao = int(STATE.get("expiracao", 1) or 1)
        except (TypeError, ValueError):
            expiracao = 1
        STATE["confluencia_estrategias"] = {
            "ativo": ativo_normalizado,
            "timeframe": f"M{expiracao}",
            "direcao": None,
            "estrategias": [],
            "call": [],
            "put": [],
            "total": 0,
            "minimo": int(STATE.get("min_indicadores_confluencia", 5) or 5),
            "aprovada": False,
            "atualizado_em": time.time(),
            "status": "analisando par",
        }
    return ativo_normalizado


def _ativo_para_sentimento_status():
    """Escolhe o mesmo par canônico usado pela confluência do Bot."""
    foco = STATE.get("ativo_em_foco")
    if foco:
        return str(foco)
    operacao = STATE.get("operacao_atual")
    if isinstance(operacao, dict) and operacao.get("ativo"):
        return str(operacao["ativo"])
    confluencia = STATE.get("confluencia_estrategias") or {}
    if isinstance(confluencia, dict) and confluencia.get("ativo"):
        return str(confluencia["ativo"])
    ciclo = STATE.get("ciclo_ativos") or []
    if ciclo:
        return str(ciclo[0])
    return str(STATE.get("ativo_manual") or "EURUSD")


def _atualizar_sentimento_status(force=False):
    """Atualiza o sentimento em background sempre no par em foco do Bot."""
    ativo = _ativo_para_sentimento_status()
    atual = dict(STATE.get("sentimento_traders") or {})
    if atual.get("ativo") != ativo:
        # Não reutiliza percentuais do par anterior durante a troca de foco.
        atual = _sentimento_indisponivel("sincronizando par")
        atual["ativo"] = ativo
        STATE["sentimento_traders"] = dict(atual)
        STATE["sentimento_traders_ultimo_refresh"] = 0.0
    if not STATE.get("conectado") or not STATE.get("api"):
        atual.setdefault("status", "aguardando conexão")
        return atual

    agora = time.time()
    ultima = float(STATE.get("sentimento_traders_ultimo_refresh", 0.0) or 0.0)
    if not force and atual.get("ativo") == ativo and agora - ultima < _SENTIMENTO_STATUS_INTERVALO:
        return atual
    if not _sentimento_refresh_lock.acquire(blocking=False):
        return atual

    def _refresh():
        try:
            sentimento = obter_sentimento_traders(ativo)
            # A consulta pode terminar depois de o scanner ter mudado de par.
            # Nesse caso, o resultado antigo não pode voltar para o painel.
            if str(STATE.get("ativo_em_foco") or "").strip().upper() != ativo:
                return
            call_pct = sentimento.get("call_pct")
            put_pct = sentimento.get("put_pct")
            try:
                call_pct = float(call_pct)
                put_pct = float(put_pct)
            except (TypeError, ValueError):
                call_pct = put_pct = None

            if call_pct is None or put_pct is None:
                direcao = None
                status = "indisponível"
            elif call_pct > put_pct:
                direcao = "call"
                status = "favorável para CALL"
            elif put_pct > call_pct:
                direcao = "put"
                status = "favorável para PUT"
            else:
                direcao = None
                status = "neutro"

            atualizado_em = time.time()
            STATE["sentimento_traders"] = {
                "ativo": ativo,
                "call_pct": call_pct,
                "put_pct": put_pct,
                "sinal": int(sentimento.get("sinal", 0) or 0),
                "forca": float(sentimento.get("forca", 0.0) or 0.0),
                "direcao": direcao,
                "status": status,
                "atualizado_em": atualizado_em,
            }
            STATE["sentimento_traders_ultimo_refresh"] = atualizado_em
        finally:
            _sentimento_refresh_lock.release()

    threading.Thread(target=_refresh, name="sentimento-refresh", daemon=True).start()
    return atual


def filtros_pro(cand):
    if not cand or len(cand) < 5:
        return {"tendencia": "neutro", "sequencia_ok": True, "volatilidade_ok": True, "pavio_ok": True, "mercado": "lateral"}
    
    filtros = MotorIA.calcular_filtros_pro(cand)
    filtros["volatilidade_ok"] = MotorIA.filtrar_volatilidade(cand)
    filtros["pavio_ok"] = MotorIA.filtrar_pavio(cand)
    filtros["mercado"] = MotorIA.detectar_mercado(cand)
    return filtros

def detectar_padroes(df):
    if len(df) < 6:
        return 0, []
    c = df['close'].values
    o = df['open'].values
    h = df['high'].values
    l = df['low'].values

    def body(i):       return abs(o[i] - c[i])
    def rng(i):        return h[i] - l[i]
    def upper_shadow(i): return h[i] - max(o[i], c[i])
    def lower_shadow(i): return min(o[i], c[i]) - l[i]
    def is_bull(i):    return c[i] > o[i]
    def is_bear(i):    return o[i] > c[i]
    def is_doji(i):
        r = rng(i)
        return body(i) <= 0.05 * r if r > 0 else False
    def approx_eq(a, b, tol=0.001):
        ref = max(abs(a), abs(b), 1e-9)
        return abs(a - b) <= tol * ref

    sinais = []
    nomes  = []
    padroes_config = _cfg_estrategia("candlestick").get("padroes") or {}
    def add(sinal, nome):
        nome_base = re.sub(r"\s*[↑↓]\s*$", "", str(nome)).strip()
        chave = CANDLESTICK_PATTERN_DETECTOR_KEYS.get(nome_base)
        if chave and not bool(padroes_config.get(chave, True)):
            return
        sinais.append(sinal)
        nomes.append(nome)

    if len(df) >= 4:
        if (is_doji(-2) and is_bear(-3) and is_bull(-1) and c[-1] > (h[-3] + l[-3]) * 0.5 and c[-3] < (h[-1] + l[-1]) * 0.5):
            add(1, "Bebê Abandonado ↑")
        if (is_doji(-2) and is_bull(-3) and is_bear(-1) and c[-1] < (h[-3] + l[-3]) * 0.5 and c[-3] > (h[-1] + l[-1]) * 0.5):
            add(-1, "Bebê Abandonado ↓")
    if (is_bear(-2) and is_bull(-1) and c[-1] > (h[-2] + l[-2]) * 0.5 and c[-2] < (h[-1] + l[-1]) * 0.5 and o[-1] <= c[-2] and l[-1] <= l[-2]):
        add(1, "Perfurante ↑")
    if (is_bull(-2) and is_bear(-1) and c[-1] < (h[-2] + l[-2]) * 0.5 and c[-2] > (h[-1] + l[-1]) * 0.5 and o[-1] >= c[-2] and l[-1] >= l[-2]):
        add(-1, "Cobertura de Nuvem ↓")
    if is_doji(-1):
        if is_bear(-2):  add(1,  "Doji ↑")
        elif is_bull(-2): add(-1, "Doji ↓")
    if is_doji(-1) and rng(-1) > 0:
        sym = abs(upper_shadow(-1) - lower_shadow(-1)) < 0.1 * rng(-1)
        if sym and is_bear(-2):  add(1,  "Estrela Doji ↑")
        elif sym and is_bull(-2): add(-1, "Estrela Doji ↓")
    if len(df) >= 4:
        if (is_bull(-3) and is_bull(-2) and is_bear(-1) and l[-2] > h[-3] + 0.3 * body(-3) and l[-1] >= h[-3]):
            add(1, "Lacuna Tasuki Alta ↑")
        if (is_bear(-3) and is_bear(-2) and is_bull(-1) and h[-2] < l[-3] - 0.3 * body(-3) and h[-1] <= l[-3]):
            add(-1, "Lacuna Tasuki Baixa ↓")
    if is_doji(-1) and lower_shadow(-1) > 0:
        if upper_shadow(-1) < 0.3 * lower_shadow(-1):
            if is_bear(-2):   add(1,  "Doji Libélula ↑")
            elif is_bull(-2): add(-1, "Doji Libélula ↓")
    if (is_bear(-2) and is_bull(-1) and c[-1] > o[-2] and o[-1] < c[-2] and body(-1) > body(-2)):
        add(1, "Engolfo Bullish ↑")
    if (is_bull(-2) and is_bear(-1) and c[-1] < o[-2] and o[-1] > c[-2] and body(-1) > body(-2)):
        add(-1, "Engolfo Bearish ↓")
    if len(df) >= 4:
        if (is_bear(-3) and is_doji(-2) and is_bull(-1) and c[-1] > 0.5 * (h[-1] + l[-1])):
            add(1, "Estrela Doji Manhã ↑")
        if (is_bull(-3) and is_doji(-2) and is_bear(-1) and c[-1] < 0.5 * (h[-1] + l[-1])):
            add(-1, "Estrela Doji Noite ↓")
    if len(df) >= 4:
        if (is_bear(-3) and not is_doji(-2) and body(-2) < 0.3 * body(-1) and body(-2) < 0.3 * body(-3) and is_bull(-1) and c[-1] > 0.5 * (h[-1] + l[-1])):
            add(1, "Estrela da Manhã ↑")
        if (is_bull(-3) and not is_doji(-2) and body(-2) < 0.3 * body(-1) and body(-2) < 0.3 * body(-3) and is_bear(-1) and c[-1] < 0.5 * (h[-1] + l[-1])):
            add(-1, "Estrela da Noite ↓")
    if len(df) >= 6:
        if (is_bull(-5) and is_bull(-1) and c[-1] > c[-5] and body(-1) > body(-2) > body(-3) > body(-4) and body(-5) > body(-2)):
            add(1, "3 Métodos Alta ↑")
        if (is_bear(-5) and is_bear(-1) and c[-1] < c[-5] and body(-1) > body(-2) > body(-3) > body(-4) and body(-5) > body(-2)):
            add(-1, "3 Métodos Baixa ↓")
    if (is_bull(-2) and is_bull(-1) and body(-2) > 0 and l[-1] > h[-2] + 0.3 * body(-2)):
        add(1, "Janela Ascendente ↑")
    if (is_bear(-2) and is_bear(-1) and body(-2) > 0 and h[-1] < l[-2] - 0.3 * body(-2)):
        add(-1, "Janela Descendente ↓")
    if is_doji(-1) and upper_shadow(-1) > 0:
        if lower_shadow(-1) < 0.3 * upper_shadow(-1):
            if is_bear(-2):   add(1,  "Doji Lápide ↑")
            elif is_bull(-2): add(-1, "Doji Lápide ↓")
    if (is_bull(-1) and body(-1) > 0 and upper_shadow(-1) < 0.3 * lower_shadow(-1) and lower_shadow(-1) > 2 * body(-1)):
        add(1, "Martelo ↑")
    if (is_bull(-1) and body(-1) > 0 and lower_shadow(-1) < 0.3 * upper_shadow(-1) and upper_shadow(-1) > 2 * body(-1)):
        add(1, "Martelo Invertido ↑")
    if (is_bear(-1) and body(-1) > 0 and lower_shadow(-1) < 0.3 * upper_shadow(-1) and upper_shadow(-1) > 2 * body(-1)):
        add(-1, "Estrela Cadente ↓")
    if (is_bear(-1) and body(-1) > 0 and upper_shadow(-1) < 0.3 * lower_shadow(-1) and lower_shadow(-1) > 2 * body(-1)):
        add(-1, "Enforcado ↓")
    if body(-2) > body(-1) and o[-1] > c[-2] and c[-1] < o[-2]:
        if is_bear(-2) and is_bull(-1): add(1,  "Harami Bullish ↑")
        elif is_bull(-2) and is_bear(-1): add(-1, "Harami Bearish ↓")
    if body(-1) > 0.9 * rng(-1) and body(-1) > 0:
        if is_bull(-1): add(1, "Marubozu Alta ↑")
        else:           add(-1, "Marubozu Baixa ↓")
    if len(df) >= 4:
        if all(is_bull(-i) for i in range(1, 4)) and c[-1] > c[-2] > c[-3]:
            add(1, "3 Soldados ↑")
        if all(is_bear(-i) for i in range(1, 4)) and c[-1] < c[-2] < c[-3]:
            add(-1, "3 Corvos ↓")
    if approx_eq(l[-1], l[-2]) and is_bear(-2) and is_bull(-1):
        add(1, "Pinça Fundo ↑")
    if approx_eq(h[-1], h[-2]) and is_bull(-2) and is_bear(-1):
        add(-1, "Pinça Topo ↓")
    if is_bear(-2) and is_bull(-1) and o[-1] >= o[-2]:
        add(1, "Chute Bullish ↑")
    if is_bull(-2) and is_bear(-1) and o[-1] <= o[-2]:
        add(-1, "Chute Bearish ↓")
    if len(df) >= 4:
        if is_bear(-3) and is_bull(-2) and body(-3) > body(-2) and c[-1] > c[-2]:
            add(1, "3 Por Dentro ↑")
        if is_bull(-3) and is_bear(-2) and body(-3) > body(-2) and c[-1] < c[-2]:
            add(-1, "3 Por Dentro ↓")
    if len(df) >= 4:
        if is_bear(-3) and is_bull(-2) and body(-2) > body(-3) and c[-1] > c[-2]:
            add(1, "3 Por Fora ↑")
        if is_bull(-3) and is_bear(-2) and body(-2) > body(-3) and c[-1] < c[-2]:
            add(-1, "3 Por Fora ↓")
    if len(df) >= 6:
        if is_bull(-5) and all(is_bear(-i) for i in range(2, 5)) and is_bull(-1) and c[-1] > c[-5]:
            add(1, "Mat Hold ↑")
    if is_bull(-1) and is_bear(-2) and approx_eq(o[-1], o[-2]):
        add(1, "Linhas Separação ↑")
    if is_bear(-1) and is_bull(-2) and approx_eq(o[-1], o[-2]):
        add(-1, "Linhas Separação ↓")
    if len(df) >= 4:
        if all(is_bull(-i) for i in range(1, 4)) and upper_shadow(-1) > upper_shadow(-2):
            add(-1, "Avanço Bloqueado ↓")
    if len(df) >= 4:
        if all(is_bull(-i) for i in range(1, 4)) and body(-1) < body(-2):
            add(-1, "Deliberação ↓")
    if approx_eq(c[-1], c[-2]) and is_bull(-1) != is_bull(-2):
        if is_bull(-1): add(1,  "Encontro Bullish ↑")
        else:           add(-1, "Encontro Bearish ↓")
    if is_bear(-2) and is_bull(-1) and approx_eq(c[-1], l[-2]):
        add(-1, "Pescoço ↓")
    if (is_bear(-2) and is_bear(-1) and body(-1) <= 0.4 * body(-2) and o[-1] >= c[-2] and c[-1] <= o[-2]):
        add(1, "Pombo Voltando ↑")
    if (is_bull(-2) and is_bull(-1) and body(-1) <= 0.4 * body(-2) and o[-1] <= c[-2] and c[-1] >= o[-2]):
        add(-1, "Pombo Voltando ↓")
    if len(df) >= 4:
        if (is_bull(-3) and is_bear(-2) and is_bear(-1) and o[-2] > h[-3] and o[-1] >= c[-2] and c[-1] <= c[-3]):
            add(-1, "Dois Corvos ↓")
    if len(df) >= 6:
        if (is_bear(-5) and is_bear(-1) and c[-1] < c[-5] and all(is_bull(-i) for i in range(2, 5)) and all(c[-i] > l[-5] and h[-i] < o[-5] for i in range(2, 5))):
            add(-1, "Queda 3 Métodos ↓")
        if (is_bull(-5) and is_bull(-1) and c[-1] > c[-5] and all(is_bear(-i) for i in range(2, 5)) and all(c[-i] < h[-5] and l[-i] > o[-5] for i in range(2, 5))):
            add(1, "Alta 3 Métodos ↑")
    if len(df) >= 6:
        if (is_bear(-5) and body(-5) >= 0.6 * rng(-5) and is_bull(-1) and body(-1) >= 0.6 * rng(-1) and all(rng(-i) < 0.5 * body(-5) for i in range(2, 5))):
            add(1, "Torre Bullish ↑")
        if (is_bull(-5) and body(-5) >= 0.6 * rng(-5) and is_bear(-1) and body(-1) >= 0.6 * rng(-1) and all(rng(-i) < 0.5 * body(-5) for i in range(2, 5))):
            add(-1, "Torre Bearish ↓")
    if (body(-2) >= 0.5 * rng(-2) and body(-1) >= 0.5 * rng(-1) and approx_eq(c[-2], c[-1])):
        if is_bear(-2) and is_bull(-1): add(1,  "Contra-Ataque ↑")
        elif is_bull(-2) and is_bear(-1): add(-1, "Contra-Ataque ↓")

    if not sinais:
        return 0, []
    total = sum(sinais)
    sinal_final = 1 if total > 0 else (-1 if total < 0 else 0)
    return sinal_final, nomes

def sinal_fluxo6(c, o):
    if len(c) < 9: return 0
    cond_bull = [c[-1] > c[-3], c[-3] > o[-3], c[-5] > c[-9]]
    cond_bear = [c[-1] < c[-3], c[-3] < o[-3], c[-5] < c[-9]]
    bull = sum(cond_bull) >= 2
    bear = sum(cond_bear) >= 2
    return 1 if bull else (-1 if bear else 0)

def calcular_efectiv_v2(df, period=13, multiplier=2.0):
    n = len(df)
    if n < period + 5: return 0
    c = df['close'].values
    h = df['high'].values
    lo = df['low'].values
    tr = np.maximum.reduce([h - lo, np.abs(h - np.roll(c, 1)), np.abs(lo - np.roll(c, 1))])
    tr[0] = h[0] - lo[0]
    atr = np.zeros(n)
    atr[period-1] = np.mean(tr[:period])
    alpha = 1.0 / period
    for i in range(period, n):
        atr[i] = alpha * tr[i] + (1 - alpha) * atr[i-1]
    atr_m = atr * multiplier
    atr_ts = np.zeros(n)
    pos = np.zeros(n, dtype=int)
    for i in range(1, n):
        pt = atr_ts[i-1]
        if c[i] > pt and c[i-1] > pt:
            atr_ts[i] = max(pt, c[i] - atr_m[i])
        elif c[i] < pt and c[i-1] < pt:
            atr_ts[i] = min(pt, c[i] + atr_m[i])
        elif c[i] > pt:
            atr_ts[i] = c[i] - atr_m[i]
        else:
            atr_ts[i] = c[i] + atr_m[i]
        if c[i-1] < pt and c[i] > pt:
            pos[i] = 1
        elif c[i-1] > pt and c[i] < pt:
            pos[i] = -1
        else:
            pos[i] = pos[i-1]
    persistencia = 1
    for i in range(n - 2, -1, -1):
        if pos[i] == pos[-1]:
            persistencia += 1
        else:
            break
    return pos[-1], persistencia


def _efectiv_v2_estrategia_signal(df) -> int:
    """Camada de configuração real do Efectiv V2: período, sensibilidade
    (multiplicador do ATR), confirmações mínimas (barras de persistência na
    mesma posição) e força mínima, além de timeframe/candles mínimos/direção."""
    cfg = _cfg_estrategia("efectiv")
    if not cfg.get("ativo", True) or not _estrategia_timeframe_ok(cfg):
        _registrar_sinal_estrategia("efectiv", None, 0)
        return 0
    period = int(cfg.get("periodo", 13) or 13)
    if len(df) < max(int(cfg.get("min_candles", period + 5) or 0), period + 5):
        _registrar_sinal_estrategia("efectiv", None, 0)
        return 0
    multiplicador = cfg.get("multiplicador")
    if multiplicador is None:
        multiplicador = _SENSIBILIDADE_MULTIPLICADOR.get(cfg.get("sensibilidade", "media"), 2.0)
    pos, persistencia = calcular_efectiv_v2(df, period=period, multiplier=float(multiplicador))
    if pos == 0:
        _registrar_sinal_estrategia("efectiv", None, 0)
        return 0
    direcao = "call" if pos == 1 else "put"
    if persistencia < int(cfg.get("confirmacoes_minimas", 3) or 1):
        _registrar_sinal_estrategia("efectiv", None, 0)
        return 0
    forca = min(100.0, 40.0 + persistencia * 15.0)
    if forca < float(cfg.get("forca_minima", 70) or 0) or not _estrategia_direcao_ok(cfg, direcao):
        _registrar_sinal_estrategia("efectiv", None, forca)
        return 0
    _registrar_sinal_estrategia("efectiv", direcao, forca)
    return pos

# ============================================================
# TOP 5 INDICADORES PORTADOS DOS FONTES MQL4
# ============================================================
# As implementações abaixo reproduzem as regras essenciais dos fontes enviados
# em candles cronológicos. A última vela recebida é tratada como em formação e
# nunca confirma um sinal; isso é mais seguro para o robô de opções.


def _top5_preco_heiken_extremo(closed):
    o = np.asarray([_num(c, "open") for c in closed], dtype=float)
    h = np.asarray([_num(c, "high") for c in closed], dtype=float)
    l = np.asarray([_num(c, "low") for c in closed], dtype=float)
    c = np.asarray([_num(c, "close") for c in closed], dtype=float)
    ha_close = (o + h + l + c) / 4.0
    ha_open = np.empty(len(closed), dtype=float)
    ha_open[0] = (o[0] + c[0]) / 2.0
    for i in range(1, len(closed)):
        ha_open[i] = (ha_open[i - 1] + ha_close[i - 1]) / 2.0
    ha_high = np.maximum(h, np.maximum(ha_open, ha_close))
    ha_low = np.minimum(l, np.minimum(ha_open, ha_close))
    return np.where(ha_close > ha_open, ha_high, np.where(ha_close < ha_open, ha_low, ha_close))


def _top5_media(valores, periodo, metodo):
    valores = np.asarray(valores, dtype=float)
    periodo = max(1, int(periodo))
    metodo = str(metodo or "tema").lower()
    serie = pd.Series(valores, dtype="float64")
    if metodo == "sma":
        return serie.rolling(periodo, min_periods=1).mean().to_numpy()
    if metodo == "smma":
        return serie.ewm(alpha=1.0 / periodo, adjust=False).mean().to_numpy()
    if metodo == "lwma":
        out = np.empty(len(valores), dtype=float)
        for i in range(len(valores)):
            inicio = max(0, i - periodo + 1)
            janela = valores[inicio:i + 1]
            pesos = np.arange(1, len(janela) + 1, dtype=float)
            out[i] = float(np.dot(janela, pesos) / pesos.sum())
        return out
    if metodo == "ema":
        return _ema_numpy(valores, periodo)
    # TEMA é o padrão do fonte `precision-trend-on-moving-averages.mq4`.
    e1 = _ema_numpy(valores, periodo)
    e2 = _ema_numpy(e1, periodo)
    e3 = _ema_numpy(e2, periodo)
    return e3 + 3.0 * (e1 - e2)


def _top5_registrar(nome, sinal, forca, cfg):
    if sinal and forca >= float(cfg.get("forca_minima", 0) or 0) and _estrategia_direcao_ok(cfg, sinal):
        _registrar_sinal_estrategia(nome, sinal, forca)
        return sinal
    _registrar_sinal_estrategia(nome, None, forca if sinal else 0.0)
    return None


def _precision_trend_top5_signal(candles):
    nome = "precision_trend"
    cfg = _cfg_estrategia(nome)
    if not cfg.get("ativo", True) or not _estrategia_timeframe_ok(cfg):
        return _top5_registrar(nome, None, 0.0, cfg)
    try:
        periodo = max(2, int(cfg.get("periodo", 30) or 30))
        minimo = max(periodo + 2, int(cfg.get("min_candles", 55) or 55))
        closed = _closed(candles)
        if len(closed) < minimo:
            return _top5_registrar(nome, None, 0.0, cfg)
        high = np.asarray([_num(c, "high") for c in closed], dtype=float)
        low = np.asarray([_num(c, "low") for c in closed], dtype=float)
        close = np.asarray([_num(c, "close") for c in closed], dtype=float)
        sensibilidade = max(0.1, float(cfg.get("sensibilidade", 2.0) or 2.0))
        amplitude = pd.Series(high - low).rolling(periodo, min_periods=1).mean().to_numpy() * sensibilidade
        n = len(close)
        estado = np.zeros(n, dtype=int)
        limite_baixo = np.empty(n); limite_alto = np.empty(n)
        minimo_close = np.empty(n); maximo_close = np.empty(n)
        limite_baixo[0] = close[0] - amplitude[0]
        limite_alto[0] = close[0] + amplitude[0]
        minimo_close[0] = maximo_close[0] = close[0]
        for i in range(1, n):
            estado[i] = estado[i - 1]
            limite_baixo[i] = limite_baixo[i - 1]
            limite_alto[i] = limite_alto[i - 1]
            minimo_close[i] = minimo_close[i - 1]
            maximo_close[i] = maximo_close[i - 1]
            if estado[i - 1] == 0:
                if close[i] > limite_alto[i - 1]:
                    minimo_close[i] = close[i]
                    limite_baixo[i] = close[i] - amplitude[i]
                    estado[i] = 1
                elif close[i] < limite_baixo[i - 1]:
                    maximo_close[i] = close[i]
                    limite_alto[i] = close[i] + amplitude[i]
                    estado[i] = -1
            elif estado[i - 1] == 1:
                limite_baixo[i] = minimo_close[i - 1] - amplitude[i]
                if close[i] > minimo_close[i - 1]:
                    minimo_close[i] = close[i]
                if close[i] < limite_baixo[i - 1]:
                    maximo_close[i] = close[i]
                    limite_alto[i] = close[i] + amplitude[i]
                    estado[i] = -1
            else:
                limite_alto[i] = maximo_close[i - 1] + amplitude[i]
                if close[i] < maximo_close[i - 1]:
                    maximo_close[i] = close[i]
                if close[i] > limite_alto[i - 1]:
                    minimo_close[i] = close[i]
                    limite_baixo[i] = close[i] - amplitude[i]
                    estado[i] = 1
        preco = _top5_preco_heiken_extremo(closed) if cfg.get("preco_media", "heiken_extremo") == "heiken_extremo" else close
        media = _top5_media(preco, int(cfg.get("periodo_media", 14) or 14), cfg.get("metodo_media", "tema"))
        inclinacao = 1 if media[-1] > media[-2] else (-1 if media[-1] < media[-2] else 0)
        final_atual = estado[-1] if not cfg.get("exigir_concordancia", True) else (estado[-1] if estado[-1] == inclinacao else 0)
        final_anterior = estado[-2] if not cfg.get("exigir_concordancia", True) else (estado[-2] if estado[-2] == (1 if media[-2] > media[-3] else (-1 if media[-2] < media[-3] else 0)) else 0)
        sinal = "call" if final_atual == 1 and final_anterior != 1 else ("put" if final_atual == -1 and final_anterior != -1 else None)
        return _top5_registrar(nome, sinal, 100.0 if sinal else 0.0, cfg)
    except (TypeError, ValueError, IndexError, FloatingPointError):
        return _top5_registrar(nome, None, 0.0, cfg)


def _ddfx_bbstop_top5_signal(candles):
    nome = "ddfx_bbstop"
    cfg = _cfg_estrategia(nome)
    if not cfg.get("ativo", True) or not _estrategia_timeframe_ok(cfg):
        return _top5_registrar(nome, None, 0.0, cfg)
    try:
        periodo = max(2, int(cfg.get("periodo", 14) or 14))
        closed = _closed(candles)
        if len(closed) < max(periodo + 3, int(cfg.get("min_candles", 30) or 30)):
            return _top5_registrar(nome, None, 0.0, cfg)
        high = np.asarray([_num(c, "high") for c in closed], dtype=float)
        low = np.asarray([_num(c, "low") for c in closed], dtype=float)
        close = np.asarray([_num(c, "close") for c in closed], dtype=float)
        s = pd.Series(close)
        media = s.rolling(periodo, min_periods=periodo).mean().to_numpy()
        desvio = s.rolling(periodo, min_periods=periodo).std(ddof=0).to_numpy()
        upper = media + float(cfg.get("desvio", 2.0) or 2.0) * desvio
        lower = media - float(cfg.get("desvio", 2.0) or 2.0) * desvio
        estado = np.zeros(len(close), dtype=int)
        trail_upper = upper.copy(); trail_lower = lower.copy()
        risco = float(cfg.get("risco", 1.0) or 1.0)
        for i in range(1, len(close)):
            if not np.isfinite(upper[i - 1]) or not np.isfinite(lower[i - 1]):
                continue
            estado[i] = estado[i - 1]
            if close[i] > upper[i - 1]: estado[i] = 1
            elif close[i] < lower[i - 1]: estado[i] = -1
            if estado[i] == 1 and np.isfinite(trail_lower[i - 1]) and lower[i] < trail_lower[i - 1]:
                trail_lower[i] = trail_lower[i - 1]
            if estado[i] == -1 and np.isfinite(trail_upper[i - 1]) and upper[i] > trail_upper[i - 1]:
                trail_upper[i] = trail_upper[i - 1]
            if estado[i] == 1 and np.isfinite(trail_lower[i]):
                trail_lower[i] -= 0.5 * (risco - 1.0) * (upper[i] - lower[i])
            if estado[i] == -1 and np.isfinite(trail_upper[i]):
                trail_upper[i] += 0.5 * (risco - 1.0) * (upper[i] - lower[i])
        sinal = "call" if estado[-1] == 1 and estado[-2] != 1 else ("put" if estado[-1] == -1 and estado[-2] != -1 else None)
        return _top5_registrar(nome, sinal, 100.0 if sinal else 0.0, cfg)
    except (TypeError, ValueError, IndexError, FloatingPointError):
        return _top5_registrar(nome, None, 0.0, cfg)


def _top5_fractais(high, low, raio):
    n = len(high); altos = np.zeros(n, dtype=bool); baixos = np.zeros(n, dtype=bool)
    for i in range(raio, n - raio):
        altos[i] = high[i] > np.max(high[i - raio:i]) and high[i] > np.max(high[i + 1:i + raio + 1])
        baixos[i] = low[i] < np.min(low[i - raio:i]) and low[i] < np.min(low[i + 1:i + raio + 1])
    return altos, baixos


def _top5_pivots_depth(high, low, depth):
    n = len(high); altos = np.zeros(n, dtype=bool); baixos = np.zeros(n, dtype=bool)
    depth = max(2, int(depth))
    for i in range(depth - 1, n):
        janela_h = high[max(0, i - depth + 1):i + 1]
        janela_l = low[max(0, i - depth + 1):i + 1]
        altos[i] = high[i] >= np.max(janela_h)
        baixos[i] = low[i] <= np.min(janela_l)
    return altos, baixos


def _double_zigzag_top5_signal(candles):
    nome = "double_zigzag"
    cfg = _cfg_estrategia(nome)
    if not cfg.get("ativo", True) or not _estrategia_timeframe_ok(cfg):
        return _top5_registrar(nome, None, 0.0, cfg)
    try:
        closed = _closed(candles)
        raio = max(1, int(cfg.get("confirmacao_fractal", 2) or 2))
        lenta = max(2, int(cfg.get("profundidade_lenta", 24) or 24))
        rapida = max(2, int(cfg.get("profundidade_rapida", 6) or 6))
        if len(closed) < max(int(cfg.get("min_candles", 35) or 35), lenta + raio + 2):
            return _top5_registrar(nome, None, 0.0, cfg)
        high = np.asarray([_num(c, "high") for c in closed], dtype=float)
        low = np.asarray([_num(c, "low") for c in closed], dtype=float)
        fr_altos, fr_baixos = _top5_fractais(high, low, raio)
        lento_altos, lento_baixos = _top5_pivots_depth(high, low, lenta)
        rapido_altos, rapido_baixos = _top5_pivots_depth(high, low, rapida)
        indice = len(closed) - 1 - raio
        compra_lenta = bool(fr_baixos[indice] and lento_baixos[indice])
        compra_rapida = bool(fr_baixos[indice] and rapido_baixos[indice])
        venda_lenta = bool(fr_altos[indice] and lento_altos[indice])
        venda_rapida = bool(fr_altos[indice] and rapido_altos[indice])
        if compra_lenta or compra_rapida:
            forca = 100.0 if compra_lenta and compra_rapida else 85.0
            return _top5_registrar(nome, "call", forca, cfg)
        if venda_lenta or venda_rapida:
            forca = 100.0 if venda_lenta and venda_rapida else 85.0
            return _top5_registrar(nome, "put", forca, cfg)
        return _top5_registrar(nome, None, 0.0, cfg)
    except (TypeError, ValueError, IndexError, FloatingPointError):
        return _top5_registrar(nome, None, 0.0, cfg)


def _top5_parabolic_series(high, low, passo, maximo):
    n = len(high); sar = np.empty(n, dtype=float); direcao = np.ones(n, dtype=int)
    sar[0] = low[0]; ep = high[0]; af = passo; alta = True
    for i in range(1, n):
        anterior = sar[i - 1]
        valor = anterior + af * (ep - anterior)
        if alta:
            valor = min(valor, low[i - 1], low[i - 2] if i > 1 else low[i - 1])
            if low[i] < valor:
                alta = False; valor = ep; ep = low[i]; af = passo
            else:
                if high[i] > ep:
                    ep = high[i]; af = min(maximo, af + passo)
        else:
            valor = max(valor, high[i - 1], high[i - 2] if i > 1 else high[i - 1])
            if high[i] > valor:
                alta = True; valor = ep; ep = high[i]; af = passo
            else:
                if low[i] < ep:
                    ep = low[i]; af = min(maximo, af + passo)
        sar[i] = valor; direcao[i] = 1 if alta else -1
    return sar, direcao


def _parabolic_sar_top5_signal(candles):
    nome = "parabolic_sar"
    cfg = _cfg_estrategia(nome)
    if not cfg.get("ativo", True) or not _estrategia_timeframe_ok(cfg):
        return _top5_registrar(nome, None, 0.0, cfg)
    try:
        closed = _closed(candles)
        if len(closed) < int(cfg.get("min_candles", 25) or 25):
            return _top5_registrar(nome, None, 0.0, cfg)
        high = np.asarray([_num(c, "high") for c in closed], dtype=float)
        low = np.asarray([_num(c, "low") for c in closed], dtype=float)
        passo = min(0.2, max(0.001, float(cfg.get("passo", 0.02) or 0.02)))
        maximo = min(1.0, max(passo, float(cfg.get("maximo", 0.20) or 0.20)))
        _, direcao = _top5_parabolic_series(high, low, passo, maximo)
        sinal = "call" if direcao[-1] == 1 and direcao[-2] != 1 else ("put" if direcao[-1] == -1 and direcao[-2] != -1 else None)
        return _top5_registrar(nome, sinal, 100.0 if sinal else 0.0, cfg)
    except (TypeError, ValueError, IndexError, FloatingPointError):
        return _top5_registrar(nome, None, 0.0, cfg)


def _top5_ichimoku_mid(high, low, periodo):
    hi = pd.Series(high).rolling(periodo, min_periods=periodo).max()
    lo = pd.Series(low).rolling(periodo, min_periods=periodo).min()
    return ((hi + lo) / 2.0).to_numpy()


def _forex_guru_cloud_top5_signal(candles):
    nome = "forex_guru_cloud"
    cfg = _cfg_estrategia(nome)
    if not cfg.get("ativo", True) or not _estrategia_timeframe_ok(cfg):
        return _top5_registrar(nome, None, 0.0, cfg)
    try:
        closed = _closed(candles)
        tenkan = max(2, int(cfg.get("tenkan", 8) or 8))
        kijun = max(2, int(cfg.get("kijun", 29) or 29))
        senkou = max(2, int(cfg.get("senkou", 34) or 34))
        if len(closed) < max(int(cfg.get("min_candles", 45) or 45), senkou + 2):
            return _top5_registrar(nome, None, 0.0, cfg)
        high = np.asarray([_num(c, "high") for c in closed], dtype=float)
        low = np.asarray([_num(c, "low") for c in closed], dtype=float)
        close = np.asarray([_num(c, "close") for c in closed], dtype=float)
        tenkan_line = _top5_ichimoku_mid(high, low, tenkan)
        kijun_line = _top5_ichimoku_mid(high, low, kijun)
        span_a = (tenkan_line + kijun_line) / 2.0
        span_b = _top5_ichimoku_mid(high, low, senkou)
        topo = np.maximum(span_a, span_b); fundo = np.minimum(span_a, span_b)
        if not np.all(np.isfinite([topo[-1], topo[-2], fundo[-1], fundo[-2], close[-1], close[-2]])):
            return _top5_registrar(nome, None, 0.0, cfg)
        sinal = None
        if close[-1] > topo[-1] and close[-2] <= topo[-2]: sinal = "call"
        elif close[-1] < fundo[-1] and close[-2] >= fundo[-2]: sinal = "put"
        return _top5_registrar(nome, sinal, 100.0 if sinal else 0.0, cfg)
    except (TypeError, ValueError, IndexError, FloatingPointError):
        return _top5_registrar(nome, None, 0.0, cfg)


def top5_indicadores_sinais(candles):
    funcoes = {
        "precision_trend": _precision_trend_top5_signal,
        "ddfx_bbstop": _ddfx_bbstop_top5_signal,
        "double_zigzag": _double_zigzag_top5_signal,
        "parabolic_sar": _parabolic_sar_top5_signal,
        "forex_guru_cloud": _forex_guru_cloud_top5_signal,
    }
    resultado = {}
    for nome, funcao in funcoes.items():
        try:
            sinal = funcao(candles)
        except Exception as exc:
            _log_scan(f"⚠️ Falha no indicador portado {nome}: {exc}")
            sinal = None
            _registrar_sinal_estrategia(nome, None, 0.0)
        resultado[nome] = sinal
    return resultado


_INDICADORES_CONFLUENCIA = (
    ("fluxo6", "Fluxo de candles"),
    ("efectiv", "Efectiv V2"),
    ("lta_ltb", "LTA / LTB"),
    ("order_flow", "Order Flow"),
    ("persistencia", "Persistência"),
    ("vacuo_liquidez", "Vácuo de liquidez"),
    ("sentimento", "Sentimento dos traders"),
    ("codigo_cores_pro", "Código das Cores Pro+"),
    ("ax1_rt", "AX1_RT"),
    ("indicador_rsi", "RSI"),
    ("indicador_aroon", "Aroon"),
    ("indicador_darvas", "Darvas"),
    ("indicador_suporte_resistencia", "Suporte e resistência"),
    ("indicador_fibonacci", "Fibonacci"),
    ("estrategia_price_action", "Price Action"),
    ("top5_precision_trend", "Precision Trend"),
    ("top5_ddfx_bbstop", "DDFX BBStop"),
    ("top5_double_zigzag", "Double ZigZag"),
    ("top5_parabolic_sar", "Parabolic SAR"),
    ("top5_forex_guru_cloud", "Forex Guru Cloud"),
)


def _contar_confluencia_indicadores(fatores_scores, sinais_catalogo=None):
    """Conta módulos e estratégias que apontam para a mesma direção.

    O Candlestick é um único módulo agregado: o sinal bruto e os padrões
    configuráveis não são exibidos como duas estratégias. As estratégias do
    catálogo entram com seu nome próprio quando confirmam CALL ou PUT, incluindo
    explicitamente Milhão Maioria e Milhão Minoria.
    """
    chamadas, puts = [], []
    candlestick_padroes_call, candlestick_padroes_put = [], []
    for chave, nome in _INDICADORES_CONFLUENCIA:
        try:
            valor = float(fatores_scores.get(chave, 0) or 0)
        except (TypeError, ValueError):
            valor = 0.0
        if valor > 0:
            chamadas.append(nome)
        elif valor < 0:
            puts.append(nome)

    # Os padrões escolhidos na sessão Candlestick são fatores próprios. Assim,
    # o painel mostra, por exemplo, "Candlestick — Martelo", em vez de perder
    # o padrão dentro de um rótulo genérico ou contar Candlestick duas vezes.
    cfg_candlestick = _cfg_estrategia("candlestick")
    try:
        valor_candlestick = float(fatores_scores.get("candle", 0) or 0)
    except (TypeError, ValueError):
        valor_candlestick = 0.0
    direcao_candlestick = 1 if valor_candlestick > 0 else (-1 if valor_candlestick < 0 else 0)
    if cfg_candlestick.get("ativo", True) and direcao_candlestick:
        for chave, nome_padrao in CANDLESTICK_PATTERN_LABELS.items():
            try:
                valor = float(fatores_scores.get(chave, 0) or 0)
            except (TypeError, ValueError):
                valor = 0.0
            if (valor > 0 and direcao_candlestick > 0) or (valor < 0 and direcao_candlestick < 0):
                if direcao_candlestick > 0:
                    candlestick_padroes_call.append(nome_padrao)
                else:
                    candlestick_padroes_put.append(nome_padrao)
    if candlestick_padroes_call:
        chamadas.append("Candlestick — " + " + ".join(candlestick_padroes_call))
    elif candlestick_padroes_put:
        puts.append("Candlestick — " + " + ".join(candlestick_padroes_put))
    else:
        # Fallback para uma única entrada agregada se não houver padrão individual
        # exposto, mas a estratégia Candlestick tiver sinal configurado.
        try:
            valor_candlestick = float(fatores_scores.get("candle", 0) or 0)
        except (TypeError, ValueError):
            valor_candlestick = 0.0
        if valor_candlestick > 0:
            chamadas.append("Candlestick")
        elif valor_candlestick < 0:
            puts.append("Candlestick")

    if sinais_catalogo is None:
        sinais_catalogo = {}
    if isinstance(sinais_catalogo, Mapping):
        for nome, sinal in sinais_catalogo.items():
            nome = str(nome)
            if sinal == "call":
                chamadas.append(nome)
            elif sinal == "put":
                puts.append(nome)
    chamadas = list(dict.fromkeys(chamadas))
    puts = list(dict.fromkeys(puts))
    return {"call": chamadas, "put": puts, "total": len(chamadas) + len(puts)}


def _minimo_confluencia():
    """Retorna o mínimo configurado, com padrão de dez confirmações."""
    try:
        configurado = int(STATE.get("min_indicadores_confluencia", 10) or 10)
    except (TypeError, ValueError):
        configurado = 10
    # +1 representa o Candlestick agregado, exibido como um único item.
    maximo = len(_INDICADORES_CONFLUENCIA) + 1 + len(CATALOG_STRATEGIES)
    return max(1, min(configurado, maximo))


def _resolver_confluencia(confluencia):
    """Escolhe a direção com mais confirmações e só aprova a partir do mínimo."""
    chamadas = list(confluencia.get("call") or [])
    puts = list(confluencia.get("put") or [])
    minimo = _minimo_confluencia()
    if len(chamadas) >= minimo and len(chamadas) > len(puts):
        return "call", chamadas, puts, chamadas, minimo
    if len(puts) >= minimo and len(puts) > len(chamadas):
        return "put", chamadas, puts, puts, minimo
    return None, chamadas, puts, [], minimo


def _score_timeframe_ia(df, label, ativo):
    MIN_VELAS = 15
    if df.empty or len(df) < MIN_VELAS:
        return 0, None, None, {}

    # As cinco últimas velas fechadas formam a janela comum de confirmação.
    # Qualquer Doji nessa janela cancela todos os sinais antes da confluência.
    try:
        candles_para_validar = df.to_dict("records")
    except (AttributeError, TypeError):
        candles_para_validar = []
    if _janela_tem_doji(candles_para_validar, tamanho=5):
        STATE["catalogo_ultimo_voto"] = {"sinais": {}, "calls": [], "puts": [], "direcao": None, "confluencias": 0, "total": 0}
        STATE["confluencia_estrategias"] = {
            "ativo": ativo, "timeframe": label, "direcao": None, "estrategias": [],
            "call": [], "put": [], "total": 0, "minimo": _minimo_confluencia(),
            "aprovada": False, "atualizado_em": time.time(),
        }
        return 0, None, None, {}
    
    c = df['close'].values
    o = df['open'].values
    
    sinal_candle, padroes_det = detectar_padroes(df)
    
    sinal_fluxo = sinal_fluxo6(c, o) if STATE.get("usar_fluxo", True) else 0
    
    pos_efectiv = _efectiv_v2_estrategia_signal(df) if STATE.get("usar_efectiv", True) else 0
    
    roll_min = df['low'].rolling(10, center=True, min_periods=1).min()
    roll_max = df['high'].rolling(10, center=True, min_periods=1).max()
    df_copy = df.copy()
    df_copy['is_min'] = df['low'] == roll_min
    df_copy['is_max'] = df['high'] == roll_max
    fundos = df_copy[df_copy['is_min']].tail(2)
    topos = df_copy[df_copy['is_max']].tail(2)
    lta = STATE.get("usar_lta_ltb", True) and len(fundos) >= 2 and fundos['low'].iloc[-1] > fundos['low'].iloc[-2]
    ltb = STATE.get("usar_lta_ltb", True) and len(topos) >= 2 and topos['high'].iloc[-1] < topos['high'].iloc[-2]
    
    sinal_of, ag_idx = calcular_order_flow(df) if STATE.get("usar_order_flow", True) else (0, 0.0)
    
    persistencia = calcular_persistencia(df) if STATE.get("usar_persistencia", True) else 0
    
    
    
    vacuo = calcular_vacuo_liquidez(df) if STATE.get("usar_vacuo", True) else 0
    
    exaustao = calcular_exaustao_fluxo(df) if STATE.get("usar_exaustao", True) else False
    
    ruido = calcular_ruido_estatistico(df) if STATE.get("usar_ruido", True) else False
    
    # Traders Mood removido do cálculo de confluência; a direção usa somente
    # indicadores e estratégias configurados na aba Gestão.
    sentimento = _sentimento_indisponivel("removido do fluxo")
    
    cand_dict = df.tail(20).to_dict('records')

    # Janela maior para as estratégias com configuração individual (Candlestick,
    # Price Action e os 5 indicadores), cujo período configurável pode passar de 20.
    _periodos_config = [
        _cfg_estrategia(n).get("periodo", 20)
        for n in ("candlestick", "price_action", "rsi", "aroon", "darvas", "suporte_resistencia", "fibonacci", "efectiv", "precision_trend", "ddfx_bbstop", "double_zigzag", "parabolic_sar", "forex_guru_cloud")
    ]
    _periodos_config.extend([
        _cfg_estrategia("precision_trend").get("periodo_media", 14),
        _cfg_estrategia("double_zigzag").get("profundidade_lenta", 24),
        _cfg_estrategia("forex_guru_cloud").get("senkou", 34),
    ])
    try:
        _maior_periodo = max([int(p) for p in _periodos_config if p] or [20])
    except (TypeError, ValueError):
        _maior_periodo = 20
    janela_estrategias = min(len(df), max(30, _maior_periodo + 10))
    cand_dict_estrategias = df.tail(janela_estrategias).to_dict('records')

    # Catálogo de estratégias: as estratégias são calculadas sobre candles fechados e
    # entram como fatores independentes no voto já existente do robô.
    catalogo_voto = {"sinais": {}, "calls": [], "puts": [], "direcao": None, "confluencias": 0, "total": 0}
    # Limpa o último voto antes de recalcular, evitando que um catálogo
    # desativado ou uma falha de leitura reapresente sinais antigos.
    STATE["catalogo_ultimo_voto"] = dict(catalogo_voto)
    if STATE.get("usar_catalogo", True):
        try:
            selecionadas = STATE.get("catalogo_estrategias")
            if selecionadas is None:
                selecionadas = list(CATALOG_STRATEGIES)
            catalogo_voto = CatalogoEstrategias.voto(cand_dict, selecionadas)
            STATE["catalogo_ultimo_voto"] = {
                "direcao": catalogo_voto.get("direcao"),
                "confluencias": catalogo_voto.get("confluencias", 0),
                "total": catalogo_voto.get("total", 0),
                "sinais": catalogo_voto.get("sinais", {}),
            }
        except Exception as exc:
            _log_scan(f"⚠️ Falha no catálogo de estratégias para {ativo}: {exc}")
    filtros = MotorIA.calcular_filtros_pro(cand_dict) if STATE.get("usar_filtros_pro", True) else {"tendencia": "neutro", "sequencia_ok": True}
    tendencia_ia = filtros.get('tendencia', 'neutro')
    sequencia_ok = filtros.get('sequencia_ok', True)
    mercado_estado = MotorIA.detectar_mercado(cand_dict) if STATE.get("usar_filtros_pro", True) else 'tendencia'
    volatilidade_ok = MotorIA.filtrar_volatilidade(cand_dict) if STATE.get("usar_filtros_pro", True) else True
    pavio_ok = MotorIA.filtrar_pavio(cand_dict) if STATE.get("usar_filtros_pro", True) else True

    # Indicadores complementares: Cores Pro confirma na vela atual; AX1_RT
    # considera o sinal de três velas atrás, após duas velas concluídas.
    sinal_cores_pro = _sinal_codigo_das_cores_pro(cand_dict)
    sinal_ax1_rt = _sinal_ax1_rt(cand_dict)
    candlestick_35_scores = _candlestick_35_scores(_closed(cand_dict_estrategias))
    price_action_scores = price_action_indicadores(cand_dict_estrategias) if STATE.get("usar_indicadores", True) else {}
    _indicadores_habilitados = {
        "RSI": "usar_rsi", "Aroon": "usar_aroon", "Darvas": "usar_darvas",
        "Suporte/Resistência": "usar_suporte_resistencia", "Fibonacci": "usar_fibonacci",
    }
    price_action_scores = {
        nome: sinal for nome, sinal in price_action_scores.items()
        if STATE.get(_indicadores_habilitados.get(nome, "usar_indicadores"), True)
    }
    # Estratégia Candlestick com configuração própria (período/força mínima/
    # confirmações/timeframe), separada da contagem bruta dos 35 padrões acima.
    sinal_candlestick_estrategia = _candlestick_estrategia_signal(cand_dict_estrategias)
    sinais_top5 = top5_indicadores_sinais(cand_dict_estrategias) if STATE.get("usar_top5_indicadores", True) else {}
    # Estratégia Price Action de verdade (tendência/rompimento/rejeição/pullback/extremos),
    # que antes não existia separada dos indicadores técnicos.
    sinal_price_action_estrategia = _price_action_signal(cand_dict_estrategias) if STATE.get("usar_price_action", True) else None
    
    estrategias_motor = ['P23', 'REV', 'EX4', 'TRI', '5VELA']
    sinais_motor = []
    for est in estrategias_motor:
        try:
            sig = Motor.analisar_sinal_unico(est, cand_dict)
            if sig is not None:
                sinais_motor.append((est, sig))
        except Exception:
            pass
    
    api_ia = STATE.get("api")
    rank_estrategias = {}
    if api_ia and len(cand_dict) >= 20:
        try:
            rank_estrategias = MotorIA.catalogar_v36(api_ia, ativo, estrategias_motor)
        except Exception:
            pass
    
    fatores_scores = {}

    # Voto das estratégias do catálogo. O peso é moderado para que o catálogo
    # complemente, e não substitua, os filtros de risco e o motor existente.
    min_indicadores_catalogo = max(1, min(int(STATE.get("min_indicadores_confluencia", 10) or 10), len(CATALOG_STRATEGIES)))
    catalogo_direcao = catalogo_voto.get("direcao")
    catalogo_confluencias = int(catalogo_voto.get("confluencias", 0) or 0)
    if catalogo_confluencias >= min_indicadores_catalogo and catalogo_direcao == "call":
        fatores_scores["catalogo_estrategias"] = min(2.0, 0.75 + 0.25 * catalogo_confluencias)
    elif catalogo_confluencias >= min_indicadores_catalogo and catalogo_direcao == "put":
        fatores_scores["catalogo_estrategias"] = -min(2.0, 0.75 + 0.25 * catalogo_confluencias)
    else:
        fatores_scores["catalogo_estrategias"] = 0
    # Candlestick é um único fator agregado pelos padrões configuráveis.
    # Não reaproveitamos o detector antigo em paralelo, evitando duplicidade e
    # garantindo que padrões desligados não continuem influenciando a confluência.
    cfg_candlestick = _cfg_estrategia('candlestick')
    peso_candlestick_cfg = float(cfg_candlestick.get('peso', 1.0) or 1.0)
    sinal_candlestick_unificado = sinal_candlestick_estrategia if cfg_candlestick.get('ativo', True) else None
    if sinal_candlestick_unificado == 'call': fatores_scores['candle'] = peso_candlestick_cfg
    elif sinal_candlestick_unificado == 'put': fatores_scores['candle'] = -peso_candlestick_cfg
    else: fatores_scores['candle'] = 0
    
    if sinal_fluxo == 1: fatores_scores['fluxo6'] = 1
    elif sinal_fluxo == -1: fatores_scores['fluxo6'] = -1
    else: fatores_scores['fluxo6'] = 0
    
    peso_efectiv_cfg = float(_cfg_estrategia('efectiv').get('peso', 1.0) or 1.0)
    if pos_efectiv == 1: fatores_scores['efectiv'] = peso_efectiv_cfg
    elif pos_efectiv == -1: fatores_scores['efectiv'] = -peso_efectiv_cfg
    else: fatores_scores['efectiv'] = 0
    
    if lta and not ltb: fatores_scores['lta_ltb'] = 1
    elif ltb and not lta: fatores_scores['lta_ltb'] = -1
    else: fatores_scores['lta_ltb'] = 0
    
    if sinal_of == 1: fatores_scores['order_flow'] = 1
    elif sinal_of == -1: fatores_scores['order_flow'] = -1
    else: fatores_scores['order_flow'] = 0
    
    if persistencia == 1: fatores_scores['persistencia'] = 1
    elif persistencia == -1: fatores_scores['persistencia'] = -1
    else: fatores_scores['persistencia'] = 0
    
    
    
    if vacuo == 1: fatores_scores['vacuo_liquidez'] = 1
    elif vacuo == -1: fatores_scores['vacuo_liquidez'] = -1
    else: fatores_scores['vacuo_liquidez'] = 0
    
    if sentimento['sinal'] == 1: fatores_scores['sentimento'] = 1
    elif sentimento['sinal'] == -1: fatores_scores['sentimento'] = -1
    else: fatores_scores['sentimento'] = 0
    if sentimento['forca'] > 60:
        fatores_scores['sentimento'] *= 1.5
    
    if tendencia_ia == 'call': fatores_scores['tendencia_ia'] = 0.5
    elif tendencia_ia == 'put': fatores_scores['tendencia_ia'] = -0.5
    else: fatores_scores['tendencia_ia'] = 0
    if not sequencia_ok: fatores_scores['sequencia'] = -2
    else: fatores_scores['sequencia'] = 0.5
    if not volatilidade_ok: fatores_scores['volatilidade'] = -2
    else: fatores_scores['volatilidade'] = 0
    if not pavio_ok: fatores_scores['pavio'] = -2
    else: fatores_scores['pavio'] = 0

    if sinal_cores_pro == 'call': fatores_scores['codigo_cores_pro'] = 1
    elif sinal_cores_pro == 'put': fatores_scores['codigo_cores_pro'] = -1
    else: fatores_scores['codigo_cores_pro'] = 0

    if sinal_ax1_rt == 'call': fatores_scores['ax1_rt'] = 1
    elif sinal_ax1_rt == 'put': fatores_scores['ax1_rt'] = -1
    else: fatores_scores['ax1_rt'] = 0

    fatores_scores.update(candlestick_35_scores)
    _nome_para_cfg_indicador = {
        'RSI': 'rsi', 'Aroon': 'aroon', 'Darvas': 'darvas',
        'Suporte/Resistência': 'suporte_resistencia', 'Fibonacci': 'fibonacci',
    }
    for nome_indicador, sinal_indicador in price_action_scores.items():
        chave_indicador = {
            'RSI': 'indicador_rsi',
            'Aroon': 'indicador_aroon',
            'Darvas': 'indicador_darvas',
            'Suporte/Resistência': 'indicador_suporte_resistencia',
            'Fibonacci': 'indicador_fibonacci',
        }.get(nome_indicador, 'indicador_' + nome_indicador.lower())
        peso_indicador = float(_cfg_estrategia(_nome_para_cfg_indicador.get(nome_indicador, '')).get('peso', 0.75) or 0.75)
        if sinal_indicador == 'call':
            fatores_scores[chave_indicador] = peso_indicador
        elif sinal_indicador == 'put':
            fatores_scores[chave_indicador] = -peso_indicador
        else:
            fatores_scores[chave_indicador] = 0

    # Price Action com configuração própria (peso configurável). Candlestick já
    # foi consolidado no fator `candle` acima e não é contado novamente.
    peso_price_action_cfg = float(_cfg_estrategia('price_action').get('peso', 1.0) or 1.0)
    if sinal_price_action_estrategia == 'call':
        fatores_scores['estrategia_price_action'] = peso_price_action_cfg
    elif sinal_price_action_estrategia == 'put':
        fatores_scores['estrategia_price_action'] = -peso_price_action_cfg
    else:
        fatores_scores['estrategia_price_action'] = 0

    # Top 5 portado dos fontes MQL4: cada indicador entra como fator separado,
    # respeitando o peso configurado e sem transformar o voto em ordem isolada.
    _top5_score_keys = {
        "precision_trend": "top5_precision_trend",
        "ddfx_bbstop": "top5_ddfx_bbstop",
        "double_zigzag": "top5_double_zigzag",
        "parabolic_sar": "top5_parabolic_sar",
        "forex_guru_cloud": "top5_forex_guru_cloud",
    }
    for _nome_top5, _chave_top5 in _top5_score_keys.items():
        _sinal_top5 = sinais_top5.get(_nome_top5)
        _peso_top5 = float(_cfg_estrategia(_nome_top5).get('peso', 1.0) or 1.0)
        if _sinal_top5 == 'call':
            fatores_scores[_chave_top5] = _peso_top5
        elif _sinal_top5 == 'put':
            fatores_scores[_chave_top5] = -_peso_top5
        else:
            fatores_scores[_chave_top5] = 0
    
    if mercado_estado == 'lateral':
        fatores_scores['mercado'] = -3
    else:
        fatores_scores['mercado'] = 0.5
    
    motor_score = 0
    for est, sig in sinais_motor:
        if sig == 'call': motor_score += 0.5
        elif sig == 'put': motor_score -= 0.5
        rank = rank_estrategias.get(est, 50)
        if rank > 60:
            motor_score *= 1.2
    fatores_scores['motor'] = motor_score
    
    if exaustao:
        fatores_scores['exaustao'] = -2
    else:
        fatores_scores['exaustao'] = 0
    
    if ruido:
        fatores_scores['ruído'] = -5
    else:
        fatores_scores['ruído'] = 0
    
    padrao_dom = padroes_det[0] if padroes_det else "sem_padrao"
    estado_ia = (ativo, padrao_dom, label, "estado")
    
    score_final, confianca, _direcao_ia = _calcular_score_ia(estado_ia, fatores_scores)
    confluencia = _contar_confluencia_indicadores(fatores_scores, catalogo_voto.get("sinais", {}))
    direcao_confluencia, chamadas, puts, estrategias_em_confluencia, minimo = _resolver_confluencia(confluencia)
    STATE["confluencia_estrategias"] = {
        "ativo": ativo,
        "timeframe": label,
        "direcao": direcao_confluencia,
        "estrategias": list(estrategias_em_confluencia),
        "call": list(chamadas),
        "put": list(puts),
        "total": len(chamadas) + len(puts),
        "minimo": minimo,
        "aprovada": bool(direcao_confluencia),
        "atualizado_em": time.time(),
    }

    return score_final, direcao_confluencia, estado_ia, fatores_scores

def _timeframe_configurado():
    """Retorna o timeframe configurado para coleta de candles e expiração."""
    try:
        expiracao_min = int(STATE.get("expiracao", 1))
    except (TypeError, ValueError):
        expiracao_min = 1
    if expiracao_min not in (1, 5, 15):
        expiracao_min = 1
    return expiracao_min * 60, f"M{expiracao_min}"


_JANELA_PAUSA_NOVA_ENTRADA_SEGUNDOS = 30


def _estado_janela_candle(tf_seg=None, instante=None):
    """Calcula a janela do candle sem alterar o estado do scanner.

    A pausa vale apenas enquanto o candle está em formação e faltam 30 segundos
    ou menos para o fechamento. No instante em que o próximo candle começa, o
    restante volta a ser o timeframe inteiro e as novas entradas são liberadas.
    O cálculo usa epoch, alinhado às marcas de tempo das velas da corretora.
    """
    if tf_seg is None:
        tf_seg, _ = _timeframe_configurado()
    try:
        tf = int(tf_seg)
    except (TypeError, ValueError):
        tf = 60
    if tf not in (60, 300, 900):
        tf = 60

    agora = float(time.time() if instante is None else instante)
    inicio_candle = int(agora // tf) * tf
    fechamento_candle = inicio_candle + tf
    tempo_restante = fechamento_candle - agora
    pausada = 0 < tempo_restante <= _JANELA_PAUSA_NOVA_ENTRADA_SEGUNDOS
    return {
        "timeframe_segundos": tf,
        "timeframe": _tf_label_de_segundos(tf) if "_tf_label_de_segundos" in globals() else f"M{tf // 60}",
        "inicio_candle_epoch": inicio_candle,
        "fechamento_candle_epoch": fechamento_candle,
        "tempo_restante": max(0.0, tempo_restante),
        "pausar_novas_entradas": pausada,
    }


def _novas_entradas_pausadas(tf_seg=None, instante=None):
    """Retorna True somente no trecho final do candle atual."""
    return _estado_janela_candle(tf_seg, instante)["pausar_novas_entradas"]


def analisar_script_lua(codigo):
    """Analisa scripts Lua de confirmação sem executar Lua arbitrário.

    Reconhece tanto scripts de confluência (Bollinger/RSI/EMA) quanto regras
    simples de direção por vela. Quando a regra CALL/PUT é clara, o script
    fica AUTO; quando não é possível reproduzir a regra com segurança, fica
    em REVISÃO.
    """
    texto = str(codigo or '')
    up = texto.upper()

    p = {
        'indicators': [],
        'params': {},
        'call': [],
        'put': [],
        'mode': 'unknown',
        'essential_unknown': [],
        'notes': []
    }

    if re.search(r'\b(?:SMA|BB_|BOLLINGER|STDEV|BB_UPPER|BB_LOWER)\b', up):
        p['indicators'].append('BOLLINGER')

    if re.search(r'\bRSI\s*\(', up) or 'RSI_VALUE' in up:
        p['indicators'].append('RSI')

    if re.search(r'\bEMA\s*\(', up) or 'EMA_VALUE' in up:
        p['indicators'].append('EMA')

    patterns = [
        ('bb_period', r'BB_PERIOD\s*=\s*INPUT\s*\(\s*(\d+)'),
        ('rsi_period', r'RSI_PERIOD\s*=\s*INPUT\s*\(\s*(\d+)'),
        ('ema_period', r'EMA_PERIOD\s*=\s*INPUT\s*\(\s*(\d+)')
    ]

    for key, pat in patterns:
        m = re.search(pat, up)
        if m:
            p['params'][key] = int(m.group(1))

    m = re.search(
        r'BB_MULT\s*=\s*INPUT\s*\(\s*([0-9.]+)',
        up
    )

    if m:
        p['params']['bb_mult'] = float(m.group(1))

    call_limits = [
        float(x)
        for x in re.findall(
            r'RSI_VALUE\s*<\s*(\d+(?:\.\d+)?)',
            up
        )
    ]

    put_limits = [
        float(x)
        for x in re.findall(
            r'RSI_VALUE\s*>\s*(\d+(?:\.\d+)?)',
            up
        )
    ]

    p['params']['rsi_call_max'] = (
        call_limits[0] if call_limits else None
    )

    p['params']['rsi_put_min'] = (
        put_limits[0] if put_limits else None
    )

    if len(call_limits) > 1:
        p['params']['rsi_call_aggressive'] = call_limits[-1]

    if len(put_limits) > 1:
        p['params']['rsi_put_aggressive'] = put_limits[-1]

    has_low = (
        'TOUCHLOWER' in up
        or bool(re.search(r'LOW\s*<=\s*BB_LOWER', up))
    )

    has_up = (
        'TOUCHUPPER' in up
        or bool(re.search(r'HIGH\s*>=\s*BB_UPPER', up))
    )

    has_rsi = (
        'RSI_VALUE' in up
        or bool(re.search(r'RSI\s*\(', up))
    )

    has_buy = (
        'BUYENTRY' in up
        or bool(re.search(r'\bCALL\b', up))
    )

    has_sell = (
        'SELLENTRY' in up
        or bool(re.search(r'\bPUT\b', up))
    )

    ema_call = bool(
        re.search(r'CLOSE\s*>\s*EMA_VALUE', up)
    )

    ema_put = bool(
        re.search(r'CLOSE\s*<\s*EMA_VALUE', up)
    )

    has_ema = 'EMA_VALUE' in up
    ema_filter = has_ema and ema_call and ema_put

    candle_call = bool(
        re.search(
            r'(?:CALLE[N]?TRY|CALLENTRY)\s*=\s*CLOSE\s*>\s*OPEN',
            up
        )
    )

    candle_put = bool(
        re.search(
            r'(?:PUTENTRY|SELLENTRY)\s*=\s*CLOSE\s*<\s*OPEN',
            up
        )
    )

    if not candle_call:
        candle_call = bool(
            re.search(
                r"PLOT_SHAPE\s*\(\s*CLOSE\s*>\s*OPEN\s*,\s*['\"]CALL",
                up
            )
        )

    if not candle_put:
        candle_put = bool(
            re.search(
                r"PLOT_SHAPE\s*\(\s*CLOSE\s*<\s*OPEN\s*,\s*['\"]PUT",
                up
            )
        )

    if has_low and has_up and has_rsi and has_buy and has_sell:

        p['mode'] = 'auto'
        p['params']['ema_filter'] = ema_filter

        mmodo = re.search(
            r'MODO\s*=\s*INPUT\s*\(\s*1',
            up
        )

        p['params']['modo_default'] = (
            'conservador'
            if mmodo
            else 'desconhecido'
        )

        p['params']['rsi_call_max'] = (
            p['params']['rsi_call_max']
            if p['params']['rsi_call_max'] is not None
            else 45.0
        )

        p['params']['rsi_put_min'] = (
            p['params']['rsi_put_min']
            if p['params']['rsi_put_min'] is not None
            else 55.0
        )

        p['call_rule'] = (
            'toque banda inferior + RSI abaixo de '
            + str(p['params']['rsi_call_max'])
            + (
                ' + close acima da EMA'
                if ema_filter
                else ''
            )
        )

        p['put_rule'] = (
            'toque banda superior + RSI acima de '
            + str(p['params']['rsi_put_min'])
            + (
                ' + close abaixo da EMA'
                if ema_filter
                else ''
            )
        )

        p['call'].append(p['call_rule'])
        p['put'].append(p['put_rule'])

    elif candle_call and candle_put:

        p['mode'] = 'auto'
        p['params']['candle_direction'] = True

        p['call_rule'] = 'vela verde: close > open'
        p['put_rule'] = 'vela vermelha: close < open'

        p['call'].append(p['call_rule'])
        p['put'].append(p['put_rule'])

        p['notes'].append(
            'Regra simples de direção por cor da vela.'
        )

    else:

        faltantes = []

        if not (has_low or candle_call):
            faltantes.append('regra CALL')

        if not (has_up or candle_put):
            faltantes.append('regra PUT')

        if 'BOLLINGER' in p['indicators'] and not has_low:
            faltantes.append('toque banda inferior')

        if 'BOLLINGER' in p['indicators'] and not has_up:
            faltantes.append('toque banda superior')

        if 'RSI' in p['indicators'] and not has_rsi:
            faltantes.append('RSI')

        if not faltantes:
            faltantes.append(
                'regras CALL/PUT não reconhecidas'
            )

        p['essential_unknown'].append(
            'Não foi possível mapear integralmente: '
            + ', '.join(dict.fromkeys(faltantes))
        )

    if (
        'BOLLINGER' in p['indicators']
        and 'bb_period' not in p['params']
    ):
        p['essential_unknown'].append(
            'Período da Bollinger não identificado.'
        )

    if (
        'RSI' in p['indicators']
        and 'rsi_period' not in p['params']
    ):
        p['essential_unknown'].append(
            'Período do RSI não identificado.'
        )

    if (
        'EMA' in p['indicators']
        and 'ema_period' not in p['params']
        and ema_filter
    ):
        p['essential_unknown'].append(
            'Período da EMA não identificado.'
        )

    if (
        'BOLLINGER' in p['indicators']
        and 'bb_mult' not in p['params']
    ):
        p['essential_unknown'].append(
            'Desvio da Bollinger não identificado.'
        )

    p['status'] = (
        'AUTO'
        if p['mode'] == 'auto'
        and not p['essential_unknown']
        else (
            'REVIEW'
            if (
                p['indicators']
                or has_buy
                or has_sell
            )
            else 'INCOMPATIBLE'
        )
    )

    return p


def salvar_script_confirmacao(nome, codigo, active=True):

    nome = str(nome or '').strip()[:120]
    codigo = str(codigo or '').strip()

    if not nome or not codigo:
        return False, 'Nome e código são obrigatórios.'

    parsed = analisar_script_lua(codigo)
    status = parsed['status']

    try:
        with SCRIPT_DB_LOCK:
            conn = _script_db()

            conn.execute(
                """
                INSERT INTO confirmation_scripts(
                    name,
                    code,
                    parsed,
                    status,
                    active,
                    updated_at
                )
                VALUES(
                    ?, ?, ?, ?, ?, CURRENT_TIMESTAMP
                )

                ON CONFLICT(name) DO UPDATE SET
                    code=excluded.code,
                    parsed=excluded.parsed,
                    status=excluded.status,
                    active=excluded.active,
                    updated_at=CURRENT_TIMESTAMP
                """,
                (
                    nome,
                    codigo,
                    json.dumps(
                        parsed,
                        ensure_ascii=False
                    ),
                    status,
                    1 if status == 'AUTO' and active else 0
                )
            )

            conn.commit()
            conn.close()

        return True, status

    except Exception as e:
        return False, str(e)

_LUA_FORBIDDEN_PATTERNS = (
    ("os.", r"(?<![A-Za-z0-9_])os\s*\."),
    ("io.", r"(?<![A-Za-z0-9_])io\s*\."),
    ("debug.", r"(?<![A-Za-z0-9_])debug\s*\."),
    ("package", r"(?<![A-Za-z0-9_])package(?![A-Za-z0-9_])"),
    ("require", r"(?<![A-Za-z0-9_])require\s*\("),
    ("dofile", r"(?<![A-Za-z0-9_])dofile\s*\("),
    ("loadfile", r"(?<![A-Za-z0-9_])loadfile\s*\("),
    ("load(", r"(?<![A-Za-z0-9_])load\s*\("),
    ("os[", r"(?<![A-Za-z0-9_])os\s*\["),
    ("io[", r"(?<![A-Za-z0-9_])io\s*\["),
)

def _autorizar_script_lua(script):
    texto = str(script or "").replace("\r\n", "\n").strip()
    if not texto:
        return False, "Insira um script Lua Quadcode antes de salvar."
    if len(texto) > 120_000:
        return False, "O script excede o limite de 120 KB."
    proibido = next((token for token, pattern in _LUA_FORBIDDEN_PATTERNS if re.search(pattern, texto, re.I)), None)
    if proibido:
        return False, f"Token não permitido no script: {proibido}"

    # Primeiro passa pelo leitor determinístico fornecido. Isso reconhece
    # confluência Bollinger/RSI/EMA e regras simples de vela sem executar Lua.
    parsed = analisar_script_lua(texto)
    if parsed.get("status") == "AUTO":
        return True, "Script Lua Quadcode autorizado pelo leitor automático."

    # Mantém compatibilidade com os adaptadores locais já implementados para
    # SCRIPT CASH, signal/on_candle e plot_shape comparativo.
    legado = (
        re.search(r"\binstrument\s*\{", texto, re.I)
        or re.search(r"\bplot_shape\s*\(", texto, re.I)
        or re.search(r"\bfunction\s+(signal|on_candle)\s*\(", texto, re.I)
        or re.search(r"(?im)^\s*--\s*MEUROBO_SIGNAL\s*:\s*(CALL|PUT)\s*$", texto)
        or (re.search(r"buffer1\s*=\s*smaFast\s*-\s*smaSlow", texto, re.I)
            and re.search(r"buffer2\s*=\s*wma\s*\(\s*buffer1", texto, re.I))
    )
    if legado:
        return True, "Script Lua Quadcode autorizado (compatibilidade local)."

    detalhes = "; ".join(parsed.get("essential_unknown") or [])
    return False, "Leitor automático não conseguiu mapear CALL/PUT com segurança" + (f": {detalhes}" if detalhes else ".")


class _QCSSeries:
    """Série QCS mínima: [0] é a barra atual e [1] a anterior."""
    def __init__(self, values, pos):
        self.values = values
        self.pos = pos
    def __getitem__(self, offset):
        try: idx = self.pos - int(offset)
        except (TypeError, ValueError): return None
        return self.values[idx] if 0 <= idx < len(self.values) else None
    def _v(self): return self[0]
    def _o(self, other): return other._v() if isinstance(other, _QCSSeries) else other
    def __add__(self, o): return (self._v() or 0) + (self._o(o) or 0)
    def __radd__(self, o): return (o or 0) + (self._v() or 0)
    def __sub__(self, o): return (self._v() or 0) - (self._o(o) or 0)
    def __rsub__(self, o): return (o or 0) - (self._v() or 0)
    def __mul__(self, o): return (self._v() or 0) * (self._o(o) or 0)
    def __rmul__(self, o): return (o or 0) * (self._v() or 0)
    def __truediv__(self, o): return (self._v() or 0) / (self._o(o) or 1)
    def __rtruediv__(self, o): return (o or 0) / (self._v() or 1)
    def __lt__(self, o): return self._v() is not None and self._v() < self._o(o)
    def __le__(self, o): return self._v() is not None and self._v() <= self._o(o)
    def __gt__(self, o): return self._v() is not None and self._v() > self._o(o)
    def __ge__(self, o): return self._v() is not None and self._v() >= self._o(o)
    def __eq__(self, o): return self._v() == self._o(o)
    def __bool__(self): return bool(self._v())
    def __abs__(self): return abs(self._v() or 0)


def _qcs_series_calc(values, pos, period, kind='sma'):
    period = max(1, int(period or 1)); out = []
    for i in range(len(values)):
        sample = values[max(0, i-period+1):i+1]
        if len(sample) < period or any(v is None for v in sample): out.append(None); continue
        if kind == 'wma':
            den = period * (period + 1) / 2
            out.append(sum(v*w for v,w in zip(sample, range(1, period+1))) / den)
        else: out.append(sum(sample) / period)
    return _QCSSeries(out, pos)


def _qcs_split_args(text):
    args=[]; start=0; depth=0; quote=None
    for i,ch in enumerate(text):
        if quote:
            if ch == quote and (i == 0 or text[i-1] != '\\'): quote=None
        elif ch in "'\"": quote=ch
        elif ch in '([{': depth += 1
        elif ch in ')]}': depth -= 1
        elif ch == ',' and depth == 0:
            args.append(text[start:i].strip()); start=i+1
    args.append(text[start:].strip())
    return args


def _qcs_plot_calls(script):
    calls=[]; pos=0; needle='plot_shape'
    while True:
        begin=script.lower().find(needle, pos)
        if begin < 0: break
        open_at=script.find('(', begin)
        if open_at < 0: break
        depth=0; quote=None; close_at=None
        for i in range(open_at, len(script)):
            ch=script[i]
            if quote:
                if ch == quote and script[i-1] != '\\': quote=None
            elif ch in "'\"": quote=ch
            elif ch == '(' : depth += 1
            elif ch == ')':
                depth -= 1
                if depth == 0: close_at=i; break
        if close_at is None: break
        args=_qcs_split_args(script[open_at+1:close_at])
        if len(args) >= 2:
            offset = args[6].strip() if len(args) >= 7 else '0'
            calls.append((args[0], args[1].strip(" '\""), offset))
        pos=close_at+1
    return calls


def _qcs_generic_signal(script, candles):
    """Executa um subconjunto amplo e seguro do QCS sem executar Lua arbitrário."""
    if not candles or not re.search(r'plot_shape\s*\(', script, re.I): return None
    calls = _qcs_plot_calls(script)
    if not calls: return None
    n=len(candles); fields={}
    for key in ('open','high','low','close'):
        fields[key]=[float(c.get(key, c.get(key+'_price'))) for c in candles]
    # Defaults comuns de visibilidade para scripts que declaram grupos omitidos.
    visible={name: True for name in re.findall(r'\bvisible[A-Za-z0-9_]*', script)}
    def sma(source, period): return _qcs_series_calc(source.values if isinstance(source,_QCSSeries) else source, pos, period, 'sma')
    def wma(source, period): return _qcs_series_calc(source.values if isinstance(source,_QCSSeries) else source, pos, period, 'wma')
    def ema(source, period):
        vals=source.values if isinstance(source,_QCSSeries) else source; a=2/(int(period)+1); out=[]
        for i,v in enumerate(vals): out.append(v if i==0 else (None if v is None or out[-1] is None else a*v+(1-a)*out[-1]))
        return _QCSSeries(out,pos)
    def security(*args): return _QCSSeries(fields['close'],pos)
    # Parse numeric input defaults, including named input_group declarations.
    inputs={}
    for name, val in re.findall(r'\b([A-Za-z_]\w*)\s*=\s*input\s*\(\s*(-?\d+(?:\.\d+)?)', script, re.I):
        inputs[name]=float(val) if '.' in val else int(val)
    calls_found=[]
    # Avaliar primeiro a vela atual e, se ela não tiver sinal, a última vela
    # anterior. Isso permite capturar scripts que desenham o marcador na vela
    # anterior ou que só confirmam a condição quando a vela fecha.
    # A origem é incluída no motivo para o scanner não confundir os dois casos.
    for pos in [n - 1, n - 2]:
        if pos < 0:
            continue
        env={'abs':abs,'math':math,'sma':sma,'wma':wma,'ema':ema,'security':security,'true':True,'false':False,'nil':None}
        env.update(visible); env.update(inputs)
        for key, vals in fields.items(): env[key]=_QCSSeries(vals,pos)
        env['inputs']={}; env['averages']={}
        # Basic QCS title/average selections.
        title_map={1:_QCSSeries(fields['open'],pos),2:_QCSSeries(fields['high'],pos),3:_QCSSeries(fields['low'],pos),4:_QCSSeries(fields['close'],pos),5:_QCSSeries([(h+l)/2 for h,l in zip(fields['high'],fields['low'])],pos),6:_QCSSeries([(h+l+c)/3 for h,l,c in zip(fields['high'],fields['low'],fields['close'])],pos),7:_QCSSeries([(o+h+l+c)/4 for o,h,l,c in zip(fields['open'],fields['high'],fields['low'],fields['close'])],pos)}
        env['inputs']=title_map; env['averages']={1:sma,2:ema,3:wma,4:sma,5:ema}
        # Evaluate simple assignments in source order. Unsupported drawing/config
        # statements are ignored; signal expressions remain safe eval only.
        for raw in script.splitlines():
            line=re.sub(r'--.*$', '', raw).strip()
            if not line or line.startswith(('if ','elseif ','else','end','input_group','instrument')): continue
            m=re.match(r'(?:local\s+)?([A-Za-z_]\w*)\s*=\s*(.+)$', line)
            if not m or '==' in m.group(2) or m.group(2).startswith('{'): continue
            name, expr=m.group(1),m.group(2).strip()
            expr=expr.replace('~=','!=').replace(' and ',' and ').replace(' or ',' or ')
            expr=re.sub(r'\btrue\b','True',expr,flags=re.I); expr=re.sub(r'\bfalse\b','False',expr,flags=re.I); expr=re.sub(r'\bnil\b','None',expr,flags=re.I)
            expr=re.sub(r'\bcurrent_ticker_id\b','None',expr)
            try: env[name]=eval(expr, {'__builtins__':{}}, env)
            except Exception: pass
        for expr,label,offset in calls:
            expr=expr.replace('~=','!=').replace(' and ',' and ').replace(' or ',' or ')
            expr=re.sub(r'\btrue\b','True',expr,flags=re.I); expr=re.sub(r'\bfalse\b','False',expr,flags=re.I)
            try:
                if bool(eval(expr, {'__builtins__':{}}, env)):
                    low=label.lower()
                    if 'call' in low or low in ('buy','compra'): calls_found.append(('call',100.0,f"QCS plot_shape: {label} ({'vela atual' if pos == n - 1 else 'vela anterior'}, deslocamento {offset})"))
                    elif 'put' in low or 'sell' in low or 'venda' in low: calls_found.append(('put',100.0,f"QCS plot_shape: {label} ({'vela atual' if pos == n - 1 else 'vela anterior'}, deslocamento {offset})"))
            except Exception: continue
    return calls_found[0] if calls_found else None

def _script_lua_signal(candles):
    """Interpreta o contrato seguro do modo manual.

    Quadcode continua sendo a linguagem de entrada. Para permitir execução local
    sem expor o processo a Lua arbitrário, o adaptador aceita sinais explícitos,
    o cruzamento determinístico do SCRIPT CASH e formas simples de plot_shape.
    O SCRIPT CASH pode usar a vela mais recente para compensar seu plot_shape
    com deslocamento -1; os demais scripts usam apenas candles fechados.
    """
    script = str(STATE.get("script_lua") or "")
    autorizado, erro = _autorizar_script_lua(script)
    STATE["script_lua_autorizado"] = bool(autorizado)
    STATE["script_lua_erro"] = "" if autorizado else erro
    if not autorizado or not candles:
        return None, 0.0, erro
    # O SCRIPT CASH possui um interpretador determinístico próprio para
    # SMA/WMA e cruzamento. Ele precisa ser priorizado: o runtime genérico
    # não deve interceptar o script e transformar um cruzamento válido em
    # "sem sinal".
    eh_script_cash = (
        re.search(r"\bbuffer1\s*=\s*smaFast\s*-\s*smaSlow", script, re.I)
        and re.search(r"\bbuffer2\s*=\s*wma\s*\(\s*buffer1", script, re.I)
        and re.search(r"\bplot_shape\s*\(", script, re.I)
    )
    # Alguns scripts colocam `1` no plot_shape e deixam a regra real no
    # if externo. Reconhecer esse padrão antes do runtime evita interpretar
    # a seta como sinal permanente e reproduz exatamente o engolfo informado.
    eh_engolfo = (
        re.search(r'close\s*\[\s*1\s*\]\s*<\s*open\s*\[\s*1\s*\]', script, re.I)
        and re.search(r'close\s*>\s*high\s*\[\s*1\s*\]', script, re.I)
        and re.search(r'close\s*\[\s*2\s*\]\s*>=\s*open', script, re.I)
        and re.search(r'close\s*\[\s*1\s*\]\s*>\s*open\s*\[\s*1\s*\]', script, re.I)
        and re.search(r'close\s*<\s*low\s*\[\s*1\s*\]', script, re.I)
        and re.search(r'close\s*\[\s*2\s*\]\s*<=\s*open', script, re.I)
    )
    if eh_engolfo and len(candles) >= 3:
        def _num(c, key, fallback=None):
            value = c.get(key, fallback)
            return float(value) if value is not None else None
        def _engolfo_at(i):
            if i < 2: return None
            cur, prev, prev2 = candles[i], candles[i-1], candles[i-2]
            o, c = _num(cur, 'open', cur.get('open_price')), _num(cur, 'close', cur.get('close_price'))
            po, pc = _num(prev, 'open', prev.get('open_price')), _num(prev, 'close', prev.get('close_price'))
            ph, pl = _num(prev, 'high', prev.get('max')), _num(prev, 'low', prev.get('min'))
            p2c = _num(prev2, 'close', prev2.get('close_price'))
            if None in (o,c,po,pc,ph,pl,p2c): return None
            if pc < po and c > o and c > ph and p2c >= o: return 'call'
            if pc > po and c < o and c < pl and p2c <= o: return 'put'
            return None
        for idx in (len(candles)-1, len(candles)-2):
            direction = _engolfo_at(idx)
            if direction:
                origem = 'vela atual' if idx == len(candles)-1 else 'vela anterior'
                nome = 'COMPRA!' if direction == 'call' else 'VENDA!'
                return direction, 100.0, f'Quadcode {nome}: condição if/elseif confirmada ({origem})'
        return None, 0.0, 'script de engolfo sem sinal na vela atual ou anterior'

    # Primeiro tenta o runtime amplo para scripts gerais com séries,
    # averages, security, condições multilinha e múltiplos plot_shape.
    try:
        qcs_result = None if eh_script_cash else _qcs_generic_signal(script, candles)
        if qcs_result:
            return qcs_result
        if (not eh_script_cash) and re.search(r'plot_shape\s*\(', script, re.I):
            return None, 0.0, 'sem sinal na vela atual ou anterior'
    except Exception as _qcs_error:
        _log_scan(f"⚠️ QCS runtime fallback: {_qcs_error}")
    # O Quadcode avalia sinais na vela fechada. A última vela retornada pela
    # corretora normalmente ainda está em formação; usá-la causa sinais que
    # aparecem/desaparecem aleatoriamente no painel. Remova-a quando houver
    # timestamp disponível e mantenha somente candles cujo fechamento já passou.
    try:
        tf_seg = int(STATE.get("expiracao", 1) or 1) * 60
    except (TypeError, ValueError):
        tf_seg = 60
    agora = time.time()
    fechadas = []
    for candle in candles:
        try:
            inicio = float(candle.get("from", candle.get("id")))
            if inicio > 100_000_000_000:
                inicio /= 1000.0
            if inicio + tf_seg <= agora + 0.25:
                fechadas.append(candle)
        except (AttributeError, TypeError, ValueError):
            pass

    # O SCRIPT CASH original desenha o plot_shape com deslocamento -1. Se o
    # leitor esperar a confirmação da vela fechada, o marcador visual aparece
    # uma vela antes e a ordem parece sair duas velas depois. Para esse script,
    # preserve a vela mais recente retornada pela corretora e avalie o mesmo
    # cruzamento em tempo real, como o Quadcode faz durante a formação.
    if eh_script_cash:
        candles = list(candles)
    else:
        # Nos demais scripts, a política segura continua sendo usar somente
        # candles fechados para não liberar sinais que possam repintar.
        if not fechadas:
            fechadas = list(candles[:-1]) if len(candles) > 1 else []
        candles = fechadas
    if not candles:
        return None, 0.0, "aguardando candle fechado"
    upper = script.upper()
    # A diretiva de teste só é válida em comentário de linha. Antes, qualquer
    # ocorrência dentro de uma string, nome de variável ou texto copiado podia
    # liberar uma direção que não fazia parte da lógica do script.
    explicit = re.findall(r"(?im)^\s*--\s*MEUROBO_SIGNAL\s*:\s*(CALL|PUT)\s*$", script)
    if explicit:
        direcao = explicit[-1].lower()
        return direcao, 100.0, "sinal explícito autorizado"
    last = candles[-1]
    try:
        op = float(last.get("open", last.get("open_price", 0)))
        cl = float(last.get("close", last.get("close_price", 0)))
    except (TypeError, ValueError):
        return None, 0.0, "vela inválida"

    # Compatibilidade com o padrão Quadcode do SCRIPT CASH:
    # buffer1 = smaFast - smaSlow; buffer2 = wma(buffer1, Signal_period)
    # buyCondition/sellCondition são cruzamentos confirmados entre as séries.
    # O adaptador usa a série close (equivalente ao título padrão mais comum)
    # e avalia somente candles fechados.
    if re.search(r"buffer1\s*=\s*smaFast\s*-\s*smaSlow", script, re.I) and re.search(r"buffer2\s*=\s*wma\s*\(\s*buffer1", script, re.I):
        def _lua_input_int(nome, padrao):
            achado = re.search(r"\b" + re.escape(nome) + r"\s*=\s*input\(\s*(\d+)", script, re.I)
            return max(1, min(1000, int(achado.group(1)))) if achado else padrao
        fast_period = _lua_input_int("MaFast_period", 1)
        slow_period = _lua_input_int("MaSlow_period", 34)
        signal_period = _lua_input_int("Signal_period", 5)

        # `inputs.titles` do Quadcode usa MaValue para escolher a série de
        # preço. No SCRIPT CASH, o valor padrão 5 corresponde a HL2.
        # Não substituir silenciosamente essa série por close: isso muda os
        # pontos de cruzamento e faz o robô divergir do indicador original.
        mvalue_match = re.search(
            r"\bMaValue\s*=\s*input\(\s*(\d+)", script, re.I
        )
        ma_value = int(mvalue_match.group(1)) if mvalue_match else 5
        ma_value = max(1, min(7, ma_value))

        def _title_value(candle):
            try:
                op = float(candle.get("open", candle.get("open_price")))
                hi = float(candle.get("high", candle.get("max")))
                lo = float(candle.get("low", candle.get("min")))
                cl = float(candle.get("close", candle.get("close_price")))
            except (AttributeError, TypeError, ValueError):
                return None
            # Ordem compatível com inputs.titles: open, high, low, close,
            # hl2, hlc3 e ohlc4.
            return {
                1: op,
                2: hi,
                3: lo,
                4: cl,
                5: (hi + lo) / 2.0,
                6: (hi + lo + cl) / 3.0,
                7: (op + hi + lo + cl) / 4.0,
            }[ma_value]

        closes = [_title_value(candle) for candle in candles]
        required = slow_period + signal_period + 3
        if len(closes) >= required and all(v is not None for v in closes[-required:]):
            def _sma_at(values, index, period):
                if index + 1 < period: return None
                sample=values[index-period+1:index+1]
                return sum(sample) / period if all(v is not None for v in sample) else None
            fast=[]; slow=[]
            for idx in range(len(closes)):
                fast.append(_sma_at(closes, idx, fast_period))
                slow.append(_sma_at(closes, idx, slow_period))
            buffer1=[(a-b if a is not None and b is not None else None) for a,b in zip(fast,slow)]
            def _wma_at(values, index, period):
                if index + 1 < period: return None
                sample=values[index-period+1:index+1]
                if any(v is None for v in sample): return None
                peso=sum(range(1,period+1))
                return sum(value * weight for value,weight in zip(sample,range(1,period+1))) / peso
            buffer2=[_wma_at(buffer1, idx, signal_period) for idx in range(len(buffer1))]
            # [1] no Quadcode representa a barra anterior.
            if buffer1[-1] is not None and buffer2[-1] is not None and buffer1[-2] is not None and buffer2[-2] is not None:
                # O código Quadcode dispara somente no candle do cruzamento:
                # buyCondition: buffer1 > buffer2 e buffer1[1] < buffer2[1]
                # sellCondition: buffer1 < buffer2 e buffer1[1] > buffer2[1]
                compra = buffer1[-1] > buffer2[-1] and buffer1[-2] < buffer2[-2]
                venda = buffer1[-1] < buffer2[-1] and buffer1[-2] > buffer2[-2]
                if compra:
                    return "call", 100.0, f"SCRIPT CASH: buyCondition confirmado; série {ma_value}, SMA({fast_period}/{slow_period}) + WMA({signal_period})"
                if venda:
                    return "put", 100.0, f"SCRIPT CASH: sellCondition confirmado; série {ma_value}, SMA({fast_period}/{slow_period}) + WMA({signal_period})"
            return None, 0.0, "script CASH aguardando cruzamento SMA/WMA"
    # Avalia as formas simples e documentadas de plot_shape. A condição é
    # aplicada somente à última vela fechada; não se usa a vela em formação e
    # não se infere direção pela cor da vela quando o script não declarou uma
    # condição correspondente.
    def _valor_ref(ref):
        ref = ref.strip().lower()
        deslocamento = 0
        m = re.fullmatch(r"(open|close)\s*\[\s*(\d+)\s*\]", ref)
        if m:
            ref, deslocamento = m.group(1), int(m.group(2))
        elif ref not in ("open", "close"):
            return None
        idx = len(candles) - 1 - deslocamento
        if idx < 0:
            return None
        try:
            chave = "open" if ref == "open" else "close"
            return float(candles[idx].get(chave, candles[idx].get(f"{chave}_price")))
        except (AttributeError, TypeError, ValueError):
            return None

    def _condicao(condicao):
        # Permite apenas comparações numéricas entre open/close e referências
        # indexadas. Expressões desconhecidas são rejeitadas, nunca inferidas.
        m = re.fullmatch(r"\s*(open|close)(?:\s*\[\s*(\d+)\s*\])?\s*(>=|<=|==|~=|>|<)\s*(open|close)(?:\s*\[\s*(\d+)\s*\])?\s*", condicao, re.I)
        if not m:
            return None
        esquerda = _valor_ref(f"{m.group(1)}[{m.group(2)}]" if m.group(2) else m.group(1))
        direita = _valor_ref(f"{m.group(4)}[{m.group(5)}]" if m.group(5) else m.group(4))
        if esquerda is None or direita is None:
            return None
        operador = m.group(3)
        return {">": esquerda > direita, "<": esquerda < direita,
                ">=": esquerda >= direita, "<=": esquerda <= direita,
                "==": esquerda == direita, "~=": esquerda != direita}[operador]

    encontrados = re.findall(r"plot_shape\s*\(\s*([^,\n]+)\s*,\s*['\"](CALL|PUT)['\"]", script, re.I)
    for condicao, rotulo in encontrados:
        resultado = _condicao(condicao)
        if resultado is True:
            return rotulo.lower(), 100.0, f"plot_shape confirmado: {condicao.strip()}"

    # Não invente sinais para condições não suportadas. Isso evita o fallback
    # anterior que podia parecer aleatório ao alternar entre candles.
    return None, 0.0, "script autorizado: padrão Quadcode não suportado deterministicamente"

def analisar_confluencia(ativo, respeitar_janela_busca=True):
    """Busca sinais no timeframe configurado e exige confluência.

    A janela temporal é aplicada somente quando a função está sendo usada para
    procurar um novo sinal no scanner. Fluxos que já possuem uma direção
    confirmada podem chamar esta função sem repetir essa trava.
    """
    ativo = _definir_ativo_em_foco(ativo, limpar_confluencia=True) or ativo
    api = STATE.get("api")
    tf_seg, tf_label = _timeframe_configurado()
    if not api:
        return None, None, tf_seg, 0, None, {}

    _log_scan(f"🔎 [CONFLUÊNCIA] Analisando indicadores em {tf_label} para {ativo}...")
    try:
        active_id = _resolver_active_id(ativo)
        if active_id is None:
            _log_scan(f"⚠️ {ativo}/{tf_label}: active_id não encontrado no catálogo da corretora; requisição não enviada.")
            return None, None, tf_seg, 0, None, {}
        velas_raw = _api_call_com_timeout(api.get_candles, 15, active_id, tf_seg, 200, time.time())
        if not velas_raw:
            _log_scan(f"⏱️ {ativo}/{tf_label}: corretora não respondeu com velas em 15s.")
            return None, None, tf_seg, 0, None, {}

        df = _candles_para_df(velas_raw)
        if df.empty or len(df) < 15:
            _log_scan(f"⏱️ {ativo}/{tf_label}: velas insuficientes ({len(df)}).")
            return None, None, tf_seg, 0, None, {}

        janela_busca = _janela_busca_sinais(tf_seg)
        try:
            inicio_busca = _inicio_vela_atual(df, tf_seg)
            idade_vela = max(0.0, time.time() - inicio_busca)
        except (TypeError, ValueError):
            _log_scan(f"⏱️ {ativo}/{tf_label}: início da vela indisponível para validar a janela de busca.")
            return None, None, tf_seg, 0, None, {}
        if respeitar_janela_busca and idade_vela > janela_busca:
            _log_scan(
                f"⏭ {ativo}/{tf_label}: busca de sinais encerrada aos {janela_busca}s "
                f"(vela com {idade_vela:.1f}s). Aguardando a próxima vela."
            )
            return None, None, tf_seg, 0, None, {}

        cotacao_atual, fonte_cotacao = _obter_cotacao_ao_vivo(api, ativo, tf_seg, df)
        # MODO SCRIPT-ONLY: nenhum indicador, catálogo, candlestick ou IA participa.
        candles_script = df.to_dict("records")
        direcao_script, score_script, motivo_script = _script_lua_signal(candles_script)
        if not STATE.get("script_lua_autorizado"):
            _log_scan(f"⏭ {ativo}/{tf_label}: entrada bloqueada — {STATE.get('script_lua_erro')}")
        else:
            _log_scan(f"🧩 [LUA QUADCODE] {ativo}/{tf_label}: {motivo_script}")
        if direcao_script in ("call", "put"):
            STATE["confluencia_estrategias"] = {
                "ativo": ativo, "timeframe": tf_label, "direcao": direcao_script,
                "estrategias": ["Script Lua Quadcode"],
                "call": ["Script Lua Quadcode"] if direcao_script == "call" else [],
                "put": ["Script Lua Quadcode"] if direcao_script == "put" else [],
                "total": 1, "minimo": 1, "aprovada": True, "atualizado_em": time.time(),
            }
            return direcao_script, tf_label, tf_seg, score_script, None, {"script_lua": score_script}
        STATE["confluencia_estrategias"] = {
            "ativo": ativo, "timeframe": tf_label, "direcao": None,
            "estrategias": [], "call": [], "put": [], "total": 0,
            "minimo": 1, "aprovada": False, "atualizado_em": time.time(),
        }
        return None, tf_label, tf_seg, 0.0, None, {"script_lua": 0.0}
    except Exception as e:
        _log_scan(f"⚠️ Erro ao buscar velas {tf_label} de {ativo}: {e}")
        return None, None, tf_seg, 0, None, {}

def verificar_horario(asset=None):
    hora_ini = STATE.get("horario_inicio", "00:00")
    hora_fim = STATE.get("horario_fim", "23:59")
    agora = _agora_brasilia().strftime("%H:%M")
    if not (hora_ini <= agora <= hora_fim):
        return False
    permitido, _ = _ttz_check_entry(asset)
    return permitido

def stop_atingido():
    try:
        acumulado = float(STATE.get("saldo_acumulado", 0.0) or 0.0)
        stop_win = max(0.01, float(STATE.get("stop_win", 100.0) or 100.0))
        stop_loss = max(0.01, float(STATE.get("stop_loss", 100.0) or 100.0))
    except (TypeError, ValueError):
        return False
    return acumulado >= stop_win or acumulado <= -abs(stop_loss)

def encerrar_por_stop():
    """Encerra a sessão assim que um limite financeiro é atingido."""
    if not stop_atingido():
        return False
    if STATE.get("running"):
        acumulado = float(STATE.get("saldo_acumulado", 0.0) or 0.0)
        stop_win = float(STATE.get("stop_win", 100.0) or 100.0)
        motivo = "STOP WIN ✅" if acumulado >= stop_win else "STOP LOSS 🛑"
        _log_scan(
            f"🎯 {motivo} | Sessão: R${acumulado:+.2f} | "
            f"W:{STATE.get('wins', 0)} L:{STATE.get('losses', 0)} E:{STATE.get('empates', 0)}"
        )
        STATE["running"] = False
        STATE["gale_pendente"] = None
        _emit_status("stop atingido")
    return True

def _tf_label_de_segundos(tf_seg):
    return {60: "M1", 300: "M5", 900: "M15"}.get(tf_seg, f"{tf_seg}s")

def registrar_op(ativo, direcao, valor, resultado, lucro, camada_gale=0, tf_seg=None, modalidade=None, mercado=None, vela_entrada=None, ordem_id=None, soros_nivel=None, soros_pct=None):
    """Registra o que foi efetivamente enviado e o resultado confirmado."""
    soros_em_uso = bool(STATE.get("usar_soros"))
    soros_status = gerenciador_soros.get_status()
    nivel_soros = soros_status.get("nivel_atual") if soros_nivel is None and soros_em_uso else soros_nivel
    pct_soros = soros_status.get("reinvestimento") if soros_pct is None and soros_em_uso else soros_pct
    instante = _agora_brasilia()
    op = {
        "ts": instante.strftime("%H:%M:%S"),
        "momento_execucao": instante.isoformat(),
        "ativo": ativo,
        "direcao": str(direcao or "").upper(),
        "valor": round(float(valor), 2),
        "valor_enviado": round(float(valor), 2),
        "resultado": resultado,
        "lucro": round(float(lucro or 0), 2),
        "gale": int(camada_gale or 0),
        "nivel_martingale": int(camada_gale or 0),
        "fator_gale": STATE.get("fator_gale") if camada_gale > 0 else None,
        "fator_martingale": STATE.get("fator_gale"),
        "soros_nivel": nivel_soros,
        "nivel_soros": nivel_soros,
        "soros_pct": pct_soros,
        "porcentagem_soros": pct_soros,
        "ordem_id": str(ordem_id) if ordem_id is not None else None,
        "operacao_id": str(ordem_id) if ordem_id is not None else None,
        "saldo_apos": round(STATE.get("saldo", 0.0), 2),
        "tf": _tf_label_de_segundos(tf_seg) if tf_seg else "-",
        "tf_seg": int(tf_seg) if tf_seg else None,
        "modalidade": (modalidade or "").upper(),
        "mercado": mercado or _identificar_mercado_ativo(ativo),
        "vela_entrada": int(vela_entrada) if vela_entrada is not None else None,
    }
    STATE["historico"].insert(0, op)
    STATE["historico"] = STATE["historico"][:5]
    STATE["ultima_operacao"] = op
    if STATE.get("operacao_atual") and STATE["operacao_atual"].get("ativo") == ativo:
        STATE["operacao_atual"] = None
    _emit_status(f"operação registrada: {ativo} {resultado}")
    return op

_TIMEOUT_COMPRA = 30

def _api_call_com_timeout(fn, timeout, *args, **kwargs):
    """Executa uma chamada serializada sem abandonar threads em caso de espera.

    As primitivas da biblioteca têm seus próprios prazos. Manter esta camada
    síncrona evita o padrão anterior de criar uma thread por polling e deixá-la
    presa no lock da API quando o prazo externo expirava.
    """
    inicio = time.monotonic()
    resultado = _api_call(fn, *args, **kwargs)
    decorrido = time.monotonic() - inicio
    if decorrido > float(timeout):
        _log_scan(f"⚠️ Chamada {getattr(fn, '__name__', 'API')} excedeu {timeout}s ({decorrido:.1f}s).")
    return resultado

def _api_buy_com_timeout(fn, *args, **kwargs):
    """Envia uma única ordem sem criar thread que possa sobreviver ao timeout."""
    inicio = time.monotonic()
    try:
        resultado = _api_call(fn, *args, **kwargs)
    except Exception as exc:
        return False, str(exc)
    decorrido = time.monotonic() - inicio
    if decorrido > _TIMEOUT_COMPRA:
        _log_scan(f"⚠️ Corretora respondeu à ordem após {_TIMEOUT_COMPRA}s ({decorrido:.1f}s).")
        return False, "timeout aguardando resposta da corretora"
    return resultado

_api_lock = threading.RLock()
_API_LOCK_TIMEOUT = 15
_api_lock_estado = {"ultimo_reset": 0.0}

def _resetar_api_lock():
    global _api_lock
    agora = time.time()
    if agora - _api_lock_estado["ultimo_reset"] < 15:
        return
    _api_lock = threading.RLock()
    _api_lock_estado["ultimo_reset"] = agora
    _emit_status("lock da API resetado")

def _api_call(fn, *args, **kwargs):
    lock_ref = _api_lock
    if not lock_ref.acquire(timeout=_API_LOCK_TIMEOUT):
        raise TimeoutError(f"Lock da API ocupado por mais de {_API_LOCK_TIMEOUT}s")
    try:
        return fn(*args, **kwargs)
    finally:
        lock_ref.release()

def _api_call_if_available(fn, *args, **kwargs):
    """Executa apenas se a API estiver livre; usado por tarefas de painel."""
    lock_ref = _api_lock
    if not lock_ref.acquire(blocking=False):
        return None, False
    try:
        return fn(*args, **kwargs), True
    finally:
        lock_ref.release()

def _comprar(api, ativo, direcao, valor, expiracao_min, modalidade):
    """Abre uma opção Binary ou Turbo sem escolha implícita pela duração."""
    try:
        dir_api = str(direcao or "").lower().strip()
        if dir_api not in ("call", "put"):
            return False, f"Direção inválida: {dir_api}", modalidade
        mod = _normalizar_modalidade(modalidade)
        if mod == "ambas":
            return False, "A ordem precisa de uma modalidade concreta", mod
        if not _modalidade_disponivel_para_tf(ativo, mod, expiracao_min):
            return False, f"Modalidade {mod} indisponível ou incompatível com M{expiracao_min} para {ativo}", mod
        try:
            server_timestamp = float(api.get_server_timestamp())
        except Exception:
            try:
                server_timestamp = float(api.api.timesync.server_timestamp)
            except Exception:
                server_timestamp = time.time()
        expiracao_epoch, _ = get_expiration_time(server_timestamp, int(expiracao_min))
        _log_scan(
            f"  📤 [COMPRA] Enviando: {ativo} {dir_api.upper()} R${valor} "
            f"{mod.upper()} M{expiracao_min} (expira {expiracao_epoch})"
        )
        active_id = _resolver_active_id(ativo, mod)
        if active_id is None:
            return False, f"active_id não encontrado para {ativo} ({mod})", mod
        check, order_id = _api_buy_com_timeout(
            api.buy_by_raw_expirations,
            float(valor), active_id, dir_api, mod, int(expiracao_epoch),
        )
        if check and order_id:
            _log_scan(f"  ✅ [COMPRA] Ordem aceita! ID: {order_id} | {mod.upper()}")
            return True, order_id, mod
        motivo = str(order_id) if order_id else "Sem confirmação da corretora"
        _log_scan(f"  ❌ [COMPRA] Ordem rejeitada: {motivo} | Modalidade: {mod.upper()}")
        return False, motivo, mod
    except Exception as e:
        _log_scan(f"  ⚠️ [COMPRA] Exceção ao enviar [{ativo}]: {e}")
        return False, str(e), _normalizar_modalidade(modalidade)

def _falha_de_comunicacao(motivo):
    texto = str(motivo or "").lower()
    marcadores = (
        "timeout", "timed out", "não respondeu", "nao respondeu",
        "sem confirmação", "sem confirmacao", "conex", "connection",
        "socket", "websocket", "network", "rede", "temporar",
    )
    return any(marcador in texto for marcador in marcadores)

def _normalizar_lucro_resultado(resultado):
    """Converte números, (status, lucro) e tuplas aninhadas em lucro float."""
    if resultado is None:
        return None
    if isinstance(resultado, dict):
        for chave in ("lucro", "profit", "win_amount", "amount", "sum", "value"):
            if chave in resultado:
                convertido = _normalizar_lucro_resultado(resultado[chave])
                if convertido is not None:
                    return convertido
        return None
    if isinstance(resultado, (tuple, list)):
        candidatos = [resultado[1]] if len(resultado) == 2 and isinstance(resultado[0], str) else list(reversed(resultado))
        for candidato in candidatos:
            convertido = _normalizar_lucro_resultado(candidato)
            if convertido is not None:
                return convertido
        return None
    try:
        return float(resultado)
    except (TypeError, ValueError):
        return None


def _aguardar_resultado(api, order_id, expiracao_min, modalidade):
    # Binary e Turbo usam o mesmo acompanhamento de fechamento na biblioteca.
    modalidade = _normalizar_modalidade(modalidade)
    if modalidade == "ambas":
        modalidade = "turbo"
    tempo_limite = time.time() + (expiracao_min * 60) + 45
    _log_scan(f"  ⏳ [RESULTADO] Aguardando resultado da ordem {order_id} ({modalidade.upper()})...")
    while time.time() < tempo_limite:
        try:
            restante = max(5, min(20, int(tempo_limite - time.time())))
            retorno = api.check_win_v3(order_id, timeout=restante)
            lucro = _normalizar_lucro_resultado(retorno)
            if lucro is not None:
                _log_scan(f"  ✅ [RESULTADO] Ordem {order_id}: lucro R${lucro:.2f}")
                return lucro
        except Exception as e:
            _log_scan(f"⚠️ Erro ao checar resultado de {order_id} ({modalidade}): {e}")
        time.sleep(1)
    _log_scan(f"🛑 Timeout total atingido ao aguardar resultado da ordem {order_id}")
    return None

def _atraso_martingale_segundos():
    """Retorna o atraso configurado, preservando zero e limitando-o a 29s."""
    bruto = STATE.get("atraso_martingale_segundos", 0)
    if bruto is None or bruto == "":
        bruto = 0
    try:
        return max(0, min(int(bruto), 29))
    except (TypeError, ValueError):
        return 0


def _agendar_gale_proximo_sinal(ativo, camada, direcao, tf_seg, vela_entrada=None):
    """Mantém o Gale pendente até o próximo sinal válido.

    Neste modo não existe uma janela de expiração por ativo ou por vela: o
    scanner pode mudar de ativo e atravessar vários candles, mas o mesmo nível
    continua pendente até ser consumido por uma única entrada válida. Isso
    evita perder o Martingale ou executá-lo no mesmo candle do LOSS.
    """
    atraso = _atraso_martingale_segundos()
    tf = max(1, int(tf_seg or 60))
    agora = time.time()
    inicio_entrada = _horario_do_sinal(tf, vela_entrada if vela_entrada is not None else agora)
    pendente_atual = STATE.get("gale_pendente") or {}
    if pendente_atual:
        _log_scan(f"⏭ Gale já pendente para {pendente_atual.get('origem_ativo', ativo)}; novo agendamento ignorado.")
        return False
    STATE["gale_pendente"] = {
        "camada": int(camada),
        "direcao_origem": str(direcao or "").lower(),
        "tf_seg": tf,
        "origem_ativo": ativo,
        "vela_entrada": inicio_entrada,
        "liberar_em": agora + atraso,
        "criado_em": agora,
        "modo": "proximo_sinal",
        "proxima_entrada_autorizada": "proximo_sinal",
    }
    gerenciador_martingale.proxima_entrada_autorizada = "proximo_sinal"
    _log_scan(
        f"⏳ [MARTINGALE] Gale {camada} aguardando o próximo sinal válido "
        f"(origem {ativo}; atraso de {atraso}s)."
    )
    _emit_status(f"Gale {camada} aguardando próximo sinal")
    return True


def _estado_gale_pendente(pendente, tf_sinal, instante=None):
    """Retorna o estado temporal do Gale pendente.

    ``proximo_sinal`` nunca expira por mudança de ativo, vela ou timeframe;
    somente o primeiro sinal válido depois do atraso o consome.
    """
    if not pendente:
        return "sem_pendente"
    agora = time.time() if instante is None else float(instante)
    liberar_em = float(pendente.get("liberar_em", 0) or 0)
    if pendente.get("modo") == "proximo_sinal" or "expira_em" not in pendente:
        return "aguardando" if agora < liberar_em else "disponivel"
    # Compatibilidade com pendências antigas criadas pela versão anterior.
    tf_pendente = max(1, int(pendente.get("tf_seg", tf_sinal or 60) or 60))
    vela_alvo = int(pendente.get("vela_alvo", 0) or 0)
    expira_em = float(pendente.get("expira_em", 0) or 0)
    if not vela_alvo:
        vela_entrada = int(pendente.get("vela_entrada", 0) or 0)
        vela_alvo = vela_entrada + tf_pendente if vela_entrada else _horario_do_sinal(tf_pendente, agora) + tf_pendente
        expira_em = vela_alvo + tf_pendente
    vela_atual = _horario_do_sinal(tf_pendente, agora)
    if agora < liberar_em or vela_atual < vela_alvo:
        return "aguardando"
    if agora >= expira_em or vela_atual > vela_alvo:
        return "expirado"
    return "disponivel"


def _resolver_resultado_tardio(op_ref, ativo, order_id, modalidade, camada_gale):
    api = STATE["api"]
    # Turbo usa o mesmo endpoint de resultado das opções binárias na biblioteca.
    mod = "binary"
    tempo_limite = time.time() + 600
    while time.time() < tempo_limite and api:
        try:
            retorno = api.check_win_v3(order_id, timeout=20)
            resultado_lucro = _normalizar_lucro_resultado(retorno)
        except Exception:
            resultado_lucro = None
        if resultado_lucro is not None:
            resultado = "win" if resultado_lucro > 0 else ("loss" if resultado_lucro < 0 else "empate")
            _log_scan(f"🔁 Resultado tardio recuperado para {ativo}: {resultado.upper()} R${resultado_lucro:.2f}")
            op_ref["resultado"] = resultado
            op_ref["lucro"] = round(resultado_lucro, 2)
            STATE["saldo_acumulado"] += resultado_lucro
            if resultado_lucro > 0:
                STATE["wins"] += 1
                STATE["lucro_bruto"] += resultado_lucro
            elif resultado_lucro < 0:
                STATE["losses"] += 1
                STATE["prejuizo_bruto"] += resultado_lucro
            else:
                STATE["empates"] += 1
            _emit_status(f"resultado tardio: {ativo} {resultado}")
            valor_perdido = float(op_ref.get("valor") or STATE["valor_entrada"])
            nivel_soros_executado = int(op_ref.get("soros_nivel") or 0)
            if resultado == "win":
                gerenciador_soros.registrar_resultado(True, resultado_lucro, order_id, nivel_soros_executado)
            elif resultado == "loss":
                gerenciador_soros.registrar_resultado(False, resultado_lucro, order_id, nivel_soros_executado)
            resultado_martingale = gerenciador_martingale.registrar_resultado(
                resultado == "win", resultado_lucro, order_id, valor_perdido, ativo,
                str(op_ref.get("direcao", "")).lower(), int(op_ref.get("tf_seg") or 60), op_ref.get("vela_entrada")
            )
            STATE["martingale_state"] = gerenciador_martingale.get_status()
            if resultado == "win":
                STATE.get("valor_gale_base", {}).pop(ativo, None)
            if resultado == "loss":
                usar_gale = bool(STATE.get("usar_gale", False))
                niveis_gale = int(STATE.get("niveis_gale", 0) or 0)
                STATE.setdefault("valor_gale_base", {})[ativo] = valor_perdido
                if usar_gale and camada_gale < niveis_gale and not stop_atingido() and STATE.get("running"):
                    prox_camada = camada_gale + 1
                    direcao = str(op_ref.get("direcao", "")).lower()
                    tf_seg = int(op_ref.get("tf_seg") or 60)
                    if STATE.get("martingale_modo") == "proximo_sinal":
                        _agendar_gale_proximo_sinal(ativo, prox_camada, direcao, tf_seg, vela_entrada=op_ref.get("vela_entrada"))
                    else:
                        prox_valor = gerenciador_martingale.valor_atual
                        STATE["gale_atual"][ativo] = prox_camada
                        STATE["direcao_gale"][ativo] = direcao
                        STATE["tf_gale"][ativo] = tf_seg
                        _log_scan(
                            f"🔄 [MARTINGALE] Resultado tardio confirmou LOSS; iniciando Gale "
                            f"{prox_camada}/{niveis_gale} para {ativo} | Valor: R${prox_valor:.2f}"
                        )
                        with _lock_ativos:
                            _adicionar_em_op(ativo, "Gale após resultado tardio")
                        _emit_status(f"gale tardio {prox_camada} iniciado: {ativo}")
                        operar(ativo, _profundidade=prox_camada, direcao_forçada=direcao, tf_forçado=tf_seg)
                elif usar_gale and camada_gale < niveis_gale:
                    _log_scan("🔄 [MARTINGALE] Gale tardio não iniciado: bot parado, stop atingido ou limite indisponível.")
            return
    op_ref["resultado"] = "sem_confirmacao"
    _log_scan(f"🔁 Resultado tardio de {ativo} não recuperado — corretora nunca confirmou.")
    _emit_status(f"resultado tardio esgotado: {ativo}")

def operar(ativo, _profundidade=0, direcao_forçada=None, tf_forçado=None, score_forçado=None, manual=False, chave_sinal=None, estado_ia_forcado=None, fatores_ia_forcado=None, modalidade_forçada=None):
    ativo = _definir_ativo_em_foco(ativo) or ativo
    api = STATE["api"]
    mercado_ativo = _identificar_mercado_ativo(ativo)
    # --- BLOQUEIO POR NOTÍCIAS ---
    bloqueado, titulo_noticia = (False, "")
    if STATE.get("noticias_ativas", True) and STATE.get("bloquear_por_noticias", True):
        bloqueado, titulo_noticia = gerenciador_noticias.verificar_bloqueio(
            ativo,
            tempo_antes=int(STATE.get("tempo_antes_noticia", 5)),
            tempo_depois=int(STATE.get("tempo_depois_noticia", 5)),
        )
    if bloqueado:
        _log_scan(f"⚠️ OPERAÇÃO BLOQUEADA: Notícia de Alto Impacto ({titulo_noticia}) para {ativo[:3]}")
        with _lock_ativos:
            _remover_em_op(ativo, f"bloqueio notícia: {titulo_noticia}")
            if not manual:
                _remover_do_ciclo(ativo, "bloqueio notícia")
        return
    # -----------------------------

    
    if not api:
        _log_scan(f"❌ [ETAPA 1] API não conectada para {ativo}")
        with _lock_ativos:
            _remover_em_op(ativo, "API não conectada")
        return
    
    if not manual and not STATE["running"]:
        _log_scan(f"❌ [ETAPA 2] Bot não está em execução para {ativo}")
        with _lock_ativos:
            _remover_em_op(ativo, "bot parado")
        return
    
    if not manual:
        _verificar_reset_diario()
        if not verificar_horario(ativo):
            _, motivo_ttz = _ttz_check_entry(ativo)
            motivo = motivo_ttz if STATE.get("ttz_ativo") else "fora do horário"
            _log_scan(f"❌ [ETAPA 2] Entrada bloqueada para {ativo}: {motivo}")
            with _lock_ativos:
                _remover_em_op(ativo, motivo)
            return
        if encerrar_por_stop():
            _log_scan(f"❌ [ETAPA 2] Stop atingido para {ativo}")
            with _lock_ativos:
                _remover_em_op(ativo, "stop atingido")
            return
        if STATE["total_operacoes"] >= STATE["limite_diario"]:
            _log_scan(f"❌ [ETAPA 2] Limite diário atingido para {ativo}")
            with _lock_ativos:
                _remover_em_op(ativo, "limite diário atingido")
            return
    
    niveis_gale = STATE["niveis_gale"]
    usar_gale   = STATE["usar_gale"]
    fator_gale  = STATE["fator_gale"]
    modalidade_preferida = _normalizar_modalidade(
        modalidade_forçada if modalidade_forçada is not None else STATE.get("modalidade", "ambas")
    )
    camada_gale = int(_profundidade or 0)

    # A pausa por losses bloqueia qualquer nova entrada de nível base. A
    # checagem precisa existir aqui, além do scanner e da rota manual, porque
    # entre a reserva do sinal e o envio da ordem a pausa pode ser ativada por
    # outra operação concluída. Gales já autorizados não são interrompidos.
    if camada_gale <= 0:
        restante_pausa = _pausa_losses_restante_seg()
        if restante_pausa > 0:
            _log_scan(
                f"⏭ [PAUSA LOSSES] Entrada bloqueada para {ativo}: "
                f"{restante_pausa / 60:.1f} min restantes."
            )
            if chave_sinal:
                _liberar_sinal(chave_sinal)
            with _lock_ativos:
                _remover_em_op(ativo, "pausa por losses seguidos")
            return
    
    if camada_gale > niveis_gale:
        _log_scan(f"🔄 [MARTINGALE] Limite de Gale atingido ({camada_gale}/{niveis_gale}) para {ativo} — encerrando ciclo.")
        STATE["gale_atual"].pop(ativo, None)
        STATE["direcao_gale"].pop(ativo, None)
        STATE["tf_gale"].pop(ativo, None)
        with _lock_ativos:
            _remover_em_op(ativo, "gale esgotado")
        return
    
    estado_ia_op = None
    fatores_ia_op = None
    
    if camada_gale == 0:
        if direcao_forçada:
            # O scanner ou a interface manual já confirmou a direção.
            # Entrada manual não deve ser reanalisada e cancelada por uma
            # direção diferente encontrada em uma nova leitura.
            direcao_analisada = str(direcao_forçada).lower().strip()
            if direcao_analisada not in ("call", "put"):
                direcao_analisada = None
            tf_seg_analisado = int(tf_forçado or _timeframe_configurado()[0])
            tf_label = _tf_label_de_segundos(tf_seg_analisado)
            score_analisado = score_forçado if score_forçado is not None else 0.0
            estado_ia_analisado = estado_ia_forcado
            fatores_ia_analisados = fatores_ia_forcado or {}
            _log_scan(
                f"✅ [SINAL CONFIRMADO] {ativo}: usando direção já confirmada pelo scanner "
                f"({direcao_analisada or 'nenhuma'} / {tf_label}); sem nova busca."
            )
        else:
            direcao_analisada, tf_label, tf_seg_analisado, score_analisado, estado_ia_analisado, fatores_ia_analisados = analisar_confluencia(
                ativo,
                respeitar_janela_busca=not manual,
            )
        if direcao_forçada:
            direcao_solicitada = str(direcao_forçada).lower().strip()
            if direcao_analisada != direcao_solicitada:
                _log_scan(
                    f"⏭ Entrada manual cancelada: confluência confirmou "
                    f"{(direcao_analisada or 'nenhuma').upper()}, mas foi solicitada {direcao_solicitada.upper()}."
                )
                direcao = None
            else:
                direcao = direcao_analisada
        else:
            direcao = direcao_analisada
        tf_seg = tf_forçado or tf_seg_analisado
        score = score_forçado if direcao_forçada and direcao else score_analisado
        estado_ia_op = estado_ia_forcado if direcao_forçada and direcao else estado_ia_analisado
        fatores_ia_op = fatores_ia_forcado if direcao_forçada and direcao else fatores_ia_analisados
        
        if not direcao:
            _liberar_sinal(chave_sinal)
            with _lock_ativos:
                _remover_em_op(ativo, "sem confluência — cancelado")
            return
        
        if chave_sinal is None:
            chave_sinal = _chave_do_sinal(ativo, direcao, tf_seg)
        if not _sinal_ja_reservado(chave_sinal):
            if not _reservar_sinal(chave_sinal, "manual" if manual else "operar"):
                _log_scan(f"⏭ Sinal duplicado ignorado: {ativo} {direcao.upper()} {_tf_label_de_segundos(tf_seg)}.")
                with _lock_ativos:
                    _remover_em_op(ativo, "sinal duplicado")
                    _remover_do_ciclo(ativo, "sinal duplicado")
                return
        
        if not _ativo_binario_turbo_existe(ativo):
            _log_scan(f"🚫 [ETAPA 3] Ativo {ativo} não existe no catálogo Binary/Turbo.")
            with _lock_ativos:
                _remover_em_op(ativo, "ativo inexistente")
                _remover_do_ciclo(ativo, "ativo inexistente")
            return
        
        STATE["direcao_gale"][ativo] = direcao
        STATE["tf_gale"][ativo]      = tf_seg
        # Sem Gale pendente, o Soros calcula a entrada base. Os dois estados
        # permanecem independentes; a prioridade de valor só é Martingale
        # quando existe uma recuperação autorizada após LOSS.
        valor = gerenciador_soros.calcular_valor_entrada(STATE["valor_entrada"])
        valor = round(float(valor), 2)
    else:
        direcao = STATE["direcao_gale"].get(ativo)
        tf_seg  = STATE["tf_gale"].get(ativo, 60)
        if not direcao:
            _log_scan(f"⚠️ [MARTINGALE] Gale {camada_gale} sem direção para {ativo} — cancelado.")
            STATE["gale_atual"].pop(ativo, None)
            with _lock_ativos:
                _remover_em_op(ativo, "gale sem direção — cancelado")
            return
        if not _ativo_binario_turbo_existe(ativo):
            _log_scan(f"⏭ [MARTINGALE] Gale {camada_gale} cancelado: {ativo} não existe mais no catálogo Binary/Turbo.")
            STATE["gale_atual"].pop(ativo, None)
            STATE["direcao_gale"].pop(ativo, None)
            STATE["tf_gale"].pop(ativo, None)
            with _lock_ativos:
                _remover_em_op(ativo, "gale cancelado — ativo inexistente")
            return
        # O Gale recupera o valor que REALMENTE perdeu na entrada anterior
        # (que pode já vir ajustada pelo Soros), não um valor fixo — por
        # isso multiplica pelo fator em cima do último valor perdido salvo
        # em STATE["valor_gale_base"], atualizado no momento de cada LOSS.
        base_perdida = STATE.get("valor_gale_base", {}).get(ativo, STATE["valor_entrada"])
        valor_autorizado = gerenciador_martingale.valor_atual if gerenciador_martingale.nivel_atual == camada_gale else None
        valor = round(float(valor_autorizado if valor_autorizado is not None else base_perdida * fator_gale), 2)
        if valor < 0.01:
            valor = 0.01
        if gerenciador_martingale.nivel_atual != camada_gale:
            _log_scan(f"⚠️ [MARTINGALE] Estado divergente antes da entrada: esperado nível {camada_gale}, estado {gerenciador_martingale.nivel_atual}.")
            with _lock_ativos:
                _remover_em_op(ativo, "estado Martingale divergente")
            return
        _log_scan(f"🔄 [MARTINGALE] Gale {camada_gale}/{niveis_gale} | Ativo: {ativo} | Valor: R${valor:.2f} (base perdida R${base_perdida:.2f}) | Direção: {direcao.upper()}")
    
    if manual:
        expiracao_min = max(1, STATE.get("expiracao", 1))
    else:
        expiracao_min = max(1, round((tf_seg or 60) / 60))

    # A referência temporal da entrada é preservada para que o modo
    # "próximo sinal" possa aceitar o Gale somente no candle seguinte.
    vela_entrada = _horario_do_sinal(tf_seg, time.time())
    mercado_ativo = _identificar_mercado_ativo(ativo)
    _log_scan(f"  🌐 [ETAPA 5] Mercado identificado: {mercado_ativo} | Ativo: {ativo}")
    
    modalidade, aberto = detectar_melhor_modalidade(
        ativo,
        modalidade_preferida if manual else None,
        expiracao_min,
    )
    _log_scan(f"  📊 [ETAPA 6] Modalidade escolhida: {modalidade.upper()} | Ativo: {ativo} | Aberto: {aberto}")
    
    if not aberto:
        prefixo = f"⏭ [MARTINGALE] Gale {camada_gale} cancelado" if camada_gale else "🚫 [ETAPA 4] Ordem cancelada"
        _log_scan(f"{prefixo}: {ativo} fechado em todas as modalidades para M{expiracao_min}.")
        _liberar_sinal(chave_sinal)
        STATE["gale_atual"].pop(ativo, None)
        STATE["direcao_gale"].pop(ativo, None)
        STATE["tf_gale"].pop(ativo, None)
        with _lock_ativos:
            _remover_em_op(ativo, "modalidade indisponível")
            if camada_gale == 0:
                _remover_do_ciclo(ativo, "modalidade indisponível")
        return
    
    _log_scan(
        f"🚀 [ETAPA 9] SINAL GERADO: {ativo} | {direcao.upper()} | "
        f"Mercado: {mercado_ativo} | Modalidade: {modalidade.upper()} | "
        f"TF: {_tf_label_de_segundos(tf_seg)} | Valor: R${valor} | Expiração: M{expiracao_min}"
        + (f" | Gale: {camada_gale}/{niveis_gale}" if camada_gale > 0 else "")
    )
    
    with _lock_ativos:
        _adicionar_em_op(ativo, "entrada")
    
    _gale_disparado = False
    _motivo_saida = "finalizado"

    # A pausa temporal bloqueia somente a abertura de um novo ciclo (Gale 0).
    # Operações já aceitas e a lógica de Gale/Martingale seguem inalteradas.
    # Esta segunda verificação fica imediatamente antes da compra para evitar
    # que um sinal analisado antes da virada dos 30s ainda gere uma ordem.
    if camada_gale == 0:
        janela_candle = _estado_janela_candle(tf_seg)
        if janela_candle["pausar_novas_entradas"]:
            restante = janela_candle["tempo_restante"]
            _log_scan(
                f"⏸️ [PAUSA TIMEFRAME] Nova entrada bloqueada para {ativo}: "
                f"{janela_candle['timeframe']} com {restante:.1f}s restantes. "
                "Ciclo e scanner continuam ativos."
            )
            STATE["gale_atual"].pop(ativo, None)
            STATE["direcao_gale"].pop(ativo, None)
            STATE["tf_gale"].pop(ativo, None)
            _liberar_sinal(chave_sinal)
            with _lock_ativos:
                _remover_em_op(ativo, "pausa dos últimos 30s do candle")
            return

    # Barreira final contra corrida: confirmar novamente o sentimento antes de
    # enviar qualquer entrada, inclusive uma entrada de Gale. Isso evita que
    # uma mudança de sentimento durante a análise transforme um sinal válido em
    # uma ordem desalinhada.
    # Barreira final contra corrida: o resultado de outra operação pode ter
    # atingido um stop enquanto esta entrada era analisada. Nunca enviar uma
    # nova ordem depois que o limite da sessão foi alcançado.
    if stop_atingido():
        _log_scan(
            f"🛑 [STOP] Entrada cancelada antes do envio: {ativo} | "
            f"Sessão R${STATE['saldo_acumulado']:+.2f}"
        )
        STATE["gale_atual"].pop(ativo, None)
        STATE["direcao_gale"].pop(ativo, None)
        STATE["tf_gale"].pop(ativo, None)
        _liberar_sinal(chave_sinal)
        with _lock_ativos:
            _remover_em_op(ativo, "stop atingido antes do envio")
        return
    
    try:
        _log_scan(f"💸 [ETAPA 10] ENVIANDO ORDEM: {ativo} {direcao.upper()} R${valor} ({modalidade.upper()} / M{expiracao_min})")
        
        # Uma única tentativa por sinal. Reenviar após timeout pode duplicar a
        # ordem se a corretora tiver aceitado a primeira solicitação.
        mod_usado = _normalizar_modalidade(modalidade)
        check, order_id, mod_usado = _comprar(api, ativo, direcao, valor, expiracao_min, mod_usado)
        if not check:
            _log_scan(f"  ❌ [ETAPA 10] {mod_usado.upper()} falhou sem reenvio: {order_id}")
        
        if not check or not order_id:
            motivo = str(order_id or "Ativo fechado ou ordem rejeitada")
            _log_scan(f"❌ [ETAPA 11] ORDEM REJEITADA: {ativo} | Motivo: {motivo} | Mercado: {mercado_ativo}")
            registrar_op(ativo, direcao, valor, "erro", 0, camada_gale, tf_seg=tf_seg, modalidade=modalidade, mercado=mercado_ativo, vela_entrada=vela_entrada)
            _liberar_sinal(chave_sinal)
            STATE["gale_atual"].pop(ativo, None)
            STATE["direcao_gale"].pop(ativo, None)
            STATE["tf_gale"].pop(ativo, None)
            _motivo_saida = f"rejeitado pela corretora — {motivo}"
            _gale_disparado = False
            with _lock_ativos:
                _remover_em_op(ativo, _motivo_saida)
            return
        
        _log_scan(f"✅ [ETAPA 11] ORDEM ACEITA: {ativo} | ID: {order_id} | Modalidade: {mod_usado.upper()} | Mercado: {mercado_ativo}")
        STATE["cooldown"][ativo]  = time.time()
        STATE["total_operacoes"] += 1
        entrada_em = time.time()
        STATE["operacao_atual"] = {
            "ativo": ativo,
            "direcao": direcao.upper(),
            "valor": round(valor, 2),
            "valor_enviado": round(valor, 2),
            "tf": _tf_label_de_segundos(tf_seg) if tf_seg else "-",
            "modalidade": mod_usado.upper(),
            "gale": camada_gale,
            "soros_nivel": gerenciador_soros.nivel_atual if STATE.get("usar_soros") else 0,
            "entrada_em": entrada_em,
            "expira_em": entrada_em + expiracao_min * 60,
            "vela_entrada": vela_entrada,
            "ordem_id": str(order_id),
        }
        gerenciador_martingale.registrar_entrada(order_id, valor, ativo, direcao, tf_seg, vela_entrada)
        STATE["martingale_state"] = gerenciador_martingale.get_status()
        _emit_status(f"operação em andamento: {ativo}")
        
        resultado_lucro = _aguardar_resultado(api, order_id, expiracao_min, mod_usado)
        
        try:
            _saldo_novo, _saldo_executado = _api_call_if_available(api.get_balance)
            if _saldo_executado and _saldo_novo is not None:
                STATE["saldo"] = _saldo_novo
        except Exception:
            pass
        
        if resultado_lucro is None:
            _log_scan(f"⚠️ Timeout: Resultado não recebido para {ativo}. Continuando em background...")
            _op_pendente = registrar_op(ativo, direcao, valor, "desconhecido", 0, camada_gale, tf_seg=tf_seg, modalidade=mod_usado, mercado=mercado_ativo, vela_entrada=vela_entrada, ordem_id=order_id, soros_nivel=gerenciador_soros.nivel_atual if STATE.get("usar_soros") else 0, soros_pct=gerenciador_soros.reinvestimento if STATE.get("usar_soros") else None)
            threading.Thread(
                target=_resolver_resultado_tardio,
                args=(_op_pendente, ativo, order_id, mod_usado, camada_gale),
                daemon=True
            ).start()
            STATE["gale_atual"].pop(ativo, None)
            STATE["direcao_gale"].pop(ativo, None)
            STATE["tf_gale"].pop(ativo, None)
            _motivo_saida = "timeout de resultado"
            _gale_disparado = False
            with _lock_ativos:
                _remover_em_op(ativo, _motivo_saida)
            return
        
        STATE["saldo_acumulado"] += resultado_lucro
        ganhou = resultado_lucro > 0
        is_loss_confirmado = resultado_lucro < 0
        nivel_soros_executado = gerenciador_soros.nivel_atual if STATE.get("usar_soros") else 0
        # Primeiro confirma o resultado nos dois estados, usando o ID real da
        # ordem. Os conjuntos internos impedem que um mesmo WIN/LOSS avance ou
        # resete duas vezes caso a corretora devolva o evento novamente.
        if ganhou:
            gerenciador_soros.registrar_resultado(True, resultado_lucro, order_id, nivel_soros_executado)
        elif is_loss_confirmado:
            gerenciador_soros.registrar_resultado(False, resultado_lucro, order_id, nivel_soros_executado)
        resultado_martingale = gerenciador_martingale.registrar_resultado(
            ganhou, resultado_lucro, order_id, valor, ativo, direcao, tf_seg, vela_entrada
        )
        STATE["martingale_state"] = gerenciador_martingale.get_status()
        if estado_ia_op:
            ia_registrar(estado_ia_op, ganhou)
            if fatores_ia_op:
                _atualizar_pesos_ia(estado_ia_op, ganhou, fatores_ia_op)
        
        if ganhou:
            _log_scan(
                f"✅ [ETAPA 12] WIN: {ativo} | Lucro: R${resultado_lucro:.2f} | "
                f"Mercado: {mercado_ativo} | Modalidade: {mod_usado.upper()}"
                + (f" | Gale: {camada_gale}" if camada_gale > 0 else "")
            )
            STATE["wins"] += 1
            STATE["lucro_bruto"] += resultado_lucro
            # Qualquer WIN encerra a contagem de losses seguidos, inclusive
            # a recuperação no Gale — o ciclo terminou positivo.
            STATE["losses_seguidos_atual"] = 0
            registrar_op(ativo, direcao, valor, "win", resultado_lucro, camada_gale, tf_seg=tf_seg, modalidade=mod_usado, mercado=mercado_ativo, vela_entrada=vela_entrada, ordem_id=order_id, soros_nivel=nivel_soros_executado, soros_pct=gerenciador_soros.reinvestimento if STATE.get("usar_soros") else None)
            # O Soros reage a qualquer WIN, inclusive WIN de Gale; o estado
            # Martingale já foi resetado pela confirmação acima.
            STATE["gale_atual"].pop(ativo, None)
            STATE["direcao_gale"].pop(ativo, None)
            STATE["tf_gale"].pop(ativo, None)
            STATE.get("valor_gale_base", {}).pop(ativo, None)
            _motivo_saida = "operação finalizada — WIN"
            _gale_disparado = False
            if camada_gale > 0:
                _log_scan(f"🎉 [MARTINGALE] Recuperação no Gale {camada_gale} — ciclo encerrado com WIN.")
            with _lock_ativos:
                _remover_em_op(ativo, _motivo_saida)
        else:
            is_loss = resultado_lucro < 0
            is_empate = resultado_lucro == 0
            pausa_losses_ativada = False
            if is_loss:
                _log_scan(
                    f"❌ [ETAPA 12] LOSS: {ativo} | Prejuízo: R${resultado_lucro:.2f} | "
                    f"Mercado: {mercado_ativo} | Modalidade: {mod_usado.upper()}"
                    + (f" | Gale: {camada_gale}/{niveis_gale}" if camada_gale > 0 else "")
                )
                STATE["losses"] += 1
                STATE["prejuizo_bruto"] += resultado_lucro
                registrar_op(ativo, direcao, valor, "loss", resultado_lucro, camada_gale, tf_seg=tf_seg, modalidade=mod_usado, mercado=mercado_ativo, vela_entrada=vela_entrada, ordem_id=order_id, soros_nivel=nivel_soros_executado, soros_pct=gerenciador_soros.reinvestimento if STATE.get("usar_soros") else None)
                # Guarda o valor REAL que acabou de perder — é a base que o
                # próximo nível de Gale vai multiplicar pelo fator, para
                # recuperar o prejuízo de verdade (inclusive quando esta
                # entrada já vinha ajustada pelo Soros).
                STATE.setdefault("valor_gale_base", {})[ativo] = valor
                # A pausa tem prioridade sobre o Martingale. O contador é
                # atualizado neste momento, antes de decidir se haverá Gale.
                pausa_losses_ativada = _registrar_loss_seguido()
                if pausa_losses_ativada:
                    gerenciador_martingale.resetar()
                    STATE["martingale_state"] = gerenciador_martingale.get_status()
            else:
                _log_scan(f"⚪ [ETAPA 12] EMPATE: {ativo} | Mercado: {mercado_ativo} | Modalidade: {mod_usado.upper()}")
                STATE["empates"] += 1
                registrar_op(ativo, direcao, valor, "empate", 0, camada_gale, tf_seg=tf_seg, modalidade=mod_usado, mercado=mercado_ativo, vela_entrada=vela_entrada, ordem_id=order_id, soros_nivel=nivel_soros_executado, soros_pct=gerenciador_soros.reinvestimento if STATE.get("usar_soros") else None)
            
            deve_fazer_gale = is_loss or (is_empate and mod_usado == 'digital')
            
            resultado_ja_processado = bool(resultado_martingale.get("duplicado"))
            acao_martingale = resultado_martingale.get("acao")
            if (deve_fazer_gale and usar_gale and not pausa_losses_ativada and
                    not resultado_ja_processado and
                    acao_martingale in ("proxima_vela", "aguardar_sinal") and not stop_atingido()):
                prox_camada = int(resultado_martingale.get("nivel") or (camada_gale + 1))
                modo_gale = STATE.get("martingale_modo", "proxima_vela")
                if modo_gale == "proximo_sinal":
                    agendado = _agendar_gale_proximo_sinal(ativo, prox_camada, direcao, tf_seg, vela_entrada=vela_entrada)
                    _gale_disparado = bool(agendado)
                    _motivo_saida = "Gale aguardando próximo sinal confirmado" if agendado else "Gale já pendente"
                    STATE["gale_atual"].pop(ativo, None)
                    STATE["direcao_gale"].pop(ativo, None)
                    STATE["tf_gale"].pop(ativo, None)
                    with _lock_ativos:
                        _remover_em_op(ativo, _motivo_saida)
                else:
                    # Próxima vela significa a primeira vela posterior à vela
                    # que originou o LOSS, nunca uma entrada no mesmo candle.
                    inicio_vela = _horario_do_sinal(tf_seg, vela_entrada)
                    liberar_em = inicio_vela + max(1, int(tf_seg or 60))
                    atraso = _atraso_martingale_segundos()
                    liberar_em = max(liberar_em, time.time() + atraso)
                    espera = max(0.0, liberar_em - time.time())
                    if espera > 0:
                        _log_scan(f"⏳ [MARTINGALE] Aguardando {espera:.1f}s até a próxima vela para o Gale {prox_camada}.")
                        time.sleep(espera)
                    if stop_atingido() or (not manual and not STATE.get("running", True)):
                        _log_scan("⏭ [MARTINGALE] Gale cancelado durante a espera: stop atingido ou bot parado.")
                        _gale_disparado = False
                        _motivo_saida = "Gale cancelado durante espera"
                        with _lock_ativos:
                            _remover_em_op(ativo, _motivo_saida)
                    else:
                        STATE["gale_atual"][ativo] = prox_camada
                        STATE["direcao_gale"][ativo] = direcao
                        STATE["tf_gale"][ativo] = tf_seg
                        _log_scan(
                            f"🔄 [MARTINGALE] Iniciando Gale {prox_camada}/{niveis_gale} para {ativo} | "
                            f"Valor: R${gerenciador_martingale.valor_atual:.2f} | Direção: {direcao.upper()} | TF: {_tf_label_de_segundos(tf_seg)}"
                        )
                        _emit_status(f"gale {prox_camada} iniciado: {ativo}")
                        operar(ativo, _profundidade=prox_camada, manual=manual, direcao_forçada=direcao, tf_forçado=tf_seg)
                        _gale_disparado = True
            else:
                if deve_fazer_gale and pausa_losses_ativada:
                    _log_scan(f"⏸️ [MARTINGALE] Gale cancelado: limite de losses seguidos atingido.")
                elif deve_fazer_gale and camada_gale >= niveis_gale:
                    _log_scan(f"🔄 [MARTINGALE] Gale {camada_gale}/{niveis_gale} esgotado para {ativo} — encerrando ciclo.")
                elif deve_fazer_gale and stop_atingido():
                    _log_scan(f"🔄 [MARTINGALE] Gale cancelado — Stop atingido.")
                # O loss já foi contado imediatamente acima, antes da decisão
                # sobre o Gale, para que o limite 1 funcione de fato.
                STATE["gale_atual"].pop(ativo, None)
                STATE["direcao_gale"].pop(ativo, None)
                STATE["tf_gale"].pop(ativo, None)
                _gale_disparado = False
                if stop_atingido():
                    _motivo_saida = "finalizado — stop atingido"
                else:
                    _motivo_saida = "finalizado — fim do ciclo"
                with _lock_ativos:
                    _remover_em_op(ativo, _motivo_saida)
    except Exception as e:
        _log_scan(f"⚠️ Erro inesperado em operar({ativo}): {e}")
        STATE["gale_atual"].pop(ativo, None)
        STATE["direcao_gale"].pop(ativo, None)
        STATE["tf_gale"].pop(ativo, None)
        _gale_disparado = False
        _motivo_saida = f"erro inesperado — {e}"
        with _lock_ativos:
            _remover_em_op(ativo, _motivo_saida)

_ativos_em_op: set = set()
_ativos_em_op_ts: dict = {}
_lock_ativos   = threading.RLock()
_sinais_reservados: dict = {}
_lock_sinais = threading.RLock()
_TTL_SINAL_RESERVADO = 60 * 60

def _horario_do_sinal(tf_seg, instante=None):
    try:
        tf = max(1, int(tf_seg))
    except (TypeError, ValueError):
        tf = 60
    ts = int(time.time() if instante is None else instante)
    return ts - (ts % tf)

def _chave_do_sinal(ativo, direcao, tf_seg, horario_sinal=None):
    direcao_norm = str(direcao or "").lower().strip()
    return (str(ativo).upper().strip(), direcao_norm, int(tf_seg or 60), _horario_do_sinal(tf_seg, horario_sinal))

def _limpar_sinais_expirados(agora=None):
    referencia = time.time() if agora is None else agora
    expirados = [
        chave for chave, dados in _sinais_reservados.items()
        if referencia - dados.get("criado_em", referencia) > _TTL_SINAL_RESERVADO
    ]
    for chave in expirados:
        _sinais_reservados.pop(chave, None)

def _reservar_sinal(chave, origem="scanner"):
    with _lock_sinais:
        _limpar_sinais_expirados()
        if chave in _sinais_reservados:
            return False
        _sinais_reservados[chave] = {"criado_em": time.time(), "origem": origem}
        return True

def _liberar_sinal(chave):
    if not chave:
        return
    with _lock_sinais:
        _sinais_reservados.pop(chave, None)

def _sinal_ja_reservado(chave):
    with _lock_sinais:
        return chave in _sinais_reservados

_ativos_em_op_motivo = {}

def _marcar_em_op(chave, motivo=None):
    _ativos_em_op.add(chave)
    _ativos_em_op_ts[chave] = time.time()
    if motivo:
        _ativos_em_op_motivo[chave] = str(motivo)

def _desmarcar_em_op(chave):
    _ativos_em_op.discard(chave)
    _ativos_em_op_ts.pop(chave, None)
    _ativos_em_op_motivo.pop(chave, None)

def _adicionar_em_op(chave, motivo="entrada"):
    era_novo = chave not in _ativos_em_op
    _marcar_em_op(chave, motivo)
    if era_novo:
        _log_scan(f"➕ Vaga preenchida: {chave} ({motivo})")
        _emit_status(f"vaga preenchida: {chave}")

def _remover_em_op(chave, motivo="finalizado"):
    existia = chave in _ativos_em_op
    _desmarcar_em_op(chave)
    if existia:
        _log_scan(f"➖ Vaga liberada: {chave} ({motivo})")
        _emit_status(f"vaga liberada: {chave}")

def _remover_do_ciclo(ativo, motivo):
    if ativo in STATE["ciclo_ativos"]:
        STATE["ciclo_ativos"].remove(ativo)
        _log_scan(f"➖ Removido da análise: {ativo} ({motivo})")
        _emit_status(f"removido da análise: {ativo}")


_ULTIMO_CANDLE_PAUSA_LOGADO = None


def _aguardar_fim_pausa_timeframe(session_id):
    """Suspende apenas a busca por novas entradas até o próximo candle.

    O scanner permanece no mesmo ciclo e conserva ``ciclo_ativos``. A espera é
    interrompível se o bot for parado ou se uma nova sessão for iniciada. Um
    Gale pendente não deve passar por esta espera, pois a lógica de Gale deve
    continuar sendo tratada pelo fluxo já existente.
    """
    global _ULTIMO_CANDLE_PAUSA_LOGADO

    tf_seg, tf_label = _timeframe_configurado()
    estado = _estado_janela_candle(tf_seg)
    if not estado["pausar_novas_entradas"]:
        return True

    candle_atual = estado["inicio_candle_epoch"]
    if _ULTIMO_CANDLE_PAUSA_LOGADO != candle_atual:
        _ULTIMO_CANDLE_PAUSA_LOGADO = candle_atual
        _log_scan(
            f"⏸️ [PAUSA TIMEFRAME] Scanner pausado para novas entradas em {tf_label}: "
            f"{estado['tempo_restante']:.1f}s restantes. "
            "Mantendo o ciclo e os ativos atuais."
        )

    while STATE.get("running") and STATE.get("session_id") == session_id:
        estado = _estado_janela_candle(tf_seg)
        if not estado["pausar_novas_entradas"]:
            _ULTIMO_CANDLE_PAUSA_LOGADO = None
            _log_scan(
                f"▶️ [PAUSA TIMEFRAME] Novo candle {tf_label} iniciado — "
                "novas entradas liberadas automaticamente."
            )
            return True
        time.sleep(min(1.0, max(0.1, float(estado["tempo_restante"]))))

    return False


_ULTIMO_LOG_PAUSA_LOSSES = None


def _pausa_losses_restante_seg():
    """Retorna os segundos restantes da pausa por losses, sem lançar exceção."""
    try:
        pausa_ate = float(STATE.get("pausa_losses_ate", 0.0) or 0.0)
    except (TypeError, ValueError):
        pausa_ate = 0.0
    return max(0.0, pausa_ate - time.time())


def _registrar_loss_seguido():
    """Registra um loss e ativa a pausa antes de qualquer novo Martingale.

    O limite representa losses confirmados consecutivos. Ao atingir o limite,
    a pausa tem prioridade sobre o Gale: nenhuma nova perna é iniciada.
    Retorna True quando a pausa foi ativada neste resultado.
    """
    try:
        limite = max(0, min(int(STATE.get("losses_seguidos_limite", 0) or 0), 20))
    except (TypeError, ValueError):
        limite = 0
    if limite <= 0:
        return False

    try:
        atual = max(0, int(STATE.get("losses_seguidos_atual", 0) or 0)) + 1
    except (TypeError, ValueError):
        atual = 1
    STATE["losses_seguidos_atual"] = atual
    if atual < limite:
        return False

    try:
        pausa_min = max(0.0, min(float(STATE.get("losses_seguidos_pausa_min", 30) or 0), 720.0))
    except (TypeError, ValueError):
        pausa_min = 30.0
    if pausa_min <= 0:
        # Duração zero equivale a pausa desativada; não bloqueia o Gale.
        STATE["losses_seguidos_atual"] = 0
        return False

    STATE["pausa_losses_ate"] = time.time() + pausa_min * 60
    _log_scan(
        f"🧊 [PAUSA LOSSES] {atual} losses seguidos atingido — "
        f"pausando novas entradas por {pausa_min:.0f} min; Martingale não será iniciado."
    )
    # A sequência terminou no limite; após o período de pausa, uma nova perda
    # deve iniciar uma nova sequência, e não disparar outra pausa imediatamente.
    STATE["losses_seguidos_atual"] = 0
    _emit_status("pausa por losses seguidos")
    return True


def _aguardar_fim_pausa_losses(session_id):
    """Suspende novas entradas depois de N losses seguidos (ciclo completo,
    já contando o Gale como uma perna do mesmo ciclo), pelo tempo configurado
    em ``losses_seguidos_pausa_min``. Não deve ser chamada para um Gale
    pendente — isso é responsabilidade do chamador, igual à pausa de
    timeframe (``_aguardar_fim_pausa_timeframe``).
    """
    global _ULTIMO_LOG_PAUSA_LOSSES

    pausa_ate = float(STATE.get("pausa_losses_ate", 0.0) or 0.0)
    agora = time.time()
    if agora >= pausa_ate:
        return True

    if _ULTIMO_LOG_PAUSA_LOSSES != pausa_ate:
        _ULTIMO_LOG_PAUSA_LOSSES = pausa_ate
        _log_scan(
            f"⏸️ [PAUSA LOSSES] Novas entradas pausadas por losses seguidos: "
            f"{(pausa_ate - agora) / 60:.1f} min restantes."
        )

    while STATE.get("running") and STATE.get("session_id") == session_id:
        agora = time.time()
        pausa_ate = float(STATE.get("pausa_losses_ate", 0.0) or 0.0)
        if agora >= pausa_ate:
            _ULTIMO_LOG_PAUSA_LOSSES = None
            _log_scan("▶️ [PAUSA LOSSES] Tempo de espera encerrado — novas entradas liberadas.")
            return True
        time.sleep(min(2.0, max(0.2, pausa_ate - agora)))

    return False


def loop_bot(session_id):
    api = STATE["api"]
    _log_scan("═══ SCANNER LUA QUADCODE INICIADO ═══")
    _log_scan("📋 Ativos: catálogo completo de instrumentos Binary e Turbo")
    _log_scan(f"📋 Modalidades operacionais: {_normalizar_modalidade(STATE.get('modalidade', 'ambas')).upper()}")
    _log_scan("📋 Fonte de sinais: script Lua Quadcode autorizado")
    _log_scan(f"📋 Timeframe de candles/expiração: {_tf_label_de_segundos(_timeframe_configurado()[0])}")
    gale_txt = f"Sim ({STATE['niveis_gale']}x × {STATE['fator_gale']})" if STATE["usar_gale"] else "Não"
    _log_scan(f"📋 Atraso após LOSS antes do Gale: {_atraso_martingale_segundos()}s")
    _log_scan(f"📋 Gale: {gale_txt} | Stop Win: R$ {STATE['stop_win']} | Stop Loss: R$ {STATE['stop_loss']}")
    _log_scan(f"📋 Valor base: R$ {STATE['valor_entrada']}")
    limite_losses_cfg = int(STATE.get("losses_seguidos_limite", 0) or 0)
    if limite_losses_cfg > 0:
        _log_scan(
            f"📋 Pausa por losses seguidos: {limite_losses_cfg} losses → "
            f"{STATE.get('losses_seguidos_pausa_min', 30)} min sem novas entradas"
        )
    else:
        _log_scan("📋 Pausa por losses seguidos: desativada")
    
    _estava_desconectado = False
    
    while STATE["running"]:
        try:
            if STATE.get("session_id") != session_id:
                break
            
            try:
                conectado = _api_call(api.check_connect)
            except Exception:
                conectado = False
            
            if not api or not conectado:
                _estava_desconectado = True
                _log_scan("🔌 Conexão com a IQ Option caiu. Tentando reconectar...")
                for tentativa_reconexao in range(3):
                    try:
                        _api_call(api.connect)
                        time.sleep(3)
                        if _api_call(api.check_connect):
                            STATE["conectado"] = True
                            _log_scan(f"✅ Reconexão bem-sucedida (tentativa {tentativa_reconexao + 1}).")
                            break
                    except Exception as e:
                        _log_scan(f"⚠️ Falha ao reconectar (tentativa {tentativa_reconexao + 1}): {e}")
                        time.sleep(5)
                else:
                    _log_scan("❌ Não foi possível reconectar após 3 tentativas. Aguardando 30s...")
                    time.sleep(30)
                time.sleep(5)
                continue
            
            if _estava_desconectado:
                _log_scan("🔁 Reconexão detectada — reconstruindo lista de ativos válidos...")
                STATE["ultimo_refresh_ativos"] = 0
                with _lock_ativos:
                    for a in list(STATE["ciclo_ativos"]):
                        _remover_do_ciclo(a, "reconexão — lista reconstruída")
                    for a in list(_ativos_em_op):
                        if not _ativo_binario_turbo_existe(a.replace("Analisando ", "")):
                            _remover_em_op(a, "reconexão — ativo inexistente no catálogo Binary/Turbo")
                _log_scan("✅ Lista de ativos reconstruída.")
                _estava_desconectado = False
                _emit_status("reconexão — lista reconstruída")
            
            _verificar_reset_diario()
            
            with _lock_ativos:
                _agora_watchdog = time.time()
                for _a in list(_ativos_em_op):
                    tempo_max = 600
                    if _a.startswith("Analisando "):
                        tempo_max = 120
                    if _agora_watchdog - _ativos_em_op_ts.get(_a, _agora_watchdog) > tempo_max:
                        _remover_em_op(_a, f"watchdog — vaga presa há mais de {tempo_max}s")
            
            if encerrar_por_stop():
                break
            
            if STATE["total_operacoes"] >= STATE["limite_diario"]:
                _log_scan("⏸️ Limite diário de operações atingido. Aguardando o próximo dia...")
                time.sleep(30)
                continue
            
            if not verificar_horario():
                time.sleep(3)
                continue

            # Não inicia uma nova rodada de busca durante a pausa temporal
            # nem durante a pausa por losses seguidos. Um Gale pendente
            # mantém o fluxo original para não alterar Gale/Martingale.
            if not STATE.get("gale_pendente"):
                if not _aguardar_fim_pausa_losses(session_id):
                    break
                if not _aguardar_fim_pausa_timeframe(session_id):
                    break
            
            is_otc_now = mercado_em_otc()
            pares = _ativos_binarios_turbo(api)
            random.shuffle(pares)
            if not pares:
                _log_scan("⚠️ Catálogo Binary/Turbo vazio; aguardando atualização do cache.")
                time.sleep(3)
                continue
            
            if is_otc_now:
                pares_otc = sorted([p for p in pares if _ativo_e_otc(p)])
                pares_normais = sorted([p for p in pares if not _ativo_e_otc(p)])
                pares = pares_otc + pares_normais
                _log_scan(f"🌙 [SCANNER] Modo OTC: {len(pares_otc)} pares OTC + {len(pares_normais)} pares normais disponíveis")
            else:
                pares_normais = [p for p in pares if not _ativo_e_otc(p)]
                pares_normais.sort(key=lambda x: 0 if any(m in x.upper() for m in _FOREX_MAJORS) else 1)
                pares_otc = sorted([p for p in pares if _ativo_e_otc(p)])
                pares = pares_normais + pares_otc
                _log_scan(f"☀️ [SCANNER] Mercado Aberto: {len(pares_normais)} pares normais + {len(pares_otc)} pares OTC disponíveis")
            
            with _lock_ativos:
                STATE["ciclo_ativos"] = []
            
            _log_scan(f"🔎 [SCANNER] Analisando {len(pares)} pares Forex...")
            
            for ativo in pares:
                if not STATE["running"] or encerrar_por_stop():
                    break

                # A análise é interrompida antes de consultar o próximo ativo.
                # Assim, durante os últimos 30s não há novas análises nem novas
                # reservas de sinal; o mesmo ciclo retoma no ativo atual após a virada.
                # O mesmo vale para a pausa por losses seguidos.
                if not STATE.get("gale_pendente"):
                    if not _aguardar_fim_pausa_losses(session_id):
                        break
                    if not _aguardar_fim_pausa_timeframe(session_id):
                        break
                
                if ativo in _ativos_em_op:
                    continue
                if not _ativo_binario_turbo_existe(ativo):
                    continue
                
                modalidade_filtro = _normalizar_modalidade(STATE.get("modalidade", "ambas"))
                is_open = verificar_ativo_aberto(ativo, modalidade_filtro)
                
                if not is_open:
                    if not is_otc_now and not _ativo_e_otc(ativo):
                        pass
                    else:
                        continue
                
                with _lock_ativos:
                    candidatos_poda = list(STATE["ciclo_ativos"])
                for a in candidatos_poda:
                    if not _ativo_binario_turbo_existe(a):
                        with _lock_ativos:
                            _remover_do_ciclo(a, "ativo inexistente no catálogo Binary/Turbo")
                    elif not verificar_ativo_aberto(a, modalidade_filtro):
                        with _lock_ativos:
                            _remover_do_ciclo(a, "mercado fechado em Binary/Turbo")
                
                with _lock_ativos:
                    if ativo not in STATE["ciclo_ativos"]:
                        _definir_ativo_em_foco(ativo, limpar_confluencia=True)
                        STATE["ciclo_ativos"].insert(0, ativo)
                        # Mantém todos os ativos do ciclo visíveis; a abertura
                        # de ordens continua serializada pela regra existente.
                        STATE["ciclo_ativos"] = STATE["ciclo_ativos"][:len(pares)]
                        _emit_status(f"em análise: {ativo}")
                
                direcao, tf_label, tf_seg, score, estado_ia, fatores_ia = analisar_confluencia(ativo)
                profundidade_sinal = 0
                pendente = STATE.get("gale_pendente") or {}
                if pendente:
                    estado_pendente = _estado_gale_pendente(pendente, tf_seg)
                    if estado_pendente == "aguardando":
                        # O resultado pode ter chegado antes da virada do candle;
                        # não consumir o Gale no mesmo candle da operação perdida.
                        direcao = None
                    elif estado_pendente == "expirado":
                        _log_scan(
                            f"⏭ [MARTINGALE] Gale {pendente.get('camada', 1)} cancelado: "
                            f"nenhum sinal válido na próxima vela de {pendente.get('origem_ativo', ativo)}."
                        )
                        STATE["gale_pendente"] = None
                    elif estado_pendente == "timeframe":
                        tf_pendente = int(pendente.get("tf_seg", tf_seg or 60) or 60)
                        _log_scan(
                            f"⏭ [MARTINGALE] Gale pendente cancelado: timeframe alterado "
                            f"de {_tf_label_de_segundos(tf_pendente)} para {_tf_label_de_segundos(tf_seg)}."
                        )
                        STATE["gale_pendente"] = None
                    elif estado_pendente == "disponivel" and direcao:
                        profundidade_sinal = int(pendente.get("camada", 1) or 1)
                        origem_gale = pendente.get("origem_ativo", ativo)
                        STATE["gale_pendente"] = None
                        _log_scan(
                            f"🔄 [MARTINGALE] Próximo sinal confirmado na vela seguinte em {ativo}; "
                            f"consumindo Gale {profundidade_sinal} originado por {origem_gale}."
                        )
                        STATE["gale_atual"][ativo] = profundidade_sinal
                        STATE["direcao_gale"][ativo] = direcao
                        STATE["tf_gale"][ativo] = tf_seg
                
                try:
                    chave_sinal = None
                    if direcao:
                        with _lock_ativos:
                            ops_reais = [
                                a for a in _ativos_em_op
                                if not a.startswith("Analisando ")
                                and not (
                                    str(a).upper() == str(ativo).upper()
                                    and _ativos_em_op_motivo.get(a) == "sinal detectado"
                                )
                            ]
                            if len(ops_reais) >= 1:
                                _log_scan(f"⏳ Sinal ignorado (já existe uma operação em andamento): {ativo}")
                                direcao = None
                            else:
                                chave_sinal = _chave_do_sinal(ativo, direcao, tf_seg)
                                if not _reservar_sinal(chave_sinal, "scanner"):
                                    _log_scan(f"⏭ Sinal duplicado ignorado: {ativo} {direcao.upper()} {_tf_label_de_segundos(tf_seg)}.")
                                    direcao = None
                                else:
                                    _log_scan(f"➕ Sinal reservado para entrada: {ativo}")
                    
                    if direcao:
                        mercado_str = _identificar_mercado_ativo(ativo)
                        _log_scan(f"🎯 [SCANNER] SINAL: {ativo} {direcao.upper()} (Score: {score:.1f} | Mercado: {mercado_str} | TF: {tf_label})")
                        _log_scan(f"⏸️ Aguardando o resultado de {ativo} antes de procurar um novo par...")
                        operar(
                            ativo,
                            _profundidade=profundidade_sinal,
                            direcao_forçada=direcao,
                            tf_forçado=tf_seg,
                            score_forçado=score,
                            manual=False,
                            chave_sinal=chave_sinal,
                            estado_ia_forcado=estado_ia,
                            fatores_ia_forcado=fatores_ia,
                        )
                        _log_scan(f"▶️ Operação de {ativo} concluída. Retomando a busca por novos pares...")
                    else:
                        with _lock_ativos:
                            _remover_do_ciclo(ativo, "análise concluída — sem sinal")
                except Exception as e:
                    _log_scan(f"⚠️ Erro ao processar {ativo}: {e}")
                    with _lock_ativos:
                        if ativo in _ativos_em_op:
                            _remover_em_op(ativo, "erro no scanner")
                        _remover_do_ciclo(ativo, "erro no scanner")
                    continue
                
                time.sleep(0.05)
            
            _log_scan("✅ Ciclo concluído. Próxima rodada em 5s...")
            STATE["pares_scan"] = len(pares)
            _emit_status("ciclo concluído")
            time.sleep(5)
        
        except Exception as e:
            _log_scan(f"⚠️ Erro no Loop: {e}")
            time.sleep(5)
    
    duracao = int(time.time() - STATE["inicio_sessao"]) if STATE.get("inicio_sessao") else 0
    h, rem = divmod(duracao, 3600)
    m, s = divmod(rem, 60)
    total = STATE["wins"] + STATE["losses"]
    wr = f"{round(STATE['wins'] / total * 100, 1)}%" if total > 0 else "-%"
    _log_scan("=" * 50)
    _log_scan("📋 RESUMO DA SESSÃO — LUA QUADCODE")
    _log_scan(f"Duração  : {h:02d}h {m:02d}m {s:02d}s")
    _log_scan(f"Resultado: R$ {STATE['saldo_acumulado']:+.2f}")
    _log_scan(f"W: {STATE['wins']}  L: {STATE['losses']}  E: {STATE['empates']}  |  WR: {wr}")
    _log_scan("📋 Fonte de sinais: script Lua Quadcode autorizado")
    _log_scan("=" * 50)
    _log_scan("═══ Scanner encerrado ═══")

_LOGIN_STATE = {"status": "idle", "msg": "", "saldo": 0.0, "tipo": "PRACTICE"}
_balance_refresh_lock = threading.Lock()
_BALANCE_REFRESH_TTL = 5.0
_balance_updated_at = 0.0

def _refresh_balance_background(api):
    global _balance_updated_at
    if not _balance_refresh_lock.acquire(blocking=False):
        return
    try:
        saldo_novo, executado = _api_call_if_available(api.get_balance)
        if executado and saldo_novo is not None:
            STATE["saldo"] = saldo_novo
            _balance_updated_at = time.time()
    except Exception:
        pass
    finally:
        _balance_refresh_lock.release()

@app.route('/api/login', methods=['POST'])
def api_login():
    data = request.json or {}
    email = data.get('email', '').strip()
    senha = data.get('senha', '').strip()
    tipo  = data.get('tipo', 'PRACTICE').upper()
    if not email or not senha:
        return jsonify({"ok": False, "msg": "Email e senha obrigatórios"}), 400
    
    if STATE.get("conectado") and STATE.get("email") == email and STATE.get("api"):
        saldo = STATE.get("saldo", 0.0)
        return jsonify({"ok": True, "saldo": round(saldo, 2), "tipo": STATE.get("tipo_conta", tipo)})
    
    if _LOGIN_STATE["status"] == "connecting":
        return jsonify({"ok": False, "msg": "Login em andamento, aguarde...", "status": "connecting"}), 202
    
    _LOGIN_STATE["status"] = "connecting"
    _LOGIN_STATE["msg"] = "Conectando..."
    
    def _do_login_background():
        try:
            import iqoptionapi.global_value as gv
            gv.balance_id = None
            gv.SSID = None
            gv.check_websocket_if_connect = None
            gv.check_websocket_if_error = False
            gv.websocket_error_reason = None
            gv.ssl_Mutual_exclusion = False
            gv.ssl_Mutual_exclusion_write = False
            
            _log_scan(f"🔐 Iniciando login para {email}...")
            api = IQ_Option(email, senha)
            
            _result = [None, None]
            _done = threading.Event()
            def _do_connect():
                try:
                    _result[0], _result[1] = api.connect()
                except Exception as _e:
                    _result[0] = False
                    _result[1] = str(_e)
                finally:
                    _done.set()
            _t = threading.Thread(target=_do_connect, daemon=True)
            _t.start()
            _done.wait(timeout=180)
            
            check, reason = _result[0], _result[1]
            if not check:
                _LOGIN_STATE["status"] = "error"
                _LOGIN_STATE["msg"] = f"Falha: {reason or 'Timeout de conexão'}"
                _log_scan(f"❌ Login falhou: {_LOGIN_STATE['msg']}")
                _emit_status("login_falhou")
                return
            
            def _registrar_instrumentos():
                try:
                    _api_call_com_timeout(api.get_ALL_Binary_ACTIVES_OPCODE, 30)
                    _log_scan("✅ Tabela de instrumentos binários registrada.")
                except Exception as _e:
                    _log_scan(f"⚠️ Falha ao registrar instrumentos extras: {_e}")
            threading.Thread(target=_registrar_instrumentos, daemon=True).start()
            
            if _api_call_com_timeout(api.change_balance, 15, tipo) is None:
                raise TimeoutError("Timeout ao selecionar a conta")
            time.sleep(0.5)
            saldo = _api_call_com_timeout(api.get_balance, 10)
            if saldo is None:
                raise TimeoutError("Timeout ao obter o saldo inicial")
            
            STATE.update({
                "api": api, "conectado": True, "running": False,
                "session_id": STATE["session_id"] + 1, "tipo_conta": tipo,
                "email": email, "saldo": saldo, "saldo_inicial": saldo,
                "saldo_acumulado": 0.0, "lucro_bruto": 0.0, "prejuizo_bruto": 0.0,
                "wins": 0, "losses": 0, "empates": 0,
                "historico": [], "scan_log": [], "ciclo_ativos": [],
                "gale_atual": {}, "direcao_gale": {}, "tf_gale": {}, "gale_pendente": None,
                "losses_seguidos_atual": 0, "pausa_losses_ate": 0.0,
                "martingale_state": gerenciador_martingale.get_status(), "valor_gale_base": {}, "cooldown": {}
            })
            _verificar_reset_diario()
            
            _LOGIN_STATE["status"] = "ok"
            _LOGIN_STATE["msg"] = "Conectado"
            _LOGIN_STATE["saldo"] = round(saldo, 2)
            _LOGIN_STATE["tipo"] = tipo
            
            modo_mercado = "OTC" if mercado_em_otc() else "Mercado Aberto"
            _log_scan(f"✅ Login OK — {email} | {tipo} | Saldo: R${saldo:.2f}")
            _log_scan(f"🌐 Modo de mercado atual: {modo_mercado}")
            threading.Thread(target=_ttz_auto_login_from_robot, args=(email, senha), name="ttz-auto-login", daemon=True).start()
            
            def _preencher_cache_abertos():
                try:
                    _log_scan("📡 Preenchendo cache de ativos abertos...")
                    try:
                        OPEN_TIME = _api_call_com_timeout(api.get_all_open_time, 60)
                        if OPEN_TIME and isinstance(OPEN_TIME, dict):
                            STATE["ativos_abertos"] = OPEN_TIME
                            STATE["ultimo_refresh_ativos"] = time.time()
                            total = 0
                            abertos = 0
                            for cat in ('turbo', 'binary', 'digital', 'forex'):
                                info = OPEN_TIME.get(cat, {})
                                if isinstance(info, dict):
                                    total += len(info)
                                    abertos += sum(1 for v in info.values() if isinstance(v, dict) and v.get('open'))
                            _log_scan(f"✅ Cache preenchido: {total} ativos, {abertos} abertos")
                        else:
                            _log_scan("⚠️ Cache vazio — usando fallback do WebSocket")
                            _usar_cache_interno_biblioteca()
                    except Exception as e:
                        _log_scan(f"⚠️ Falha ao obter ativos abertos: {e}. Usando fallback...")
                        _usar_cache_interno_biblioteca()
                except Exception as e:
                    _log_scan(f"⚠️ Falha ao preencher cache: {e}")
            
            def _usar_cache_interno_biblioteca():
                try:
                    _log_scan("📡 Tentando obter cache do WebSocket interno...")
                    time.sleep(3)
                    ws = getattr(api, 'api', None)
                    if not ws:
                        return
                    data = getattr(ws, 'api_option_init_all_result_v2', None)
                    if data and isinstance(data, dict) and len(data) > 0:
                        parsed = _parse_binary_cache(data)
                        if parsed:
                            STATE["ativos_abertos"] = parsed
                            STATE["ultimo_refresh_ativos"] = time.time()
                            return
                    data = getattr(ws, 'api_option_init_all_result', None)
                    if data and isinstance(data, dict):
                        parsed = _parse_binary_cache(data)
                        if parsed:
                            STATE["ativos_abertos"] = parsed
                            STATE["ultimo_refresh_ativos"] = time.time()
                            return
                except Exception as e:
                    _log_scan(f"⚠️ Falha no fallback: {e}")
            
            threading.Thread(target=_preencher_cache_abertos, daemon=True).start()
            _emit_status("login")
        except Exception as e:
            _LOGIN_STATE["status"] = "error"
            _LOGIN_STATE["msg"] = str(e)
            _log_scan(f"❌ Exceção no login: {e}")
            _emit_status("login_erro")
    
    threading.Thread(target=_do_login_background, daemon=True).start()
    return jsonify({"ok": True, "msg": "Login iniciado em background. Aguarde o status conectado.", "status": "connecting"})

@app.route('/api/login_status', methods=['GET'])
def api_login_status():
    if STATE.get("conectado") and STATE.get("api"):
        return jsonify({
            "ok": True, "status": "ok",
            "conectado": True,
            "saldo": round(STATE.get("saldo", 0.0), 2),
            "tipo": STATE.get("tipo_conta", "PRACTICE"),
            "email": STATE.get("email", "")
        })
    return jsonify({
        "ok": _LOGIN_STATE["status"] == "ok",
        "status": _LOGIN_STATE["status"],
        "msg": _LOGIN_STATE["msg"],
        "saldo": _LOGIN_STATE.get("saldo", 0.0),
        "tipo": _LOGIN_STATE.get("tipo", "PRACTICE"),
        "conectado": STATE.get("conectado", False)
    })

def _build_status_payload(atualizar_saldo=True):
    _verificar_reset_diario()
    api = STATE["api"]
    # O painel é consultado com frequência. A leitura da corretora ocorre em
    # background e o endpoint devolve imediatamente o último saldo conhecido.
    if atualizar_saldo and api and STATE["conectado"]:
        global _balance_updated_at
        if time.time() - _balance_updated_at >= _BALANCE_REFRESH_TTL:
            threading.Thread(target=_refresh_balance_background, args=(api,), name="saldo-refresh", daemon=True).start()
    total = STATE["wins"] + STATE["losses"]
    winrate = round(STATE["wins"] / total * 100, 1) if total > 0 else 0.0
    janela_candle = _estado_janela_candle()
    with _lock_ativos:
        ops_reais_raw = sorted(_ativos_em_op, key=lambda x: _ativos_em_op_ts.get(x, 0), reverse=True)
        niveis_gale_cfg = STATE.get("niveis_gale", 0)
        ops_reais = []
        for a in ops_reais_raw:
            camada = STATE.get("gale_atual", {}).get(a, 0)
            if camada > 0:
                ops_reais.append(f"{a} (Gale {camada}/{niveis_gale_cfg})")
            else:
                ops_reais.append(a)
        em_analise_ciclo = [f"Analisando {a}" for a in STATE.get("ciclo_ativos", []) if a not in _ativos_em_op]
        em_op = ops_reais + em_analise_ciclo
    
    # Atualizar status do Soros
    if STATE.get("usar_soros"):
        STATE["soros_status"] = gerenciador_soros.get_status()

    sentimento_status = _atualizar_sentimento_status()
    
    return {
        "hora_brasilia": _agora_brasilia().strftime("%H:%M:%S"),
        "fuso_horario": "America/Sao_Paulo",
        # O frontend usa este valor para calcular o countdown com o mesmo
        # relógio do backend, evitando zeragem causada por diferença de horário.
        "agora_epoch": time.time(),
        "conectado": STATE["conectado"], "running": STATE["running"], "tipo_conta": STATE["tipo_conta"],
        "saldo": round(STATE["saldo"], 2),
        "saldo_acumulado": round(STATE["saldo_acumulado"], 2),
        "lucro_bruto": round(STATE.get("lucro_bruto", 0.0), 2),
        "prejuizo_bruto": round(STATE.get("prejuizo_bruto", 0.0), 2),
        "wins": STATE["wins"], "losses": STATE["losses"], "empates": STATE["empates"], "winrate": winrate,
        "total_ops": STATE["total_operacoes"], "limite_diario": STATE.get("limite_diario", 1000),
        "historico": STATE["historico"][:5], "ultima_op": STATE["ultima_operacao"],
        "scan_log": STATE["scan_log"][:10], "em_operacao": em_op, "em_operacao_qt": len(em_op),
        "pares_scan": STATE.get("pares_scan", 0), "modo_otc": STATE.get("modo_otc", False),
        "ativo_em_foco": STATE.get("ativo_em_foco"),
                "script_lua": STATE.get("script_lua", ""),
        "script_lua_autorizado": STATE.get("script_lua_autorizado", False),
        "script_lua_erro": STATE.get("script_lua_erro", ""),
        "usar_catalogo": False,
        "catalogo_estrategias": STATE.get("catalogo_estrategias", list(CATALOG_STRATEGIES)),
        "catalogo_total_estrategias": len(CATALOG_STRATEGIES),
        "catalogo_padroes_candle": list(CATALOG_CANDLE_PATTERNS),
        "catalogo_indicadores": ["RSI", "Aroon", "Darvas", "Suporte/Resistência", "Fibonacci", "Precision Trend", "DDFX BBStop", "Double ZigZag", "Parabolic SAR", "Forex Guru Cloud"],
        "catalogo_ultimo_voto": STATE.get("catalogo_ultimo_voto", {}),
        "confluencia_estrategias": dict(STATE.get("confluencia_estrategias") or {}),
        "configuracoes": {
            chave: STATE.get(chave) for chave in (
                "valor_entrada", "usar_gale", "niveis_gale", "fator_gale", "atraso_martingale_segundos", "martingale_modo", "stop_win", "stop_loss",
                "losses_seguidos_limite", "losses_seguidos_pausa_min",
                "limite_diario", "expiracao", "modo_auto", "modalidade", "horario_inicio", "horario_fim",
                "ttz_ativo", "ttz_time_action", "ttz_filter_by_currency", "ttz_refresh_seconds", "ttz_selected_zones", "ttz_blocked_zones", "ttz_schedule",
                "usar_soros", "niveis_soros", "reinvestimento_soros", "script_lua", "script_lua_autorizado",
                "min_indicadores_confluencia",

                "usar_price_action", "usar_indicadores", "usar_top5_indicadores", "usar_rsi", "usar_aroon",
                "usar_darvas", "usar_suporte_resistencia", "usar_fibonacci", "usar_fluxo", "usar_efectiv",
                "usar_lta_ltb", "usar_order_flow", "usar_persistencia", "usar_vacuo", "usar_sentimento",
                "usar_filtros_pro", "usar_exaustao", "usar_ruido", "bloquear_por_noticias", "noticias_ativas",
                "tempo_antes_noticia", "tempo_depois_noticia",
            )
        },
        "soros_status": STATE.get("soros_status") or gerenciador_soros.get_status(),
        "martingale_status": STATE.get("martingale_state") or gerenciador_martingale.get_status(),
        "config_estrategias": {},
        "ultimo_sinal_estrategia": STATE.get("ultimo_sinal_estrategia", {}),
        "operacao_atual": STATE.get("operacao_atual"),
        "timeframe_operacao": _tf_label_de_segundos(_timeframe_configurado()[0]),
        "expiracao_operacao": _timeframe_configurado()[0] // 60,
        "pausar_novas_entradas": janela_candle["pausar_novas_entradas"],
        "tempo_restante_candle": round(janela_candle["tempo_restante"], 3),
        "fechamento_candle_epoch": janela_candle["fechamento_candle_epoch"],
        "ttz": _ttz_status(),
        "sentimento_traders": sentimento_status,
        "pausa_losses": {
            "ativa": time.time() < float(STATE.get("pausa_losses_ate", 0.0) or 0.0),
            "restante_seg": max(0.0, round(float(STATE.get("pausa_losses_ate", 0.0) or 0.0) - time.time(), 1)),
            "losses_seguidos_atual": int(STATE.get("losses_seguidos_atual", 0) or 0),
        },
    }

def _emit_status(motivo="update"):
    try:
        socketio.emit('status_update', _build_status_payload(atualizar_saldo=False))
    except Exception as e:
        _log_scan(f"⚠️ Falha ao emitir status via WebSocket ({motivo}): {e}")

@socketio.on('connect')
def _on_socket_connect():
    # Socket.IO não envia automaticamente os headers personalizados usados pelo
    # fetch; o frontend repassa a senha opcional como query string.
    if not _backend_access_authorized(request.args.get("backend_password", "")):
        return False
    from flask_socketio import emit
    emit('status_update', _build_status_payload())

@app.route('/api/status', methods=['GET'])
def api_status():
    return jsonify(_build_status_payload())

def _ttz_bridge_authorized():
    expected = os.getenv('TTZ_BRIDGE_SECRET', '').strip()
    provided = request.headers.get('X-TTZ-Bridge-Secret', '')
    if expected and hmac.compare_digest(provided, expected):
        return True
    if request.remote_addr in ('127.0.0.1', '::1') and not expected:
        return True
    # O dashboard oficial faz a ponte pelo navegador; aceite somente a origem
    # oficial quando nenhum segredo local estiver configurado.
    return request.headers.get('Origin', '').rstrip('/') == TTZ_BASE_URL


@app.route('/api/ttz/login', methods=['POST'])
def api_ttz_login():
    data = request.json or {}
    email = str(data.get('email') or '').strip()
    password = str(data.get('password') or data.get('senha') or '')
    if not email or not password:
        return jsonify({'ok': False, 'msg': 'E-mail e senha TTZ são obrigatórios'}), 400
    try:
        cookie_header, session_data = _ttz_login(email, password)
        STATE['ttz_session_cookie'] = cookie_header
        STATE['ttz_session_email'] = email
        STATE['ttz_session_updated_at'] = time.time()
        STATE['ttz_source'] = 'dashboard autenticado'
        STATE['ttz_last_update'] = 0
        STATE['ttz_error'] = ''
        _ttz_refresh(force=True)
        return jsonify({'ok': True, 'msg': 'Sessão TTZ conectada', 'ttz': _ttz_status()})
    except Exception as exc:
        STATE['ttz_session_cookie'] = ''
        STATE['ttz_session_email'] = ''
        STATE['ttz_session_updated_at'] = 0
        STATE['ttz_error'] = f'Falha no login TTZ: {exc}'
        return jsonify({'ok': False, 'msg': str(exc), 'ttz': _ttz_status()}), 401


@app.route('/api/ttz/logout', methods=['POST'])
def api_ttz_logout():
    STATE['ttz_session_cookie'] = ''
    STATE['ttz_session_email'] = ''
    STATE['ttz_session_updated_at'] = 0
    STATE['ttz_source'] = ''
    STATE['ttz_market_token'] = ''
    STATE['ttz_market_payload'] = None
    STATE['ttz_market_received_at'] = 0
    _ttz_clear_market_token()
    STATE['ttz_events'] = []
    STATE['ttz_last_update'] = 0
    STATE['ttz_error'] = ''
    return jsonify({'ok': True, 'ttz': _ttz_status()})


@app.route('/api/ttz/ingest', methods=['POST'])
def api_ttz_ingest():
    if not _ttz_bridge_authorized():
        return jsonify({'ok': False, 'msg': 'Ponte TTZ não autorizada'}), 403
    data = request.json or {}
    token = str(data.get('token') or '').strip()
    payload = _ttz_decode_market_token(token)
    if not payload:
        return jsonify({'ok': False, 'msg': 'Token TTZ inválido ou expirado'}), 400
    STATE['ttz_market_token'] = token
    STATE['ttz_market_payload'] = payload
    STATE['ttz_market_received_at'] = time.time()
    _ttz_persist_market_token(token)
    STATE['ttz_source'] = 'dashboard-api'
    STATE['ttz_last_update'] = time.time()
    STATE['ttz_error'] = ''
    _emit_status('TTZ dashboard atualizado')
    current, next_item = _ttz_market_state(payload)
    return jsonify({'ok': True, 'current_zone': current, 'next_zone': next_item, 'source': 'dashboard-api'})


@app.route('/api/config', methods=['POST'])
def api_config():
    data = request.json or {}
    if "script_lua" in data:
        valido, mensagem = _autorizar_script_lua(data.get("script_lua"))
        if not valido:
            return jsonify({"ok": False, "erro": mensagem, "msg": mensagem}), 400
        STATE["script_lua"] = str(data.get("script_lua") or "").replace("\r\n", "\n").strip()
        STATE["script_lua_autorizado"] = True
        STATE["script_lua_erro"] = ""
    elif not STATE.get("script_lua"):
        STATE["script_lua_autorizado"] = False
        STATE["script_lua_erro"] = "Nenhum script Lua Quadcode autorizado."
    mapa_tipos = {
        "valor_entrada": float, "fator_gale": float, "atraso_martingale_segundos": int, "martingale_modo": str, "stop_win": float, "stop_loss": float,
        "niveis_gale": int, "limite_diario": int, "expiracao": int, "max_gale": int,
        "losses_seguidos_limite": int, "losses_seguidos_pausa_min": float,
        "horario_inicio": str, "horario_fim": str,
        "min_indicadores_confluencia": int,
        "usar_gale": bool, "modo_auto": bool, "ativo_manual": str, "modalidade": str,
        "horario_inicio": str, "horario_fim": str, "usar_soros": bool, "niveis_soros": int, "reinvestimento_soros": int,
        "usar_catalogo": bool, "script_lua": str,
        "usar_price_action": bool, "usar_indicadores": bool, "usar_top5_indicadores": bool,
        "usar_rsi": bool, "usar_aroon": bool, "usar_darvas": bool,
        "usar_suporte_resistencia": bool, "usar_fibonacci": bool,
        "usar_fluxo": bool, "usar_efectiv": bool, "usar_lta_ltb": bool,
        "usar_order_flow": bool, "usar_persistencia": bool, "usar_vacuo": bool,
        "usar_sentimento": bool, "usar_filtros_pro": bool, "usar_exaustao": bool,
        "usar_ruido": bool, "bloquear_por_noticias": bool, "noticias_ativas": bool,
        "tempo_antes_noticia": int, "tempo_depois_noticia": int,
        "ttz_ativo": bool, "ttz_time_action": str, "ttz_filter_by_currency": bool,
        "ttz_refresh_seconds": int,
    }
    for campo, tipo in mapa_tipos.items():
        if campo in data:
            try:
                STATE[campo] = tipo(data[campo])
            except Exception:
                pass

    STATE["modalidade"] = _normalizar_modalidade(STATE.get("modalidade", "ambas"))

    if "ttz_blocked_zones" in data or "ttz_selected_zones" in data:
        try:
            recebidas = data.get("ttz_blocked_zones") if "ttz_blocked_zones" in data else data.get("ttz_selected_zones")
            STATE["ttz_blocked_zones"] = _ttz_normalize_zone_list(recebidas)
            # Mantém o campo antigo como alias para compatibilidade com clientes anteriores.
            STATE["ttz_selected_zones"] = list(STATE["ttz_blocked_zones"])
        except Exception:
            STATE["ttz_blocked_zones"] = []
            STATE["ttz_selected_zones"] = []
    if "ttz_schedule" in data:
        STATE["ttz_schedule"] = _ttz_normalize_schedule(data.get("ttz_schedule"))
        STATE["ttz_events"] = []
    if any(campo in data for campo in ("ttz_ativo", "ttz_time_action", "ttz_filter_by_currency", "ttz_refresh_seconds")):
        STATE["ttz_time_action"] = "ALLOW" if str(STATE.get("ttz_time_action", "PAUSE")).upper() == "ALLOW" else "PAUSE"
        STATE["ttz_refresh_seconds"] = max(15, min(int(STATE.get("ttz_refresh_seconds", 60) or 60), 900))
        STATE["ttz_last_update"] = 0
        STATE["ttz_error"] = ""

    if "catalogo_estrategias" in data:
        try:
            recebidas = data.get("catalogo_estrategias")
            if recebidas is None:
                STATE["catalogo_estrategias"] = list(CATALOG_STRATEGIES)
            else:
                STATE["catalogo_estrategias"] = [nome for nome in recebidas if nome in CATALOG_STRATEGIES]
        except Exception:
            STATE["catalogo_estrategias"] = list(CATALOG_STRATEGIES)

    if "config_estrategias" in data and isinstance(data.get("config_estrategias"), dict):
        atual = STATE.get("config_estrategias") or {}
        for nome, cfg_recebida in data["config_estrategias"].items():
            if nome not in ESTRATEGIA_CONFIG_DEFAULTS or not isinstance(cfg_recebida, dict):
                continue
            defaults = ESTRATEGIA_CONFIG_DEFAULTS[nome]
            saneada = dict(atual.get(nome, {}))
            for campo, valor in cfg_recebida.items():
                if campo not in defaults:
                    continue
                default_val = defaults[campo]
                try:
                    if isinstance(default_val, bool):
                        saneada[campo] = bool(valor)
                    elif isinstance(default_val, int) and not isinstance(default_val, bool):
                        saneada[campo] = max(1, int(valor))
                    elif isinstance(default_val, float):
                        saneada[campo] = float(valor)
                    elif campo == "padroes":
                        recebidos = valor if isinstance(valor, dict) else {}
                        saneada[campo] = {
                            chave: bool(recebidos.get(chave, padrao))
                            for chave, padrao in CANDLESTICK_PATTERN_DEFAULTS.items()
                        }
                    elif campo == "timeframes":
                        tfs = [int(x) for x in (valor or []) if int(x) in (1, 5, 15)]
                        saneada[campo] = tfs or [1, 5, 15]
                    elif campo == "direcao":
                        saneada[campo] = valor if valor in ("call", "put", "ambos") else "ambos"
                    elif campo == "sensibilidade":
                        saneada[campo] = valor if valor in _SENSIBILIDADE_MULTIPLICADOR else "media"
                    else:
                        saneada[campo] = valor
                except (TypeError, ValueError):
                    continue
            if "forca_minima" in saneada:
                saneada["forca_minima"] = max(0, min(100, saneada["forca_minima"]))
            atual[nome] = saneada
        STATE["config_estrategias"] = atual

    STATE["valor_entrada"] = max(0.01, round(float(STATE.get("valor_entrada", 5.0) or 5.0), 2))
    STATE["niveis_gale"] = max(0, min(int(STATE.get("niveis_gale", 0) or 0), 10))
    # 0 = pausa por losses seguidos desativada; limite prático de 20 losses e 720 min (12h).
    STATE["losses_seguidos_limite"] = max(0, min(int(STATE.get("losses_seguidos_limite", 0) or 0), 20))
    STATE["losses_seguidos_pausa_min"] = max(0.0, min(float(STATE.get("losses_seguidos_pausa_min", 0) or 0), 720.0))
    STATE["fator_gale"] = max(1.0, round(float(STATE.get("fator_gale", 2.2) or 2.2), 4))
    STATE["atraso_martingale_segundos"] = _atraso_martingale_segundos()
    if STATE.get("martingale_modo") not in ("proxima_vela", "proximo_sinal"):
        STATE["martingale_modo"] = "proxima_vela"
    gerenciador_martingale.configurar(
        STATE.get("usar_gale", False), STATE["valor_entrada"], STATE["fator_gale"],
        STATE["niveis_gale"], STATE["martingale_modo"]
    )
    STATE["martingale_state"] = gerenciador_martingale.get_status()
    STATE["min_indicadores_confluencia"] = _minimo_confluencia()
    valor_antes = STATE.get("tempo_antes_noticia", 5)
    valor_depois = STATE.get("tempo_depois_noticia", 5)
    STATE["tempo_antes_noticia"] = max(0, min(int(5 if valor_antes is None else valor_antes), 1440))
    STATE["tempo_depois_noticia"] = max(0, min(int(5 if valor_depois is None else valor_depois), 1440))
    STATE["limite_diario"] = max(1, min(int(STATE.get("limite_diario", 1000)), 1000))
    STATE["stop_win"] = max(0.01, float(STATE.get("stop_win", 100.0)))
    STATE["stop_loss"] = max(0.01, float(STATE.get("stop_loss", 100.0)))
    if STATE.get("expiracao") not in (1, 5, 15):
        STATE["expiracao"] = 1
    # A modalidade é escolhida na interface e validada em cada entrada conforme
    # a disponibilidade real e a duração compatível.
    STATE['modalidade'] = _normalizar_modalidade(STATE.get('modalidade', 'ambas'))
    if 'ativo_manual' in data and not STATE.get('running') and not STATE.get('operacao_atual'):
        _definir_ativo_em_foco(STATE.get('ativo_manual'), limpar_confluencia=True)

    # Configurar Soros
    usar_soros = STATE.get('usar_soros', False)
    niveis_soros = max(1, min(STATE.get('niveis_soros', 3), 10))
    reinvestimento = max(0, min(STATE.get('reinvestimento_soros', 100), 100))
    
    try:
        if usar_soros:
            gerenciador_soros.ativar_soros(niveis_soros, reinvestimento)
            _log_scan(f"🎯 Soros ativado: {niveis_soros} niveis, {reinvestimento}% reinvestimento")
        else:
            gerenciador_soros.configurar(False, niveis_soros, reinvestimento)
            _log_scan(f"🎯 Soros desativado")
    except Exception as e:
        # Não deixa uma falha no Soros impedir o salvamento do resto da configuração
        _log_scan(f"⚠️ Erro ao configurar Soros: {e}")
    
    _emit_status("configuração atualizada")
    return jsonify({"ok": True, "ttz": _ttz_status()})

@app.route('/api/start', methods=['POST'])
def api_start():
    global _ativos_em_op
    if not STATE["conectado"] or not STATE["api"]:
        return jsonify({"ok": False, "msg": "Não conectado"}), 400
    valido, mensagem = _autorizar_script_lua(STATE.get("script_lua"))
    if not valido:
        STATE["script_lua_autorizado"] = False
        STATE["script_lua_erro"] = mensagem
        return jsonify({"ok": False, "msg": "O robô só inicia com um script Lua Quadcode autorizado: " + mensagem}), 400
    if STATE["running"]:
        return jsonify({"ok": False, "msg": "Bot já rodando"})
    with _lock_ativos:
        _ativos_em_op = set()
        _ativos_em_op_ts.clear()
    _verificar_reset_diario()
    gerenciador_soros.resetar_sequencia()
    gerenciador_martingale.resetar()
    STATE.update({
        "running": True, "saldo_acumulado": 0.0, "lucro_bruto": 0.0, "prejuizo_bruto": 0.0,
        "wins": 0, "losses": 0, "empates": 0,
        "gale_atual": {}, "direcao_gale": {}, "tf_gale": {}, "gale_pendente": None,
        "martingale_state": gerenciador_martingale.get_status(), "valor_gale_base": {}, "cooldown": {},
        "losses_seguidos_atual": 0, "pausa_losses_ate": 0.0,
        "scan_log": [], "ciclo_ativos": [],
        "ativo_em_foco": None,
        "sentimento_traders": _sentimento_indisponivel("aguardando análise do par"),
        "sentimento_traders_ultimo_refresh": 0.0,
        "confluencia_estrategias": {
            "ativo": None, "timeframe": "", "direcao": None,
            "estrategias": [], "call": [], "put": [], "total": 0,
            "minimo": _minimo_confluencia(), "aprovada": False,
            "atualizado_em": time.time(),
        },
        "inicio_sessao": time.time()
    })
    threading.Thread(target=loop_bot, args=(STATE["session_id"],), daemon=True).start()
    _emit_status("bot iniciado")
    return jsonify({"ok": True})

@app.route('/api/ativos', methods=['GET'])
def api_ativos():
    try:
        api = STATE.get("api")
        dados = _refresh_ativos_abertos(api) if api else STATE.get("ativos_abertos") or {}
        catalogo = _catalogo_binario_turbo(dados)
        if not catalogo and api:
            catalogo = _catalogo_binario_turbo(_get_cache_from_library(api))
        ativos = [item["ativo"] for item in catalogo]
        STATE["pares_scan"] = len(ativos)
        resumo_modalidades = {
            modalidade: {
                "total": sum(modalidade in item["modalidades"] for item in catalogo),
                "abertos": sum(bool(item["abertas"].get(modalidade)) for item in catalogo),
            }
            for modalidade in ("binary", "turbo")
        }
        _log_scan(
            f"📡 API /ativos: {len(ativos)} instrumentos | "
            f"BINÁRIA {resumo_modalidades['binary']['total']} "
            f"({resumo_modalidades['binary']['abertos']} abertos) | "
            f"TURBO {resumo_modalidades['turbo']['total']} "
            f"({resumo_modalidades['turbo']['abertos']} abertos)"
        )
        return jsonify({
            "ok": True,
            "ativos": ativos,
            "catalogo": catalogo,
            "total": len(ativos),
            "modalidades": ["binary", "turbo"],
            "resumo_modalidades": resumo_modalidades,
        })
    except Exception as e:
        _log_scan(f"⚠️ Erro em /api/ativos: {e}")
        return jsonify({"ok": False, "ativos": [], "catalogo": [], "total": 0, "erro": str(e)}), 500

@app.route('/api/stop', methods=['POST'])
def api_stop():
    STATE["running"] = False
    _log_scan("Bot pausado via API")
    _emit_status("bot pausado")
    return jsonify({"ok": True})

@app.route('/api/operar_manual', methods=['POST'])
def api_operar_manual():
    api = STATE["api"]
    if not api:
        return jsonify({"ok": False, "msg": "Não conectado (Refaça o login)"}), 400
    is_connected = STATE.get("conectado", False)
    if not is_connected:
        return jsonify({"ok": False, "msg": "Não conectado (aguarde alguns segundos e tente novamente)"}), 400
    
    data = request.json or {}
    ativo = data.get('ativo')
    direcao = data.get('direcao')
    if not ativo or not direcao:
        return jsonify({"ok": False, "msg": "Ativo e direção obrigatórios"}), 400
    
    if not _ativo_binario_turbo_existe(ativo):
        return jsonify({"ok": False, "msg": f"Ativo {ativo} não pertence ao catálogo Binary/Turbo disponível."}), 400
    
    _verificar_reset_diario()
    if not verificar_horario(ativo):
        _, motivo_ttz = _ttz_check_entry(ativo)
        msg = motivo_ttz if STATE.get("ttz_ativo") else "Fora do horário de operação configurado"
        return jsonify({"ok": False, "msg": msg, "ttz": _ttz_status()}), 400
    if stop_atingido():
        return jsonify({"ok": False, "msg": "Stop Win/Loss diário já atingido"}), 400
    if STATE["total_operacoes"] >= STATE["limite_diario"]:
        return jsonify({"ok": False, "msg": "Limite diário de operações atingido"}), 400

    restante_pausa = _pausa_losses_restante_seg()
    if restante_pausa > 0:
        minutos = int(restante_pausa // 60)
        segundos = int(restante_pausa % 60)
        _log_scan(
            f"⏭ [PAUSA LOSSES] Entrada manual bloqueada para {ativo}: "
            f"{minutos}min {segundos:02d}s restantes."
        )
        return jsonify({
            "ok": False,
            "msg": f"Pausa por losses seguidos ativa: {minutos}min {segundos:02d}s restantes",
            "pausa_losses": {
                "ativa": True,
                "restante_seg": round(restante_pausa, 1),
                "losses_seguidos_atual": int(STATE.get("losses_seguidos_atual", 0) or 0),
            },
        }), 409
    
    modalidade_manual = _normalizar_modalidade(data.get("modalidade") if "modalidade" in data else STATE.get("modalidade", "ambas"))
    tf_manual = max(60, int(STATE.get("expiracao", 1)) * 60)
    if modalidade_manual != "ambas" and not _modalidade_compativel_com_expiracao(modalidade_manual, tf_manual // 60):
        return jsonify({
            "ok": False,
            "msg": f"A modalidade {modalidade_manual.upper()} não é compatível com M{tf_manual // 60}. Use AMBAS ou ajuste o timeframe.",
        }), 400
    janela_candle = _estado_janela_candle(tf_manual)
    if janela_candle["pausar_novas_entradas"]:
        return jsonify({
            "ok": False,
            "msg": (
                f"Novas entradas pausadas nos últimos 30 segundos do candle "
                f"{janela_candle['timeframe']} ({janela_candle['tempo_restante']:.1f}s restantes)"
            ),
            "pausar_novas_entradas": True,
            "tempo_restante_candle": round(janela_candle["tempo_restante"], 3),
        }), 409
    chave_sinal = _chave_do_sinal(ativo, direcao, tf_manual)
    with _lock_ativos:
        if ativo in _ativos_em_op:
            return jsonify({"ok": False, "msg": "Já existe uma operação em andamento para este ativo"}), 409
        if not _reservar_sinal(chave_sinal, "manual"):
            return jsonify({"ok": False, "msg": "Este sinal já foi processado"}), 409
        _remover_do_ciclo(ativo, "entrada manual")
        _adicionar_em_op(ativo, "entrada manual")
    
    mercado_str = _identificar_mercado_ativo(ativo)
    _log_scan(f"🖐️ ENTRADA MANUAL: {ativo} {direcao.upper()} | Preferência: {modalidade_manual.upper()} | Mercado: {mercado_str}")
    
    threading.Thread(
        target=operar,
        args=(ativo,),
        kwargs={'direcao_forçada': direcao, 'tf_forçado': tf_manual, 'manual': True, 'chave_sinal': chave_sinal, 'estado_ia_forcado': None, 'modalidade_forçada': modalidade_manual},
        daemon=True,
    ).start()
    return jsonify({"ok": True})

@app.route('/api/trocar_conta', methods=['POST'])
def api_trocar_conta():
    api = STATE["api"]
    if not api:
        return jsonify({"ok": False, "msg": "Não conectado"}), 400
    data = request.json or {}
    tipo = data.get('tipo', 'PRACTICE').upper()
    if tipo not in ('REAL', 'PRACTICE'):
        return jsonify({"ok": False, "msg": "Tipo inválido"}), 400
    try:
        if _api_call_com_timeout(api.change_balance, 15, tipo) is None:
            raise TimeoutError("Timeout ao trocar a conta")
        time.sleep(0.5)
        saldo = _api_call_com_timeout(api.get_balance, 10)
        if saldo is None:
            raise TimeoutError("Timeout ao atualizar o saldo da conta")
        STATE["tipo_conta"] = tipo
        STATE["saldo"] = saldo
        _LOGIN_STATE["tipo"] = tipo
        _LOGIN_STATE["saldo"] = round(saldo, 2)
        _log_scan(f"🔄 Conta trocada para {tipo} — Saldo: R${saldo:.2f}")
        _emit_status("trocar_conta")
        return jsonify({"ok": True, "saldo": round(saldo, 2), "tipo": tipo})
    except Exception as e:
        _log_scan(f"⚠️ Erro ao trocar conta: {e}")
        return jsonify({"ok": False, "msg": str(e)}), 500

@app.route('/api/noticias', methods=['GET'])
def api_noticias():
    gerenciador_noticias.atualizar_lista_fake()
    status = gerenciador_noticias.get_status()
    return jsonify({
        "ok": True,
        "noticias": status
    })

@app.route('/api/ia_status', methods=['GET'])
def api_ia_status():
    estados_info = {}
    for estado, hist in _historico_ia.items():
        confianca = sum(hist) / len(hist) if hist else 0.0
        acertos = sum(1 for h in hist if h == 1)
        estados_info[str(estado)] = {
            "confianca": round(confianca, 4),
            "total": len(hist),
            "acertos": acertos,
            "erros": len(hist) - acertos,
        }
    return jsonify({
        "ok": True,
        "estados_monitorados": len(_historico_ia),
        "pesos_ativos": len(_pesos_ia),
        "janela_ia": _JANELA_IA,
        "estados": estados_info,
        "pesos": {str(k): v for k, v in _pesos_ia.items()},
    })

def _ttz_realtime_updater():
    """Mantém o calendário TTZ atualizado e transmite a contagem ao frontend."""
    ultimo_emit = 0.0
    while True:
        time.sleep(1)
        if not STATE.get("ttz_ativo"):
            continue
        try:
            _ttz_refresh()
            agora = time.time()
            if agora - ultimo_emit >= 1.0:
                _emit_status("TTZ tempo real")
                ultimo_emit = agora
        except Exception as exc:
            STATE["ttz_error"] = f"Atualizador TTZ interrompido: {exc.__class__.__name__}"


def _ttz_browser_bridge_loop():
    """Opcionalmente lê o token pela aba TTZ autenticada via CDP local."""
    try:
        from ttz_browser_bridge import read_market_token, send_token
    except Exception as exc:
        STATE["ttz_error"] = f"Ponte TTZ indisponível: {exc.__class__.__name__}"
        return
    intervalo = max(30, int(os.getenv("TTZ_BRIDGE_REFRESH_SECONDS", "60")))
    while True:
        try:
            token = read_market_token()
            send_token(token)
        except Exception as exc:
            if STATE.get("ttz_ativo"):
                STATE["ttz_error"] = f"Ponte TTZ aguardando dashboard: {exc}"
        time.sleep(intervalo)


if __name__ == '__main__':
    threading.Thread(target=_ttz_realtime_updater, name="ttz-realtime", daemon=True).start()
    if os.getenv("TTZ_BROWSER_BRIDGE_AUTOSTART", "0") == "1":
        threading.Thread(target=_ttz_browser_bridge_loop, name="ttz-browser-bridge", daemon=True).start()
    print("🚀 Meu Script — Lua Quadcode")
    print(f"📋 Servidor rodando em http://0.0.0.0:5000")
    print(f"📋 Fonte de sinais: script Lua Quadcode autorizado")
    print(f"📋 Estratégias internas desativadas; somente script manual")
    print(f"📋 TF: M1 / M5 / M15 | Mercados: Forex + Forex OTC")
    socketio.run(app, host='0.0.0.0', port=int(os.environ.get('PORT') or os.environ.get('SERVER_PORT') or '5000'), debug=False, allow_unsafe_werkzeug=True)
