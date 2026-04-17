"""
Solver V2 — Affectation agents opérations police.
Flask + OR-Tools CP-SAT

═══════════════════════════════════════════════════════════════
CONTRAINTES DURES (H) — violation = solution refusée
═══════════════════════════════════════════════════════════════
H1  Présence agent pour la demi-journée demandée
H2  Postes interdits par agent (global ou par demi-journée)
H3  Incompatibilités entre agents sur un même poste
H4  Accueil : habilitation requise + volontaires (heures sup) exclus
H5  Suiveuse / Terrain : volontaires (heures sup) bloqués
H6  Chaque slot nommé rempli exactement une fois
H7  Chaque agent affecté à au plus un slot
H8  Équipe forcée pour LAPI1 / LAPI2 / Suiveuse (mode choix)

═══════════════════════════════════════════════════════════════
CONTRAINTES SOUPLES (S) — objectif à maximiser via scoring
═══════════════════════════════════════════════════════════════
S1  Équité automatique : déficit par groupe vs cibles auto-ajustées
    (LAPI 35%, Back-office 35%, Suiveuse 15%, Terrain 15%)
S2  Anti-répétition : pénalité si même groupe que les N dernières sessions
    (fenêtre glissante configurable, pas de cap LAPI fixe)
S3  Priorité volontaires : heures sup fortement orientés LAPI, puis Back-office
    (quota calculé dynamiquement selon le nb de volontaires)
S4  Rotation binômes Terrain : pénalité graduée sur les paires récentes
S5  AvoidAffectations : pénalité si répétition exacte d'un tirage rejeté
S6  Soulagement Terrain : favoriser autres postes pour agents surchargés Terrain
S7  Compensation Accueil↔LAPI : boost LAPI pour agent ayant fait Accueil récemment
S8  Exploration nouveaux agents : bonus pour postes jamais tentés
S9  Scarcité : bonus sur postes avec peu de candidats (évite les impasses)
S10 Répétition immédiate : pénalité quasi-dure si même poste que session précédente

═══════════════════════════════════════════════════════════════
ALLOCATION SECTEURS
═══════════════════════════════════════════════════════════════
  - Tri par couverture cumulée ascendante (secteurs les moins couverts en priorité)
  - LAPI1 et LAPI2 : ensembles disjoints obligatoires
  - Respect des cardinalités requises (requiredSectorsLAPI1 / LAPI2)
"""

import os
import random
import unicodedata
from collections import defaultdict
from itertools import combinations as _iter_comb, groupby as _groupby
from typing import Any, Dict, List, Optional, Set, Tuple

from flask import Flask, jsonify, request
from ortools.sat.python import cp_model


app = Flask(__name__)


# ─────────────────────────────────────────────────────────────────────────────
# CONFIGURATION MÉTIER
# ─────────────────────────────────────────────────────────────────────────────

class C:
    # Fenêtres historique
    REPEAT_WINDOW = 3          # Sessions récentes pour pénalité anti-répétition
    BINOME_WINDOW = 6          # Sessions récentes pour rotation binômes Terrain
    HISTORY_DEPTH = 10         # Profondeur totale chargée pour compteurs récents
    EQUITY_WINDOW_DAYS = 30    # Fenêtre glissante pour équité (jours)

    # Cibles d'équité par groupe (S1) — auto-ajustées selon la session
    EQUITY_TARGETS: Dict[str, float] = {
        "LAPI": 0.35,
        "Back-office": 0.35,
        "Suiveuse": 0.15,
        "Terrain": 0.15,
    }
    EQUITY_ALPHA = 0.6         # 60% cible fixe + 40% moyenne observée dans l'historique

    # Délimitation des postes nommés
    POSTES_NAMED = ["LAPI1", "LAPI2", "Accueil", "Suiveuse", "Back-office"]
    LAPI_SET: Set[str] = {"LAPI1", "LAPI2"}

    # Cardinalités secteurs par défaut
    DEFAULT_SECTORS_LAPI = 4

    # Solveur
    SOLVER_TIME_SECONDS = 15
    SOLVER_WORKERS = 4

    # ── Scores (entiers, CP-SAT Maximize) ────────────────────────────────────
    # S1  Équité / déficit
    SC_DEFICIT_MULT = 2_600_000     # par unité de déficit
    SC_DEFICIT_CAP = 780_000        # plafond bonus déficit
    SC_PRIORITY_BONUS = 320_000     # poste = groupe prioritaire de l'agent

    # S2  Anti-répétition (même groupe de poste sur les sessions récentes)
    SC_REPEAT_LAST = 160_000        # même groupe que la session N-1
    SC_REPEAT_STREAK2 = 260_000     # 2 sessions consécutives identiques
    SC_REPEAT_STREAK3 = 180_000     # 3 sessions consécutives identiques
    SC_REPEAT_DECAY = 90_000        # pénalité décroissante pour sessions plus anciennes

    # S3  Volontaires (heures sup)
    SC_VOL_LAPI_BONUS = 5_000_000   # très fort pour orienter vers LAPI
    SC_VOL_BO_BONUS = 1_000_000     # moyen pour orienter vers Back-office

    # S5  AvoidAffectations
    SC_AVOID = 1_200_000

    # S6  Soulagement Terrain
    SC_TERRAIN_RELIEF_MULT = 280_000

    # S7  Compensation Accueil→LAPI
    SC_ACCUEIL_LAPI_BOOST_1 = 600_000   # Accueil à N-1
    SC_ACCUEIL_LAPI_BOOST_2 = 250_000   # Accueil à N-2

    # S8  Exploration nouveaux agents
    SC_EXPLORATION_BONUS = 50_000

    # S9  Scarcité
    SC_SCARCITY = 2_200_000         # divisé par nb candidats éligibles

    # S10 Répétition immédiate (même poste que session précédente)
    SC_IMMEDIATE_REPEAT = 50_000_000  # quasi-dure


# ─────────────────────────────────────────────────────────────────────────────
# NORMALISATIONS
# ─────────────────────────────────────────────────────────────────────────────

def nrm(value: Any) -> str:
    return unicodedata.normalize("NFD", str(value or "")).encode("ascii", "ignore").decode("ascii").strip().lower()


def nrm_demi(value: Any) -> str:
    t = nrm(value)
    if "matin" in t:
        return "Matin"
    if "apres" in t:
        return "Après-midi"
    if "jour" in t:
        return "Journée"
    return str(value or "").strip()


def nrm_poste(value: Any) -> str:
    t = nrm(value)
    if not t:
        return ""
    if t == "lapi":
        return "LAPI"
    if t in {"lapi1", "lapi 1"}:
        return "LAPI1"
    if t in {"lapi2", "lapi 2"}:
        return "LAPI2"
    if "accueil" in t:
        return "Accueil"
    if "suiveuse" in t or "suiv" in t:
        return "Suiveuse"
    if "back" in t:
        return "Back-office"
    if "terrain" in t:
        return "Terrain"
    return str(value or "").strip()


def nrm_bool(value: Any) -> bool:
    if value in (True, 1):
        return True
    if value in (False, 0, "", None):
        return False
    if isinstance(value, (int, float)):
        return value != 0
    t = nrm(value)
    if not t:
        return False
    if any(s in str(value) for s in ["✔", "✅", "☑", "✓"]):
        return True
    if any(s in str(value) for s in ["❌", "✖", "✗"]):
        return False
    return t in {"true", "vrai", "oui", "yes", "1", "x"}


def to_int(value: Any, default: int = 0) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def poste_group(poste: str) -> str:
    return "LAPI" if poste in C.LAPI_SET else poste


def nrm_team(value: Any) -> str:
    """Normalise un nom d’équipe : '\u00c9quipe 1' → '1', 'A' → 'a'."""
    s = str(value or "").strip()
    parts = s.split()
    return parts[-1].lower() if parts else ""


# ─────────────────────────────────────────────────────────────────────────────
# PARSING DU PAYLOAD
# ─────────────────────────────────────────────────────────────────────────────

def parse_agents(payload: dict) -> List[dict]:
    """H1 — Filtre les agents présents pour la demi-journée."""
    demi = nrm_demi((payload or {}).get("demiJournee"))
    result = []
    for raw in ((payload or {}).get("workbook") or {}).get("agents") or []:
        nom = str((raw or {}).get("nom") or "").strip()
        if not nom:
            continue
        if demi == "Matin":
            present = nrm_bool(raw.get("presentMatin"))
            hs = nrm_bool(raw.get("heuresSupMatin"))
        elif demi == "Après-midi":
            present = nrm_bool(raw.get("presentApresMidi"))
            hs = nrm_bool(raw.get("heuresSupApresMidi"))
        elif demi == "Journée":
            present = nrm_bool(raw.get("presentMatin")) and nrm_bool(raw.get("presentApresMidi"))
            hs = nrm_bool(raw.get("heuresSupMatin")) or nrm_bool(raw.get("heuresSupApresMidi"))
        else:
            present = nrm_bool(raw.get("presentMatin")) or nrm_bool(raw.get("presentApresMidi"))
            hs = nrm_bool(raw.get("heuresSupMatin")) or nrm_bool(raw.get("heuresSupApresMidi"))
        if not present:
            continue
        result.append({
            "nom": nom,
            "key": nrm(nom),
            "equipe": str((raw or {}).get("equipe") or "").strip(),
            "heures_sup": hs,
            "accueil_hab": nrm_bool((raw or {}).get("accueil")),
        })
    return result


def parse_counts(payload: dict) -> Dict[str, int]:
    params = ((payload or {}).get("workbook") or {}).get("parametres") or {}
    return {
        "LAPI1": to_int(params.get("LAPI 1"), 2),
        "LAPI2": to_int(params.get("LAPI 2"), 2),
        "Accueil": to_int(params.get("Accueil"), 2),
        "Suiveuse": to_int(params.get("Suiveuse"), 1),
        "Back-office": to_int(params.get("Back-office"), 1),
    }


def parse_restrictions(payload: dict) -> Tuple[str, Dict[str, List[dict]]]:
    """H2 — Postes interdits par agent."""
    demi = nrm_demi((payload or {}).get("demiJournee"))
    result: Dict[str, List[dict]] = defaultdict(list)
    for row in ((payload or {}).get("workbook") or {}).get("postesInterdits") or []:
        agent_key = nrm((row or {}).get("agent"))
        poste = nrm_poste((row or {}).get("poste"))
        row_demi = nrm_demi((row or {}).get("demiJournee"))
        if not agent_key or not poste:
            continue
        result[agent_key].append({"poste": poste, "demi": row_demi})
    return demi, dict(result)


def parse_incompatibilities(payload: dict) -> List[dict]:
    """H3 — Incompatibilités entre agents."""
    result = []
    for row in ((payload or {}).get("workbook") or {}).get("incompatibilites") or []:
        a1 = nrm((row or {}).get("agent1"))
        a2 = nrm((row or {}).get("agent2"))
        poste = nrm_poste((row or {}).get("poste"))
        if not a1 or not a2:
            continue
        result.append({"a1": a1, "a2": a2, "poste": poste})
    return result


def parse_history(payload: dict) -> dict:
    """
    Construit tous les contextes historiques nécessaires au scoring :
    - counts          : {agent_key: {group: int}}           (total sessions)
    - presence        : {agent_key: int}
    - recent_postes   : {agent_key: [poste, ...]}           (HISTORY_DEPTH, plus récent en tête)
    - recent_binomes  : {agent_key: [partner_key, ...]}     (BINOME_WINDOW, dédupliqué)
    - sector_coverage : {sector: {"LAPI1": int, "LAPI2": int}}
    - last_session    : {agent_key: poste}                  (session précédente uniquement)
    - avoid_map       : {agent_key: set(group)}             (depuis avoidAffectations)
    """
    rows = ((payload or {}).get("workbook") or {}).get("historique") or []

    counts: Dict[str, Dict[str, int]] = defaultdict(lambda: defaultdict(int))
    presence: Dict[str, int] = defaultdict(int)
    recent_postes_raw: Dict[str, List[str]] = defaultdict(list)
    recent_binomes_raw: Dict[str, List[str]] = defaultdict(list)
    sector_coverage: Dict[str, Dict[str, int]] = defaultdict(lambda: defaultdict(int))

    for row in rows:
        agent_field = str((row or {}).get("agent") or "").strip()
        poste = nrm_poste((row or {}).get("poste"))
        secteur_field = str((row or {}).get("secteur") or "").strip()
        if not agent_field or not poste or poste == "Non affecté":
            continue

        names = [p.strip() for p in agent_field.split("/") if p.strip()]
        group = poste_group(poste)

        for nom in names:
            key = nrm(nom)
            counts[key][group] += 1
            presence[key] += 1
            recent_postes_raw[key].append(poste)
            for partner in names:
                if partner != nom:
                    recent_binomes_raw[key].append(nrm(partner))

        for sec in [s.strip() for s in secteur_field.split("/") if s.strip()]:
            if poste in C.LAPI_SET:
                sector_coverage[sec][poste] += 1

    # recent_postes : les HISTORY_DEPTH derniers, plus récent en tête
    recent_postes = {k: list(reversed(v[-C.HISTORY_DEPTH:])) for k, v in recent_postes_raw.items()}

    # recent_binomes : dédupliqué, plus récent en tête, limité à BINOME_WINDOW
    recent_binomes: Dict[str, List[str]] = {}
    for key, raw in recent_binomes_raw.items():
        seen: List[str] = []
        for b in reversed(raw):
            if b not in seen:
                seen.append(b)
            if len(seen) >= C.BINOME_WINDOW:
                break
        recent_binomes[key] = seen

    # terrain_coverage : nb de fois où chaque secteur a été affecté en Terrain
    terrain_coverage: Dict[str, int] = defaultdict(int)
    for row in rows:
        p = nrm_poste((row or {}).get("poste"))
        if p != "Terrain":
            continue
        sec_field = str((row or {}).get("secteur") or "").strip()
        for sec in [s.strip() for s in sec_field.split("/") if s.strip()]:
            terrain_coverage[sec] += 1

    # last_session : affectation de la toute dernière session (date + demi)
    last_session: Dict[str, str] = {}
    last_session_sectors: Set[str] = set()  # secteurs LAPI de la dernière session
    if rows:
        last_row = rows[-1]
        last_date = (last_row or {}).get("date")
        last_demi = nrm_demi((last_row or {}).get("demiJournee"))
        for row in reversed(rows):
            if (row or {}).get("date") != last_date:
                break
            if nrm_demi((row or {}).get("demiJournee")) != last_demi:
                break
            af = str((row or {}).get("agent") or "").strip()
            p = nrm_poste((row or {}).get("poste"))
            if not af or not p:
                continue
            for nom in [x.strip() for x in af.split("/") if x.strip()]:
                last_session[nrm(nom)] = p
            # Collecter les secteurs LAPI de la dernière session
            if p in C.LAPI_SET:
                sec_field = str((row or {}).get("secteur") or "").strip()
                for sec in [s.strip() for s in sec_field.split("/") if s.strip()]:
                    last_session_sectors.add(sec)

    # avoid_map depuis avoidAffectations (tirage précédent rejeté)
    avoid_map: Dict[str, Set[str]] = defaultdict(set)
    avoid_terrain_binomes: Dict[str, List[str]] = defaultdict(list)
    for aff in ((payload or {}).get("options") or {}).get("avoidAffectations") or []:
        p = nrm_poste((aff or {}).get("poste"))
        group = poste_group(p)
        agents_in_aff = []
        for entry in (aff or {}).get("agents") or []:
            nom = str(entry[0] if isinstance(entry, list) else entry or "").strip()
            if nom:
                avoid_map[nrm(nom)].add(group)
                if group == "Terrain":
                    agents_in_aff.append(nrm(nom))
        # Injecter les binômes Terrain dans recent_binomes (position 0 = le plus récent)
        for i, ak in enumerate(agents_in_aff):
            for bk in agents_in_aff:
                if ak != bk and bk not in avoid_terrain_binomes[ak]:
                    avoid_terrain_binomes[ak].insert(0, bk)
        # Injecter les secteurs LAPI dans last_session_sectors pour pénaliser leur réutilisation
        if p in C.LAPI_SET:
            for sec in (aff or {}).get("secteurs") or []:
                if sec:
                    last_session_sectors.add(str(sec).strip())

    # Fusionner les binômes Terrain à éviter avec les binômes historiques
    merged_binomes = dict(recent_binomes)
    for ak, partners in avoid_terrain_binomes.items():
        merged_binomes[ak] = list(dict.fromkeys(partners + merged_binomes.get(ak, [])))
    recent_binomes = merged_binomes

    return {
        "counts": dict(counts),
        "presence": dict(presence),
        "recent_postes": recent_postes,
        "recent_binomes": recent_binomes,
        "sector_coverage": dict(sector_coverage),
        "terrain_coverage": dict(terrain_coverage),
        "last_session": last_session,
        "last_session_sectors": last_session_sectors,
        "avoid_map": dict(avoid_map),
    }


# ─────────────────────────────────────────────────────────────────────────────
# ÉQUITÉ — CIBLES AUTO-AJUSTÉES (S1)
# ─────────────────────────────────────────────────────────────────────────────

def compute_deficits(agents: List[dict], hist: dict, counts_by_slot: Dict[str, int]) -> Dict[str, dict]:
    """
    Pour chaque agent : calcule le déficit par groupe (cible - ratio observé).
    Cible = alpha × cible_fixe + (1 - alpha) × ratio_moyen_historique.
    Retourne {agent_key: {group: float, "_priority": group}}.
    """
    total_slots = sum(counts_by_slot.values())
    if total_slots == 0:
        return {}

    # Ratio de chaque groupe dans la session courante
    session_ratios: Dict[str, float] = {}
    lapi_slots = counts_by_slot.get("LAPI1", 0) + counts_by_slot.get("LAPI2", 0)
    session_total_named = (
        lapi_slots
        + counts_by_slot.get("Accueil", 0)
        + counts_by_slot.get("Suiveuse", 0)
        + counts_by_slot.get("Back-office", 0)
    )
    if session_total_named > 0:
        session_ratios["LAPI"] = lapi_slots / session_total_named
        session_ratios["Accueil"] = counts_by_slot.get("Accueil", 0) / session_total_named
        session_ratios["Suiveuse"] = counts_by_slot.get("Suiveuse", 0) / session_total_named
        session_ratios["Back-office"] = counts_by_slot.get("Back-office", 0) / session_total_named

    # Ratio moyen observé dans l'historique global
    all_counts: Dict[str, int] = defaultdict(int)
    for agent_counts in hist.get("counts", {}).values():
        for g, n in agent_counts.items():
            all_counts[g] += n
    total_hist = sum(all_counts.values()) or 1
    hist_avg: Dict[str, float] = {g: n / total_hist for g, n in all_counts.items()}

    active_groups = list(C.EQUITY_TARGETS.keys())

    deficits: Dict[str, dict] = {}
    h_counts = hist.get("counts", {})
    h_presence = hist.get("presence", {})

    for agent in agents:
        key = agent["key"]
        pres = max(1, h_presence.get(key, 0))
        agent_counts = h_counts.get(key, {})
        is_new = pres <= 3

        deficit: Dict[str, Any] = {}
        for group in active_groups:
            fixed_target = C.EQUITY_TARGETS.get(group, session_ratios.get(group, 0.0))
            observed_avg = hist_avg.get(group, fixed_target)
            blended_target = C.EQUITY_ALPHA * fixed_target + (1.0 - C.EQUITY_ALPHA) * observed_avg
            actual = agent_counts.get(group, 0) / pres
            deficit[group] = blended_target - actual

        if deficit:
            deficit["_priority"] = max(
                (g for g in deficit if not g.startswith("_")),
                key=lambda g: deficit[g]
            )
        deficit["_is_new"] = is_new
        deficits[key] = deficit

    return deficits


# ─────────────────────────────────────────────────────────────────────────────
# QUOTA VOLONTAIRES (S3)
# ─────────────────────────────────────────────────────────────────────────────

def compute_volunteer_targets(agents: List[dict], counts: Dict[str, int]) -> dict:
    """
    Calcule combien de volontaires (heures sup) peuvent aller sur LAPI1 / LAPI2.
    Règle : ≤2 → tous ; 3 → max 2 ; ≥4 → max 4 (plafonné aux slots disponibles).
    """
    volunteers = [a for a in agents if a["heures_sup"]]
    n = len(volunteers)
    if n == 0:
        return {"lapi1": 0, "lapi2": 0, "allow_lapi1": False, "allow_lapi2": False, "keys": set()}

    quota = n if n <= 2 else (2 if n == 3 else min(4, n))
    nb1 = counts.get("LAPI1", 0)
    nb2 = counts.get("LAPI2", 0)
    target = min(quota, nb1 + nb2)
    t1 = min(nb1, target)
    t2 = min(nb2, max(0, target - t1))

    return {
        "lapi1": t1,
        "lapi2": t2,
        "allow_lapi1": t1 > 0,
        "allow_lapi2": t2 > 0,
        "keys": {a["key"] for a in volunteers},
    }


# ─────────────────────────────────────────────────────────────────────────────
# ÉLIGIBILITÉ DURE (H2–H8)
# ─────────────────────────────────────────────────────────────────────────────

def is_forbidden(key: str, poste: str, demi: str, restrictions: dict) -> bool:
    for item in restrictions.get(key, []):
        if item["demi"] and item["demi"] != demi:
            continue
        rp = item["poste"]
        if rp == "LAPI" and poste in C.LAPI_SET:
            return True
        if rp == poste:
            return True
    return False


def is_hard_eligible(agent: dict, poste: str, demi: str, restrictions: dict) -> bool:
    """Vérifie les contraintes H2–H5."""
    key = agent["key"]
    if is_forbidden(key, poste, demi, restrictions):
        return False
    if poste == "Accueil":
        if not agent.get("accueil_hab"):
            return False
        if agent.get("heures_sup"):
            return False
    if poste in ("Suiveuse", "Terrain") and agent.get("heures_sup"):
        return False
    return True


def is_slot_eligible(agent: dict, slot: dict, demi: str, restrictions: dict, vol_targets: dict) -> bool:
    """Éligibilité complète pour un slot nommé (H2–H8)."""
    poste = slot["poste"]
    if not is_hard_eligible(agent, poste, demi, restrictions):
        return False
    # H8 : équipe forcée
    req_team = slot.get("required_team")
    if req_team and nrm_team(agent.get("equipe")) != nrm_team(req_team):
        return False
    # S3 : volontaires bloqués sur LAPI si quota = 0
    if agent["heures_sup"]:
        if poste == "LAPI1" and not vol_targets.get("allow_lapi1"):
            return False
        if poste == "LAPI2" and not vol_targets.get("allow_lapi2"):
            return False
    return True


# ─────────────────────────────────────────────────────────────────────────────
# SCORING (S1–S10)
# ─────────────────────────────────────────────────────────────────────────────

def score_agent_slot(
    agent: dict,
    slot: dict,
    hist: dict,
    deficits: dict,
    demi: str,
    vol_targets: dict,
    eligible_count: int,
) -> int:
    key = agent["key"]
    poste = slot["poste"]
    group = poste_group(poste)
    is_vol = agent["heures_sup"]
    last_session = hist.get("last_session", {})
    avoid_map = hist.get("avoid_map", {})
    recent = hist.get("recent_postes", {}).get(key, [])
    recent_groups = [poste_group(p) for p in recent]

    score = 0

    # ── S1 : Équité / déficit ─────────────────────────────────────────────────
    d = deficits.get(key, {})
    def_val = d.get(group, 0.0)
    raw_bonus = int(def_val * C.SC_DEFICIT_MULT)
    score += max(-C.SC_DEFICIT_CAP, min(C.SC_DEFICIT_CAP, raw_bonus))
    if group == d.get("_priority"):
        score += C.SC_PRIORITY_BONUS

    # ── S2 : Anti-répétition (préservée pour volontaires sur LAPI/BO) ─────────
    preserve_vol = is_vol and (poste in C.LAPI_SET or poste == "Back-office")
    if not preserve_vol:
        streak = 0
        for g in recent_groups:
            if g != group:
                break
            streak += 1
        if recent_groups and recent_groups[0] == group:
            score -= C.SC_REPEAT_LAST
        if streak >= 2:
            score -= C.SC_REPEAT_STREAK2
        if streak >= 3:
            score -= C.SC_REPEAT_STREAK3
        for i in range(1, min(len(recent_groups), C.REPEAT_WINDOW + 1)):
            if recent_groups[i] == group:
                score -= max(30_000, C.SC_REPEAT_DECAY - i * 20_000)

    # ── S3 : Priorité volontaires ─────────────────────────────────────────────
    if is_vol:
        if poste in C.LAPI_SET:
            score += C.SC_VOL_LAPI_BONUS
        elif poste == "Back-office":
            score += C.SC_VOL_BO_BONUS

    # ── S5 : AvoidAffectations ────────────────────────────────────────────────
    if group in avoid_map.get(key, set()):
        score -= C.SC_AVOID

    # ── S6 : Soulagement Terrain ──────────────────────────────────────────────
    if poste != "Terrain":
        pres = max(1, hist.get("presence", {}).get(key, 0))
        terrain_ratio = hist.get("counts", {}).get(key, {}).get("Terrain", 0) / pres
        overload = max(0.0, terrain_ratio - 0.20)
        score += int(overload * C.SC_TERRAIN_RELIEF_MULT)

    # ── S7 : Compensation Accueil → LAPI ─────────────────────────────────────
    if poste in C.LAPI_SET and not is_vol:
        if recent and recent[0] == "Accueil":
            score += C.SC_ACCUEIL_LAPI_BOOST_1
        elif len(recent) > 1 and recent[1] == "Accueil":
            score += C.SC_ACCUEIL_LAPI_BOOST_2

    # ── S8 : Exploration nouveaux agents ─────────────────────────────────────
    if d.get("_is_new"):
        agent_all_counts = hist.get("counts", {}).get(key, {})
        if group not in agent_all_counts:
            score += C.SC_EXPLORATION_BONUS

    # ── S9 : Scarcité ────────────────────────────────────────────────────────
    if eligible_count > 0:
        score += C.SC_SCARCITY // eligible_count

    # ── S10 : Répétition immédiate ────────────────────────────────────────────
    if last_session.get(key) == poste:
        score -= C.SC_IMMEDIATE_REPEAT

    return score


# ─────────────────────────────────────────────────────────────────────────────
# CONSTRUCTION DES SLOTS
# ─────────────────────────────────────────────────────────────────────────────

def build_slots(counts: Dict[str, int], forced_teams: dict) -> List[dict]:
    ft = forced_teams or {}
    slots = []
    for poste in C.POSTES_NAMED:
        n = counts.get(poste, 0)
        req = None
        if poste == "LAPI1":
            req = str(ft.get("lapi1") or "").strip() or None
        elif poste == "LAPI2":
            req = str(ft.get("lapi2") or "").strip() or None
        elif poste == "Suiveuse":
            req = str(ft.get("suiveuse") or "").strip() or None
        for i in range(max(0, n)):
            slots.append({"id": f"{poste}#{i + 1}", "poste": poste, "required_team": req})
    return slots


# ─────────────────────────────────────────────────────────────────────────────
# SOLVEUR CP-SAT — POSTES NOMMÉS
# ─────────────────────────────────────────────────────────────────────────────

def solve_named(
    agents: List[dict],
    slots: List[dict],
    hist: dict,
    deficits: dict,
    demi: str,
    restrictions: dict,
    incompatibilities: List[dict],
    vol_targets: dict,
) -> Tuple[List[dict], List[dict]]:
    """
    Affecte les agents aux slots nommés via CP-SAT.
    Retourne (assignments [{poste, agent_nom}], remaining [agent]).
    """
    model = cp_model.CpModel()

    # Pré-calcul des candidats éligibles par slot
    eligible_per_slot: List[List[int]] = []
    for slot in slots:
        eligible = [
            ai for ai, ag in enumerate(agents)
            if is_slot_eligible(ag, slot, demi, restrictions, vol_targets)
        ]
        eligible_per_slot.append(eligible)

    # Variables booléennes x[agent_idx, slot_idx]
    variables: Dict[Tuple[int, int], Any] = {}
    for si, slot in enumerate(slots):
        for ai in eligible_per_slot[si]:
            variables[(ai, si)] = model.NewBoolVar(f"x_{ai}_{si}")

    # H6 : chaque slot rempli exactement une fois
    for si, slot in enumerate(slots):
        slot_vars = [variables[(ai, si)] for ai in eligible_per_slot[si] if (ai, si) in variables]
        if not slot_vars:
            reasons = []
            for ag in agents:
                poste = slot["poste"]
                r = []
                if is_forbidden(ag["key"], poste, demi, restrictions):
                    r.append("poste interdit")
                elif poste == "Accueil" and not ag.get("accueil_hab"):
                    r.append("non habilité Accueil")
                elif poste in ("Suiveuse", "Terrain") and ag.get("heures_sup"):
                    r.append("heures_sup→exclu Suiveuse/Terrain")
                elif slot.get("required_team") and nrm_team(ag.get("equipe")) != nrm_team(slot.get("required_team")):
                    r.append(f"équipe '{ag.get('equipe')}' ≠ '{slot.get('required_team')}' (nrm: '{nrm_team(ag.get('equipe'))}' ≠ '{nrm_team(slot.get('required_team'))}')")
                elif ag["heures_sup"] and poste == "LAPI1" and not vol_targets.get("allow_lapi1"):
                    r.append("heures_sup quota LAPI1=0")
                elif ag["heures_sup"] and poste == "LAPI2" and not vol_targets.get("allow_lapi2"):
                    r.append("heures_sup quota LAPI2=0")
                else:
                    r.append("raison inconnue")
                reasons.append(f"{ag['nom']}: {r[0]}")
            detail = " | ".join(reasons[:15])
            raise ValueError(
                f"Aucun agent éligible pour '{slot['poste']}' (slot {slot['id']}). "
                f"Détail: {detail}"
            )
        model.Add(sum(slot_vars) == 1)

    # H7 : chaque agent utilisé au plus une fois
    for ai in range(len(agents)):
        agent_vars = [variables[(ai, si)] for si in range(len(slots)) if (ai, si) in variables]
        if agent_vars:
            model.Add(sum(agent_vars) <= 1)

    # H3 : incompatibilités
    agent_index = {ag["key"]: ai for ai, ag in enumerate(agents)}
    for row in incompatibilities:
        a1 = agent_index.get(row["a1"])
        a2 = agent_index.get(row["a2"])
        if a1 is None or a2 is None:
            continue
        check_postes = list(C.LAPI_SET) if row["poste"] == "LAPI" else (
            [row["poste"]] if row["poste"] in C.POSTES_NAMED else C.POSTES_NAMED
        )
        for poste in check_postes:
            for si, slot in enumerate(slots):
                if slot["poste"] != poste:
                    continue
                v1 = variables.get((a1, si))
                v2 = variables.get((a2, si))
                if v1 is not None and v2 is not None:
                    model.Add(v1 + v2 <= 1)

    # S3 : quota global volontaires par poste LAPI
    vol_keys = vol_targets.get("keys", set())
    for poste, cap in [("LAPI1", vol_targets.get("lapi1", 0)), ("LAPI2", vol_targets.get("lapi2", 0))]:
        all_vol_vars = [
            variables[(ai, si)]
            for si, slot in enumerate(slots)
            if slot["poste"] == poste
            for ai in eligible_per_slot[si]
            if (ai, si) in variables and agents[ai]["key"] in vol_keys
        ]
        if all_vol_vars:
            model.Add(sum(all_vol_vars) <= max(1, cap))

    # Objectif : maximiser le score total
    objective_terms = []
    for si, slot in enumerate(slots):
        ec = len(eligible_per_slot[si])
        for ai in eligible_per_slot[si]:
            if (ai, si) not in variables:
                continue
            s = score_agent_slot(agents[ai], slot, hist, deficits, demi, vol_targets, ec)
            objective_terms.append(s * variables[(ai, si)])

    if objective_terms:
        model.Maximize(sum(objective_terms))

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = C.SOLVER_TIME_SECONDS
    solver.parameters.num_search_workers = C.SOLVER_WORKERS
    status = solver.Solve(model)

    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        raise ValueError(
            "Aucune solution faisable trouvée. "
            "Vérifiez les présences, postes interdits et incompatibilités."
        )

    assignments = []
    used: Set[str] = set()
    for si, slot in enumerate(slots):
        for ai in eligible_per_slot[si]:
            var = variables.get((ai, si))
            if var is not None and solver.Value(var) == 1:
                assignments.append({"poste": slot["poste"], "agent_nom": agents[ai]["nom"]})
                used.add(agents[ai]["key"])
                break

    remaining = [ag for ag in agents if ag["key"] not in used]
    return assignments, remaining


# ─────────────────────────────────────────────────────────────────────────────
# CONSTITUTION DES ÉQUIPES TERRAIN (S4 — rotation binômes)
# ─────────────────────────────────────────────────────────────────────────────

def are_terrain_incompatible(a: dict, b: dict, incompatibilities: List[dict]) -> bool:
    ak, bk = a["key"], b["key"]
    for row in incompatibilities:
        if {ak, bk} != {row["a1"], row["a2"]}:
            continue
        if not row["poste"] or row["poste"] in ("Terrain", ""):
            return True
    return False


def terrain_pair_score(a: dict, b: dict, hist: dict) -> int:
    """Score bas = meilleure paire."""
    ak, bk = a["key"], b["key"]
    rb_a = hist.get("recent_binomes", {}).get(ak, [])
    rb_b = hist.get("recent_binomes", {}).get(bk, [])
    idx_ab = rb_a.index(bk) if bk in rb_a else -1
    idx_ba = rb_b.index(ak) if ak in rb_b else -1
    candidates = [i for i in [idx_ab, idx_ba] if i >= 0]
    best = min(candidates) if candidates else -1

    s = 0
    if best >= 0:
        s += max(125, 500 - best * 150)
    if a.get("equipe") != b.get("equipe"):
        s += 100
    return s


def build_terrain_groups(remaining: List[dict], incompatibilities: List[dict], hist: dict) -> List[dict]:
    groups = []
    queue = list(remaining)

    while len(queue) >= 2:
        first = queue.pop(0)
        best_idx, best_sc = None, float("inf")
        for idx, cand in enumerate(queue):
            if are_terrain_incompatible(first, cand, incompatibilities):
                continue
            sc = terrain_pair_score(first, cand, hist)
            if sc < best_sc:
                best_sc = sc
                best_idx = idx
        if best_idx is None:
            groups.append({"poste": "Terrain", "agents": [first["nom"]], "secteurs": []})
            continue
        second = queue.pop(best_idx)
        groups.append({"poste": "Terrain", "agents": [first["nom"], second["nom"]], "secteurs": []})

    if queue:
        lone = queue[0]
        # Tenter d'adjoindre au dernier groupe si compatible
        if groups and not any(
            are_terrain_incompatible(lone, {"key": nrm(m), "nom": m}, incompatibilities)
            for m in groups[-1]["agents"]
        ):
            groups[-1]["agents"].append(lone["nom"])
        else:
            groups.append({"poste": "Terrain", "agents": [lone["nom"]], "secteurs": []})

    return groups


# ─────────────────────────────────────────────────────────────────────────────
# ALLOCATION DES SECTEURS — géographie LAPI + équité Terrain
# ─────────────────────────────────────────────────────────────────────────────

_AXES = [
    ({"NE", "NO"}, {"SE", "SO"}),  # axe Nord / Sud
    ({"NE", "SE"}, {"NO", "SO"}),  # axe Est / Ouest
]


def _axis_opposed(g1: List[str], g2: List[str], zone_map: Dict[str, str]) -> bool:
    z1 = {zone_map[s] for s in g1 if zone_map.get(s)}
    z2 = {zone_map[s] for s in g2 if zone_map.get(s)}
    for side1, side2 in _AXES:
        if z1 <= side1 and z2 <= side2:
            return True
        if z1 <= side2 and z2 <= side1:
            return True
    return False


def _partition_geographic(
    pool: List[str], zone_map: Dict[str, str], req1: int, req2: int
) -> Tuple[List[str], List[str]]:
    """
    Partitionne `pool` en deux groupes (req1, req2) en cherchant :
      1. Split parfait par axe géographique
      2. Recherche exhaustive C(n, req1) si n ≤ 14
      3. Fallback glouton
    Score : (nb_dépassements_≤2zones, total_zones, 0_si_axes_opposés)
    """
    n = len(pool)
    needed = req1 + req2
    if n < needed:
        return pool[:req1], pool[req1:req1 + req2]

    # 1. Essai rapide par axe
    for side1, side2 in _AXES:
        g1 = [s for s in pool if zone_map.get(s) in side1]
        g2 = [s for s in pool if zone_map.get(s) in side2]
        if len(g1) == req1 and len(g2) == req2:
            return g1, g2
        if len(g1) == req2 and len(g2) == req1:
            return g2, g1

    # 2. Recherche exhaustive (pool ≤ 14 secteurs → au plus C(14,4)=1001)
    if n <= 14:
        best: Optional[Tuple[List[str], List[str]]] = None
        best_key: Optional[tuple] = None
        pool_set = set(pool)
        for combo in _iter_comb(pool, req1):
            g1 = list(combo)
            g2 = [s for s in pool if s not in set(g1)]
            if len(g2) != req2:
                continue
            z1 = {zone_map[s] for s in g1 if zone_map.get(s)}
            z2 = {zone_map[s] for s in g2 if zone_map.get(s)}
            over = max(0, len(z1) - 2) + max(0, len(z2) - 2)
            opp = 0 if _axis_opposed(g1, g2, zone_map) else 1
            key = (over, len(z1) + len(z2), opp)
            if best_key is None or key < best_key:
                best_key = key
                best = (g1, g2)
        if best:
            return best

    # 3. Fallback glouton : remplir g1 depuis les zones les plus représentées
    by_zone: Dict[str, List[str]] = defaultdict(list)
    for s in pool:
        by_zone[zone_map.get(s, "")].append(s)
    zones_sorted = sorted(by_zone.keys(), key=lambda z: -len(by_zone[z]))
    g1: List[str] = []
    for z in zones_sorted:
        for s in by_zone[z]:
            if len(g1) < req1:
                g1.append(s)
    g1_set = set(g1)
    g2 = [s for s in pool if s not in g1_set][:req2]
    return g1, g2


def allocate_sectors(affectations: List[dict], payload: dict, hist: dict, attempt: int = 0) -> None:
    workbook = (payload or {}).get("workbook") or {}
    options = (payload or {}).get("options") or {}

    raw_secteurs = workbook.get("secteurs") or []
    all_sectors: List[str] = []
    zone_map: Dict[str, str] = {}
    for item in raw_secteurs:
        sec = str((item or {}).get("secteur") or "").strip()
        zone = str((item or {}).get("zone") or "").strip().upper()
        if sec:
            all_sectors.append(sec)
            if zone:
                zone_map[sec] = zone

    if not all_sectors:
        return

    req1 = to_int(options.get("requiredSectorsLAPI1"), C.DEFAULT_SECTORS_LAPI)
    req2 = to_int(options.get("requiredSectorsLAPI2"), C.DEFAULT_SECTORS_LAPI)

    lapi_cov = hist.get("sector_coverage", {})
    terrain_cov = hist.get("terrain_coverage", {})
    recent_lapi_secs = hist.get("last_session_sectors", set())

    rng = random.Random(attempt) if attempt > 0 else None

    def jittered_sort(sectors: List[str], key_fn) -> List[str]:
        base = sorted(sectors, key=key_fn)
        if rng is None:
            return base
        result: List[str] = []
        for _, grp in _groupby(base, key=key_fn):
            g = list(grp)
            rng.shuffle(g)
            result.extend(g)
        return result

    def lapi_sort_key(s: str) -> tuple:
        total = lapi_cov.get(s, {}).get("LAPI1", 0) + lapi_cov.get(s, {}).get("LAPI2", 0)
        return (total, 1 if s in recent_lapi_secs else 0)

    lapi1 = next((a for a in affectations if a["poste"] == "LAPI1"), None)
    lapi2 = next((a for a in affectations if a["poste"] == "LAPI2"), None)
    used: Set[str] = set()

    # ── LAPI : équité + partition géographique ────────────────────────────────
    if lapi1 or lapi2:
        lapi_sorted = jittered_sort(all_sectors, lapi_sort_key)
        if lapi1 and lapi2:
            needed = req1 + req2
            if len(lapi_sorted) < needed:
                raise ValueError(
                    f"Pas assez de secteurs : {len(lapi_sorted)} disponibles, {needed} requis."
                )
            pool = lapi_sorted[:needed]
            g1, g2 = _partition_geographic(pool, zone_map, req1, req2)
            lapi1["secteurs"] = g1
            lapi2["secteurs"] = g2
            used.update(g1 + g2)
        elif lapi1:
            lapi1["secteurs"] = lapi_sorted[:req1]
            used.update(lapi1["secteurs"])
        else:
            lapi2["secteurs"] = lapi_sorted[:req2]
            used.update(lapi2["secteurs"])

    # ── Terrain : équité couverture, secteurs les moins vus en priorité ───────
    terrain_pool = [s for s in all_sectors if s not in used] or list(all_sectors)
    terrain_sorted = jittered_sort(terrain_pool, lambda s: (terrain_cov.get(s, 0), s))

    terrain_items = [a for a in affectations if a["poste"] == "Terrain"]
    for idx, item in enumerate(terrain_items):
        item["secteurs"] = [terrain_sorted[idx % len(terrain_sorted)]] if terrain_sorted else []


# ─────────────────────────────────────────────────────────────────────────────
# AVERTISSEMENTS
# ─────────────────────────────────────────────────────────────────────────────

def collect_warnings(affectations: List[dict], hist: dict) -> List[str]:
    warnings = []
    last_session = hist.get("last_session", {})

    lapi1 = next((a for a in affectations if a["poste"] == "LAPI1"), None)
    lapi2 = next((a for a in affectations if a["poste"] == "LAPI2"), None)
    if lapi1 and lapi2:
        overlaps = [s for s in lapi1.get("secteurs", []) if s in lapi2.get("secteurs", [])]
        if overlaps:
            warnings.append(f"⚠️ Doublons secteurs LAPI : {', '.join(overlaps)}")

    for aff in affectations:
        for nom in aff.get("agents") or []:
            if last_session.get(nrm(nom)) == aff["poste"]:
                warnings.append(
                    f"ℹ️ {nom} répète '{aff['poste']}' (même poste que la session précédente)"
                )

    return warnings


# ─────────────────────────────────────────────────────────────────────────────
# POINT D'ENTRÉE PRINCIPAL
# ─────────────────────────────────────────────────────────────────────────────

def build_result(payload: dict) -> dict:
    demi = nrm_demi((payload or {}).get("demiJournee"))
    forced_teams = (payload or {}).get("forcedTeams") or {}

    # Parsing
    agents = parse_agents(payload)
    if len(agents) < 2:
        raise ValueError("Pas assez d'agents présents (minimum 2).")

    counts = parse_counts(payload)
    slots = build_slots(counts, forced_teams)

    if len(slots) > len(agents):
        raise ValueError(
            f"Pas assez d'agents présents ({len(agents)}) "
            f"pour couvrir les {len(slots)} postes demandés."
        )

    demi_ctx, restrictions = parse_restrictions(payload)
    if not demi:
        demi = demi_ctx

    incompatibilities = parse_incompatibilities(payload)
    hist = parse_history(payload)
    deficits = compute_deficits(agents, hist, counts)
    vol_targets = compute_volunteer_targets(agents, counts)

    # Résolution postes nommés
    assignments, remaining = solve_named(
        agents, slots, hist, deficits, demi, restrictions, incompatibilities, vol_targets
    )

    # Construction des affectations nommées
    grouped: Dict[str, List[str]] = defaultdict(list)
    for row in assignments:
        grouped[row["poste"]].append(row["agent_nom"])

    affectations: List[dict] = []
    for poste in C.POSTES_NAMED:
        if grouped.get(poste):
            affectations.append({"poste": poste, "agents": grouped[poste], "secteurs": []})

    # Équipes Terrain
    terrain_groups = build_terrain_groups(remaining, incompatibilities, hist)
    affectations.extend(terrain_groups)

    # Allocation des secteurs
    allocate_sectors(affectations, payload, hist, attempt=int((payload.get("options") or {}).get("sectorAttempt") or 0))

    # Avertissements
    warnings = collect_warnings(affectations, hist)

    return {
        "date": (payload or {}).get("date"),
        "demiJournee": demi,
        "affectations": affectations,
        "warnings": warnings,
        "meta": {
            "agentsInput": len(agents),
            "slotsNamed": len(slots),
            "terrainGroups": len(terrain_groups),
            "volunteerTargets": {k: v for k, v in vol_targets.items() if k != "keys"},
        },
    }


# ─────────────────────────────────────────────────────────────────────────────
# ROUTES FLASK
# ─────────────────────────────────────────────────────────────────────────────

@app.route("/health", methods=["GET", "POST"])
def health():
    return jsonify({"success": True, "status": "ok", "version": "2.0.0"})


@app.route("/solve", methods=["POST"])
def solve():
    payload = request.get_json(silent=True) or {}
    try:
        result = build_result(payload)
        return jsonify({"success": True, "result": result})
    except ValueError as error:
        return jsonify({"success": False, "error": str(error)}), 400
    except Exception as error:
        return jsonify({"success": False, "error": str(error)}), 500


@app.route("/reshuffle_sectors", methods=["POST"])
def reshuffle_sectors():
    payload = request.get_json(silent=True) or {}
    try:
        affectations = payload.get("affectations") or []
        attempt = max(1, int((payload.get("attempt") or 1)))
        if not affectations:
            raise ValueError("Aucune affectation fournie.")
        # Réinitialiser les secteurs
        for a in affectations:
            a["secteurs"] = []
        hist = parse_history(payload)
        allocate_sectors(affectations, payload, hist, attempt=attempt)
        warnings = collect_warnings(affectations, hist)
        return jsonify({"success": True, "affectations": affectations, "warnings": warnings})
    except ValueError as e:
        return jsonify({"success": False, "error": str(e)}), 400
    except Exception as e:
        return jsonify({"success": False, "error": str(e)}), 500


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", "5000")))
