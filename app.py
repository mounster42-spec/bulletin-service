import os
import unicodedata

from flask import Flask, jsonify, request
from ortools.sat.python import cp_model


app = Flask(__name__)


def normalize(value):
    return unicodedata.normalize("NFD", str(value or "")).encode("ascii", "ignore").decode("ascii").strip().lower()


def normalize_demi(value):
    text = normalize(value)
    if not text:
        return ""
    if "matin" in text:
        return "Matin"
    if "apres" in text:
        return "Après-midi"
    if "jour" in text:
        return "Journée"
    return str(value or "").strip()


def normalize_poste(value):
    text = normalize(value)
    if not text:
        return ""
    if text == "lapi":
        return "LAPI"
    if text in {"lapi1", "lapi 1"}:
        return "LAPI1"
    if text in {"lapi2", "lapi 2"}:
        return "LAPI2"
    if "accueil" in text:
        return "Accueil"
    if "suiveuse" in text or "suiv" in text:
        return "Suiveuse"
    if "back" in text:
        return "Back-office"
    if "terrain" in text:
        return "Terrain"
    return str(value or "").strip()


def normalize_bool(value):
    if value in (True, 1):
        return True
    if value in (False, 0, "", None):
        return False
    if isinstance(value, (int, float)):
        return value != 0
    text = normalize(value)
    if not text:
        return False
    if any(symbol in str(value) for symbol in ["✔", "✅", "☑", "✓"]):
        return True
    if any(symbol in str(value) for symbol in ["❌", "✖", "✗"]):
        return False
    return text in {"true", "vrai", "oui", "yes", "1", "x"}


def parse_int(value, default=0):
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def get_presence(agent, demi_journee):
    if demi_journee == "Matin":
        return normalize_bool(agent.get("presentMatin"))
    if demi_journee == "Après-midi":
        return normalize_bool(agent.get("presentApresMidi"))
    if demi_journee == "Journée":
        return normalize_bool(agent.get("presentMatin")) and normalize_bool(agent.get("presentApresMidi"))
    return normalize_bool(agent.get("presentMatin")) or normalize_bool(agent.get("presentApresMidi"))


def get_heures_sup(agent, demi_journee):
    if demi_journee == "Matin":
        return normalize_bool(agent.get("heuresSupMatin"))
    if demi_journee == "Après-midi":
        return normalize_bool(agent.get("heuresSupApresMidi"))
    if demi_journee == "Journée":
        return normalize_bool(agent.get("heuresSupMatin")) or normalize_bool(agent.get("heuresSupApresMidi"))
    return normalize_bool(agent.get("heuresSupMatin")) or normalize_bool(agent.get("heuresSupApresMidi"))


def build_active_agents(payload):
    workbook = (payload or {}).get("workbook") or {}
    demi_journee = normalize_demi((payload or {}).get("demiJournee"))
    agents = []
    for raw in workbook.get("agents") or []:
        nom = str((raw or {}).get("nom") or "").strip()
        if not nom:
            continue
        if not get_presence(raw or {}, demi_journee):
            continue
        agents.append(
            {
                "nom": nom,
                "equipe": str((raw or {}).get("equipe") or "").strip(),
                "heuresSup": get_heures_sup(raw or {}, demi_journee),
                "accueil": normalize_bool((raw or {}).get("accueil")),
            }
        )
    return agents


def build_poste_counts(payload):
    params = (((payload or {}).get("workbook") or {}).get("parametres") or {})
    return {
        "LAPI1": parse_int(params.get("LAPI 1"), 2),
        "LAPI2": parse_int(params.get("LAPI 2"), 2),
        "Accueil": parse_int(params.get("Accueil"), 2),
        "Suiveuse": parse_int(params.get("Suiveuse"), 1),
        "Back-office": parse_int(params.get("Back-office"), 1),
    }


def build_slots(payload, counts):
    forced_teams = (payload or {}).get("forcedTeams") or {}
    return [
        *[
            {"id": f"Accueil#{i + 1}", "poste": "Accueil", "required_team": None}
            for i in range(max(0, counts["Accueil"]))
        ],
        *[
            {"id": f"LAPI1#{i + 1}", "poste": "LAPI1", "required_team": str(forced_teams.get("lapi1") or "").strip() or None}
            for i in range(max(0, counts["LAPI1"]))
        ],
        *[
            {"id": f"LAPI2#{i + 1}", "poste": "LAPI2", "required_team": str(forced_teams.get("lapi2") or "").strip() or None}
            for i in range(max(0, counts["LAPI2"]))
        ],
        *[
            {"id": f"Suiveuse#{i + 1}", "poste": "Suiveuse", "required_team": str(forced_teams.get("suiveuse") or "").strip() or None}
            for i in range(max(0, counts["Suiveuse"]))
        ],
        *[
            {"id": f"Back-office#{i + 1}", "poste": "Back-office", "required_team": None}
            for i in range(max(0, counts["Back-office"]))
        ],
    ]


def is_matching_poste(restriction_poste, poste):
    normalized = normalize_poste(restriction_poste)
    if not normalized:
        return True
    if normalized == "LAPI":
        return poste in {"LAPI1", "LAPI2"}
    return normalized == poste


def build_restrictions(payload):
    demi_journee = normalize_demi((payload or {}).get("demiJournee"))
    rows = (((payload or {}).get("workbook") or {}).get("postesInterdits") or [])
    restrictions = {}
    for row in rows:
        agent = normalize((row or {}).get("agent"))
        poste = normalize_poste((row or {}).get("poste"))
        demi = normalize_demi((row or {}).get("demiJournee"))
        if not agent or not poste:
            continue
        restrictions.setdefault(agent, []).append({"poste": poste, "demi": demi})
    return demi_journee, restrictions


def is_forbidden(agent_name, poste, demi_journee, restrictions):
    for item in restrictions.get(normalize(agent_name), []):
        if item["demi"] and item["demi"] != demi_journee:
            continue
        if is_matching_poste(item["poste"], poste):
            return True
    return False


def build_incompatibilities(payload):
    rows = (((payload or {}).get("workbook") or {}).get("incompatibilites") or [])
    result = []
    for row in rows:
        agent1 = normalize((row or {}).get("agent1"))
        agent2 = normalize((row or {}).get("agent2"))
        poste = normalize_poste((row or {}).get("poste"))
        if not agent1 or not agent2:
            continue
        result.append({"agent1": agent1, "agent2": agent2, "poste": poste})
    return result


def build_history_maps(payload):
    history = (((payload or {}).get("workbook") or {}).get("historique") or [])
    counts = {}
    last_poste = {}
    for row in history:
        agent_field = str((row or {}).get("agent") or "").strip()
        poste = normalize_poste((row or {}).get("poste"))
        if not agent_field or not poste:
            continue
        agent_names = [part.strip() for part in agent_field.split("/") if part.strip()]
        for name in agent_names:
            key = normalize(name)
            counts.setdefault(key, {})
            counts[key][poste] = counts[key].get(poste, 0) + 1
            last_poste[key] = poste
    return counts, last_poste


def candidate_allowed(agent, slot, demi_journee, restrictions):
    poste = slot["poste"]
    if slot.get("required_team") and slot["required_team"] != agent.get("equipe"):
        return False
    if is_forbidden(agent["nom"], poste, demi_journee, restrictions):
        return False
    if poste == "Accueil":
        if not agent.get("accueil"):
            return False
        if agent.get("heuresSup"):
            return False
    if poste == "Suiveuse" and agent.get("heuresSup"):
        return False
    return True


def candidate_score(agent, poste, history_counts, last_poste):
    key = normalize(agent["nom"])
    history = history_counts.get(key, {})
    score = 10000
    score -= history.get(poste, 0) * 180
    if last_poste.get(key) == poste:
        score -= 1400
    if poste in {"LAPI1", "LAPI2"} and agent.get("heuresSup"):
        score += 350
    if poste == "Back-office" and agent.get("heuresSup"):
        score += 120
    if poste == "Accueil" and agent.get("accueil"):
        score += 150
    return score


def solve_named_slots(agents, slots, payload):
    demi_journee, restrictions = build_restrictions(payload)
    incompatibilities = build_incompatibilities(payload)
    history_counts, last_poste = build_history_maps(payload)

    model = cp_model.CpModel()
    variables = {}
    agent_index = {normalize(agent["nom"]): i for i, agent in enumerate(agents)}

    for slot_idx, slot in enumerate(slots):
        for agent_idx, agent in enumerate(agents):
            if candidate_allowed(agent, slot, demi_journee, restrictions):
                variables[(agent_idx, slot_idx)] = model.NewBoolVar(f"x_{agent_idx}_{slot_idx}")

    for slot_idx, _slot in enumerate(slots):
        slot_vars = [variables[(agent_idx, slot_idx)] for agent_idx in range(len(agents)) if (agent_idx, slot_idx) in variables]
        if not slot_vars:
            raise ValueError(f"Aucun candidat éligible pour {_slot['poste']}")
        model.Add(sum(slot_vars) == 1)

    for agent_idx, _agent in enumerate(agents):
        agent_vars = [variables[(agent_idx, slot_idx)] for slot_idx in range(len(slots)) if (agent_idx, slot_idx) in variables]
        if agent_vars:
            model.Add(sum(agent_vars) <= 1)

    for row in incompatibilities:
        a = agent_index.get(row["agent1"])
        b = agent_index.get(row["agent2"])
        if a is None or b is None:
            continue
        for poste in ["Accueil", "LAPI1", "LAPI2", "Suiveuse", "Back-office"]:
            if row["poste"] and not is_matching_poste(row["poste"], poste):
                continue
            poste_slots = [idx for idx, slot in enumerate(slots) if slot["poste"] == poste]
            vars_a = [variables[(a, idx)] for idx in poste_slots if (a, idx) in variables]
            vars_b = [variables[(b, idx)] for idx in poste_slots if (b, idx) in variables]
            if vars_a or vars_b:
                model.Add(sum(vars_a) + sum(vars_b) <= 1)

    objective_terms = []
    for (agent_idx, slot_idx), var in variables.items():
        score = candidate_score(agents[agent_idx], slots[slot_idx]["poste"], history_counts, last_poste)
        objective_terms.append(score * var)
    model.Maximize(sum(objective_terms))

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = 10
    solver.parameters.num_search_workers = 8
    status = solver.Solve(model)
    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        raise ValueError("Aucune solution faisable trouvée pour les postes nommés")

    assignments = []
    used_agents = set()
    for slot_idx, slot in enumerate(slots):
        for agent_idx, agent in enumerate(agents):
            var = variables.get((agent_idx, slot_idx))
            if var is not None and solver.Value(var) == 1:
                assignments.append({"poste": slot["poste"], "agent": agent["nom"]})
                used_agents.add(normalize(agent["nom"]))
                break

    remaining = [agent for agent in agents if normalize(agent["nom"]) not in used_agents]
    return assignments, remaining


def pair_incompatible(agent_a, agent_b, incompatibilities):
    if not agent_a or not agent_b:
        return False
    a = normalize(agent_a["nom"])
    b = normalize(agent_b["nom"])
    for row in incompatibilities:
        if {a, b} != {row["agent1"], row["agent2"]}:
            continue
        if not row["poste"] or is_matching_poste(row["poste"], "Terrain"):
            return True
    return False


def build_terrain_affectations(remaining_agents, payload):
    incompatibilities = build_incompatibilities(payload)
    queue = list(remaining_agents)
    terrain = []
    while queue:
        first = queue.pop(0)
        partner_index = None
        for idx, candidate in enumerate(queue):
            if not pair_incompatible(first, candidate, incompatibilities):
                partner_index = idx
                break
        if partner_index is None:
            terrain.append({"poste": "Terrain", "agents": [first["nom"]], "secteurs": []})
            continue
        second = queue.pop(partner_index)
        terrain.append({"poste": "Terrain", "agents": [first["nom"], second["nom"]], "secteurs": []})
    return terrain


def allocate_sectors(payload, affectations):
    workbook = (payload or {}).get("workbook") or {}
    options = (payload or {}).get("options") or {}
    sectors = [str((item or {}).get("secteur") or "").strip() for item in workbook.get("secteurs") or [] if str((item or {}).get("secteur") or "").strip()]
    required_lapi1 = parse_int(options.get("requiredSectorsLAPI1"), 4)
    required_lapi2 = parse_int(options.get("requiredSectorsLAPI2"), 4)

    lapi1 = next((item for item in affectations if item["poste"] == "LAPI1"), None)
    lapi2 = next((item for item in affectations if item["poste"] == "LAPI2"), None)

    offset = 0
    if lapi1:
        lapi1["secteurs"] = sectors[offset:offset + required_lapi1]
        offset += len(lapi1["secteurs"])
    if lapi2:
        lapi2["secteurs"] = sectors[offset:offset + required_lapi2]
        offset += len(lapi2["secteurs"])

    terrain_sectors = sectors[offset:] or sectors[:]
    terrain_affectations = [item for item in affectations if item["poste"] == "Terrain"]
    for idx, item in enumerate(terrain_affectations):
        if not terrain_sectors:
            item["secteurs"] = []
            continue
        item["secteurs"] = [terrain_sectors[idx % len(terrain_sectors)]]

    return affectations


def build_result(payload):
    agents = build_active_agents(payload)
    if len(agents) < 2:
        raise ValueError("Pas assez d'agents présents pour lancer le solveur")

    counts = build_poste_counts(payload)
    slots = build_slots(payload, counts)
    if len(slots) > len(agents):
        raise ValueError("Pas assez d'agents présents pour couvrir les postes demandés")

    named_assignments, remaining_agents = solve_named_slots(agents, slots, payload)

    grouped = {}
    for row in named_assignments:
        grouped.setdefault(row["poste"], []).append(row["agent"])

    affectations = []
    for poste in ["LAPI1", "LAPI2", "Accueil", "Suiveuse", "Back-office"]:
        if grouped.get(poste):
            affectations.append({"poste": poste, "agents": grouped[poste], "secteurs": []})

    affectations.extend(build_terrain_affectations(remaining_agents, payload))
    affectations = allocate_sectors(payload, affectations)

    return {
        "date": (payload or {}).get("date"),
        "demiJournee": normalize_demi((payload or {}).get("demiJournee")),
        "affectations": affectations,
        "warnings": [],
        "meta": {
            "agentsInput": len(agents),
            "slotsNamed": len(slots),
            "terrainGroups": len([item for item in affectations if item["poste"] == "Terrain"]),
        },
    }


@app.route("/health", methods=["GET", "POST"])
def health():
    return jsonify({"success": True, "status": "ok"})


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


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", "5000")))
