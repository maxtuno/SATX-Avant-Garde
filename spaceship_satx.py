"""
Problema: Self-Sustaining Spaceship — síntesis óptima (capacidad + operación).

Se decide (i) capacidad instalada entera por módulo cap_u[m] y (ii) operación diaria run_q[t,m]
en un horizonte discreto K, manteniendo balances de recursos dentro de rangos seguros.

Para soportar operación fraccional sin bilinearidad, se introduce una cuantización Q:
- cap_u[m] = número entero de unidades instaladas.
- run_q[t,m] = enteros en “cuantos” (p.ej. Q=4 => cuartos de unidad por día).
  Se impone run_q[t,m] <= Q * cap_u[m] (lineal).
- Los inventarios S' se escalan por Q: S' = Q * S físico.
  Así, con run_q, los balances quedan enteros y lineales.

Objetivo: minimizar capacidad instalada (ponderada) y opcionalmente el presupuesto energético
diario EB' (también en escala Q).

Fecha: 2026-01-19
Autor: ASPIE / SATX.
© Oscar Riveros. Todos los derechos reservados.
"""

import satx

SAT    = "wsl kissat <"
MC     = "wsl ganak --verb 0 <"
MAXSAT = "wsl open-wbo <"
MIP    = "wsl lp_solve -fmps <"

BITS = 32


def build_spaceship_model(params):
    """
    params:
      K: int >= 1
      Q: int >= 1  (cuantización; Q=4 => run en cuartos de unidad)
      resources: r -> {safe_min:int, safe_max:int, init:int}   (UNIDADES FÍSICAS; se escalan por Q internamente)
      crew: {prod: r->int, cons: r->int}                       (por día, unidades físicas; se escalan por Q)
      modules: m -> {
          cap_ub:int, cap_cost:int, energy:int,
          prod: r->int, cons: r->int                           (por unidad física completa; NO se escalan)
      }
      sustain_mode: "cyclic" | "nondecreasing" | "free"
      optimize_energy: bool
      objective_mode: "capacity_only" | "capacity_then_energy" | "weighted"
      weights: {W_CAP:int, W_EB:int}
    """

    K = int(params["K"])
    assert K >= 1

    Q = int(params.get("Q", 1))
    assert Q >= 1

    resources = params["resources"]
    crew = params["crew"]
    modules = params["modules"]

    sustain_mode = params.get("sustain_mode", "cyclic")
    optimize_energy = bool(params.get("optimize_energy", True))
    objective_mode = params.get("objective_mode", "capacity_then_energy")
    weights = params.get("weights", {"W_CAP": 1, "W_EB": 1})

    satx.engine(bits=BITS, signed=False, width_policy="strict", const_policy="strict")

    R = list(resources.keys())
    M = list(modules.keys())

    # -------------------------
    # Variables
    # -------------------------
    cap_u = {m: satx.integer() for m in M}                         # unidades instaladas (enteras)
    run_q = {(t, m): satx.integer() for t in range(K) for m in M}  # cuantos de operación (enteros)
    S = {(t, r): satx.integer() for t in range(K + 1) for r in R}  # inventarios escalados: S' = Q*S_físico
    EBq = satx.integer() if optimize_energy else None              # presupuesto energético escalado

    # -------------------------
    # Bounds inventarios y estado inicial (escalados por Q)
    # -------------------------
    for r in R:
        smin = int(resources[r]["safe_min"]) * Q
        smax = int(resources[r]["safe_max"]) * Q
        s0   = int(resources[r]["init"]) * Q
        assert 0 <= smin <= smax
        assert smin <= s0 <= smax

        satx.add(S[(0, r)] == s0)
        for t in range(K + 1):
            satx.add(smin <= S[(t, r)])
            satx.add(S[(t, r)] <= smax)

    # -------------------------
    # Bounds capacidad y operación
    # -------------------------
    for m in M:
        cap_ub = int(modules[m]["cap_ub"])
        assert cap_ub >= 0
        satx.add(0 <= cap_u[m])
        satx.add(cap_u[m] <= cap_ub)

    for t in range(K):
        for m in M:
            cap_ub = int(modules[m]["cap_ub"])
            satx.add(0 <= run_q[(t, m)])
            satx.add(run_q[(t, m)] <= Q * cap_ub)      # cota global
            satx.add(run_q[(t, m)] <= Q * cap_u[m])    # run <= Q*cap (lineal)

    # -------------------------
    # Dinámica de balances (enteros, lineal)
    #
    # S'_{t+1,r} = S'_{t,r}
    #           + Q*crew_prod[r] + Σ_m prod[m,r]*run_q[t,m]
    #           - Q*crew_cons[r] - Σ_m cons[m,r]*run_q[t,m]
    # -------------------------
    crew_prod = crew.get("prod", {})
    crew_cons = crew.get("cons", {})

    for t in range(K):
        for r in R:
            crew_prod_r = int(crew_prod.get(r, 0))
            crew_cons_r = int(crew_cons.get(r, 0))
            assert crew_prod_r >= 0 and crew_cons_r >= 0

            inflow_terms = []
            outflow_terms = []

            for m in M:
                p_mr = int(modules[m].get("prod", {}).get(r, 0))
                c_mr = int(modules[m].get("cons", {}).get(r, 0))
                assert p_mr >= 0 and c_mr >= 0

                if p_mr != 0:
                    inflow_terms.append(p_mr * run_q[(t, m)])
                if c_mr != 0:
                    outflow_terms.append(c_mr * run_q[(t, m)])

            inflow_mod = satx.ssum(inflow_terms) if inflow_terms else satx.z0()
            outflow_mod = satx.ssum(outflow_terms) if outflow_terms else satx.z0()

            inflow = (Q * crew_prod_r) + inflow_mod
            outflow = (Q * crew_cons_r) + outflow_mod

            satx.add(S[(t + 1, r)] == S[(t, r)] + inflow - outflow)

    # -------------------------
    # Sustentabilidad final
    # -------------------------
    if sustain_mode == "cyclic":
        for r in R:
            satx.add(S[(K, r)] == S[(0, r)])
    elif sustain_mode == "nondecreasing":
        for r in R:
            satx.add(S[(K, r)] >= S[(0, r)])
    elif sustain_mode == "free":
        pass
    else:
        raise ValueError(f"sustain_mode inválido: {sustain_mode}")

    # -------------------------
    # Energía (escalada): EBq >= Σ_m E_m * run_q[t,m],  ∀t
    # -------------------------
    EBq_ub = 0
    if optimize_energy:
        for m in M:
            e_m = int(modules[m].get("energy", 0))
            cap_ub = int(modules[m]["cap_ub"])
            assert e_m >= 0 and cap_ub >= 0
            EBq_ub += Q * cap_ub * e_m

        satx.add(0 <= EBq)
        satx.add(EBq <= EBq_ub)

        for t in range(K):
            e_terms = []
            for m in M:
                e_m = int(modules[m].get("energy", 0))
                assert e_m >= 0
                if e_m != 0:
                    e_terms.append(e_m * run_q[(t, m)])
            satx.add((satx.ssum(e_terms) if e_terms else satx.z0()) <= EBq)

    # -------------------------
    # Objetivo
    # -------------------------
    cap_cost_terms = []
    for m in M:
        w = int(modules[m].get("cap_cost", 1))
        assert w >= 0
        if w != 0:
            cap_cost_terms.append(w * cap_u[m])

    CAPCOST = satx.ssum(cap_cost_terms) if cap_cost_terms else satx.z0()

    if objective_mode == "capacity_only" or (not optimize_energy):
        objective = CAPCOST
    elif objective_mode == "capacity_then_energy":
        # Lexicográfico (capacidad, luego energía) vía Big-M seguro:
        Mbig = int(EBq_ub) + 1
        assert 0 <= Mbig < (1 << BITS)
        objective = (Mbig * CAPCOST) + EBq
    elif objective_mode == "weighted":
        W_CAP = int(weights.get("W_CAP", 1))
        W_EB  = int(weights.get("W_EB", 1))
        assert W_CAP >= 0 and W_EB >= 0
        objective = (W_CAP * CAPCOST) + (W_EB * EBq)
    else:
        raise ValueError(f"objective_mode inválido: {objective_mode}")

    # Vars a observar (para extracción/validación)
    vars_list = []
    vars_list.extend([cap_u[m] for m in M])
    vars_list.extend([run_q[(t, m)] for t in range(K) for m in M])
    vars_list.extend([S[(t, r)] for t in range(K + 1) for r in R])
    if optimize_energy:
        vars_list.append(EBq)

    return {
        "K": K, "Q": Q,
        "R": R, "M": M,
        "cap_u": cap_u,
        "run_q": run_q,
        "S": S,
        "EBq": EBq,
        "objective": objective,
        "vars": vars_list,
        "EBq_ub": EBq_ub,
    }


def example_params_toy_feasible():
    """
    Toy corregido para que 'cyclic' sea consistente:
    - Water_Recycle produce 5 de H2O por unidad (en vez de 2).
    - Q=4 permite duty-cycle fraccional (p.ej. CO2_to_O2 a 0.75/día => run_q=3).
    """
    return {
        "K": 7,
        "Q": 4,
        "resources": {
            "O2":   {"safe_min": 40, "safe_max": 120, "init": 80},
            "CO2":  {"safe_min":  0, "safe_max":  80, "init": 10},
            "H2O":  {"safe_min": 30, "safe_max": 120, "init": 60},
            "FOOD": {"safe_min": 10, "safe_max":  80, "init": 30},
            "WASTE":{"safe_min":  0, "safe_max":  80, "init":  0},
            "NUTR": {"safe_min":  0, "safe_max":  80, "init": 10},
        },
        "crew": {
            "prod": {"CO2": 8, "WASTE": 3},
            "cons": {"O2": 8, "H2O": 4, "FOOD": 2},
        },
        "modules": {
            "CO2_to_O2": {
                "cap_ub": 10, "cap_cost": 1, "energy": 2,
                "prod": {"O2": 8},
                "cons": {"CO2": 8},
            },
            "Water_Recycle": {
                "cap_ub": 10, "cap_cost": 1, "energy": 1,
                "prod": {"H2O": 5},
                "cons": {"WASTE": 2},
            },
            "Compost": {
                "cap_ub": 10, "cap_cost": 1, "energy": 1,
                "prod": {"NUTR": 1},
                "cons": {"WASTE": 1},
            },
            "Farm": {
                "cap_ub": 10, "cap_cost": 2, "energy": 3,
                "prod": {"FOOD": 2, "O2": 2},
                "cons": {"NUTR": 1, "H2O": 1, "CO2": 2},
            },
        },
        "sustain_mode": "cyclic",
        "optimize_energy": True,
        "objective_mode": "capacity_then_energy",
    }


if __name__ == "__main__":
    params = example_params_toy_feasible()
    mdl = build_spaceship_model(params)

    satx.to_mip(
        format="mps",
        objective=mdl["objective"],
        sense="min",
        path="spaceship.mps",
    )

    # Resolver desde Python (opcional):
    result = satx.mip(
        mdl["vars"],
        objective=mdl["objective"],
        sense="min",
        format="mps",
        solver=MIP,
    )

    print(result["status"], result.get("objective"))
    print("Q =", mdl["Q"])
    if mdl["EBq"] is not None:
        print("EBq =", mdl["EBq"].value, "=> EB =", mdl["EBq"].value / mdl["Q"])
    for m in mdl["M"]:
        print("cap_u", m, mdl["cap_u"][m].value)

    Q = mdl["Q"]

    print("=== RUN SCHEDULE (physical units) ===")
    for t in range(mdl["K"]):
        e_t_q = 0
        row = []
        for m in mdl["M"]:
            rq = mdl["run_q"][(t, m)].value
            row.append((m, rq, rq / Q))
            e_t_q += int(params["modules"][m]["energy"]) * rq
        print("t=", t, row, "E_t_q=", e_t_q, "E_t=", e_t_q / Q)

    print("=== STATES ===")
    for t in range(mdl["K"] + 1):
        print("t=", t, {r: mdl["S"][(t, r)].value / Q for r in mdl["R"]})
