"""
Problema: Micro-red discreta robusta a escenarios con preferencias ponderadas y re-optimización lineal.

Este archivo integra, sobre una sola ontología de decisión:
(i) SAT (factibilidad hard),
(ii) #SAT (exposure/ratio sobre el CNF completo si el contador está disponible),
(iii) Conteo proyectado exacto sobre diseño por enumeración finita (robustez sobre observables),
(iv) Weighted MaxSAT (preferencias soft con pesos) y fallback determinista si el backend no retorna modelo,
(v) MIP (optimización lineal del despacho) ejecutado dentro del código e impresión de resultados,
(vi) CAS (motor algebraico) para derivar pesos racionales y luego escalarlos a enteros.

Fecha: 2026-01-20
Autor: ASPIE / SATX
© Oscar Riveros. Todos los derechos reservados.
"""

import satx
from fractions import Fraction


# ---------------------------------------------------------------------
# Configuración estándar (requerida)
# ---------------------------------------------------------------------
SAT    = "wsl kissat <"
MC     = "wsl ganak --verb 0 <"
MAXSAT = "wsl open-wbo <"
MIP    = "wsl lp_solve -fmps <"

BITS = 32


# ---------------------------------------------------------------------
# CAS: pesos/coeficientes desde expresiones racionales
# ---------------------------------------------------------------------
def cas_fraction(expr: str) -> Fraction:
    """
    Evalúa expr en el motor CAS y retorna un Fraction.
    Heurística: espera salida "a/b" o "a" (enteros).
    """
    cas = satx.cas.Engine()
    out = cas.run(expr).strip()

    if "/" in out:
        a, b = out.split("/", 1)
        return Fraction(int(a.strip()), int(b.strip()))
    return Fraction(int(out), 1)


def scaled_int_weight(fr: Fraction, scale: int = 60) -> int:
    """
    Convierte un racional fr a entero positivo por escalamiento.
    MaxSAT requiere pesos enteros positivos.
    """
    w = fr * scale
    if w.denominator != 1:
        # Escala determinista adicional para eliminar denominador.
        w = fr * (scale * w.denominator)
    w_int = int(w)
    return max(1, w_int)


# ---------------------------------------------------------------------
# Especificación del problema (datos)
# ---------------------------------------------------------------------
def problem_data():
    """
    Define los datos del problema (capacidades, demandas, costos, escenarios y pesos soft).
    Devuelve un dict inmutable (convención) para reutilización consistente entre fases.
    """
    cap = {"solar": 5, "nuclear": 8, "bateria": 4}

    scenarios = ["bajo", "alto"]
    T = [0, 1]
    d = {
        "bajo": {0: 6,  1: 5},
        "alto": {0: 10, 1: 9},
    }

    # Costos lineales (MIP)
    c = {"solar": 1, "nuclear": 3, "bateria": 2}
    pi = {"bajo": 1, "alto": 1}

    # Pesos soft derivados por CAS (racionales) -> enteros
    w_solar_fr = cas_fraction("simplify( (1/3) + (1/6) )")     # 1/2
    w_anti_nu  = cas_fraction("simplify( (2/3) )")             # 2/3
    w_batt_fr  = cas_fraction("simplify( (1/5) + (1/10) )")    # 3/10

    w_solar = scaled_int_weight(w_solar_fr, scale=60)
    w_anti  = scaled_int_weight(w_anti_nu,  scale=60)
    w_batt  = scaled_int_weight(w_batt_fr,  scale=60)

    soft = {
        "prefer_solar":  ("solar",   1, w_solar),
        "avoid_nuclear": ("nuclear", 0, w_anti),
        "prefer_batt":   ("bateria", 1, w_batt),
    }

    return {
        "cap": cap,
        "scenarios": scenarios,
        "T": T,
        "d": d,
        "c": c,
        "pi": pi,
        "soft": soft,
    }


# ---------------------------------------------------------------------
# Construcción del modelo SATX (hard + soft)
# ---------------------------------------------------------------------
def build_engine(data, include_soft=True):
    """
    Construye el motor SATX y registra restricciones hard y (opcionalmente) soft.
    Retorna:
      - x: dict {src -> Unit} (decisiones públicas 0/1)
      - p: dict {(src,k,t) -> Unit} (despacho privado)
    """
    satx.engine(bits=BITS, signed=False, strict=True)

    # Decisiones públicas (0/1)
    x = {
        "solar":   satx.integer(bits=BITS, force_int=True),
        "nuclear": satx.integer(bits=BITS, force_int=True),
        "bateria": satx.integer(bits=BITS, force_int=True),
    }
    for v in x.values():
        satx.add(0 <= v)
        satx.add(v <= 1)

    cap = data["cap"]
    scenarios = data["scenarios"]
    T = data["T"]
    d = data["d"]

    # Hard: a lo más 2 fuentes instaladas
    satx.add(x["solar"] + x["nuclear"] + x["bateria"] <= 2)

    # Despacho privado p[s,k,t] con cotas lineales y demanda por escenario/tiempo
    p = {}
    for k in scenarios:
        for t in T:
            for s in x.keys():
                p[(s, k, t)] = satx.integer(bits=BITS, force_int=True)
                satx.add(0 <= p[(s, k, t)])
                satx.add(p[(s, k, t)] <= cap[s] * x[s])

            satx.add(
                p[("solar", k, t)] + p[("nuclear", k, t)] + p[("bateria", k, t)]
                >= d[k][t]
            )

    # Soft (Weighted MaxSAT): SOLO si include_soft=True
    if include_soft:
        soft = data["soft"]
        satx.add(x[soft["prefer_solar"][0]]  == soft["prefer_solar"][1],  soft=True, weight=soft["prefer_solar"][2])
        satx.add(x[soft["avoid_nuclear"][0]] == soft["avoid_nuclear"][1], soft=True, weight=soft["avoid_nuclear"][2])
        satx.add(x[soft["prefer_batt"][0]]   == soft["prefer_batt"][1],   soft=True, weight=soft["prefer_batt"][2])

    return x, p


# ---------------------------------------------------------------------
# Utilidades: diseño (dict) <-> tupla
# ---------------------------------------------------------------------
def tuple_to_design(tup):
    return {"solar": int(tup[0]), "nuclear": int(tup[1]), "bateria": int(tup[2])}


def design_to_tuple(d):
    return (int(d["solar"]), int(d["nuclear"]), int(d["bateria"]))


# ---------------------------------------------------------------------
# SAT: factibilidad hard-only + witness
# ---------------------------------------------------------------------
def run_sat_hard_only(data):
    """
    Construye engine fresco y corre SAT ignorando soft.
    Retorna diseño witness (x_solar, x_nuclear, x_bateria) y dict.
    """
    x, _p = build_engine(data)
    feasible = satx.satisfy(ignore_soft=True, solver=SAT)
    if not feasible:
        return {"sat": False, "x": None}

    model_x = (int(x["solar"].value), int(x["nuclear"].value), int(x["bateria"].value))
    return {"sat": True, "x": model_x}


# ---------------------------------------------------------------------
# #SAT: exposure completo (si MC está operativo)
# ---------------------------------------------------------------------
def run_sharp_sat_exposure_full(data):
    """
    Construye engine fresco y computa exposure(event) sobre CNF completo.
    Si el backend de conteo no está operativo, el resultado puede ser 0 o error.
    """
    x, _p = build_engine(data)
    event = (x["solar"] == 1)
    # normalize=True pide ratio; internal_max_vars controla fallback interno cuando aplica.
    info_full = satx.exposure(event, solver=MC, normalize=True, internal_max_vars=2048)
    return info_full


# ---------------------------------------------------------------------
# Conteo proyectado exacto sobre diseño: enumeración de {0,1}^3
# ---------------------------------------------------------------------
def projected_design_count_enum(data):
    """
    Conteo proyectado exacto sobre diseño x ∈ {0,1}^3:
      cuenta cuántos diseños admiten ∃ despacho p que satisface hard.
    """
    designs = [
        {"solar": a, "nuclear": b, "bateria": c}
        for a in (0, 1) for b in (0, 1) for c in (0, 1)
    ]

    total = 0
    with_solar = 0
    feasible_designs = []

    for dsgn in designs:
        x, _p = build_engine(data)
        satx.add(x["solar"] == dsgn["solar"])
        satx.add(x["nuclear"] == dsgn["nuclear"])
        satx.add(x["bateria"] == dsgn["bateria"])

        ok = satx.satisfy(ignore_soft=True, solver=SAT)
        if ok:
            total += 1
            feasible_designs.append(dsgn)
            if dsgn["solar"] == 1:
                with_solar += 1

    ratio = (with_solar / total) if total > 0 else 0.0
    return {
        "projected_total_designs": total,
        "projected_designs_with_solar": with_solar,
        "projected_ratio_solar": ratio,
        "feasible_designs": feasible_designs,
    }


# ---------------------------------------------------------------------
# Weighted MaxSAT: intento de resolver por backend, con fallback determinista
# ---------------------------------------------------------------------
def soft_score(data, design):
    """
    Score de preferencias soft (para fallback cuando MaxSAT no retorna modelo).
    Suma pesos de soft satisfechas por el diseño.
    """
    soft = data["soft"]
    score = 0

    s, val, w = soft["prefer_solar"]
    if design[s] == val:
        score += w

    s, val, w = soft["avoid_nuclear"]
    if design[s] == val:
        score += w

    s, val, w = soft["prefer_batt"]
    if design[s] == val:
        score += w

    return score


def select_design_via_maxsat_or_fallback(data, feasible_designs):
    """
    1) Intenta MaxSAT con backend externo.
       - Si retorna modelo, lo usa.
       - Si retorna UNSAT o sin modelo, hace fallback:
         elige el diseño factible que maximiza soft_score.

    Retorna dict:
      {
        "method": "maxsat" | "fallback",
        "design": {...} | None,
        "maxsat_raw": res_dict
      }
    """
    x, _p = build_engine(data, include_soft=True)
    res = satx.maxsat([x["solar"], x["nuclear"], x["bateria"]], solver=MAXSAT)

    # Caso ideal: backend entrega modelo alineado
    if isinstance(res, dict) and res.get("status") == "ok":
        ml = res.get("model_list")
        if ml and len(ml) == 3:
            design = {"solar": int(ml[0]), "nuclear": int(ml[1]), "bateria": int(ml[2])}
            return {"method": "maxsat", "design": design, "maxsat_raw": res}

    # Fallback: escoger mejor diseño factible por score soft
    if not feasible_designs:
        return {"method": "fallback", "design": None, "maxsat_raw": res}

    best = None
    best_score = None
    for dsgn in feasible_designs:
        sc = soft_score(data, dsgn)
        if best is None or sc > best_score:
            best = dsgn
            best_score = sc

    return {
        "method": "fallback",
        "design": best,
        "maxsat_raw": res,
        "fallback_score": best_score,
    }


# ---------------------------------------------------------------------
# MIP: ejecutar dentro del código e imprimir resultados
# ---------------------------------------------------------------------
def run_mip_and_print(data, fixed_design):
    """
    Ejecuta MIP dentro del código e imprime resultados.
    IMPORTANTE (SATX 0.5.4): MIP NO soporta soft/weighted constraints en el engine.
    Por eso construimos un engine hard-only (include_soft=False).
    """
    if fixed_design is None:
        raise RuntimeError("MIP requiere un diseño fijo (fixed_design != None).")

    # Engine hard-only: sin soft
    x, p = build_engine(data, include_soft=False)

    # Fijar diseño (hard)
    satx.add(x["solar"]   == int(fixed_design["solar"]))
    satx.add(x["nuclear"] == int(fixed_design["nuclear"]))
    satx.add(x["bateria"] == int(fixed_design["bateria"]))

    scenarios = data["scenarios"]
    T = data["T"]
    c = data["c"]
    pi = data["pi"]

    objective = 0
    mip_vars = []

    # Orden fijo para alinear model_list (si existe)
    for k in scenarios:
        for t in T:
            for s in ("solar", "nuclear", "bateria"):
                pv = p[(s, k, t)]
                mip_vars.append(pv)
                objective = objective + (pi[k] * c[s]) * pv

    res = satx.mip(
        mip_vars,
        objective=objective,
        sense="min",
        solver=MIP,
        format="mps",
    )

    print("\n[MIP]")
    print("fixed_design:", fixed_design)

    if not isinstance(res, dict):
        print("Unexpected MIP result type:", type(res))
        return

    print("status:", res.get("status"))
    if "objective" in res:
        print("objective:", res.get("objective"))

    ml = res.get("model_list")
    if ml is not None:
        idx = 0
        for k in scenarios:
            for t in T:
                row = {}
                for s in ("solar", "nuclear", "bateria"):
                    row[f"p[{s},{k},{t}]"] = ml[idx]
                    idx += 1
                print(row)
    else:
        any_val = False
        for k in scenarios:
            for t in T:
                row = {}
                for s in ("solar", "nuclear", "bateria"):
                    v = p[(s, k, t)]
                    row[f"p[{s},{k},{t}]"] = (None if v.value is None else int(v.value))
                    any_val = any_val or (v.value is not None)
                print(row)
        if not any_val:
            print("(no model values parsed; revise raw_output)")

    if res.get("raw_output"):
        print("\n[MIP raw_output]\n", res["raw_output"])

    # --- Retorno estructurado para auditoría CAS ---
    mip_pvals = {}
    if ml is not None:
        idx = 0
        for k in scenarios:
            for t in T:
                for s in ("solar", "nuclear", "bateria"):
                    mip_pvals[(s, k, t)] = int(ml[idx])
                    idx += 1
    else:
        # fallback si no hay model_list
        for k in scenarios:
            for t in T:
                for s in ("solar", "nuclear", "bateria"):
                    v = p[(s, k, t)]
                    mip_pvals[(s, k, t)] = 0 if v.value is None else int(v.value)

    return {"res": res, "mip_pvals": mip_pvals}

# ---------------------------------------------------------------------
# Teoría (demo): conteo proyectado en satx.theory (separado del engine)
# ---------------------------------------------------------------------
def run_theory_projected_count_demo():
    """
    Demo intencionalmente pequeño: muestra conteo proyectado sobre 3 variables públicas.
    No pretende equivaler 1:1 al modelo operativo con despacho; es una demostración del mecanismo.
    """
    th = satx.theory
    spec = satx.h10_b.H10BSpec(bits=BITS, signed=False, arith="no_overflow")
    sig = th.signature(["x_solar", "x_nuclear", "x_bateria"], spec)

    def phi_builder(v):
        satx.add(0 <= v["x_solar"]);   satx.add(v["x_solar"] <= 1)
        satx.add(0 <= v["x_nuclear"]); satx.add(v["x_nuclear"] <= 1)
        satx.add(0 <= v["x_bateria"]); satx.add(v["x_bateria"] <= 1)

        satx.add(v["x_solar"] + v["x_nuclear"] + v["x_bateria"] <= 2)
        return satx.any([v["x_solar"] == 1, v["x_bateria"] == 1])

    phi = th.atom(sig, phi_builder)
    return th.count(phi, project=["x_solar", "x_nuclear", "x_bateria"], internal_max_vars=2048)

# ---------------------------------------------------------------------
# CAS PROTAGONISTA: certificado dual + sensibilidad (precio sombra) del despacho
# ---------------------------------------------------------------------
from dataclasses import dataclass

@dataclass(frozen=True)
class DualCertificate:
    lam: int                 # lambda (shadow price) para la restricción de demanda
    mu: dict                 # mu[s] para cotas superiores p_s <= U_s
    dual_obj: int            # valor dual (debe igualar al primal en óptimo)
    primal_obj: int          # valor primal reportado (MIP) o recomputado
    gap: int                 # primal - dual (debe ser 0 en fuerte dualidad)


class CASHelper:
    """
    Wrapper pequeño para usar satx.cas.Engine() como motor de aritmética exacta:
    - construye expresiones, simplifica, y parsea enteros/fracciones.
    """
    def __init__(self):
        self.cas = satx.cas.Engine()

    def run(self, expr: str) -> str:
        return self.cas.run(expr).strip()

    def as_fraction(self, s: str) -> Fraction:
        s = s.strip()
        if "/" in s:
            a, b = s.split("/", 1)
            return Fraction(int(a.strip()), int(b.strip()))
        return Fraction(int(s), 1)

    def simp_frac(self, expr: str) -> Fraction:
        out = self.run(f"simplify( {expr} )")
        return self.as_fraction(out)

    def simp_int(self, expr: str) -> int:
        fr = self.simp_frac(expr)
        if fr.denominator != 1:
            raise ValueError(f"CAS devolvió fracción no-entera: {fr} para expr={expr}")
        return int(fr)


def merit_order_thresholds(design, data, cas: CASHelper):
    """
    Calcula (con CAS) los umbrales de demanda donde cambia el marginal:
      t1 = U_(cheapest)
      t2 = U_(cheapest)+U_(2nd)
      ...
    Retorna lista de (src, cost, U, threshold_prefix_sum).
    """
    cap = data["cap"]
    c = data["c"]

    # capacidades efectivas
    U = {s: cap[s] * int(design[s]) for s in ("solar", "nuclear", "bateria")}

    # ordenar por costo
    order = sorted([(s, c[s], U[s]) for s in U.keys()], key=lambda x: x[1])

    out = []
    acc = 0
    for (s, cost, u) in order:
        # acc := acc + u (pero vía CAS para dejar trazabilidad simbólica)
        acc = cas.simp_int(f"{acc} + {u}")
        out.append((s, cost, u, acc))
    return out


def predicted_lambda_for_demand(demand: int, thresholds):
    """
    Con thresholds de merit order, predice lambda (shadow price marginal):
    - si demand <= t1 => cost1
    - elif demand <= t2 => cost2
    - ...
    (si demanda excede suma total => infeasible, lambda=None)
    """
    prev = 0
    for (s, cost, u, th) in thresholds:
        if demand <= th:
            return cost
        prev = th
    return None


def dual_certificate_single_period(design, demand: int, data, cas: CASHelper, mip_dispatch):
    """
    Certificado dual para un periodo (k,t):
    Primal (despacho):
      min sum_s c_s p_s
      s.t. sum_s p_s >= d
           0 <= p_s <= U_s

    Dual equivalente:
      max d*λ - sum_s U_s*μ_s
      s.t. λ - μ_s <= c_s
           λ >= 0, μ_s >= 0

    En el óptimo tipo “merit order”:
      λ = costo marginal (último generador usado)
      μ_s = max(0, λ - c_s)
    """
    cap = data["cap"]
    c = data["c"]

    U = {s: cap[s] * int(design[s]) for s in ("solar", "nuclear", "bateria")}
    costs = {s: int(c[s]) for s in ("solar", "nuclear", "bateria")}

    # 1) primal objective desde el despacho MIP del periodo (k,t)
    primal = 0
    for s in ("solar", "nuclear", "bateria"):
        primal = cas.simp_int(f"{primal} + {costs[s]}*{int(mip_dispatch[s])}")

    # 2) lambda predicho por merit-order (sensibilidad)
    th = merit_order_thresholds(design, data, cas)
    lam = predicted_lambda_for_demand(demand, th)
    if lam is None:
        # si infeasible, no hay certificado (pero tu SAT ya garantiza factibilidad)
        return DualCertificate(lam=-1, mu={}, dual_obj=-1, primal_obj=primal, gap=primal - (-1))

    # 3) mu_s = max(0, lam - c_s), pero como lam y c_s son ints, lo computamos con CAS por claridad
    mu = {}
    for s in ("solar", "nuclear", "bateria"):
        diff = cas.simp_int(f"{lam} - {costs[s]}")
        mu[s] = max(0, diff)

    # 4) dual objective = d*lam - sum_s U_s*mu_s
    dual = cas.simp_int(f"{demand}*{lam}")
    for s in ("solar", "nuclear", "bateria"):
        dual = cas.simp_int(f"{dual} - {U[s]}*{mu[s]}")

    gap = cas.simp_int(f"{primal} - {dual}")
    return DualCertificate(lam=lam, mu=mu, dual_obj=dual, primal_obj=primal, gap=gap)


def cas_dispatch_audit(design, data, mip_pvals):
    """
    Auditoría CAS “publication-ready”:
    - imprime umbrales (sensibilidad) del diseño
    - para cada (k,t):
        * demanda d
        * despacho MIP
        * lambda predicho (shadow price)
        * certificado dual (dual_obj) y gap (=0 esperado)
    """
    cas = CASHelper()
    scenarios = data["scenarios"]
    T = data["T"]
    d = data["d"]

    print("\n[CAS AUDIT]")
    print("design:", design)

    th = merit_order_thresholds(design, data, cas)
    print("merit-order thresholds (src, cost, U, cumulative_U):")
    for row in th:
        print("  ", row)

    ok_all = True
    for k in scenarios:
        for t in T:
            demand = int(d[k][t])
            disp = {
                "solar":   int(mip_pvals[("solar", k, t)]),
                "nuclear": int(mip_pvals[("nuclear", k, t)]),
                "bateria": int(mip_pvals[("bateria", k, t)]),
            }

            cert = dual_certificate_single_period(design, demand, data, cas, disp)

            print(f"\n(k={k}, t={t}) demand={demand}")
            print("  dispatch:", disp)
            print("  lambda(pred):", cert.lam)
            print("  mu:", cert.mu)
            print("  primal_obj:", cert.primal_obj, "dual_obj:", cert.dual_obj, "gap:", cert.gap)

            if cert.gap != 0:
                ok_all = False

    print("\n[CAS AUDIT SUMMARY] strong_duality_ok =", ok_all)


# ---------------------------------------------------------------------
# Main: pipeline multi-backend (aislado por fase)
# ---------------------------------------------------------------------
def main():
    data = problem_data()

    # 1) SAT hard-only
    sat_info = run_sat_hard_only(data)
    print("\n[SAT hard-only]", sat_info)

    # 2) #SAT exposure full (si MC está operativo)
    try:
        exposure_full = run_sharp_sat_exposure_full(data)
    except Exception as e:
        exposure_full = {"error": repr(e)}
    proj_enum = projected_design_count_enum(data)

    print("\n[#SAT via exposure]", {
        "exposure_full": exposure_full,
        "projected_over_design_enum": proj_enum,
    })

    # 3) Weighted MaxSAT (o fallback)
    opt = select_design_via_maxsat_or_fallback(data, proj_enum["feasible_designs"])
    print("\n[Weighted MaxSAT]", opt.get("maxsat_raw"))
    if opt.get("method") == "fallback":
        print("[MaxSAT fallback] chosen_design:", opt.get("design"), "score:", opt.get("fallback_score"))

    # 4) Theory demo
    th_cnt = run_theory_projected_count_demo()
    print("\n[Theory projected count demo]", th_cnt)

    # 5) MIP ejecutado: usar diseño elegido por MaxSAT o fallback (si ninguno, usar witness SAT)
    fixed = opt.get("design")
    if fixed is None and sat_info.get("sat") and sat_info.get("x") is not None:
        fixed = tuple_to_design(sat_info["x"])

    if fixed is None:
        raise RuntimeError("No hay diseño fijo disponible para ejecutar MIP (MaxSAT sin modelo y SAT sin witness).")

    mip_pack = run_mip_and_print(data, fixed_design=fixed)
    cas_dispatch_audit(fixed, data, mip_pack["mip_pvals"])



if __name__ == "__main__":
    main()
