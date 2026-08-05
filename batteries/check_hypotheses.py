#!/usr/bin/env python3
"""Guard #3: the displayed parameters must satisfy the displayed hypotheses,
and the displayed derived numbers must equal their recomputation.

Part A parses the benchmark tuple printed in papers/civic_drift.tex and checks
it against the hypotheses the same paper states: primitive ranges, (SS), (SS+),
(H), box-wide det J > 0, and the cure-dominance inequality of thm:hyst(iv).

Part B parses every printed derived scalar near the benchmark -- alpha_mono,
the det J bound, the (SS) slack, G(0), G(1), beta_dagger, the saddle
eigenvalues, the cure-dominance values, and rho_cure -- recomputes each from
the parsed tuple, and requires agreement at the printed precision. (The
measured escape 0.0801 is battery-measured, not analytic; the battery asserts
it.)

This guard exists because nothing else catches "the figures use parameters the
theorem excludes" or "a printed number drifted from its recomputation" -- both
accumulate quietly and look fine in every build. Exit code 0 iff every check
passes.
"""
import re
import sys
from math import sqrt
from pathlib import Path

TEX = Path(__file__).resolve().parent.parent / "papers" / "civic_drift.tex"
TEX_LOOPS = Path(__file__).resolve().parent.parent / "papers" / "civic_loops.tex"

# Paper III printed derived scalars.  The loop benchmark is stated in
# civic_loops.tex:358 and shares Paper II's primitives with g = 0.
PRINTED_LOOPS = {
    "eps_star":     r"\\varepsilon\^\\ast = ([0-9.]+)\$, a \$([0-9.]+)\\%",
}

BENCH_RE = re.compile(
    r"benchmark parameters \$\(\\eta, c, \\lambda_0, I, v, \\alpha\) = "
    r"\(([\d.]+), ([\d.]+), ([\d.]+), ([\d.]+), ([\d.]+), ([\d.]+)\)\$"
)

PRINTED = {
    "alpha_mono": r"\\alpha_\{\\mathrm\{mono\}\} = ([0-9.]+)",
    "detJ_bound": r"\\det J \\ge ([0-9.]+)",
    "ss_slack":   r"2\\alpha c\^2 I = ([0-9.]+)",
    "G0":         r"G\(0\) = (-?[0-9.]+)\$ and \$G\(1\)",
    "G1":         r"G\(0\) = -?[0-9.]+\$ and \$G\(1\) = ([0-9.]+)",
    "beta_dag":   r"sitting at \$\\beta\^\\dagger = ([0-9.]+)",
    "lam_pf":     r"\\lambda_\{\\mathrm\{PF\}\} = ([0-9.]+)",
    "lam_2":      r"\\lambda_2 = ([0-9.]+)",
    "curedom_l":  r"reads \$([0-9.]+) < [0-9.]+\$",
    "curedom_r":  r"reads \$[0-9.]+ < ([0-9.]+)\$",
    "rho_cure":   r"\\rho_\{\\mathrm\{restore\}\} = \\rho_\{\\mathrm\{cure\}\} = ([0-9.]+)\$ there",
}


def tol_of(printed: str) -> float:
    decimals = len(printed.split(".")[1]) if "." in printed else 0
    return 0.5 * 10 ** (-decimals) * 1.0000001


def main() -> int:
    text = TEX.read_text()
    m = BENCH_RE.search(text)
    if not m:
        print("FAIL  could not parse the printed benchmark tuple from civic_drift.tex")
        return 1
    eta, c, lam0, I, v, alpha = (float(g) for g in m.groups())
    print(f"printed benchmark: eta={eta} c={c} lam0={lam0} I={I} v={v} alpha={alpha}")

    def s(b):
        return (1 - lam0) * (1 - eta * (1 - b)) ** 2

    def sp(b):
        return 2 * eta * (1 - lam0) * (1 - eta * (1 - b))

    def G(b):
        return -v + 2 * c * (1 - c * b) * I / (1 - s(b))

    checks = []

    def check(name, ok, detail):
        checks.append(ok)
        print(f"{'PASS' if ok else 'FAIL'}  {name}: {detail}")

    # ---------------- Part A: hypotheses ----------------
    check("primitives", 0 < eta < 1 and 0 < c < 1 and 0 < lam0 < 1 and I > 0 and v > 0 and alpha > 0,
          "eta,c,lam0 in (0,1); I,v,alpha > 0")

    ss = 2 * alpha * c * c * I
    check("(SS) cooperativity", ss < lam0, f"2*alpha*c^2*I = {ss:.6f} < lam0 = {lam0}")

    a_mono = lam0 * s(0) / (2 * c * I * (c * s(0) + 2 * eta * (1 - lam0)))
    check("(SS+) convergent step", alpha < a_mono,
          f"alpha = {alpha} vs alpha_mono = {a_mono:.6f} (ratio {alpha / a_mono:.2f})")

    check("(H) threshold structure", G(0) < 0 < G(1), f"G(0) = {G(0):.4f}, G(1) = {G(1):.4f}")

    # det J is linear decreasing in D, so the box minimum sits on D = I/lam0.
    Dmax = I / lam0
    det_min = min(
        s(b) - Dmax * (2 * alpha * c * c * s(b) + 2 * alpha * c * (1 - c * b) * sp(b))
        for b in (i / 10000 for i in range(10001))
    )
    check("det J > 0 on B", det_min > 0, f"box-wide min det J = {det_min:.4f}")

    lhs, rhs = c * c * I, v * eta * (1 - lam0) * (1 - eta)
    check("cure dominance (thm:hyst iv)", lhs < rhs, f"c^2*I = {lhs:.4f} < {rhs:.4f}")

    # ---------------- Part B: printed derived values ----------------
    printed = {}
    for key, pat in PRINTED.items():
        pm = re.search(pat, text)
        if not pm:
            check(f"parse {key}", False, "printed value not found -- tex phrasing drifted")
            continue
        printed[key] = pm.group(1)

    # beta_dagger: larger root of the numerator quadratic q = -v(1-s) + 2cI(1-cb)
    a0 = (1 - lam0) * (1 - eta) ** 2
    a1 = 2 * (1 - lam0) * (1 - eta) * eta
    a2 = (1 - lam0) * eta * eta
    qa, qb, qc = v * a2, v * a1 - 2 * c * c * I, v * a0 - v + 2 * c * I
    beta_dag = (-qb + sqrt(qb * qb - 4 * qa * qc)) / (2 * qa)
    Dbar = I / (1 - s(beta_dag))
    aJ = 1 - 2 * alpha * c * c * Dbar
    bJ = 2 * alpha * c * (1 - c * beta_dag)
    cJ = sp(beta_dag) * Dbar
    dJ = s(beta_dag)
    tr, det = aJ + dJ, aJ * dJ - bJ * cJ
    disc = sqrt(tr * tr - 4 * det)
    lam_pf, lam_2 = (tr + disc) / 2, (tr - disc) / 2
    rho_cure = 2 * c * (1 - c) - v * lam0 / I

    computed = {
        "alpha_mono": a_mono, "ss_slack": ss, "G0": G(0), "G1": G(1),
        "beta_dag": beta_dag, "lam_pf": lam_pf, "lam_2": lam_2,
        "curedom_l": lhs, "curedom_r": rhs, "rho_cure": rho_cure,
    }
    for key, val in computed.items():
        if key not in printed:
            continue
        p = printed[key]
        ok = abs(val - float(p)) <= tol_of(p)
        check(f"printed {key}", ok, f"tex prints {p}, recomputed {val:.6f}")
    if "detJ_bound" in printed:
        p = printed["detJ_bound"]
        check("printed detJ_bound", det_min >= float(p) - 1e-12,
              f"tex prints det J >= {p}, recomputed min {det_min:.4f}")

    # ---------------- Part C: Paper III printed derived values ----------------
    if TEX_LOOPS.exists():
        loops = TEX_LOOPS.read_text(encoding="utf-8")
        m = re.search(PRINTED_LOOPS["eps_star"], loops)
        if not m:
            check("parse eps_star", False,
                  "civic_loops.tex no longer prints the inflation slack -- phrasing drifted")
        else:
            # eps* = R (alpha_mono/alpha - 1) with R = I/(lam0 - g), g = 0 at the benchmark
            R = I / lam0
            eps_star = R * (a_mono / alpha - 1.0)
            printed_eps, printed_pct = m.group(1), m.group(2)
            check("printed eps_star",
                  abs(eps_star - float(printed_eps)) <= tol_of(printed_eps),
                  f"loops prints {printed_eps}, recomputed {eps_star:.6f}")
            check("printed eps_star pct",
                  abs(100.0 * eps_star / R - float(printed_pct)) <= tol_of(printed_pct),
                  f"loops prints {printed_pct}%, recomputed {100.0 * eps_star / R:.2f}%")
            # eps* is exactly the boundary: strict dominance holds just below and fails just above
            s0 = s(0.0)
            dom = lambda M: (1 - 2 * alpha * c * c * M) * s0 - (2 * alpha * c) * (2 * eta * (1 - lam0) * M)
            check("eps_star is the exact dominance boundary",
                  dom(R + 0.99 * eps_star) > 0 > dom(R + 1.01 * eps_star),
                  f"margin {dom(R + 0.99 * eps_star):+.2e} just below, "
                  f"{dom(R + 1.01 * eps_star):+.2e} just above")

    if all(checks):
        print("guard #3: GREEN -- printed parameters satisfy printed hypotheses, "
              "printed derived values match recomputation")
        return 0
    print("guard #3: RED -- a displayed parameter, hypothesis, or derived value is out of joint")
    return 1


if __name__ == "__main__":
    sys.exit(main())
