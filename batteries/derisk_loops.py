"""De-risking numerics for 'Civic Loops: Regulating the Feedback Structure, Not the Knob'.

Every conjectured theorem gets a numerical witness before any prose is written.
N0: aggregation-conservation map.  N1: knob-free certificate (small gain).
N2: gain ceilings.  N3: observability/laundering.  N4: rate separation.
N5: identification pipeline.
"""
import numpy as np
rng = np.random.default_rng(23)
PASS = []

def report(name, ok, detail=""):
    PASS.append(ok)
    print(f"{'PASS' if ok else 'FAIL'}  {name}" + (f"  [{detail}]" if detail else ""))

# ============================================================================
# N0: AGGREGATION-CONSERVATION MAP
# Single type, e=0, c=1, u := 1-beta, w = eta*u. Stationary measured gap by
# (stock functional) x (loss degree) x (feedback):
#   A  single-claim mean, p=2:  gap2 = iota^2 u^2/(eta u - zeta)^2   flat iff zeta=0
#   B  single-claim mean, p=1:  gap1 = |iota| u/(eta u - zeta)       flat iff zeta=0
#   C  portfolio L2,      p=2:  gap2 = u^2 I/(1-(1-lam0)(1-eta u)^2 - g)
#        never flat; d(gap2)/du sign = sign(lam0 + eta u(1-lam0) - g)
#        => U_qs increasing in beta globally iff g <= lam0;
#           interior MIN of gap2 at u_c=(g-lam0)/(eta(1-lam0)) when lam0<g<lam0+eta(1-lam0)
#   D  portfolio L1,      p=1:  gap1 = u J/(lam0 - g + (1-lam0) eta u)   FLAT iff g=lam0
# ============================================================================

# --- N0a: closed forms vs long simulation of stationarity ---
ok = True
for _ in range(150):
    eta = rng.uniform(0.2, 0.9); u = rng.uniform(0.05, 1.0); beta = 1 - u
    w = eta * u
    # A/B single-claim with feedback zeta < w
    zeta = rng.uniform(-0.3, 0.9 * w); iota = rng.uniform(0.05, 0.5)
    x = 0.0
    for _ in range(4000): x = (1 - w + zeta) * x + iota
    gap2_sim = (u * x) ** 2; gap1_sim = abs(u * x)
    if abs(gap2_sim - (iota * u / (eta * u - zeta)) ** 2) > 1e-8 * (1 + gap2_sim): ok = False
    if abs(gap1_sim - iota * u / (eta * u - zeta)) > 1e-8 * (1 + gap1_sim): ok = False
    # C portfolio L2 with stock feedback g < 1 - s(u)
    lam0 = rng.uniform(0.02, 0.3); s = (1 - lam0) * (1 - w) ** 2
    g = rng.uniform(0, 0.9 * (1 - s)); I = rng.uniform(0.05, 0.5)
    D = 0.0
    for _ in range(6000): D = (s + g) * D + I
    gap2p = u * u * D
    if abs(gap2p - u * u * I / (1 - s - g)) > 1e-7 * (1 + gap2p): ok = False
    # D portfolio L1
    sl = (1 - lam0) * (1 - w); gl = rng.uniform(0, 0.9 * (1 - sl)); J = rng.uniform(0.05, 0.5)
    M = 0.0
    for _ in range(6000): M = (sl + gl) * M + J
    gap1p = u * M
    if abs(gap1p - u * J / (1 - sl - gl)) > 1e-7 * (1 + gap1p): ok = False
report("N0a  stationary closed forms (all four cells) vs iterated stationarity", ok)

# --- N0b: conservation loci. A,B flat iff zeta=0; D flat iff g=lam0; C never flat ---
ok = True
ug = np.linspace(0.05, 1.0, 200)
for _ in range(200):
    eta = rng.uniform(0.2, 0.9); iota = 0.2; I = J = 0.2
    lam0 = rng.uniform(0.02, 0.3)
    # A at zeta=0: flat in u
    gA = (iota * ug / (eta * ug)) ** 2
    if gA.max() - gA.min() > 1e-12: ok = False
    # D at g=lam0: gap1 = u J/((1-lam0) eta u) flat
    gD = ug * J / (lam0 - lam0 + (1 - lam0) * eta * ug)
    if gD.max() - gD.min() > 1e-12: ok = False
    # C: never flat for any g in [0, lam0]: strictly increasing in u
    g = rng.uniform(0, lam0)
    den = 1 - (1 - lam0) * (1 - eta * ug) ** 2 - g
    gC = ug * ug * I / den
    if not np.all(np.diff(gC) > 0): ok = False
report("N0b  conservation loci: zeta=0 (single), g=lam0 (L1 portfolio); L2 portfolio never flat", ok)

# --- N0c: cell-C regime structure: global monotone iff g<=lam0; interior min of
#          gap2 at u_c=(g-lam0)/(eta(1-lam0)) for moderate gain; decreasing branch
#          near capture exists; divergence boundary beta_div from 1-s-g=0 ---
ok = True
for _ in range(300):
    eta = rng.uniform(0.25, 0.85); lam0 = rng.uniform(0.03, 0.25); I = 0.2
    case = rng.integers(0, 2)
    if case == 0:
        g = rng.uniform(0, lam0 * 0.95)             # below grounding rate
    else:
        g = rng.uniform(lam0 * 1.1, min(lam0 + eta * (1 - lam0) * 0.9,
                                        1 - (1 - lam0) * (1 - eta) ** 2 - 1e-3))
    den = 1 - (1 - lam0) * (1 - eta * ug) ** 2 - g
    mask = den > 1e-9
    gC = np.where(mask, ug * ug * I / np.where(mask, den, 1), np.nan)
    vals = gC[mask]; us = ug[mask]
    if case == 0:
        if not np.all(np.diff(vals) > 0): ok = False          # monotone in u
    else:
        u_c = (g - lam0) / (eta * (1 - lam0))
        if not (us.min() < u_c < us.max()): continue
        u_min = us[np.nanargmin(vals)]
        if abs(u_min - u_c) > 0.02: ok = False                # interior min at u_c
report("N0c  L2 portfolio: monotone iff g<=lam0; interior gap-minimum at u_c=(g-lam0)/(eta(1-lam0))", ok)

# ============================================================================
# N1: KNOB-FREE CERTIFICATE (monotone small gain)
# Reduced map with stock feedback g:  D' = (s(beta)+g) D + I,
# s(beta) = (1-lam0)(1-eta(1-beta))^2;  U = -v beta - (1-c beta)^2 D.
# G_g(beta) = -v + 2c(1-c beta) I/(1 - s(beta) - g).
# Sufficient certificate (margin):  v (lam0 - g) >= 2 c I  =>  G_g < 0 on (0,1]
# and EVERY sign-consistent adaptation rule converges to calibrated.
# Necessary side: v (lam0 - g) < 2 c (1-c) I => captured corner locally stable.
# ============================================================================

def srate(b, eta, lam0):  return (1 - lam0) * (1 - eta * (1 - b)) ** 2
def Gg(b, p):
    den = 1 - srate(b, p['eta'], p['lam0']) - p['g']
    return -p['v'] + 2 * p['c'] * (1 - p['c'] * b) * p['I'] / den

def draw_loop(zone, tries=400):
    for _ in range(tries):
        eta = rng.uniform(0.25, 0.8); c = rng.uniform(0.55, 0.95)
        lam0 = rng.uniform(0.03, 0.2); g = rng.uniform(0, lam0 * 0.85)
        I = rng.uniform(0.01, 0.06)
        lo = 2 * c * (1 - c) * I / (lam0 - g)      # below: captured stable
        hi = 2 * c * I / (lam0 - g)                # above: certified safe
        if zone == 'A':   v = rng.uniform(hi * 1.02, hi * 2.5)
        elif zone == 'C': v = rng.uniform(lo * 0.3, lo * 0.98)
        else:             v = rng.uniform(lo * 1.02, hi * 0.98)
        alpha = rng.uniform(0.2, 0.95) * (lam0 - g) / (2 * c ** 2 * I)   # (SS_g)
        p = dict(eta=eta, c=c, lam0=lam0, g=g, I=I, v=v, alpha=alpha)
        if zone == 'B' and lo >= hi * 0.98: continue
        return p
    return None

def step_rule(b, D, p, rule='grad', state=None):
    Up = -p['v'] + 2 * p['c'] * (1 - p['c'] * b) * D
    if rule == 'grad':
        b2 = b + p['alpha'] * Up
    elif rule == 'sign':
        b2 = b + 0.01 * np.sign(Up)
    elif rule == 'momentum':
        m = 0.7 * state + p['alpha'] * Up; state = m; b2 = b + m
    elif rule == 'mult':
        b2 = b * (1 + 0.5 * np.tanh(8 * Up)) + 0.02 * max(0.0, np.tanh(8 * Up))
    b2 = min(1.0, max(0.0, b2))
    D2 = max(0.0, (srate(b, p['eta'], p['lam0']) + p['g']) * D + p['I'])
    return b2, D2, (state if rule == 'momentum' else None)

# --- N1a: certificate => G_g < 0 on (0,1] and all rules calibrate from any init ---
ok, n = True, 0
bg = np.linspace(1e-4, 1, 2001)
while n < 60:
    p = draw_loop('A')
    if p is None: continue
    n += 1
    if np.max([Gg(b, p) for b in bg]) >= 0:
        pass  # certificate is sufficient, not necessary for G<0... but bound implies it:
    if not np.all(np.array([Gg(b, p) for b in bg]) < 0): ok = False
    Dmax = p['I'] / (p['lam0'] - p['g'])
    for rule in ('grad', 'sign', 'momentum', 'mult'):
        for (b0, D0) in ((0.9, 2 * Dmax), (0.5, Dmax), (0.99, 0.5 * Dmax)):
            b, D, st = b0, D0, 0.0
            for _ in range(6000):
                b, D, st = step_rule(b, D, p, rule, st)
            if b > 1e-3: ok = False
report("N1a  certificate v(lam0-g)>=2cI: G_g<0 on (0,1]; ALL sign-consistent rules calibrate", ok,
       f"{n} certified draws x 4 rules x 3 inits")

# --- N1b: necessary side: below the capture line, captured corner locally stable ---
ok, n = True, 0
while n < 60:
    p = draw_loop('C')
    if p is None: continue
    n += 1
    if not Gg(1.0, p) > 0: ok = False
    b, D = 1.0, p['I'] / (1 - srate(1, p['eta'], p['lam0']) - p['g'])
    for _ in range(3000): b, D, _ = step_rule(b, D, p, 'grad')
    if b < 1 - 1e-6: ok = False
report("N1b  below capture line v(lam0-g)<2c(1-c)I: captured corner locally stable", ok, f"{n} draws")

# --- N1c: intermediate zone: both fates occur; when max G > 0 with G(1) < 0,
#          the descending crossing is a STABLE PARTIAL-CAPTURE equilibrium ---
ok, fates = True, set()
n = 0
while n < 150:
    # bias toward the interior-max corner: c(lam0-g) > 2 eta (1-lam0)(1-c) feasible
    eta = rng.uniform(0.22, 0.45); c = rng.uniform(0.85, 0.97)
    lam0 = rng.uniform(0.12, 0.3); g = rng.uniform(0, 0.3 * lam0)
    I = rng.uniform(0.01, 0.06)
    lo = 2 * c * (1 - c) * I / (lam0 - g); hi = 2 * c * I / (lam0 - g)
    if lo >= hi * 0.98: continue
    v = rng.uniform(lo * 1.02, lo * 1.02 + (hi - lo) * (0.25 if rng.random() < 0.5 else 0.95))
    alpha = rng.uniform(0.2, 0.9) * (lam0 - g) / (2 * c ** 2 * I)
    p = dict(eta=eta, c=c, lam0=lam0, g=g, I=I, v=v, alpha=alpha)
    n += 1
    Gv = np.array([Gg(b, p) for b in bg])
    if Gv.max() < 0:
        fates.add('global-calibrated')
        b, D, _ = 0.9, 2 * p['I'] / (p['lam0'] - p['g']), None
        for _ in range(8000): b, D, _ = step_rule(b, D, p, 'grad')
        if b > 1e-3: ok = False
    else:
        fates.add('partial-capture-attractor')
        # G(1) < 0 in zone B, so a descending (+ -> -) crossing exists: stable interior eq
        if Gg(1.0, p) >= 0: ok = False; continue
        idx = np.where((Gv[:-1] > 0) & (Gv[1:] <= 0))[0]
        if len(idx) == 0: ok = False; continue
        bs = bg[idx[-1]]
        Ds = p['I'] / (1 - srate(bs, p['eta'], p['lam0']) - p['g'])
        b, D = min(1.0, bs + 0.03), Ds
        for _ in range(12000): b, D, _ = step_rule(b, D, p, 'grad')
        if not (1e-4 < b < 1 - 1e-4 and abs(Gg(b, p)) < 1e-6 and abs(b - bs) < 0.05): ok = False
report("N1c  intermediate zone: both fates; descending G-crossing = stable partial-capture equilibrium",
       ok and len(fates) == 2, f"fates seen: {sorted(fates)}")

# ============================================================================
# N2: GAIN CEILINGS
# Portfolio: captured stock finite iff g < lam0; D*(1) = I/(lam0-g) -> inf.
# Amplitude: at capture, multiplier 1 - eta*e + zeta: diverges iff zeta > eta*e.
# ============================================================================
ok = True
for _ in range(200):
    lam0 = rng.uniform(0.03, 0.3); I = rng.uniform(0.05, 0.4)
    g = rng.uniform(0, 0.8 * lam0) if rng.random() < 0.5 else rng.uniform(1.25 * lam0, 2 * lam0)
    T = min(int(30 / abs(g - lam0)) + 100, 200000)
    D = 1.0
    for _ in range(T): D = ((1 - lam0) + g) * D + I
    if g < lam0:
        if abs(D - I / (lam0 - g)) > 1e-5 * (1 + D): ok = False
    else:
        if D < 1e8: ok = False
    eta = rng.uniform(0.2, 0.9); e = rng.uniform(0.05, 0.9)
    zeta = rng.uniform(0, 0.8 * eta * e) if rng.random() < 0.5 else rng.uniform(1.25 * eta * e, 2 * eta * e)
    T = min(int(30 / abs(zeta - eta * e)) + 100, 200000)
    x = 1.0
    for _ in range(T): x = (1 - eta * e + zeta) * x + 0.1
    if zeta < eta * e:
        if abs(x - 0.1 / (eta * e - zeta)) > 1e-5 * (1 + x): ok = False
    else:
        if x < 1e8: ok = False
report("N2   gain ceilings: portfolio g_c = lam0; amplitude zeta_c = eta*e (divergence iff above)", ok)

# ============================================================================
# N3: LAUNDERING AS OBSERVABILITY FAILURE
# Captured face (beta=1, e_L=0): A = diag(aH, aL), aH = 1-etaH*kap+zeta < 1,
# aL = 1+zeta > 1. Satisfaction output y = -piH (1-dH)^2 xH^2 - piL (1-dL)^2 xL^2;
# linearized C = (dy/dxH, dy/dxL) has dy/dxL = 0 identically at beta=1.
# => unstable mode in unobservable subspace (rank 1). Any epsilon-weighted audit
# sensor restores rank 2; detection latency T ~ ln(1/eps)/ln(1+zeta).
# ============================================================================
etaH, etaL = 0.5, 0.6; kap = 0.5; piH = piL = 0.5; zeta = 0.012
iH, iL = 0.02, -0.02
aH, aL = 1 - etaH * kap + zeta, 1 + zeta            # capture face: w_L(1)=0
xHs = iH / (etaH * kap - zeta)
A = np.diag([aH, aL])
xL0 = iL
C1 = np.array([-2 * piH * kap ** 2 * xHs, 0.0])     # satisfaction sensor: zero weight on L
O1 = np.vstack([C1, C1 @ A])
C2 = np.array([-2 * piH * xHs, -2 * piL * xL0])     # unweighted audit sensor
O2 = np.vstack([C1, C2, C1 @ A, C2 @ A])
r1, r2 = np.linalg.matrix_rank(O1), np.linalg.matrix_rank(O2)
in_kernel = np.allclose(O1 @ np.array([0.0, 1.0]), 0.0)
# calibrated-state contrast (beta=0): satisfaction sensor alone is observable
xLc = iL / (etaL - zeta); xHc = iH / (etaH - zeta)
Cc = np.array([-2 * piH * xHc, -2 * piL * xLc])
Ac = np.diag([1 - etaH + zeta, 1 - etaL + zeta])
Oc = np.vstack([Cc, Cc @ Ac])
rc = np.linalg.matrix_rank(Oc)
# latency law: alarm when eps*piL*xL(t)^2 exceeds theta
theta = 1.0
es, Ts = [], []
for ee in (1e-2, 1e-3, 1e-4, 1e-5, 1e-6):
    x = iL; t = 0
    while ee * piL * x * x < theta and t < 10 ** 6:
        x = aL * x + iL; t += 1
    es.append(np.log(1 / ee)); Ts.append(t)
slope = np.polyfit(es, Ts, 1)[0]
pred = 1 / (2 * np.log(aL))
latfit = np.corrcoef(es, Ts)[0, 1]
lat_ok = abs(slope - pred) / pred < 0.05 and latfit > 0.999
report("N3   capture is an unobservable instability: rank(O)=1, e_L in ker; audit sensor -> rank 2;"
       " calibrated state observable; latency T ~ ln(1/eps)/(2 ln(1+zeta))",
       r1 == 1 and in_kernel and r2 == 2 and rc == 2 and lat_ok,
       f"ranks {r1}/{r2}/{rc}; latency slope {slope:.0f} vs predicted {pred:.0f}")

# ============================================================================
# N4: RATE SEPARATION (adaptation cadence as a regulable)
# Paper-two benchmark (g=0). From a transient init (beta0, D0) above the fast
# separatrix, fate depends on alpha: capture iff alpha > alpha_c; the separatrix
# height D_sep(alpha) increases as alpha decreases, ~ 1/alpha.
# ============================================================================
P2 = dict(eta=0.5, c=0.9, lam0=0.02, g=0.0, I=0.02, v=0.10)
def fate(b0, D0, alpha, p, T=20000):
    b, D = b0, D0
    for _ in range(T):
        Up = -p['v'] + 2 * p['c'] * (1 - p['c'] * b) * D
        b2 = min(1.0, max(0.0, b + alpha * Up))
        D = max(0.0, (srate(b, p['eta'], p['lam0']) + p['g']) * D + p['I'])
        b = b2
    return b > 0.5
def Dsep(alpha, p, b0=0.4):
    lo, hi = 0.0, 80.0
    if fate(b0, lo, alpha, p) or not fate(b0, hi, alpha, p): return np.nan
    for _ in range(40):
        mid = 0.5 * (lo + hi)
        if fate(b0, mid, alpha, p): hi = mid
        else: lo = mid
    return 0.5 * (lo + hi)
alphas = [0.6, 0.3, 0.15, 0.075]
seps = [Dsep(a, P2) for a in alphas]
mono = np.all(np.diff(seps) > 0)
prods = [a * s for a, s in zip(alphas, seps)]
scale_ok = max(prods) / min(prods) < 3.0
# capture iff alpha above threshold at fixed transient init
b0, D0 = 0.4, 2.0
fates4 = [fate(b0, D0, a, P2) for a in (0.6, 0.3, 0.1, 0.04, 0.015)]
thresh_ok = fates4[0] and not fates4[-1] and fates4 == sorted(fates4, reverse=True)
report("N4   rate separation: D_sep increases as alpha falls (~1/alpha); capture iff alpha > alpha_c",
       mono and scale_ok and thresh_ok,
       f"D_sep(0.6..0.075) = {', '.join(f'{s:.2f}' for s in seps)}; alpha*D_sep = "
       f"{', '.join(f'{x:.2f}' for x in prods)}")

# ============================================================================
# N5: IDENTIFICATION PIPELINE
# Simulated contested-stream panel -> (lam0_hat, eta_hat, g_hat) -> certificate
# margin -> verified out-of-sample fate prediction.
# ============================================================================
def simulate_panel(eta, lam0, g, I0, T=600, seed=0):
    G = np.random.default_rng(9000 + seed)
    beta = 0.45 + 0.30 * np.sin(np.arange(T) / 40)
    claims, Dagg = [], I0 / lam0
    rows_u, rows_r, arr_X, arr_Y, deaths, exposure = [], [], [], [], 0, 0
    for t in range(T):
        w = eta * (1 - beta[t])
        survivors = []
        for x in claims:
            exposure += 1
            if G.random() < lam0: deaths += 1
            else:
                x2 = (1 - w) ** 2 * x
                rows_u.append(1 - beta[t]); rows_r.append(np.sqrt(x2 / x))
                survivors.append(x2)
        claims = survivors
        mean_mass = I0 + g * Dagg
        nk = 3
        for _ in range(nk):
            claims.append(G.gamma(6.0, mean_mass / (nk * 6.0)))
        arr_X.append(Dagg); arr_Y.append(sum(claims[-nk:]))
        Dagg = sum(claims)
    lam_hat = deaths / max(exposure, 1)
    eta_hat = -np.polyfit(np.array(rows_u), np.array(rows_r), 1)[0]
    Xa, Ya = np.array(arr_X[40:]), np.array(arr_Y[40:])
    cf = np.polyfit(Xa, Ya, 1)
    return lam_hat, eta_hat, cf[0], cf[1]

ok_id, errs = True, []
for k in range(30):
    eta = rng.uniform(0.3, 0.8); lam0 = rng.uniform(0.06, 0.2)
    g = rng.uniform(0, 0.6 * lam0); I0 = rng.uniform(0.05, 0.2)
    lh, eh, gh, I0h = simulate_panel(eta, lam0, g, I0, seed=k)
    errs.append((abs(lh - lam0) / lam0, abs(eh - eta) / eta,
                 abs(gh - g) / lam0, abs(I0h - I0) / I0))
e = np.array(errs).mean(axis=0)
ok_id = e[0] < 0.15 and e[1] < 0.05 and e[2] < 0.25 and e[3] < 0.25
# certificate pipeline: estimates -> margin -> out-of-sample fate prediction
ok_pred, n_pred = True, 0
for k in range(40):
    eta = rng.uniform(0.3, 0.75); lam0 = rng.uniform(0.08, 0.18)
    g = rng.uniform(0, 0.5 * lam0); I0 = rng.uniform(0.04, 0.12)
    c = rng.uniform(0.6, 0.9)
    lh, eh, gh, I0h = simulate_panel(eta, lam0, g, I0, seed=100 + k)
    if rng.random() < 0.5:
        v = 1.4 * 2 * c * I0h / max(lh - gh, 1e-3)            # estimated-certified
        margin = v * (lh - gh) - 2 * c * I0h
        p = dict(eta=eta, c=c, lam0=lam0, g=g, I=I0, v=v)
        alpha = 0.5 * (lam0 - g) / (2 * c ** 2 * I0)
        captured = fate(0.9, 3 * I0 / (lam0 - g), alpha, p, T=30000)
        if margin > 0 and captured: ok_pred = False
        n_pred += 1
    else:
        v = 0.55 * 2 * c * (1 - c) * I0h / max(lh - gh, 1e-3)  # estimated-capturable
        p = dict(eta=eta, c=c, lam0=lam0, g=g, I=I0, v=v)
        alpha = 0.5 * (lam0 - g) / (2 * c ** 2 * I0)
        captured = fate(1.0, I0 / (lam0 - g), alpha, p, T=10000)
        if not captured: ok_pred = False
        n_pred += 1
report("N5   identification: (lam0, eta, g) recovered from panels; estimated certificate "
       "predicts true fate out of sample", ok_id and ok_pred,
       f"mean errs lam0/eta/g/I0 = {e[0]:.2f}/{e[1]:.3f}/{e[2]:.2f}/{e[3]:.2f}; {n_pred} fate predictions")

# ============================================================================
# N6: SINGULAR-PERTURBATION LIMIT OF THE SEPARATRIX
# As alpha -> 0 with E0 = kappa/alpha, the transit becomes the alpha-free
# JUMP MAP  (beta, Et) -> (beta + A(beta) Et,  sigma(beta) Et),
# A = 2c(1-c beta), sigma = s + g.  kappa*(beta0) = separatrix scale of the
# jump map; then  alpha (D_sep - D*(beta0)) -> kappa*.  The continuum integral
#   K(beta0) = int_{beta0}^{beta_saddle} (1 - s - g) / (2c(1-cb)) db
# is an upper bound, tight when jumps are small (beta0 near the saddle).
# ============================================================================
from scipy.integrate import quad
from scipy.optimize import brentq
p6 = P2
bsad = brentq(lambda b: Gg(b, dict(p6, alpha=0)), 0.5, 0.999)
def Kint(b0):
    val, _ = quad(lambda b: (1 - srate(b, p6['eta'], p6['lam0']) - p6['g'])
                  / (2 * p6['c'] * (1 - p6['c'] * b)), b0, bsad)
    return val
def kappa_star(b0):
    def crosses(E0):
        b, E = b0, E0
        for _ in range(6000):
            b2 = b + 2 * p6['c'] * (1 - p6['c'] * b) * E
            E *= srate(b, p6['eta'], p6['lam0']) + p6['g']
            b = b2
            if b >= bsad: return True
            if E < 1e-14: return False
        return False
    lo, hi = 0.0, 3.0
    for _ in range(60):
        mid = 0.5 * (lo + hi)
        if crosses(mid): hi = mid
        else: lo = mid
    return 0.5 * (lo + hi)

def fate_decisive(b0, D0, a, p, Tmax):
    b, D = b0, D0
    for _ in range(Tmax):
        Up = -p['v'] + 2 * p['c'] * (1 - p['c'] * b) * D
        b2 = min(1.0, max(0.0, b + a * Up))
        D = max(0.0, (srate(b, p['eta'], p['lam0']) + p['g']) * D + p['I'])
        b = b2
        if b > 0.999: return True
        if b < 0.02: return False
    return b > 0.5

K6, ks6 = Kint(0.4), kappa_star(0.4)
Dbar0 = p6['I'] / (1 - srate(0.4, p6['eta'], p6['lam0']) - p6['g'])
alphas6 = [0.6, 0.3, 0.15, 0.075, 0.0375, 0.01875]
prods6 = []
for a in alphas6:
    Tmax = int(min(25000 + 900 / a, 150000))
    lo, hi = 0.0, 200.0
    for _ in range(42):
        mid = 0.5 * (lo + hi)
        if fate_decisive(0.4, mid, a, p6, Tmax): hi = mid
        else: lo = mid
    prods6.append(a * (0.5 * (lo + hi) - Dbar0))
mono6 = all(prods6[i] > prods6[i + 1] - 1e-9 for i in range(len(prods6) - 1))
extrap = 2 * prods6[-1] - prods6[-2]
# continuum-agreement: beta0 near the saddle => small jumps => kappa* ~ K
K9, ks9 = Kint(0.9), kappa_star(0.9)
ok6 = (mono6 and abs(ks6 - K6) / K6 < 0.05
       and abs(extrap - ks6) / ks6 < 0.05 and abs(prods6[-1] - ks6) / ks6 < 0.08
       and abs(ks9 - K9) / K9 < 0.05)
report("N6   separatrix limit: alpha*(D_sep - D*) -> kappa* of the explicit jump map;"
       " integral K approximates kappa*, tight near the saddle", ok6,
       f"kappa* = {ks6:.4f}, K = {K6:.4f}; products = "
       f"{', '.join(f'{x:.3f}' for x in prods6)}; extrap = {extrap:.4f};"
       f" near-saddle kappa*/K = {ks9:.4f}/{K9:.4f}")

# ============================================================================
# N7: EXACT NONLINEAR INDISTINGUISHABILITY ON THE CAPTURED FACE
# Diagonal dynamics + output independent of x_L: the full nonlinear
# satisfaction output sequence is a function of x_H alone. Any two states
# differing only in x_L are indistinguishable for all time; the epsilon-sensor
# separates them.
# ============================================================================
etaH7, kap7, zeta7 = 0.5, 0.5, 0.012
iH7, iL7 = 0.02, -0.02
piH7 = piL7 = 0.5
def face_step(xH, xL):
    return (1 - etaH7 * kap7 + zeta7) * xH + iH7, (1 + zeta7) * xL + iL7
def y_sat(xH, xL): return -piH7 * kap7 ** 2 * xH ** 2 - piL7 * 0.0 * xL ** 2
def y_eps(xH, xL, ee): return y_sat(xH, xL) - ee * piL7 * xL ** 2
xH, xLa, xLb = 0.05, -0.3, 0.7
max_dev, eps_gap = 0.0, []
xh1, xl1, xh2, xl2 = xH, xLa, xH, xLb
for t in range(400):
    max_dev = max(max_dev, abs(y_sat(xh1, xl1) - y_sat(xh2, xl2)))
    eps_gap.append(abs(y_eps(xh1, xl1, 1e-3) - y_eps(xh2, xl2, 1e-3)))
    xh1, xl1 = face_step(xh1, xl1); xh2, xl2 = face_step(xh2, xl2)
rate7 = np.log(eps_gap[-1] / eps_gap[-31]) / 30
ok7 = (max_dev == 0.0 and all(np.diff(eps_gap[-50:]) > 0)
       and abs(rate7 - 2 * np.log(1 + zeta7)) / (2 * np.log(1 + zeta7)) < 0.05)
report("N7   exact nonlinear indistinguishability: satisfaction outputs identical for all t;"
       " epsilon-sensor separates and grows", ok7,
       f"max satisfaction deviation = {max_dev}; tail growth rate {rate7:.4f} vs 2ln(1+zeta) = {2*np.log(1+zeta7):.4f}")

# ============================================================================
# N8: ESTIMATOR ASYMPTOTICS AND THE SAFE-SIDE CERTIFICATION RULE
# (a) RMSE of (lam0, eta, g, I0) scales ~ 1/sqrt(T).
# (b) Delta-method margin SE; rule "certify iff m_hat - 2 SE > 0" never
#     certifies a truly capturable loop, and retains power when margin large.
# ============================================================================
def simulate_panel_se(eta, lam0, g, I0, T, seed):
    G = np.random.default_rng(50000 + seed)
    beta = 0.45 + 0.30 * np.sin(np.arange(T) / 40)
    claims, Dagg = [], I0 / lam0
    arr_X, arr_Y, deaths, exposure = [], [], 0, 0
    rows_u, rows_r = [], []
    for t in range(T):
        w = eta * (1 - beta[t])
        survivors = []
        for x in claims:
            exposure += 1
            if G.random() < lam0: deaths += 1
            else:
                x2 = (1 - w) ** 2 * x
                rows_u.append(1 - beta[t]); rows_r.append(np.sqrt(x2 / x))
                survivors.append(x2)
        claims = survivors
        mean_mass = I0 + g * Dagg
        nk = 3
        for _ in range(nk):
            claims.append(G.gamma(6.0, mean_mass / (nk * 6.0)))
        arr_X.append(Dagg); arr_Y.append(sum(claims[-nk:]))
        Dagg = sum(claims)
    lam_hat = deaths / max(exposure, 1)
    se_lam = np.sqrt(lam_hat * (1 - lam_hat) / max(exposure, 1))
    eta_hat = -np.polyfit(np.array(rows_u), np.array(rows_r), 1)[0]
    Xa, Ya = np.array(arr_X[40:]), np.array(arr_Y[40:])
    Xd = np.column_stack([Xa, np.ones_like(Xa)])
    coef, res, _, _ = np.linalg.lstsq(Xd, Ya, rcond=None)
    nobs = len(Ya); sig2 = float(res[0]) / (nobs - 2) if len(res) else np.var(Ya - Xd @ coef) * nobs / (nobs - 2)
    cov = sig2 * np.linalg.inv(Xd.T @ Xd)
    return lam_hat, eta_hat, coef[0], coef[1], se_lam, cov

Ts8 = [300, 600, 1200, 2400]
rmse = []
for T in Ts8:
    errs = []
    for r in range(24):
        eta = 0.55; lam0 = 0.12; g = 0.05; I0 = 0.08
        lh, eh, gh, Ih, _, _ = simulate_panel_se(eta, lam0, g, I0, T, seed=T + r)
        errs.append([(lh - lam0) ** 2, (eh - eta) ** 2, (gh - g) ** 2, (Ih - I0) ** 2])
    rmse.append(np.sqrt(np.mean(errs, axis=0)))
rmse = np.array(rmse)
slopes = [np.polyfit(np.log(Ts8), np.log(rmse[:, j]), 1)[0] for j in range(4)]
# eta_hat is regression-exact by construction (within-claim contraction ratios
# are noiseless), so its RMSE is floating-point dust and carries no rate law:
# assert exactness directly, and the T^(-1/2) law for the three noisy estimators.
ok8a = all(-0.75 < slopes[j] < -0.3 for j in (0, 2, 3)) and bool(np.all(rmse[:, 1] < 1e-10))
# safe-side rule
false_cert, n_cap, power, n_safe = 0, 0, 0, 0
for k in range(40):
    eta = rng.uniform(0.35, 0.7); lam0 = rng.uniform(0.08, 0.18)
    g = rng.uniform(0, 0.5 * lam0); I0 = rng.uniform(0.04, 0.12); c = rng.uniform(0.6, 0.9)
    danger = rng.random() < 0.5
    if danger:
        v = rng.uniform(0.3, 0.9) * 2 * c * (1 - c) * I0 / (lam0 - g)   # capturable: below capture line
    else:
        v = rng.uniform(1.6, 2.6) * 2 * c * I0 / (lam0 - g)             # comfortably certified
    lh, eh, gh, Ih, se_lam, cov = simulate_panel_se(eta, lam0, g, I0, 600, seed=777 + k)
    m_hat = v * (lh - gh) - 2 * c * Ih
    var_m = (v ** 2) * (se_lam ** 2 + cov[0, 0]) + (2 * c) ** 2 * cov[1, 1]             + 2 * (-v) * (2 * c) * (-1) * cov[0, 1]
    se_m = np.sqrt(max(var_m, 0))
    certify = m_hat - 2 * se_m > 0
    if danger:
        n_cap += 1
        if certify: false_cert += 1
    else:
        n_safe += 1
        if certify: power += 1
ok8b = false_cert == 0 and power / max(n_safe, 1) >= 0.8
report("N8   inference: RMSE ~ T^(-1/2); safe-side rule (certify iff m - 2SE > 0): zero false"
       " certifications, power retained", ok8a and ok8b,
       f"slopes (lam0,g,I0) = {slopes[0]:.2f}, {slopes[2]:.2f}, {slopes[3]:.2f};"
       f" eta exact (max RMSE {rmse[:, 1].max():.1e}); false certs {false_cert}/{n_cap},"
       f" power {power}/{n_safe}")

# ============================================================================
# N9: NETWORK CERTIFICATE (spectral generalization)
# Stock law D' = (S(beta) + Gm) D + I, S = diag(s_k(beta_k)), Gm >= 0.
# Policy-free bound: D <= R := (Id - Sbar - Gm)^{-1} I  whenever rho(Sbar+Gm)<1,
# Sbar = diag(1-lam0k). Certificate: v_k >= 2 c_k R_k for all k  =>  every
# sign-consistent per-community rule calibrates. Ceiling: divergence at full
# capture iff rho(Sbar + Gm) >= 1. Scalar case recovers v(lam0-g) >= 2cI.
# ============================================================================
ok9 = True
for trial in range(40):
    Kn = 4
    lam = rng.uniform(0.05, 0.25, Kn); etan = rng.uniform(0.3, 0.7, Kn)
    cn = rng.uniform(0.6, 0.9, Kn)
    Gm = rng.uniform(0, 1, (Kn, Kn)); Gm *= rng.uniform(0.2, 0.8) * np.min(lam) / np.max(Gm.sum(axis=1))
    Sbar = np.diag(1 - lam)
    rho = max(abs(np.linalg.eigvals(Sbar + Gm)))
    if rho >= 1: continue
    Ivec = rng.uniform(0.01, 0.05, Kn)
    R = np.linalg.solve(np.eye(Kn) - Sbar - Gm, Ivec)
    # (a) policy-free bound along an adversarial random beta-path
    D = 5 * R
    for t in range(4000):
        b = rng.uniform(0, 1, Kn)
        S = np.diag((1 - lam) * (1 - etan * (1 - b)) ** 2)
        D = (S + Gm) @ D + Ivec
    if not np.all(D <= R * (1 + 1e-6)): ok9 = False
    # (b) certificate => sign-consistent multi-knob rules calibrate
    v = 2 * cn * R * rng.uniform(1.05, 1.6, Kn)
    alph = 0.3 * np.min(lam - Gm.sum(axis=1)) / (2 * np.max(cn) ** 2 * np.max(R))
    for rule in ('grad', 'sign'):
        b = rng.uniform(0.5, 1, Kn); D = 3 * R
        for t in range(8000):
            grad = -v + 2 * cn * (1 - cn * b) * D
            if rule == 'grad': b = np.clip(b + alph * grad, 0, 1)
            else: b = np.clip(b + 0.005 * np.sign(grad), 0, 1)
            S = np.diag((1 - lam) * (1 - etan * (1 - b)) ** 2)
            D = (S + Gm) @ D + Ivec
        if np.max(b) > 5e-3: ok9 = False
# (c) spectral ceiling at full capture
for trial in range(40):
    Kn = 4
    lam = rng.uniform(0.05, 0.25, Kn)
    Gm = rng.uniform(0, 1, (Kn, Kn)); Sbar = np.diag(1 - lam)
    target = rng.choice([0.85, 1.18])
    rho0 = max(abs(np.linalg.eigvals(Sbar + Gm)))
    Gm *= 1.0  # scale Gm so that rho(Sbar+Gm) hits target
    lo_s, hi_s = 0.0, 10.0
    for _ in range(60):
        mid = 0.5 * (lo_s + hi_s)
        if max(abs(np.linalg.eigvals(Sbar + mid * Gm))) < target: lo_s = mid
        else: hi_s = mid
    Gs = 0.5 * (lo_s + hi_s) * Gm
    rho = max(abs(np.linalg.eigvals(Sbar + Gs)))
    Ivec = np.full(Kn, 0.02)
    D = np.ones(Kn)
    T = min(int(40 / abs(rho - 1)) + 100, 120000)
    for t in range(T): D = (Sbar + Gs) @ D + Ivec
    if rho < 1 and np.max(D) > 1e7: ok9 = False
    if rho > 1 and np.max(D) < 1e7: ok9 = False
# (d) scalar recovery
lam0s, gs_, Is_ = 0.15, 0.06, 0.03
Rs = np.linalg.solve(np.array([[1 - (1 - lam0s) - gs_]]), np.array([Is_]))[0]
ok9 = ok9 and abs(Rs - Is_ / (lam0s - gs_)) < 1e-12
report("N9   network certificate: D <= (Id-Sbar-Gm)^{-1} I policy-free; v_k >= 2 c_k R_k"
       " calibrates all rules; divergence iff rho(Sbar+Gm) >= 1; scalar case recovered", ok9)

print()
print(f"{'='*70}")
print(f"LOOPS DE-RISK RESULT: {sum(PASS)}/{len(PASS)} suites pass")
