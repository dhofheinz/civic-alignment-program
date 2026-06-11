"""De-risking numerics for 'Civic Drift: Threshold Dynamics of Satisfaction-Optimized Deference'.

Every conjectured theorem gets a numerical witness before any prose is written.
Pillar 1: continuous-type statics.  Pillar 2: repeated exposure / horizon.
Pillar 3: endogenous deference dynamics (bistability, hysteresis, early warning).
"""
import numpy as np
rng = np.random.default_rng(11)
PASS = []

def report(name, ok, detail=""):
    PASS.append(ok)
    print(f"{'PASS' if ok else 'FAIL'}  {name}" + (f"  [{detail}]" if detail else ""))

# ============================================================================
# PILLAR 1: CONTINUOUS TYPES
# Generalized model: types tau ~ pi (discrete grid), extraction e(tau) in [0,1),
# d_tau(beta) = (1-e)beta, w_tau(beta) = eta(1-(1-e)beta), r = eta(1-e).
# mu'_tau - m = A_tau + B_tau*beta,  A = (1-eta)(mu-m),  B = r(mu-m).
# S(beta) := Var_tau(mu'_tau) = Var(A) + 2Cov(A,B)beta + Var(B)beta^2.
# ============================================================================

def draw_field(K, straddle=None, comonotone=False):
    """Random discrete type field satisfying A1 (dm < d_tau) and dilution a.e."""
    theta = float(rng.integers(0, 2))
    m = rng.uniform(0.05, 0.95)
    pi = rng.dirichlet(np.ones(K))
    if straddle is True:
        # half the types on each side of m
        lo = rng.uniform(0.02, m - 0.02, K // 2)
        hi = rng.uniform(m + 0.02, 0.98, K - K // 2)
        mu = np.concatenate([lo, hi])
    else:
        mu = rng.uniform(0.02, 0.98, K)
    sig = rng.uniform(0, 0.15, K)
    dm = (m - theta) ** 2
    dt = sig ** 2 + (mu - theta) ** 2
    # enforce A1: resample mu/sig where violated (push mu away from theta)
    bad = dt <= dm
    tries = 0
    while bad.any() and tries < 200:
        mu[bad] = np.clip(theta + np.sign(mu[bad] - theta + 1e-9) *
                          (np.sqrt(dm) + rng.uniform(0.05, 0.5, bad.sum())), 0.02, 0.98)
        dt = sig ** 2 + (mu - theta) ** 2
        bad = dt <= dm
        tries += 1
    if bad.any():
        return None
    gam = (m - theta) * (mu - theta)
    eta = rng.uniform(0.02, dt / (dt + dm))            # dilution a.e.
    e = rng.uniform(0, 0.95, K)                         # extraction in [0,0.95]
    if comonotone:
        # make A(tau), B(tau) comonotone: sort both by a common index
        order = np.argsort((1 - eta) * (mu - m))
        # reorder r so B sorts the same way as A
        r = eta * (1 - e)
        rB = np.sort(r * (mu - m))[np.argsort(np.argsort((1 - eta)[order] * (mu - m)[order]))]
        # simpler: rebuild e so that B is increasing along A's order
        # (construct B values directly comonotone with A, then back out nothing —
        #  we only need the (A,B) pair for the covariance test)
        A = (1 - eta) * (mu - m)
        idx = np.argsort(A)
        Bvals = np.sort(eta * (1 - e) * (mu - m))
        B = np.empty(K); B[idx] = Bvals
        return dict(theta=theta, m=m, pi=pi, mu=mu, sig=sig, dm=dm, dt=dt,
                    gam=gam, eta=eta, e=e, A=A, B=B)
    A = (1 - eta) * (mu - m)
    B = eta * (1 - e) * (mu - m)
    return dict(theta=theta, m=m, pi=pi, mu=mu, sig=sig, dm=dm, dt=dt,
                gam=gam, eta=eta, e=e, A=A, B=B)

def wfield(F, b):
    return F['eta'] * (1 - (1 - F['e']) * b)

def S_direct(F, b):
    mup = F['m'] + (1 - wfield(F, b)) * (F['mu'] - F['m'])
    mbar = np.sum(F['pi'] * mup)
    return np.sum(F['pi'] * (mup - mbar) ** 2)

def wvar(p, x):
    mx = np.sum(p * x); return np.sum(p * (x - mx) ** 2)

def wcov(p, x, y):
    return np.sum(p * (x - np.sum(p * x)) * (y - np.sum(p * y)))

# --- P1a: S(beta) quadratic identity (exact) ---
ok = True
for _ in range(300):
    F = draw_field(50)
    if F is None: continue
    VA, VB = wvar(F['pi'], F['A']), wvar(F['pi'], F['B'])
    CAB = wcov(F['pi'], F['A'], F['B'])
    for b in np.linspace(0, 1, 7):
        lhs = S_direct(F, b); rhs = VA + 2 * CAB * b + VB * b * b
        if abs(lhs - rhs) > 1e-12 * (1 + abs(rhs)): ok = False
report("P1a  S(beta) = Var(A) + 2Cov(A,B)b + Var(B)b^2  (exact identity)", ok)

# --- P1b: S non-decreasing on [0,1] <=> Cov(A,B) >= 0 ---
ok, n_neg = True, 0
for _ in range(800):
    F = draw_field(40)
    if F is None: continue
    CAB = wcov(F['pi'], F['A'], F['B'])
    VB = wvar(F['pi'], F['B'])
    B = np.linspace(0, 1, 101)
    Sv = np.array([S_direct(F, b) for b in B])
    if CAB >= 0 and not np.all(np.diff(Sv) > -1e-14): ok = False
    if CAB < -1e-10:
        n_neg += 1
        # quadratic decreases until beta = -Cov/Var(B); test at half that point
        eps_star = 0.5 * min(1.0, abs(CAB) / max(VB, 1e-300))
        if S_direct(F, eps_star) - S_direct(F, 0.0) >= 0: ok = False
report("P1b  S nondecreasing <=> Cov(A,B)>=0 (quadratic, convex)", ok, f"{n_neg} negative-Cov draws exercised")

# --- P1c: two-type straddle => Cov >= 0 ---
ok = True
for _ in range(5000):
    m = rng.uniform(0.1, 0.9)
    xH, xL = rng.uniform(0.01, 1 - m), -rng.uniform(0.01, m)   # straddle deviations
    etaH, etaL = rng.uniform(0.01, 1, 2)
    eH, eL = rng.uniform(0, 1), rng.uniform(0, 0.99)            # r_L>0
    piH = rng.uniform(0.05, 0.95)
    A = np.array([(1 - etaH) * xH, (1 - etaL) * xL])
    B = np.array([etaH * (1 - eH) * xH, etaL * (1 - eL) * xL])
    p = np.array([piH, 1 - piH])
    if wcov(p, A, B) < -1e-14: ok = False
report("P1c  two-type straddle => Cov(A,B) >= 0", ok)

# --- P1d: comonotone A,B => Cov >= 0 (Chebyshev) ---
ok = True
for _ in range(500):
    F = draw_field(40, comonotone=True)
    if F is None: continue
    if wcov(F['pi'], F['A'], F['B']) < -1e-13: ok = False
report("P1d  comonotone A(tau),B(tau) => Cov >= 0", ok)

# --- P1e: continuous-type capacity theorem ---
def C_cont(F, b, lam, nu):
    w = wfield(F, b)
    mse = (1 - w) ** 2 * F['dt'] + w ** 2 * F['dm'] + 2 * w * (1 - w) * F['gam']
    W = np.sum(F['pi'] * (1 - w) ** 2 * F['sig'] ** 2)
    return -np.sum(F['pi'] * mse) - lam * W - nu * S_direct(F, b)

ok = True
for _ in range(400):
    F = draw_field(40, straddle=True)
    if F is None: continue
    CAB = wcov(F['pi'], F['A'], F['B'])
    if CAB < 0: continue            # theorem hypothesis
    lam, nu = rng.uniform(0.1, 3, 2)
    B = np.linspace(0, 1, 41)
    Cv = np.array([C_cont(F, b, lam, nu) for b in B])
    if not np.all(np.diff(Cv) < 0): ok = False
report("P1e  continuous-type Theorem A: C strictly decreasing under Cov>=0 + dilution a.e.", ok)

# --- P1f: paper-one counterexample embeds as negative covariance ---
p = np.array([0.5, 0.5])
A = np.array([(1 - .5) * (0.6 - 0.1), (1 - .5) * (0.5 - 0.1)])
B = np.array([.5 * (1 - .5) * (0.6 - 0.1), .5 * (1 - 0) * (0.5 - 0.1)])
cov_ce = wcov(p, A, B)
report("P1f  paper-one same-side counterexample has Cov(A,B) < 0", cov_ce < 0,
       f"Cov = {cov_ce:.7f}, S'(0) = {2*cov_ce:.7f} (paper: g(0)g'(0)/2 = {0.5*0.05*-0.075:.7f})")

# --- P1g: harm density mg(tau) = 2 r(tau) h_tau(beta) ---
ok, eps = True, 1e-7
for _ in range(300):
    F = draw_field(30)
    if F is None: continue
    for b in (0.13, 0.5, 0.87):
        w = wfield(F, b)
        h = (F['dt'] - F['gam']) - w * (F['dt'] + F['dm'] - 2 * F['gam'])
        an = 2 * F['eta'] * (1 - F['e']) * h
        wp, wm = wfield(F, b + eps), wfield(F, b - eps)
        q = lambda w: (1 - w) ** 2 * F['dt'] + w ** 2 * F['dm'] + 2 * w * (1 - w) * F['gam']
        fd = (q(wp) - q(wm)) / (2 * eps)
        if np.max(np.abs(fd - an)) > 1e-5 * (1 + np.max(np.abs(an))): ok = False
report("P1g  harm density mg(tau) = 2 r(tau) h_tau(beta)  (per-type, finite diff)", ok)

# ============================================================================
# PILLAR 2: REPEATED EXPOSURE (fixed event, t updates, same beta)
# W_t = 1-(1-w)^t ;  MSE_t = q(W_t) ;  T* = ln(1-w*)/ln(1-eta)
# ============================================================================

def qfun(W, dt, dm, gam):
    return (1 - W) ** 2 * dt + W ** 2 * dm + 2 * W * (1 - W) * gam

# --- P2a: t-step closed form vs exact moment recursion ---
ok = True
for _ in range(400):
    theta = float(rng.integers(0, 2)); m = rng.uniform(0.05, 0.95)
    mu = rng.uniform(0.02, 0.98); sig = rng.uniform(0, 0.2)
    dm = (m - theta) ** 2; dt = sig ** 2 + (mu - theta) ** 2
    if dm >= dt: continue
    gam = (m - theta) * (mu - theta)
    eta = rng.uniform(0.05, dt / (dt + dm)); e = rng.uniform(0, 0.9)
    b = rng.uniform(0, 1); w = eta * (1 - (1 - e) * b)
    et, gt = dt, gam
    for t in range(1, 13):
        et = (1 - w) ** 2 * et + 2 * (1 - w) * w * gt + w ** 2 * dm
        gt = (1 - w) * gt + w * dm
        Wt = 1 - (1 - w) ** t
        if abs(et - qfun(Wt, dt, dm, gam)) > 1e-12 * (1 + et): ok = False
report("P2a  MSE_t = q(1-(1-w)^t)  (exact vs moment recursion)", ok)

# --- P2b: horizon threshold. Finite T* iff gamma < delta_m (w* < 1);
#          when gamma >= delta_m (mean beyond evidence) no inversion at any horizon ---
ok, n_flip, n_noinv = True, 0, 0
for _ in range(600):
    theta = 0.0
    m = rng.uniform(0.2, 0.6)
    if rng.random() < 0.7:
        # inverting configuration: prior mean between truth and evidence => gamma < delta_m
        mu = rng.uniform(0.02, m - 0.05)
        sig2 = (m * m - mu * mu) + rng.uniform(0.01, 0.12)
    else:
        # non-inverting: mean beyond evidence => gamma >= delta_m, T* = +infinity
        mu = rng.uniform(m + 0.05, 0.95)
        sig2 = rng.uniform(0.0, 0.04)
    dm = m * m; dt = sig2 + mu * mu
    if dm >= dt: continue
    gam = m * mu
    a = dt + dm - 2 * gam
    wstar = (dt - gam) / a
    eta = rng.uniform(0.1, min(0.95, dt / (dt + dm)))
    eps = 1e-6
    def dmse0(t):
        def f(b):
            w = eta * (1 - b); return qfun(1 - (1 - w) ** t, dt, dm, gam)
        return (f(eps) - f(0)) / eps
    if wstar >= 1.0:                       # case (ii): no inversion ever
        n_noinv += 1
        for t in (1, 3, 8):
            if dmse0(t) <= 0: ok = False
        # analytic large-t check: W_t(0) < 1 <= w* for all t
        if not all(wstar > 1 - (1 - eta) ** t for t in (50, 200)): ok = False
        continue
    Tstar = np.log(1 - wstar) / np.log(1 - eta)
    n_flip += 1
    tlo, thi = int(np.floor(Tstar)), int(np.ceil(Tstar)) + 1
    if tlo >= 1 and Tstar - tlo > 1e-6 and dmse0(tlo) <= 0: ok = False
    if thi - Tstar > 1e-6 and dmse0(thi) >= 0: ok = False
report("P2b  T* finite iff gamma<delta_m: sign flips at T*=ln(1-w*)/ln(1-eta); else monotone harm",
       ok, f"{n_flip} finite-T* + {n_noinv} no-inversion configs")

# --- P2c: accuracy-optimal beta*(t) closed form (e=0 type), increasing in t ---
ok = True
for _ in range(200):
    theta = 0.0; m = rng.uniform(0.25, 0.6)
    mu = rng.uniform(0.02, m - 0.08)
    sig2 = (m * m - mu * mu) + rng.uniform(0.02, 0.12)
    dm, dt_ = m * m, sig2 + mu * mu
    gam = m * mu; a = dt_ + dm - 2 * gam; wstar = (dt_ - gam) / a
    eta = rng.uniform(0.25, min(0.95, dt_ / (dt_ + dm)))
    Tstar = np.log(1 - wstar) / np.log(1 - eta)
    prev = -1.0
    for t in range(int(np.ceil(Tstar)) + 1, int(np.ceil(Tstar)) + 8):
        bstar = 1 - (1 - (1 - wstar) ** (1 / t)) / eta
        if not (0 <= bstar <= 1): continue
        grid = np.linspace(0, 1, 4001)
        msev = qfun(1 - (1 - eta * (1 - grid)) ** t, dt_, dm, gam)
        bnum = grid[np.argmin(msev)]
        if abs(bstar - bnum) > 5e-4: ok = False
        if bstar < prev - 1e-12: ok = False           # increasing in t
        prev = bstar
report("P2c  beta*_acc(t) = 1 - [1-(1-w*)^(1/t)]/eta, increasing in t  (inverting regime)", ok)

# --- P2d: inversion bands ---
# (a) credulity band: shared (mu, sigma) => shared w*<1; eta_L > eta_H =>
#     T*_L < T*_H; for t in (T*_L, T*_H) deference helps L and harms H.
ok, bands = True, 0
for _ in range(400):
    theta = 0.0; m = rng.uniform(0.25, 0.6)
    mu = rng.uniform(0.02, m - 0.08); sig2 = (m * m - mu * mu) + rng.uniform(0.02, 0.12)
    dm, dt_ = m * m, sig2 + mu * mu; gam = m * mu
    wstar = (dt_ - gam) / (dt_ + dm - 2 * gam)
    cap = dt_ / (dt_ + dm)
    etaH = rng.uniform(0.12, cap * 0.55)
    etaL = rng.uniform(min(etaH * 1.4, cap * 0.99), cap)
    if etaL <= etaH: continue
    kap = rng.uniform(0.05, 0.9)
    TL = np.log(1 - wstar) / np.log(1 - etaL)
    TH = np.log(1 - wstar) / np.log(1 - etaH)
    if TH - TL < 1.5: continue
    t = int(np.ceil(TL)) + max(1, int((TH - TL) / 3))
    if not (TL < t < TH): continue
    eps = 1e-6
    def d0(eta, e, t):
        def f(b):
            w = eta * (1 - (1 - e) * b); return qfun(1 - (1 - w) ** t, dt_, dm, gam)
        return (f(eps) - f(0)) / eps
    dl, dh = d0(etaL, 0.0, t), d0(etaH, kap, t)
    if abs(dl) < 1e-10 or abs(dh) < 1e-10: continue   # numerically marginal
    bands += 1
    if not (dl < 0 < dh): ok = False
# (b) straddle permanence: type a with mean in (theta, m) flips at finite T*_a;
#     type b with mean beyond m (gamma_b > delta_m) never flips.
ok2, n2 = True, 0
for _ in range(300):
    theta = 0.0; m = rng.uniform(0.25, 0.55)
    mua = rng.uniform(0.03, m - 0.08); siga2 = (m * m - mua * mua) + rng.uniform(0.02, 0.1)
    mub = rng.uniform(m + 0.07, 0.95); sigb2 = rng.uniform(0.0, 0.03)
    dma = m * m; da = siga2 + mua * mua; ga = m * mua
    wsa = (da - ga) / (da + dma - 2 * ga)
    db = sigb2 + mub * mub; gb = m * mub
    if db <= dma: continue
    etaa = rng.uniform(0.15, min(0.9, da / (da + dma)))
    etab = rng.uniform(0.15, min(0.9, db / (db + dma)))
    ea, eb = rng.uniform(0, 0.8), rng.uniform(0, 0.8)
    Ta = np.log(1 - wsa) / np.log(1 - etaa)
    eps = 1e-6; good = True
    for t in (int(np.ceil(Ta)) + 2, int(np.ceil(Ta)) + 6):
        def fa(b):
            w = etaa * (1 - (1 - ea) * b); return qfun(1 - (1 - w) ** t, da, dma, ga)
        def fb(b):
            w = etab * (1 - (1 - eb) * b); return qfun(1 - (1 - w) ** t, db, dma, gb)
        dA = (fa(eps) - fa(0)) / eps; dB = (fb(eps) - fb(0)) / eps
        if abs(dA) < 1e-10 or abs(dB) < 1e-10: good = False; break
        if not (dA < 0 < dB): ok2 = False
    if good: n2 += 1
report("P2d  bands: (a) credulity band (T*_L,T*_H); (b) straddle: truth-side flips at T*, far type never",
       ok and ok2, f"{bands} credulity bands, {n2} straddle configs")

# --- P2e: noisy evidence AR(1): stationary MSE = b_m^2 + w*sig_m^2/(2-w) ---
ok = True
for _ in range(12):
    w = rng.uniform(0.1, 0.9); sig_m = rng.uniform(0.02, 0.15)
    bm = rng.uniform(-0.05, 0.05); theta = 0.4
    N, T = 20000, 4000
    b = rng.uniform(0, 1, N)
    for t in range(T):
        mt = theta + bm + sig_m * rng.standard_normal(N)
        b = (1 - w) * b + w * mt
    emp = np.mean((b - theta) ** 2)
    th = bm ** 2 + w * sig_m ** 2 / (2 - w)
    if abs(emp - th) > 0.03 * (abs(th) + 1e-4): ok = False
report("P2e  stationary MSE = b_m^2 + w sig_m^2/(2-w); deference smooths variance", ok)

# ============================================================================
# PILLAR 3: ENDOGENOUS DEFERENCE
# ============================================================================

# --- P3a: knife-edge lemma: (1-d)^2 / w^2 = 1/eta^2 identically;
#          quasi-static satisfaction flat in beta when injection exogenous ---
ok = True
for _ in range(2000):
    eta = rng.uniform(0.05, 1); e = rng.uniform(0, 0.99); b = rng.uniform(0, 1)
    d = (1 - e) * b; w = eta * (1 - d)
    if abs((1 - d) ** 2 / w ** 2 - 1 / eta ** 2) > 1e-12: ok = False
# quasi-static U with two types, exogenous injections iota_tau: x* = iota/w
for _ in range(200):
    etaH, etaL = rng.uniform(0.1, 0.95, 2); kap = rng.uniform(0, 0.95)
    iH, iL = rng.uniform(0.01, 0.3), -rng.uniform(0.01, 0.3)
    piH = rng.uniform(0.1, 0.9)
    Uqs = []
    for b in np.linspace(0, 0.99, 30):
        dH, dL = (1 - kap) * b, b
        wH, wL = etaH * (1 - dH), etaL * (1 - dL)
        xH, xL = iH / wH, iL / wL
        Uqs.append(-(piH * (1 - dH) ** 2 * xH ** 2 + (1 - piH) * (1 - dL) ** 2 * xL ** 2))
    Uqs = np.array(Uqs)
    if Uqs.max() - Uqs.min() > 1e-12 * (1 + abs(Uqs).max()): ok = False
report("P3a  knife-edge: (1-d)^2/w^2 = 1/eta^2; quasi-static U exactly FLAT in beta (zeta=0)", ok)

# --- P3b: myopia trap with stratification feedback zeta>0:
#          instantaneous U'_beta > 0 at fixed x, quasi-static U strictly decreasing ---
ok = True
for _ in range(300):
    eta = rng.uniform(0.2, 0.9); iota = rng.uniform(0.02, 0.3)
    zeta = rng.uniform(0.005, eta * 0.04)
    Bg = np.linspace(0, 0.95, 40)
    Uqs, dU_inst = [], []
    for b in Bg:
        w = eta * (1 - b)
        if w - zeta <= 1e-3: break
        x = iota / (w - zeta)                       # x_{t+1} = (1-w)x + zeta x + iota
        Uqs.append(-(1 - b) ** 2 * x ** 2)
        # instantaneous gradient at fixed x: d/db [-(1-b)^2 x^2] = 2(1-b)x^2 > 0
        dU_inst.append(2 * (1 - b) * x ** 2)
    Uqs = np.array(Uqs)
    if len(Uqs) > 5:
        if not np.all(np.diff(Uqs) < 0): ok = False         # long-run U strictly decreasing
        if not np.all(np.array(dU_inst[:-1]) > 0): ok = False  # myopic gradient points up
report("P3b  myopia trap (zeta>0): instantaneous U' > 0, quasi-static U strictly decreasing", ok)

# --- P3c: reduced (beta, D) map bistability iff G(0)<0<G(1) ---
def reduced_map_params():
    return dict(eta=0.5, c=0.9, lam0=0.02, I=0.02, v=0.10, alpha=0.6)

def srate(b, P):  return (1 - P['lam0']) * (1 - P['eta'] * (1 - b)) ** 2
def Dstar(b, P):  return P['I'] / (1 - srate(b, P))
def G(b, P, rho=0.0):
    return -P['v'] + (2 * P['c'] * (1 - P['c'] * b) - rho) * Dstar(b, P)

def step(b, D, P, rho=0.0, noise=0.0):
    Up = -P['v'] + (2 * P['c'] * (1 - P['c'] * b) - rho) * D
    b2 = min(1.0, max(0.0, b + P['alpha'] * Up))
    D2 = max(0.0, srate(b, P) * D + P['I'] + noise)
    return b2, D2

P = reduced_map_params()
g0, g1 = G(0, P), G(1, P)
Bg = np.linspace(0, 1, 100001); Gv = np.array([G(b, P) for b in Bg])
roots = np.sum(np.diff(np.sign(Gv)) != 0)
# simulate from both corners
b, D = 0.0, Dstar(0, P)
for _ in range(4000): b, D = step(b, D, P)
calib = (b < 1e-6 and abs(D - Dstar(0, P)) < 1e-8)
b, D = 1.0, Dstar(1, P)
for _ in range(4000): b, D = step(b, D, P)
capt = (b > 1 - 1e-6 and abs(D - Dstar(1, P)) < 1e-6)
report("P3c  reduced map bistable: G(0)<0<G(1), one interior saddle, two corner attractors",
       (g0 < 0 < g1) and roots == 1 and calib and capt,
       f"G(0)={g0:.4f}, G(1)={g1:.4f}, interior roots={roots}, D*={Dstar(0,P):.4f}/{Dstar(1,P):.3f}")

# separatrix: bisection on initial D at beta0 = 0.4
def fate(D0, P, b0=0.4, T=6000):
    b, D = b0, D0
    for _ in range(T): b, D = step(b, D, P)
    return b > 0.5
lo, hi = 0.0, 2.0
assert not fate(lo, P) and fate(hi, P)
for _ in range(50):
    mid = 0.5 * (lo + hi)
    if fate(mid, P): hi = mid
    else: lo = mid
report("P3c' separatrix located by bisection (basin boundary exists)", True,
       f"D_sep(beta0=0.4) = {0.5*(lo+hi):.5f}")

# --- P3d: hysteresis: cure threshold rho_cure = 2c(1-c) - v*lam0/I; up/down sweep ---
rho_cure_cf = 2 * P['c'] * (1 - P['c']) - P['v'] * P['lam0'] / P['I']
# up-sweep from captured corner
b, D = 1.0, Dstar(1, P)
escape_rho = None
for rho in np.linspace(0, 0.15, 1501):
    for _ in range(400): b, D = step(b, D, P, rho=rho)
    if b < 0.5 and escape_rho is None:
        escape_rho = rho; break
# down-sweep from calibrated back to rho=0
b2, D2 = 0.0, Dstar(0, P)
stay = True
for rho in np.linspace(0.15, 0.0, 301):
    for _ in range(200): b2, D2 = step(b2, D2, P, rho=rho)
    if b2 > 0.5: stay = False
report("P3d  hysteresis: escape at rho ~ rho_cure; calibrated persists at rho=0 after cure",
       escape_rho is not None and abs(escape_rho - rho_cure_cf) < 0.005 and stay,
       f"closed form rho_cure = {rho_cure_cf:.4f}, measured escape = {escape_rho:.4f}, gap vs prevention(=0): {rho_cure_cf:.3f}")

# --- P3e: critical slowing down (interior-equilibrium variant, quadratic deference cost) ---
# J'(b,D) = -v*b + 2c(1-cb)D ; interior equilibria = fixed points of
# phi(b) := 2c D*(b) / (v + 2c^2 D*(b)),  D*(b) = I/(1-s(b)).
P3 = dict(eta=0.5, c=0.9, lam0=0.02, v=0.16, alpha=0.8)
def Dst(b, I, P): return I / (1 - (1 - P['lam0']) * (1 - P['eta'] * (1 - b)) ** 2)
def phi(b, I, P):
    D = Dst(b, I, P); return 2 * P['c'] * D / (P['v'] + 2 * P['c'] ** 2 * D)
def n_interior_fp(I, P):
    bg = np.linspace(1e-4, 1 - 1e-4, 40001)
    f = np.array([phi(x, I, P) for x in bg]) - bg
    return int(np.sum(np.diff(np.sign(f)) != 0))
I0 = 0.02
n0 = n_interior_fp(I0, P3)
cap0 = phi(1.0, I0, P3) >= 1.0                 # captured corner attracting at I0
Ilo, Ihi = I0, 0.2
fold_ok = n_interior_fp(Ihi, P3) == 0
for _ in range(48):
    Im = 0.5 * (Ilo + Ihi)
    if n_interior_fp(Im, P3) >= 2: Ilo = Im
    else: Ihi = Im
I_fold = 0.5 * (Ilo + Ihi)
window = I_fold / I0
def step_q(b, D, I, P, noise=0.0):
    Up = -P['v'] * b + 2 * P['c'] * (1 - P['c'] * b) * D
    b2 = min(1.0, max(0.0, b + P['alpha'] * Up))
    D2 = max(0.0, (1 - P['lam0']) * (1 - P['eta'] * (1 - b)) ** 2 * D + I + noise)
    return b2, D2
bg = np.linspace(1e-4, 1 - 1e-4, 40001)
f = np.array([phi(x, I0, P3) for x in bg]) - bg
blo = bg[np.where(np.diff(np.sign(f)) != 0)[0][0]]
b, D = blo, Dst(blo, I0, P3)
plateaus = np.linspace(I0, 0.96 * I_fold, 12)
sig_n = 1.5e-3
stats, escaped = [], False
for I in plateaus:
    for _ in range(4000):
        b, D = step_q(b, D, I, P3, noise=sig_n * rng.standard_normal())
    buf = np.empty(12000)
    esc = False
    for t in range(12000):
        b, D = step_q(b, D, I, P3, noise=sig_n * rng.standard_normal())
        buf[t] = D
        if b > 0.7: esc = True; break
    if esc: escaped = True; break
    x = buf - buf.mean()
    stats.append((x.var(), np.corrcoef(x[:-1], x[1:])[0, 1]))
v_e, a_e = stats[1]; v_l, a_l = stats[-1]
slowing = (len(stats) >= 8) and (v_l > 2.5 * v_e) and (a_l > a_e + 0.03)
report("P3e  critical slowing down at the fold: var & AC1 of disagreement stock D rise",
       (n0 == 2) and cap0 and fold_ok and (window > 1.25) and slowing,
       f"interior fps={n0}, fold window x{window:.2f}, plateaus={len(stats)}, var(D) x{v_l/max(v_e,1e-30):.1f}, AC1(D) {a_e:.3f}->{a_l:.3f}")

# --- P3f: microfounded capture + satisfaction-capacity DECOUPLING (laundering) ---
# At beta=1 the agreement weight (1-d_L)^2 on type L vanishes exactly while x_L
# diverges: measured U stays bounded (can even improve) while civic capacity -> -inf.
etaH = etaL = 0.5; kap = 0.5; piH = 0.5
iH, iL = 0.02, -0.02; zeta = 0.012; alpha = 0.8
def micro_step(b, xH, xL):
    dH, dL = (1 - kap) * b, b
    wH, wL = etaH * (1 - dH), etaL * (1 - dL)
    dU = 2 * piH * (1 - kap) * (1 - dH) * xH ** 2 + 2 * (1 - piH) * (1 - dL) * xL ** 2
    b2 = min(1.0, max(0.0, b + alpha * dU))
    return b2, (1 - wH + zeta) * xH + iH, (1 - wL + zeta) * xL + iL
def Umeas(b, xH, xL):
    dH, dL = (1 - kap) * b, b
    return -(piH * (1 - dH) ** 2 * xH ** 2 + (1 - piH) * (1 - dL) ** 2 * xL ** 2)
def Cciv(xH, xL):  # agreement-unweighted civic proxy: population squared deviation
    return -(piH * xH ** 2 + (1 - piH) * xL ** 2)
# (i) gradient ascent on instantaneous U reaches capture
b, xH, xL = 0.05, iH / etaH, iL / etaL
for _ in range(6000): b, xH, xL = micro_step(b, xH, xL)
captured = b > 0.99
xL_mid = abs(xL)
for _ in range(6000): b, xH, xL = micro_step(b, xH, xL)
diverging = abs(xL) > 5 * xL_mid                      # (ii) laundered divergence
U_cap, C_cap = Umeas(b, xH, xL), Cciv(xH, xL)
# calibrated benchmark: beta pinned at 0
xH0, xL0 = iH / etaH, iL / etaL
for _ in range(12000):
    xH0 = (1 - etaH + zeta) * xH0 + iH
    xL0 = (1 - etaL + zeta) * xL0 + iL
U_cal, C_cal = Umeas(0.0, xH0, xL0), Cciv(xH0, xL0)
# (iii) along the interior ascent path, quasi-static U is strictly decreasing
# (myopia); the corner itself launders: U bounded while C collapses.
ok_path = True
for bb in np.linspace(0, 0.9, 19):
    dL_ = bb; wL_ = etaL * (1 - dL_)
    if wL_ - zeta <= 1e-3: ok_path = False; break
qsU = []
for bb in np.linspace(0, 0.9, 19):
    dH_, dL_ = (1 - kap) * bb, bb
    wH_, wL_ = etaH * (1 - dH_), etaL * (1 - dL_)
    xh, xl = iH / (wH_ - zeta), iL / (wL_ - zeta)
    qsU.append(-(piH * (1 - dH_) ** 2 * xh ** 2 + (1 - piH) * (1 - dL_) ** 2 * xl ** 2))
myopia = ok_path and np.all(np.diff(np.array(qsU)) < 0)
decouple = captured and diverging and (C_cap < 50 * C_cal) and np.isfinite(U_cap) and (U_cap > 3 * U_cal)
report("P3f  capture + decoupling: U bounded (laundered) while C collapses; interior path myopic",
       decouple and myopia,
       f"beta_end={b:.3f}, U_cap={U_cap:.5f} vs U_cal={U_cal:.5f}; C_cap ~ -1e{int(np.log10(-C_cap)):d} vs C_cal={C_cal:.5f}; |x_L| grew ~1e{int(np.log10(abs(xL)/max(xL_mid,1e-300))):d}x")

# ============================================================================
# EXTENSIONS: proof-obligation suites (sequel v1)
# ============================================================================

# --- P3g: single-claim (rank-one) variant: D' = (m(b) sqrt(D) + j)^2,
#          m(b) = (1-lam0)(1-eta(1-b)). Same bistable corner structure. ---
Pg = dict(eta=0.5, c=0.9, lam0=0.02, v=0.10, alpha=0.6, j=0.083)
def m_g(b, P):  return (1 - P['lam0']) * (1 - P['eta'] * (1 - b))
def Dst_g(b, P):
    r = P['j'] / (1 - m_g(b, P)); return r * r
def G_g(b, P):  return -P['v'] + 2 * P['c'] * (1 - P['c'] * b) * Dst_g(b, P)
def step_g(b, D, P):
    Up = -P['v'] + 2 * P['c'] * (1 - P['c'] * b) * D
    b2 = min(1.0, max(0.0, b + P['alpha'] * Up))
    D2 = (m_g(b, P) * np.sqrt(max(D, 0.0)) + P['j']) ** 2
    return b2, D2
gg0, gg1 = G_g(0, Pg), G_g(1, Pg)
Gv = np.array([G_g(x, Pg) for x in np.linspace(0, 1, 50001)])
roots_g = int(np.sum(np.diff(np.sign(Gv)) != 0))
b, D = 0.0, Dst_g(0, Pg)
for _ in range(5000): b, D = step_g(b, D, Pg)
cal_g = (b < 1e-6 and abs(D - Dst_g(0, Pg)) < 1e-8)
b, D = 1.0, Dst_g(1, Pg)
for _ in range(5000): b, D = step_g(b, D, Pg)
cap_g = (b > 1 - 1e-6 and abs(D - Dst_g(1, Pg)) < 1e-4)
report("P3g  rank-one (sqrt-D) variant: same corner bistability (robustness of affine reduction)",
       (gg0 < 0 < gg1) and roots_g >= 1 and cal_g and cap_g,
       f"G(0)={gg0:.4f}, G(1)={gg1:.3f}, D*={Dst_g(0,Pg):.4f}/{Dst_g(1,Pg):.1f}, interior roots={roots_g}")

# --- P3h: noisy prevention. Arrhenius scaling of escape from the calibrated
#          corner (log mean escape time linear in 1/sigma^2) and protection
#          monotone in the civic weight rho at fixed sigma. ---
def srate_v(b, P):  return (1 - P['lam0']) * (1 - P['eta'] * (1 - b)) ** 2
P_esc = dict(P); P_esc['I'] = 0.040   # shallow basin near corner fold, still bistable (rho_cure = 0.13)
def ensemble_escape(sigma, rho, P, n=80, cap=250000, seed=0):
    g = np.random.default_rng(1000 + seed)
    b = np.zeros(n); D = np.full(n, Dstar(0, P)); t_esc = np.full(n, cap, dtype=float)
    alive = np.ones(n, bool)
    for t in range(cap):
        if not alive.any(): break
        Up = -P['v'] + (2 * P['c'] * (1 - P['c'] * b) - rho) * D + sigma * g.standard_normal(n)
        b = np.clip(b + P['alpha'] * Up, 0.0, 1.0)
        D = np.maximum(0.0, srate_v(b, P) * D + P['I'])
        newly = alive & (b > 0.9)
        t_esc[newly] = t
        alive &= ~newly
    return t_esc, int((~alive).sum()), n
sigmas = [0.046, 0.052, 0.060, 0.070]
pts, diag = [], []
slope, R2 = float('nan'), float('nan')
for k, s in enumerate(sigmas):
    te, nesc, n = ensemble_escape(s, 0.0, P_esc, seed=k)
    Tbar = te.sum() / (nesc + 0.5)          # hazard-rate MLE under censoring
    diag.append(f"s={s}: {nesc}/{n} esc, Tbar={Tbar:.0f}")
    if nesc >= 1: pts.append((1.0 / s ** 2, np.log(Tbar)))
print("      P3h diag: " + " | ".join(diag))
arr_ok = len(pts) >= 3
if arr_ok:
    X = np.array([p[0] for p in pts]); Y = np.array([p[1] for p in pts])
    A = np.vstack([X, np.ones_like(X)]).T
    coef, res, *_ = np.linalg.lstsq(A, Y, rcond=None)
    slope = coef[0]
    Yhat = A @ coef
    R2 = 1 - np.sum((Y - Yhat) ** 2) / np.sum((Y - Y.mean()) ** 2)
    arr_ok = (slope > 0) and (R2 > 0.9)
s_rho = 0.070
rates = []
for k, rho in enumerate([0.0, 0.02, 0.04]):
    te, nesc, n = ensemble_escape(s_rho, rho, P_esc, seed=50 + k)
    rates.append((nesc + 0.5) / te.sum())
rho_ok = (rates[0] > rates[1] > rates[2]) and (rates[0] >= 5 * rates[2])
report("P3h  measurement-noise escape: Arrhenius in 1/sigma^2; protection monotone in rho << rho_cure",
       arr_ok and rho_ok,
       f"fit pts={len(pts)}, slope={slope:.4f}, R2={R2:.3f}; hazard(rho=0/.02/.04) = "
       f"{rates[0]:.1e}/{rates[1]:.1e}/{rates[2]:.1e}")

# --- P3i: slow eigenvalue -> 1 along the low branch approaching the fold,
#          with saddle-node sqrt scaling 1 - lambda ~ K sqrt(I_fold - I). ---
def low_branch_lambda(I, P):
    bg = np.linspace(1e-4, 1 - 1e-4, 40001)
    f = np.array([phi(x, I, P) for x in bg]) - bg
    ix = np.where(np.diff(np.sign(f)) != 0)[0]
    blo = bg[ix[0]]
    D = Dst(blo, I, P)
    a = 1 + P['alpha'] * (-P['v'] - 2 * P['c'] ** 2 * D)
    bb = P['alpha'] * 2 * P['c'] * (1 - P['c'] * blo)
    sp = (1 - P['lam0']) * 2 * (1 - P['eta'] * (1 - blo)) * P['eta']
    cc = sp * D
    d = (1 - P['lam0']) * (1 - P['eta'] * (1 - blo)) ** 2
    tr, det = a + d, a * d - bb * cc
    return (tr + np.sqrt(max(tr * tr - 4 * det, 0.0))) / 2
Igrid = np.linspace(I0, 0.999 * I_fold, 25)
lams = np.array([low_branch_lambda(I, P3) for I in Igrid])
gaps = np.sqrt(I_fold - Igrid)
corr = np.corrcoef(1 - lams, gaps)[0, 1]
report("P3i  fold mechanics: lambda_slow -> 1 monotonically, 1-lambda ~ sqrt(I_fold - I)",
       np.all(np.diff(lams) > -1e-9) and lams[-1] > 0.95 and corr > 0.99,
       f"lambda: {lams[0]:.3f} -> {lams[-1]:.4f}, corr(1-lam, sqrt gap) = {corr:.4f}")

# --- P3j: instability <=> transversality. At any interior fixed point of the
#          linear-cost map, Perron eigenvalue > 1  iff  G'(beta) > 0. ---
def G_vec(bg, Pr):
    s = (1 - Pr['lam0']) * (1 - Pr['eta'] * (1 - bg)) ** 2
    return -Pr['v'] + 2 * Pr['c'] * (1 - Pr['c'] * bg) * Pr['I'] / (1 - s)
ok, tested = True, 0
bg = np.linspace(1e-5, 1 - 1e-5, 4001)
for trial in range(800):
    eta = rng.uniform(0.2, 0.8); c = rng.uniform(0.5, 0.95)
    lam0 = rng.uniform(0.01, 0.1); I = rng.uniform(0.01, 0.05)
    s0 = (1 - lam0) * (1 - eta) ** 2
    vlo, vhi = 2 * c * I / (1 - s0), 2 * c * (1 - c) * I / lam0
    if vhi <= vlo: continue
    v = rng.uniform(vlo, vhi)
    alpha = 0.9 * lam0 / (2 * c ** 2 * I)            # step-size condition (SS)
    Pr = dict(eta=eta, c=c, lam0=lam0, I=I, v=v, alpha=alpha)
    Gv = G_vec(bg, Pr)
    ix = np.where(np.diff(np.sign(Gv)) != 0)[0]
    for i in ix:
        br = 0.5 * (bg[i] + bg[i + 1])
        h = 1e-6
        Gp = (G_vec(np.array([br + h]), Pr)[0] - G_vec(np.array([br - h]), Pr)[0]) / (2 * h)
        if abs(Gp) < 1e-7: continue
        D = Dstar(br, Pr)
        a = 1 - 2 * alpha * c ** 2 * D
        bb = 2 * alpha * c * (1 - c * br)
        sp = (1 - lam0) * 2 * (1 - eta * (1 - br)) * eta
        cc = sp * D; d = srate(br, Pr)
        tr, det = a + d, a * d - bb * cc
        lamPF = (tr + np.sqrt(max(tr * tr - 4 * det, 0.0))) / 2
        if (lamPF > 1) != (Gp > 0): ok = False
        tested += 1
# benchmark saddle eigenvalues (hyperbolicity witness for Theorem C)
Gv_b = G_vec(bg, P)
i_b = np.where(np.diff(np.sign(Gv_b)) != 0)[0][0]
b_dag = 0.5 * (bg[i_b] + bg[i_b + 1]); D_dag = Dstar(b_dag, P)
a_ = 1 - 2 * P['alpha'] * P['c'] ** 2 * D_dag
b_ = 2 * P['alpha'] * P['c'] * (1 - P['c'] * b_dag)
c_ = (1 - P['lam0']) * 2 * (1 - P['eta'] * (1 - b_dag)) * P['eta'] * D_dag
d_ = srate(b_dag, P)
tr_, det_ = a_ + d_, a_ * d_ - b_ * c_
disc = np.sqrt(max(tr_ * tr_ - 4 * det_, 0.0))
l1, l2 = (tr_ + disc) / 2, (tr_ - disc) / 2
report("P3j  identity: interior fixed point unstable (lambda_PF > 1)  <=>  G'(beta) > 0",
       ok and tested > 300 and l1 > 1 and -1 < l2 < 1,
       f"{tested} interior roots tested under (SS); benchmark saddle beta={b_dag:.4f}, "
       f"lambda_PF={l1:.4f}, lambda_2={l2:.4f}")

# --- P5a: aggregation lemma. Claim-portfolio stock follows the affine law
#          D' = (1-lam0)(1-w)^2 D + I exactly in expectation. ---
T, reps = 80, 1600
beta_path = 0.3 + 0.2 * np.sin(np.linspace(0, 3, T))
eta_a, lam_a, I_a = 0.5, 0.05, 0.03
g = np.random.default_rng(7)
D0 = 0.4
mc = np.zeros((reps, T))
for rrr in range(reps):
    claims = list(np.full(8, D0 / 8))
    for t in range(T):
        w = eta_a * (1 - beta_path[t])
        claims = [(1 - w) ** 2 * x for x in claims]
        claims = [x for x in claims if g.random() > lam_a]
        claims.append(g.exponential(I_a))
        mc[rrr, t] = sum(claims)
Dth = np.empty(T); Dcur = D0
for t in range(T):
    w = eta_a * (1 - beta_path[t])
    Dcur = (1 - lam_a) * (1 - w) ** 2 * Dcur + I_a
    Dth[t] = Dcur
relerr = np.max(np.abs(mc.mean(axis=0) - Dth) / (np.abs(Dth) + 1e-9))
report("P5a  aggregation: portfolio stock obeys affine law exactly in expectation", relerr < 0.05,
       f"max rel err of MC mean vs affine recursion = {relerr:.3f} over {T} steps")



# ============================================================================
# REVISION SUITES (editorial integration packet): saturated-variant laundering,
# rank-one single-claim law, separatrix sweep, saturated gradient bounds.
# ============================================================================

# --- S1 SATURATED-CAPTURE SUITE (P2-D1): bounded beliefs x in [-xbar, xbar].
# At capture the L-weight is identically zero while |x_L| sits at the bound:
# blind while maximally wrong. The ordering U_cap > U_cal and the capture
# limit U -> -piH kap^2 (iH/(etaH kap - zeta))^2 survive saturation exactly.
etaH = etaL = 0.5; kap = 0.5; piH = 0.5
iH, iL = 0.02, -0.02; zeta = 0.012; alpha = 0.8; xbar = 1.0
def sat_step(b, xH, xL, a=alpha, iH_=iH):
    dH, dL = (1 - kap) * b, b
    wH, wL = etaH * (1 - dH), etaL * (1 - dL)
    dU = 2 * piH * (1 - kap) * (1 - dH) * xH ** 2 + 2 * (1 - piH) * (1 - dL) * xL ** 2
    b2 = min(1.0, max(0.0, b + a * dU))
    xH2 = min(xbar, max(-xbar, (1 - wH + zeta) * xH + iH_))
    xL2 = min(xbar, max(-xbar, (1 - wL + zeta) * xL + iL))
    return b2, xH2, xL2
def Umeas(b, xH, xL):
    dH, dL = (1 - kap) * b, b
    return -(piH * (1 - dH) ** 2 * xH ** 2 + (1 - piH) * (1 - dL) ** 2 * xL ** 2)
def Cciv(xH, xL): return -(piH * xH ** 2 + (1 - piH) * xL ** 2)
b, xH, xL = 0.05, iH / etaH, iL / etaL
for _ in range(20000): b, xH, xL = sat_step(b, xH, xL)
xHstar = iH / (etaH * kap - zeta)
U_cap, C_cap = Umeas(b, xH, xL), Cciv(xH, xL)
xH0, xL0 = iH / etaH, iL / etaL
for _ in range(20000):
    xH0 = (1 - etaH + zeta) * xH0 + iH
    xL0 = (1 - etaL + zeta) * xL0 + iL
U_cal, C_cal = Umeas(0.0, xH0, xL0), Cciv(xH0, xL0)
ok_s1 = (b == 1.0 and abs(abs(xL) - xbar) < 1e-12                       # pinned at the bound
         and abs(xH - xHstar) < 1e-9                                    # honest H-channel limit
         and abs(U_cap + piH * kap ** 2 * xHstar ** 2) < 1e-12          # capture limit exact
         and U_cap > U_cal                                              # ordering preserved
         and abs(C_cap + (piH * xHstar ** 2 + (1 - piH) * xbar ** 2)) < 1e-9)  # capacity floor
report("S1   saturated capture: beta=1, |x_L|=xbar (max the state space permits), L-weight "
       "identically zero, ordering U_cap>U_cal preserved, capacity at its floor", ok_s1,
       f"U_cap={U_cap:.2e} vs U_cal={U_cal:.2e}; C_floor={C_cap:.4f}; xH*={xHstar:.4f}")

# --- S2 SATURATED THEOREM 5(i): geometric convergence; finite-time dichotomy.
# (a) ordinary benchmark (iH != 0): post-saturation (1-beta) contracts by at
#     least (1 - 2 alpha piL xbar^2) per step and attainment is finite-time.
b, xH, xL = 0.05, iH / etaH, iL / etaL
steps_to_face = None
for t in range(50000):
    b, xH, xL = sat_step(b, xH, xL)
    if b == 1.0: steps_to_face = t + 1; break
for _ in range(2000): b, xH, xL = sat_step(b, xH, xL)     # at the face, error climbs to the bound
ok_s2a = steps_to_face is not None and abs(abs(xL) - xbar) < 1e-12
# (b) boundary instance iH = 0: with 2 alpha piL xbar^2 >= 1, one post-saturation
#     step attains the face exactly; with < 1, contraction is exactly geometric
#     at rate (1 - 2 alpha piL xbar^2) and the face is never attained in a long window.
a_hi = 1.2  # 2*a*piL*xbar^2 = 1.2 >= 1
b, xH, xL = 0.05, 0.0, iL / etaL
sat_seen, face_step = False, None
for t in range(20000):
    if abs(xL) >= xbar - 1e-12: sat_seen = True
    b, xH, xL = sat_step(b, xH, xL, a=a_hi, iH_=0.0)
    if sat_seen and b == 1.0: face_step = t; break
ok_hi = face_step is not None
a_lo = 0.05  # 2*a*piL*xbar^2 = 0.05 < 1
b, xH, xL = 0.05, 0.0, iL / etaL
for _ in range(120000):                                   # pre-phase: reach the bound
    if abs(xL) >= xbar - 1e-12: break
    b, xH, xL = sat_step(b, xH, xL, a=a_lo, iH_=0.0)
ratios, below = [], abs(xL) >= xbar - 1e-12
for t in range(300):
    b2, xH, xL = sat_step(b, xH, xL, a=a_lo, iH_=0.0)
    if b < 1.0 and (1 - b) > 1e-6 and xH == 0.0:      # avoid float cancellation in 1-b
        ratios.append((1 - b2) / (1 - b))
    b = b2
    if b >= 1.0: below = False
target = 1 - 2 * a_lo * (1 - piH) * xbar ** 2
ok_lo = below and len(ratios) > 100 and max(abs(r - target) for r in ratios) < 1e-8
report("S2   saturated Theorem 5(i): geometric contraction of (1-beta); finite-time attainment "
       "guaranteed iff 2*alpha*piL*xbar^2 >= 1 (boundary instance iH=0)", ok_s2a and ok_hi and ok_lo,
       f"benchmark: face in {steps_to_face} steps, then |x_L| pinned at xbar; iH=0 branch: "
       f"rate-{a_hi} finite-time, rate-{a_lo} exactly geometric at {target:.3f}, asymptotic only")

# --- S3 RANK-ONE SINGLE-CLAIM SUITE (P2-D7): law D' = (m(beta) sqrt(D) + j)^2,
# m(beta) = 1 - eta(1-beta). Reproduces the bistable phenomenology: calibrated
# attractor, absorbing capture corner with unbounded stock, separatrix between.
def rank1_fate(b0, D0, eta, c, v, j, a, T=40000):
    b, D = b0, D0
    for _ in range(T):
        dU = -v + 2 * c * (1 - c * b) * D
        b = min(1.0, max(0.0, b + a * dU))
        w = eta * (1 - b)
        D = ((1 - w) * np.sqrt(D) + j) ** 2
        if b > 0.999 and D > 50: return True
        if b < 1e-3 and abs(D - j ** 2 / (eta ** 2)) < 1e-6: return False
    return b > 0.5
from scipy.optimize import brentq as _bq1
ok_s3, n3 = True, 0
for _ in range(40):
    eta = rng.uniform(0.35, 0.7); c = rng.uniform(0.75, 0.95); j = rng.uniform(0.02, 0.08)
    Dcal = j ** 2 / eta ** 2
    v = rng.uniform(1.3, 3.0) * 2 * c * Dcal          # G(0) < 0
    a = rng.uniform(0.1, 0.5)
    n3 += 1
    Dnull1 = v / (2 * c * (1 - c))                     # corner nullcline
    Gr1 = lambda b: -v + 2 * c * (1 - c * b) * j ** 2 / (eta * (1 - b)) ** 2
    bsad = _bq1(Gr1, 1e-4, 1 - 1e-3)                   # rank-one saddle (G(0)<0, G(1-)>0)
    if rank1_fate(0.3 * bsad, Dcal, eta, c, v, j, a): ok_s3 = False           # calibrated attractor
    if not rank1_fate(0.999, 2 * Dnull1 + 10, eta, c, v, j, a): ok_s3 = False  # captured corner
    # separatrix: fate monotone in D0 below the saddle
    b0 = 0.6 * bsad; hi = None
    for mult in (2, 5, 20, 100, 500, 2000, 10000):
        if rank1_fate(b0, mult * Dcal, eta, c, v, j, a): hi = mult * Dcal; break
    if hi is None: ok_s3 = False; continue
    if rank1_fate(b0, 0.2 * Dcal, eta, c, v, j, a): ok_s3 = False
report("S3   rank-one single-claim law D'=(m(b) sqrt(D)+j)^2: bistable phenomenology "
       "(calibrated attractor, absorbing capture corner, separatrix)", ok_s3, f"{n3} draws")

# --- S4 SEPARATRIX SWEEP (P2-D14): location of the saddle beta-dagger across a
# parameter sweep around benchmark; the benchmark value is benchmark-specific.
from scipy.optimize import brentq as _bq
def Gfun(b, eta, c, lam0, I, v):
    s = (1 - lam0) * (1 - eta * (1 - b)) ** 2
    return -v + 2 * c * (1 - c * b) * I / (1 - s)
roots = []
tries = 0
while len(roots) < 120 and tries < 4000:
    tries += 1
    eta = rng.uniform(0.3, 0.7); c = rng.uniform(0.75, 0.95)
    lam0 = rng.uniform(0.01, 0.06); I = rng.uniform(0.01, 0.06)
    v = rng.uniform(0.05, 0.35)
    g0, g1 = Gfun(0, eta, c, lam0, I, v), Gfun(1, eta, c, lam0, I, v)
    if not (g0 < 0 < g1): continue
    bg = np.linspace(1e-4, 1 - 1e-4, 600)
    gv = np.array([Gfun(b, eta, c, lam0, I, v) for b in bg])
    if np.sum((gv[:-1] < 0) & (gv[1:] >= 0)) != 1 or np.any((gv[:-1] > 0) & (gv[1:] <= 0)):
        continue                                       # single up-crossing only
    roots.append(_bq(lambda b: Gfun(b, eta, c, lam0, I, v), 1e-4, 1 - 1e-4))
roots = np.array(roots)
ok_s4 = len(roots) >= 100 and roots.min() < 0.80 and roots.max() > 0.95
report("S4   separatrix sweep: saddle location across bistable draws around benchmark", ok_s4,
       f"n={len(roots)}, beta-dagger range [{roots.min():.2f}, {roots.max():.2f}], "
       f"median {np.median(roots):.2f}")

# --- S5 SIGN ALIGNMENT AND GRADIENT FLOOR UNDER SATURATION (P2-D1c): across
# random admissible draws, |x_L,t| >= |iota_L| for all t >= 1 and the interior
# gradient is bounded below by 2 piL (1-beta) iota_L^2.
ok_s5 = True
for _ in range(120):
    eH = rng.uniform(0.3, 0.8); eL = rng.uniform(0.3, 0.8); kp = rng.uniform(0.2, 0.95)
    zt = rng.uniform(0.0, 0.9 * eH * kp); pH = rng.uniform(0.2, 0.8)
    iL_ = -rng.uniform(0.005, 0.2); iH_ = rng.uniform(0.0, 0.2)
    al = rng.uniform(0.05, 1.0); xb = 1.0
    b, xH, xL = rng.uniform(0, 0.3), iH_ / eH, iL_ / eL
    for t in range(800):
        dH, dL = (1 - kp) * b, b
        wH, wL = eH * (1 - dH), eL * (1 - dL)
        dU = 2 * pH * (1 - kp) * (1 - dH) * xH ** 2 + 2 * (1 - pH) * (1 - dL) * xL ** 2
        if dU < 2 * (1 - pH) * (1 - b) * iL_ ** 2 - 1e-12: ok_s5 = False
        b = min(1.0, max(0.0, b + al * dU))
        xH = min(xb, max(-xb, (1 - wH + zt) * xH + iH_))
        xL = min(xb, max(-xb, (1 - wL + zt) * xL + iL_))
        if t >= 1 and abs(xL) < abs(iL_) - 1e-12: ok_s5 = False
report("S5   saturation-robust bounds: |x_L| >= |iota_L| and dU >= 2 piL (1-beta) iota_L^2 "
       "along every path", ok_s5, "120 random admissible draws")

print()
print(f"{'='*70}")
print(f"DE-RISK RESULT: {sum(PASS)}/{len(PASS)} suites pass")
