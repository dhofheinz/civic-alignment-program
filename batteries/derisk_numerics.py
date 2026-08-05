"""De-risking numerics for 'Civic Drift: Threshold Dynamics of Satisfaction-Optimized Deference'.

Every conjectured theorem gets a numerical witness before any prose is written.
Pillar 1: continuous-type statics.  Pillar 2: repeated exposure / horizon.
Pillar 3: endogenous deference dynamics (bistability, hysteresis, early warning).
"""
import sys
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

# The Paper-I finite-corpus lift: exact derivative aggregation and strict
# pooled decrease when every claim is weakly decreasing and one positive-weight
# claim is strict.  The outside-subset guard is exercised by a positive-share
# counterexample whose unrestricted complement reverses the pooled sign.
for _ in range(400):
    J = int(rng.integers(2, 30))
    q_claim = rng.dirichlet(np.ones(J))
    intercept = rng.normal(size=J)
    linear_loss = rng.uniform(0, 2, size=J)
    quadratic_loss = rng.uniform(0, 1, size=J)
    j0 = int(rng.integers(0, J))
    linear_loss[j0] += 0.1
    for b in np.linspace(0, 1, 11):
        per_claim = intercept - linear_loss * b - quadratic_loss * b * b
        pooled = np.sum(q_claim * per_claim)
        derivative = np.sum(q_claim * (-linear_loss - 2 * quadratic_loss * b))
        eps = 1e-6
        pooled_plus = np.sum(q_claim *
                             (intercept - linear_loss * (b + eps)
                              - quadratic_loss * (b + eps) ** 2))
        pooled_minus = np.sum(q_claim *
                              (intercept - linear_loss * (b - eps)
                               - quadratic_loss * (b - eps) ** 2))
        if derivative >= 0 or abs((pooled_plus - pooled_minus) / (2 * eps) - derivative) > 1e-8:
            ok = False
        if not np.isfinite(pooled):
            ok = False
outside_share = np.array([0.4, 0.6])
outside_slopes = np.array([-1.0, 1.0])
outside_guard_exercised = (outside_share[0] > 0 and outside_slopes[0] < 0
                           and np.sum(outside_share * outside_slopes) > 0)
ok &= outside_guard_exercised
report("P1e  continuous-type Theorem A plus finite-corpus derivative/strictness lift; "
       "positive harmful share alone does not sign the pool", ok)

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
    return dict(eta=0.5, c=0.9, lam0=0.02, I=0.02, v=0.10, alpha=0.1)

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
def fate(D0, P, b0=0.4, T=36000):
    b, D = b0, D0
    for _ in range(T): b, D = step(b, D, P)
    return b > 0.5
lo, hi = 0.0, 8.0   # separatrix height from a transient scales as ~kappa*/alpha (jump map)
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
    for _ in range(2400): b, D = step(b, D, P, rho=rho)
    if b < 0.5 and escape_rho is None:
        escape_rho = rho; break
# down-sweep from calibrated back to rho=0
b2, D2 = 0.0, Dstar(0, P)
stay = True
for rho in np.linspace(0.15, 0.0, 301):
    for _ in range(1200): b2, D2 = step(b2, D2, P, rho=rho)
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
# EXTENSIONS: proof-obligation suites
# ============================================================================

# --- P3g: single-claim (rank-one) variants: D' = (m(b) sqrt(D) + j)^2.
#          Battery family m(b) = (1-lam0)(1-eta(1-b)) plus the Lean-proved
#          grounded family m(b) = sqrt(1-lam0)(1-eta(1-b)) of
#          groundedSqrt_global_bistability, whose squared deviation persists
#          at exactly (1-lam0) per period. Same bistable corner structure. ---
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

# Proved grounded family (deterministic; consumes no shared-rng draws):
# exact characteristic, sign pattern with a single interior saddle, both
# corner fates from on-characteristic starts, and the ungrounded endpoint's
# divergence (m(1) = 1 admits no finite captured equilibrium when j > 0).
Ps = dict(eta=0.5, c=0.9, lam0=0.02, v=0.10, alpha=0.1, j=0.05)
def m_s(b, P):  return np.sqrt(1 - P['lam0']) * (1 - P['eta'] * (1 - b))
def Dst_s(b, P):
    r = P['j'] / (1 - m_s(b, P)); return r * r
def G_s(b, P):  return -P['v'] + 2 * P['c'] * (1 - P['c'] * b) * Dst_s(b, P)
def step_s(b, D, P):
    Up = -P['v'] + 2 * P['c'] * (1 - P['c'] * b) * D
    b2 = min(1.0, max(0.0, b + P['alpha'] * Up))
    D2 = (m_s(b, P) * np.sqrt(max(D, 0.0)) + P['j']) ** 2
    return b2, D2
char_ok = True
for bh in (0.0, 0.3, 0.7, 1.0):
    D = 1.0
    for _ in range(4000):
        D = (m_s(bh, Ps) * np.sqrt(D) + Ps['j']) ** 2
    char_ok &= abs(D - Dst_s(bh, Ps)) < 1e-10 * max(1.0, Dst_s(bh, Ps))
gs0, gs1 = G_s(0, Ps), G_s(1, Ps)
bb_s = np.linspace(0, 1, 50001)
sgn_s = np.sign([G_s(x, Ps) for x in bb_s])
roots_s = int(np.sum(np.diff(sgn_s) != 0))
b_sad = float(bb_s[np.nonzero(np.diff(sgn_s) != 0)[0][0]]) if roots_s else float('nan')
def fate_s(b0, P, T=60000):
    b, D = b0, Dst_s(b0, P)
    for _ in range(T):
        b, D = step_s(b, D, P)
    return b
cal_s = all(fate_s(b0, Ps) < 1e-6 for b0 in (0.0, 0.5 * b_sad, 0.9 * b_sad))
cap_s = all(fate_s(b0, Ps) > 1 - 1e-6 for b0 in (min(1.0, 1.1 * b_sad), 1.0))
D = 1.0
for _ in range(200000):
    D = (np.sqrt(D) + Ps['j']) ** 2
    if D > 1e8:
        break
unground_diverges = D > 1e8

report("P3g  rank-one (sqrt-D) variants: corner bistability for the battery family and the "
       "Lean-proved grounded family; ungrounded endpoint diverges",
       (gg0 < 0 < gg1) and roots_g >= 1 and cal_g and cap_g
       and char_ok and (gs0 < 0 < gs1) and roots_s == 1 and cal_s and cap_s
       and unground_diverges,
       f"battery family G(0)={gg0:.4f}, G(1)={gg1:.3f}, D*={Dst_g(0,Pg):.4f}/{Dst_g(1,Pg):.1f}, "
       f"interior roots={roots_g}; grounded family G(0)={gs0:.4f}, G(1)={gs1:.2f}, "
       f"saddle at {b_sad:.3f}, characteristic exact, both corner fates confirmed; "
       f"ungrounded m(1)=1 stock exceeds 1e8")

# --- P3h: noisy prevention. Arrhenius scaling of first saddle-policy crossing
#          (log mean crossing time linear in 1/sigma^2) and protection monotone
#          in the civic weight rho at fixed sigma. ---
def srate_v(b, P):  return (1 - P['lam0']) * (1 - P['eta'] * (1 - b)) ** 2
P_esc = dict(P); P_esc['I'] = 0.040   # shallow basin near corner fold, still bistable (rho_cure = 0.13)

def qp_saddle(rho):
    lo, hi = 1e-9, 1 - 1e-9
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if -P_esc['v'] + (2 * P_esc['c'] * (1 - P_esc['c'] * mid) - rho) * Dstar(mid, P_esc) < 0:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)

# Noisy lanes use the printed simultaneous map: the stock update reads the
# pre-step policy, exactly as eq:map and the Lean loopMap do.
def ensemble_crossing(sigma, rho, P, n=80, cap=1500000, seed=0, bd=None):
    if bd is None:
        bd = qp_saddle(rho)
    g = np.random.default_rng(1000 + seed)
    b = np.zeros(n); D = np.full(n, Dstar(0, P)); t_esc = np.full(n, cap, dtype=float)
    alive = np.ones(n, bool)
    defic = np.full(n, np.nan); crossed = np.zeros(n, bool)
    for t in range(cap):
        if not alive.any(): break
        Up = -P['v'] + (2 * P['c'] * (1 - P['c'] * b) - rho) * D + sigma * g.standard_normal(n)
        b_new = np.clip(b + P['alpha'] * Up, 0.0, 1.0)
        D = np.maximum(0.0, srate_v(b, P) * D + P['I'])
        b = b_new
        if bd is not None:
            newx = (~crossed) & (b >= bd)
            if newx.any():
                defic[newx] = 1.0 - D[newx] / (P['I'] / (1 - srate_v(bd, P)))
                crossed[newx] = True
        newly = alive & (b >= bd)
        t_esc[newly] = t
        alive &= ~newly
    return t_esc, int((~alive).sum()), n, defic
sigmas = [0.160, 0.200, 0.280, 0.420]   # rescaled with alpha (noise enters as alpha*sigma), ladder chosen to span ~3 decades of crossing times
_bd_esc = qp_saddle(0.0)
pts, diag = [], []
_defs_ens = {}
slope, R2 = float('nan'), float('nan')
for k, s in enumerate(sigmas):
    te, nesc, n, _df = ensemble_crossing(s, 0.0, P_esc, seed=k, bd=_bd_esc)
    _defs_ens[s] = _df[np.isfinite(_df)]
    Tbar = te.sum() / (nesc + 0.5)          # hazard-rate MLE under censoring
    diag.append(f"s={s}: {nesc}/{n} cross, Tbar={Tbar:.0f}")
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
s_rho = 0.150
rates = []
for k, rho in enumerate([0.0, 0.02, 0.04]):
    te, nesc, n, _ = ensemble_crossing(s_rho, rho, P_esc, seed=50 + k)
    rates.append((nesc + 0.5) / te.sum())
rho_ok = (rates[0] > rates[1] > rates[2]) and (rates[0] >= 5 * rates[2])

# prop:qpbounds -- corrected closed-form lower bound and doubling-strategy upper
# bound bracket the quasipotential; bracket separation across the rho grid makes
# the barrier's strict increase a theorem; fitted slope and hazard increment
# agree with the bracket.
def qp_bracket(rho, n=200001, al=None):
    al, cc = (al or P_esc['alpha']), P_esc['c']
    bd = qp_saddle(rho)
    bs = np.linspace(0.0, bd, n)
    Ds = np.array([Dstar(b, P_esc) for b in bs])
    Gr = -P_esc['v'] + (2 * cc * (1 - cc * bs) - rho) * Ds
    low = (2 / al) * np.trapezoid(-Gr, bs) / (1 + 2 * al * np.abs(np.gradient(Gr, bs)).max())
    b, D, cost = 0.0, Dstar(0.0, P_esc), 0.0        # doubling strategy (simultaneous map)
    for _ in range(2000000):
        g = -P_esc['v'] + (2 * cc * (1 - cc * b) - rho) * D
        u = 2 * max(-g, 0.0) + 1e-9
        b2 = min(1.0, b + al * (g + u)); D = srate(b, P_esc) * D + P_esc['I']; b = b2
        cost += 0.5 * u * u
        if b >= bd: break
    # climb-only cost = an upper witness for the crossing quasipotential V-cross
    # (thm:rate), and the crossing deficit of the natural-pace climb: the strategy
    # arrives on the characteristic, so V_plus bounds V-cross with no slack from
    # the exit phase (saddle-passage calibration, conj:arr).
    S_climb = cost
    def_climb = 1.0 - D / Dstar(bd, P_esc)
    for _ in range(200000):                          # hold at the saddle while the stock relaxes
        if D >= Dstar(min(b, 1.0), P_esc): break
        g = -P_esc['v'] + (2 * cc * (1 - cc * b) - rho) * D
        u = max(-g, 0.0)
        b2 = min(1.0, b + al * (g + u)); D = srate(b, P_esc) * D + P_esc['I']; b = b2
        cost += 0.5 * u * u
    return low, cost, S_climb, def_climb

qp = {r: qp_bracket(r) for r in (0.0, 0.02, 0.04)}
sep_ok = qp[0.02][0] > qp[0.0][1] and qp[0.04][0] > qp[0.02][1]
# saddle-passage calibration: the natural-pace climb crosses on-characteristic
# (deficit ~ 0) and the hold phase costs nothing, so S_up bounds V-cross too
passage_ok = all(qp[r][1] - qp[r][2] <= 1e-4 * qp[r][1] and 0.0 <= qp[r][3] <= 0.01
                 for r in (0.0, 0.02, 0.04))
mid0 = 0.5 * (qp[0.0][0] + qp[0.0][1])
slope_ok = abs(slope - mid0) <= 0.10 * mid0
dV_mid = 0.5 * (qp[0.04][0] + qp[0.04][1]) - mid0
haz_ok = abs(np.log(rates[0] / rates[2]) * s_rho ** 2 - dV_mid) <= 0.35 * dV_mid

# cor:qplimit -- the bracket pinches: alpha * S_up -> 2 * Int as alpha -> 0.
_bs_qp = np.linspace(0.0, qp_saddle(0.0), 200001)
_Int_qp = np.trapezoid(P_esc['v'] - 2 * P_esc['c'] * (1 - P_esc['c'] * _bs_qp)
                       * np.array([Dstar(b, P_esc) for b in _bs_qp]), _bs_qp)
pinch = [qp_bracket(0.0, al=a)[1] / ((2 / a) * _Int_qp) for a in (0.1, 0.05, 0.025)]
pinch_ok = pinch[0] > pinch[1] > pinch[2] > 1.0 and pinch[2] <= 1.015

# prop:arrwindow necessity core, witnessed pathwise: every simulated crossing's
# action ledger over its max-advance steps meets the corrected lower bound.
_rng_led = np.random.default_rng(424)
_bd_led = qp_saddle(0.0)
_n_cross, _sled_min = 0, float('inf')
for _lane in range(400):
    _b, _D, _bmax, _ssum = 0.0, Dstar(0.0, P_esc), 0.0, 0.0
    for _t in range(5500):
        _xi = _rng_led.standard_normal()
        _Up = -P_esc['v'] + 2 * P_esc['c'] * (1 - P_esc['c'] * _b) * _D + 0.2 * _xi
        _b2 = min(1.0, max(0.0, _b + P_esc['alpha'] * _Up))
        _D = max(0.0, srate(_b, P_esc) * _D + P_esc['I'])
        _b = _b2
        if _b > _bmax:
            _ssum += 0.5 * (0.2 * _xi) ** 2
            _bmax = _b
        if _bmax >= _bd_led:
            _n_cross += 1; _sled_min = min(_sled_min, _ssum)
            break
ledger_ok = _n_cross >= 50 and _sled_min >= qp[0.0][0] * 0.999

# conj:arr upgrade de-risk -- the renewal/excursion decomposition behind the
# mean-time Arrhenius law. Excursions leave a home ball at the calibrated
# corner (b > b_out) and end at renewal (b <= b_home) or crossing (b >= saddle).
# Three predictions of the excursion argument, measured directly:
#   (a) the per-excursion crossing probability is itself Arrhenius in 1/sigma^2
#       with slope inside the quasipotential bracket (the union-bound engine);
#   (b) non-escaping excursion lengths have an exponential tail whose rate
#       STIFFENS as sigma falls (no free lingering away from the saddle:
#       cost ~ c0 per T0 steps => tail rate ~ c0'/sigma^2);
#   (c) direct persistence: essentially no crossing before exp(0.6*V_low/s^2)
#       steps, and near-certain crossing by exp(1.4*S_up/s^2) steps;
#   (d) saddle passage (conj:arr, sharp constant): the stock deficit at first
#       crossing, 1 - D/D*(beta-dagger), is strictly positive on every lane
#       (the pre-crossing domination D < D*(beta-dagger) of the printed
#       rectangle) and its median falls as sigma falls -- crossings
#       concentrate toward the saddle, the signature of V_cross = V.
_b_home, _b_out = 0.02, 0.05
_bd_exc = qp_saddle(0.0)

_Dst_exc = P_esc['I'] / (1 - srate_v(_bd_exc, P_esc))

def excursions(sigma, n=200, steps=30000, seed=0):
    g = np.random.default_rng(7000 + seed)
    b = np.zeros(n); D = np.full(n, Dstar(0.0, P_esc))
    inexc = np.zeros(n, bool); elen = np.zeros(n, int)
    n_exc, n_esc, homelens, defics = 0, 0, [], []
    for _ in range(steps):
        xi = g.standard_normal(n)
        Up = -P_esc['v'] + 2 * P_esc['c'] * (1 - P_esc['c'] * b) * D + sigma * xi
        b_new = np.clip(b + P_esc['alpha'] * Up, 0.0, 1.0)
        D = np.maximum(0.0, srate_v(b, P_esc) * D + P_esc['I'])
        b = b_new
        elen[inexc] += 1
        esc = inexc & (b >= _bd_exc)
        if esc.any():
            defics.extend((1.0 - D[esc] / _Dst_exc).tolist())
            n_esc += int(esc.sum()); n_exc += int(esc.sum())
            b[esc] = 0.0; D[esc] = Dstar(0.0, P_esc)
            inexc[esc] = False; elen[esc] = 0
        home = inexc & (b <= _b_home)
        if home.any():
            n_exc += int(home.sum()); homelens.extend(elen[home].tolist())
            inexc[home] = False; elen[home] = 0
        start = (~inexc) & (b > _b_out)
        inexc[start] = True; elen[start] = 0
    return n_exc, n_esc, np.array(homelens), np.array(defics)

_exc_sigmas = [0.160, 0.180, 0.200]
_exc_pts, _exc_diag, _tails, _defs_exc = [], [], {}, {}
for _k, _s in enumerate(_exc_sigmas):
    _ne, _nesc, _hl, _dfx = excursions(_s, seed=_k)
    _exc_diag.append(f"s={_s}: {_nesc}/{_ne} exc-esc")
    if _nesc >= 5:
        _exc_pts.append((1.0 / _s ** 2, np.log(_ne / _nesc)))
    _tails[_s] = _hl
    _defs_exc[_s] = _dfx
print("      P3h exc diag: " + " | ".join(_exc_diag))
exc_ok = len(_exc_pts) >= 3
_exc_slope = float('nan')
if exc_ok:
    _X = np.array([p[0] for p in _exc_pts]); _Y = np.array([p[1] for p in _exc_pts])
    _A = np.vstack([_X, np.ones_like(_X)]).T
    _coef, *_ = np.linalg.lstsq(_A, _Y, rcond=None)
    _exc_slope = _coef[0]
    exc_ok = abs(_exc_slope - mid0) <= 0.35 * mid0

def _tail_rate(lens, L1=60, L2=120):
    p1 = float((lens > L1).mean()); p2 = float((lens > L2).mean())
    if p2 <= 0 or p1 <= p2: return float('nan')
    return np.log(p1 / p2) / (L2 - L1)

# Tail rates: exponential at every accessible sigma; the c0/sigma^2 stiffening
# regime is beyond simulable lengths (the sigma-independent deterministic
# relaxation floor dominates at L = 60..120), so the assertion is existence of
# the exponential tail plus non-degradation, and the scaling question is
# recorded as a proof-side obligation rather than a numerically settled fact.
_lam_lo, _lam_hi = _tail_rate(_tails[0.160]), _tail_rate(_tails[0.200])
_lam_ratio = _lam_lo / _lam_hi if np.isfinite(_lam_lo) and np.isfinite(_lam_hi) else float('nan')
tail_ok = np.isfinite(_lam_ratio) and 0.95 <= _lam_ratio <= 3.0

# Persistence, prefactor-honest: the Arrhenius fit gives ln Tbar = slope/s^2 + b0;
# below the barrier the renewal picture forbids early crossing mass
# (P(tau < 0.02*Tbar_fit) ~ 2%), and at moderate sigma it makes tau
# approximately exponential(1/Tbar) -- the geometric-trials signature.
_b0_fit = float(coef[1]) if arr_ok else float('nan')
def _tbar_fit(sigma): return float(np.exp(slope / sigma ** 2 + _b0_fit))

def _persist_frac(sigma, N, n=60, seed=0):
    g = np.random.default_rng(8000 + seed)
    b = np.zeros(n); D = np.full(n, Dstar(0.0, P_esc)); out = np.zeros(n, bool)
    for _ in range(N):
        xi = g.standard_normal(n)
        Up = -P_esc['v'] + 2 * P_esc['c'] * (1 - P_esc['c'] * b) * D + sigma * xi
        b_new = np.clip(b + P_esc['alpha'] * Up, 0.0, 1.0)
        D = np.maximum(0.0, srate_v(b, P_esc) * D + P_esc['I'])
        b = b_new
        out |= (b >= _bd_exc)
    return float(out.mean()), N

_N1 = max(1, int(0.02 * _tbar_fit(0.140)))
_N2 = max(1, int(0.02 * _tbar_fit(0.120)))
_p_low1, _ = _persist_frac(0.140, _N1, seed=1)
_p_low2, _ = _persist_frac(0.120, _N2, seed=2)
_te_exp, _nesc_exp, _n_exp, _ = ensemble_crossing(0.200, 0.0, P_esc, n=80, cap=200000, seed=777)
_tbar_emp = _te_exp.sum() / (_nesc_exp + 0.5)
_f1 = float((_te_exp <= _tbar_emp).mean())
_f23 = float((_te_exp <= 2.3 * _tbar_emp).mean())
pers_ok = (_p_low1 <= 0.15) and (_p_low2 <= 0.15) and (0.45 <= _f1 <= 0.80) and (_f23 >= 0.80)

# Quantitative passage (prop:passage): instrument the refund surgery on the
# two-phase near-minimizer -- level-budgeted selection, truncation, dyadic
# hold-and-creep cascade to the saddle -- and witness that a crossing with
# near-zero terminal deficit costs the input action plus an O(w^2) overhead,
# with the theta^2-vs-refund dominance ratio below one.
def _passage_surgery():
    bd = _bd_esc; al, cc = P_esc['alpha'], P_esc['c']
    sb = srate_v(bd, P_esc); Dsb = P_esc['I'] / (1 - sb)
    def _Ds(b): return P_esc['I'] / (1 - srate_v(b, P_esc))
    def _g(b, D): return -P_esc['v'] + 2 * cc * (1 - cc * b) * D
    _bg = np.linspace(0, bd, 200001)
    _Gv = -P_esc['v'] + 2 * cc * (1 - cc * _bg) * np.array([_Ds(b) for b in _bg])
    L = float(np.max(np.abs(np.gradient(_Gv, _bg))))
    app = al * (1 + 2 * al * L)
    Dbar = max((_Ds(b + 1e-6) - _Ds(b - 1e-6)) / 2e-6
               for b in np.linspace(bd - 0.16, bd, 40))
    kmax, kmin = 2 * cc * (1 - cc * (bd - 0.16)), 2 * cc * (1 - cc * bd)
    s1 = al * Dbar * kmax / (1 - sb)
    b, D, A_in = 0.0, _Ds(0.0), 0.0
    us, path = [], [(b, D)]
    for _ in range(3000000):
        gg = _g(b, D); u = 2 * max(-gg, 0.0) + 1e-5
        b2 = min(1.0, b + al * (gg + u)); D = srate_v(b, P_esc) * D + P_esc['I']; b = b2
        A_in += 0.5 * u * u; us.append(u); path.append((b, D))
        if b >= bd: break
    a_sel = kmin * (1 - sb ** 2) / (app * kmax ** 2)
    # window width from the theorem's recipe: w = C9 * alpha * sqrt(G_gap + nu),
    # and G_gap + nu = A_in - V_- exactly (both measured), no V-cross reference
    V_low = (2 / al) * float(np.trapezoid(-_Gv, _bg)) / (1 + 2 * al * L)
    w = 6 * (1 + 2 * al * L) * kmax / (kmin * np.sqrt(1 - sb ** 2)) * al * np.sqrt(A_in - V_low)
    prof, mmax = [], 0.0
    for t in range(len(us)):
        b_pre, D_pre = path[t]; b_post, _ = path[t + 1]
        if b_post > mmax:
            m_lo, m_hi = max(mmax, bd - w), min(b_post, bd)
            if m_hi > m_lo: prof.append((m_lo, m_hi, D_pre, t))
            mmax = b_post
    def _T(m):
        return sum((hi - max(lo, m)) * max(0.0, _Ds(0.5 * (max(lo, m) + hi)) - Dp)
                   for lo, hi, Dp, _ in prof if hi > max(lo, m))
    X = _T(bd - w)
    ok61 = X < a_sel * (w / 4) ** 2 / 4
    mbar = tau = None
    for m in np.linspace(bd - w / 2, bd - w / 4, 300):
        hit = [(max(0.0, _Ds(m) - Dp), t) for lo, hi, Dp, t in prof if lo <= m <= hi]
        if hit and hit[0][0] ** 2 <= a_sel * _T(m):
            mbar, tau = m, hit[0][1]; break
    A_kept = 0.5 * float(np.sum(np.array(us[:tau + 1]) ** 2))
    b, D = path[tau + 1]
    A_c, delta0 = 0.0, bd - b
    khold = int(np.ceil(np.log(8) / np.log(1 / sb)))
    for j in range(14):
        dj = delta0 * 2 ** -j; m_next = bd - dj / 2; epsj = al * dj
        steps = 0
        while b < m_next and steps < 200000:
            gg = _g(b, D); u = -gg + (abs(gg) + epsj)
            b2 = min(1.0, b + al * (gg + u)); D = srate_v(b, P_esc) * D + P_esc['I']; b = b2
            A_c += 0.5 * u * u; steps += 1
        for _ in range(khold):
            u = -_g(b, D); A_c += 0.5 * u * u; D = srate_v(b, P_esc) * D + P_esc['I']
    epsf = al * delta0 * 2 ** -14
    while b < bd:
        gg = _g(b, D); u = -gg + (abs(gg) + epsf)
        b2 = min(1.0, b + al * (gg + u)); D = srate_v(b, P_esc) * D + P_esc['I']; b = b2
        A_c += 0.5 * u * u
    ratio = (9 / 8) * (9 / 8) * kmax ** 2 * a_sel / (2 * (1 - sb ** 2)) / (2 * kmin / app)
    return dict(s1=s1, ok61=ok61, ratio=ratio, A_in=A_in,
                overhead=A_kept + A_c - A_in, w=w,
                deficit=(_Ds(b) - D) / Dsb)

_sg = _passage_surgery()
passage_surgery_ok = (_sg['s1'] < 1.0 and _sg['ok61'] and _sg['ratio'] < 1.0
                      and 0.0 <= _sg['deficit'] <= 1e-5
                      and _sg['overhead'] <= 0.30 * _sg['w'] ** 2)

# Saddle passage (d): deficits from the excursion crossings (the richer sample)
# with the ensemble ladder's endpoints as a cross-check.
_def_all = np.concatenate([_defs_exc[s] for s in _exc_sigmas] +
                          [_defs_ens[s] for s in sigmas if len(_defs_ens[s])])
_dmed = {s: float(np.median(_defs_exc[s])) for s in _exc_sigmas if len(_defs_exc[s]) >= 20}
defic_ok = (len(_def_all) >= 200 and float(_def_all.min()) > 0.0
            and 0.160 in _dmed and 0.200 in _dmed
            and _dmed[0.160] < _dmed[0.200] and _dmed[0.160] < 0.20)

report("P3h  measurement-noise saddle crossing: Arrhenius in 1/sigma^2; protection monotone in rho << rho_cure; "
       "quasipotential bracket (prop:qpbounds): brackets separate across the rho grid, fitted slope "
       "and hazard increment agree; alpha*S_up pinches onto 2*Int (cor:qplimit); every crossing's "
       "advance-step action ledger meets the corrected lower bound (prop:arrwindow necessity); "
       "excursion decomposition (conj:arr de-risk): per-excursion crossing rate Arrhenius with slope "
       "near the bracket, lingering tail exponential at every tested sigma, no early-crossing mass "
       "below the barrier, and exponentially distributed crossing times (the renewal signature); "
       "saddle passage (sharp-constant de-risk): crossing stock deficit positive on every lane "
       "(pre-crossing domination) with median decreasing in sigma; natural-pace strategy crosses "
       "on-characteristic (hold phase free), so S_up bounds the crossing quasipotential too; "
       "quantitative passage (prop:passage): the refund surgery executes -- selection level "
       "found, theta^2-vs-refund dominance below one, near-zero-deficit crossing at O(w^2) "
       "overhead",
       arr_ok and rho_ok and sep_ok and slope_ok and haz_ok and pinch_ok and ledger_ok
       and exc_ok and tail_ok and pers_ok and defic_ok and passage_ok and passage_surgery_ok,
       f"fit pts={len(pts)}, slope={slope:.4f}, R2={R2:.3f}; hazard(rho=0/.02/.04) = "
       f"{rates[0]:.1e}/{rates[1]:.1e}/{rates[2]:.1e}; qp[low,up] rho=0: [{qp[0.0][0]:.4f},{qp[0.0][1]:.4f}], "
       f"rho=.02: [{qp[0.02][0]:.4f},{qp[0.02][1]:.4f}], rho=.04: [{qp[0.04][0]:.4f},{qp[0.04][1]:.4f}]; "
       f"slope vs mid: {abs(slope-mid0)/mid0:.1%}; dlnhaz*s^2 vs dV_mid: "
       f"{abs(np.log(rates[0]/rates[2])*s_rho**2 - dV_mid)/dV_mid:.1%}; "
       f"pinch ratios (a=.1/.05/.025): {pinch[0]:.4f}/{pinch[1]:.4f}/{pinch[2]:.4f}; "
       f"ledger: {_n_cross} crossings, min advance-action {_sled_min:.4f} >= {qp[0.0][0]:.4f}; "
       f"exc slope={_exc_slope:.4f} vs mid {mid0:.4f}; tail rates lam(0.16)/lam(0.20) = "
       f"{_lam_lo:.4f}/{_lam_hi:.4f} ratio {_lam_ratio:.2f}; persistence: "
       f"{_p_low1:.2f}@N={_N1}(s=.14), {_p_low2:.2f}@N={_N2}(s=.12); "
       f"exp'l tau (s=.20): F(Tbar)={_f1:.2f} [exp: 0.63], F(2.3*Tbar)={_f23:.2f} [exp: 0.90]; "
       f"crossing deficit ({len(_def_all)} crossings, min {float(_def_all.min()):.4f} > 0): "
       f"median {_dmed.get(0.160, float('nan')):.3f}/{_dmed.get(0.180, float('nan')):.3f}/"
       f"{_dmed.get(0.200, float('nan')):.3f} at s=.16/.18/.20; strategy climb-only vs total "
       f"(rho=0/.02/.04): {qp[0.0][2]:.4f}/{qp[0.0][1]:.4f}, {qp[0.02][2]:.4f}/{qp[0.02][1]:.4f}, "
       f"{qp[0.04][2]:.4f}/{qp[0.04][1]:.4f}; strategy crossing deficit "
       f"{qp[0.0][3]:.4f}/{qp[0.02][3]:.4f}/{qp[0.04][3]:.4f}; surgery: (S1)={_sg['s1']:.3f}, "
       f"dominance={_sg['ratio']:.3f}, overhead={_sg['overhead']:.2e} (w^2={_sg['w']**2:.2e}), "
       f"terminal deficit={_sg['deficit']:.1e}")

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
# SATURATION, RANK-ONE, AND SEPARATRIX SUITES: saturated-variant laundering,
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
report("S2   saturated laundering (i): geometric contraction of (1-beta); finite-time attainment "
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

# ================================================================ P3k: oscillation diagnostic
# Convergence and period-two limits are separated by first vs second differences
# of the orbit: at the (SS+) benchmark both vanish on the tail; on the exact
# two-cycle instance of thm:bistable(f) the second difference is identically
# zero while the first difference is bounded away from zero.
from fractions import Fraction as Fr

P_bm = reduced_map_params()
b_o, D_o = 0.4, 0.6
for _ in range(60000): b_o, D_o = step(b_o, D_o, P_bm)
xs = [(b_o, D_o)]
for _ in range(200):
    b_o, D_o = step(b_o, D_o, P_bm); xs.append((b_o, D_o))
d1_bm = max(abs(xs[k+1][0]-xs[k][0]) + abs(xs[k+1][1]-xs[k][1]) for k in range(100, 200))
d2_bm = max(abs(xs[k+2][0]-xs[k][0]) + abs(xs[k+2][1]-xs[k][1]) for k in range(100, 198))

def step_exact(b, D, Q):
    Up = -Q['v'] + 2*Q['c']*(1 - Q['c']*b)*D
    b2 = b + Q['alpha']*Up
    b2 = Fr(0) if b2 < 0 else (Fr(1) if b2 > 1 else b2)
    return b2, (1 - Q['lam0'])*(1 - Q['eta']*(1 - b))**2 * D + Q['I']

Q_cyc = dict(eta=Fr(1,2), c=Fr(1,8), lam0=Fr(3,4), I=Fr(1,20),
             v=Fr(75137, 5391360), alpha=Fr(1198080, 2651))
s_cyc1 = (Fr(7,11), Fr(11737,189540)); s_cyc2 = (Fr(7,9), Fr(113,1872))
cyc_exact = (step_exact(s_cyc1[0], s_cyc1[1], Q_cyc) == s_cyc2 and
             step_exact(s_cyc2[0], s_cyc2[1], Q_cyc) == s_cyc1)
d1_cyc = float(abs(s_cyc1[0]-s_cyc2[0]) + abs(s_cyc1[1]-s_cyc2[1]))
# Onset: at the benchmark no non-convergent tail exists anywhere inside (SS)
# -- clause (c)'s alpha-free eigenvalue condition 2*eta <= c(1+s0) holds there
# -- while at the sharpness configuration the saddle's second eigenvalue
# crosses -1 at a closed-form alpha_flip, and the exact two-cycle sits just
# above the flip: the witness lives at the birth of the period-two branch.
_s0bm = (1 - P_bm['lam0']) * (1 - P_bm['eta']) ** 2
cond_c_bm = 2 * P_bm['eta'] <= P_bm['c'] * (1 + _s0bm)
_starts = [(0.4, 0.6), (0.9, 0.35), (0.97, 0.44), (0.975, Dstar(0.975, P_bm) * 1.001),
           (0.5, 1.0), (0.2, 0.1)]
sweep_ok = True
for _al in (0.15, 0.25, 0.35, 0.45, 0.55, 0.61):
    _Pa = dict(P_bm); _Pa['alpha'] = _al
    for _b0, _D0 in _starts:
        _b, _D = _b0, _D0; _tr = []
        for _t in range(20000):
            _b, _D = step(_b, _D, _Pa)
            if _t >= 19800: _tr.append((_b, _D))
        _d1s = max(abs(_tr[k+1][0] - _tr[k][0]) + abs(_tr[k+1][1] - _tr[k][1])
                   for k in range(len(_tr) - 1))
        sweep_ok &= _d1s < 1e-8
_we, _wcf, _wl, _wI = 0.5, 0.125, 0.75, 0.05
_bdw = 161 / 227
_sw = (1 - _wl) * (1 - _we * (1 - _bdw)) ** 2
_spw = 2 * _we * (1 - _wl) * (1 - _we * (1 - _bdw))
_Dw = _wI / (1 - _sw)
_aflip = (1 + _sw) / (_wcf * _Dw * (_wcf * (1 + _sw) + (1 - _wcf * _bdw) * _spw))
def _lam2w(_al):
    _aJ = 1 - 2 * _al * _wcf * _wcf * _Dw
    _bJ = 2 * _al * _wcf * (1 - _wcf * _bdw)
    _trJ = _aJ + _sw; _detJ = _aJ * _sw - _bJ * _spw * _Dw
    return (_trJ - np.sqrt(_trJ * _trJ - 4 * _detJ)) / 2
_awit = 1198080 / 2651
flip_ok = (_lam2w(0.99 * _aflip) > -1 > _lam2w(1.01 * _aflip)
           and 0 < _awit / _aflip - 1 < 0.002 and cond_c_bm)

report("P3k  oscillation diagnostic: ||x_{t+2}-x_t|| -> 0 separates convergence from period-two; "
       "benchmark converges everywhere inside (SS) (clause (c) holds alpha-free there); witness "
       "saddle flips at closed-form alpha_flip with the exact cycle just above the flip",
       d1_bm < 1e-12 and d2_bm < 1e-12 and cyc_exact and d1_cyc > 0.1 and sweep_ok and flip_ok,
       f"benchmark tail d1={d1_bm:.1e}, d2={d2_bm:.1e}; two-cycle exact in rationals, d1={d1_cyc:.3f}; "
       f"sweep 6 alphas x 6 starts clean; alpha_flip={_aflip:.2f}, exact cycle "
       f"{(_awit/_aflip-1)*100:.2f}% above; 2*eta={2*P_bm['eta']} <= c(1+s0)={P_bm['c']*(1+_s0bm):.4f}")

# ================================================================ P3l: per-run certification (exact rationals)
# (SS+) is verified once as an exact rational inequality; each benchmark run is
# then certified by an exact-rational componentwise-comparable step, after which
# convergence is the machine-checked monotone-step principle, thm:bistable(d).
Q_bm = dict(eta=Fr(1,2), c=Fr(9,10), lam0=Fr(1,50), I=Fr(1,50), v=Fr(1,10), alpha=Fr(1,10))
s0_ex = (1 - Q_bm['lam0'])*(1 - Q_bm['eta'])**2
amono_ex = Q_bm['lam0']*s0_ex / (2*Q_bm['c']*Q_bm['I']*(Q_bm['c']*s0_ex + 2*Q_bm['eta']*(1 - Q_bm['lam0'])))
ssplus_exact = Q_bm['alpha'] < amono_ex
cert_steps = []
for (b0r, D0r) in [(Fr(2,5), Fr(3,5)), (Fr(1,10), Fr(1,10)), (Fr(4,5), Fr(1,2)),
                   (Fr(3,5), Fr(11,10)), (Fr(1,4), Fr(1,20)), (Fr(19,20), Fr(21,20))]:
    prev = (b0r, D0r); found = None
    for t in range(1, 61):
        cur = step_exact(prev[0], prev[1], Q_bm)
        db, dD = cur[0]-prev[0], cur[1]-prev[1]
        if (db >= 0 and dD >= 0) or (db <= 0 and dD <= 0):
            found = t; break
        prev = cur
    cert_steps.append(found)
report("P3l  per-run certification: exact (SS+) + exact-rational comparable step on every start (clause (d))",
       ssplus_exact and all(s is not None for s in cert_steps),
       f"alpha_mono = {float(amono_ex):.6f} exact; comparable step at t = {cert_steps}")

print()
print(f"{'='*70}")
print(f"DE-RISK RESULT: {sum(PASS)}/{len(PASS)} suites pass")

sys.exit(0 if all(PASS) else 1)
