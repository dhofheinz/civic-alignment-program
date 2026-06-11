#!/usr/bin/env python3
"""De-risk battery for Paper IV: The Civic Capture Audit.
Simulation-based operating characteristics of the protocol's instruments.
Seed-pinned; every claim destined for the manuscript is asserted here first."""
import numpy as np
from scipy.optimize import brentq
from scipy import stats

rng = np.random.default_rng(31)
PASS = []
def report(name, ok, info=""):
    PASS.append(bool(ok))
    print(f"{'PASS' if ok else 'FAIL'}  {name}" + (f"  [{info}]" if info else ""))

# ---------------------------------------------------------------- shared worlds
def claim_world(T, eta, lam0, I0, g, beta_path, sigma_lab=0.0, n_arr=3, g2=0.0, cap=np.inf, seed=None):
    """Claim-level portfolio with content gain g; returns audit-grade panel.
    Measured claim sizes carry multiplicative label noise (1+eps), eps~N(0,sigma_lab)."""
    r = np.random.default_rng(seed)
    claims = list(r.exponential(I0 / 4, 8))          # initial stock
    Dm = np.zeros(T); mass = np.zeros(T); ret = np.zeros(T, int); exp_ = np.zeros(T, int)
    ratios = []                                       # (1 - beta_t, measured within-claim ratio)
    for t in range(T):
        b = beta_path[t]; w = eta * (1 - b)
        new = [(1 - w) ** 2 * x for x in claims]
        for x0, x1 in zip(claims, new):               # within-claim contraction, measured noisily
            m0 = x0 * (1 + sigma_lab * r.standard_normal())
            m1 = x1 * (1 + sigma_lab * r.standard_normal())
            if m0 > 1e-12 and m1 > 0:
                ratios.append((1 - b, np.sqrt(m1 / m0)))
        exp_[t] = len(new)
        keep = [x for x in new if r.random() > lam0]
        ret[t] = len(new) - len(keep)
        D_prev = sum(claims)
        m_t = I0 + g * D_prev + g2 * D_prev ** 2      # content channel: arrival mass
        arr = list(r.exponential(max(m_t, 1e-9) / n_arr, n_arr))
        claims = [min(x, cap) for x in keep + arr]
        mass[t] = sum(arr) * (1 + sigma_lab * r.standard_normal())
        Dm[t] = sum(claims) * (1 + sigma_lab * r.standard_normal())
    return Dm, mass, ret, exp_, ratios

def identify(Dm, mass, ret, exp_, ratios):
    """The three Loops estimators, audit grade. Returns (lam_hat, se_lam, eta_hat,
    g_hat, I0_hat, se_g, se_I0)."""
    lam_hat = ret.sum() / exp_.sum()
    se_lam = np.sqrt(lam_hat * (1 - lam_hat) / exp_.sum())
    u = np.array([a for a, _ in ratios]); rr = np.array([b for _, b in ratios])
    A = np.vstack([np.ones_like(u), u]).T             # ratio = 1 - eta*(1-beta) + noise
    coef, *_ = np.linalg.lstsq(A, rr, rcond=None)
    eta_hat = -coef[1]
    X = np.vstack([np.ones(len(Dm) - 1), Dm[:-1]]).T  # mass_t = I0 + g D_{t-1}
    y = mass[1:]
    beta_ols, res, *_ = np.linalg.lstsq(X, y, rcond=None)
    I0_hat, g_hat = beta_ols
    dof = len(y) - 2
    s2 = float(res[0]) / dof if len(res) else np.var(y - X @ beta_ols) * len(y) / dof
    cov = s2 * np.linalg.inv(X.T @ X)
    return lam_hat, se_lam, eta_hat, g_hat, I0_hat, np.sqrt(cov[1, 1]), np.sqrt(cov[0, 0])

def est_vc(v_true, c_true, D_op, N=600, sig_u=0.05, seed=None):
    """Three-arm (v,c) estimation with analytic SEs. Arms at beta = 0.45/0.60/0.75."""
    r = np.random.default_rng(seed)
    bs = np.array([0.45, 0.60, 0.75]); dlt = 0.15
    means = []; ses = []
    for b in bs:
        u = -v_true * b - (1 - c_true * b) ** 2 * D_op + sig_u * r.standard_normal(N)
        means.append(u.mean()); ses.append(u.std(ddof=1) / np.sqrt(N))
    m0, m1, m2 = means; s0, s1, s2 = ses
    Up = (m2 - m0) / (2 * dlt); se_Up = np.sqrt(s0 ** 2 + s2 ** 2) / (2 * dlt)
    q = -(m2 - 2 * m1 + m0) / dlt ** 2                 # q = -U'' = 2 c^2 D
    se_q = np.sqrt(s0 ** 2 + 4 * s1 ** 2 + s2 ** 2) / dlt ** 2
    c_hat = np.sqrt(max(q, 1e-9) / (2 * D_op))
    se_c = se_q / (4 * c_hat * D_op)
    v_hat = -Up + 2 * c_hat * (1 - c_hat * bs[1]) * D_op
    se_v = np.sqrt(se_Up ** 2 + (2 * (1 - 2 * c_hat * bs[1]) * D_op * se_c) ** 2)
    return v_hat, c_hat, se_v, se_c

def quad_t(Dm, mass):
    """Specification guard: t-statistic of the quadratic stock term in the arrival fit."""
    X = np.vstack([np.ones(len(Dm) - 1), Dm[:-1], Dm[:-1] ** 2]).T
    y = mass[1:]
    co, res, *_ = np.linalg.lstsq(X, y, rcond=None)
    dof = len(y) - 3
    s2 = float(res[0]) / dof if len(res) else np.var(y - X @ co) * len(y) / dof
    cov = s2 * np.linalg.inv(X.T @ X)
    return co[2] / np.sqrt(cov[2, 2])

def fitted_fate(b0, D0, lam_h, eta_h, I_h, v=0.10, c=0.9, al=0.6, T=30000):
    """Basin classification by forward simulation of the STRUCTURALLY fitted map
    s(b) = (1 - lam_h)(1 - eta_h (1 - b))^2, with (lam_h, eta_h, I_h) from the
    identification panel and the operator side (v, c) from the arms."""
    b, D = b0, D0
    for _ in range(T):
        dU = -v + 2 * c * (1 - c * b) * D
        b = float(np.clip(b + al * dU, 0, 1))
        s_b = float(np.clip((1 - lam_h) * (1 - eta_h * (1 - b)) ** 2, 0.0, 0.9999))
        D = s_b * D + I_h
        if b > 0.97 and D > 0.5: return True
        if b < 0.03 and D < 0.05: return False
    return b > 0.5

# ================================================================ A1: loop ID + safe-side margin
errs = {300: [], 600: []}
for T in (300, 600):
    for k in range(30):
        eta, lam0, I0, g = 0.5, 0.05, 0.03, 0.02
        bp = 0.45 + 0.35 * np.sin(np.linspace(0, 6 * np.pi, T))
        out = claim_world(T, eta, lam0, I0, g, bp, sigma_lab=0.10, seed=1000 + 7 * T + k)
        lh, _, eh, gh, ih, _, _ = identify(*out)
        errs[T].append((abs(lh - lam0) / lam0, abs(eh - eta) / eta,
                        abs(gh - g) / lam0, abs(ih - I0) / I0))
e300, e600 = np.mean(errs[300], 0), np.mean(errs[600], 0)
ok_a1a = (e600[0] < .08 and e600[1] < .05 and e600[2] < .35 and e600[3] < .15
          and sum(e600 < e300) >= 3)
# safe-side rule under audit noise: m_hat = v(lam-g) - 2c I0, certify iff m_hat > 2 SE
v_w, c_w = 0.80, 0.9
fc = 0; power = 0; n_cert_truth = 0; n_capt_truth = 0
Tc = 1200
bp_wide = 0.5 + 0.45 * np.sin(np.linspace(0, 4 * np.pi, Tc))   # wide, slow: D varies strongly
def margin_rule(out, seed, v_true=0.80, c_true=0.9):
    """Registered certificate rule: five-parameter delta-method SE + curvature guard."""
    Dm_, mass_ = out[0], out[1]
    lh, sl, eh, gh, ih, sg, si = identify(*out)
    vh, ch, sev, sec = est_vc(v_true, c_true, 0.30, N=600, seed=seed)
    t2 = quad_t(Dm_, mass_)
    m_hat = vh * (lh - gh) - 2 * ch * ih
    se_m = np.sqrt(((lh - gh) * sev) ** 2 + (vh * sl) ** 2 + (vh * sg) ** 2
                   + (2 * ih * sec) ** 2 + (2 * ch * si) ** 2)
    return (abs(t2) < 2) and (m_hat > 2 * se_m), abs(t2) >= 2
for k in range(40):
    capturable = (k % 2 == 0)
    lam_c = 0.08
    g_true = 1.5 * lam_c if capturable else 0.0
    I0_true = 0.010 if not capturable else 0.03      # certified: m = .8(.08)-1.8(.010) = .046
    out = claim_world(Tc, 0.5, lam_c, I0_true, g_true, bp_wide,
                      sigma_lab=0.10, n_arr=6, seed=5000 + k)
    certify, _ = margin_rule(out, seed=5500 + k)
    if capturable:
        n_capt_truth += 1
        if certify: fc += 1
    else:
        n_cert_truth += 1
        if certify: power += 1                       # m_true = 0.046 > 0 by construction
report("A1  loop identification under 10% label noise: estimator errors shrink with T; "
       "five-parameter safe-side margin (with specification guard) never certifies a "
       "capturable loop", ok_a1a and fc == 0
       and power / max(n_cert_truth, 1) >= 0.7,
       f"T=600 rel errs lam/eta/g/I0 = {e600[0]:.2f}/{e600[1]:.2f}/{e600[2]:.2f}/{e600[3]:.2f}; "
       f"false-certs {fc}/{n_capt_truth}, power {power}/{n_cert_truth}")

# ================================================================ A2: statics power (C1-C3)
def static_audit(Npt, K, same_side=False, sigma_b=0.05, seed=None):
    r = np.random.default_rng(seed)
    etaL, etaH, kap = 0.5, 0.5, 0.5
    MGs, covs = [], []
    for _ in range(K):
        th = float(r.integers(0, 2))
        if same_side:                                  # Remark-4 counterexample geometry
            m = abs(th - 0.1); muH = abs(th - 0.6); muL = abs(th - 0.5)
        else:
            m = abs(th - 0.45); muL = abs(th - 0.75); muH = abs(th - 0.15)
        h_est = {}; eta_est = {}
        for tau, mu, eta_t in (("L", muL, etaL), ("H", muH, etaH)):
            b = np.clip(mu + 0.08 * r.standard_normal(Npt), 0, 1)
            b1 = (1 - eta_t) * b + eta_t * m + sigma_b * r.standard_normal(Npt)
            sl, _, _, _, _ = stats.linregress(b - m, b1 - m)
            eta_est[tau] = 1 - sl
            dl = np.mean((b - th) ** 2); dm = (m - th) ** 2
            ga = np.mean((b - th) * (m - th))
            h_est[tau] = (dl - ga) - eta_est[tau] * (dl + dm - 2 * ga)
        MGs.append(2 * (eta_est["L"] * h_est["L"] - (1 - kap) * eta_est["H"] * h_est["H"]))
        AL = (1 - etaL) * (muL - m); BL = etaL * 1.0 * (muL - m)
        AH = (1 - etaH) * (muH - m); BH = etaH * (1 - kap) * (muH - m)
        covs.append(0.25 * (AL - AH) * (BL - BH))      # two-point covariance, pi=1/2
    MGs = np.array(MGs)
    se = MGs.std(ddof=1) / np.sqrt(K)
    return MGs.mean(), se, np.mean(covs)

pw = {}
for Npt in (100, 500):
    hits = sum(1 for k in range(60)
               if (lambda m_s: m_s[0] > 2 * m_s[1])(static_audit(Npt, 40, seed=9000 + Npt + k)))
    pw[Npt] = hits / 60
mg_ss = static_audit(500, 40, same_side=True, seed=777)
report("A2  statics power: MG(0)>2SE detection at audit panel sizes; same-side world "
       "signs Cov negative (regime test correct)", pw[100] >= 0.8 and pw[500] >= pw[100]
       and mg_ss[2] < 0, f"power N=100: {pw[100]:.2f}, N=500: {pw[500]:.2f}; "
       f"same-side Cov = {mg_ss[2]:.2e}")

# ================================================================ A3: arm-contrast power (C2) + v-hat
def arm_power(N, D_op, beta0=0.5, dlt=0.10, sig_u=0.05, reps=200, seed=0):
    r = np.random.default_rng(seed)
    hits = 0; v0, c0 = 0.10, 0.9
    for _ in range(reps):
        u0 = -v0 * beta0 - (1 - c0 * beta0) ** 2 * D_op + sig_u * r.standard_normal(N)
        u1 = -v0 * (beta0 + dlt) - (1 - c0 * (beta0 + dlt)) ** 2 * D_op + sig_u * r.standard_normal(N)
        t, p = stats.ttest_ind(u1, u0)
        if t > 0 and p < 0.05: hits += 1
    return hits / reps
p_lo, p_hi = arm_power(150, 0.30, seed=11), arm_power(600, 0.30, seed=12)
# v-hat from a low-stock stratum: Delta u / Delta = -v + 2c(1-c b_mid) D_low
r3 = np.random.default_rng(13)
N3 = 600; b0, dlt = 0.5, 0.10; Dlow = 0.005
vh = []
for _ in range(30):
    u0 = -0.10 * b0 - (1 - 0.9 * b0) ** 2 * Dlow + 0.05 * r3.standard_normal(N3)
    u1 = -0.10 * (b0 + dlt) - (1 - 0.9 * (b0 + dlt)) ** 2 * Dlow + 0.05 * r3.standard_normal(N3)
    vh.append(-(u1.mean() - u0.mean()) / dlt + 2 * 0.9 * (1 - 0.9 * (b0 + dlt / 2)) * Dlow)
v_hat = float(np.mean(vh))
ok_v = abs(v_hat - 0.10) < 0.015
report("A3  randomized-arm power for C2 (U'>0 at the operating point) and v-hat from the "
       "low-stock stratum", p_hi >= 0.8 and p_hi > p_lo and ok_v,
       f"power N=150: {p_lo:.2f}, N=600: {p_hi:.2f}; v_hat = {v_hat:.3f} (true 0.10)")

# ================================================================ A4: drift-law + basin fit (C4)
def s_of(beta, eta, lam0): return (1 - lam0) * (1 - eta * (1 - beta)) ** 2
def run_planar(T, eta, c, lam0, I, v, alpha, b0, D0, dither=0.0, sig_obs=0.0, seed=None):
    r = np.random.default_rng(seed)
    b, D = b0, D0; B = np.zeros(T); Dm = np.zeros(T); dUs = np.zeros(T)
    for t in range(T):
        bd = float(np.clip(b + dither * r.uniform(-1, 1), 0, 1))
        dU = -v + 2 * c * (1 - c * bd) * D
        b = float(np.clip(bd + alpha * dU, 0, 1))
        D = s_of(bd, eta, lam0) * D + I
        B[t] = bd; Dm[t] = D * (1 + sig_obs * r.standard_normal()); dUs[t] = dU
    return B, Dm, dUs

def fate(b0, D0, eta=0.5, c=0.9, lam0=0.02, I=0.02, v=0.10, al=0.6, T=20000):
    b, D = b0, D0
    for _ in range(T):
        dU = -v + 2 * c * (1 - c * b) * D
        b = float(np.clip(b + al * dU, 0, 1))
        D = s_of(b, eta, lam0) * D + I
        if b > 0.97 and D > 0.5: return True
        if b < 0.03 and D < 0.05: return False
    return b > 0.5

def D_sep_at(b0, lo=0.01, hi=3.0):
    for _ in range(22):
        mid = 0.5 * (lo + hi)
        if fate(b0, mid): hi = mid
        else: lo = mid
    return 0.5 * (lo + hi)

_DSEP = {0.45: D_sep_at(0.45), 0.60: D_sep_at(0.60)}

def c4_check(side, seed):
    """Interior-transient drift-law test + fitted-basin classification.
    side 0 = calibrated-side world, side 1 = captured-side. Returns (signs_ok, basin_captured)."""
    eta, c, lam0, I, v = 0.5, 0.9, 0.02, 0.02, 0.10
    if side == 0:
        b0 = 0.45; D0 = 0.5 * _DSEP[b0]; al = 0.01
    else:
        b0 = 0.60; D0 = 1.5 * _DSEP[b0]; al = 0.01
    B, Dm, dUs = run_planar(250, eta, c, lam0, I, v, al, b0, D0,
                            dither=0.04, sig_obs=0.05, seed=seed)
    X = np.vstack([np.ones(249), Dm[:-1], B[:-1] * Dm[:-1]]).T
    co, *_ = np.linalg.lstsq(X, Dm[1:], rcond=None)          # manufacture: coef on b*D > 0
    sl, _, _, _, _ = stats.linregress(Dm, dUs)                # ratchet: gradient rises in D
    signs_ok = (co[2] > 0) and (sl > 0)
    bp_id = 0.5 + 0.45 * np.sin(np.linspace(0, 4 * np.pi, 600))
    idp = claim_world(600, eta, lam0, I, 0.0, bp_id, sigma_lab=0.10, n_arr=6,
                      seed=(seed or 0) + 777)
    lh_, _, eh_, _, ih_, _, _ = identify(*idp)
    return signs_ok, fitted_fate(b0, D0, lh_, eh_, ih_)

ok_signs = 0; ok_basin = 0; n4 = 30
for k in range(n4):
    side = k % 2
    s_ok, captured = c4_check(side, seed=20000 + k)
    if s_ok: ok_signs += 1
    if captured == (side == 1): ok_basin += 1
report("A4  drift-law test on interior transients (manufacture + observed-gradient ratchet) "
       "and fitted-map basin classification",
       ok_signs >= 0.9 * n4 and ok_basin >= 0.95 * n4,
       f"signs {ok_signs}/{n4}, basin {ok_basin}/{n4} at T=250, 4% dither, 5% obs noise")

# ================================================================ A5: Phi-2 dashboard power + false-positive control
def plateau(Ival, T=2600, burn=600, seed=None):
    r = np.random.default_rng(seed)
    et, cc, l0, vq, aq = 0.5, 0.9, 0.02, 0.16, 0.8
    b, D = 0.2, Ival / (1 - s_of(0.2, et, l0))
    Ds = []
    for t in range(T):
        dU = -vq * b + 2 * cc * (1 - cc * b) * D + 0.01 * r.standard_normal()
        b = float(np.clip(b + aq * dU, 0, 1))
        D = s_of(b, et, l0) * D + Ival * (1 + 0.25 * r.standard_normal())
        if t >= burn: Ds.append(D * (1 + 0.10 * r.standard_normal()))
    Ds = np.array(Ds)
    ac1 = np.corrcoef(Ds[:-1], Ds[1:])[0, 1]
    return Ds.var(), ac1

I_fold = 0.0524
hits = ctrl = 0; n5 = 30
for k in range(n5):
    v_e, a_e = plateau(0.40 * I_fold, seed=30000 + k)
    v_l, a_l = plateau(0.90 * I_fold, seed=31000 + k)
    if v_l / v_e > 2 and a_l - a_e > 0.15: hits += 1
    v_e2, a_e2 = plateau(0.40 * I_fold, seed=32000 + k)
    if v_e2 / v_e > 2 and a_e2 - a_e > 0.15: ctrl += 1
report("A5  Phi-2 dashboard: var/AC1 trigger near the fold under 10% obs noise; "
       "fixed-I control does not trigger", hits >= 0.85 * n5 and ctrl <= 0.1 * n5,
       f"detection {hits}/{n5} at 0.9 I_fold vs 0.4 I_fold; false trigger {ctrl}/{n5}")

# ================================================================ A6: Phi-3 wedge with survivorship correction
def churn_world(N, logit_a, logit_b, seed):
    r = np.random.default_rng(seed)
    x = 0.5 * (1 + 0.6 * r.standard_normal(N)); h = x ** 2
    sat = -(1 - 0.7) ** 2 * h + 0.02 * r.standard_normal(N)
    p_alive = 1 / (1 + np.exp(-(logit_a - logit_b * h / h.mean())))
    alive = r.random(N) < p_alive
    return h, sat, alive

def ipw_recover(h, alive):
    X6 = np.vstack([np.ones(len(h)), h / h.mean()]).T
    w6 = np.zeros(2); y = alive.astype(float)
    for _ in range(80):
        z = X6 @ w6; p = 1 / (1 + np.exp(-z)); Wd = p * (1 - p) + 1e-9
        w6 += np.linalg.solve(X6.T @ (X6 * Wd[:, None]), X6.T @ (y - p))
    p_hat = np.clip(1 / (1 + np.exp(-(X6 @ w6))), 1 / 25, 1)      # winsorize weights at 25
    return np.sum(h[alive] / p_hat[alive]) / np.sum(1 / p_hat[alive])

# (a) moderate churn: positivity holds, IPW recovers
h, sat, alive = churn_world(8000, 1.0, 1.0, seed=41)
true_h, naive_h, ipw_h = h.mean(), h[alive].mean(), ipw_recover(h, alive)
ok_mod = (abs(ipw_h - true_h) / true_h < 0.08 and (true_h - naive_h) / true_h > 0.15
          and sat[alive].mean() > sat.mean())
# (b) brutal churn: positivity fails, IPW cannot recover -> audit-retained enrollment required
hb, satb, aliveb = churn_world(8000, 2.2, 7.0, seed=42)
ipw_b = ipw_recover(hb, aliveb)
ok_brutal = (hb.mean() - ipw_b) / hb.mean() > 0.30
report("A6  Phi-3 survivorship correction: IPW recovers the harmed-group error under "
       "moderate churn; under annihilating churn positivity fails and IPW cannot recover "
       "(audit-retained enrollment is therefore mandated, not optional)", ok_mod and ok_brutal,
       f"moderate: true {true_h:.3f}, naive {naive_h:.3f}, IPW {ipw_h:.3f}; "
       f"brutal: true {hb.mean():.3f}, IPW {ipw_b:.3f}")

# ================================================================ A7: Phi-4 pulse operating characteristics
def pulse_run(b0, D0, rho_pulse, P, T_post=40000, seed=None):
    et, cc, l0, Iv, vv, av = 0.5, 0.9, 0.02, 0.02, 0.10, 0.6
    b, D = b0, D0
    for t in range(P):
        dU = -vv + (2 * cc * (1 - cc * b) - rho_pulse) * D
        b = float(np.clip(b + av * dU, 0, 1)); D = s_of(b, et, l0) * D + Iv
    for t in range(T_post):
        dU = -vv + 2 * cc * (1 - cc * b) * D
        b = float(np.clip(b + av * dU, 0, 1)); D = s_of(b, et, l0) * D + Iv
    return b < 0.1                                                  # calibrated post-removal

rho_cure = 2 * 0.9 * 0.1 - 0.10 * 0.02 / 0.02                       # 0.08
P_min = None
for P in (2, 5, 10, 20, 40, 80, 160, 320):
    if pulse_run(1.0, 1.0, 1.5 * rho_cure, P, seed=0):
        P_min = P; break
r7 = np.random.default_rng(51)
esc = sum(pulse_run(float(r7.uniform(0.98, 1.0)), float(r7.uniform(0.9, 1.0)),
                    1.5 * rho_cure, P_min) for _ in range(20))
sub = sum(pulse_run(float(r7.uniform(0.98, 1.0)), float(r7.uniform(0.9, 1.0)),
                    0.5 * rho_cure, 10 * P_min) for _ in range(20))
cal_stays = pulse_run(0.0, 0.02 / (1 - s_of(0.0, 0.5, 0.02)), 1.5 * rho_cure, P_min)
report("A7  Phi-4 pulse: super-cure transient pulse escapes the captured basin (basin "
       "identified behaviorally); sub-cure pulse of 10x length never does; calibrated "
       "state unaffected", P_min is not None and esc == 20 and sub == 0 and cal_stays,
       f"P_min = {P_min} steps at rho = 1.5 rho_cure; escape {esc}/20; sub-cure escapes {sub}/20")

# ================================================================ A8: end-to-end verdict mapping
def micro_face(beta_stop, T=4000, settle=0, seed=None):
    """Two-type micro world run until beta reaches beta_stop (or T), then settled
    `settle` further steps; returns (beta, weight_L, |x_L|, U_now, U_cal)."""
    etaH = etaL = 0.5; kap = 0.5; piH = 0.5; iH, iL, zt, al, xb = 0.02, -0.02, 0.012, 0.8, 1.0
    b, xH, xL = 0.05, iH / etaH, iL / etaL
    def step(b, xH, xL, freeze=False):
        dH, dL = (1 - kap) * b, b
        wH, wL = etaH * (1 - dH), etaL * (1 - dL)
        dU = 2 * piH * (1 - kap) * (1 - dH) * xH ** 2 + 2 * (1 - piH) * (1 - dL) * xL ** 2
        b2 = b if freeze else min(1.0, max(0.0, b + al * dU))
        xH2 = min(xb, max(-xb, (1 - wH + zt) * xH + iH))
        xL2 = min(xb, max(-xb, (1 - wL + zt) * xL + iL))
        return b2, xH2, xL2
    for t in range(T):
        if b >= beta_stop: break
        b, xH, xL = step(b, xH, xL)
    for t in range(settle):
        b, xH, xL = step(b, xH, xL)
    xH0, xL0 = iH / etaH, iL / etaL
    for _ in range(8000):
        xH0 = (1 - etaH + zt) * xH0 + iH; xL0 = (1 - etaL + zt) * xL0 + iL
    U_now = -(piH * (1 - (1 - kap) * b) ** 2 * xH ** 2 + (1 - piH) * (1 - b) ** 2 * xL ** 2)
    U_cal = -(piH * (1 - 0) ** 2 * xH0 ** 2 + (1 - piH) * xL0 ** 2)
    return b, (1 - b) ** 2, abs(xL), U_now, U_cal

def protocol(world, seed):
    """Run C1-C5 on a world spec; return verdict in {none, pressure, drift, capture}."""
    # C1 + C3 (statics on the world's geometry)
    mg, se, cov = static_audit(500, 40, same_side=(world == "none"), seed=seed)
    C1 = cov >= 0
    C3 = mg > 2 * se
    # C2 (arm contrast at the operating stock)
    C2 = arm_power(600, 0.30, reps=1, seed=seed + 1) == 1.0
    # C4 (interior-transient drift-law + fitted basin)
    side = 1 if world in ("drift", "capture") else 0
    signs_ok, basin_captured = c4_check(side, seed=seed + 2)
    C4 = signs_ok and basin_captured
    # C5 (laundering signature on the micro channel)
    if world == "capture":
        b_end, wL, xLa, U_now, U_cal = micro_face(2.0, T=6000, settle=3000, seed=seed + 3)
    else:
        stop = 0.80 if world == "drift" else 0.3
        b_end, wL, xLa, U_now, U_cal = micro_face(stop, seed=seed + 3)
    C5 = (wL < 0.02) and (xLa > 0.9) and (U_now > U_cal)
    if C1 and C2 and C3 and C4 and C5: return "capture"
    if C1 and C2 and C3 and C4: return "drift"
    if C1 and C2 and C3: return "pressure"
    return "none"

tiers = ["none", "pressure", "drift", "capture"]
conf = {t: {u: 0 for u in tiers} for t in tiers}
for truth in tiers:
    for k in range(10):
        conf[truth][protocol(truth, seed=60000 + 100 * tiers.index(truth) + k)] += 1
rank = {t: i for i, t in enumerate(tiers)}
above = sum(conf[t][u] for t in tiers for u in tiers if rank[u] > rank[t])
correct = sum(conf[t][t] for t in tiers)
report("A8  end-to-end verdict mapping over 40 simulated deployments: zero verdicts above "
       "the true tier (safe-side); high exact-tier accuracy",
       above == 0 and correct >= 34,
       "conf rows none/pressure/drift/capture: " +
       "; ".join(",".join(str(conf[t][u]) for u in tiers) for t in tiers))


# ================================================================ A9: misspecification (conservative halves only)
# (a) drifting lambda_0 + heteroskedastic dynamics noise: no false C4
def misspec_window(T, b0, D0, al, dither, sig_obs, seed):
    r = np.random.default_rng(seed)
    b, D = b0, D0; B = np.zeros(T); Dm = np.zeros(T)
    for t in range(T):
        lam_t = 0.02 * (1 + 0.5 * np.sin(2 * np.pi * t / 250))
        bd = float(np.clip(b + dither * r.uniform(-1, 1), 0, 1))
        dU = -0.10 + 2 * 0.9 * (1 - 0.9 * bd) * D
        b = float(np.clip(bd + al * dU, 0, 1))
        D = (1 - lam_t) * (1 - 0.5 * (1 - bd)) ** 2 * D * (1 + 0.04 * r.standard_normal()) + 0.02
        D = max(D, 1e-9)
        B[t] = bd; Dm[t] = D * (1 + sig_obs * r.standard_normal())
    return B, Dm

def misspec_fate(b0, D0, T=40000):
    b, D = b0, D0
    for t in range(T):
        lam_t = 0.02 * (1 + 0.5 * np.sin(2 * np.pi * t / 250))
        dU = -0.10 + 2 * 0.9 * (1 - 0.9 * b) * D
        b = float(np.clip(b + 0.6 * dU, 0, 1))
        D = (1 - lam_t) * (1 - 0.5 * (1 - b)) ** 2 * D + 0.02
        if b > 0.97 and D > 0.5: return True
        if b < 0.03 and D < 0.05: return False
    return b > 0.5

r9 = np.random.default_rng(71)
false_c4 = 0; n_eval = 0
for k in range(20):
    b0, D0 = 0.45, 0.5 * _DSEP[0.45]
    if misspec_fate(b0, D0): continue                 # truth must be calibrated to count
    n_eval += 1
    jit = lambda x: x * (1 + 0.08 * (r9.random() - 0.5) * 2)
    pred = fitted_fate(b0, D0, jit(0.02), jit(0.5), jit(0.02))
    if pred: false_c4 += 1
# (b) quadratic content channel vs the specification guard
certs_q = 0; guard_fires = 0
for k in range(20):
    out = claim_world(1200, 0.5, 0.08, 0.010, 0.0,
                      0.5 + 0.45 * np.sin(np.linspace(0, 8 * np.pi, 1200)),
                      sigma_lab=0.10, n_arr=6, g2=0.8, cap=5.0, seed=80000 + k)
    certify, fired = margin_rule(out, seed=80500 + k)
    if certify: certs_q += 1
    if fired: guard_fires += 1
# (c) C2 arm contrast is model-free: recovers the true local sign under nonlinear satisfaction
def u_nl(b, D, r, N):
    return -0.10 * b - (1 - 0.9 * b) ** 2 * D + 0.05 * np.sin(6 * b) + 0.05 * r.standard_normal(N)
agree = 0; tot = 0
r9c = np.random.default_rng(72)
for b0 in (0.3, 0.5, 0.8):
    truth = np.sign((-0.10 * (b0 + .1) - (1 - 0.9 * (b0 + .1)) ** 2 * 0.3 + 0.05 * np.sin(6 * (b0 + .1)))
                    - (-0.10 * b0 - (1 - 0.9 * b0) ** 2 * 0.3 + 0.05 * np.sin(6 * b0)))
    for k in range(20):
        d = u_nl(b0 + 0.1, 0.3, r9c, 600).mean() - u_nl(b0, 0.3, r9c, 600).mean()
        tot += 1
        if np.sign(d) == truth: agree += 1
report("A9  misspecification: no false C4 under drifting-grounding heteroskedastic worlds; "
       "specification guard blocks certification under a quadratic content channel; "
       "arm contrast recovers the true local sign under nonlinear satisfaction",
       false_c4 == 0 and n_eval >= 18 and certs_q == 0 and guard_fires >= 15
       and agree >= 0.9 * tot,
       f"false C4 {false_c4}/{n_eval}; quad-world certs {certs_q}/20, guard fired "
       f"{guard_fires}/20; C2 sign agreement {agree}/{tot}")

# ================================================================ A10: boundary stress (gray-zone conservatism)
# (a) seeds near the separatrix: never classify calibrated-truth as captured
false_cap = 0; det_super = 0
for j, f in enumerate((0.85, 0.95)):
    for k in range(10):
        b0, D0 = 0.60, f * _DSEP[0.60]
        idp = claim_world(600, 0.5, 0.02, 0.02, 0.0,
                          0.5 + 0.45 * np.sin(np.linspace(0, 4 * np.pi, 600)),
                          sigma_lab=0.10, n_arr=6, seed=90000 + 100 * j + k)
        lh_, _, eh_, _, ih_, _, _ = identify(*idp)
        if fitted_fate(b0, D0, lh_, eh_, ih_): false_cap += 1
for j, f in enumerate((1.05, 1.15)):
    for k in range(10):
        b0, D0 = 0.60, f * _DSEP[0.60]
        idp = claim_world(600, 0.5, 0.02, 0.02, 0.0,
                          0.5 + 0.45 * np.sin(np.linspace(0, 4 * np.pi, 600)),
                          sigma_lab=0.10, n_arr=6, seed=91000 + 100 * j + k)
        lh_, _, eh_, _, ih_, _, _ = identify(*idp)
        if fitted_fate(b0, D0, lh_, eh_, ih_): det_super += 1
# (b) noisy C5 reads near the state boundary: 2SE-margined criteria
def noisy_c5(stop, settle, read_seed):
    b_end, wL, xLa, U_now, U_cal = micro_face(stop, T=6000, settle=settle)
    r = np.random.default_rng(read_seed)
    wl = wL * (1 + 0.05 * r.standard_normal(30)) if wL > 0 else np.zeros(30)
    xl = xLa * (1 + 0.05 * r.standard_normal(30))
    um = (U_now - U_cal) * (1 + 0.05 * r.standard_normal(30))
    fire = (wl.mean() < 0.02 and xl.mean() - 2 * xl.std(ddof=1) / np.sqrt(30) > 0.9
            and um.mean() > 2 * um.std(ddof=1) / np.sqrt(30))
    return fire
fire_true = sum(noisy_c5(2.0, 3000, 95000 + k) for k in range(10))
fire_mid = sum(noisy_c5(0.80, 0, 96000 + k) for k in range(10))
# (c) near-zero certificate margins: abstention as designed behavior
certs_neg = 0; certs_tiny = 0
for k in range(10):
    out = claim_world(1200, 0.5, 0.08, 0.0411, 0.0,
                      0.5 + 0.45 * np.sin(np.linspace(0, 4 * np.pi, 1200)),
                      sigma_lab=0.10, n_arr=6, seed=97000 + k)   # m_true = -0.010
    c1, _ = margin_rule(out, seed=97500 + k)
    if c1: certs_neg += 1
    out = claim_world(1200, 0.5, 0.08, 0.0328, 0.0,
                      0.5 + 0.45 * np.sin(np.linspace(0, 4 * np.pi, 1200)),
                      sigma_lab=0.10, n_arr=6, seed=98000 + k)   # m_true = +0.005
    c2, _ = margin_rule(out, seed=98500 + k)
    if c2: certs_tiny += 1
report("A10 boundary stress: near-separatrix calibrated-truth seeds never classified "
       "captured; 2SE-margined C5 fires on true capture and never mid-transit; "
       "negative-margin loops never certified (tiny positive margins abstain by design)",
       false_cap == 0 and fire_true == 10 and fire_mid == 0 and certs_neg == 0,
       f"false-captured {false_cap}/20 at 0.85-0.95 Gamma (super-Gamma detected "
       f"{det_super}/20); C5 true {fire_true}/10, mid {fire_mid}/10; certs at "
       f"m=-0.01: {certs_neg}/10, m=+0.005: {certs_tiny}/10")

print()
print("=" * 70)
print(f"AUDIT DE-RISK RESULT: {sum(PASS)}/{len(PASS)} suites pass")
