"""Figures for the Civic Drift skeleton (parameters identical to derisk_numerics.py)."""
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

rng = np.random.default_rng(3)
plt.rcParams.update({
    "font.family": "serif",
    "font.serif": ["cmr10"],
    "mathtext.fontset": "cm",
    "axes.formatter.use_mathtext": True,
    "font.size": 9,
    "axes.spines.top": False,
    "axes.spines.right": False,
    "pdf.fonttype": 42,
})
PDF_METADATA = {"CreationDate": None, "ModDate": None}

# ---------- shared reduced model (linear-cost corner variant) ----------
P = dict(eta=0.5, c=0.9, lam0=0.02, I=0.02, v=0.10, alpha=0.1)
def srate(b, P):  return (1 - P['lam0']) * (1 - P['eta'] * (1 - b)) ** 2
def Dstar(b, P):  return P['I'] / (1 - srate(b, P))
def step(b, D, P, rho=0.0, noise=0.0):
    Up = -P['v'] + (2 * P['c'] * (1 - P['c'] * b) - rho) * D
    return (min(1.0, max(0.0, b + P['alpha'] * Up)),
            max(0.0, srate(b, P) * D + P['I'] + noise))

# ============ Figure 1: phase portrait, nullclines, basins ============
fig, ax = plt.subplots(figsize=(4.6, 3.4))
Dmax = 1.15
# basin classification on a grid (vectorized; iteration count scaled with 1/alpha)
nb, nd = 160, 140
bb = np.linspace(0, 1, nb); dd = np.linspace(0, Dmax, nd)
Bg, Dg = np.meshgrid(bb, dd)
b_arr, D_arr = Bg.copy(), Dg.copy()
for _ in range(5400):
    Up = -P['v'] + 2 * P['c'] * (1 - P['c'] * b_arr) * D_arr
    D_new = np.maximum(0.0, srate(b_arr, P) * D_arr + P['I'])
    b_arr = np.clip(b_arr + P['alpha'] * Up, 0.0, 1.0)
    D_arr = D_new
basin = (b_arr > 0.5).astype(float)
ax.contourf(bb, dd, basin, levels=[-0.5, 0.5, 1.5],
            colors=["#dce8f5", "#f5ddd6"], alpha=0.9)
# nullclines
bg = np.linspace(0, 0.995, 400)
ax.plot(bg, P['v'] / (2 * P['c'] * (1 - P['c'] * bg)), 'k--', lw=1.2,
        label=r"$\beta$-nullcline  $D=v/[2c(1-c\beta)]$")
ax.plot(bg, [Dstar(b, P) for b in bg], 'k-', lw=1.2,
        label=r"$D$-nullcline  $D=I/(1-s(\beta))$")
# sample trajectories
for (b0, D0) in [(0.15, 0.55), (0.55, 0.25), (0.35, 0.95), (0.8, 0.6), (0.6, 1.05), (0.05, 0.05)]:
    b, D = b0, D0
    tb, td = [b], [D]
    for _ in range(1560):
        b, D = step(b, D, P)
        tb.append(b); td.append(D)
    ax.plot(tb, td, lw=0.8, color="#444444", alpha=0.8)
    ax.plot(b0, D0, '.', ms=4, color="#444444")
ax.plot(0, Dstar(0, P), 'o', ms=7, mfc="#1f5fa8", mec='k', zorder=5,
        clip_on=False, label="calibrated attractor")
ax.plot(1, Dstar(1, P), 's', ms=7, mfc="#c0392b", mec='k', zorder=5,
        clip_on=False, label="captured attractor")
ax.set_xlabel(r"deference $\beta$"); ax.set_ylabel(r"disagreement stock $D$")
ax.set_xlim(0, 1); ax.set_ylim(0, Dmax)
ax.legend(loc="upper left", fontsize=7, frameon=False)
fig.tight_layout(); fig.savefig("fig_phase.pdf", metadata=PDF_METADATA); plt.close(fig)

# ============ Figure 2: hysteresis loop ============
rho_cure = 2 * P['c'] * (1 - P['c']) - P['v'] * P['lam0'] / P['I']
fig, ax = plt.subplots(figsize=(4.6, 3.0))
# up-sweep from captured
b, D = 1.0, Dstar(1, P)
rs_up = np.linspace(0, 0.15, 400); bu = []
for rho in rs_up:
    for _ in range(2400): b, D = step(b, D, P, rho=rho)
    bu.append(b)
# down-sweep from wherever the up-sweep ended
rs_dn = rs_up[::-1]; bd = []
for rho in rs_dn:
    for _ in range(2400): b, D = step(b, D, P, rho=rho)
    bd.append(b)
ax.plot(rs_up, bu, color="#c0392b", lw=1.8, label="up-sweep (start captured)")
ax.plot(rs_dn, bd, color="#1f5fa8", lw=1.8, ls="--", label="down-sweep (after cure)")
ax.axvline(rho_cure, color='k', lw=0.9, ls=':')
ax.annotate(r"$\rho_{\mathrm{cure}}=2c(1-c)-v\lambda_0/I$", (rho_cure, 0.55),
            xytext=(rho_cure + 0.008, 0.62), fontsize=8)
ax.annotate("prevention threshold = 0\n(deterministic)", (0.002, 0.06), fontsize=8, color="#1f5fa8")
ax.set_xlabel(r"civic weight $\rho$"); ax.set_ylabel(r"deference $\beta$")
ax.set_ylim(-0.05, 1.05)
ax.legend(loc="center right", fontsize=7, frameon=False)
fig.tight_layout(); fig.savefig("fig_hysteresis.pdf", metadata=PDF_METADATA); plt.close(fig)

# ============ Figure 3: early-warning indicators near the fold ============
P3 = dict(eta=0.5, c=0.9, lam0=0.02, v=0.16, alpha=0.8)
def Dst(b, I, P): return I / (1 - (1 - P['lam0']) * (1 - P['eta'] * (1 - b)) ** 2)
def phi(b, I, P):
    D = Dst(b, I, P); return 2 * P['c'] * D / (P['v'] + 2 * P['c'] ** 2 * D)
def n_fp(I, P):
    bg = np.linspace(1e-4, 1 - 1e-4, 30001)
    f = np.array([phi(x, I, P) for x in bg]) - bg
    return int(np.sum(np.diff(np.sign(f)) != 0))
def step_q(b, D, I, P, noise=0.0):
    Up = -P['v'] * b + 2 * P['c'] * (1 - P['c'] * b) * D
    return (min(1.0, max(0.0, b + P['alpha'] * Up)),
            max(0.0, (1 - P['lam0']) * (1 - P['eta'] * (1 - b)) ** 2 * D + I + noise))
I0, Ilo, Ihi = 0.02, 0.02, 0.2
for _ in range(48):
    Im = 0.5 * (Ilo + Ihi)
    if n_fp(Im, P3) >= 2: Ilo = Im
    else: Ihi = Im
I_fold = 0.5 * (Ilo + Ihi)
bg = np.linspace(1e-4, 1 - 1e-4, 30001)
f = np.array([phi(x, I0, P3) for x in bg]) - bg
blo = bg[np.where(np.diff(np.sign(f)) != 0)[0][0]]
b, D = blo, Dst(blo, I0, P3)
plateaus = np.linspace(I0, 0.96 * I_fold, 12)
V, A = [], []
for I in plateaus:
    for _ in range(4000): b, D = step_q(b, D, I, P3, noise=1.5e-3 * rng.standard_normal())
    buf = np.empty(12000)
    for t in range(12000):
        b, D = step_q(b, D, I, P3, noise=1.5e-3 * rng.standard_normal())
        buf[t] = D
    x = buf - buf.mean()
    V.append(x.var()); A.append(np.corrcoef(x[:-1], x[1:])[0, 1])
fig, ax = plt.subplots(figsize=(4.6, 3.0))
xx = plateaus / I_fold
ax.plot(xx, np.array(V) / V[0], 'o-', color="#1f5fa8", lw=1.4, ms=4,
        label=r"Var$(D)$ / Var$_0$")
ax2 = ax.twinx(); ax2.spines["right"].set_visible(True)
ax2.plot(xx, A, 's--', color="#c0392b", lw=1.4, ms=4, label=r"lag-1 autocorr$(D)$")
ax.axvline(1.0, color='k', lw=0.9, ls=':'); ax.annotate("fold\n(capture)", (1.0, 0.8),
            xytext=(0.965, 1.6), fontsize=8, ha="right")
ax.set_xlabel(r"injection rate $I\,/\,I_{\mathrm{fold}}$")
ax.set_ylabel("relative variance"); ax2.set_ylabel("autocorrelation")
ax.set_xlim(min(xx) - 0.02, 1.02)
h1, l1 = ax.get_legend_handles_labels(); h2, l2 = ax2.get_legend_handles_labels()
ax.legend(h1 + h2, l1 + l2, loc="upper left", fontsize=7, frameon=False)
fig.tight_layout(); fig.savefig("fig_warning.pdf", metadata=PDF_METADATA); plt.close(fig)

# ============ Figure 4: Arrhenius crossing scaling + civic-weight protection ============
P_e = dict(P); P_e['I'] = 0.040
def saddle_policy(rho):
    lo, hi = 0.0, 1.0
    for _ in range(100):
        mid = 0.5 * (lo + hi)
        grad = -P_e['v'] + (2 * P_e['c'] * (1 - P_e['c'] * mid) - rho) * Dstar(mid, P_e)
        if grad < 0:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)

def crossing_times(sigma, rho, n=48, cap=1500000, seed=0):
    g = np.random.default_rng(2000 + seed)
    b = np.zeros(n); D = np.full(n, Dstar(0, P_e)); te = np.full(n, cap, float)
    alive = np.ones(n, bool)
    bd = saddle_policy(rho)
    for t in range(cap):
        if not alive.any(): break
        Up = -P_e['v'] + (2 * P_e['c'] * (1 - P_e['c'] * b) - rho) * D + sigma * g.standard_normal(n)
        b_new = np.clip(b + P_e['alpha'] * Up, 0, 1)
        D = np.maximum(0.0, srate(b, P_e) * D + P_e['I'])
        b = b_new
        newly = alive & (b >= bd); te[newly] = t; alive &= ~newly
    return te, int((~alive).sum())
sig_list = [0.160, 0.200, 0.280, 0.420]   # rescaled with alpha (noise enters as alpha*sigma), spanning the crossing-time range
X, Y = [], []
for k, s in enumerate(sig_list):
    te, ne = crossing_times(s, 0.0, seed=k)
    X.append(1 / s ** 2); Y.append(np.log10(te.sum() / (ne + 0.5)))
rhos = [0.0, 0.02, 0.04]; HZ = []
for k, r in enumerate(rhos):
    te, ne = crossing_times(0.150, r, seed=60 + k)
    HZ.append((ne + 0.5) / te.sum())
fig, (axA, axB) = plt.subplots(1, 2, figsize=(6.4, 2.7), gridspec_kw={"width_ratios": [3, 2]})
cf = np.polyfit(X, Y, 1)
axA.plot(X, np.polyval(cf, X), '-', color="#999999", lw=1)
axA.plot(X, Y, 'o', color="#1f5fa8", ms=5)
axA.set_xlabel(r"$1/\sigma^2$"); axA.set_ylabel(r"$\log_{10}$ mean crossing time")
axA.set_title("Arrhenius scaling", fontsize=9)
axB.bar([str(r) for r in rhos], HZ, color=["#c0392b", "#b07aa1", "#1f5fa8"], width=0.6)
axB.set_yscale("log"); axB.set_xlabel(r"civic weight $\rho$")
axB.set_ylabel("crossing hazard (per step)")
axB.set_title(r"protection at $\rho \ll \rho_{\mathrm{cure}}$", fontsize=9)
fig.tight_layout(); fig.savefig("fig_arrhenius.pdf", metadata=PDF_METADATA); plt.close(fig)

print("figures written:", "fig_phase.pdf fig_hysteresis.pdf fig_warning.pdf fig_arrhenius.pdf")
print(f"rho_cure={rho_cure:.4f}, I_fold={I_fold:.4f}, warning: var x{V[-1]/V[0]:.1f}, AC1 {A[0]:.2f}->{A[-1]:.2f}")
