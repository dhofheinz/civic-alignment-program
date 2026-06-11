"""Figures for the Civic Loops skeleton (parameters match derisk_loops.py)."""
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

plt.rcParams.update({"font.size": 9, "axes.spines.top": False, "axes.spines.right": False})

def srate(b, eta, lam0): return (1 - lam0) * (1 - eta * (1 - b)) ** 2

# ================= Figure 1: certificate zones in the (g, v) plane =================
eta, c, lam0, I = 0.5, 0.9, 0.15, 0.03
gs = np.linspace(0, 0.95 * lam0, 240)
v_safe = 2 * c * I / (lam0 - gs)
v_cap = 2 * c * (1 - c) * I / (lam0 - gs)
fig, ax = plt.subplots(figsize=(5.2, 3.4))
vmax = 1.15 * v_safe.max()
ax.fill_between(gs, v_safe, vmax, color="#dce8f5", alpha=0.95)
ax.fill_between(gs, 0, v_cap, color="#f5ddd6", alpha=0.95)
ax.fill_between(gs, v_cap, v_safe, color="#f2ecd8", alpha=0.95)
# sub-region of zone B with a partial-capture attractor: capture line < v < max_beta F
bg = np.linspace(1e-4, 1, 1200)
gline = np.linspace(0, 0.945 * lam0, 160)
v_int = []
for g in gline:
    den = 1 - (1 - lam0) * (1 - eta * (1 - bg)) ** 2 - g
    F = 2 * c * (1 - c * bg) * I / den
    v_int.append(F.max())
v_int = np.array(v_int)
v_cap_l = 2 * c * (1 - c) * I / (lam0 - gline)
ax.fill_between(gline, v_cap_l, v_int, color="#b07aa1", alpha=0.45,
                label="partial-capture attractor exists")
ax.plot(gline, v_int, color="#b07aa1", lw=1.2, ls="-.")
ax.plot(gs, v_safe, 'k-', lw=1.6, label=r"certificate  $v(\lambda_0-g)=2cI$")
ax.plot(gs, v_cap, 'k--', lw=1.4, label=r"capture line  $v(\lambda_0-g)=2c(1-c)I$")
ax.axvline(lam0, color="#c0392b", lw=1.6)
ax.annotate("divergence wall\n$g=\\lambda_0$", (lam0, 0.55 * vmax), xytext=(lam0 * 0.78, 0.62 * vmax),
            fontsize=8, color="#c0392b", ha="right")
ax.annotate("certified safe:\nany policy, any rate", (0.012, 0.86 * vmax), fontsize=8, color="#1f5fa8")
ax.annotate("captured corner stable", (0.012, 0.035), fontsize=8, color="#c0392b")
ax.set_xlabel(r"content gain $g$"); ax.set_ylabel(r"usefulness premium $v$")
ax.set_xlim(0, lam0 * 1.06); ax.set_ylim(0, vmax)
ax.legend(loc="center left", fontsize=7, frameon=False)
fig.tight_layout(); fig.savefig("fig_zones.png", dpi=220); plt.close(fig)

# ============ Figure 2: aggregation-conservation cells ============
fig, ax = plt.subplots(figsize=(5.4, 3.4))
beta = np.linspace(0, 0.995, 800); u = 1 - beta
eta = 0.5; iota = 0.2; I = J = 0.2; lam0 = 0.12
def rel(x): return x / x[0]
# A: single-claim, zeta = 0 (flat)
gA0 = (iota * u / (eta * u)) ** 2
# A': single-claim, zeta > 0 (pole at beta = 1 - zeta/eta)
zeta = 0.04
mA = u > zeta / eta + 0.015
gAz = np.full_like(u, np.nan); gAz[mA] = (iota * u[mA] / (eta * u[mA] - zeta)) ** 2
# D: L1 portfolio at g = lam0 (flat)
gD = u * J / ((1 - lam0) * eta * u)
# C: L2 portfolio, g < lam0 (monotone fall) and lam0 < g (interior min, then wall)
def gapC(g):
    den = 1 - (1 - lam0) * (1 - eta * u) ** 2 - g
    out = np.full_like(u, np.nan); m = den > 5e-3
    out[m] = u[m] ** 2 * I / den[m]
    return out
gC_lo = gapC(0.05)
g_hi = 0.22
gC_hi = gapC(g_hi)
u_c = (g_hi - lam0) / (eta * (1 - lam0)); b_c = 1 - u_c
ax.plot(beta, rel(gA0), color="#444444", lw=2.2, label=r"single claim, $\zeta=0$: conserved")
ax.plot(beta, rel(gD), color="#999999", lw=2.2, ls=":", label=r"$L^1$ portfolio, $g=\lambda_0$: conserved")
ax.plot(beta, gAz / gAz[0], color="#c0392b", lw=1.7, label=r"single claim, $\zeta>0$: rises (myopia)")
ax.plot(beta, rel(gC_lo), color="#1f5fa8", lw=1.7, label=r"$L^2$ portfolio, $g<\lambda_0$: falls (capture rewarded)")
gh = gC_hi / gC_hi[0]
ax.plot(beta, gh, color="#b07aa1", lw=1.7, label=r"$L^2$ portfolio, $g>\lambda_0$: interior min, then wall")
ic = np.nanargmin(np.where(beta > 0.2, gh, np.nan))
ax.plot([beta[ic]], [gh[ic]], 'o', ms=5, mfc="#b07aa1", mec='k')
ax.annotate(r"$\beta_c$", (beta[ic], gh[ic]), xytext=(beta[ic] + 0.02, gh[ic] + 0.25), fontsize=9)
ax.axhline(1.0, color="#dddddd", lw=0.6, zorder=0)
ax.set_xlabel(r"deference $\beta$")
ax.set_ylabel(r"stationary gap / gap at $\beta=0$")
ax.set_ylim(0, 3.0); ax.set_xlim(0, 1)
ax.legend(loc="upper left", fontsize=6.8, frameon=False)
fig.tight_layout(); fig.savefig("fig_conservation.png", dpi=220); plt.close(fig)

print("figures written: fig_zones.png fig_conservation.png")

# ============ Figure 3: separatrix limit (rate separation) ============
# Recomputes the N6 quantities so the figure is self-contained.
from scipy.integrate import quad as _quad
from scipy.optimize import brentq as _brentq
P2f = dict(eta=0.5, c=0.9, lam0=0.02, g=0.0, I=0.02, v=0.10)
def _s(b): return (1 - P2f['lam0']) * (1 - P2f['eta'] * (1 - b)) ** 2
def _G(b): return -P2f['v'] + 2 * P2f['c'] * (1 - P2f['c'] * b) * P2f['I'] / (1 - _s(b) - P2f['g'])
_bsad = _brentq(_G, 0.5, 0.999)
_K = _quad(lambda b: (1 - _s(b) - P2f['g']) / (2 * P2f['c'] * (1 - P2f['c'] * b)), 0.4, _bsad)[0]
def _kappa(b0):
    def crosses(E0):
        b, E = b0, E0
        for _ in range(6000):
            b2 = b + 2 * P2f['c'] * (1 - P2f['c'] * b) * E
            E *= _s(b) + P2f['g']
            b = b2
            if b >= _bsad: return True
            if E < 1e-14: return False
        return False
    lo, hi = 0.0, 3.0
    for _ in range(60):
        mid = 0.5 * (lo + hi)
        if crosses(mid): hi = mid
        else: lo = mid
    return 0.5 * (lo + hi)
_ks = _kappa(0.4)
def _fate(b0, D0, a, Tmax):
    b, D = b0, D0
    for _ in range(Tmax):
        Up = -P2f['v'] + 2 * P2f['c'] * (1 - P2f['c'] * b) * D
        b2 = min(1.0, max(0.0, b + a * Up))
        D = max(0.0, (_s(b) + P2f['g']) * D + P2f['I'])
        b = b2
        if b > 0.999: return True
        if b < 0.02: return False
    return b > 0.5
_Dbar0 = P2f['I'] / (1 - _s(0.4) - P2f['g'])
_alphas = [0.6, 0.3, 0.15, 0.075, 0.0375, 0.01875]
_prods = []
for a in _alphas:
    Tmax = int(min(25000 + 900 / a, 150000))
    lo, hi = 0.0, 200.0
    for _ in range(42):
        mid = 0.5 * (lo + hi)
        if _fate(0.4, mid, a, Tmax): hi = mid
        else: lo = mid
    _prods.append(a * (0.5 * (lo + hi) - _Dbar0))
fig, ax = plt.subplots(figsize=(5.0, 3.2))
ax.semilogx(_alphas, _prods, 'o-', color="#1f5fa8", lw=1.5, ms=5,
            label=r"measured $\alpha\,(D_{\mathrm{sep}}-D^\ast(\beta_0))$")
ax.axhline(_ks, color="#222222", lw=1.6,
           label=rf"jump-map limit $\kappa^\ast={_ks:.3f}$")
ax.axhline(_K, color="#888888", lw=1.3, ls="--",
           label=rf"continuum integral $K={_K:.3f}$")
extrap = 2 * _prods[-1] - _prods[-2]
ax.plot([_alphas[-1] * 0.55], [extrap], 's', mfc='none', mec="#1f5fa8", ms=7,
        label=rf"Richardson extrapolation ${extrap:.3f}$")
ax.set_xlabel(r"adaptation rate $\alpha$")
ax.set_ylabel(r"$\alpha\,(D_{\mathrm{sep}} - D^\ast(\beta_0))$")
ax.set_ylim(0.2, 0.58)
ax.legend(fontsize=7, frameon=False, loc="upper left")
fig.tight_layout(); fig.savefig("fig_ratesep.png", dpi=220); plt.close(fig)
print("figure written: fig_ratesep.png")
