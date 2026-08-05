/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.Network

/-!
# Paper III: slack bounds and a strict network certificate

`thm:network`(ii) (`civic_loops.tex:336,276`) says the coordinatewise argument is
"identical" to the scalar one.  The scalar proof first enters the exact box
`D ≤ R`; clause (i) supplies only componentwise `limsup D_k ≤ R_k`, which is the
same *converges-to-the-box versus enters-the-box* defect as `lem:box`.

Two lemmas isolate the issue:

* `networkGradient_le_certificate_add_error` — the certificate inequality with an
  additive stock slack, so the exact box is never needed;
* `exists_common_entry_time` — finiteness of the community index makes the
  per-coordinate entry times synchronize by taking their maximum.

Together they give `networkGradient_eventually_le`. At the paper's sharp
certificate this does not force exact entry or prevent an unrestricted rule
from jumping upward when the remaining gradient error is positive. A strict
certificate absorbs that error and yields the unconditional convergence result
`networkDeference_tendsto_zero_of_strictMargin` below.
-/

namespace CivicAlignment.PaperIII

open Filter Matrix Set Topology
open scoped BigOperators Norms.Operator

variable {K : Type*} [Fintype K] [DecidableEq K]

section SlackBound

omit [Fintype K] [DecidableEq K] in
/--
**The certificate inequality with stock slack.** The scalar development carries
`gradU_le_neg_certificate_add_error` for exactly this purpose; this is its
network form, and it is what removes the need for the exact box.
-/
theorem networkGradient_le_certificate_add_error
    {lambda₀ η I v c : K → ℝ} {G : Matrix K K ℝ}
    (model : NetworkModelAssumptions lambda₀ η I v c G)
    {R β D : K → ℝ} {ε : ℝ}
    (hcertificate : ∀ k, 2 * c k * R k ≤ v k)
    (hβ : ∀ k, β k ∈ Icc (0 : ℝ) 1) (hε : 0 ≤ ε)
    (hD : ∀ k, D k ≤ R k + ε) :
    ∀ k, networkGradient v c β D k
      ≤ -2 * c k ^ 2 * β k * R k + 2 * c k * ε := by
  intro k
  have hc := model.c_pos k
  have hcle := model.c_lt_one k
  have hβ0 := (hβ k).1
  have hβ1 := (hβ k).2
  have hresidual : 0 ≤ 1 - c k * β k := by nlinarith [hc, hcle, hβ0, hβ1]
  have hfactor : 0 ≤ 2 * c k * (1 - c k * β k) := by positivity
  have hstep : 2 * c k * (1 - c k * β k) * D k
      ≤ 2 * c k * (1 - c k * β k) * (R k + ε) :=
    mul_le_mul_of_nonneg_left (hD k) hfactor
  have hcert := hcertificate k
  have key : 2 * c k * (1 - c k * β k) * (R k + ε)
      ≤ 2 * c k * R k - 2 * c k ^ 2 * β k * R k + 2 * c k * ε := by
    have hcbe : 0 ≤ 2 * c k * ε * (c k * β k) := by positivity
    nlinarith [hcbe]
  simp only [networkGradient]
  linarith [hstep, key, hcert]

end SlackBound

section Synchronization

omit [Fintype K] [DecidableEq K] in
/--
**The synchronization lemma.** Componentwise `limsup ≤ R` does not by itself give
a time after which the coupled vector lies in the exact box.  It does give one
for every positive slack, because the community index is finite: take the maximum
of the per-coordinate entry times.
-/
theorem exists_common_entry_time [Finite K]
    {D : ℕ → K → ℝ} {R : K → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hlimsup : ∀ k, limsup (fun t ↦ D t k) atTop ≤ R k)
    (hbdd : ∀ k, IsBoundedUnder (· ≤ ·) atTop (fun t ↦ D t k)) :
    ∃ T : ℕ, ∀ t, T ≤ t → ∀ k, D t k ≤ R k + ε := by
  classical
  letI := Fintype.ofFinite K
  have hpointwise : ∀ k : K, ∃ Tk : ℕ, ∀ t, Tk ≤ t → D t k ≤ R k + ε := by
    intro k
    have hlt : limsup (fun t ↦ D t k) atTop < R k + ε := by
      have := hlimsup k
      linarith
    have hev : ∀ᶠ t in atTop, D t k < R k + ε :=
      eventually_lt_of_limsup_lt hlt (hbdd k)
    obtain ⟨Tk, hTk⟩ := eventually_atTop.mp hev
    exact ⟨Tk, fun t ht ↦ (hTk t ht).le⟩
  choose T hT using hpointwise
  refine ⟨Finset.univ.sup T, fun t ht k ↦ hT k t ?_⟩
  exact le_trans (Finset.le_sup (Finset.mem_univ k)) ht

end Synchronization

section Closure

/-- The stock coordinates are bounded above whenever the worst-case matrix
powers are summable. This is the spectral-radius-ready form of the boundedness
lemma used by Paper III, Theorem 5.2(ii'). -/
theorem networkStock_isBoundedUnder_of_summable [Nonempty K]
    {lambda₀ η I v c : K → ℝ} {G : Matrix K K ℝ}
    (model : NetworkModelAssumptions lambda₀ η I v c G)
    (hsum : Summable (fun n : ℕ ↦ networkWorstMatrix lambda₀ G ^ n))
    {β D : ℕ → K → ℝ} (hβ : ∀ t k, β t k ∈ Icc (0 : ℝ) 1)
    (htraj : IsNetworkLoopTrajectory lambda₀ η G I β D) (hD0 : 0 ≤ D 0) :
    ∀ k, IsBoundedUnder (· ≤ ·) atTop (fun t ↦ D t k) := by
  intro k
  have hle := networkStockTrajectory_le_upper
    (fun t ↦ networkTransition_nonnegative model (hβ t))
    (fun t ↦ networkTransition_le_worst model (hβ t))
    (networkWorstMatrix_nonnegative model) (fun j ↦ (model.I_pos j).le) htraj hD0
  have htend := networkUpperPath_tendsto_of_summable
    (networkWorstMatrix lambda₀ G) I (D 0) hsum
  obtain ⟨b, hb⟩ := (tendsto_pi_nhds.mp htend k).isBoundedUnder_le
  rw [eventually_map] at hb
  refine ⟨b, ?_⟩
  rw [eventually_map]
  filter_upwards [hb] with t ht
  exact le_trans (hle t k) ht

/-- The stock coordinates are bounded above: each is dominated by the
time-homogeneous upper path, which converges under the operator-norm bound.
This discharges the boundedness side condition of `exists_common_entry_time`. -/
theorem networkStock_isBoundedUnder [Nonempty K]
    {lambda₀ η I v c : K → ℝ} {G : Matrix K K ℝ}
    (model : NetworkModelAssumptions lambda₀ η I v c G)
    (hnorm : ‖networkWorstMatrix lambda₀ G‖ < 1)
    {β D : ℕ → K → ℝ} (hβ : ∀ t k, β t k ∈ Icc (0 : ℝ) 1)
    (htraj : IsNetworkLoopTrajectory lambda₀ η G I β D) (hD0 : 0 ≤ D 0) :
    ∀ k, IsBoundedUnder (· ≤ ·) atTop (fun t ↦ D t k) := by
  intro k
  have hle := networkStockTrajectory_le_upper
    (fun t ↦ networkTransition_nonnegative model (hβ t))
    (fun t ↦ networkTransition_le_worst model (hβ t))
    (networkWorstMatrix_nonnegative model) (fun j ↦ (model.I_pos j).le) htraj hD0
  have htend := networkUpperPath_tendsto (networkWorstMatrix lambda₀ G) I (D 0) hnorm
  obtain ⟨b, hb⟩ := (tendsto_pi_nhds.mp htend k).isBoundedUnder_le
  rw [eventually_map] at hb
  refine ⟨b, ?_⟩
  rw [eventually_map]
  filter_upwards [hb] with t ht
  exact le_trans (hle t k) ht


/--
**The eventual slack estimate.** Under the certificate, every network policy
path eventually satisfies the coordinatewise gradient bound with any prescribed
positive slack. This is enough for the strict-margin theorem below, but is
weaker than the exact eventual-box hypothesis in
`NetworkCertificateForwardOfNormConclusions`.
-/
theorem networkGradient_eventually_le [Nonempty K]
    {lambda₀ η I v c : K → ℝ} {G : Matrix K K ℝ}
    (model : NetworkModelAssumptions lambda₀ η I v c G)
    (hnorm : ‖networkWorstMatrix lambda₀ G‖ < 1)
    (hcertificate : ∀ k,
      2 * c k * networkResolvent (networkWorstMatrix lambda₀ G) I k ≤ v k)
    {β D : ℕ → K → ℝ} (hβ : ∀ t k, β t k ∈ Icc (0 : ℝ) 1)
    (htraj : IsNetworkLoopTrajectory lambda₀ η G I β D) (hD0 : 0 ≤ D 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, ∀ t, T ≤ t → ∀ k,
      networkGradient v c (β t) (D t) k
        ≤ -2 * c k ^ 2 * β t k
            * networkResolvent (networkWorstMatrix lambda₀ G) I k
          + 2 * c k * ε := by
  set M := networkWorstMatrix lambda₀ G with hM
  have hMnonneg : MatrixEntrywiseNonnegative M := networkWorstMatrix_nonnegative model
  have hR : ∀ k, 0 < networkResolvent M I k :=
    networkResolvent_positive hMnonneg model.I_pos hnorm
  have hlimsup := networkPolicyFreeBound model hnorm hβ htraj hD0
  have hbdd := networkStock_isBoundedUnder model hnorm hβ htraj hD0
  obtain ⟨T, hT⟩ := exists_common_entry_time hε hlimsup hbdd
  refine ⟨T, fun t ht ↦ ?_⟩
  exact networkGradient_le_certificate_add_error model hcertificate
    (fun k ↦ hβ t k) hε.le (hT t ht)

end Closure

#print axioms networkGradient_le_certificate_add_error
#print axioms exists_common_entry_time
#print axioms networkStock_isBoundedUnder_of_summable
#print axioms networkStock_isBoundedUnder
#print axioms networkGradient_eventually_le


section StrictDescent

omit [Fintype K] [DecidableEq K] in
/--
**Strict margin makes the gradient uniformly negative.** Unlike the sharp case,
this holds at *every* policy value including `β_k = 0`, so `sign_consistent`
forbids any increase — which is what removes the need for entry into the exact
box `D ≤ R`, and hence for any simultaneity across communities.
-/
theorem networkGradient_neg_of_strictMargin
    {lambda₀ η I v c : K → ℝ} {G : Matrix K K ℝ}
    (model : NetworkModelAssumptions lambda₀ η I v c G)
    {R β D : K → ℝ} {ε μ : ℝ} (_hμ : 0 < μ)
    (hstrict : ∀ k, 2 * c k * R k + μ ≤ v k)
    (hβ : ∀ k, β k ∈ Icc (0 : ℝ) 1) (hR : ∀ k, 0 ≤ R k)
    (hε : 0 ≤ ε) (hεbound : 2 * ε ≤ μ / 2)
    (hD : ∀ k, D k ≤ R k + ε) :
    ∀ k, networkGradient v c β D k ≤ -(μ / 2) := by
  intro k
  have hc := model.c_pos k
  have hcle := model.c_lt_one k
  have hβ0 := (hβ k).1
  have hβ1 := (hβ k).2
  have hresidual : 0 ≤ 1 - c k * β k := by nlinarith
  have hRε : 0 ≤ R k + ε := by linarith [hR k]
  have hstep : 2 * c k * (1 - c k * β k) * D k ≤ 2 * c k * (R k + ε) := by
    have h1 : 2 * c k * (1 - c k * β k) * D k
        ≤ 2 * c k * (1 - c k * β k) * (R k + ε) :=
      mul_le_mul_of_nonneg_left (hD k) (by positivity)
    have h2 : 0 ≤ 2 * c k * (R k + ε) * (c k * β k) :=
      mul_nonneg (mul_nonneg (by positivity) hRε) (mul_nonneg hc.le hβ0)
    nlinarith [h1, h2]
  have hcε : 2 * c k * ε ≤ μ / 2 := by nlinarith [hcle, hε, hεbound, hc]
  simp only [networkGradient]
  nlinarith [hstep, hstrict k, hcε]

/--
**`thm:network`(ii'), closed under a strict certificate.** Every per-coordinate
sign-consistent responsive rule drives deference to zero in every community —
with no hypothesis on the initial stock and no appeal to the exact box.

Strictness is not decoration. At the sharp margin `v_k = 2c_k R_k` the gradient
can be marginally positive at low `β_k`; `sign_consistent` then permits an
arbitrary jump back up, communities can stagger their descents, and the coupled
stock need never enter `D ≤ R`, which is what
`networkDeference_tendsto_zero_of_eventually_bounded` requires.
-/
theorem networkDeference_tendsto_zero_of_strictMargin_of_summable [Nonempty K]
    {lambda₀ η I v c : K → ℝ} {G : Matrix K K ℝ}
    (model : NetworkModelAssumptions lambda₀ η I v c G)
    (hsum : Summable (fun n : ℕ ↦ networkWorstMatrix lambda₀ G ^ n))
    {μ : ℝ} (hμ : 0 < μ)
    (hstrict : ∀ k,
      2 * c k * networkResolvent (networkWorstMatrix lambda₀ G) I k + μ ≤ v k)
    {β D : ℕ → K → ℝ}
    (htraj : IsNetworkLoopTrajectory lambda₀ η G I β D) (hD0 : 0 ≤ D 0)
    (rule : NetworkSignConsistentResponsive v c β D) :
    Tendsto β atTop (nhds 0) := by
  set M := networkWorstMatrix lambda₀ G with hM
  have hMnonneg : MatrixEntrywiseNonnegative M := networkWorstMatrix_nonnegative model
  have hR : ∀ k, 0 < networkResolvent M I k :=
    networkResolvent_positive_of_summable hMnonneg model.I_pos hsum
  have hlimsup := network_policyFree_bound_of_summable
    (fun t ↦ networkTransition_nonnegative model (rule.unit_interval t))
    (fun t ↦ networkTransition_le_worst model (rule.unit_interval t))
    hMnonneg model.I_pos hsum htraj hD0
  have hbdd := networkStock_isBoundedUnder_of_summable
    model hsum rule.unit_interval htraj hD0
  obtain ⟨T, hT⟩ := exists_common_entry_time (by linarith : (0:ℝ) < μ / 8) hlimsup hbdd
  have hgrad : ∀ t, T ≤ t → ∀ k,
      networkGradient v c (β t) (D t) k ≤ -(μ / 2) := by
    intro t ht
    exact networkGradient_neg_of_strictMargin model hμ hstrict
      (rule.unit_interval t) (fun k ↦ (hR k).le) (by linarith) (by linarith)
      (hT t ht)
  have hstep : ∀ t, T ≤ t → ∀ k, β (t + 1) k ≤ β t k := fun t ht k ↦
    rule.sign_consistent k t ((hgrad t ht k).trans (by linarith))
  apply tendsto_pi_nhds.mpr
  intro k
  change Tendsto (fun t ↦ β t k) atTop (nhds (0 : ℝ))
  have hanti : Antitone (fun n ↦ β (T + n) k) := by
    apply antitone_nat_of_succ_le
    intro n
    simpa only [Nat.add_assoc] using hstep (T + n) (by omega) k
  apply tendsto_order.2
  refine ⟨fun a ha ↦ Eventually.of_forall fun n ↦ ha.trans_le (rule.unit_interval n k).1, ?_⟩
  intro b hb
  obtain ⟨d, hdpos, hresponsive⟩ := rule.responsive k (min (μ / 2) b)
    (lt_min (by linarith) hb)
  have hbelow : ∃ n, β (T + n) k < b := by
    apply exists_lt_of_uniform_descent (u := fun n ↦ β (T + n) k)
    · intro n; exact (rule.unit_interval (T + n) k).1
    · exact hdpos
    · intro n hn
      have hg := (hgrad (T + n) (by omega) k).trans (neg_le_neg (min_le_left (μ / 2) b))
      have hdec := hresponsive (T + n) hg ((min_le_right (μ / 2) b).trans hn)
      have hnext : β (T + n + 1) k ≤ β (T + n) k - d := by linarith
      simpa only [Nat.add_assoc] using hnext
  obtain ⟨n, hn⟩ := hbelow
  refine Filter.eventually_atTop.2 ⟨T + n, fun t ht ↦ ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ht
  have hle : β ((T + n) + j) k ≤ β (T + n) k := by
    simpa only [Nat.add_assoc] using hanti (Nat.le_add_right n j)
  exact hle.trans_lt hn

/-- The strict dynamic network certificate under the stronger one-step
operator-norm condition retained as a computation-ready corollary. -/
theorem networkDeference_tendsto_zero_of_strictMargin [Nonempty K]
    {lambda₀ η I v c : K → ℝ} {G : Matrix K K ℝ}
    (model : NetworkModelAssumptions lambda₀ η I v c G)
    (hnorm : ‖networkWorstMatrix lambda₀ G‖ < 1)
    {μ : ℝ} (hμ : 0 < μ)
    (hstrict : ∀ k,
      2 * c k * networkResolvent (networkWorstMatrix lambda₀ G) I k + μ ≤ v k)
    {β D : ℕ → K → ℝ}
    (htraj : IsNetworkLoopTrajectory lambda₀ η G I β D) (hD0 : 0 ≤ D 0)
    (rule : NetworkSignConsistentResponsive v c β D) :
    Tendsto β atTop (nhds 0) :=
  networkDeference_tendsto_zero_of_strictMargin_of_summable model
    (summable_geometric_of_norm_lt_one hnorm) hμ hstrict htraj hD0 rule

/-- Paper III, Theorem 5.2(ii') (`thm:network`), `civic_loops.tex:336`, under
the theorem's literal complex spectral-radius premise. -/
theorem networkDeference_tendsto_zero_of_strictMargin_of_spectralRadius [Nonempty K]
    {lambda₀ η I v c : K → ℝ} {G : Matrix K K ℝ}
    (model : NetworkModelAssumptions lambda₀ η I v c G)
    (hrho : spectralRadius ℂ
      (complexifyNetworkMatrix (networkWorstMatrix lambda₀ G)) < 1)
    {μ : ℝ} (hμ : 0 < μ)
    (hstrict : ∀ k,
      2 * c k * networkResolvent (networkWorstMatrix lambda₀ G) I k + μ ≤ v k)
    {β D : ℕ → K → ℝ}
    (htraj : IsNetworkLoopTrajectory lambda₀ η G I β D) (hD0 : 0 ≤ D 0)
    (rule : NetworkSignConsistentResponsive v c β D) :
    Tendsto β atTop (nhds 0) :=
  networkDeference_tendsto_zero_of_strictMargin_of_summable model
    (summable_real_matrix_powers_of_spectralRadius_lt_one hrho)
    hμ hstrict htraj hD0 rule

end StrictDescent

#print axioms networkGradient_neg_of_strictMargin
#print axioms networkDeference_tendsto_zero_of_strictMargin_of_summable
#print axioms networkDeference_tendsto_zero_of_strictMargin
#print axioms networkDeference_tendsto_zero_of_strictMargin_of_spectralRadius

section SpectralConverse

/-- Coordinatewise convergence of the nonnegative injection series in
Paper III, Theorem 5.2(iii) (`thm:network`), `civic_loops.tex:336`. -/
def NetworkInjectionSeriesConverges (M : Matrix K K ℝ) (I : K → ℝ) : Prop :=
  ∀ k, Summable (fun n : ℕ ↦ (M ^ n *ᵥ I) k)

/-- A uniform componentwise upper bound for the full-capture affine stock path
in Paper III, Theorem 5.2(iii) (`thm:network`), `civic_loops.tex:336`. -/
def NetworkUpperPathBounded (M : Matrix K K ℝ) (I D₀ : K → ℝ) : Prop :=
  ∃ b : ℝ, ∀ n k, networkUpperPath M I D₀ n k ≤ b

omit [Fintype K] [DecidableEq K] in
/-- A strictly positive finite injection vector dominates every nonnegative
initial stock after multiplication by one nonnegative scalar. -/
theorem exists_nonnegative_injection_domination [Finite K]
    {I D₀ : K → ℝ} (hI : ∀ k, 0 < I k) (hD₀ : 0 ≤ D₀) :
    ∃ C : ℝ, 0 ≤ C ∧ D₀ ≤ C • I := by
  classical
  letI := Fintype.ofFinite K
  let C : ℝ := ∑ k, D₀ k / I k
  have hratio : ∀ k, 0 ≤ D₀ k / I k := fun k ↦
    div_nonneg (hD₀ k) (hI k).le
  refine ⟨C, Finset.sum_nonneg fun k _ ↦ hratio k, ?_⟩
  intro k
  change D₀ k ≤ C * I k
  apply (div_le_iff₀ (hI k)).mp
  exact Finset.single_le_sum (fun j _ ↦ hratio j) (Finset.mem_univ k)

/-- Bounded nonnegative stock forces coordinatewise convergence of the
nonnegative injection series. This is the forward implication in Paper III,
Theorem 5.2(iii) (`thm:network`), `civic_loops.tex:336`. -/
theorem networkInjectionSeriesConverges_of_upperPath_bounded
    {M : Matrix K K ℝ} {I D₀ : K → ℝ}
    (hM : MatrixEntrywiseNonnegative M) (hI : 0 ≤ I) (hD₀ : 0 ≤ D₀)
    (hbdd : NetworkUpperPathBounded M I D₀) :
    NetworkInjectionSeriesConverges M I := by
  obtain ⟨b, hb⟩ := hbdd
  intro k
  have hterm : ∀ n : ℕ, 0 ≤ (M ^ n *ᵥ I) k := fun n ↦
    matrix_mulVec_nonnegative (matrix_pow_nonnegative hM n) hI k
  apply summable_of_sum_range_le (c := b) hterm
  intro n
  have htransient : 0 ≤ (M ^ n *ᵥ D₀) k :=
    matrix_mulVec_nonnegative (matrix_pow_nonnegative hM n) hD₀ k
  have hformula : networkUpperPath M I D₀ n k =
      (M ^ n *ᵥ D₀) k + ∑ j ∈ Finset.range n, (M ^ j *ᵥ I) k := by
    rw [networkUpperPath_eq]
    simp [Matrix.sum_mulVec, Finset.sum_apply]
  calc
    (∑ j ∈ Finset.range n, (M ^ j *ᵥ I) k) ≤
        (M ^ n *ᵥ D₀) k + ∑ j ∈ Finset.range n, (M ^ j *ᵥ I) k := by
      linarith
    _ = networkUpperPath M I D₀ n k := hformula.symm
    _ ≤ b := hb n k

/-- Coordinatewise convergence of the injection series bounds the affine stock
path from every nonnegative initial condition. This is the reverse implication
in Paper III, Theorem 5.2(iii) (`thm:network`), `civic_loops.tex:336`. -/
theorem networkUpperPath_bounded_of_injectionSeriesConverges
    {M : Matrix K K ℝ} {I D₀ : K → ℝ}
    (hM : MatrixEntrywiseNonnegative M) (hI : ∀ k, 0 < I k) (hD₀ : 0 ≤ D₀)
    (hseries : NetworkInjectionSeriesConverges M I) :
    NetworkUpperPathBounded M I D₀ := by
  obtain ⟨C, hC, hDle⟩ := exists_nonnegative_injection_domination hI hD₀
  let B : ℝ := ∑ k, (C + 1) * ∑' n : ℕ, (M ^ n *ᵥ I) k
  refine ⟨B, fun n k ↦ ?_⟩
  have hI_nonnegative : 0 ≤ I := fun j ↦ (hI j).le
  have hterm : ∀ (j : ℕ) (i : K), 0 ≤ (M ^ j *ᵥ I) i := fun j i ↦
    matrix_mulVec_nonnegative (matrix_pow_nonnegative hM j) hI_nonnegative i
  have htsum_nonnegative : ∀ i, 0 ≤ ∑' j : ℕ, (M ^ j *ᵥ I) i := fun i ↦
    tsum_nonneg fun j ↦ hterm j i
  have htransient_le : (M ^ n *ᵥ D₀) k ≤ C * (M ^ n *ᵥ I) k := by
    have hmono := matrix_mulVec_mono_right (matrix_pow_nonnegative hM n) hDle k
    simpa only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] using hmono
  have hterm_le : (M ^ n *ᵥ I) k ≤ ∑' j : ℕ, (M ^ j *ᵥ I) k :=
    (hseries k).le_tsum n (fun j _ ↦ hterm j k)
  have hpartial_le : (∑ j ∈ Finset.range n, (M ^ j *ᵥ I) k) ≤
      ∑' j : ℕ, (M ^ j *ᵥ I) k :=
    (hseries k).sum_le_tsum (Finset.range n) (fun j _ ↦ hterm j k)
  have hformula : networkUpperPath M I D₀ n k =
      (M ^ n *ᵥ D₀) k + ∑ j ∈ Finset.range n, (M ^ j *ᵥ I) k := by
    rw [networkUpperPath_eq]
    simp [Matrix.sum_mulVec, Finset.sum_apply]
  have hcoordinate : networkUpperPath M I D₀ n k ≤
      (C + 1) * ∑' j : ℕ, (M ^ j *ᵥ I) k := by
    rw [hformula]
    nlinarith [mul_le_mul_of_nonneg_left hterm_le hC]
  apply hcoordinate.trans
  exact Finset.single_le_sum
    (fun i _ ↦ mul_nonneg (by linarith) (htsum_nonnegative i))
    (Finset.mem_univ k)

/-- Paper III, Theorem 5.2(iii) (`thm:network`), `civic_loops.tex:336`:
for a nonnegative transition, positive injection, and nonnegative initial stock,
bounded stock is equivalent to convergence of the nonnegative injection series. -/
theorem networkUpperPath_bounded_iff_injectionSeriesConverges
    {M : Matrix K K ℝ} {I D₀ : K → ℝ}
    (hM : MatrixEntrywiseNonnegative M) (hI : ∀ k, 0 < I k) (hD₀ : 0 ≤ D₀) :
    NetworkUpperPathBounded M I D₀ ↔ NetworkInjectionSeriesConverges M I := by
  constructor
  · exact networkInjectionSeriesConverges_of_upperPath_bounded hM
      (fun k ↦ (hI k).le) hD₀
  · exact networkUpperPath_bounded_of_injectionSeriesConverges hM hI hD₀

/-- For a nonnegative matrix and a strictly positive injection, convergence of
the injection series forces summability of every matrix power. Positivity lets
the injection dominate each coordinate basis vector. -/
theorem summable_matrix_powers_of_injectionSeriesConverges
    {M : Matrix K K ℝ} {I : K → ℝ}
    (hM : MatrixEntrywiseNonnegative M) (hI : ∀ k, 0 < I k)
    (hseries : NetworkInjectionSeriesConverges M I) :
    Summable (fun n : ℕ ↦ M ^ n) := by
  have hentry : ∀ i j, Summable (fun n : ℕ ↦ (M ^ n) i j) := by
    intro i j
    obtain ⟨C, _, hsingle⟩ := exists_nonnegative_injection_domination
      hI (D₀ := Pi.single j 1) (Pi.single_nonneg.mpr zero_le_one)
    have hentry_nonnegative : ∀ n : ℕ, 0 ≤ (M ^ n) i j := fun n ↦
      matrix_pow_nonnegative hM n i j
    have hentry_le : ∀ n : ℕ, (M ^ n) i j ≤ C * (M ^ n *ᵥ I) i := by
      intro n
      have hmono := matrix_mulVec_mono_right (matrix_pow_nonnegative hM n) hsingle i
      simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.mulVec_smul,
        Pi.smul_apply, smul_eq_mul] using hmono
    exact Summable.of_nonneg_of_le hentry_nonnegative hentry_le
      ((hseries i).mul_left C)
  have hsingle : ∀ i j,
      Summable (fun n : ℕ ↦ Matrix.single i j ((M ^ n) i j)) := by
    intro i j
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using
      (hentry i j).smul_const (Matrix.single i j (1 : ℝ))
  have hfinset : ∀ (s : Finset K) (f : K → ℕ → Matrix K K ℝ),
      (∀ i ∈ s, Summable (f i)) →
      Summable (fun n ↦ ∑ i ∈ s, f i n) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        simpa [Finset.sum_insert ha] using (hf a (Finset.mem_insert_self a s)).add
          (ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))
  have hrows : ∀ i, Summable
      (fun n : ℕ ↦ ∑ j, Matrix.single i j ((M ^ n) i j)) := by
    intro i
    simpa only [Finset.sum_apply] using hfinset Finset.univ
      (fun j n ↦ Matrix.single i j ((M ^ n) i j))
      (fun j _ ↦ hsingle i j)
  have hall : Summable
      (fun n : ℕ ↦ ∑ i, ∑ j, Matrix.single i j ((M ^ n) i j)) := by
    simpa only [Finset.sum_apply] using hfinset Finset.univ
      (fun i n ↦ ∑ j, Matrix.single i j ((M ^ n) i j))
      (fun i _ ↦ hrows i)
  simpa only [← Matrix.matrix_eq_sum_single] using hall

/-- Summability of all matrix powers implies convergence of the injection
series for every injection vector. -/
theorem networkInjectionSeriesConverges_of_summable_matrix_powers
    {M : Matrix K K ℝ} {I : K → ℝ}
    (hsum : Summable (fun n : ℕ ↦ M ^ n)) :
    NetworkInjectionSeriesConverges M I := by
  have hentry : ∀ i j, Summable (fun n : ℕ ↦ (M ^ n) i j) := by
    intro i j
    let outer : Matrix K K ℝ →L[ℝ] (K → ℝ) := ContinuousLinearMap.proj i
    let inner : (K → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
    let evalEntry : Matrix K K ℝ →L[ℝ] ℝ := inner.comp outer
    have heval : ∀ A : Matrix K K ℝ, evalEntry A = A i j := by
      intro A
      rfl
    have hmapped := hsum.map evalEntry evalEntry.continuous
    rw [show (evalEntry ∘ fun n : ℕ ↦ M ^ n) = fun n : ℕ ↦ (M ^ n) i j by
      funext n
      exact heval (M ^ n)] at hmapped
    exact hmapped
  have hfinset : ∀ (s : Finset K) (f : K → ℕ → ℝ),
      (∀ i ∈ s, Summable (f i)) →
      Summable (fun n ↦ ∑ i ∈ s, f i n) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        simpa [Finset.sum_insert ha] using (hf a (Finset.mem_insert_self a s)).add
          (ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))
  intro i
  have hcoordinate : Summable (fun n : ℕ ↦ ∑ j, (M ^ n) i j * I j) :=
    hfinset Finset.univ (fun j n ↦ (M ^ n) i j * I j)
      (fun j _ ↦ (hentry i j).mul_right (I j))
  simpa only [Matrix.mulVec, dotProduct] using hcoordinate

/-- The standard nonnegative-matrix characterization quoted in Paper III,
Theorem 4(iii): the positive injection series converges exactly when the honest
complex spectral radius is below one. No Perron--Frobenius axiom is needed. -/
theorem networkInjectionSeriesConverges_iff_spectralRadius_lt_one
    [Nonempty K] {M : Matrix K K ℝ} {I : K → ℝ}
    (hM : MatrixEntrywiseNonnegative M) (hI : ∀ k, 0 < I k) :
    NetworkInjectionSeriesConverges M I ↔
      spectralRadius ℂ (complexifyNetworkMatrix M) < 1 := by
  constructor
  · intro hseries
    exact spectralRadius_lt_one_of_summable_real_matrix_powers
      (summable_matrix_powers_of_injectionSeriesConverges hM hI hseries)
  · intro hrho
    exact networkInjectionSeriesConverges_of_summable_matrix_powers
      (summable_real_matrix_powers_of_spectralRadius_lt_one hrho)

/-- Paper III, Theorem 5.2(iii) (`thm:network`), `civic_loops.tex:336`, with
both equivalent characterizations: bounded full-capture stock, convergence of
the nonnegative injection series, and complex spectral radius below one. -/
theorem networkUpperPath_bounded_iff_spectralRadius_lt_one
    [Nonempty K] {M : Matrix K K ℝ} {I D₀ : K → ℝ}
    (hM : MatrixEntrywiseNonnegative M) (hI : ∀ k, 0 < I k) (hD₀ : 0 ≤ D₀) :
    NetworkUpperPathBounded M I D₀ ↔
      spectralRadius ℂ (complexifyNetworkMatrix M) < 1 :=
  (networkUpperPath_bounded_iff_injectionSeriesConverges hM hI hD₀).trans
    (networkInjectionSeriesConverges_iff_spectralRadius_lt_one hM hI)

/-- Bounded full-capture stock from any nonnegative initial condition forces
the injected transition powers to vanish. -/
theorem networkPowers_tendsto_zero_of_upperPath_bounded
    {M : Matrix K K ℝ} {I D₀ : K → ℝ}
    (hM : MatrixEntrywiseNonnegative M) (hI : 0 ≤ I) (hD₀ : 0 ≤ D₀)
    (hbdd : NetworkUpperPathBounded M I D₀) :
    Tendsto (fun n ↦ (M ^ n) *ᵥ I) atTop (nhds 0) := by
  have hseries := networkInjectionSeriesConverges_of_upperPath_bounded hM hI hD₀ hbdd
  apply tendsto_pi_nhds.mpr
  intro k
  exact (hseries k).tendsto_atTop_zero

/--
**The dynamical half of `thm:network`(iii), without Perron--Frobenius.**
If the captured stock stays bounded then the transition powers annihilate the
injection.  Combined with `I ≻ 0` this is the asymptotic-stability
characterization, and it is what the divergence claim needs — the paper's left
Perron vector is not required.
-/
theorem networkPowers_tendsto_zero_of_bounded
    {M : Matrix K K ℝ} {I : K → ℝ} {b : ℝ}
    (hM : MatrixEntrywiseNonnegative M) (hI : ∀ k, 0 ≤ I k)
    (hbdd : ∀ n k, networkUpperPath M I 0 n k ≤ b) :
    Tendsto (fun n ↦ (M ^ n) *ᵥ I) atTop (nhds 0) := by
  have hterm : ∀ (n : ℕ) (k : K), 0 ≤ (M ^ n *ᵥ I) k := fun n k ↦
    matrix_mulVec_nonnegative (matrix_pow_nonnegative hM n) hI k
  apply tendsto_pi_nhds.mpr
  intro k
  have hpartial : ∀ n : ℕ, ∑ j ∈ Finset.range n, (M ^ j *ᵥ I) k ≤ b := by
    intro n
    have hsum : (∑ j ∈ Finset.range n, (M ^ j *ᵥ I) k)
        = networkUpperPath M I 0 n k := by
      rw [networkUpperPath_eq]
      simp [Matrix.sum_mulVec, Finset.sum_apply]
    rw [hsum]
    exact hbdd n k
  have hsummable : Summable (fun j ↦ (M ^ j *ᵥ I) k) :=
    summable_of_sum_range_le (fun n ↦ hterm n k) hpartial
  simpa using hsummable.tendsto_atTop_zero

end SpectralConverse

/-! ## The complete network theorem -/

/-- All substantive clauses of Paper III's network certificate, stated from
the paper's literal complex spectral-radius premise. -/
structure NetworkCertificateForwardConclusions
    (lambda₀ η I v c : K → ℝ) (G : Matrix K K ℝ) : Prop where
  spectral_condition :
    spectralRadius ℂ
      (complexifyNetworkMatrix (networkWorstMatrix lambda₀ G)) < 1
  resolvent_inverse :
    networkResolvent (networkWorstMatrix lambda₀ G) I =
      Ring.inverse (1 - networkWorstMatrix lambda₀ G) *ᵥ I
  resolvent_positive :
    ∀ k, 0 < networkResolvent (networkWorstMatrix lambda₀ G) I k
  policy_free_bound : ∀ {β D : ℕ → K → ℝ},
    (∀ t k, β t k ∈ Icc (0 : ℝ) 1) →
    IsNetworkLoopTrajectory lambda₀ η G I β D → 0 ≤ D 0 →
    ∀ k, limsup (fun t ↦ D t k) atTop ≤
      networkResolvent (networkWorstMatrix lambda₀ G) I k
  certificate_gradient : ∀ {β D : K → ℝ},
    (∀ k, β k ∈ Icc (0 : ℝ) 1) →
    D ≤ networkResolvent (networkWorstMatrix lambda₀ G) I →
    ∀ k, networkGradient v c β D k ≤
      -2 * c k ^ 2 * β k * networkResolvent (networkWorstMatrix lambda₀ G) I k
  certificate_strict : ∀ {β D : K → ℝ},
    (∀ k, β k ∈ Icc (0 : ℝ) 1) →
    D ≤ networkResolvent (networkWorstMatrix lambda₀ G) I →
    ∀ {k}, 0 < β k → networkGradient v c β D k < 0
  strict_dynamic : ∀ {μ : ℝ}, 0 < μ →
    (∀ k,
      2 * c k * networkResolvent (networkWorstMatrix lambda₀ G) I k + μ ≤ v k) →
    ∀ {β D : ℕ → K → ℝ},
      IsNetworkLoopTrajectory lambda₀ η G I β D → 0 ≤ D 0 →
      NetworkSignConsistentResponsive v c β D →
      Tendsto β atTop (nhds 0)
  stability_series : ∀ {D₀ : K → ℝ}, 0 ≤ D₀ →
    (NetworkUpperPathBounded (networkWorstMatrix lambda₀ G) I D₀ ↔
      NetworkInjectionSeriesConverges (networkWorstMatrix lambda₀ G) I)
  stability_spectral : ∀ {D₀ : K → ℝ}, 0 ≤ D₀ →
    (NetworkUpperPathBounded (networkWorstMatrix lambda₀ G) I D₀ ↔
      spectralRadius ℂ
        (complexifyNetworkMatrix (networkWorstMatrix lambda₀ G)) < 1)
  bounded_forces_powers_zero : ∀ {D₀ : K → ℝ}, 0 ≤ D₀ →
    NetworkUpperPathBounded (networkWorstMatrix lambda₀ G) I D₀ →
    Tendsto (fun n ↦ networkWorstMatrix lambda₀ G ^ n *ᵥ I) atTop (nhds 0)
  decentralized_condition :
    (∀ k, ∑ j, G k j < lambda₀ k) →
      ‖networkWorstMatrix lambda₀ G‖ < 1 ∧
        spectralRadius ℂ
          (complexifyNetworkMatrix (networkWorstMatrix lambda₀ G)) < 1

/--
Paper III, Theorem 5.2 (`thm:network`), `civic_loops.tex:336`.

From the theorem's literal complex spectral-radius premise this packages the
policy-free resolvent bound, the sharp static certificate, the uniformly strict
dynamic certificate, the full bounded-stock/series/spectral stability ceiling,
vanishing transition powers, and the decentralized row-sum condition. The
scalar recovery is the `K = 1` specialization already stated and proved by
`gainCeilings` in `Ceiling.lean`.
-/
theorem networkCertificateForward
    [Nonempty K] {lambda₀ η I v c : K → ℝ} {G : Matrix K K ℝ}
    (model : NetworkModelAssumptions lambda₀ η I v c G)
    (hrho : spectralRadius ℂ
      (complexifyNetworkMatrix (networkWorstMatrix lambda₀ G)) < 1)
    (hcertificate : ∀ k,
      2 * c k * networkResolvent (networkWorstMatrix lambda₀ G) I k ≤ v k) :
    NetworkCertificateForwardConclusions lambda₀ η I v c G := by
  have hM : MatrixEntrywiseNonnegative (networkWorstMatrix lambda₀ G) :=
    networkWorstMatrix_nonnegative model
  have hsum : Summable (fun n : ℕ ↦ networkWorstMatrix lambda₀ G ^ n) :=
    summable_real_matrix_powers_of_spectralRadius_lt_one hrho
  have hR : ∀ k, 0 < networkResolvent (networkWorstMatrix lambda₀ G) I k :=
    networkResolvent_positive_of_summable hM model.I_pos hsum
  refine {
    spectral_condition := hrho
    resolvent_inverse :=
      networkResolvent_eq_ringInverse_mulVec_of_summable
        (networkWorstMatrix lambda₀ G) I hsum
    resolvent_positive := hR
    policy_free_bound := ?_
    certificate_gradient := ?_
    certificate_strict := ?_
    strict_dynamic := ?_
    stability_series := ?_
    stability_spectral := ?_
    bounded_forces_powers_zero := ?_
    decentralized_condition := ?_ }
  · intro β D hβ htraj hD₀
    exact networkPolicyFreeBound_of_spectralRadius model hrho hβ htraj hD₀
  · intro β D hβ hD
    exact networkGradient_le_certificate model hcertificate hβ hD
  · intro β D hβ hD k hβk
    exact networkGradient_neg_of_pos model hR hcertificate hβ hD hβk
  · intro μ hμ hstrict β D htraj hD₀ rule
    exact networkDeference_tendsto_zero_of_strictMargin_of_spectralRadius
      model hrho hμ hstrict htraj hD₀ rule
  · exact fun {D₀} hD₀ ↦ networkUpperPath_bounded_iff_injectionSeriesConverges
      (D₀ := D₀) hM model.I_pos hD₀
  · exact fun {D₀} hD₀ ↦ networkUpperPath_bounded_iff_spectralRadius_lt_one
      (D₀ := D₀) hM model.I_pos hD₀
  · exact fun {D₀} hD₀ hbdd ↦ networkPowers_tendsto_zero_of_upperPath_bounded
      (D₀ := D₀) hM (fun k ↦ (model.I_pos k).le) hD₀ hbdd
  · intro hgain
    exact ⟨decentralizedGain_implies_norm_lt_one model hgain,
      decentralizedGain_implies_spectralRadius_lt_one model hgain⟩

#print axioms networkPowers_tendsto_zero_of_bounded
#print axioms exists_nonnegative_injection_domination
#print axioms networkInjectionSeriesConverges_of_upperPath_bounded
#print axioms networkUpperPath_bounded_of_injectionSeriesConverges
#print axioms networkUpperPath_bounded_iff_injectionSeriesConverges
#print axioms summable_matrix_powers_of_injectionSeriesConverges
#print axioms networkInjectionSeriesConverges_of_summable_matrix_powers
#print axioms networkInjectionSeriesConverges_iff_spectralRadius_lt_one
#print axioms networkUpperPath_bounded_iff_spectralRadius_lt_one
#print axioms networkPowers_tendsto_zero_of_upperPath_bounded
#print axioms networkCertificateForward

end CivicAlignment.PaperIII
