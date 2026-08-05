/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.ClassificationConvergence

/-!
# Paper III: the epsilon-inflated box, with an explicit slack

`thm:classify` proves convergence for orbits in `B = [0,1] x [I, R]`,
`R := I/(λ₀-g)`, because `(SS_g^+)` is read off the extrema of `B`.  Orbits
from arbitrary nonnegative stock never enter `B` when they start above it --- the
excess contracts geometrically but stays positive --- so the paper runs the
argument on "a sufficiently small `ε`-inflation" of `B` instead.

That slack is not merely small: it is exact.  On `B_ε = [0,1] x [I, R+ε]` the
four extrema give strict diagonal dominance precisely when

  `R + ε  <  I (s(0)+g) / (α · convergentStepDenominator p)`,

whose right side is `R · α_mono(g)/α`.  So the admissible inflation is

  `ε* = R (α_mono(g)/α - 1)`,

the box height times the fractional `(SS_g^+)` margin: the slack you can afford
is exactly the slack you have.  This file proves that, together with invariance
of `B_ε`, the fact that cooperativity on `B_ε` is implied rather than assumed,
and geometric entry into `B_ε` from arbitrary nonnegative stock.
-/

namespace CivicAlignment.PaperIII

open Filter Set Topology

noncomputable section

variable {p : LoopParams}

/-! ## The exact admissible slack -/

/-- The ceiling below which the inflated box still carries strict dominance. -/
def dominanceCeiling (p : LoopParams) : ℝ :=
  p.I * (p.s 0 + p.g) / (p.α * convergentStepDenominator p)

/-- The exact admissible inflation of `B`: the box height times the margin. -/
def inflationSlack (p : LoopParams) : ℝ :=
  dominanceCeiling p - stockCeiling p

/--
Strict diagonal dominance on the box with ceiling `M` holds exactly below
`dominanceCeiling`.  This is the identity that turns "sufficiently small" into a
closed form.
-/
theorem dominance_iff_lt_dominanceCeiling (model : LoopModelAssumptions p)
    (_hgain : p.g < p.lambda₀) (M : ℝ) :
    policyStockUpper p * stockPolicyUpperAt p M <
        policyDiagonalLowerAt p M * stockDiagonalLower p ↔
      M < dominanceCeiling p := by
  have hden : 0 < convergentStepDenominator p :=
    convergentStepDenominator_pos model
  have hd : 0 < stockDiagonalLower p := stockDiagonalLower_pos model
  have hαI : 0 < p.α * convergentStepDenominator p :=
    mul_pos model.α_pos hden
  rw [dominanceCeiling, lt_div_iff₀ hαI]
  simp only [policyStockUpper, stockPolicyUpperAt, policyDiagonalLowerAt,
    stockDiagonalLower, convergentStepDenominator]
  constructor <;> intro h <;> nlinarith [model.c_pos, model.α_pos, model.I_pos, h]

/-- Under `(SS_g^+)` the admissible slack is strictly positive. -/
theorem inflationSlack_pos (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) (ssplus : ConvergentStepAssumption p) :
    0 < inflationSlack p := by
  have hden : 0 < convergentStepDenominator p :=
    convergentStepDenominator_pos model
  have hgap : 0 < p.lambda₀ - p.g := sub_pos.mpr hgain
  have hd : 0 < stockDiagonalLower p := stockDiagonalLower_pos model
  have hbound := ssplus.bound
  rw [lt_div_iff₀ hden] at hbound
  have hαI : 0 < p.α * convergentStepDenominator p := mul_pos model.α_pos hden
  rw [inflationSlack, sub_pos, stockCeiling, dominanceCeiling,
    div_lt_div_iff₀ hgap hαI]
  simp only [stockDiagonalLower] at hd hbound
  nlinarith [model.I_pos, hbound, hd]

/-- The ceiling of the inflated box, `R + ε`. -/
def inflatedCeiling (p : LoopParams) (ε : ℝ) : ℝ := stockCeiling p + ε

/-- Paper III's box, inflated by a slack `ε`. -/
def inflatedBox (p : LoopParams) (ε : ℝ) : Set LoopState :=
  boxAt p (inflatedCeiling p ε)

/-- At zero slack the inflated box is the printed box `B`. -/
theorem inflatedBox_zero (p : LoopParams) :
    inflatedBox p 0 = classificationBox p := by
  simp only [inflatedBox, inflatedCeiling, add_zero, boxAt_stockCeiling]

/-! ## What the inflated box inherits -/

/-- The inflated box is forward invariant for every nonnegative slack. -/
theorem inflatedBox_invariant (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {ε : ℝ} (hε : 0 ≤ ε) :
    MapsTo p.loopMap (inflatedBox p ε) (inflatedBox p ε) := by
  rintro ⟨β, D⟩ ⟨hβ, hD⟩
  have hgap : 0 < p.lambda₀ - p.g := sub_pos.mpr hgain
  have hs := stockMultiplier_nonneg_le model hβ
  have hD0 : 0 ≤ D := le_trans model.I_pos.le hD.1
  have hmult0 : 0 ≤ p.s β + p.g := by linarith [hs.1, model.g_nonneg]
  have hRfix : (1 - p.lambda₀ + p.g) * stockCeiling p + p.I = stockCeiling p := by
    have hSI : stockCeiling p * (p.lambda₀ - p.g) = p.I := by
      rw [stockCeiling]; field_simp
    linear_combination -hSI
  refine ⟨LoopParams.clipUnit_mem _, ?_, ?_⟩
  · change p.I ≤ (p.s β + p.g) * D + p.I
    nlinarith [mul_nonneg hmult0 hD0]
  · change (p.s β + p.g) * D + p.I ≤ inflatedCeiling p ε
    simp only [inflatedCeiling] at hD ⊢
    have hσ1 : p.s β + p.g ≤ 1 - p.lambda₀ + p.g := by linarith [hs.2]
    have hceil0 : 0 ≤ stockCeiling p + ε := le_trans hD0 hD.2
    have hkey : (p.s β + p.g) * D ≤ (1 - p.lambda₀ + p.g) * (stockCeiling p + ε) :=
      mul_le_mul hσ1 hD.2 hD0 (by linarith [hs.1, model.g_nonneg, hs.2])
    nlinarith [hkey, hRfix, model.lambda₀_pos, hε, hgain]

/--
On the inflated box, cooperativity is implied by strict dominance rather than
assumed: the policy diagonal entry is automatically positive.
-/
theorem policyDiagonalLowerAt_pos_of_dominance (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {M : ℝ} (hM : 0 ≤ M)
    (hdom : M < dominanceCeiling p) :
    0 < policyDiagonalLowerAt p M := by
  have hd : 0 < stockDiagonalLower p := stockDiagonalLower_pos model
  have hstrict := (dominance_iff_lt_dominanceCeiling model hgain M).2 hdom
  have hcross : 0 ≤ policyStockUpper p * stockPolicyUpperAt p M := by
    simp only [policyStockUpper, stockPolicyUpperAt]
    have h1 : 0 ≤ 2 * p.α * p.c :=
      mul_nonneg (mul_nonneg two_pos.le model.α_pos.le) model.c_pos.le
    have h2 : 0 ≤ 2 * p.η * (1 - p.lambda₀) * M :=
      mul_nonneg (mul_nonneg (mul_nonneg two_pos.le model.η_pos.le)
        (sub_nonneg.mpr model.lambda₀_lt_one.le)) hM
    exact mul_nonneg h1 h2
  nlinarith [hstrict, hcross, hd]

/-! ## Entry from arbitrary nonnegative stock -/

/-- The stock excess over the stationary ceiling contracts uniformly in policy. -/
theorem stock_excess_contracts (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {x : ℕ → LoopState} (traj : IsLoopOrbit p x)
    (hβ : ∀ n, (x n).1 ∈ Icc (0 : ℝ) 1) (hD : ∀ n, 0 ≤ (x n).2) (n : ℕ) :
    (x (n + 1)).2 - stockCeiling p ≤
      (1 - p.lambda₀ + p.g) * ((x n).2 - stockCeiling p) := by
  have hgap : 0 < p.lambda₀ - p.g := sub_pos.mpr hgain
  have hRfix : (1 - p.lambda₀ + p.g) * stockCeiling p + p.I = stockCeiling p := by
    have hSI : stockCeiling p * (p.lambda₀ - p.g) = p.I := by
      rw [stockCeiling]; field_simp
    linear_combination -hSI
  have hs := stockMultiplier_nonneg_le model (hβ n)
  have hstep : (x (n + 1)).2 = (p.s (x n).1 + p.g) * (x n).2 + p.I := by
    rw [traj n]; rfl
  rw [hstep]
  nlinarith [hs.2, hD n, hRfix]

/--
Geometric decay of the excess: the orbit's stock falls below every strictly
positive inflation of the ceiling in finitely many steps, uniformly in policy.
-/
theorem stock_le_inflatedCeiling_eventually (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {x : ℕ → LoopState} (traj : IsLoopOrbit p x)
    (hβ : ∀ n, (x n).1 ∈ Icc (0 : ℝ) 1) (hD : ∀ n, 0 ≤ (x n).2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (x n).2 ≤ inflatedCeiling p ε := by
  set σ : ℝ := 1 - p.lambda₀ + p.g with hσdef
  have hσ0 : 0 ≤ σ :=
    add_nonneg (sub_nonneg.mpr model.lambda₀_lt_one.le) model.g_nonneg
  have hσ1 : σ < 1 := by rw [hσdef]; linarith
  have hgeom : ∀ n, (x n).2 - stockCeiling p ≤ σ ^ n * ((x 0).2 - stockCeiling p) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hstep := stock_excess_contracts model hgain traj hβ hD n
        have := mul_le_mul_of_nonneg_left ih hσ0
        calc (x (n + 1)).2 - stockCeiling p ≤ σ * ((x n).2 - stockCeiling p) := hstep
          _ ≤ σ * (σ ^ n * ((x 0).2 - stockCeiling p)) := this
          _ = σ ^ (n + 1) * ((x 0).2 - stockCeiling p) := by ring
  rcases le_or_gt ((x 0).2 - stockCeiling p) 0 with hle | hgt
  · filter_upwards with n
    have := hgeom n
    have hpow : 0 ≤ σ ^ n := pow_nonneg hσ0 n
    have : σ ^ n * ((x 0).2 - stockCeiling p) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpow hle
    simp only [inflatedCeiling]
    linarith [hgeom n]
  · have htend : Tendsto (fun n : ℕ ↦ σ ^ n * ((x 0).2 - stockCeiling p))
        atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hσ0 hσ1).mul_const
        ((x 0).2 - stockCeiling p)
    filter_upwards [htend.eventually (ge_mem_nhds hε)] with n hn
    simp only [inflatedCeiling]
    linarith [hgeom n]

/--
Paper III, the `ε`-inflation bridge, quantitative form.  Under `(SS_g^+)` there
is a strictly positive explicit slack `ε*` such that for every `ε` in `(0, ε*)`
the inflated box is forward invariant, carries strict diagonal dominance with
cooperativity implied, and is entered in finitely many steps from arbitrary
nonnegative stock.
-/
theorem inflationBridge (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (ssplus : ConvergentStepAssumption p) :
    0 < inflationSlack p ∧
    ∀ ε ∈ Ioo (0 : ℝ) (inflationSlack p),
      MapsTo p.loopMap (inflatedBox p ε) (inflatedBox p ε) ∧
      policyStockUpper p * stockPolicyUpperAt p (inflatedCeiling p ε) <
        policyDiagonalLowerAt p (inflatedCeiling p ε) * stockDiagonalLower p ∧
      0 < policyDiagonalLowerAt p (inflatedCeiling p ε) ∧
      ∀ {x : ℕ → LoopState}, IsLoopOrbit p x →
        (∀ n, (x n).1 ∈ Icc (0 : ℝ) 1) → (∀ n, 0 ≤ (x n).2) →
        ∀ᶠ n in atTop, (x n).2 ≤ inflatedCeiling p ε := by
  have hslack := inflationSlack_pos model hgain ssplus
  refine ⟨hslack, fun ε hε => ?_⟩
  have hceil : inflatedCeiling p ε < dominanceCeiling p := by
    simp only [inflatedCeiling, inflationSlack] at hε ⊢
    linarith [hε.2]
  have hceil_nonneg : 0 ≤ inflatedCeiling p ε := by
    have : 0 < stockCeiling p :=
      div_pos model.I_pos (sub_pos.mpr hgain)
    simp only [inflatedCeiling]; linarith [hε.1]
  exact ⟨inflatedBox_invariant model hgain hε.1.le,
    (dominance_iff_lt_dominanceCeiling model hgain _).2 hceil,
    policyDiagonalLowerAt_pos_of_dominance model hgain hceil_nonneg hceil,
    fun traj hβ hD =>
      stock_le_inflatedCeiling_eventually model hgain traj hβ hD hε.1⟩

#print axioms dominance_iff_lt_dominanceCeiling
#print axioms inflationSlack_pos
#print axioms inflatedBox_invariant
#print axioms policyDiagonalLowerAt_pos_of_dominance
#print axioms stock_excess_contracts
#print axioms stock_le_inflatedCeiling_eventually
#print axioms inflationBridge

/-! ## The bridge in force: convergence from arbitrary nonnegative stock -/

/-- Every admissible slack yields a ceiling the convergence argument accepts. -/
theorem ceilingAssumption_inflated (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) (inflationSlack p)) :
    CeilingAssumption p (inflatedCeiling p ε) := by
  have hceil : inflatedCeiling p ε < dominanceCeiling p := by
    simp only [inflatedCeiling, inflationSlack] at hε ⊢
    linarith [hε.2]
  have hceil_nonneg : 0 ≤ inflatedCeiling p ε := by
    have : 0 < stockCeiling p := div_pos model.I_pos (sub_pos.mpr hgain)
    simp only [inflatedCeiling]; linarith [hε.1]
  have hdom := (dominance_iff_lt_dominanceCeiling model hgain _).2 hceil
  exact ⟨⟨by simp only [inflatedCeiling]; linarith [hε.1],
      (policyDiagonalLowerAt_pos_of_dominance model hgain hceil_nonneg hceil).le⟩,
    hdom⟩

/--
Paper III, `thm:classify` for arbitrary nonnegative stock.  Under `(SS_g^+)`
every orbit of the simultaneous loop starting from any nonnegative stock
converges to a loop equilibrium: the orbit enters the `ε`-inflated box in
finitely many steps for any admissible slack, and the convergence argument runs
there verbatim.  This is the `ε`-inflation bridge in force.
-/
theorem globalConvergence_of_nonnegative_stock (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) (ssplus : ConvergentStepAssumption p)
    {x : ℕ → LoopState} (traj : IsLoopOrbit p x)
    (hβ₀ : (x 0).1 ∈ Icc (0 : ℝ) 1) (hD₀ : 0 ≤ (x 0).2) :
    ∃ q, Tendsto x atTop (𝓝 q) ∧ IsLoopEquilibrium p q.1 q.2 := by
  have hslack := inflationSlack_pos model hgain ssplus
  set ε : ℝ := inflationSlack p / 2 with hεdef
  have hεmem : ε ∈ Ioo (0 : ℝ) (inflationSlack p) := ⟨by positivity, by linarith⟩
  have hM := ceilingAssumption_inflated model hgain hεmem
  have hβ : ∀ n, (x n).1 ∈ Icc (0 : ℝ) 1 := policy_mem_unit traj hβ₀
  have hD : ∀ n, 0 ≤ (x n).2 := stock_nonneg model traj hβ₀ hD₀
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (stock_le_inflatedCeiling_eventually model hgain traj hβ hD hεmem.1)
  have hlow1 : ∀ k, p.I ≤ (x (k + 1)).2 := by
    intro k
    have hmult : 0 ≤ (p.s (x k).1 + p.g) * (x k).2 :=
      mul_nonneg (add_nonneg (stockMultiplier_nonneg_le model (hβ k)).1
        model.g_nonneg) (hD k)
    rw [traj k]
    simpa only [LoopParams.loopMap, LoopParams.stockStep] using
      le_add_of_nonneg_left hmult
  have hshiftTraj : IsLoopOrbit p (fun n ↦ x (n + (N + 1))) := by
    intro n
    simpa only [show n + 1 + (N + 1) = n + (N + 1) + 1 by omega] using traj (n + (N + 1))
  have hstart : (fun n ↦ x (n + (N + 1))) 0 ∈ boxAt p (inflatedCeiling p ε) := by
    refine ⟨hβ _, ?_, hN _ (by omega)⟩
    simpa only [show 0 + (N + 1) = N + 1 by omega] using hlow1 N
  obtain ⟨q, _, hlim, hq⟩ := classification_globalConvergence_of_convergentStep
    model hgain hM hshiftTraj hstart
  exact ⟨q, (tendsto_add_atTop_iff_nat (N + 1)).1 hlim, hq⟩

#print axioms ceilingAssumption_inflated
#print axioms globalConvergence_of_nonnegative_stock

end

end CivicAlignment.PaperIII
