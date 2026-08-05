/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.BistabilityTheorem
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Paper II: convergence under the orientation-preserving step bound

This file formalizes the self-contained convergence argument of Paper II's
`thm:bistable`.  Cooperativity alone permits a period-two orbit.  The stronger
condition `(SS+)` makes the diagonal product dominate the two cross effects;
that excludes alternation between southeast and northwest increments.
-/

namespace CivicAlignment.PaperII

open Filter Function Set Topology

noncomputable section

/-! ## The stronger step condition and its four uniform coefficients -/

/-- The denominator in Paper II's convergent-step threshold. -/
def convergentStepDenominator (p : LoopParams) : ℝ :=
  2 * p.c * p.I * (p.c * p.s 0 + 2 * p.η * (1 - p.lambda₀))

/-- Paper II, Assumption `(SS+)` (`ass:ssplus`), `civic_drift.tex:202`. -/
structure ConvergentStepAssumption (p : LoopParams) : Prop where
  bound : p.α < p.lambda₀ * p.s 0 / convergentStepDenominator p

/-- Uniform lower bound for the policy diagonal response on `B`. -/
def policyDiagonalLower (p : LoopParams) : ℝ :=
  1 - 2 * p.α * p.c ^ 2 * (p.I / p.lambda₀)

/-- Uniform upper bound for the stock-to-policy cross response on `B`. -/
def policyStockUpper (p : LoopParams) : ℝ :=
  2 * p.α * p.c

/-- Uniform upper bound for the policy-to-stock cross response on `B`. -/
def stockPolicyUpper (p : LoopParams) : ℝ :=
  2 * p.η * (1 - p.lambda₀) * (p.I / p.lambda₀)

/-- Uniform lower bound for the stock diagonal response on `B`. -/
def stockDiagonalLower (p : LoopParams) : ℝ :=
  p.s 0

/-- Positivity needed to interpret Paper II's `(SS+)` denominator;
auxiliary to `thm:bistable(e)`, `civic_drift.tex:197--223`. -/
theorem convergentStepDenominator_pos {p : LoopParams}
    (model : DriftModelAssumptions p) :
    0 < convergentStepDenominator p := by
  have hs0 : 0 ≤ p.s 0 :=
    (driftStockMultiplier_nonneg_le model (by norm_num)).1
  have htail : 0 < 2 * p.η * (1 - p.lambda₀) :=
    mul_pos (mul_pos two_pos model.η_pos) (sub_pos.mpr model.lambda₀_lt_one)
  have hbracket : 0 < p.c * p.s 0 + 2 * p.η * (1 - p.lambda₀) :=
    add_pos_of_nonneg_of_pos (mul_nonneg model.c_pos.le hs0) htail
  simp only [convergentStepDenominator]
  exact mul_pos (mul_pos (mul_pos two_pos model.c_pos) model.I_pos) hbracket

/-- `(SS+)` forces the least stock diagonal to be positive;
auxiliary to `thm:bistable(e)`, `civic_drift.tex:197--223`. -/
theorem ConvergentStepAssumption.stockDiagonalLower_pos {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p) :
    0 < stockDiagonalLower p := by
  have hquot : 0 < p.lambda₀ * p.s 0 / convergentStepDenominator p :=
    model.α_pos.trans ssplus.bound
  have hden := convergentStepDenominator_pos model
  have hnum : 0 < p.lambda₀ * p.s 0 := (div_pos_iff.mp hquot).elim
    (fun h => h.1) (fun h => (not_lt_of_ge hden.le h.2).elim)
  rcases (mul_pos_iff.mp hnum) with h | h
  · simpa only [stockDiagonalLower] using h.2
  · exact (not_lt_of_ge model.lambda₀_pos.le h.1).elim

/-- Paper II's convergent-step condition implies its strict cooperative step;
auxiliary to `thm:bistable(e)`, `civic_drift.tex:197--223`. -/
theorem ConvergentStepAssumption.toStrictSmallStep {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p) :
    StrictSmallStepAssumption p := by
  have hs0 := ssplus.stockDiagonalLower_pos model
  have hden := convergentStepDenominator_pos model
  have hbound : p.α * convergentStepDenominator p < p.lambda₀ * p.s 0 :=
    (lt_div_iff₀ hden).mp ssplus.bound
  have htail : 0 < 2 * p.η * (1 - p.lambda₀) :=
    mul_pos (mul_pos two_pos model.η_pos) (sub_pos.mpr model.lambda₀_lt_one)
  have hbase : 0 < 2 * p.c * p.I := mul_pos (mul_pos two_pos model.c_pos) model.I_pos
  have hdenCore :
      2 * p.c * p.I * (p.c * p.s 0) < convergentStepDenominator p := by
    simp only [convergentStepDenominator]
    exact mul_lt_mul_of_pos_left (lt_add_of_pos_right _ htail) hbase
  have hcore :
      (2 * p.α * p.c ^ 2 * p.I) * p.s 0 < p.lambda₀ * p.s 0 := by
    calc
      (2 * p.α * p.c ^ 2 * p.I) * p.s 0 =
          p.α * (2 * p.c * p.I * (p.c * p.s 0)) := by ring
      _ < p.α * convergentStepDenominator p :=
        mul_lt_mul_of_pos_left hdenCore model.α_pos
      _ < p.lambda₀ * p.s 0 := hbound
  refine ⟨?_⟩
  have hs0' : 0 < p.s 0 := by simpa only [stockDiagonalLower] using hs0
  exact (mul_lt_mul_iff_left₀ hs0').mp hcore

/-- `(SS+)` leaves a strictly positive uniform policy diagonal;
auxiliary to `thm:bistable(e)`, `civic_drift.tex:197--223`. -/
theorem ConvergentStepAssumption.policyDiagonalLower_pos {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p) :
    0 < policyDiagonalLower p := by
  have hsmall := ssplus.toStrictSmallStep model
  have hlambda := model.lambda₀_pos
  have hratio : 2 * p.α * p.c ^ 2 * (p.I / p.lambda₀) < 1 := by
    rw [show 2 * p.α * p.c ^ 2 * (p.I / p.lambda₀) =
      (2 * p.α * p.c ^ 2 * p.I) / p.lambda₀ by ring]
    exact (div_lt_one hlambda).2 hsmall.bound
  simpa only [policyDiagonalLower] using sub_pos.mpr hratio

/-- The uniform stock-to-policy cross bound is positive;
auxiliary to `thm:bistable(e)`, `civic_drift.tex:197--223`. -/
theorem policyStockUpper_pos {p : LoopParams} (model : DriftModelAssumptions p) :
    0 < policyStockUpper p := by
  simp only [policyStockUpper]
  exact mul_pos (mul_pos two_pos model.α_pos) model.c_pos

/-- `(SS+)` is exactly strict dominance of the uniform diagonal product over
the two cross effects. -/
theorem ConvergentStepAssumption.crossProduct_lt_diagonalProduct {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p) :
    policyStockUpper p * stockPolicyUpper p <
      policyDiagonalLower p * stockDiagonalLower p := by
  have hden := convergentStepDenominator_pos model
  have hbound : p.α * convergentStepDenominator p < p.lambda₀ * p.s 0 :=
    (lt_div_iff₀ hden).mp ssplus.bound
  simp only [convergentStepDenominator] at hbound
  have hscaled :
      p.lambda₀ * (policyStockUpper p * stockPolicyUpper p) <
        p.lambda₀ * (policyDiagonalLower p * stockDiagonalLower p) := by
    have hleft :
        p.lambda₀ * (policyStockUpper p * stockPolicyUpper p) =
          4 * p.α * p.c * p.η * (1 - p.lambda₀) * p.I := by
      simp only [policyStockUpper, stockPolicyUpper]
      field_simp [model.lambda₀_pos.ne']
      ring
    have hright :
        p.lambda₀ * (policyDiagonalLower p * stockDiagonalLower p) =
          (p.lambda₀ - 2 * p.α * p.c ^ 2 * p.I) * p.s 0 := by
      simp only [policyDiagonalLower, stockDiagonalLower]
      field_simp [model.lambda₀_pos.ne']
    rw [hleft, hright]
    nlinarith [hbound]
  exact (mul_lt_mul_iff_right₀ model.lambda₀_pos).mp hscaled

/-! ## Uniform difference estimates on the invariant box -/

/-- The stock multiplier has the paper's sharp uniform slope bound on `[0,1]`. -/
theorem stockMultiplier_sub_le {p : LoopParams} (model : DriftModelAssumptions p)
    {β₁ β₂ : ℝ} (hβ₁ : β₁ ∈ Icc (0 : ℝ) 1) (hβ₂ : β₂ ∈ Icc (0 : ℝ) 1)
    (hβ : β₁ ≤ β₂) :
    p.s β₂ - p.s β₁ ≤
      2 * p.η * (1 - p.lambda₀) * (β₂ - β₁) := by
  let r₁ := 1 - p.η * (1 - β₁)
  let r₂ := 1 - p.η * (1 - β₂)
  have hr₁_nonneg : 0 ≤ r₁ := by
    dsimp only [r₁]
    have hresidual : 1 - β₁ ≤ 1 := by linarith [hβ₁.1]
    have := mul_le_mul_of_nonneg_left hresidual model.η_pos.le
    nlinarith [model.η_le_one]
  have hr₂_nonneg : 0 ≤ r₂ := by
    dsimp only [r₂]
    have hresidual : 1 - β₂ ≤ 1 := by linarith [hβ₂.1]
    have := mul_le_mul_of_nonneg_left hresidual model.η_pos.le
    nlinarith [model.η_le_one]
  have hr₁_le : r₁ ≤ 1 := by
    dsimp only [r₁]
    exact sub_le_self _ (mul_nonneg model.η_pos.le (sub_nonneg.mpr hβ₁.2))
  have hr₂_le : r₂ ≤ 1 := by
    dsimp only [r₂]
    exact sub_le_self _ (mul_nonneg model.η_pos.le (sub_nonneg.mpr hβ₂.2))
  have hdiff : r₂ - r₁ = p.η * (β₂ - β₁) := by
    dsimp only [r₁, r₂]
    ring
  have hsum : r₂ + r₁ ≤ 2 := by linarith
  have hfactor : r₂ ^ 2 - r₁ ^ 2 = (r₂ - r₁) * (r₂ + r₁) := by ring
  have hdelta_nonneg : 0 ≤ p.η * (β₂ - β₁) :=
    mul_nonneg model.η_pos.le (sub_nonneg.mpr hβ)
  calc
    p.s β₂ - p.s β₁ = (1 - p.lambda₀) * (r₂ ^ 2 - r₁ ^ 2) := by
      simp only [LoopParams.s]
      dsimp only [r₁, r₂]
      ring
    _ = (1 - p.lambda₀) * (p.η * (β₂ - β₁) * (r₂ + r₁)) := by
      rw [hfactor, hdiff]
    _ ≤ (1 - p.lambda₀) * (p.η * (β₂ - β₁) * 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsum hdelta_nonneg)
        (sub_nonneg.mpr model.lambda₀_lt_one.le)
    _ = 2 * p.η * (1 - p.lambda₀) * (β₂ - β₁) := by ring

/-- Lower policy-input estimate for a southeast increment. -/
theorem southeast_unclipped_difference_lower {p : LoopParams}
    (model : DriftModelAssumptions p) {x y : LoopState}
    (hx : x ∈ absorbingBox p) (hy : y ∈ absorbingBox p)
    (hβ : x.1 ≤ y.1) (hD : y.2 ≤ x.2) :
    policyDiagonalLower p * (y.1 - x.1) -
        policyStockUpper p * (x.2 - y.2) ≤
      unclippedDeferenceInput p y.1 y.2 - unclippedDeferenceInput p x.1 x.2 := by
  have hk : 0 ≤ 2 * p.α * p.c ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) (sq_nonneg p.c)
  have ha : policyDiagonalLower p ≤ 1 - 2 * p.α * p.c ^ 2 * y.2 := by
    simp only [policyDiagonalLower]
    have := mul_le_mul_of_nonneg_left hy.2.2 hk
    linarith
  have hb : 2 * p.α * p.c * (1 - p.c * x.1) ≤ policyStockUpper p := by
    have hcx : 0 ≤ p.c * x.1 := mul_nonneg model.c_pos.le hx.1.1
    have hcoef : 0 ≤ 2 * p.α * p.c :=
      mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) model.c_pos.le
    simp only [policyStockUpper]
    nlinarith [mul_le_mul_of_nonneg_left (show 1 - p.c * x.1 ≤ 1 by linarith) hcoef]
  have hap := mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hβ)
  have hbq := mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr hD)
  simp only [unclippedDeferenceInput, LoopParams.gradU]
  nlinarith

/-- Upper stock estimate for a southeast increment. -/
theorem southeast_stock_difference_upper {p : LoopParams}
    (model : DriftModelAssumptions p) {x y : LoopState}
    (hx : x ∈ absorbingBox p) (hy : y ∈ absorbingBox p)
    (hβ : x.1 ≤ y.1) (hD : y.2 ≤ x.2) :
    p.stockStep y.1 y.2 - p.stockStep x.1 x.2 ≤
      stockPolicyUpper p * (y.1 - x.1) -
        stockDiagonalLower p * (x.2 - y.2) := by
  have hsmono : p.s x.1 ≤ p.s y.1 :=
    (driftStockMultiplier_strictMonoOn model).monotoneOn hx.1 hy.1 hβ
  have hsdiff_nonneg : 0 ≤ p.s y.1 - p.s x.1 := sub_nonneg.mpr hsmono
  have hslope := stockMultiplier_sub_le model hx.1 hy.1 hβ
  have hstockPolicy :
      (p.s y.1 - p.s x.1) * y.2 ≤ stockPolicyUpper p * (y.1 - x.1) := by
    have hupper_nonneg : 0 ≤ p.I / p.lambda₀ :=
      (div_pos model.I_pos model.lambda₀_pos).le
    have hslope_nonneg :
        0 ≤ 2 * p.η * (1 - p.lambda₀) * (y.1 - x.1) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) model.η_pos.le)
          (sub_nonneg.mpr model.lambda₀_lt_one.le))
        (sub_nonneg.mpr hβ)
    have hy_nonneg : 0 ≤ y.2 := model.I_pos.le.trans hy.2.1
    have hmul := mul_le_mul hslope hy.2.2 hy_nonneg hslope_nonneg
    simpa only [stockPolicyUpper] using (show
      (p.s y.1 - p.s x.1) * y.2 ≤
        2 * p.η * (1 - p.lambda₀) * (p.I / p.lambda₀) * (y.1 - x.1) by
      calc
        (p.s y.1 - p.s x.1) * y.2 ≤
            (2 * p.η * (1 - p.lambda₀) * (y.1 - x.1)) *
              (p.I / p.lambda₀) := hmul
        _ = 2 * p.η * (1 - p.lambda₀) * (p.I / p.lambda₀) *
              (y.1 - x.1) := by ring)
  have hs0 : p.s 0 ≤ p.s x.1 :=
    (driftStockMultiplier_strictMonoOn model).monotoneOn (by norm_num) hx.1 hx.1.1
  have hstockDiagonal := mul_le_mul_of_nonneg_right hs0 (sub_nonneg.mpr hD)
  simp only [LoopParams.stockStep, model.no_content_gain, add_zero,
    stockDiagonalLower]
  nlinarith

/-- Upper policy-input estimate for a northwest increment. -/
theorem northwest_unclipped_difference_upper {p : LoopParams}
    (model : DriftModelAssumptions p) {x y : LoopState}
    (hx : x ∈ absorbingBox p) (hy : y ∈ absorbingBox p)
    (hβ : y.1 ≤ x.1) (hD : x.2 ≤ y.2) :
    unclippedDeferenceInput p y.1 y.2 - unclippedDeferenceInput p x.1 x.2 ≤
      -policyDiagonalLower p * (x.1 - y.1) +
        policyStockUpper p * (y.2 - x.2) := by
  have hk : 0 ≤ 2 * p.α * p.c ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) (sq_nonneg p.c)
  have ha : policyDiagonalLower p ≤ 1 - 2 * p.α * p.c ^ 2 * y.2 := by
    simp only [policyDiagonalLower]
    have := mul_le_mul_of_nonneg_left hy.2.2 hk
    linarith
  have hb : 2 * p.α * p.c * (1 - p.c * x.1) ≤ policyStockUpper p := by
    have hcx : 0 ≤ p.c * x.1 := mul_nonneg model.c_pos.le hx.1.1
    have hcoef : 0 ≤ 2 * p.α * p.c :=
      mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) model.c_pos.le
    simp only [policyStockUpper]
    nlinarith [mul_le_mul_of_nonneg_left (show 1 - p.c * x.1 ≤ 1 by linarith) hcoef]
  have hap := mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hβ)
  have hbq := mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr hD)
  simp only [unclippedDeferenceInput, LoopParams.gradU]
  nlinarith

/-- Lower stock estimate for a northwest increment. -/
theorem northwest_stock_difference_lower {p : LoopParams}
    (model : DriftModelAssumptions p) {x y : LoopState}
    (hx : x ∈ absorbingBox p) (hy : y ∈ absorbingBox p)
    (hβ : y.1 ≤ x.1) (hD : x.2 ≤ y.2) :
    -stockPolicyUpper p * (x.1 - y.1) +
        stockDiagonalLower p * (y.2 - x.2) ≤
      p.stockStep y.1 y.2 - p.stockStep x.1 x.2 := by
  have hsmono : p.s y.1 ≤ p.s x.1 :=
    (driftStockMultiplier_strictMonoOn model).monotoneOn hy.1 hx.1 hβ
  have hsdiff_nonneg : 0 ≤ p.s x.1 - p.s y.1 := sub_nonneg.mpr hsmono
  have hslope := stockMultiplier_sub_le model hy.1 hx.1 hβ
  have hstockPolicy :
      (p.s x.1 - p.s y.1) * y.2 ≤ stockPolicyUpper p * (x.1 - y.1) := by
    have hupper_nonneg : 0 ≤ p.I / p.lambda₀ :=
      (div_pos model.I_pos model.lambda₀_pos).le
    have hslope_nonneg :
        0 ≤ 2 * p.η * (1 - p.lambda₀) * (x.1 - y.1) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) model.η_pos.le)
          (sub_nonneg.mpr model.lambda₀_lt_one.le))
        (sub_nonneg.mpr hβ)
    have hy_nonneg : 0 ≤ y.2 := model.I_pos.le.trans hy.2.1
    have hmul := mul_le_mul hslope hy.2.2 hy_nonneg hslope_nonneg
    simpa only [stockPolicyUpper] using (show
      (p.s x.1 - p.s y.1) * y.2 ≤
        2 * p.η * (1 - p.lambda₀) * (p.I / p.lambda₀) * (x.1 - y.1) by
      calc
        (p.s x.1 - p.s y.1) * y.2 ≤
            (2 * p.η * (1 - p.lambda₀) * (x.1 - y.1)) *
              (p.I / p.lambda₀) := hmul
        _ = 2 * p.η * (1 - p.lambda₀) * (p.I / p.lambda₀) *
              (x.1 - y.1) := by ring)
  have hs0 : p.s 0 ≤ p.s x.1 :=
    (driftStockMultiplier_strictMonoOn model).monotoneOn (by norm_num) hx.1 hx.1.1
  have hstockDiagonal := mul_le_mul_of_nonneg_right hs0 (sub_nonneg.mpr hD)
  simp only [LoopParams.stockStep, model.no_content_gain, add_zero,
    stockDiagonalLower]
  nlinarith

/-! ## Comparable steps and monotone convergence -/

/-- The projected simultaneous loop map is continuous. -/
theorem continuous_loopMap (p : LoopParams) : Continuous p.loopMap := by
  unfold LoopParams.loopMap LoopParams.deferenceStep LoopParams.stockStep
    LoopParams.gradU LoopParams.s LoopParams.clipUnit
  fun_prop

/-- An orbit starting in `B` stays in `B`. -/
theorem trajectory_mem_absorbingBox {p : LoopParams} (model : DriftModelAssumptions p)
    {x : ℕ → LoopState} (traj : IsLoopTrajectory p x)
    (hx0 : x 0 ∈ absorbingBox p) : ∀ n, x n ∈ absorbingBox p := by
  intro n
  induction n with
  | zero => exact hx0
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by omega, traj n]
      exact invariantBox model ih

/-- A componentwise increasing step propagates forever by cooperativity. -/
theorem trajectory_tail_monotone_of_le {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    {x : ℕ → LoopState} (traj : IsLoopTrajectory p x)
    (hmem : ∀ n, x n ∈ absorbingBox p) {t : ℕ} (hstep : x t ≤ x (t + 1)) :
    Monotone (fun n ↦ x (n + t)) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero =>
      simpa [Nat.add_comm] using hstep
  | succ n ih =>
      have hmono := loopMap_monotoneOn_box model ss
        (hmem (n + t)) (hmem (n + 1 + t)) ih
      calc
        x (Nat.succ n + t) = p.loopMap (x (n + t)) := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using traj (n + t)
        _ ≤ p.loopMap (x (n + 1 + t)) := hmono
        _ = x (Nat.succ n + 1 + t) := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using (traj (n + 1 + t)).symm

/-- A componentwise decreasing step propagates forever by cooperativity. -/
theorem trajectory_tail_antitone_of_ge {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    {x : ℕ → LoopState} (traj : IsLoopTrajectory p x)
    (hmem : ∀ n, x n ∈ absorbingBox p) {t : ℕ} (hstep : x (t + 1) ≤ x t) :
    Antitone (fun n ↦ x (n + t)) := by
  apply antitone_nat_of_succ_le
  intro n
  induction n with
  | zero =>
      simpa [Nat.add_comm] using hstep
  | succ n ih =>
      have hmono := loopMap_monotoneOn_box model ss
        (hmem (n + 1 + t)) (hmem (n + t)) ih
      calc
        x (Nat.succ n + 1 + t) = p.loopMap (x (n + 1 + t)) := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using traj (n + 1 + t)
        _ ≤ p.loopMap (x (n + t)) := hmono
        _ = x (Nat.succ n + t) := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using (traj (n + t)).symm

/-- A componentwise monotone sequence contained in `B` converges in `ℝ²`. -/
theorem monotone_sequence_tendsto_in_absorbingBox {p : LoopParams}
    {x : ℕ → LoopState} (hmono : Monotone x)
    (hmem : ∀ n, x n ∈ absorbingBox p) :
    ∃ q ∈ absorbingBox p, Tendsto x atTop (𝓝 q) := by
  have hβmono : Monotone (fun n ↦ (x n).1) := fun _ _ h ↦ (hmono h).1
  have hDmono : Monotone (fun n ↦ (x n).2) := fun _ _ h ↦ (hmono h).2
  have hβbdd : BddAbove (range fun n ↦ (x n).1) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (hmem n).1.2
  have hDbdd : BddAbove (range fun n ↦ (x n).2) := by
    refine ⟨p.I / p.lambda₀, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (hmem n).2.2
  let q : LoopState :=
    (⨆ n, (x n).1, ⨆ n, (x n).2)
  have hβlim : Tendsto (fun n ↦ (x n).1) atTop (𝓝 q.1) := by
    simpa only [q] using tendsto_atTop_ciSup hβmono hβbdd
  have hDlim : Tendsto (fun n ↦ (x n).2) atTop (𝓝 q.2) := by
    simpa only [q] using tendsto_atTop_ciSup hDmono hDbdd
  have hlim : Tendsto x atTop (𝓝 q) := (Prod.tendsto_iff x q).2 ⟨hβlim, hDlim⟩
  have hclosed : IsClosed (absorbingBox p) := isClosed_Icc.prod isClosed_Icc
  exact ⟨q, hclosed.mem_of_tendsto hlim (Eventually.of_forall hmem), hlim⟩

/-- A componentwise antitone sequence contained in `B` converges in `ℝ²`. -/
theorem antitone_sequence_tendsto_in_absorbingBox {p : LoopParams}
    {x : ℕ → LoopState} (hanti : Antitone x)
    (hmem : ∀ n, x n ∈ absorbingBox p) :
    ∃ q ∈ absorbingBox p, Tendsto x atTop (𝓝 q) := by
  have hβanti : Antitone (fun n ↦ (x n).1) := fun _ _ h ↦ (hanti h).1
  have hDanti : Antitone (fun n ↦ (x n).2) := fun _ _ h ↦ (hanti h).2
  have hβbdd : BddBelow (range fun n ↦ (x n).1) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (hmem n).1.1
  have hDbdd : BddBelow (range fun n ↦ (x n).2) := by
    refine ⟨p.I, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (hmem n).2.1
  let q : LoopState :=
    (⨅ n, (x n).1, ⨅ n, (x n).2)
  have hβlim : Tendsto (fun n ↦ (x n).1) atTop (𝓝 q.1) := by
    simpa only [q] using tendsto_atTop_ciInf hβanti hβbdd
  have hDlim : Tendsto (fun n ↦ (x n).2) atTop (𝓝 q.2) := by
    simpa only [q] using tendsto_atTop_ciInf hDanti hDbdd
  have hlim : Tendsto x atTop (𝓝 q) := (Prod.tendsto_iff x q).2 ⟨hβlim, hDlim⟩
  have hclosed : IsClosed (absorbingBox p) := isClosed_Icc.prod isClosed_Icc
  exact ⟨q, hclosed.mem_of_tendsto hlim (Eventually.of_forall hmem), hlim⟩

/-- The limit of a loop trajectory is a fixed point of the loop map. -/
theorem trajectory_limit_is_equilibrium {p : LoopParams} {x : ℕ → LoopState}
    (traj : IsLoopTrajectory p x) {q : LoopState}
    (hlim : Tendsto x atTop (𝓝 q)) : IsLoopEquilibrium p q.1 q.2 := by
  have hshift : Tendsto (fun n ↦ x (n + 1)) atTop (𝓝 q) :=
    (tendsto_add_atTop_iff_nat 1).2 hlim
  have hmapToQ : Tendsto (fun n ↦ p.loopMap (x n)) atTop (𝓝 q) := by
    apply hshift.congr'
    exact Eventually.of_forall fun n ↦ traj n
  have hmapToMap : Tendsto (fun n ↦ p.loopMap (x n)) atTop (𝓝 (p.loopMap q)) :=
    ((continuous_loopMap p).tendsto q).comp hlim
  exact tendsto_nhds_unique hmapToMap hmapToQ

/-- Paper II, Theorem 3.14 (`thm:bistable`), clause (d),
`civic_drift.tex:262`: one comparable step makes the tail monotone and forces
convergence to a fixed point. -/
theorem comparableStep_convergesToFixedPoint {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    {x : ℕ → LoopState} (traj : IsLoopTrajectory p x)
    (hx0 : x 0 ∈ absorbingBox p) {t : ℕ}
    (hcomparable : x t ≤ x (t + 1) ∨ x (t + 1) ≤ x t) :
    ∃ q ∈ absorbingBox p,
      Tendsto x atTop (𝓝 q) ∧ IsLoopEquilibrium p q.1 q.2 := by
  have hmem := trajectory_mem_absorbingBox model traj hx0
  rcases hcomparable with hstep | hstep
  · have hmono := trajectory_tail_monotone_of_le model ss traj hmem hstep
    obtain ⟨q, hq, hlim⟩ := monotone_sequence_tendsto_in_absorbingBox hmono
      (fun n ↦ hmem (n + t))
    have hfull : Tendsto x atTop (𝓝 q) := (tendsto_add_atTop_iff_nat t).1 hlim
    exact ⟨q, hq, hfull, trajectory_limit_is_equilibrium traj hfull⟩
  · have hanti := trajectory_tail_antitone_of_ge model ss traj hmem hstep
    obtain ⟨q, hq, hlim⟩ := antitone_sequence_tendsto_in_absorbingBox hanti
      (fun n ↦ hmem (n + t))
    have hfull : Tendsto x atTop (𝓝 q) := (tendsto_add_atTop_iff_nat t).1 hlim
    exact ⟨q, hq, hfull, trajectory_limit_is_equilibrium traj hfull⟩

/-! ## Exclusion of quadrant alternation under `(SS+)` -/

/-- A strict southeast increment: policy rises while stock falls. -/
def Southeast (x y : LoopState) : Prop :=
  x.1 < y.1 ∧ y.2 < x.2

/-- A strict northwest increment: policy falls while stock rises. -/
def Northwest (x y : LoopState) : Prop :=
  y.1 < x.1 ∧ x.2 < y.2

/-- Any non-comparable pair in the planar product order has exactly one of the
two strict mixed directions. -/
theorem southeast_or_northwest_of_not_comparable {x y : LoopState}
    (h : ¬(x ≤ y ∨ y ≤ x)) : Southeast x y ∨ Northwest x y := by
  rcases lt_trichotomy x.1 y.1 with hβ | hβ | hβ
  · left
    refine ⟨hβ, ?_⟩
    by_contra hD
    exact h (Or.inl ⟨hβ.le, not_lt.mp hD⟩)
  · exfalso
    apply h
    rcases le_total x.2 y.2 with hD | hD
    · exact Or.inl ⟨hβ.le, hD⟩
    · exact Or.inr ⟨hβ.ge, hD⟩
  · right
    refine ⟨hβ, ?_⟩
    by_contra hD
    exact h (Or.inr ⟨hβ.le, not_lt.mp hD⟩)

/-- The elementary small-gain contradiction used in both orientations. -/
theorem cross_inequalities_impossible {a b c d u w : ℝ}
    (hu : 0 < u) (hw : 0 < w) (hb : 0 < b) (hd : 0 < d)
    (hgain : b * c < a * d) (hpolicy : a * u < b * w)
    (hstock : d * w < c * u) : False := by
  have h₁ := mul_lt_mul_of_pos_right hpolicy (mul_pos hd hw)
  have h₂ := mul_lt_mul_of_pos_left hstock (mul_pos hb hw)
  have hnormalized : (a * d) * (u * w) < (b * c) * (u * w) := by
    calc
      (a * d) * (u * w) = (a * u) * (d * w) := by ring
      _ < (b * w) * (d * w) := h₁
      _ < (b * w) * (c * u) := h₂
      _ = (b * c) * (u * w) := by ring
  have hbad : a * d < b * c :=
    (mul_lt_mul_iff_left₀ (mul_pos hu hw)).mp hnormalized
  exact (not_lt_of_ge hgain.le) hbad

/-- Under `(SS+)`, a southeast step cannot be followed by a northwest step. -/
theorem no_southeast_to_northwest {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    {x y : LoopState} (hx : x ∈ absorbingBox p) (hy : y ∈ absorbingBox p)
    (hxy : Southeast x y) : ¬Northwest (p.loopMap x) (p.loopMap y) := by
  intro hnext
  have hinput : unclippedDeferenceInput p y.1 y.2 <
      unclippedDeferenceInput p x.1 x.2 := by
    by_contra hnot
    have hmono := LoopParams.monotone_clipUnit (not_lt.mp hnot)
    have hpolicy : (p.loopMap x).1 ≤ (p.loopMap y).1 := by
      simpa only [LoopParams.loopMap, LoopParams.deferenceStep,
        unclippedDeferenceInput] using hmono
    exact (not_lt_of_ge hpolicy) hnext.1
  have hpolicyBound := southeast_unclipped_difference_lower model hx hy
    hxy.1.le hxy.2.le
  have hpolicy : policyDiagonalLower p * (y.1 - x.1) <
      policyStockUpper p * (x.2 - y.2) := by
    nlinarith
  have hstockBound := southeast_stock_difference_upper model hx hy
    hxy.1.le hxy.2.le
  have hstock : stockDiagonalLower p * (x.2 - y.2) <
      stockPolicyUpper p * (y.1 - x.1) := by
    have hnextStock : 0 < p.stockStep y.1 y.2 - p.stockStep x.1 x.2 := by
      simpa only [LoopParams.loopMap] using sub_pos.mpr hnext.2
    nlinarith
  exact cross_inequalities_impossible (sub_pos.mpr hxy.1) (sub_pos.mpr hxy.2)
    (policyStockUpper_pos model) (ssplus.stockDiagonalLower_pos model)
    (ssplus.crossProduct_lt_diagonalProduct model) hpolicy hstock

/-- Under `(SS+)`, a northwest step cannot be followed by a southeast step. -/
theorem no_northwest_to_southeast {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    {x y : LoopState} (hx : x ∈ absorbingBox p) (hy : y ∈ absorbingBox p)
    (hxy : Northwest x y) : ¬Southeast (p.loopMap x) (p.loopMap y) := by
  intro hnext
  have hinput : unclippedDeferenceInput p x.1 x.2 <
      unclippedDeferenceInput p y.1 y.2 := by
    by_contra hnot
    have hmono := LoopParams.monotone_clipUnit (not_lt.mp hnot)
    have hpolicy : (p.loopMap y).1 ≤ (p.loopMap x).1 := by
      simpa only [LoopParams.loopMap, LoopParams.deferenceStep,
        unclippedDeferenceInput] using hmono
    exact (not_lt_of_ge hpolicy) hnext.1
  have hpolicyBound := northwest_unclipped_difference_upper model hx hy
    hxy.1.le hxy.2.le
  have hpolicy : policyDiagonalLower p * (x.1 - y.1) <
      policyStockUpper p * (y.2 - x.2) := by
    nlinarith
  have hstockBound := northwest_stock_difference_lower model hx hy
    hxy.1.le hxy.2.le
  have hstock : stockDiagonalLower p * (y.2 - x.2) <
      stockPolicyUpper p * (x.1 - y.1) := by
    have hnextStock : p.stockStep y.1 y.2 - p.stockStep x.1 x.2 < 0 := by
      simpa only [LoopParams.loopMap] using sub_neg.mpr hnext.2
    nlinarith
  exact cross_inequalities_impossible (sub_pos.mpr hxy.1) (sub_pos.mpr hxy.2)
    (policyStockUpper_pos model) (ssplus.stockDiagonalLower_pos model)
    (ssplus.crossProduct_lt_diagonalProduct model) hpolicy hstock

/-- Trajectory form of southeast-to-northwest exclusion. -/
theorem trajectory_no_southeast_to_northwest {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    {x : ℕ → LoopState} (traj : IsLoopTrajectory p x)
    (hmem : ∀ n, x n ∈ absorbingBox p) {n : ℕ}
    (hstep : Southeast (x n) (x (n + 1))) :
    ¬Northwest (x (n + 1)) (x (n + 2)) := by
  have h := no_southeast_to_northwest model ssplus (hmem n) (hmem (n + 1)) hstep
  simpa [show n + 2 = (n + 1) + 1 by omega, traj n, traj (n + 1)] using h

/-- Trajectory form of northwest-to-southeast exclusion. -/
theorem trajectory_no_northwest_to_southeast {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    {x : ℕ → LoopState} (traj : IsLoopTrajectory p x)
    (hmem : ∀ n, x n ∈ absorbingBox p) {n : ℕ}
    (hstep : Northwest (x n) (x (n + 1))) :
    ¬Southeast (x (n + 1)) (x (n + 2)) := by
  have h := no_northwest_to_southeast model ssplus (hmem n) (hmem (n + 1)) hstep
  simpa [show n + 2 = (n + 1) + 1 by omega, traj n, traj (n + 1)] using h

/-- If no step is comparable and the first step is southeast, every step is. -/
theorem trajectory_southeast_of_no_comparable_step {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    {x : ℕ → LoopState} (traj : IsLoopTrajectory p x)
    (hmem : ∀ n, x n ∈ absorbingBox p)
    (hnone : ∀ n, ¬(x n ≤ x (n + 1) ∨ x (n + 1) ≤ x n))
    (hfirst : Southeast (x 0) (x 1)) :
    ∀ n, Southeast (x n) (x (n + 1)) := by
  intro n
  induction n with
  | zero => simpa using hfirst
  | succ n ih =>
      rcases southeast_or_northwest_of_not_comparable (hnone (n + 1)) with h | h
      · simpa [Nat.succ_eq_add_one] using h
      · exact (trajectory_no_southeast_to_northwest model ssplus traj hmem ih
          (by simpa [Nat.succ_eq_add_one] using h)).elim

/-- If no step is comparable and the first step is northwest, every step is. -/
theorem trajectory_northwest_of_no_comparable_step {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    {x : ℕ → LoopState} (traj : IsLoopTrajectory p x)
    (hmem : ∀ n, x n ∈ absorbingBox p)
    (hnone : ∀ n, ¬(x n ≤ x (n + 1) ∨ x (n + 1) ≤ x n))
    (hfirst : Northwest (x 0) (x 1)) :
    ∀ n, Northwest (x n) (x (n + 1)) := by
  intro n
  induction n with
  | zero => simpa using hfirst
  | succ n ih =>
      rcases southeast_or_northwest_of_not_comparable (hnone (n + 1)) with h | h
      · exact (trajectory_no_northwest_to_southeast model ssplus traj hmem ih
          (by simpa [Nat.succ_eq_add_one] using h)).elim
      · simpa [Nat.succ_eq_add_one] using h

/-- A trajectory whose every step is southeast converges in the invariant box. -/
theorem southeast_trajectory_tendsto_in_absorbingBox {p : LoopParams}
    {x : ℕ → LoopState} (hmem : ∀ n, x n ∈ absorbingBox p)
    (hstep : ∀ n, Southeast (x n) (x (n + 1))) :
    ∃ q ∈ absorbingBox p, Tendsto x atTop (𝓝 q) := by
  have hβmono : Monotone (fun n ↦ (x n).1) :=
    monotone_nat_of_le_succ fun n ↦ (hstep n).1.le
  have hDanti : Antitone (fun n ↦ (x n).2) :=
    antitone_nat_of_succ_le fun n ↦ (hstep n).2.le
  have hβbdd : BddAbove (range fun n ↦ (x n).1) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; exact (hmem n).1.2⟩
  have hDbdd : BddBelow (range fun n ↦ (x n).2) :=
    ⟨p.I, by rintro _ ⟨n, rfl⟩; exact (hmem n).2.1⟩
  let q : LoopState := (⨆ n, (x n).1, ⨅ n, (x n).2)
  have hlim : Tendsto x atTop (𝓝 q) := (Prod.tendsto_iff x q).2 ⟨
    by simpa only [q] using tendsto_atTop_ciSup hβmono hβbdd,
    by simpa only [q] using tendsto_atTop_ciInf hDanti hDbdd⟩
  have hclosed : IsClosed (absorbingBox p) := isClosed_Icc.prod isClosed_Icc
  exact ⟨q, hclosed.mem_of_tendsto hlim (Eventually.of_forall hmem), hlim⟩

/-- A trajectory whose every step is northwest converges in the invariant box. -/
theorem northwest_trajectory_tendsto_in_absorbingBox {p : LoopParams}
    {x : ℕ → LoopState} (hmem : ∀ n, x n ∈ absorbingBox p)
    (hstep : ∀ n, Northwest (x n) (x (n + 1))) :
    ∃ q ∈ absorbingBox p, Tendsto x atTop (𝓝 q) := by
  have hβanti : Antitone (fun n ↦ (x n).1) :=
    antitone_nat_of_succ_le fun n ↦ (hstep n).1.le
  have hDmono : Monotone (fun n ↦ (x n).2) :=
    monotone_nat_of_le_succ fun n ↦ (hstep n).2.le
  have hβbdd : BddBelow (range fun n ↦ (x n).1) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact (hmem n).1.1⟩
  have hDbdd : BddAbove (range fun n ↦ (x n).2) :=
    ⟨p.I / p.lambda₀, by rintro _ ⟨n, rfl⟩; exact (hmem n).2.2⟩
  let q : LoopState := (⨅ n, (x n).1, ⨆ n, (x n).2)
  have hlim : Tendsto x atTop (𝓝 q) := (Prod.tendsto_iff x q).2 ⟨
    by simpa only [q] using tendsto_atTop_ciInf hβanti hβbdd,
    by simpa only [q] using tendsto_atTop_ciSup hDmono hDbdd⟩
  have hclosed : IsClosed (absorbingBox p) := isClosed_Icc.prod isClosed_Icc
  exact ⟨q, hclosed.mem_of_tendsto hlim (Eventually.of_forall hmem), hlim⟩

/-- Turn the fixed-point catalogue into an equality catalogue for a state pair. -/
theorem equilibrium_mem_bistable_catalogue {p : LoopParams}
    (model : DriftModelAssumptions p) (threshold : ThresholdAssumption p)
    {q : LoopState} (heq : IsLoopEquilibrium p q.1 q.2) :
    q = calibratedPoint p ∨ q = saddlePoint p threshold ∨ q = capturedPoint p := by
  rcases (loopEquilibrium_iff_three_points model threshold q.1 q.2).mp heq with h | h | h
  · left
    exact Prod.ext h.1 h.2
  · right; left
    exact Prod.ext h.1 h.2
  · right; right
    exact Prod.ext h.1 h.2

/--
Paper II, Theorem 3.14 (`thm:bistable`), clause (e),
`civic_drift.tex:266`.

Under the literal `(SS+)` bound, every orbit in `B` converges to one of the
three fixed points.  The proof is self-contained: a comparable step invokes
clause (d); otherwise `(SS+)` excludes quadrant alternation, so the policy and
stock coordinates are monotone in opposite directions.
-/
theorem bistability_globalConvergence_of_convergentStep {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) {x : ℕ → LoopState}
    (traj : IsLoopTrajectory p x) (hx0 : x 0 ∈ absorbingBox p) :
    ∃ q ∈ absorbingBox p, Tendsto x atTop (𝓝 q) ∧
      (q = calibratedPoint p ∨ q = saddlePoint p threshold ∨ q = capturedPoint p) := by
  have ss : SmallStepAssumption p := (ssplus.toStrictSmallStep model).toSmallStep
  have hmem := trajectory_mem_absorbingBox model traj hx0
  by_cases hcomparable : ∃ t, x t ≤ x (t + 1) ∨ x (t + 1) ≤ x t
  · obtain ⟨t, ht⟩ := hcomparable
    obtain ⟨q, hq, hlim, heq⟩ :=
      comparableStep_convergesToFixedPoint model ss traj hx0 ht
    exact ⟨q, hq, hlim, equilibrium_mem_bistable_catalogue model threshold heq⟩
  · have hnone : ∀ n, ¬(x n ≤ x (n + 1) ∨ x (n + 1) ≤ x n) := by
      intro n hn
      exact hcomparable ⟨n, hn⟩
    rcases southeast_or_northwest_of_not_comparable (hnone 0) with hfirst | hfirst
    · have hall := trajectory_southeast_of_no_comparable_step model ssplus traj hmem hnone
        (by simpa using hfirst)
      obtain ⟨q, hq, hlim⟩ := southeast_trajectory_tendsto_in_absorbingBox hmem hall
      have heq := trajectory_limit_is_equilibrium traj hlim
      exact ⟨q, hq, hlim, equilibrium_mem_bistable_catalogue model threshold heq⟩
    · have hall := trajectory_northwest_of_no_comparable_step model ssplus traj hmem hnone
        (by simpa using hfirst)
      obtain ⟨q, hq, hlim⟩ := northwest_trajectory_tendsto_in_absorbingBox hmem hall
      have heq := trajectory_limit_is_equilibrium traj hlim
      exact ⟨q, hq, hlim, equilibrium_mem_bistable_catalogue model threshold heq⟩

#print axioms convergentStepDenominator_pos
#print axioms ConvergentStepAssumption.stockDiagonalLower_pos
#print axioms ConvergentStepAssumption.toStrictSmallStep
#print axioms ConvergentStepAssumption.policyDiagonalLower_pos
#print axioms policyStockUpper_pos
#print axioms ConvergentStepAssumption.crossProduct_lt_diagonalProduct
#print axioms stockMultiplier_sub_le
#print axioms southeast_unclipped_difference_lower
#print axioms southeast_stock_difference_upper
#print axioms northwest_unclipped_difference_upper
#print axioms northwest_stock_difference_lower
#print axioms continuous_loopMap
#print axioms trajectory_mem_absorbingBox
#print axioms trajectory_tail_monotone_of_le
#print axioms trajectory_tail_antitone_of_ge
#print axioms monotone_sequence_tendsto_in_absorbingBox
#print axioms antitone_sequence_tendsto_in_absorbingBox
#print axioms trajectory_limit_is_equilibrium
#print axioms comparableStep_convergesToFixedPoint
#print axioms southeast_or_northwest_of_not_comparable
#print axioms cross_inequalities_impossible
#print axioms no_southeast_to_northwest
#print axioms no_northwest_to_southeast
#print axioms trajectory_no_southeast_to_northwest
#print axioms trajectory_no_northwest_to_southeast
#print axioms trajectory_southeast_of_no_comparable_step
#print axioms trajectory_northwest_of_no_comparable_step
#print axioms southeast_trajectory_tendsto_in_absorbingBox
#print axioms northwest_trajectory_tendsto_in_absorbingBox
#print axioms equilibrium_mem_bistable_catalogue
#print axioms bistability_globalConvergence_of_convergentStep

end

end CivicAlignment.PaperII
