/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.ClippedStep
import CivicAlignment.PaperII.AbsorbingCeiling
import Mathlib.Topology.UnitInterval

/-!
# Paper II: bistability and the basin dichotomy

This file formalizes the elementary fixed-point and Jacobian clauses of
`thm:bistable`.  It also records an exact period-two counterexample to the
global convergence clause: the Smith/Hirsch--Smith result cited by the paper
requires additional orientation and injectivity hypotheses.
-/

namespace CivicAlignment.PaperII

open Filter Function Set Topology

noncomputable section

/-! ## Fixed-point catalogue -/

/-- A Paper II loop equilibrium is an actual fixed point of the simultaneous map. -/
def IsLoopEquilibrium (p : LoopParams) (β D : ℝ) : Prop :=
  p.loopMap (β, D) = (β, D)

/-- The calibrated corner `p₁`. -/
def calibratedPoint (p : LoopParams) : LoopState :=
  (0, p.stationaryStock 0)

/-- The unique interior crossing `p₂`. -/
def saddlePoint (p : LoopParams) (threshold : ThresholdAssumption p) : LoopState :=
  (threshold.βdagger, p.stationaryStock threshold.βdagger)

/-- The captured corner `p₃`. -/
def capturedPoint (p : LoopParams) : LoopState :=
  (1, p.stationaryStock 1)

/-- Projection equals the calibrated endpoint exactly for inputs at or below zero:
`lem:clip`(ii) at the lower face. -/
theorem clipUnit_eq_zero_iff (x : ℝ) : LoopParams.clipUnit x = 0 ↔ x ≤ 0 := by
  simp only [clipUnit_eq_clipTo]
  exact clipTo_eq_lo_iff zero_lt_one x

/-- Projection equals the captured endpoint exactly for inputs at or above one:
`lem:clip`(ii) at the upper face. -/
theorem clipUnit_eq_one_iff (x : ℝ) : LoopParams.clipUnit x = 1 ↔ 1 ≤ x := by
  simp only [clipUnit_eq_clipTo]
  exact clipTo_eq_hi_iff zero_lt_one x

/-- Projection is the identity on its target interval: `lem:clip`(ii), inactive case. -/
theorem clipUnit_eq_self {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    LoopParams.clipUnit x = x :=
  clipUnit_eq_self' hx

/-- An interior output of interval projection has that output as its unique preimage:
the deadzone of `lem:clip`(ii) is confined to the two faces. -/
theorem clipUnit_eq_interior_iff {x β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1) :
    LoopParams.clipUnit x = β ↔ x = β := by
  simp only [clipUnit_eq_clipTo]
  exact clipTo_eq_interior_iff hβ

/-- The stationary-stock denominator is positive throughout the policy interval. -/
theorem one_sub_s_pos {p : LoopParams} (model : DriftModelAssumptions p)
    {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 < 1 - p.s β := by
  have hs := driftStockMultiplier_nonneg_le model hβ
  linarith [model.lambda₀_pos]

/-- The stationary characteristic lies in the paper's invariant stock interval. -/
theorem stationaryStock_mem_stockInterval {p : LoopParams}
    (model : DriftModelAssumptions p) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    p.stationaryStock β ∈ Icc p.I (p.I / p.lambda₀) := by
  have hs := driftStockMultiplier_nonneg_le model hβ
  have hden : 0 < 1 - p.s β := one_sub_s_pos model hβ
  have hden_le_one : 1 - p.s β ≤ 1 := by linarith [hs.1]
  have hlambda_le_den : p.lambda₀ ≤ 1 - p.s β := by linarith [hs.2]
  simp only [LoopParams.stationaryStock, model.no_content_gain, sub_zero]
  constructor
  · exact (le_div_iff₀ hden).2 (by nlinarith [model.I_pos])
  · exact (div_le_div_iff₀ hden model.lambda₀_pos).2 (by
      nlinarith [model.I_pos, hlambda_le_den])

/-- At every admissible fixed policy, the stationary stock is fixed by the stock map. -/
theorem stationaryStock_fixed {p : LoopParams} (model : DriftModelAssumptions p)
    {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    p.stockStep β (p.stationaryStock β) = p.stationaryStock β := by
  have hden : 1 - p.s β ≠ 0 := (one_sub_s_pos model hβ).ne'
  simp only [LoopParams.stockStep, LoopParams.stationaryStock,
    model.no_content_gain, add_zero, sub_zero]
  field_simp [hden]
  ring

/-- Every loop fixed point has its stock on the stationary characteristic. -/
theorem equilibrium_stock_eq_stationary {p : LoopParams}
    (model : DriftModelAssumptions p) {β D : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) (hequilibrium : IsLoopEquilibrium p β D) :
    D = p.stationaryStock β := by
  have hstock := congrArg Prod.snd hequilibrium
  simp only [LoopParams.loopMap, LoopParams.stockStep, model.no_content_gain,
    add_zero] at hstock
  have hden : 1 - p.s β ≠ 0 := (one_sub_s_pos model hβ).ne'
  simp only [LoopParams.stationaryStock, model.no_content_gain, sub_zero]
  apply (eq_div_iff hden).2
  nlinarith

/-- The calibrated corner is a fixed point under the left endpoint sign in (H). -/
theorem calibratedPoint_fixed {p : LoopParams} (model : DriftModelAssumptions p)
    (threshold : ThresholdAssumption p) :
    IsLoopEquilibrium p 0 (p.stationaryStock 0) := by
  have hβ : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hstock := stationaryStock_fixed model hβ
  have hgrad : p.gradU 0 (p.stationaryStock 0) = p.G 0 :=
    (G_eq_gradU_stationary p 0).symm
  have hpolicy : p.deferenceStep 0 (p.stationaryStock 0) = 0 := by
    simp only [LoopParams.deferenceStep, hgrad, zero_add]
    rw [clipUnit_eq_zero_iff]
    exact mul_nonpos_of_nonneg_of_nonpos model.α_pos.le threshold.G_zero_neg.le
  exact Prod.ext hpolicy hstock

/-- The unique transversal crossing gives the interior fixed point. -/
theorem saddlePoint_fixed {p : LoopParams} (model : DriftModelAssumptions p)
    (threshold : ThresholdAssumption p) :
    IsLoopEquilibrium p threshold.βdagger
      (p.stationaryStock threshold.βdagger) := by
  have hβ : threshold.βdagger ∈ Icc (0 : ℝ) 1 :=
    ⟨threshold.βdagger_mem.1.le, threshold.βdagger_mem.2.le⟩
  have hstock := stationaryStock_fixed model hβ
  have hgrad : p.gradU threshold.βdagger
      (p.stationaryStock threshold.βdagger) = 0 := by
    rw [← G_eq_gradU_stationary]
    exact threshold.G_zero
  have hpolicy : p.deferenceStep threshold.βdagger
      (p.stationaryStock threshold.βdagger) = threshold.βdagger := by
    simp only [LoopParams.deferenceStep, hgrad, mul_zero, add_zero]
    exact clipUnit_eq_self hβ
  exact Prod.ext hpolicy hstock

/-- The captured corner is a fixed point under the right endpoint sign in (H). -/
theorem capturedPoint_fixed {p : LoopParams} (model : DriftModelAssumptions p)
    (threshold : ThresholdAssumption p) :
    IsLoopEquilibrium p 1 (p.stationaryStock 1) := by
  have hβ : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  have hstock := stationaryStock_fixed model hβ
  have hgrad : p.gradU 1 (p.stationaryStock 1) = p.G 1 :=
    (G_eq_gradU_stationary p 1).symm
  have hpolicy : p.deferenceStep 1 (p.stationaryStock 1) = 1 := by
    simp only [LoopParams.deferenceStep, hgrad]
    rw [clipUnit_eq_one_iff]
    have hpos := mul_pos model.α_pos threshold.G_one_pos
    linarith
  exact Prod.ext hpolicy hstock

/-- The stationary stock is strictly increasing with policy on `[0,1]`. -/
theorem stationaryStock_strictMonoOn {p : LoopParams}
    (model : DriftModelAssumptions p) :
    StrictMonoOn p.stationaryStock (Icc (0 : ℝ) 1) := by
  intro β₁ hβ₁ β₂ hβ₂ hβ
  have hs := driftStockMultiplier_strictMonoOn model hβ₁ hβ₂ hβ
  have hden₁ : 0 < 1 - p.s β₁ := one_sub_s_pos model hβ₁
  have hden₂ : 0 < 1 - p.s β₂ := one_sub_s_pos model hβ₂
  simp only [LoopParams.stationaryStock, model.no_content_gain, sub_zero]
  exact (div_lt_div_iff₀ hden₁ hden₂).2 (by nlinarith [model.I_pos])

/--
Paper II, Theorem 3.14 (`thm:bistable`), clause (ii), `civic_drift.tex:237`.

Under (H), the loop has exactly the calibrated corner, the unique interior
crossing, and the captured corner as fixed points.
-/
theorem loopEquilibrium_iff_three_points {p : LoopParams}
    (model : DriftModelAssumptions p) (threshold : ThresholdAssumption p)
    (β D : ℝ) :
    IsLoopEquilibrium p β D ↔
      (β = 0 ∧ D = p.stationaryStock 0) ∨
      (β = threshold.βdagger ∧ D = p.stationaryStock threshold.βdagger) ∨
      (β = 1 ∧ D = p.stationaryStock 1) := by
  constructor
  · intro hequilibrium
    have hpolicy := congrArg Prod.fst hequilibrium
    simp only [LoopParams.loopMap] at hpolicy
    have hβ : β ∈ Icc (0 : ℝ) 1 := by
      have hmem := LoopParams.clipUnit_mem
        (β + p.α * p.gradU β D)
      simp only [LoopParams.deferenceStep] at hpolicy
      rwa [hpolicy] at hmem
    have hD := equilibrium_stock_eq_stationary model hβ hequilibrium
    by_cases hzero : β = 0
    · exact Or.inl ⟨hzero, hzero ▸ hD⟩
    by_cases hone : β = 1
    · exact Or.inr (Or.inr ⟨hone, hone ▸ hD⟩)
    have hβint : β ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hβ.1 (Ne.symm hzero), lt_of_le_of_ne hβ.2 hone⟩
    have hinput : β + p.α * p.gradU β D = β := by
      exact (clipUnit_eq_interior_iff hβint).1 (by
        simpa only [LoopParams.deferenceStep] using hpolicy)
    have hgrad : p.gradU β D = 0 := by
      nlinarith [model.α_pos]
    have hG : p.G β = 0 := by
      rw [G_eq_gradU_stationary, ← hD]
      exact hgrad
    have hdagger : β = threshold.βdagger := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hbefore | hafter
      · have := threshold.G_neg_before β hβint hbefore
        linarith
      · have := threshold.G_pos_after β hβint hafter
        linarith
    exact Or.inr (Or.inl ⟨hdagger, hdagger ▸ hD⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact calibratedPoint_fixed model threshold
    · exact saddlePoint_fixed model threshold
    · exact capturedPoint_fixed model threshold

/-- The three fixed points are strictly ordered in both coordinates. -/
theorem bistableFixedPoints_componentwise_order {p : LoopParams}
    (model : DriftModelAssumptions p) (threshold : ThresholdAssumption p) :
    (0 : ℝ) < threshold.βdagger ∧
      p.stationaryStock 0 < p.stationaryStock threshold.βdagger ∧
      threshold.βdagger < 1 ∧
      p.stationaryStock threshold.βdagger < p.stationaryStock 1 := by
  have hzero : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hone : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  have hdagger : threshold.βdagger ∈ Icc (0 : ℝ) 1 :=
    ⟨threshold.βdagger_mem.1.le, threshold.βdagger_mem.2.le⟩
  exact ⟨threshold.βdagger_mem.1,
    stationaryStock_strictMonoOn model hzero hdagger threshold.βdagger_mem.1,
    threshold.βdagger_mem.2,
    stationaryStock_strictMonoOn model hdagger hone threshold.βdagger_mem.2⟩

/-! ## Interior Jacobian -/

/-- The four entries of the unclipped planar Jacobian. -/
structure LoopJacobian where
  a : ℝ
  b : ℝ
  cJ : ℝ
  d : ℝ

namespace LoopJacobian

/-- Trace of a planar Jacobian. -/
def trace (J : LoopJacobian) : ℝ := J.a + J.d

/-- Determinant of a planar Jacobian. -/
def det (J : LoopJacobian) : ℝ := J.a * J.d - J.b * J.cJ

/-- Characteristic polynomial of a planar Jacobian. -/
def charPoly (J : LoopJacobian) (x : ℝ) : ℝ :=
  x ^ 2 - J.trace * x + J.det

/-- The manifestly real discriminant formula for a 2×2 matrix. -/
def discriminant (J : LoopJacobian) : ℝ :=
  (J.a - J.d) ^ 2 + 4 * J.b * J.cJ

/-- The larger explicit root of the characteristic polynomial. -/
def largerEigenvalue (J : LoopJacobian) : ℝ :=
  (J.trace + Real.sqrt J.discriminant) / 2

/-- The smaller explicit root of the characteristic polynomial. -/
def smallerEigenvalue (J : LoopJacobian) : ℝ :=
  (J.trace - Real.sqrt J.discriminant) / 2

/-- Nonnegative off-diagonal entries make the discriminant nonnegative. -/
theorem discriminant_nonneg (J : LoopJacobian) (hb : 0 ≤ J.b) (hcJ : 0 ≤ J.cJ) :
    0 ≤ J.discriminant := by
  simp only [discriminant]
  positivity

/-- The explicit larger root zeros the characteristic polynomial. -/
theorem charPoly_largerEigenvalue_eq_zero (J : LoopJacobian)
    (hdisc : 0 ≤ J.discriminant) :
    J.charPoly J.largerEigenvalue = 0 := by
  have hsqrt := Real.sq_sqrt hdisc
  simp only [charPoly, largerEigenvalue, trace, det, discriminant] at hsqrt ⊢
  nlinarith

/-- The explicit smaller root zeros the characteristic polynomial. -/
theorem charPoly_smallerEigenvalue_eq_zero (J : LoopJacobian)
    (hdisc : 0 ≤ J.discriminant) :
    J.charPoly J.smallerEigenvalue = 0 := by
  have hsqrt := Real.sq_sqrt hdisc
  simp only [charPoly, smallerEigenvalue, trace, det, discriminant] at hsqrt ⊢
  nlinarith

/-- The characteristic polynomial factors through the two explicit roots. -/
theorem charPoly_eq_mul_eigenvalues (J : LoopJacobian)
    (hdisc : 0 ≤ J.discriminant) (x : ℝ) :
    J.charPoly x = (x - J.largerEigenvalue) * (x - J.smallerEigenvalue) := by
  have hsqrt := Real.sq_sqrt hdisc
  simp only [charPoly, largerEigenvalue, smallerEigenvalue, trace, det,
    discriminant] at hsqrt ⊢
  nlinarith

/-- The root carrying the plus sign is at least the root carrying the minus sign. -/
theorem smallerEigenvalue_le_largerEigenvalue (J : LoopJacobian) :
    J.smallerEigenvalue ≤ J.largerEigenvalue := by
  simp only [smallerEigenvalue, largerEigenvalue]
  linarith [Real.sqrt_nonneg J.discriminant]

/-- If `d<1` and the off-diagonal product is nonnegative, the smaller root is below one. -/
theorem smallerEigenvalue_lt_one (J : LoopJacobian) (hd : J.d < 1)
    (hbc : 0 ≤ J.b * J.cJ) :
    J.smallerEigenvalue < 1 := by
  have hsq : (J.a - J.d) ^ 2 ≤ J.discriminant := by
    simp only [discriminant]
    nlinarith
  have hsqrt : |J.a - J.d| ≤ Real.sqrt J.discriminant := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  have hdiff : J.a - J.d ≤ Real.sqrt J.discriminant :=
    (le_abs_self _).trans hsqrt
  simp only [smallerEigenvalue, trace]
  linarith

/-- With the smaller root below one, `p(1)<0` exactly when the larger root exceeds one. -/
theorem largerEigenvalue_gt_one_iff_charPoly_one_neg (J : LoopJacobian)
    (hdisc : 0 ≤ J.discriminant) (hsmall : J.smallerEigenvalue < 1) :
    1 < J.largerEigenvalue ↔ J.charPoly 1 < 0 := by
  rw [J.charPoly_eq_mul_eigenvalues hdisc]
  have hfactor : 0 < 1 - J.smallerEigenvalue := sub_pos.mpr hsmall
  constructor
  · intro hlarge
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hlarge) hfactor
  · intro hproduct
    have hleft : 1 - J.largerEigenvalue < 0 := by
      by_contra hnot
      exact (not_lt_of_ge (mul_nonneg (not_lt.mp hnot) hfactor.le)) hproduct
    exact sub_neg.mp hleft

/-- At `-1`, the characteristic polynomial has the paper's factored form. -/
theorem charPoly_neg_one_eq (J : LoopJacobian) :
    J.charPoly (-1) = (1 + J.a) * (1 + J.d) - J.b * J.cJ := by
  simp only [charPoly, trace, det]
  ring

/-- Nonnegative diagonal entries make the larger explicit root nonnegative. -/
theorem largerEigenvalue_nonneg (J : LoopJacobian) (ha : 0 ≤ J.a) (hd : 0 ≤ J.d) :
    0 ≤ J.largerEigenvalue := by
  simp only [largerEigenvalue, trace]
  positivity

/-- A positive value of `p(-1)` places the smaller root strictly above `-1`. -/
theorem smallerEigenvalue_gt_neg_one_of_charPoly_neg_one_pos (J : LoopJacobian)
    (hdisc : 0 ≤ J.discriminant) (hlarge : 0 ≤ J.largerEigenvalue)
    (hpoly : 0 < J.charPoly (-1)) :
    -1 < J.smallerEigenvalue := by
  have hfactor := J.charPoly_eq_mul_eigenvalues hdisc (-1)
  have hproduct : 0 < (1 + J.largerEigenvalue) * (1 + J.smallerEigenvalue) := by
    rw [hfactor] at hpoly
    nlinarith
  have hleft : 0 < 1 + J.largerEigenvalue := by linarith
  by_contra hnot
  have hnonpos : 1 + J.smallerEigenvalue ≤ 0 := by linarith
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hleft.le hnonpos)) hproduct

end LoopJacobian

/-- The unclipped Jacobian at a policy--stock state. -/
def interiorLoopJacobian (p : LoopParams) (β D : ℝ) : LoopJacobian where
  a := 1 - 2 * p.α * p.c ^ 2 * D
  b := 2 * p.α * p.c * (1 - p.c * β)
  cJ := p.sSlope β * D
  d := p.s β

/-- The stock multiplier's derivative is positive at every interior policy. -/
theorem sSlope_pos {p : LoopParams} (model : DriftModelAssumptions p)
    {β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1) :
    0 < p.sSlope β := by
  have hresidual : 1 - β < 1 := by linarith [hβ.1]
  have hproduct : p.η * (1 - β) < 1 := calc
    p.η * (1 - β) < p.η * 1 :=
      mul_lt_mul_of_pos_left hresidual model.η_pos
    _ = p.η := mul_one p.η
    _ ≤ 1 := model.η_le_one
  have hinner : 0 < 1 - p.η * (1 - β) := sub_pos.mpr hproduct
  simp only [LoopParams.sSlope]
  exact mul_pos
    (mul_pos (mul_pos two_pos model.η_pos) (sub_pos.mpr model.lambda₀_lt_one)) hinner

/-- On the policy interval, `s'(β) ≤ 2η`. -/
theorem sSlope_le_two_eta {p : LoopParams} (model : DriftModelAssumptions p)
    {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    p.sSlope β ≤ 2 * p.η := by
  have hresidual_nonneg : 0 ≤ 1 - β := sub_nonneg.mpr hβ.2
  have hresidual_le_one : 1 - β ≤ 1 := by linarith [hβ.1]
  have hηresidual_nonneg : 0 ≤ p.η * (1 - β) :=
    mul_nonneg model.η_pos.le hresidual_nonneg
  have hηresidual_le_one : p.η * (1 - β) ≤ 1 := calc
    p.η * (1 - β) ≤ p.η * 1 :=
      mul_le_mul_of_nonneg_left hresidual_le_one model.η_pos.le
    _ = p.η := mul_one p.η
    _ ≤ 1 := model.η_le_one
  have hinner_nonneg : 0 ≤ 1 - p.η * (1 - β) :=
    sub_nonneg.mpr hηresidual_le_one
  have hinner_le_one : 1 - p.η * (1 - β) ≤ 1 := by linarith
  have hground_nonneg : 0 ≤ 1 - p.lambda₀ := by linarith [model.lambda₀_lt_one]
  have hground_le_one : 1 - p.lambda₀ ≤ 1 := by linarith [model.lambda₀_pos]
  have hproduct :
      (1 - p.lambda₀) * (1 - p.η * (1 - β)) ≤ 1 := by
    have := mul_le_mul hground_le_one hinner_le_one hinner_nonneg zero_le_one
    simpa only [one_mul] using this
  rw [LoopParams.sSlope]
  calc
    2 * p.η * (1 - p.lambda₀) * (1 - p.η * (1 - β)) =
        (2 * p.η) * ((1 - p.lambda₀) * (1 - p.η * (1 - β))) := by ring
    _ ≤ (2 * p.η) * 1 :=
      mul_le_mul_of_nonneg_left hproduct (mul_nonneg (by norm_num) model.η_pos.le)
    _ = 2 * p.η := mul_one _

/-- At the interior crossing all four Jacobian entries are nonnegative, with
strict off-diagonals. -/
theorem saddleJacobian_entry_bounds {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : StrictSmallStepAssumption p)
    (threshold : ThresholdAssumption p) :
    let J := interiorLoopJacobian p threshold.βdagger
      (p.stationaryStock threshold.βdagger)
    0 ≤ J.a ∧ J.a ≤ 1 ∧ 0 < J.b ∧ 0 < J.cJ ∧ 0 ≤ J.d ∧ J.d < 1 := by
  let β := threshold.βdagger
  let D := p.stationaryStock β
  have hβint : β ∈ Ioo (0 : ℝ) 1 := threshold.βdagger_mem
  have hβ : β ∈ Icc (0 : ℝ) 1 := ⟨hβint.1.le, hβint.2.le⟩
  have hD := stationaryStock_mem_stockInterval model hβ
  have hDpos : 0 < D := model.I_pos.trans_le hD.1
  have hDceiling : D ≤ monotonicityCeiling p :=
    hD.2.trans (stockCeiling_lt_monotonicityCeiling model ss).le
  have ha₀ : 0 ≤ 1 - 2 * p.α * p.c ^ 2 * D :=
    monotonicity_coefficient_nonneg model hDceiling
  have ha₁ : 1 - 2 * p.α * p.c ^ 2 * D ≤ 1 := by
    have : 0 ≤ 2 * p.α * p.c ^ 2 * D :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) (sq_nonneg p.c)) hDpos.le
    linarith
  have hcβ : p.c * β < 1 := calc
    p.c * β ≤ p.c * 1 := mul_le_mul_of_nonneg_left hβ.2 model.c_pos.le
    _ = p.c := mul_one p.c
    _ < 1 := model.c_lt_one
  have hb : 0 < 2 * p.α * p.c * (1 - p.c * β) :=
    mul_pos (mul_pos (mul_pos two_pos model.α_pos) model.c_pos) (sub_pos.mpr hcβ)
  have hcJ : 0 < p.sSlope β * D := mul_pos (sSlope_pos model hβint) hDpos
  have hs := driftStockMultiplier_nonneg_le model hβ
  dsimp only [interiorLoopJacobian]
  exact ⟨ha₀, ha₁, hb, hcJ, hs.1, lt_of_le_of_lt hs.2 (by linarith [model.lambda₀_pos])⟩

/-- The explicit characteristic polynomial agrees with the shared `eq:p1` quantity at one. -/
theorem saddleJacobian_charPoly_one_eq {p : LoopParams}
    (model : DriftModelAssumptions p) (threshold : ThresholdAssumption p) :
    let D := p.stationaryStock threshold.βdagger
    (interiorLoopJacobian p threshold.βdagger D).charPoly 1 =
      p.jacobianPAtOne threshold.βdagger D := by
  simp only [LoopJacobian.charPoly, LoopJacobian.trace, LoopJacobian.det,
    interiorLoopJacobian, LoopParams.jacobianPAtOne, model.no_content_gain, add_zero]
  ring

/-- The off-diagonal product at the saddle is bounded by the paper's `2η/c` estimate. -/
theorem saddleJacobian_offDiagonalProduct_lt {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : StrictSmallStepAssumption p)
    (threshold : ThresholdAssumption p) :
    let J := interiorLoopJacobian p threshold.βdagger
      (p.stationaryStock threshold.βdagger)
    J.b * J.cJ < 2 * p.η / p.c := by
  let β := threshold.βdagger
  let D := p.stationaryStock β
  let J := interiorLoopJacobian p β D
  have hβint : β ∈ Ioo (0 : ℝ) 1 := threshold.βdagger_mem
  have hβ : β ∈ Icc (0 : ℝ) 1 := ⟨hβint.1.le, hβint.2.le⟩
  have hD := stationaryStock_mem_stockInterval model hβ
  have hDpos : 0 < D := model.I_pos.trans_le hD.1
  have hentries := saddleJacobian_entry_bounds model ss threshold
  change J.b * J.cJ < 2 * p.η / p.c
  have hcβ_nonneg : 0 ≤ p.c * β := mul_nonneg model.c_pos.le hβ.1
  have hresidual_le : 1 - p.c * β ≤ 1 := by linarith
  have hcontroller_nonneg : 0 ≤ 2 * p.α * p.c :=
    mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) model.c_pos.le
  have hb : J.b ≤ 2 * p.α * p.c := by
    change 2 * p.α * p.c * (1 - p.c * β) ≤ 2 * p.α * p.c
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hresidual_le hcontroller_nonneg
  have hslope : p.sSlope β ≤ 2 * p.η := sSlope_le_two_eta model hβ
  have hcJ : J.cJ ≤ (2 * p.η) * (p.I / p.lambda₀) := by
    change p.sSlope β * D ≤ (2 * p.η) * (p.I / p.lambda₀)
    exact mul_le_mul hslope hD.2 hDpos.le
      (mul_nonneg (by norm_num) model.η_pos.le)
  have hproduct : J.b * J.cJ ≤
      (2 * p.α * p.c) * ((2 * p.η) * (p.I / p.lambda₀)) :=
    mul_le_mul hb hcJ hentries.2.2.2.1.le hcontroller_nonneg
  have hratio : 2 * p.α * p.c ^ 2 * p.I / p.lambda₀ < 1 := by
    exact (div_lt_iff₀ model.lambda₀_pos).2 (by simpa only [one_mul] using ss.bound)
  have hmultiplier : 0 < 2 * p.η / p.c := div_pos (mul_pos two_pos model.η_pos) model.c_pos
  have hstrict :
      (2 * p.α * p.c) * ((2 * p.η) * (p.I / p.lambda₀)) < 2 * p.η / p.c := by
    calc
      (2 * p.α * p.c) * ((2 * p.η) * (p.I / p.lambda₀)) =
          (2 * p.η / p.c) * (2 * p.α * p.c ^ 2 * p.I / p.lambda₀) := by
            field_simp [model.c_pos.ne', model.lambda₀_pos.ne']
      _ < (2 * p.η / p.c) * 1 := mul_lt_mul_of_pos_left hratio hmultiplier
      _ = 2 * p.η / p.c := mul_one _
  exact hproduct.trans_lt hstrict

/--
Paper II, Theorem 3.14 (`thm:bistable`), analytic heart of clause (iii),
`civic_drift.tex:264--273`.

The larger real Jacobian root exceeds one exactly when the stationary gradient
crosses upward. This is the hand-proved 2×2 result; it uses no Perron--Frobenius
import.
-/
theorem saddle_largerEigenvalue_gt_one_iff_GSlope_pos {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : StrictSmallStepAssumption p)
    (threshold : ThresholdAssumption p) :
    let J := interiorLoopJacobian p threshold.βdagger
      (p.stationaryStock threshold.βdagger)
    1 < J.largerEigenvalue ↔ 0 < p.GSlope threshold.βdagger := by
  let β := threshold.βdagger
  let D := p.stationaryStock β
  let J := interiorLoopJacobian p β D
  have hentries := saddleJacobian_entry_bounds model ss threshold
  change 1 < J.largerEigenvalue ↔ 0 < p.GSlope β
  have hdisc : 0 ≤ J.discriminant :=
    J.discriminant_nonneg hentries.2.2.1.le hentries.2.2.2.1.le
  have hsmall : J.smallerEigenvalue < 1 :=
    J.smallerEigenvalue_lt_one hentries.2.2.2.2.2
      (mul_nonneg hentries.2.2.1.le hentries.2.2.2.1.le)
  rw [J.largerEigenvalue_gt_one_iff_charPoly_one_neg hdisc hsmall]
  rw [saddleJacobian_charPoly_one_eq model threshold]
  have hβ : β ∈ Icc (0 : ℝ) 1 :=
    ⟨threshold.βdagger_mem.1.le, threshold.βdagger_mem.2.le⟩
  have hDpos : 0 < D :=
    model.I_pos.trans_le (stationaryStock_mem_stockInterval model hβ).1
  have hwall : 1 - p.s β - p.g ≠ 0 := by
    rw [model.no_content_gain, sub_zero]
    exact (one_sub_s_pos model hβ).ne'
  rw [p.jacobianPAtOne_eq_neg_GSlope β D model.I_pos.ne' hwall]
  have hsquare : 0 < (1 - p.s β - p.g) ^ 2 := sq_pos_of_ne_zero hwall
  have hscale : 0 < p.α * D * (1 - p.s β - p.g) ^ 2 / p.I :=
    div_pos (mul_pos (mul_pos model.α_pos hDpos) hsquare) model.I_pos
  constructor
  · intro hproduct
    by_contra hslope
    have hnonneg : 0 ≤
        -(p.α * D * (1 - p.s β - p.g) ^ 2 / p.I) * p.GSlope β :=
      mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hscale.le) (not_lt.mp hslope)
    exact (not_lt_of_ge hnonneg) hproduct
  · intro hslope
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hscale) hslope

/-- The second real Jacobian root is always below one at the interior crossing. -/
theorem saddle_smallerEigenvalue_lt_one {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : StrictSmallStepAssumption p)
    (threshold : ThresholdAssumption p) :
    let J := interiorLoopJacobian p threshold.βdagger
      (p.stationaryStock threshold.βdagger)
    J.smallerEigenvalue < 1 := by
  have hentries := saddleJacobian_entry_bounds model ss threshold
  exact LoopJacobian.smallerEigenvalue_lt_one _ hentries.2.2.2.2.2
    (mul_nonneg hentries.2.2.1.le hentries.2.2.2.1.le)

/--
Paper II, Theorem 3.14 (`thm:bistable`), final inequality in clause (iii),
`civic_drift.tex:237--288`.

The paper's primitive sufficient condition places the second real Jacobian
root strictly above `-1`.
-/
theorem saddle_smallerEigenvalue_gt_neg_one {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : StrictSmallStepAssumption p)
    (threshold : ThresholdAssumption p)
    (hlower : 2 * p.η ≤ p.c * (1 + p.s 0)) :
    let J := interiorLoopJacobian p threshold.βdagger
      (p.stationaryStock threshold.βdagger)
    (-1 : ℝ) < J.smallerEigenvalue := by
  let β := threshold.βdagger
  let D := p.stationaryStock β
  let J := interiorLoopJacobian p β D
  have hentries := saddleJacobian_entry_bounds model ss threshold
  have hdisc : 0 ≤ J.discriminant :=
    J.discriminant_nonneg hentries.2.2.1.le hentries.2.2.2.1.le
  have hlarge : 0 ≤ J.largerEigenvalue :=
    J.largerEigenvalue_nonneg hentries.1 hentries.2.2.2.2.1
  have hbc := saddleJacobian_offDiagonalProduct_lt model ss threshold
  have hsorder : p.s 0 < p.s β := by
    exact driftStockMultiplier_strictMonoOn model (by norm_num)
      ⟨threshold.βdagger_mem.1.le, threshold.βdagger_mem.2.le⟩
      threshold.βdagger_mem.1
  have hratio : 2 * p.η / p.c ≤ 1 + p.s 0 := by
    rw [div_le_iff₀ model.c_pos]
    nlinarith
  have hleft : 1 + p.s 0 ≤ (1 + J.a) * (1 + J.d) := by
    change 1 + p.s 0 ≤ (1 + J.a) * (1 + p.s β)
    have hsnonneg : 0 ≤ p.s β :=
      (driftStockMultiplier_nonneg_le model
        ⟨threshold.βdagger_mem.1.le, threshold.βdagger_mem.2.le⟩).1
    have hfactor : 0 ≤ 1 + p.s β := by
      linarith
    have hmul : 1 * (1 + p.s β) ≤ (1 + J.a) * (1 + p.s β) :=
      mul_le_mul_of_nonneg_right (by linarith [hentries.1]) hfactor
    linarith
  have hpoly : 0 < J.charPoly (-1) := by
    rw [J.charPoly_neg_one_eq]
    nlinarith [hbc, hratio, hleft]
  exact J.smallerEigenvalue_gt_neg_one_of_charPoly_neg_one_pos hdisc hlarge hpoly

/-! ## Exact counterexample to global convergence -/

/-- Exact rational parameters for a nontrivial period-two orbit satisfying (SS) and (H). -/
def bistabilityCycleParams : LoopParams where
  η := 1 / 2
  lambda₀ := 3 / 4
  I := 1 / 20
  v := 75137 / 5391360
  c := 1 / 8
  α := 1198080 / 2651
  g := 0

/-- The exact lower-policy state of the period-two orbit. -/
def bistabilityCycleLower : LoopState :=
  (7 / 11, 11737 / 189540)

/-- The exact higher-policy state of the period-two orbit. -/
def bistabilityCycleUpper : LoopState :=
  (7 / 9, 113 / 1872)

/-- The rational counterexample satisfies all primitive Paper II restrictions. -/
theorem bistabilityCycle_model : DriftModelAssumptions bistabilityCycleParams := by
  constructor <;> norm_num [bistabilityCycleParams]

/-- The rational counterexample satisfies the strict form of (SS). -/
theorem bistabilityCycle_strictSmallStep :
    StrictSmallStepAssumption bistabilityCycleParams := by
  constructor
  norm_num [bistabilityCycleParams]

/-- A factored form of the stationary gradient on the policy interval. -/
theorem bistabilityCycle_G_factor {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    bistabilityCycleParams.G β =
      (75137 / 5391360 : ℝ) * (β - 161 / 227) * (β + 303 / 331) /
        ((3 - β) * (5 + β)) := by
  have hthree : 3 - β ≠ 0 := by nlinarith [hβ.2]
  have hfive : 5 + β ≠ 0 := by nlinarith [hβ.1]
  change
    -(75137 / 5391360 : ℝ) +
        2 * (1 / 8 : ℝ) * (1 - (1 / 8 : ℝ) * β) * (1 / 20 : ℝ) /
          (1 - (1 - (3 / 4 : ℝ)) *
            (1 - (1 / 2 : ℝ) * (1 - β)) ^ 2 - 0) = _
  rw [show 1 - (1 - (3 / 4 : ℝ)) *
      (1 - (1 / 2 : ℝ) * (1 - β)) ^ 2 - 0 =
        ((3 - β) * (5 + β)) / 16 by ring]
  field_simp [hthree, hfive]
  ring

/-- The exact rational parameters satisfy the full threshold assumption (H). -/
def bistabilityCycleThreshold : ThresholdAssumption bistabilityCycleParams where
  βdagger := 161 / 227
  βdagger_mem := by norm_num
  G_zero := by
    norm_num [LoopParams.G, LoopParams.s, bistabilityCycleParams]
  G_zero_neg := by
    norm_num [LoopParams.G, LoopParams.s, bistabilityCycleParams]
  G_one_pos := by
    norm_num [LoopParams.G, LoopParams.s, bistabilityCycleParams]
  G_neg_before := by
    intro β hβ hbefore
    rw [bistabilityCycle_G_factor ⟨hβ.1.le, hβ.2.le⟩]
    have hv : (0 : ℝ) < 75137 / 5391360 := by norm_num
    have hroot : β - 161 / 227 < 0 := by linarith
    have hother : 0 < β + 303 / 331 := by nlinarith [hβ.1]
    have hden : 0 < (3 - β) * (5 + β) :=
      mul_pos (by nlinarith [hβ.2]) (by nlinarith [hβ.1])
    exact div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hv hroot) hother) hden
  G_pos_after := by
    intro β hβ hafter
    rw [bistabilityCycle_G_factor ⟨hβ.1.le, hβ.2.le⟩]
    have hv : (0 : ℝ) < 75137 / 5391360 := by norm_num
    have hroot : 0 < β - 161 / 227 := by linarith
    have hother : 0 < β + 303 / 331 := by nlinarith [hβ.1]
    have hden : 0 < (3 - β) * (5 + β) :=
      mul_pos (by nlinarith [hβ.2]) (by nlinarith [hβ.1])
    exact div_pos (mul_pos (mul_pos hv hroot) hother) hden
  GSlope_pos := by
    norm_num [LoopParams.GSlope, LoopParams.s, LoopParams.sSlope,
      bistabilityCycleParams]

/-- The first exact state maps to the second without activating projection. -/
theorem bistabilityCycle_lower_step :
    bistabilityCycleParams.loopMap bistabilityCycleLower = bistabilityCycleUpper := by
  apply Prod.ext
  · norm_num [LoopParams.loopMap, LoopParams.deferenceStep, LoopParams.gradU,
      bistabilityCycleParams, bistabilityCycleLower, bistabilityCycleUpper]
    exact clipUnit_eq_self (by norm_num)
  · norm_num [LoopParams.loopMap, LoopParams.stockStep, LoopParams.s,
      bistabilityCycleParams, bistabilityCycleLower, bistabilityCycleUpper]

/-- The second exact state maps back to the first without activating projection. -/
theorem bistabilityCycle_upper_step :
    bistabilityCycleParams.loopMap bistabilityCycleUpper = bistabilityCycleLower := by
  apply Prod.ext
  · norm_num [LoopParams.loopMap, LoopParams.deferenceStep, LoopParams.gradU,
      bistabilityCycleParams, bistabilityCycleLower, bistabilityCycleUpper]
    exact clipUnit_eq_self (by norm_num)
  · norm_num [LoopParams.loopMap, LoopParams.stockStep, LoopParams.s,
      bistabilityCycleParams, bistabilityCycleLower, bistabilityCycleUpper]

/-- The alternating exact trajectory generated by the two-cycle. -/
def bistabilityCycleTrajectory (n : ℕ) : LoopState :=
  if n % 2 = 0 then bistabilityCycleLower else bistabilityCycleUpper

/-- Even terms of the counterexample trajectory are the lower-policy state. -/
theorem bistabilityCycleTrajectory_even (n : ℕ) :
    bistabilityCycleTrajectory (2 * n) = bistabilityCycleLower := by
  simp [bistabilityCycleTrajectory]

/-- Odd terms of the counterexample trajectory are the higher-policy state. -/
theorem bistabilityCycleTrajectory_odd (n : ℕ) :
    bistabilityCycleTrajectory (2 * n + 1) = bistabilityCycleUpper := by
  simp [bistabilityCycleTrajectory]

/-- The alternating sequence is a genuine trajectory of the simultaneous loop map. -/
theorem bistabilityCycle_isTrajectory :
    IsLoopTrajectory bistabilityCycleParams bistabilityCycleTrajectory := by
  intro n
  have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hmod with hzero | hone
  · have hsucc : (n + 1) % 2 = 1 := by omega
    rw [show bistabilityCycleTrajectory (n + 1) = bistabilityCycleUpper by
      simp [bistabilityCycleTrajectory, hsucc]]
    rw [show bistabilityCycleTrajectory n = bistabilityCycleLower by
      simp [bistabilityCycleTrajectory, hzero]]
    exact bistabilityCycle_lower_step.symm
  · have hsucc : (n + 1) % 2 = 0 := by omega
    rw [show bistabilityCycleTrajectory (n + 1) = bistabilityCycleLower by
      simp [bistabilityCycleTrajectory, hsucc]]
    rw [show bistabilityCycleTrajectory n = bistabilityCycleUpper by
      simp [bistabilityCycleTrajectory, hone]]
    exact bistabilityCycle_upper_step.symm

/-- Every point of the exact two-cycle lies inside the paper's original invariant box. -/
theorem bistabilityCycle_mem_absorbingBox (n : ℕ) :
    bistabilityCycleTrajectory n ∈ absorbingBox bistabilityCycleParams := by
  have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hmod with hzero | hone
  · simp [bistabilityCycleTrajectory, hzero, absorbingBox, bistabilityCycleParams,
      bistabilityCycleLower]
    norm_num
  · simp [bistabilityCycleTrajectory, hone, absorbingBox, bistabilityCycleParams,
      bistabilityCycleUpper]
    norm_num

/-- Epsilon--`N` convergence of the policy coordinate of a state trajectory. -/
def PolicyCoordinateConverges (x : ℕ → LoopState) : Prop :=
  ∃ limit : ℝ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → |(x n).1 - limit| < ε

/-- The policy coordinate of the exact two-cycle does not converge. -/
theorem bistabilityCycle_policy_not_convergent :
    ¬PolicyCoordinateConverges bistabilityCycleTrajectory := by
  rintro ⟨limit, hlimit⟩
  obtain ⟨N, hN⟩ := hlimit (1 / 20) (by norm_num)
  have heven := hN (2 * N) (by omega)
  have hodd := hN (2 * N + 1) (by omega)
  rw [bistabilityCycleTrajectory_even] at heven
  rw [bistabilityCycleTrajectory_odd] at hodd
  simp only [bistabilityCycleLower, bistabilityCycleUpper] at heven hodd
  have heven' := abs_lt.mp heven
  have hodd' := abs_lt.mp hodd
  norm_num at heven' hodd'
  linarith

/--
Paper II, Theorem 3.14 (`thm:bistable`), counterexample to clause (i),
`civic_drift.tex:237--295`.

The primitive assumptions, strict (SS), and the full unique-crossing assumption
(H) all hold, yet this trajectory is a nontrivial period-two orbit inside `B`.
Hence not every trajectory converges to a fixed point.  Clause (iv)'s stronger
global basin conclusion is separately unsupported by its cited source; this
particular witness is not claimed to satisfy that clause's saddle premise.
-/
theorem bistability_global_convergence_counterexample :
    IsLoopTrajectory bistabilityCycleParams bistabilityCycleTrajectory ∧
      (∀ n, bistabilityCycleTrajectory n ∈ absorbingBox bistabilityCycleParams) ∧
      ¬PolicyCoordinateConverges bistabilityCycleTrajectory :=
  ⟨bistabilityCycle_isTrajectory, bistabilityCycle_mem_absorbingBox,
    bistabilityCycle_policy_not_convergent⟩

#print axioms clipUnit_eq_zero_iff
#print axioms clipUnit_eq_one_iff
#print axioms clipUnit_eq_self
#print axioms clipUnit_eq_interior_iff
#print axioms one_sub_s_pos
#print axioms stationaryStock_mem_stockInterval
#print axioms stationaryStock_fixed
#print axioms equilibrium_stock_eq_stationary
#print axioms calibratedPoint_fixed
#print axioms saddlePoint_fixed
#print axioms capturedPoint_fixed
#print axioms stationaryStock_strictMonoOn
#print axioms loopEquilibrium_iff_three_points
#print axioms bistableFixedPoints_componentwise_order
#print axioms LoopJacobian.discriminant_nonneg
#print axioms LoopJacobian.charPoly_largerEigenvalue_eq_zero
#print axioms LoopJacobian.charPoly_smallerEigenvalue_eq_zero
#print axioms LoopJacobian.charPoly_eq_mul_eigenvalues
#print axioms LoopJacobian.smallerEigenvalue_le_largerEigenvalue
#print axioms LoopJacobian.smallerEigenvalue_lt_one
#print axioms LoopJacobian.largerEigenvalue_gt_one_iff_charPoly_one_neg
#print axioms LoopJacobian.charPoly_neg_one_eq
#print axioms LoopJacobian.largerEigenvalue_nonneg
#print axioms LoopJacobian.smallerEigenvalue_gt_neg_one_of_charPoly_neg_one_pos
#print axioms sSlope_pos
#print axioms sSlope_le_two_eta
#print axioms saddleJacobian_entry_bounds
#print axioms saddleJacobian_charPoly_one_eq
#print axioms saddleJacobian_offDiagonalProduct_lt
#print axioms saddle_largerEigenvalue_gt_one_iff_GSlope_pos
#print axioms saddle_smallerEigenvalue_lt_one
#print axioms saddle_smallerEigenvalue_gt_neg_one
#print axioms bistabilityCycle_model
#print axioms bistabilityCycle_strictSmallStep
#print axioms bistabilityCycle_G_factor
#print axioms bistabilityCycle_lower_step
#print axioms bistabilityCycle_upper_step
#print axioms bistabilityCycleTrajectory_even
#print axioms bistabilityCycleTrajectory_odd
#print axioms bistabilityCycle_isTrajectory
#print axioms bistabilityCycle_mem_absorbingBox
#print axioms bistabilityCycle_policy_not_convergent
#print axioms bistability_global_convergence_counterexample

end

end CivicAlignment.PaperII
