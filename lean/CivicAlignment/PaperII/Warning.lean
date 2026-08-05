/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.BistabilityTheorem
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Paper II: early warning at the quadratic-cost capture fold

This file treats the quadratic usefulness cost from `prop:warning`.  The
stationary fixed-point equation can be parameterized exactly by policy:

`I = v β (1 - s β) / (2 c (1 - c β))`.

That injection curve, rather than pointwise parameter monotonicity alone, is
what makes the claimed saddle-node conclusion valid for this model.  Its
derivative has a strictly decreasing numerator, so an interior critical point
is the unique, nondegenerate maximum.  The full simultaneous-map Jacobian is
then used for the eigenvalue-one and square-root clauses.
-/

namespace CivicAlignment.PaperII

open Asymptotics Filter Set Topology

noncomputable section

/-! ## The stationary quadratic-cost family -/

/-- Paper II, `prop:warning`: stationary stock when injection `I` is varied. -/
def warningStationaryStock (p : LoopParams) (I β : ℝ) : ℝ :=
  I / (1 - p.s β)

/--
Paper II, `prop:warning`: the scalar stationary policy map `φ(β; I)`, in its
denominator-cleared form.
-/
def warningPhi (p : LoopParams) (I β : ℝ) : ℝ :=
  2 * p.c * I / (p.v * (1 - p.s β) + 2 * p.c ^ 2 * I)

/-- The injection rate whose quadratic-cost stationary policy is `β`. -/
def warningInjectionCurve (p : LoopParams) (β : ℝ) : ℝ :=
  p.v * β * (1 - p.s β) / (2 * p.c * (1 - p.c * β))

/-- Numerator controlling the derivative of `warningInjectionCurve`. -/
def warningFoldNumerator (p : LoopParams) (β : ℝ) : ℝ :=
  1 - p.s β - β * (1 - p.c * β) * p.sSlope β

/-- Algebraic derivative of the injection curve away from `1-cβ=0`. -/
def warningInjectionSlope (p : LoopParams) (β : ℝ) : ℝ :=
  p.v * warningFoldNumerator p β / (2 * p.c * (1 - p.c * β) ^ 2)

/-- The constant second derivative of the quadratic stock multiplier. -/
def warningStockCurvature (p : LoopParams) : ℝ :=
  2 * p.η ^ 2 * (1 - p.lambda₀)

/-- A fold is an interior zero of the injection-curve derivative numerator. -/
structure WarningFold (p : LoopParams) where
  βfold : ℝ
  βfold_mem : βfold ∈ Ioo (0 : ℝ) 1
  critical : warningFoldNumerator p βfold = 0

/-- The denominator-cleared `warningPhi` is exactly the paper's stock form. -/
theorem warningPhi_eq_stockForm {p : LoopParams} {I β : ℝ}
    (hstockDen : 1 - p.s β ≠ 0) :
    warningPhi p I β =
      2 * p.c * warningStationaryStock p I β /
        (p.v + 2 * p.c ^ 2 * warningStationaryStock p I β) := by
  simp only [warningPhi, warningStationaryStock]
  field_simp [hstockDen]

/-- The stationary stock denominator stays positive on the policy interval. -/
theorem warningStockDenominator_pos {p : LoopParams}
    (model : DriftModelAssumptions p) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 < 1 - p.s β :=
  one_sub_s_pos model hβ

/-- The policy-map denominator is positive for every positive injection. -/
theorem warningPhiDenominator_pos {p : LoopParams}
    (model : DriftModelAssumptions p) {I β : ℝ} (hI : 0 < I)
    (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 < p.v * (1 - p.s β) + 2 * p.c ^ 2 * I := by
  have hstock := warningStockDenominator_pos model hβ
  have hfirst : 0 < p.v * (1 - p.s β) := mul_pos model.v_pos hstock
  have hcSq : 0 < p.c ^ 2 := sq_pos_of_pos model.c_pos
  have hsecond : 0 < 2 * p.c ^ 2 * I :=
    mul_pos (mul_pos two_pos hcSq) hI
  linarith

/-- `φ(β; I)` is pointwise strictly increasing in the injection rate `I`. -/
theorem warningPhi_strictMonoOn_injection {p : LoopParams}
    (model : DriftModelAssumptions p) (β : ℝ) (hβ : β ∈ Icc (0 : ℝ) 1) :
    StrictMonoOn (fun I : ℝ => warningPhi p I β) (Ioi 0) := by
  intro I₁ hI₁ I₂ hI₂ hI
  have hq : 0 < 1 - p.s β := warningStockDenominator_pos model hβ
  have hden₁ := warningPhiDenominator_pos model hI₁ hβ
  have hden₂ := warningPhiDenominator_pos model hI₂ hβ
  change 2 * p.c * I₁ / (p.v * (1 - p.s β) + 2 * p.c ^ 2 * I₁) <
    2 * p.c * I₂ / (p.v * (1 - p.s β) + 2 * p.c ^ 2 * I₂)
  rw [div_lt_div_iff₀ hden₁ hden₂]
  have hpositive :
      0 < 2 * p.c * p.v * (1 - p.s β) * (I₂ - I₁) := by
    exact mul_pos
      (mul_pos (mul_pos (mul_pos two_pos model.c_pos) model.v_pos) hq)
      (sub_pos.mpr hI)
  nlinarith

/-- Interior fixed policies are exactly points on the injection curve. -/
theorem warningPhi_eq_self_iff {p : LoopParams}
    (model : DriftModelAssumptions p) {I β : ℝ} (hI : 0 < I)
    (hβ : β ∈ Ioo (0 : ℝ) 1) :
    warningPhi p I β = β ↔ I = warningInjectionCurve p β := by
  have hβclosed : β ∈ Icc (0 : ℝ) 1 := ⟨hβ.1.le, hβ.2.le⟩
  have hphiDen := warningPhiDenominator_pos model hI hβclosed
  have hcβ : p.c * β < 1 := calc
    p.c * β < p.c * 1 := mul_lt_mul_of_pos_left hβ.2 model.c_pos
    _ = p.c := mul_one _
    _ < 1 := model.c_lt_one
  have hcurveDen : 0 < 2 * p.c * (1 - p.c * β) :=
    mul_pos (mul_pos two_pos model.c_pos) (sub_pos.mpr hcβ)
  simp only [warningPhi, warningInjectionCurve]
  constructor
  · intro hfixed
    rw [div_eq_iff hphiDen.ne'] at hfixed
    apply (eq_div_iff hcurveDen.ne').2
    nlinarith
  · intro hinjection
    rw [eq_div_iff hcurveDen.ne'] at hinjection
    apply (div_eq_iff hphiDen.ne').2
    nlinarith

/-! ## Differential algebra of the fold -/

/-- `warningStockCurvature` is the derivative of `sSlope`. -/
theorem hasDerivAt_warning_sSlope (p : LoopParams) (β : ℝ) :
    HasDerivAt p.sSlope (warningStockCurvature p) β := by
  have hOneSub : HasDerivAt (fun x : ℝ => 1 - x) (-1) β := by
    simpa using (hasDerivAt_id β).const_sub (1 : ℝ)
  have hScaled : HasDerivAt (fun x : ℝ => p.η * (1 - x)) (-p.η) β := by
    convert! hOneSub.const_mul p.η using 1
    ring_nf
  have hinner : HasDerivAt (fun x : ℝ => 1 - p.η * (1 - x)) p.η β := by
    convert! hScaled.const_sub (1 : ℝ) using 1
    ring_nf
  convert! hinner.const_mul (2 * p.η * (1 - p.lambda₀)) using 1
  simp only [warningStockCurvature]
  ring_nf

/-- Exact derivative of the fold numerator. -/
theorem hasDerivAt_warningFoldNumerator (p : LoopParams) (β : ℝ) :
    HasDerivAt (warningFoldNumerator p)
      (-(1 - p.c * β) *
        (2 * p.sSlope β + β * warningStockCurvature p)) β := by
  have hs := p.hasDerivAt_s β
  have hslope := hasDerivAt_warning_sSlope p β
  have hlin : HasDerivAt (fun x : ℝ => 1 - p.c * x) (-p.c) β := by
    convert! ((hasDerivAt_id β).const_mul p.c).const_sub (1 : ℝ) using 1
    ring_nf
  have hfirst : HasDerivAt (fun x : ℝ => x * (1 - p.c * x))
      (1 * (1 - p.c * β) + β * (-p.c)) β := by
    convert! (hasDerivAt_id β).mul hlin using 1
  have hproduct : HasDerivAt
      (fun x : ℝ => x * (1 - p.c * x) * p.sSlope x)
      ((1 * (1 - p.c * β) + β * (-p.c)) * p.sSlope β +
        (β * (1 - p.c * β)) * warningStockCurvature p) β := by
    exact hfirst.mul hslope
  convert! (hs.const_sub (1 : ℝ)).sub hproduct using 1
  simp only [warningStockCurvature, LoopParams.sSlope]
  ring_nf

/-- Exact derivative of the injection curve off its harmless linear pole. -/
theorem hasDerivAt_warningInjectionCurve (p : LoopParams) (β : ℝ)
    (hc : p.c ≠ 0) (hpole : 1 - p.c * β ≠ 0) :
    HasDerivAt (warningInjectionCurve p) (warningInjectionSlope p β) β := by
  have hs := p.hasDerivAt_s β
  have hq : HasDerivAt (fun x : ℝ => 1 - p.s x) (-p.sSlope β) β := by
    convert! hs.const_sub (1 : ℝ) using 1
  have hfirst : HasDerivAt (fun x : ℝ => x * (1 - p.s x))
      (1 * (1 - p.s β) + β * (-p.sSlope β)) β := by
    convert! (hasDerivAt_id β).mul hq using 1
  have hnum : HasDerivAt (fun x : ℝ => p.v * x * (1 - p.s x))
      (p.v * (1 * (1 - p.s β) + β * (-p.sSlope β))) β := by
    convert! hfirst.const_mul p.v using 1
    ring_nf
  have hlin : HasDerivAt (fun x : ℝ => 1 - p.c * x) (-p.c) β := by
    convert! ((hasDerivAt_id β).const_mul p.c).const_sub (1 : ℝ) using 1
    ring_nf
  have hden := hlin.const_mul (2 * p.c)
  have hdenne : 2 * p.c * (1 - p.c * β) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hc) hpole
  convert! hnum.div hden hdenne using 1
  simp only [warningInjectionSlope, warningFoldNumerator]
  field_simp [hpole]
  ring_nf

/-- The stock multiplier's constant curvature is strictly positive. -/
theorem warningStockCurvature_pos {p : LoopParams}
    (model : DriftModelAssumptions p) :
    0 < warningStockCurvature p := by
  simp only [warningStockCurvature]
  exact mul_pos (mul_pos two_pos (sq_pos_of_pos model.η_pos))
    (sub_pos.mpr model.lambda₀_lt_one)

/-- The fold numerator has strictly negative derivative in the policy interior. -/
theorem warningFoldNumerator_deriv_neg {p : LoopParams}
    (model : DriftModelAssumptions p) {β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1) :
    deriv (warningFoldNumerator p) β < 0 := by
  rw [(hasDerivAt_warningFoldNumerator p β).deriv]
  have hcβ : p.c * β < 1 := calc
    p.c * β < p.c * 1 := mul_lt_mul_of_pos_left hβ.2 model.c_pos
    _ = p.c := mul_one _
    _ < 1 := model.c_lt_one
  have hslope : 0 < p.sSlope β := sSlope_pos model hβ
  have hcurvature : 0 < warningStockCurvature p := warningStockCurvature_pos model
  have hsum : 0 < 2 * p.sSlope β + β * warningStockCurvature p := by
    exact add_pos (mul_pos two_pos hslope) (mul_pos hβ.1 hcurvature)
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (sub_pos.mpr hcβ)) hsum

/-- The fold numerator is strictly decreasing throughout `[0,1]`. -/
theorem warningFoldNumerator_strictAntiOn {p : LoopParams}
    (model : DriftModelAssumptions p) :
    StrictAntiOn (warningFoldNumerator p) (Icc (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc (0 : ℝ) 1)
  · intro β _hβ
    exact (hasDerivAt_warningFoldNumerator p β).continuousAt.continuousWithinAt
  · intro β hβ
    rw [interior_Icc] at hβ
    exact warningFoldNumerator_deriv_neg model hβ

/-- Before the fold the injection curve has positive derivative numerator. -/
theorem warningFoldNumerator_pos_before {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) {β : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) (hbefore : β < fold.βfold) :
    0 < warningFoldNumerator p β := by
  have hfold : fold.βfold ∈ Icc (0 : ℝ) 1 :=
    ⟨fold.βfold_mem.1.le, fold.βfold_mem.2.le⟩
  have hstrict := warningFoldNumerator_strictAntiOn model hβ hfold hbefore
  rwa [fold.critical] at hstrict

/-- After the fold the injection curve has negative derivative numerator. -/
theorem warningFoldNumerator_neg_after {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) {β : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) (hafter : fold.βfold < β) :
    warningFoldNumerator p β < 0 := by
  have hfold : fold.βfold ∈ Icc (0 : ℝ) 1 :=
    ⟨fold.βfold_mem.1.le, fold.βfold_mem.2.le⟩
  have hstrict := warningFoldNumerator_strictAntiOn model hfold hβ hafter
  rwa [fold.critical] at hstrict

/-- The injection curve is continuous on the full policy interval. -/
theorem warningInjectionCurve_continuousOn {p : LoopParams}
    (model : DriftModelAssumptions p) :
    ContinuousOn (warningInjectionCurve p) (Icc (0 : ℝ) 1) := by
  intro β hβ
  have hcβ : p.c * β < 1 := calc
    p.c * β ≤ p.c * 1 := mul_le_mul_of_nonneg_left hβ.2 model.c_pos.le
    _ = p.c := mul_one _
    _ < 1 := model.c_lt_one
  exact (hasDerivAt_warningInjectionCurve p β model.c_pos.ne'
    (sub_pos.mpr hcβ).ne').continuousAt.continuousWithinAt

/-- The injection curve rises strictly from zero to its fold. -/
theorem warningInjectionCurve_strictMonoOn_before {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) :
    StrictMonoOn (warningInjectionCurve p) (Icc (0 : ℝ) fold.βfold) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) fold.βfold)
  · exact (warningInjectionCurve_continuousOn model).mono (Icc_subset_Icc_right
      fold.βfold_mem.2.le)
  · intro β hβ
    rw [interior_Icc] at hβ
    have hβclosed : β ∈ Icc (0 : ℝ) 1 :=
      ⟨hβ.1.le, hβ.2.le.trans fold.βfold_mem.2.le⟩
    have hnum := warningFoldNumerator_pos_before model fold hβclosed hβ.2
    have hcβ : p.c * β < 1 := calc
      p.c * β ≤ p.c * 1 := mul_le_mul_of_nonneg_left hβclosed.2 model.c_pos.le
      _ = p.c := mul_one _
      _ < 1 := model.c_lt_one
    rw [(hasDerivAt_warningInjectionCurve p β model.c_pos.ne'
      (sub_pos.mpr hcβ).ne').deriv]
    simp only [warningInjectionSlope]
    exact div_pos (mul_pos model.v_pos hnum)
      (mul_pos (mul_pos two_pos model.c_pos) (sq_pos_of_pos (sub_pos.mpr hcβ)))

/-- The injection curve falls strictly from its fold to the captured endpoint. -/
theorem warningInjectionCurve_strictAntiOn_after {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) :
    StrictAntiOn (warningInjectionCurve p) (Icc fold.βfold 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc fold.βfold (1 : ℝ))
  · exact (warningInjectionCurve_continuousOn model).mono (Icc_subset_Icc_left
      fold.βfold_mem.1.le)
  · intro β hβ
    rw [interior_Icc] at hβ
    have hβclosed : β ∈ Icc (0 : ℝ) 1 :=
      ⟨fold.βfold_mem.1.le.trans hβ.1.le, hβ.2.le⟩
    have hnum := warningFoldNumerator_neg_after model fold hβclosed hβ.1
    have hcβ : p.c * β < 1 := calc
      p.c * β < p.c * 1 := mul_lt_mul_of_pos_left hβ.2 model.c_pos
      _ = p.c := mul_one _
      _ < 1 := model.c_lt_one
    rw [(hasDerivAt_warningInjectionCurve p β model.c_pos.ne'
      (sub_pos.mpr hcβ).ne').deriv]
    simp only [warningInjectionSlope]
    have hden : 0 < 2 * p.c * (1 - p.c * β) ^ 2 :=
      mul_pos (mul_pos two_pos model.c_pos) (sq_pos_of_pos (sub_pos.mpr hcβ))
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg model.v_pos hnum) hden

/-- Scale factor in the exact double-root factorization of the injection gap. -/
def warningInjectionGapScale (p : LoopParams) (βfold β : ℝ) : ℝ :=
  p.v * (p.sSlope βfold + p.η ^ 2 * (1 - p.lambda₀) * β) /
    (2 * p.c * (1 - p.c * β))

/--
At a fold, the injection gap has an exact double-root factorization.  This is
the model-specific algebra behind saddle-node square-root scaling.
-/
theorem warningInjectionCurve_fold_gap_eq {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) {β : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) :
    warningInjectionCurve p fold.βfold - warningInjectionCurve p β =
      (fold.βfold - β) ^ 2 *
        warningInjectionGapScale p fold.βfold β := by
  have hcFold : p.c * fold.βfold < 1 := calc
    p.c * fold.βfold < p.c * 1 :=
      mul_lt_mul_of_pos_left fold.βfold_mem.2 model.c_pos
    _ = p.c := mul_one _
    _ < 1 := model.c_lt_one
  have hcβ : p.c * β < 1 := calc
    p.c * β ≤ p.c * 1 := mul_le_mul_of_nonneg_left hβ.2 model.c_pos.le
    _ = p.c := mul_one _
    _ < 1 := model.c_lt_one
  have hfoldPole : 1 - fold.βfold * p.c ≠ 0 := by
    nlinarith [hcFold]
  have hβPole : 1 - β * p.c ≠ 0 := by
    nlinarith [hcβ]
  have hfoldEq : 1 - p.s fold.βfold =
      fold.βfold * (1 - p.c * fold.βfold) * p.sSlope fold.βfold := by
    have hcritical := fold.critical
    simp only [warningFoldNumerator] at hcritical
    linarith [hcritical]
  have hstockAtFold : p.s fold.βfold =
      1 - fold.βfold * (1 - p.c * fold.βfold) * p.sSlope fold.βfold := by
    linarith [hfoldEq]
  have hsTaylor : p.s β = p.s fold.βfold +
      p.sSlope fold.βfold * (β - fold.βfold) +
        (1 - p.lambda₀) * p.η ^ 2 * (β - fold.βfold) ^ 2 := by
    simp only [LoopParams.s, LoopParams.sSlope]
    ring_nf
  simp only [warningInjectionCurve, warningInjectionGapScale]
  rw [hsTaylor, hstockAtFold]
  field_simp [(sub_pos.mpr hcFold).ne', (sub_pos.mpr hcβ).ne', hfoldPole, hβPole,
    model.c_pos.ne']
  ring_nf

/-! ## Exact collision and annihilation of the interior pair -/

/-- The injection curve starts at zero. -/
theorem warningInjectionCurve_zero (p : LoopParams) :
    warningInjectionCurve p 0 = 0 := by
  simp [warningInjectionCurve]

/-- The captured endpoint has a strictly positive injection threshold. -/
theorem warningInjectionCurve_one_pos {p : LoopParams}
    (model : DriftModelAssumptions p) :
    0 < warningInjectionCurve p 1 := by
  have hq : 0 < 1 - p.s 1 := warningStockDenominator_pos model (by norm_num)
  have hc : 0 < 1 - p.c := sub_pos.mpr model.c_lt_one
  simp only [warningInjectionCurve, mul_one]
  exact div_pos (mul_pos model.v_pos hq) (mul_pos (mul_pos two_pos model.c_pos) hc)

/-- The fold is the unique global maximum of the injection curve on `[0,1]`. -/
theorem warningInjectionCurve_le_fold {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) {β : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) :
    warningInjectionCurve p β ≤ warningInjectionCurve p fold.βfold := by
  rcases le_total β fold.βfold with hbefore | hafter
  · rcases hbefore.eq_or_lt with rfl | hstrict
    · exact le_rfl
    · exact (warningInjectionCurve_strictMonoOn_before model fold
        ⟨hβ.1, hstrict.le⟩
        ⟨fold.βfold_mem.1.le, le_rfl⟩ hstrict).le
  · rcases hafter.eq_or_lt with rfl | hstrict
    · exact le_rfl
    · exact (warningInjectionCurve_strictAntiOn_after model fold
        ⟨le_rfl, fold.βfold_mem.2.le⟩
        ⟨hstrict.le, hβ.2⟩ hstrict).le

/-- Equality with the fold injection occurs only at the fold policy. -/
theorem warningInjectionCurve_eq_fold_iff {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) {β : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) :
    warningInjectionCurve p β = warningInjectionCurve p fold.βfold ↔
      β = fold.βfold := by
  constructor
  · intro heq
    rcases le_total β fold.βfold with hbefore | hafter
    · exact (warningInjectionCurve_strictMonoOn_before model fold).injOn
        ⟨hβ.1, hbefore⟩ ⟨fold.βfold_mem.1.le, le_rfl⟩ heq
    · exact (warningInjectionCurve_strictAntiOn_after model fold).injOn
        ⟨hafter, hβ.2⟩ ⟨le_rfl, fold.βfold_mem.2.le⟩ heq
  · rintro rfl
    rfl

/-- Below the fold and above the captured threshold there is one lower fixed policy. -/
theorem warning_existsUnique_lower_fixedPoint {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) {I : ℝ}
    (hcaptured : warningInjectionCurve p 1 < I)
    (hbelow : I < warningInjectionCurve p fold.βfold) :
    ∃! β : ℝ, β ∈ Ioo (0 : ℝ) fold.βfold ∧ warningPhi p I β = β := by
  have hI : 0 < I := (warningInjectionCurve_one_pos model).trans hcaptured
  have hcont : ContinuousOn (warningInjectionCurve p) (Icc (0 : ℝ) fold.βfold) :=
    (warningInjectionCurve_continuousOn model).mono
      (Icc_subset_Icc_right fold.βfold_mem.2.le)
  have hIrange : I ∈ Icc (warningInjectionCurve p 0)
      (warningInjectionCurve p fold.βfold) := by
    rw [warningInjectionCurve_zero]
    exact ⟨hI.le, hbelow.le⟩
  rcases intermediate_value_Icc fold.βfold_mem.1.le hcont hIrange with
    ⟨β, hβclosed, hcurve⟩
  have hβzero : β ≠ 0 := by
    intro hzero
    subst β
    rw [warningInjectionCurve_zero] at hcurve
    linarith
  have hβfold : β ≠ fold.βfold := by
    intro hfold
    subst β
    linarith
  have hβ : β ∈ Ioo (0 : ℝ) fold.βfold :=
    ⟨lt_of_le_of_ne hβclosed.1 (Ne.symm hβzero),
      lt_of_le_of_ne hβclosed.2 hβfold⟩
  have hβunit : β ∈ Ioo (0 : ℝ) 1 :=
    ⟨hβ.1, hβ.2.trans fold.βfold_mem.2⟩
  have hfixed : warningPhi p I β = β :=
    (warningPhi_eq_self_iff model hI hβunit).2 hcurve.symm
  refine ⟨β, ⟨hβ, hfixed⟩, ?_⟩
  intro y hy
  have hyunit : y ∈ Ioo (0 : ℝ) 1 :=
    ⟨hy.1.1, hy.1.2.trans fold.βfold_mem.2⟩
  have hycurve : I = warningInjectionCurve p y :=
    (warningPhi_eq_self_iff model hI hyunit).1 hy.2
  exact ((warningInjectionCurve_strictMonoOn_before model fold).injOn
    ⟨hβ.1.le, hβ.2.le⟩ ⟨hy.1.1.le, hy.1.2.le⟩ (hcurve.trans hycurve)).symm

/-- Below the fold and above the captured threshold there is one upper fixed policy. -/
theorem warning_existsUnique_upper_fixedPoint {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) {I : ℝ}
    (hcaptured : warningInjectionCurve p 1 < I)
    (hbelow : I < warningInjectionCurve p fold.βfold) :
    ∃! β : ℝ, β ∈ Ioo fold.βfold 1 ∧ warningPhi p I β = β := by
  have hI : 0 < I := (warningInjectionCurve_one_pos model).trans hcaptured
  have hcont : ContinuousOn (warningInjectionCurve p) (Icc fold.βfold 1) :=
    (warningInjectionCurve_continuousOn model).mono
      (Icc_subset_Icc_left fold.βfold_mem.1.le)
  have hIrange : I ∈ Icc (warningInjectionCurve p 1)
      (warningInjectionCurve p fold.βfold) := ⟨hcaptured.le, hbelow.le⟩
  rcases intermediate_value_Icc' fold.βfold_mem.2.le hcont hIrange with
    ⟨β, hβclosed, hcurve⟩
  have hβfold : β ≠ fold.βfold := by
    intro hfold
    subst β
    linarith
  have hβone : β ≠ 1 := by
    intro hone
    subst β
    linarith
  have hβ : β ∈ Ioo fold.βfold 1 :=
    ⟨lt_of_le_of_ne hβclosed.1 (Ne.symm hβfold),
      lt_of_le_of_ne hβclosed.2 hβone⟩
  have hβunit : β ∈ Ioo (0 : ℝ) 1 :=
    ⟨fold.βfold_mem.1.trans hβ.1, hβ.2⟩
  have hfixed : warningPhi p I β = β :=
    (warningPhi_eq_self_iff model hI hβunit).2 hcurve.symm
  refine ⟨β, ⟨hβ, hfixed⟩, ?_⟩
  intro y hy
  have hyunit : y ∈ Ioo (0 : ℝ) 1 :=
    ⟨fold.βfold_mem.1.trans hy.1.1, hy.1.2⟩
  have hycurve : I = warningInjectionCurve p y :=
    (warningPhi_eq_self_iff model hI hyunit).1 hy.2
  exact ((warningInjectionCurve_strictAntiOn_after model fold).injOn
    ⟨hβ.1.le, hβ.2.le⟩ ⟨hy.1.1.le, hy.1.2.le⟩ (hcurve.trans hycurve)).symm

/-- At the fold injection the two interior policies have coalesced uniquely. -/
theorem warning_fold_unique_fixedPoint {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) {β : ℝ}
    (hβ : β ∈ Ioo (0 : ℝ) 1) :
    warningPhi p (warningInjectionCurve p fold.βfold) β = β ↔
      β = fold.βfold := by
  have hfoldInjection : 0 < warningInjectionCurve p fold.βfold := by
    have hmono := warningInjectionCurve_strictMonoOn_before model fold
      (show (0 : ℝ) ∈ Icc 0 fold.βfold from ⟨le_rfl, fold.βfold_mem.1.le⟩)
      (show fold.βfold ∈ Icc 0 fold.βfold from
        ⟨fold.βfold_mem.1.le, le_rfl⟩) fold.βfold_mem.1
    rwa [warningInjectionCurve_zero] at hmono
  rw [warningPhi_eq_self_iff model hfoldInjection hβ]
  rw [eq_comm]
  exact warningInjectionCurve_eq_fold_iff model fold ⟨hβ.1.le, hβ.2.le⟩

/-- Above the fold injection there are no interior fixed policies. -/
theorem warning_no_fixedPoint_above_fold {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) {I β : ℝ}
    (habove : warningInjectionCurve p fold.βfold < I)
    (hβ : β ∈ Ioo (0 : ℝ) 1) :
    warningPhi p I β ≠ β := by
  have hfoldInjection : 0 < warningInjectionCurve p fold.βfold := by
    have hmono := warningInjectionCurve_strictMonoOn_before model fold
      (show (0 : ℝ) ∈ Icc 0 fold.βfold from ⟨le_rfl, fold.βfold_mem.1.le⟩)
      (show fold.βfold ∈ Icc 0 fold.βfold from
        ⟨fold.βfold_mem.1.le, le_rfl⟩) fold.βfold_mem.1
    rwa [warningInjectionCurve_zero] at hmono
  have hI : 0 < I := hfoldInjection.trans habove
  intro hfixed
  have hcurve : I = warningInjectionCurve p β :=
    (warningPhi_eq_self_iff model hI hβ).1 hfixed
  have hmax := warningInjectionCurve_le_fold model fold
    (show β ∈ Icc (0 : ℝ) 1 from ⟨hβ.1.le, hβ.2.le⟩)
  linarith

/-! ## The full simultaneous-map Jacobian -/

/-- Stock coordinate along the quadratic-cost equilibrium characteristic. -/
def warningEquilibriumStock (p : LoopParams) (β : ℝ) : ℝ :=
  p.v * β / (2 * p.c * (1 - p.c * β))

/-- The unclipped simultaneous-map Jacobian for the quadratic policy cost. -/
def warningJacobian (p : LoopParams) (β D : ℝ) : LoopJacobian where
  a := 1 + p.α * (-p.v - 2 * p.c ^ 2 * D)
  b := p.α * 2 * p.c * (1 - p.c * β)
  cJ := p.sSlope β * D
  d := p.s β

/-- Jacobian evaluated along the equilibrium injection curve. -/
def warningEquilibriumJacobian (p : LoopParams) (β : ℝ) : LoopJacobian :=
  warningJacobian p β (warningEquilibriumStock p β)

/-- The plus-sign real root, i.e. the slow eigenvalue near the cooperative fold. -/
def warningSlowEigenvalue (p : LoopParams) (β : ℝ) : ℝ :=
  (warningEquilibriumJacobian p β).largerEigenvalue

/-- Characteristic-polynomial value at one along the equilibrium curve. -/
def warningCharPolyOne (p : LoopParams) (β : ℝ) : ℝ :=
  p.α * p.v * warningFoldNumerator p β / (1 - p.c * β)

/-- Along the injection curve the stationary-stock and policy nullclines agree. -/
theorem warningStationaryStock_on_injectionCurve {p : LoopParams}
    (model : DriftModelAssumptions p) {β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1) :
    warningStationaryStock p (warningInjectionCurve p β) β =
      warningEquilibriumStock p β := by
  have hstockDen := warningStockDenominator_pos model ⟨hβ.1.le, hβ.2.le⟩
  have hcβ : p.c * β < 1 := calc
    p.c * β < p.c * 1 := mul_lt_mul_of_pos_left hβ.2 model.c_pos
    _ = p.c := mul_one _
    _ < 1 := model.c_lt_one
  simp only [warningStationaryStock, warningInjectionCurve, warningEquilibriumStock]
  field_simp [hstockDen.ne', (sub_pos.mpr hcβ).ne', model.c_pos.ne']

/-- The characteristic polynomial at one has the fold numerator as its only sign factor. -/
theorem warningEquilibriumJacobian_charPoly_one_eq {p : LoopParams} {β : ℝ}
    (hc : p.c ≠ 0) (hpole : 1 - p.c * β ≠ 0) :
    (warningEquilibriumJacobian p β).charPoly 1 = warningCharPolyOne p β := by
  simp only [warningEquilibriumJacobian, warningJacobian, warningEquilibriumStock,
    LoopJacobian.charPoly, LoopJacobian.trace, LoopJacobian.det,
    warningCharPolyOne, warningFoldNumerator]
  field_simp [hc, hpole]
  ring_nf

/-- At an interior point all cooperative off-diagonal terms are strictly positive. -/
theorem warningEquilibriumJacobian_fold_entry_bounds {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) :
    let J := warningEquilibriumJacobian p fold.βfold
    0 < J.b ∧ 0 < J.cJ ∧ 0 ≤ J.d ∧ J.d < 1 := by
  let β := fold.βfold
  let D := warningEquilibriumStock p β
  have hcβ : p.c * β < 1 := calc
    p.c * β < p.c * 1 := mul_lt_mul_of_pos_left fold.βfold_mem.2 model.c_pos
    _ = p.c := mul_one _
    _ < 1 := model.c_lt_one
  have hD : 0 < D := by
    simp only [D, warningEquilibriumStock]
    exact div_pos (mul_pos model.v_pos fold.βfold_mem.1)
      (mul_pos (mul_pos two_pos model.c_pos) (sub_pos.mpr hcβ))
  have hslope : 0 < p.sSlope β := sSlope_pos model fold.βfold_mem
  have hs := driftStockMultiplier_nonneg_le model
    (show β ∈ Icc (0 : ℝ) 1 from
      ⟨fold.βfold_mem.1.le, fold.βfold_mem.2.le⟩)
  dsimp only [warningEquilibriumJacobian, warningJacobian]
  exact ⟨mul_pos (mul_pos (mul_pos model.α_pos two_pos) model.c_pos)
      (sub_pos.mpr hcβ),
    mul_pos hslope hD, hs.1, hs.2.trans_lt (by linarith [model.lambda₀_pos])⟩

/-- At the fold the full planar Jacobian has slow eigenvalue exactly one. -/
theorem warningFold_largerEigenvalue_eq_one {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) :
    warningSlowEigenvalue p fold.βfold = 1 := by
  let J := warningEquilibriumJacobian p fold.βfold
  have hentries := warningEquilibriumJacobian_fold_entry_bounds model fold
  have hdisc : 0 ≤ J.discriminant :=
    J.discriminant_nonneg hentries.1.le hentries.2.1.le
  have hsmall : J.smallerEigenvalue < 1 :=
    J.smallerEigenvalue_lt_one hentries.2.2.2
      (mul_nonneg hentries.1.le hentries.2.1.le)
  have hcβ : p.c * fold.βfold < 1 := calc
    p.c * fold.βfold < p.c * 1 :=
      mul_lt_mul_of_pos_left fold.βfold_mem.2 model.c_pos
    _ = p.c := mul_one _
    _ < 1 := model.c_lt_one
  have hchar : J.charPoly 1 = 0 := by
    rw [warningEquilibriumJacobian_charPoly_one_eq model.c_pos.ne'
      (sub_pos.mpr hcβ).ne']
    simp only [warningCharPolyOne, fold.critical]
    simp
  have hfactor := J.charPoly_eq_mul_eigenvalues hdisc 1
  rw [hchar] at hfactor
  have hright : 0 < 1 - J.smallerEigenvalue := sub_pos.mpr hsmall
  have hlarge : J.largerEigenvalue = 1 := by
    rcases mul_eq_zero.mp hfactor.symm with hleft | hfalse
    · linarith
    · exact False.elim (hright.ne' hfalse)
  simpa only [warningSlowEigenvalue, J] using hlarge

/-- The second real root remains strictly below one at the fold. -/
theorem warningFold_smallerEigenvalue_lt_one {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) :
    (warningEquilibriumJacobian p fold.βfold).smallerEigenvalue < 1 := by
  have hentries := warningEquilibriumJacobian_fold_entry_bounds model fold
  exact LoopJacobian.smallerEigenvalue_lt_one _ hentries.2.2.2
    (mul_nonneg hentries.1.le hentries.2.1.le)

/-- The characteristic value crosses zero simply at the fold. -/
theorem hasDerivAt_warningCharPolyOne_at_fold {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) :
    HasDerivAt (warningCharPolyOne p)
      (-p.α * p.v *
        (2 * p.sSlope fold.βfold +
          fold.βfold * warningStockCurvature p)) fold.βfold := by
  let βf := fold.βfold
  have hcβ : p.c * βf < 1 := calc
    p.c * βf < p.c * 1 := mul_lt_mul_of_pos_left fold.βfold_mem.2 model.c_pos
    _ = p.c := mul_one _
    _ < 1 := model.c_lt_one
  have hnum : HasDerivAt
      (fun β : ℝ => p.α * p.v * warningFoldNumerator p β)
      (p.α * p.v * (-(1 - p.c * βf) *
        (2 * p.sSlope βf + βf * warningStockCurvature p))) βf := by
    exact (hasDerivAt_warningFoldNumerator p βf).const_mul (p.α * p.v)
  have hden : HasDerivAt (fun β : ℝ => 1 - p.c * β) (-p.c) βf := by
    convert! ((hasDerivAt_id βf).const_mul p.c).const_sub (1 : ℝ) using 1
    ring_nf
  have hquot := hnum.div hden (sub_pos.mpr hcβ).ne'
  convert! hquot using 1
  simp only [βf, fold.critical, mul_zero]
  apply (eq_div_iff (pow_ne_zero 2 (sub_pos.mpr hcβ).ne')).2
  dsimp only [βf]
  ring_nf

/-- The simple crossing derivative is strictly negative, hence nonzero. -/
theorem warningCharPolyOne_fold_deriv_neg {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) :
    -p.α * p.v *
      (2 * p.sSlope fold.βfold +
        fold.βfold * warningStockCurvature p) < 0 := by
  have hslope := sSlope_pos model fold.βfold_mem
  have hcurve := warningStockCurvature_pos model
  have hsum : 0 < 2 * p.sSlope fold.βfold +
      fold.βfold * warningStockCurvature p :=
    add_pos (mul_pos two_pos hslope) (mul_pos fold.βfold_mem.1 hcurve)
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (neg_neg_of_pos model.α_pos) model.v_pos) hsum

/-- Continuity of the noncritical eigenvalue branch at an interior policy. -/
theorem continuousAt_warningSmallerEigenvalue {p : LoopParams} {β : ℝ}
    (hc : p.c ≠ 0) (hpole : 1 - p.c * β ≠ 0) :
    ContinuousAt
      (fun x : ℝ => (warningEquilibriumJacobian p x).smallerEigenvalue) β := by
  have hden : 2 * p.c * (1 - p.c * β) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hc) hpole
  have hD : ContinuousAt (warningEquilibriumStock p) β := by
    unfold warningEquilibriumStock
    fun_prop
  have ha : ContinuousAt
      (fun x : ℝ => 1 + p.α * (-p.v - 2 * p.c ^ 2 * warningEquilibriumStock p x)) β := by
    fun_prop
  have hb : ContinuousAt (fun x : ℝ => p.α * 2 * p.c * (1 - p.c * x)) β := by
    fun_prop
  have hcJ : ContinuousAt
      (fun x : ℝ => p.sSlope x * warningEquilibriumStock p x) β := by
    exact (hasDerivAt_warning_sSlope p β).continuousAt.mul hD
  have hd : ContinuousAt p.s β := (p.hasDerivAt_s β).continuousAt
  unfold warningEquilibriumJacobian warningJacobian LoopJacobian.smallerEigenvalue
    LoopJacobian.trace LoopJacobian.discriminant
  dsimp only
  fun_prop

/-- Near the fold, the slow-root gap is the characteristic value divided by the other gap. -/
theorem warningSlowEigenvalue_gap_eq {p : LoopParams}
    (model : DriftModelAssumptions p) {β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1) :
    1 - warningSlowEigenvalue p β =
      warningCharPolyOne p β /
        (1 - (warningEquilibriumJacobian p β).smallerEigenvalue) := by
  let J := warningEquilibriumJacobian p β
  change 1 - J.largerEigenvalue = warningCharPolyOne p β / (1 - J.smallerEigenvalue)
  have hcβ : p.c * β < 1 := calc
    p.c * β < p.c * 1 := mul_lt_mul_of_pos_left hβ.2 model.c_pos
    _ = p.c := mul_one _
    _ < 1 := model.c_lt_one
  have hD : 0 < warningEquilibriumStock p β := by
    simp only [warningEquilibriumStock]
    exact div_pos (mul_pos model.v_pos hβ.1)
      (mul_pos (mul_pos two_pos model.c_pos) (sub_pos.mpr hcβ))
  have hb : 0 < J.b := by
    dsimp only [J, warningEquilibriumJacobian, warningJacobian]
    exact mul_pos (mul_pos (mul_pos model.α_pos two_pos) model.c_pos)
      (sub_pos.mpr hcβ)
  have hcJ : 0 < J.cJ := by
    dsimp only [J, warningEquilibriumJacobian, warningJacobian]
    exact mul_pos (sSlope_pos model hβ) hD
  have hs := driftStockMultiplier_nonneg_le model ⟨hβ.1.le, hβ.2.le⟩
  have hd : J.d < 1 := by
    dsimp only [J, warningEquilibriumJacobian, warningJacobian]
    linarith [hs.2, model.lambda₀_pos]
  have hdisc : 0 ≤ J.discriminant := J.discriminant_nonneg hb.le hcJ.le
  have hsmall : J.smallerEigenvalue < 1 :=
    J.smallerEigenvalue_lt_one hd (mul_nonneg hb.le hcJ.le)
  have hfactor := J.charPoly_eq_mul_eigenvalues hdisc 1
  rw [warningEquilibriumJacobian_charPoly_one_eq model.c_pos.ne'
    (sub_pos.mpr hcβ).ne'] at hfactor
  have hden : 1 - J.smallerEigenvalue ≠ 0 := (sub_pos.mpr hsmall).ne'
  rw [hfactor]
  field_simp [hden]

/-! ## Square-root early-warning scaling -/

/-- The double-root scale is positive throughout the policy interval. -/
theorem warningInjectionGapScale_pos {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) {β : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 < warningInjectionGapScale p fold.βfold β := by
  have hslope := sSlope_pos model fold.βfold_mem
  have hground : 0 ≤ p.η ^ 2 * (1 - p.lambda₀) * β := by
    exact mul_nonneg
      (mul_nonneg (sq_nonneg p.η) (sub_nonneg.mpr model.lambda₀_lt_one.le)) hβ.1
  have hnum : 0 < p.v *
      (p.sSlope fold.βfold + p.η ^ 2 * (1 - p.lambda₀) * β) := by
    exact mul_pos model.v_pos (add_pos_of_pos_of_nonneg hslope hground)
  have hcβ : p.c * β < 1 := calc
    p.c * β ≤ p.c * 1 := mul_le_mul_of_nonneg_left hβ.2 model.c_pos.le
    _ = p.c := mul_one _
    _ < 1 := model.c_lt_one
  simp only [warningInjectionGapScale]
  exact div_pos hnum (mul_pos (mul_pos two_pos model.c_pos) (sub_pos.mpr hcβ))

/-- The double-root scale varies continuously at the fold. -/
theorem continuousAt_warningInjectionGapScale {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) :
    ContinuousAt (warningInjectionGapScale p fold.βfold) fold.βfold := by
  have hcβ : p.c * fold.βfold < 1 := calc
    p.c * fold.βfold < p.c * 1 :=
      mul_lt_mul_of_pos_left fold.βfold_mem.2 model.c_pos
    _ = p.c := mul_one _
    _ < 1 := model.c_lt_one
  have hden : 2 * p.c * (1 - p.c * fold.βfold) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero model.c_pos.ne') (sub_pos.mpr hcβ).ne'
  unfold warningInjectionGapScale
  exact (by fun_prop : ContinuousAt
    (fun β : ℝ => p.v *
      (p.sSlope fold.βfold + p.η ^ 2 * (1 - p.lambda₀) * β)) fold.βfold).div
      (by fun_prop) hden

/--
The square root of the injection shortfall is asymptotically proportional to
the policy distance from the fold along the calibrated (lower) branch.
-/
theorem warningInjectionGap_sqrt_isTheta_policyGap {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) :
    (fun β : ℝ => fold.βfold - β) =Θ[𝓝[<] fold.βfold]
      (fun β : ℝ => Real.sqrt
        (warningInjectionCurve p fold.βfold - warningInjectionCurve p β)) := by
  let L : Filter ℝ := 𝓝[<] fold.βfold
  let scale := warningInjectionGapScale p fold.βfold
  have hscalePos : 0 < scale fold.βfold :=
    warningInjectionGapScale_pos model fold
      ⟨fold.βfold_mem.1.le, fold.βfold_mem.2.le⟩
  have hscaleTendsto : Tendsto scale L (𝓝 (scale fold.βfold)) :=
    (continuousAt_warningInjectionGapScale model fold).tendsto.mono_left
      nhdsWithin_le_nhds
  have hratioEq :
      (fun β : ℝ =>
        (warningInjectionCurve p fold.βfold - warningInjectionCurve p β) /
          (fold.βfold - β) ^ 2) =ᶠ[L] scale := by
    filter_upwards [Ioo_mem_nhdsLT fold.βfold_mem.1] with β hβ
    rw [warningInjectionCurve_fold_gap_eq model fold
      ⟨hβ.1.le, hβ.2.le.trans fold.βfold_mem.2.le⟩]
    have hlinne : fold.βfold - β ≠ 0 :=
      sub_ne_zero.mpr (ne_of_gt hβ.2)
    dsimp only [scale]
    field_simp [hlinne]
  have hratioTendsto : Tendsto
      (fun β : ℝ =>
        (warningInjectionCurve p fold.βfold - warningInjectionCurve p β) /
          (fold.βfold - β) ^ 2) L (𝓝 (scale fold.βfold)) :=
    hscaleTendsto.congr' hratioEq.symm
  have hsquares :
      (fun β : ℝ => (fold.βfold - β) ^ 2) =Θ[L]
        (fun β : ℝ =>
          warningInjectionCurve p fold.βfold - warningInjectionCurve p β) :=
    isTheta_of_div_tendsto_nhds_ne_zero hratioTendsto hscalePos.ne'
  have hsquareNonneg :
      ∀ᶠ β : ℝ in L, 0 ≤ (fold.βfold - β) ^ 2 :=
    Eventually.of_forall fun β => sq_nonneg (fold.βfold - β)
  have hgapNonneg : ∀ᶠ β : ℝ in L,
      0 ≤ warningInjectionCurve p fold.βfold - warningInjectionCurve p β := by
    filter_upwards [Ioo_mem_nhdsLT fold.βfold_mem.1] with β hβ
    exact sub_nonneg.mpr (warningInjectionCurve_le_fold model fold
      ⟨hβ.1.le, hβ.2.le.trans fold.βfold_mem.2.le⟩)
  have hsqrt := hsquares.sqrt hsquareNonneg hgapNonneg
  have hsqrtSquareEq :
      (fun β : ℝ => Real.sqrt ((fold.βfold - β) ^ 2)) =ᶠ[L]
        (fun β : ℝ => fold.βfold - β) := by
    filter_upwards [self_mem_nhdsWithin] with β hβ
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (sub_pos.mpr hβ)]
  exact hsqrtSquareEq.symm.trans_isTheta hsqrt

/-- The characteristic value is asymptotically linear in distance from the fold. -/
theorem warningCharPolyOne_isTheta_policyGap {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) :
    (warningCharPolyOne p) =Θ[𝓝[<] fold.βfold]
      (fun β : ℝ => fold.βfold - β) := by
  let L : Filter ℝ := 𝓝[<] fold.βfold
  have hderivNeg := warningCharPolyOne_fold_deriv_neg model fold
  have hpair := HasDerivAtFilter.isTheta_sub
    (hasDerivAt_warningCharPolyOne_at_fold model fold) hderivNeg.ne
  have hthetaFull :
      (fun β : ℝ => warningCharPolyOne p β -
        warningCharPolyOne p fold.βfold) =Θ[𝓝 fold.βfold]
          (fun β : ℝ => β - fold.βfold) := by
    simpa only [eventually_pure] using hpair.fiberwise_left
  have hzero : warningCharPolyOne p fold.βfold = 0 := by
    simp [warningCharPolyOne, fold.critical]
  rw [hzero] at hthetaFull
  simp only [sub_zero] at hthetaFull
  have hthetaLeft : warningCharPolyOne p =Θ[L]
      (fun β : ℝ => β - fold.βfold) :=
    hthetaFull.mono nhdsWithin_le_nhds
  have hsign : (fun β : ℝ => β - fold.βfold) =Θ[L]
      (fun β : ℝ => fold.βfold - β) := by
    apply IsTheta.of_norm_eventuallyEq_norm
    exact Eventually.of_forall fun β => norm_sub_rev β fold.βfold
  exact hthetaLeft.trans hsign

/-- The full planar slow-eigenvalue gap is linear in policy distance from the fold. -/
theorem warningSlowEigenvalue_gap_isTheta_policyGap {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) :
    (fun β : ℝ => 1 - warningSlowEigenvalue p β) =Θ[𝓝[<] fold.βfold]
      (fun β : ℝ => fold.βfold - β) := by
  let L : Filter ℝ := 𝓝[<] fold.βfold
  let otherGap := fun β : ℝ =>
    1 - (warningEquilibriumJacobian p β).smallerEigenvalue
  have hcβ : p.c * fold.βfold < 1 := calc
    p.c * fold.βfold < p.c * 1 :=
      mul_lt_mul_of_pos_left fold.βfold_mem.2 model.c_pos
    _ = p.c := mul_one _
    _ < 1 := model.c_lt_one
  have hotherPos : 0 < otherGap fold.βfold :=
    sub_pos.mpr (warningFold_smallerEigenvalue_lt_one model fold)
  have hsmallTendsto : Tendsto
      (fun β : ℝ => (warningEquilibriumJacobian p β).smallerEigenvalue) L
      (𝓝 ((warningEquilibriumJacobian p fold.βfold).smallerEigenvalue)) :=
    (continuousAt_warningSmallerEigenvalue model.c_pos.ne'
      (sub_pos.mpr hcβ).ne').tendsto.mono_left nhdsWithin_le_nhds
  have hotherTendsto : Tendsto otherGap L (𝓝 (otherGap fold.βfold)) :=
    tendsto_const_nhds.sub hsmallTendsto
  have hratioOther : Tendsto (fun β : ℝ => otherGap β / 1) L
      (𝓝 (otherGap fold.βfold)) := by simpa using hotherTendsto
  have honeThetaOther : (fun _ : ℝ => (1 : ℝ)) =Θ[L] otherGap :=
    isTheta_of_div_tendsto_nhds_ne_zero hratioOther hotherPos.ne'
  have hotherThetaOne : otherGap =Θ[L] (fun _ : ℝ => (1 : ℝ)) :=
    honeThetaOther.symm
  have hquotTheta :=
    (warningCharPolyOne_isTheta_policyGap model fold).div hotherThetaOne
  have hquotTheta' :
      (fun β : ℝ => warningCharPolyOne p β / otherGap β) =Θ[L]
        (fun β : ℝ => fold.βfold - β) := by
    simpa only [div_one] using hquotTheta
  have hgapEq :
      (fun β : ℝ => 1 - warningSlowEigenvalue p β) =ᶠ[L]
        (fun β : ℝ => warningCharPolyOne p β / otherGap β) := by
    filter_upwards [Ioo_mem_nhdsLT fold.βfold_mem.1] with β hβ
    exact warningSlowEigenvalue_gap_eq model
      ⟨hβ.1, hβ.2.trans fold.βfold_mem.2⟩
  exact hgapEq.trans_isTheta hquotTheta'

/--
The paper's literal square-root warning law for the slow eigenvalue of the
full simultaneous map.
-/
theorem warningSlowEigenvalue_sqrt_scaling {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) :
    (fun β : ℝ => 1 - warningSlowEigenvalue p β) =Θ[𝓝[<] fold.βfold]
      (fun β : ℝ => Real.sqrt
        (warningInjectionCurve p fold.βfold - warningInjectionCurve p β)) :=
  (warningSlowEigenvalue_gap_isTheta_policyGap model fold).trans
    (warningInjectionGap_sqrt_isTheta_policyGap model fold)

/-! ## Proposition-level assembly -/

/-- The strict captured-corner sign is exactly `I > warningInjectionCurve p 1`. -/
theorem warningPhi_one_gt_one_iff {p : LoopParams}
    (model : DriftModelAssumptions p) {I : ℝ} (hI : 0 < I) :
    1 < warningPhi p I 1 ↔ warningInjectionCurve p 1 < I := by
  have hphiDen := warningPhiDenominator_pos model hI (show (1 : ℝ) ∈ Icc 0 1 by
    norm_num)
  have hcurveDen : 0 < 2 * p.c * (1 - p.c) :=
    mul_pos (mul_pos two_pos model.c_pos) (sub_pos.mpr model.c_lt_one)
  simp only [warningPhi, warningInjectionCurve, mul_one]
  rw [lt_div_iff₀ hphiDen, div_lt_iff₀ hcurveDen]
  constructor <;> intro h <;> nlinarith

/-- Two distinct interior fixed policies force an intervening, unique-type fold. -/
theorem warningFold_exists_of_two_fixedPoints {p : LoopParams}
    (model : DriftModelAssumptions p) {I β₁ β₂ : ℝ} (hI : 0 < I)
    (hβ₁ : β₁ ∈ Ioo (0 : ℝ) 1) (hβ₂ : β₂ ∈ Ioo (0 : ℝ) 1)
    (horder : β₁ < β₂) (hfixed₁ : warningPhi p I β₁ = β₁)
    (hfixed₂ : warningPhi p I β₂ = β₂) :
    ∃ fold : WarningFold p, β₁ < fold.βfold ∧ fold.βfold < β₂ := by
  have hcurve₁ : I = warningInjectionCurve p β₁ :=
    (warningPhi_eq_self_iff model hI hβ₁).1 hfixed₁
  have hcurve₂ : I = warningInjectionCurve p β₂ :=
    (warningPhi_eq_self_iff model hI hβ₂).1 hfixed₂
  have hcont : ContinuousOn (warningInjectionCurve p) (Icc β₁ β₂) :=
    (warningInjectionCurve_continuousOn model).mono fun β hβ =>
      ⟨hβ₁.1.le.trans hβ.1, hβ.2.trans hβ₂.2.le⟩
  rcases exists_deriv_eq_zero horder hcont (hcurve₁.symm.trans hcurve₂) with
    ⟨βf, hbetween, hderiv⟩
  have hβf : βf ∈ Ioo (0 : ℝ) 1 :=
    ⟨hβ₁.1.trans hbetween.1, hbetween.2.trans hβ₂.2⟩
  have hcβ : p.c * βf < 1 := calc
    p.c * βf < p.c * 1 := mul_lt_mul_of_pos_left hβf.2 model.c_pos
    _ = p.c := mul_one _
    _ < 1 := model.c_lt_one
  rw [(hasDerivAt_warningInjectionCurve p βf model.c_pos.ne'
    (sub_pos.mpr hcβ).ne').deriv] at hderiv
  have hden : 0 < 2 * p.c * (1 - p.c * βf) ^ 2 :=
    mul_pos (mul_pos two_pos model.c_pos) (sq_pos_of_pos (sub_pos.mpr hcβ))
  have hnum : p.v * warningFoldNumerator p βf = 0 := by
    simp only [warningInjectionSlope] at hderiv
    exact (div_eq_zero_iff).1 hderiv |>.resolve_right hden.ne'
  have hcritical : warningFoldNumerator p βf = 0 :=
    (mul_eq_zero.mp hnum).resolve_left model.v_pos.ne'
  exact ⟨⟨βf, hβf, hcritical⟩, hbetween⟩

/-- Along the lower branch the slow eigenvalue lies strictly below one. -/
theorem warningSlowEigenvalue_lt_one_before_fold {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) {β : ℝ}
    (hβ : β ∈ Ioo (0 : ℝ) fold.βfold) :
    warningSlowEigenvalue p β < 1 := by
  have hβunit : β ∈ Ioo (0 : ℝ) 1 :=
    ⟨hβ.1, hβ.2.trans fold.βfold_mem.2⟩
  have hnum := warningFoldNumerator_pos_before model fold
    ⟨hβ.1.le, hβ.2.le.trans fold.βfold_mem.2.le⟩ hβ.2
  have hcβ : p.c * β < 1 := calc
    p.c * β < p.c * 1 := mul_lt_mul_of_pos_left hβunit.2 model.c_pos
    _ = p.c := mul_one _
    _ < 1 := model.c_lt_one
  let J := warningEquilibriumJacobian p β
  have hD : 0 < warningEquilibriumStock p β := by
    simp only [warningEquilibriumStock]
    exact div_pos (mul_pos model.v_pos hβ.1)
      (mul_pos (mul_pos two_pos model.c_pos) (sub_pos.mpr hcβ))
  have hb : 0 < J.b := by
    dsimp only [J, warningEquilibriumJacobian, warningJacobian]
    exact mul_pos (mul_pos (mul_pos model.α_pos two_pos) model.c_pos)
      (sub_pos.mpr hcβ)
  have hcJ : 0 < J.cJ := by
    dsimp only [J, warningEquilibriumJacobian, warningJacobian]
    exact mul_pos (sSlope_pos model hβunit) hD
  have hs := driftStockMultiplier_nonneg_le model ⟨hβunit.1.le, hβunit.2.le⟩
  have hd : J.d < 1 := by
    dsimp only [J, warningEquilibriumJacobian, warningJacobian]
    linarith [hs.2, model.lambda₀_pos]
  have hsmall : J.smallerEigenvalue < 1 :=
    J.smallerEigenvalue_lt_one hd (mul_nonneg hb.le hcJ.le)
  have hchar : 0 < warningCharPolyOne p β := by
    simp only [warningCharPolyOne]
    exact div_pos (mul_pos (mul_pos model.α_pos model.v_pos) hnum)
      (sub_pos.mpr hcβ)
  have hgap := warningSlowEigenvalue_gap_eq model hβunit
  have hother : 0 < 1 - J.smallerEigenvalue := sub_pos.mpr hsmall
  change warningSlowEigenvalue p β < 1
  rw [← sub_pos, hgap]
  exact div_pos hchar hother

/--
Paper II, Proposition `prop:warning`, `civic_drift.tex:656--669`.

For the quadratic-cost family, `φ` is pointwise strictly increasing in
injection.  If a fold exists, the exact injection curve has one fixed policy
on each side below the fold (whenever the captured corner has the strict
attracting sign), one coalesced policy at the fold, and none above it.  The
full simultaneous Jacobian has eigenvalue one at collision, approaches it
from below along the calibrated branch, and obeys the stated square-root
scaling in precise `Θ` notation.
-/
theorem earlyWarningNearFold {p : LoopParams}
    (model : DriftModelAssumptions p) (fold : WarningFold p) :
    (∀ β ∈ Icc (0 : ℝ) 1,
      StrictMonoOn (fun I : ℝ => warningPhi p I β) (Ioi 0)) ∧
    (∀ I : ℝ, warningInjectionCurve p 1 < I →
      I < warningInjectionCurve p fold.βfold →
        (∃! β : ℝ, β ∈ Ioo (0 : ℝ) fold.βfold ∧ warningPhi p I β = β) ∧
        (∃! β : ℝ, β ∈ Ioo fold.βfold 1 ∧ warningPhi p I β = β)) ∧
    (∀ β ∈ Ioo (0 : ℝ) 1,
      (warningPhi p (warningInjectionCurve p fold.βfold) β = β ↔
        β = fold.βfold)) ∧
    (∀ I : ℝ, warningInjectionCurve p fold.βfold < I →
      ∀ β ∈ Ioo (0 : ℝ) 1, warningPhi p I β ≠ β) ∧
    0 < warningInjectionGapScale p fold.βfold fold.βfold ∧
    warningSlowEigenvalue p fold.βfold = 1 ∧
    (∀ β ∈ Ioo (0 : ℝ) fold.βfold, warningSlowEigenvalue p β < 1) ∧
    ((fun β : ℝ => 1 - warningSlowEigenvalue p β) =Θ[𝓝[<] fold.βfold]
      (fun β : ℝ => Real.sqrt
        (warningInjectionCurve p fold.βfold - warningInjectionCurve p β))) := by
  refine ⟨fun β hβ => warningPhi_strictMonoOn_injection model β hβ,
    fun I hcaptured hbelow =>
      ⟨warning_existsUnique_lower_fixedPoint model fold hcaptured hbelow,
        warning_existsUnique_upper_fixedPoint model fold hcaptured hbelow⟩,
    fun β hβ => warning_fold_unique_fixedPoint model fold hβ,
    fun I habove β hβ => warning_no_fixedPoint_above_fold model fold habove hβ,
    warningInjectionGapScale_pos model fold
      ⟨fold.βfold_mem.1.le, fold.βfold_mem.2.le⟩,
    warningFold_largerEigenvalue_eq_one model fold,
    fun β hβ => warningSlowEigenvalue_lt_one_before_fold model fold hβ,
    warningSlowEigenvalue_sqrt_scaling model fold⟩

#print axioms warningPhi_eq_stockForm
#print axioms warningStockDenominator_pos
#print axioms warningPhiDenominator_pos
#print axioms warningPhi_strictMonoOn_injection
#print axioms warningPhi_eq_self_iff
#print axioms hasDerivAt_warning_sSlope
#print axioms hasDerivAt_warningFoldNumerator
#print axioms hasDerivAt_warningInjectionCurve
#print axioms warningStockCurvature_pos
#print axioms warningFoldNumerator_deriv_neg
#print axioms warningFoldNumerator_strictAntiOn
#print axioms warningFoldNumerator_pos_before
#print axioms warningFoldNumerator_neg_after
#print axioms warningInjectionCurve_continuousOn
#print axioms warningInjectionCurve_strictMonoOn_before
#print axioms warningInjectionCurve_strictAntiOn_after
#print axioms warningInjectionCurve_fold_gap_eq
#print axioms warningInjectionCurve_zero
#print axioms warningInjectionCurve_one_pos
#print axioms warningInjectionCurve_le_fold
#print axioms warningInjectionCurve_eq_fold_iff
#print axioms warning_existsUnique_lower_fixedPoint
#print axioms warning_existsUnique_upper_fixedPoint
#print axioms warning_fold_unique_fixedPoint
#print axioms warning_no_fixedPoint_above_fold
#print axioms warningStationaryStock_on_injectionCurve
#print axioms warningEquilibriumJacobian_charPoly_one_eq
#print axioms warningEquilibriumJacobian_fold_entry_bounds
#print axioms warningFold_largerEigenvalue_eq_one
#print axioms warningFold_smallerEigenvalue_lt_one
#print axioms hasDerivAt_warningCharPolyOne_at_fold
#print axioms warningCharPolyOne_fold_deriv_neg
#print axioms continuousAt_warningSmallerEigenvalue
#print axioms warningSlowEigenvalue_gap_eq
#print axioms warningInjectionGapScale_pos
#print axioms continuousAt_warningInjectionGapScale
#print axioms warningInjectionGap_sqrt_isTheta_policyGap
#print axioms warningCharPolyOne_isTheta_policyGap
#print axioms warningSlowEigenvalue_gap_isTheta_policyGap
#print axioms warningSlowEigenvalue_sqrt_scaling
#print axioms warningPhi_one_gt_one_iff
#print axioms warningFold_exists_of_two_fixedPoints
#print axioms warningSlowEigenvalue_lt_one_before_fold
#print axioms earlyWarningNearFold

end

end CivicAlignment.PaperII
