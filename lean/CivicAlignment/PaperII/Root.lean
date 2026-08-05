/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.Bistability
import Mathlib.Topology.Order.IntermediateValue

/-!
# Paper II: the threshold is automatic

The endpoint signs in assumption `(H)` force the complete oriented threshold
structure.  The proof works through the positive-leading quadratic obtained by
clearing the stationary-stock denominator.  A weighted version is exported for
the quasipotential results later in Paper II.
-/

namespace CivicAlignment.PaperII

open Set

noncomputable section

/-! ## A reusable quadratic lemma -/

/-- A quadratic written by its three coefficients. -/
def quadraticValue (A B C x : ℝ) : ℝ := A * x ^ 2 + B * x + C

/-- Difference factorization for a quadratic. -/
theorem quadraticValue_sub (A B C x r : ℝ) :
    quadraticValue A B C x - quadraticValue A B C r =
      (x - r) * (A * (x + r) + B) := by
  simp only [quadraticValue]
  ring

/-- A positive-leading quadratic which is negative at zero and positive at one
has one interior root.  It is an ascending transversal crossing, with the
literal signs on either side. -/
theorem quadratic_unique_ascending_root_of_endpoint_signs
    {A B C : ℝ} (hA : 0 < A)
    (hzero : quadraticValue A B C 0 < 0)
    (hone : 0 < quadraticValue A B C 1) :
    ∃ r ∈ Ioo (0 : ℝ) 1,
      quadraticValue A B C r = 0 ∧
      0 < 2 * A * r + B ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, x < r → quadraticValue A B C x < 0) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, r < x → 0 < quadraticValue A B C x) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, quadraticValue A B C x = 0 → x = r) := by
  let q : ℝ → ℝ := quadraticValue A B C
  have hcont : Continuous q := by
    change Continuous (fun x : ℝ => A * x ^ 2 + B * x + C)
    fun_prop
  have hrange : (0 : ℝ) ∈ Icc (q 0) (q 1) := ⟨hzero.le, hone.le⟩
  obtain ⟨r, hrclosed, hroot⟩ :=
    intermediate_value_Icc (zero_le_one (α := ℝ)) hcont.continuousOn hrange
  have hrzero : r ≠ 0 := by
    intro hr
    subst r
    linarith
  have hrone : r ≠ 1 := by
    intro hr
    subst r
    linarith
  have hr : r ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hrclosed.1 (Ne.symm hrzero),
      lt_of_le_of_ne hrclosed.2 hrone⟩
  have hC : C < 0 := by
    simpa [q, quadraticValue] using hzero
  have hroot' : quadraticValue A B C r = 0 := by
    simpa only [q] using hroot
  have hrootExpanded : A * r ^ 2 + B * r + C = 0 := by
    simpa only [q, quadraticValue] using hroot
  have hproduct : 0 < r * (A * r + B) := by
    nlinarith
  have hbracket : 0 < A * r + B := by
    rcases mul_pos_iff.mp hproduct with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge hr.1.le hneg.1).elim
  have hslope : 0 < 2 * A * r + B := by
    nlinarith [mul_pos hA hr.1]
  have hbefore : ∀ x ∈ Ioo (0 : ℝ) 1, x < r →
      quadraticValue A B C x < 0 := by
    intro x hx hxr
    have hcoefficient : 0 < A * (x + r) + B := by
      nlinarith [mul_pos hA hx.1]
    have hfactor : (x - r) * (A * (x + r) + B) < 0 :=
      mul_neg_of_neg_of_pos (sub_neg.mpr hxr) hcoefficient
    have hdiff := quadraticValue_sub A B C x r
    rw [hroot', sub_zero] at hdiff
    rwa [hdiff]
  have hafter : ∀ x ∈ Ioo (0 : ℝ) 1, r < x →
      0 < quadraticValue A B C x := by
    intro x hx hrx
    have hcoefficient : 0 < A * (x + r) + B := by
      nlinarith [mul_pos hA hx.1]
    have hfactor : 0 < (x - r) * (A * (x + r) + B) :=
      mul_pos (sub_pos.mpr hrx) hcoefficient
    have hdiff := quadraticValue_sub A B C x r
    rw [hroot', sub_zero] at hdiff
    rwa [hdiff]
  have hunique : ∀ x ∈ Ioo (0 : ℝ) 1,
      quadraticValue A B C x = 0 → x = r := by
    intro x hx hxroot
    rcases lt_trichotomy x r with hxr | hxr | hrx
    · linarith [hbefore x hx hxr]
    · exact hxr
    · linarith [hafter x hx hrx]
  exact ⟨r, hr, hroot', hslope, hbefore, hafter, hunique⟩

/-! ## The unweighted stationary numerator -/

/-- The numerator `q = G(1-s)` in Paper II's proof of `lem:root`. -/
def thresholdNumerator (p : LoopParams) (β : ℝ) : ℝ :=
  2 * p.c * (1 - p.c * β) * p.I - p.v * (1 - p.s β)

/-- The derivative of `thresholdNumerator`. -/
def thresholdNumeratorSlope (p : LoopParams) (β : ℝ) : ℝ :=
  -2 * p.c ^ 2 * p.I + p.v * p.sSlope β

/-- The positive leading coefficient of the threshold numerator. -/
def thresholdQuadraticCoefficient (p : LoopParams) : ℝ :=
  p.v * (1 - p.lambda₀) * p.η ^ 2

/-- The linear coefficient of the threshold numerator. -/
def thresholdLinearCoefficient (p : LoopParams) : ℝ :=
  2 * p.v * (1 - p.lambda₀) * p.η * (1 - p.η) -
    2 * p.c ^ 2 * p.I

/-- The constant coefficient of the threshold numerator. -/
def thresholdConstantCoefficient (p : LoopParams) : ℝ :=
  2 * p.c * p.I - p.v +
    p.v * (1 - p.lambda₀) * (1 - p.η) ^ 2

/-- Clearing the positive denominator exposes an exact quadratic. -/
theorem thresholdNumerator_eq_quadratic (p : LoopParams) (β : ℝ) :
    thresholdNumerator p β =
      quadraticValue (thresholdQuadraticCoefficient p)
        (thresholdLinearCoefficient p) (thresholdConstantCoefficient p) β := by
  simp only [thresholdNumerator, quadraticValue, thresholdQuadraticCoefficient,
    thresholdLinearCoefficient, thresholdConstantCoefficient, LoopParams.s]
  ring

/-- The algebraic numerator slope is the derivative of that quadratic. -/
theorem thresholdNumeratorSlope_eq_quadraticSlope (p : LoopParams) (β : ℝ) :
    thresholdNumeratorSlope p β =
      2 * thresholdQuadraticCoefficient p * β + thresholdLinearCoefficient p := by
  simp only [thresholdNumeratorSlope, thresholdQuadraticCoefficient,
    thresholdLinearCoefficient, LoopParams.sSlope]
  ring

/-- Paper II's primitive restrictions make the quadratic coefficient strictly
positive, including at the permitted endpoint `η = 1`. -/
theorem thresholdQuadraticCoefficient_pos {p : LoopParams}
    (model : DriftModelAssumptions p) :
    0 < thresholdQuadraticCoefficient p := by
  simp only [thresholdQuadraticCoefficient]
  exact mul_pos (mul_pos model.v_pos (sub_pos.mpr model.lambda₀_lt_one))
    (sq_pos_of_pos model.η_pos)

/-- The stationary denominator is positive throughout `[0,1]`. -/
theorem thresholdDenominator_pos {p : LoopParams}
    (model : DriftModelAssumptions p) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 < 1 - p.s β := by
  have hs := driftStockMultiplier_nonneg_le model hβ
  linarith [model.lambda₀_pos]

/-- On the policy interval, `G` is the threshold numerator divided by its
strictly positive denominator. -/
theorem G_eq_thresholdNumerator_div {p : LoopParams}
    (model : DriftModelAssumptions p) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    p.G β = thresholdNumerator p β / (1 - p.s β) := by
  have hden := thresholdDenominator_pos model hβ
  simp only [LoopParams.G, thresholdNumerator, model.no_content_gain, sub_zero]
  field_simp [hden.ne']
  ring

/-- `G` and its cleared numerator have the same negative sign. -/
theorem G_neg_iff_thresholdNumerator_neg {p : LoopParams}
    (model : DriftModelAssumptions p) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    p.G β < 0 ↔ thresholdNumerator p β < 0 := by
  rw [G_eq_thresholdNumerator_div model hβ]
  have hden := thresholdDenominator_pos model hβ
  constructor
  · intro h
    rcases div_neg_iff.mp h with hsign | hsign
    · exact (not_lt_of_ge hden.le hsign.2).elim
    · exact hsign.1
  · intro h
    exact div_neg_of_neg_of_pos h hden

/-- `G` and its cleared numerator have the same positive sign. -/
theorem G_pos_iff_thresholdNumerator_pos {p : LoopParams}
    (model : DriftModelAssumptions p) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 < p.G β ↔ 0 < thresholdNumerator p β := by
  rw [G_eq_thresholdNumerator_div model hβ]
  have hden := thresholdDenominator_pos model hβ
  constructor
  · intro h
    rcases div_pos_iff.mp h with hsign | hsign
    · exact hsign.1
    · exact (not_lt_of_ge hden.le hsign.2).elim
  · intro h
    exact div_pos h hden

/-- Roots of `G` and of its numerator agree on the policy interval. -/
theorem G_eq_zero_iff_thresholdNumerator_eq_zero {p : LoopParams}
    (model : DriftModelAssumptions p) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    p.G β = 0 ↔ thresholdNumerator p β = 0 := by
  rw [G_eq_thresholdNumerator_div model hβ]
  have hden := thresholdDenominator_pos model hβ
  simp only [div_eq_zero_iff, hden.ne', or_false]

/-- At a root, the actual stationary-gradient derivative is the numerator
derivative divided by the positive denominator. -/
theorem GSlope_eq_thresholdNumeratorSlope_div_at_root {p : LoopParams}
    (model : DriftModelAssumptions p) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1)
    (hroot : thresholdNumerator p r = 0) :
    p.GSlope r = thresholdNumeratorSlope p r / (1 - p.s r) := by
  have hden := thresholdDenominator_pos model hr
  simp only [LoopParams.GSlope, thresholdNumeratorSlope, model.no_content_gain,
    sub_zero]
  field_simp [hden.ne']
  simp only [thresholdNumerator] at hroot
  linear_combination p.sSlope r * hroot

/-- Paper II, Lemma `lem:root`, `civic_drift.tex:214`: endpoint assumption
`(H)` automatically constructs the unique, transversally ascending threshold
structure. -/
theorem thresholdAutomatic {p : LoopParams} (model : DriftModelAssumptions p)
    (hzero : p.G 0 < 0) (hone : 0 < p.G 1) :
    Nonempty (ThresholdAssumption p) := by
  have hnumZero : thresholdNumerator p 0 < 0 :=
    (G_neg_iff_thresholdNumerator_neg model (by norm_num)).mp hzero
  have hnumOne : 0 < thresholdNumerator p 1 :=
    (G_pos_iff_thresholdNumerator_pos model (by norm_num)).mp hone
  have hpolyZero : quadraticValue (thresholdQuadraticCoefficient p)
      (thresholdLinearCoefficient p) (thresholdConstantCoefficient p) 0 < 0 := by
    rwa [← thresholdNumerator_eq_quadratic]
  have hpolyOne : 0 < quadraticValue (thresholdQuadraticCoefficient p)
      (thresholdLinearCoefficient p) (thresholdConstantCoefficient p) 1 := by
    rwa [← thresholdNumerator_eq_quadratic]
  obtain ⟨β, hβ, hpolyRoot, hpolySlope, hpolyBefore, hpolyAfter, _hunique⟩ :=
    quadratic_unique_ascending_root_of_endpoint_signs
      (thresholdQuadraticCoefficient_pos model) hpolyZero hpolyOne
  have hβclosed : β ∈ Icc (0 : ℝ) 1 := ⟨hβ.1.le, hβ.2.le⟩
  have hnumRoot : thresholdNumerator p β = 0 := by
    rw [thresholdNumerator_eq_quadratic]
    exact hpolyRoot
  have hGroot : p.G β = 0 :=
    (G_eq_zero_iff_thresholdNumerator_eq_zero model hβclosed).mpr hnumRoot
  have hnumSlope : 0 < thresholdNumeratorSlope p β := by
    rw [thresholdNumeratorSlope_eq_quadraticSlope]
    exact hpolySlope
  have hGSlope : 0 < p.GSlope β := by
    rw [GSlope_eq_thresholdNumeratorSlope_div_at_root model hβclosed hnumRoot]
    exact div_pos hnumSlope (thresholdDenominator_pos model hβclosed)
  refine ⟨{
    βdagger := β
    βdagger_mem := hβ
    G_zero := hGroot
    G_zero_neg := hzero
    G_one_pos := hone
    G_neg_before := ?_
    G_pos_after := ?_
    GSlope_pos := hGSlope }⟩
  · intro x hx hxβ
    apply (G_neg_iff_thresholdNumerator_neg model ⟨hx.1.le, hx.2.le⟩).mpr
    rw [thresholdNumerator_eq_quadratic]
    exact hpolyBefore x hx hxβ
  · intro x hx hβx
    apply (G_pos_iff_thresholdNumerator_pos model ⟨hx.1.le, hx.2.le⟩).mpr
    rw [thresholdNumerator_eq_quadratic]
    exact hpolyAfter x hx hβx

/-- A convenient chosen threshold bundle obtained from the two endpoint signs. -/
noncomputable def thresholdAssumptionOfEndpointSigns {p : LoopParams}
    (model : DriftModelAssumptions p) (hzero : p.G 0 < 0) (hone : 0 < p.G 1) :
    ThresholdAssumption p :=
  Classical.choice (thresholdAutomatic model hzero hone)

/-- The oriented sign fields make the threshold root literally unique. -/
theorem ThresholdAssumption.G_eq_zero_iff {p : LoopParams}
    (threshold : ThresholdAssumption p) {β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1) :
    p.G β = 0 ↔ β = threshold.βdagger := by
  constructor
  · intro hroot
    rcases lt_trichotomy β threshold.βdagger with hbefore | heq | hafter
    · linarith [threshold.G_neg_before β hβ hbefore]
    · exact heq
    · linarith [threshold.G_pos_after β hβ hafter]
  · rintro rfl
    exact threshold.G_zero

/-! ## Civic-weighted threshold -/

/-- The stationary gradient after adding civic weight `ρ`. -/
def weightedStationaryGradient (p : LoopParams) (ρ β : ℝ) : ℝ :=
  p.G β - ρ * p.stationaryStock β

/-- Its exact algebraic derivative under Paper II's zero-content-gain model. -/
def weightedStationaryGradientSlope (p : LoopParams) (ρ β : ℝ) : ℝ :=
  p.GSlope β - ρ * (p.I * p.sSlope β / (1 - p.s β) ^ 2)

/-- The cleared weighted numerator `qρ = q - ρI`. -/
def weightedThresholdNumerator (p : LoopParams) (ρ β : ℝ) : ℝ :=
  thresholdNumerator p β - ρ * p.I

/-- The weighted numerator remains a quadratic with the same positive leading
and linear coefficients. -/
theorem weightedThresholdNumerator_eq_quadratic (p : LoopParams) (ρ β : ℝ) :
    weightedThresholdNumerator p ρ β =
      quadraticValue (thresholdQuadraticCoefficient p)
        (thresholdLinearCoefficient p) (thresholdConstantCoefficient p - ρ * p.I) β := by
  rw [weightedThresholdNumerator, thresholdNumerator_eq_quadratic]
  simp only [quadraticValue]
  ring

/-- The weighted stationary gradient is its numerator divided by the positive
stationary denominator. -/
theorem weightedStationaryGradient_eq_numerator_div {p : LoopParams}
    (model : DriftModelAssumptions p) (ρ : ℝ) {β : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) :
    weightedStationaryGradient p ρ β =
      weightedThresholdNumerator p ρ β / (1 - p.s β) := by
  have hden := thresholdDenominator_pos model hβ
  simp only [weightedStationaryGradient, weightedThresholdNumerator,
    LoopParams.stationaryStock, model.no_content_gain, sub_zero]
  rw [G_eq_thresholdNumerator_div model hβ]
  field_simp [hden.ne']

/-- Exact derivative of the stationary stock under Paper II's zero-gain law. -/
theorem hasDerivAt_stationaryStock_zeroGain {p : LoopParams}
    (model : DriftModelAssumptions p) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    HasDerivAt p.stationaryStock
      (p.I * p.sSlope β / (1 - p.s β) ^ 2) β := by
  have hdenPos := thresholdDenominator_pos model hβ
  have hden : HasDerivAt (fun x : ℝ ↦ 1 - p.s x) (-p.sSlope β) β := by
    convert (p.hasDerivAt_s β).const_sub (1 : ℝ) using 1
  have hquot := (hasDerivAt_const β p.I).div hden hdenPos.ne'
  convert! hquot using 1
  · funext x
    simp only [LoopParams.stationaryStock, model.no_content_gain, sub_zero]
    change p.I / (1 - p.s x) = p.I / (1 - p.s x)
    rfl
  · ring

/-- `weightedStationaryGradientSlope` is the actual derivative. -/
theorem hasDerivAt_weightedStationaryGradient {p : LoopParams}
    (model : DriftModelAssumptions p) (ρ : ℝ) {β : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (weightedStationaryGradient p ρ)
      (weightedStationaryGradientSlope p ρ β) β := by
  have hden := thresholdDenominator_pos model hβ
  have hG := p.hasDerivAt_G β (by
    simpa only [model.no_content_gain, sub_zero] using hden.ne')
  have hstock := hasDerivAt_stationaryStock_zeroGain model hβ
  change HasDerivAt (fun x : ℝ => p.G x - ρ * p.stationaryStock x)
    (p.GSlope β - ρ * (p.I * p.sSlope β / (1 - p.s β) ^ 2)) β
  exact hG.sub (hstock.const_mul ρ)

/-- At a weighted root, the actual derivative is the numerator slope divided
by the positive denominator. -/
theorem weightedStationaryGradientSlope_eq_numeratorSlope_div_at_root
    {p : LoopParams} (model : DriftModelAssumptions p) (ρ : ℝ) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1)
    (hroot : weightedThresholdNumerator p ρ r = 0) :
    weightedStationaryGradientSlope p ρ r =
      thresholdNumeratorSlope p r / (1 - p.s r) := by
  have hden := thresholdDenominator_pos model hr
  simp only [weightedStationaryGradientSlope, LoopParams.GSlope,
    thresholdNumeratorSlope, model.no_content_gain, sub_zero]
  field_simp [hden.ne']
  simp only [weightedThresholdNumerator, thresholdNumerator] at hroot
  linear_combination p.sSlope r * hroot

/-- At capture, `qρ(1) = I(ρ_cure-ρ)`. -/
theorem weightedThresholdNumerator_one_eq {p : LoopParams}
    (model : DriftModelAssumptions p) (ρ : ℝ) :
    weightedThresholdNumerator p ρ 1 = p.I * (cureThreshold p - ρ) := by
  simp only [weightedThresholdNumerator, thresholdNumerator, cureThreshold,
    LoopParams.s, mul_one]
  field_simp [model.I_pos.ne']
  ring

/-- Consequently `qρ(1)>0` exactly below the cure price. -/
theorem weightedThresholdNumerator_one_pos_iff {p : LoopParams}
    (model : DriftModelAssumptions p) (ρ : ℝ) :
    0 < weightedThresholdNumerator p ρ 1 ↔ ρ < cureThreshold p := by
  rw [weightedThresholdNumerator_one_eq model]
  exact (mul_pos_iff_of_pos_left model.I_pos).trans sub_pos

/-- The complete oriented threshold bundle for a civic-weighted stationary
gradient. -/
structure WeightedThresholdAssumption (p : LoopParams) (ρ : ℝ) where
  βdagger : ℝ
  βdagger_mem : βdagger ∈ Ioo (0 : ℝ) 1
  gradient_zero : weightedStationaryGradient p ρ βdagger = 0
  gradient_zero_neg : weightedStationaryGradient p ρ 0 < 0
  gradient_one_pos : 0 < weightedStationaryGradient p ρ 1
  gradient_neg_before : ∀ β ∈ Ioo (0 : ℝ) 1, β < βdagger →
    weightedStationaryGradient p ρ β < 0
  gradient_pos_after : ∀ β ∈ Ioo (0 : ℝ) 1, βdagger < β →
    0 < weightedStationaryGradient p ρ β
  gradientSlope_pos : 0 < weightedStationaryGradientSlope p ρ βdagger

/-- Paper II, algebraic crossing clause of Proposition `prop:qpbounds`,
`civic_drift.tex:354`: below `ρ_cure`, every nonnegative civic weight has
exactly one interior, transversally ascending stationary crossing. -/
theorem weightedThresholdAutomatic {p : LoopParams}
    (model : DriftModelAssumptions p) (threshold : ThresholdAssumption p)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρcure : ρ < cureThreshold p) :
    Nonempty (WeightedThresholdAssumption p ρ) := by
  have hnumZeroBase : thresholdNumerator p 0 < 0 :=
    (G_neg_iff_thresholdNumerator_neg model (by norm_num)).mp threshold.G_zero_neg
  have hnumZero : weightedThresholdNumerator p ρ 0 < 0 := by
    simp only [weightedThresholdNumerator]
    have hρI : 0 ≤ ρ * p.I := mul_nonneg hρ model.I_pos.le
    linarith
  have hnumOne : 0 < weightedThresholdNumerator p ρ 1 :=
    (weightedThresholdNumerator_one_pos_iff model ρ).mpr hρcure
  have hpolyZero : quadraticValue (thresholdQuadraticCoefficient p)
      (thresholdLinearCoefficient p)
      (thresholdConstantCoefficient p - ρ * p.I) 0 < 0 := by
    rwa [← weightedThresholdNumerator_eq_quadratic]
  have hpolyOne : 0 < quadraticValue (thresholdQuadraticCoefficient p)
      (thresholdLinearCoefficient p)
      (thresholdConstantCoefficient p - ρ * p.I) 1 := by
    rwa [← weightedThresholdNumerator_eq_quadratic]
  obtain ⟨β, hβ, hpolyRoot, hpolySlope, hpolyBefore, hpolyAfter, _hunique⟩ :=
    quadratic_unique_ascending_root_of_endpoint_signs
      (thresholdQuadraticCoefficient_pos model) hpolyZero hpolyOne
  have hβclosed : β ∈ Icc (0 : ℝ) 1 := ⟨hβ.1.le, hβ.2.le⟩
  have hnumRoot : weightedThresholdNumerator p ρ β = 0 := by
    rw [weightedThresholdNumerator_eq_quadratic]
    exact hpolyRoot
  have hgradientRoot : weightedStationaryGradient p ρ β = 0 := by
    rw [weightedStationaryGradient_eq_numerator_div model ρ hβclosed, hnumRoot,
      zero_div]
  have hnumSlope : 0 < thresholdNumeratorSlope p β := by
    rw [thresholdNumeratorSlope_eq_quadraticSlope]
    exact hpolySlope
  have hgradientSlope : 0 < weightedStationaryGradientSlope p ρ β := by
    rw [weightedStationaryGradientSlope_eq_numeratorSlope_div_at_root
      model ρ hβclosed hnumRoot]
    exact div_pos hnumSlope (thresholdDenominator_pos model hβclosed)
  have hweightedSign {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
      weightedStationaryGradient p ρ x =
        weightedThresholdNumerator p ρ x / (1 - p.s x) :=
    weightedStationaryGradient_eq_numerator_div model ρ hx
  refine ⟨{
    βdagger := β
    βdagger_mem := hβ
    gradient_zero := hgradientRoot
    gradient_zero_neg := ?_
    gradient_one_pos := ?_
    gradient_neg_before := ?_
    gradient_pos_after := ?_
    gradientSlope_pos := hgradientSlope }⟩
  · rw [hweightedSign (by norm_num)]
    exact div_neg_of_neg_of_pos hnumZero (thresholdDenominator_pos model (by norm_num))
  · rw [hweightedSign (by norm_num)]
    exact div_pos hnumOne (thresholdDenominator_pos model (by norm_num))
  · intro x hx hxβ
    rw [hweightedSign ⟨hx.1.le, hx.2.le⟩]
    apply div_neg_of_neg_of_pos
    · rw [weightedThresholdNumerator_eq_quadratic]
      exact hpolyBefore x hx hxβ
    · exact thresholdDenominator_pos model ⟨hx.1.le, hx.2.le⟩
  · intro x hx hβx
    rw [hweightedSign ⟨hx.1.le, hx.2.le⟩]
    apply div_pos
    · rw [weightedThresholdNumerator_eq_quadratic]
      exact hpolyAfter x hx hβx
    · exact thresholdDenominator_pos model ⟨hx.1.le, hx.2.le⟩

/-- A chosen weighted threshold bundle for downstream constructions. -/
noncomputable def weightedThresholdAssumptionOfBelowCure {p : LoopParams}
    (model : DriftModelAssumptions p) (threshold : ThresholdAssumption p)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρcure : ρ < cureThreshold p) :
    WeightedThresholdAssumption p ρ :=
  Classical.choice (weightedThresholdAutomatic model threshold hρ hρcure)

/-- The weighted oriented sign fields make the crossing literally unique. -/
theorem WeightedThresholdAssumption.gradient_eq_zero_iff {p : LoopParams}
    {ρ : ℝ} (threshold : WeightedThresholdAssumption p ρ) {β : ℝ}
    (hβ : β ∈ Ioo (0 : ℝ) 1) :
    weightedStationaryGradient p ρ β = 0 ↔ β = threshold.βdagger := by
  constructor
  · intro hroot
    rcases lt_trichotomy β threshold.βdagger with hbefore | heq | hafter
    · linarith [threshold.gradient_neg_before β hβ hbefore]
    · exact heq
    · linarith [threshold.gradient_pos_after β hβ hafter]
  · rintro rfl
    exact threshold.gradient_zero

#print axioms quadraticValue_sub
#print axioms quadratic_unique_ascending_root_of_endpoint_signs
#print axioms thresholdNumerator_eq_quadratic
#print axioms thresholdNumeratorSlope_eq_quadraticSlope
#print axioms thresholdQuadraticCoefficient_pos
#print axioms thresholdDenominator_pos
#print axioms G_eq_thresholdNumerator_div
#print axioms G_neg_iff_thresholdNumerator_neg
#print axioms G_pos_iff_thresholdNumerator_pos
#print axioms G_eq_zero_iff_thresholdNumerator_eq_zero
#print axioms GSlope_eq_thresholdNumeratorSlope_div_at_root
#print axioms thresholdAutomatic
#print axioms ThresholdAssumption.G_eq_zero_iff
#print axioms weightedThresholdNumerator_eq_quadratic
#print axioms weightedStationaryGradient_eq_numerator_div
#print axioms hasDerivAt_stationaryStock_zeroGain
#print axioms hasDerivAt_weightedStationaryGradient
#print axioms weightedStationaryGradientSlope_eq_numeratorSlope_div_at_root
#print axioms weightedThresholdNumerator_one_eq
#print axioms weightedThresholdNumerator_one_pos_iff
#print axioms weightedThresholdAutomatic
#print axioms WeightedThresholdAssumption.gradient_eq_zero_iff

end


end CivicAlignment.PaperII
