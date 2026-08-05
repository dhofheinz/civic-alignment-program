/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.BistabilityTheorem
import CivicAlignment.PaperIII.AbsorbingCeiling
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

/-!
# Paper III: loop classification

The exact Paper II period-two orbit is the `g = 0` specialization of Paper
III's loop.  It therefore also refutes the unconditional convergence clause of
`thm:classify`, despite satisfying strict `(SS_g)` and remaining inside the
monotonicity-ceiling box.
-/

namespace CivicAlignment.PaperIII

open Set

noncomputable section

/-- The exact two-cycle parameters satisfy Paper III's primitive assumptions. -/
theorem classificationCycle_model :
    LoopModelAssumptions PaperII.bistabilityCycleParams := by
  constructor <;> norm_num [PaperII.bistabilityCycleParams]

/-- The exact two-cycle parameters satisfy strict `(SS_g)`. -/
theorem classificationCycle_strictStepSize :
    StrictStepSize PaperII.bistabilityCycleParams := by
  constructor
  norm_num [PaperII.bistabilityCycleParams]

/-- The content-gain restriction is strict in the exact `g = 0` counterexample. -/
theorem classificationCycle_gain_lt_lambda :
    PaperII.bistabilityCycleParams.g < PaperII.bistabilityCycleParams.lambda₀ := by
  norm_num [PaperII.bistabilityCycleParams]

/-- The same alternating sequence is a Paper III loop orbit. -/
theorem classificationCycle_isOrbit :
    IsLoopOrbit PaperII.bistabilityCycleParams PaperII.bistabilityCycleTrajectory := by
  simpa only [IsLoopOrbit, PaperII.IsLoopTrajectory] using
    PaperII.bistabilityCycle_isTrajectory

/-- Every state of the exact two-cycle lies in Paper III's enlarged cooperative box. -/
theorem classificationCycle_mem_ceilingBox (n : ℕ) :
    PaperII.bistabilityCycleTrajectory n ∈
      ceilingBox PaperII.bistabilityCycleParams := by
  have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hmod with hzero | hone
  · simp [PaperII.bistabilityCycleTrajectory, hzero, ceilingBox,
      monotonicityCeiling, PaperII.bistabilityCycleParams,
      PaperII.bistabilityCycleLower]
    norm_num
  · simp [PaperII.bistabilityCycleTrajectory, hone, ceilingBox,
      monotonicityCeiling, PaperII.bistabilityCycleParams,
      PaperII.bistabilityCycleUpper]
    norm_num

/--
Paper III, Theorem 2.2 (`thm:classify`), convergence counterexample,
`civic_loops.tex:130--182`.

Strict `(SS_g)` and all primitive assumptions hold, but this orbit alternates
between two distinct states inside `B*`; its policy coordinate does not
converge.  Thus cooperativity and compact absorption do not imply convergence
for this discrete-time map.
-/
theorem classification_global_convergence_counterexample :
    IsLoopOrbit PaperII.bistabilityCycleParams PaperII.bistabilityCycleTrajectory ∧
      (∀ n, PaperII.bistabilityCycleTrajectory n ∈
        ceilingBox PaperII.bistabilityCycleParams) ∧
      ¬PaperII.PolicyCoordinateConverges PaperII.bistabilityCycleTrajectory :=
  ⟨classificationCycle_isOrbit, classificationCycle_mem_ceilingBox,
    PaperII.bistabilityCycle_policy_not_convergent⟩

/-! ## Zone structure: scalar core -/

/-- Paper III's zone function `F(β)=2c(1-cβ)I/(1-s(β)-g)`. -/
def zoneForce (p : LoopParams) (β : ℝ) : ℝ :=
  2 * p.c * (1 - p.c * β) * p.I / (1 - p.s β - p.g)

/-- The quadratic numerator whose sign agrees with `G` below the gain ceiling. -/
def zoneNumerator (p : LoopParams) (β : ℝ) : ℝ :=
  2 * p.c * (1 - p.c * β) * p.I - p.v * (1 - p.s β - p.g)

/-- The derivative of the quadratic zone numerator. -/
def zoneNumeratorSlope (p : LoopParams) (β : ℝ) : ℝ :=
  -2 * p.c ^ 2 * p.I + p.v * p.sSlope β

/-- The strictly positive leading coefficient of the zone numerator. -/
def zoneQuadraticCoefficient (p : LoopParams) : ℝ :=
  p.v * (1 - p.lambda₀) * p.η ^ 2

/-- Zone (A), stated without choosing a particular maximizer. -/
def CalibrationZone (p : LoopParams) : Prop :=
  ∀ β ∈ Icc (0 : ℝ) 1, zoneForce p β ≤ p.v

/-- Zone (B)'s exact scalar inequalities: the endpoint is below `v`, an interior point is not. -/
def PartialCaptureBand (p : LoopParams) : Prop :=
  zoneForce p 1 ≤ p.v ∧ ∃ β ∈ Ioo (0 : ℝ) 1, p.v < zoneForce p β

/-- Zone (C), below the captured-corner line. -/
def CaptureZone (p : LoopParams) : Prop :=
  p.v < zoneForce p 1

/-- Below the gain ceiling, the stationary denominator is positive on the policy interval. -/
theorem zoneDenominator_pos {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 < 1 - p.s β - p.g := by
  have hs := stockMultiplier_nonneg_le model hβ
  linarith

/-- The paper's stationary gradient is exactly `-v+F`. -/
theorem G_eq_neg_v_add_zoneForce (p : LoopParams) (β : ℝ) :
    p.G β = -p.v + zoneForce p β := by
  rfl

/-- The zero equation for `G` is an exact quadratic numerator equation. -/
theorem zoneNumerator_eq_quadratic (p : LoopParams) (β : ℝ) :
    zoneNumerator p β =
      zoneQuadraticCoefficient p * β ^ 2 +
        (2 * p.v * (1 - p.lambda₀) * p.η * (1 - p.η) -
          2 * p.c ^ 2 * p.I) * β +
        (2 * p.c * p.I - p.v * (1 - p.g) +
          p.v * (1 - p.lambda₀) * (1 - p.η) ^ 2) := by
  simp only [zoneNumerator, zoneQuadraticCoefficient, LoopParams.s]
  ring

/-- The zone numerator's leading coefficient is strictly positive. -/
theorem zoneQuadraticCoefficient_pos {p : LoopParams} (model : LoopModelAssumptions p) :
    0 < zoneQuadraticCoefficient p := by
  simp only [zoneQuadraticCoefficient]
  exact mul_pos (mul_pos model.v_pos (sub_pos.mpr model.lambda₀_lt_one))
    (sq_pos_of_pos model.η_pos)

/-- The stationary gradient is the quadratic zone numerator divided by the positive denominator. -/
theorem G_eq_zoneNumerator_div (p : LoopParams) (β : ℝ)
    (hwall : 1 - p.s β - p.g ≠ 0) :
    p.G β = zoneNumerator p β / (1 - p.s β - p.g) := by
  simp only [LoopParams.G, zoneNumerator]
  field_simp [hwall]
  ring

/-- Below the gain ceiling, roots of `G` are exactly roots of its quadratic numerator. -/
theorem G_eq_zero_iff_zoneNumerator_eq_zero {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    p.G β = 0 ↔ zoneNumerator p β = 0 := by
  rw [G_eq_zoneNumerator_div p β (zoneDenominator_pos model hgain hβ).ne']
  simp only [div_eq_zero_iff, (zoneDenominator_pos model hgain hβ).ne', or_false]

/-- Exact derivative of the quadratic zone numerator. -/
theorem hasDerivAt_zoneNumerator (p : LoopParams) (β : ℝ) :
    HasDerivAt (zoneNumerator p) (zoneNumeratorSlope p β) β := by
  have hlinear : HasDerivAt (fun x : ℝ ↦ 1 - p.c * x) (-p.c) β := by
    (convert! ((hasDerivAt_id β).const_mul p.c).const_sub (1 : ℝ) using 1; ring)
  have hfirst : HasDerivAt
      (fun x : ℝ ↦ 2 * p.c * (1 - p.c * x) * p.I)
      (-2 * p.c ^ 2 * p.I) β := by
    (convert! (hlinear.const_mul (2 * p.c)).mul_const p.I using 1; ring)
  have hden : HasDerivAt (fun x : ℝ ↦ 1 - p.s x - p.g) (-p.sSlope β) β := by
    convert (p.hasDerivAt_s β).const_sub (1 : ℝ) |>.sub_const p.g using 1
  have hsecond : HasDerivAt (fun x : ℝ ↦ p.v * (1 - p.s x - p.g))
      (p.v * (-p.sSlope β)) β := by
    convert hden.const_mul p.v using 1
  have hraw := hfirst.sub hsecond
  have hfun :
      ((fun x : ℝ ↦ 2 * p.c * (1 - p.c * x) * p.I) -
        fun x : ℝ ↦ p.v * (1 - p.s x - p.g)) = zoneNumerator p := by
    rfl
  rw [hfun] at hraw
  apply hraw.congr_deriv
  simp only [zoneNumeratorSlope]
  ring

/-- Difference identity exposing the numerator's positive quadratic curvature. -/
theorem zoneNumerator_one_sub (p : LoopParams) (r : ℝ) :
    zoneNumerator p 1 - zoneNumerator p r =
      (1 - r) *
        (zoneNumeratorSlope p r + zoneQuadraticCoefficient p * (1 - r)) := by
  simp only [zoneNumerator, zoneNumeratorSlope, zoneQuadraticCoefficient,
    LoopParams.s, LoopParams.sSlope]
  ring

/-- An interior root followed by a negative endpoint has negative numerator slope. -/
theorem zoneNumeratorSlope_neg_of_root_of_endpoint_neg
    {p : LoopParams} (model : LoopModelAssumptions p) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (hroot : zoneNumerator p r = 0)
    (hone : zoneNumerator p 1 < 0) :
    zoneNumeratorSlope p r < 0 := by
  have hgap : 0 < 1 - r := sub_pos.mpr hr.2
  have hcoefficient := zoneQuadraticCoefficient_pos model
  have hidentity := zoneNumerator_one_sub p r
  rw [hroot, sub_zero] at hidentity
  have hproduct :
      (1 - r) * (zoneNumeratorSlope p r + zoneQuadraticCoefficient p * (1 - r)) < 0 := by
    rwa [← hidentity]
  have hbracket : zoneNumeratorSlope p r + zoneQuadraticCoefficient p * (1 - r) < 0 := by
    rcases (mul_neg_iff.mp hproduct) with h | h
    · exact h.2
    · exact (not_lt_of_ge hgap.le h.1).elim
  have hpositive : 0 < zoneQuadraticCoefficient p * (1 - r) :=
    mul_pos hcoefficient hgap
  linarith

/-- At a root, the stationary-gradient slope is numerator slope divided by the denominator. -/
theorem GSlope_eq_zoneNumeratorSlope_div_at_root
    {p : LoopParams} (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (hroot : zoneNumerator p r = 0) :
    p.GSlope r = zoneNumeratorSlope p r / (1 - p.s r - p.g) := by
  have hden := zoneDenominator_pos model hgain hr
  simp only [LoopParams.GSlope, zoneNumeratorSlope]
  field_simp [hden.ne']
  simp only [zoneNumerator] at hroot
  linear_combination p.sSlope r * hroot

/-- At capture, `F(1)=2c(1-c)I/(λ₀-g)`. -/
theorem zoneForce_one (p : LoopParams) :
    zoneForce p 1 = 2 * p.c * (1 - p.c) * p.I / (p.lambda₀ - p.g) := by
  simp only [zoneForce, LoopParams.s]
  ring

/-- `F` has the same derivative as `G`. -/
theorem hasDerivAt_zoneForce (p : LoopParams) (β : ℝ)
    (hwall : 1 - p.s β - p.g ≠ 0) :
    HasDerivAt (zoneForce p) (p.GSlope β) β := by
  have hfun : zoneForce p = fun x ↦ p.v + p.G x := by
    funext x
    simp only [zoneForce, LoopParams.G]
    ring
  rw [hfun]
  exact (p.hasDerivAt_G β hwall).const_add p.v

/--
Paper III, Theorem `thm:zones`, calculus clause: the displayed opening
condition makes `F` strictly decreasing at the captured endpoint.
-/
theorem zoneForceSlope_one_neg_of_opening_condition
    {p : LoopParams} (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hopening :
      2 * p.η * (1 - p.lambda₀) * (1 - p.c) < p.c * (p.lambda₀ - p.g)) :
    p.GSlope 1 < 0 := by
  have hscale : 0 < 2 * p.c * p.I :=
    mul_pos (mul_pos two_pos model.c_pos) model.I_pos
  have hden : 0 < 1 - p.s 1 - p.g :=
    zoneDenominator_pos model hgain (by exact ⟨zero_le_one, le_rfl⟩)
  have hbracket :
      -p.c * (1 - p.s 1 - p.g) + (1 - p.c * 1) * p.sSlope 1 < 0 := by
    simp only [LoopParams.s, LoopParams.sSlope]
    norm_num
    nlinarith
  simp only [LoopParams.GSlope]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hscale hbracket)
    (sq_pos_of_pos hden)

/-- The zone function is continuous on the compact policy interval. -/
theorem continuousOn_zoneForce {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) :
    ContinuousOn (zoneForce p) (Icc (0 : ℝ) 1) := by
  intro β hβ
  exact (hasDerivAt_zoneForce p β (zoneDenominator_pos model hgain hβ).ne').continuousAt
    |>.continuousWithinAt

/-- `F` attains a maximum on `[0,1]`. -/
theorem exists_zoneForce_maximizer {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) :
    ∃ βmax ∈ Icc (0 : ℝ) 1,
      ∀ β ∈ Icc (0 : ℝ) 1, zoneForce p β ≤ zoneForce p βmax := by
  obtain ⟨βmax, hβmax, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) 1).Nonempty by exact nonempty_Icc.mpr zero_le_one)
    (continuousOn_zoneForce model hgain)
  exact ⟨βmax, hβmax, (isMaxOn_iff.mp hmax)⟩

/-- The policy-free stock ceiling gives the paper's uniform upper bound on `F`. -/
theorem zoneForce_le_policyFreeBound {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    zoneForce p β ≤ 2 * p.c * p.I / (p.lambda₀ - p.g) := by
  have hgap : 0 < p.lambda₀ - p.g := sub_pos.mpr hgain
  have hden : 0 < 1 - p.s β - p.g := zoneDenominator_pos model hgain hβ
  have hcβ : p.c * β ≤ p.c := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hβ.2 model.c_pos.le
  have hfactor : 0 ≤ 1 - p.c * β := by linarith [model.c_lt_one.le]
  have hcβNonneg : 0 ≤ p.c * β := mul_nonneg model.c_pos.le hβ.1
  have hfactorLe : 1 - p.c * β ≤ 1 := by linarith
  have hscalePos : 0 < 2 * p.c * p.I :=
    mul_pos (mul_pos two_pos model.c_pos) model.I_pos
  have hnumNonneg : 0 ≤ 2 * p.c * (1 - p.c * β) * p.I := by
    rw [show 2 * p.c * (1 - p.c * β) * p.I =
      (2 * p.c * p.I) * (1 - p.c * β) by ring]
    exact mul_nonneg hscalePos.le hfactor
  have hnumLe : 2 * p.c * (1 - p.c * β) * p.I ≤ 2 * p.c * p.I := by
    rw [show 2 * p.c * (1 - p.c * β) * p.I =
      (2 * p.c * p.I) * (1 - p.c * β) by ring]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hfactorLe hscalePos.le
  have hs := stockMultiplier_nonneg_le model hβ
  have hdenOrder : p.lambda₀ - p.g ≤ 1 - p.s β - p.g := by linarith [hs.2]
  have hboundPos : 0 < 2 * p.c * p.I / (p.lambda₀ - p.g) :=
    div_pos hscalePos hgap
  have hboundIdentity :
      (2 * p.c * p.I / (p.lambda₀ - p.g)) * (p.lambda₀ - p.g) =
        2 * p.c * p.I := by
    field_simp [hgap.ne']
  rw [zoneForce]
  apply (div_le_iff₀ hden).2
  have hscaled := mul_le_mul_of_nonneg_left hdenOrder hboundPos.le
  nlinarith [hnumLe, hboundIdentity]

/-- The knob-free certificate is a sufficient condition for zone (A). -/
theorem calibrationZone_of_certificate {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) (hcertificate : 0 ≤ certificateMargin p) :
    CalibrationZone p := by
  intro β hβ
  have hforce := zoneForce_le_policyFreeBound model hgain hβ
  have hgap : 0 < p.lambda₀ - p.g := sub_pos.mpr hgain
  have hbound : 2 * p.c * p.I / (p.lambda₀ - p.g) ≤ p.v := by
    apply (div_le_iff₀ hgap).2
    simp only [certificateMargin] at hcertificate
    nlinarith
  exact hforce.trans hbound

/-- Zone (A)'s valid scalar conclusion is `Gₙ≤0` throughout the interval. -/
theorem calibrationZone_stationaryGradient_nonpos {p : LoopParams}
    (hzone : CalibrationZone p) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    p.G β ≤ 0 := by
  rw [G_eq_neg_v_add_zoneForce]
  linarith [hzone β hβ]

/-- Zone (C) is exactly strict positivity of the captured stationary gradient. -/
theorem captureZone_G_one_pos {p : LoopParams} (hzone : CaptureZone p) :
    0 < p.G 1 := by
  simp only [CaptureZone] at hzone
  rw [G_eq_neg_v_add_zoneForce]
  linarith [hzone]

/-- A point on the stationary stock characteristic is fixed by the stock update. -/
theorem loopStationaryStock_fixed {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    p.stockStep β (p.stationaryStock β) = p.stationaryStock β := by
  have hden := zoneDenominator_pos model hgain hβ
  simp only [LoopParams.stockStep, LoopParams.stationaryStock]
  field_simp [hden.ne']
  ring

/-- At stationary stock, the instantaneous and stationary gradients agree. -/
theorem gradU_stationaryStock_eq_G (p : LoopParams) (β : ℝ) :
    p.gradU β (p.stationaryStock β) = p.G β := by
  simp only [LoopParams.gradU, LoopParams.stationaryStock, LoopParams.G]
  ring

/-- Every stationary interior root is an actual fixed point of the projected loop map. -/
theorem stationaryRoot_equilibrium {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1)
    (hroot : p.G β = 0) :
    IsLoopEquilibrium p β (p.stationaryStock β) := by
  have hstock := loopStationaryStock_fixed model hgain hβ
  have hpolicy : p.deferenceStep β (p.stationaryStock β) = β := by
    simp only [LoopParams.deferenceStep, gradU_stationaryStock_eq_G, hroot, mul_zero,
      add_zero, clipUnit_eq_self hβ]
  simp only [IsLoopEquilibrium, LoopParams.loopMap, hpolicy, hstock]

/-- Zone (C)'s captured corner is an actual fixed point of the projected loop map. -/
theorem captureZone_capturedCorner_equilibrium {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hzone : CaptureZone p) :
    IsLoopEquilibrium p 1 (p.stationaryStock 1) := by
  have hunit : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hG := captureZone_G_one_pos hzone
  have hstock := loopStationaryStock_fixed model hgain hunit
  have hpolicy : p.deferenceStep 1 (p.stationaryStock 1) = 1 := by
    rw [LoopParams.deferenceStep, gradU_stationaryStock_eq_G,
      PaperII.clipUnit_eq_one_iff]
    nlinarith [mul_pos model.α_pos hG]
  simp only [IsLoopEquilibrium, LoopParams.loopMap, hpolicy, hstock]

/-- Zone (B)'s inequalities give the two sign facts claimed in the theorem. -/
theorem partialCaptureBand_signs {p : LoopParams} (hzone : PartialCaptureBand p) :
    p.G 1 ≤ 0 ∧ ∃ β ∈ Ioo (0 : ℝ) 1, 0 < p.G β := by
  constructor
  · rw [G_eq_neg_v_add_zoneForce]
    linarith [hzone.1]
  · obtain ⟨β, hβ, hforce⟩ := hzone.2
    refine ⟨β, hβ, ?_⟩
    rw [G_eq_neg_v_add_zoneForce]
    linarith

/-- If the endpoint inequality in zone (B) is strict, continuity guarantees an interior root. -/
theorem partialCaptureBand_exists_interior_root_of_strict_endpoint
    {p : LoopParams} (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hzone : PartialCaptureBand p) (hstrict : zoneForce p 1 < p.v) :
    ∃ β ∈ Ioo (0 : ℝ) 1, p.G β = 0 := by
  obtain ⟨β₀, hβ₀, hforce⟩ := hzone.2
  have hG₀ : 0 < p.G β₀ := by
    rw [G_eq_neg_v_add_zoneForce]
    linarith
  have hG₁ : p.G 1 < 0 := by
    rw [G_eq_neg_v_add_zoneForce]
    linarith
  have hcont : ContinuousOn p.G (Icc β₀ 1) := by
    intro β hβ
    have hβunit : β ∈ Icc (0 : ℝ) 1 := ⟨hβ₀.1.le.trans hβ.1, hβ.2⟩
    exact (p.hasDerivAt_G β (zoneDenominator_pos model hgain hβunit).ne').continuousAt
      |>.continuousWithinAt
  have hzeroRange : (0 : ℝ) ∈ Icc (p.G 1) (p.G β₀) := ⟨hG₁.le, hG₀.le⟩
  rcases intermediate_value_Icc' hβ₀.2.le hcont hzeroRange with ⟨β, hβ, hG⟩
  have hne₀ : β ≠ β₀ := by
    intro h
    subst β
    linarith
  have hne₁ : β ≠ 1 := by
    intro h
    subst β
    linarith
  have hβgt : β₀ < β := lt_of_le_of_ne hβ.1 (Ne.symm hne₀)
  exact ⟨β, ⟨hβ₀.1.trans hβgt, lt_of_le_of_ne hβ.2 hne₁⟩, hG⟩

/--
With a strict endpoint inequality, the quadratic structure strengthens the
continuity argument: an interior root is automatically a transversal
descending crossing.
-/
theorem partialCaptureBand_exists_descending_root_of_strict_endpoint
    {p : LoopParams} (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hzone : PartialCaptureBand p) (hstrict : zoneForce p 1 < p.v) :
    ∃ β ∈ Ioo (0 : ℝ) 1, p.G β = 0 ∧ p.GSlope β < 0 := by
  obtain ⟨β, hβ, hG⟩ :=
    partialCaptureBand_exists_interior_root_of_strict_endpoint model hgain hzone hstrict
  have hβclosed : β ∈ Icc (0 : ℝ) 1 := ⟨hβ.1.le, hβ.2.le⟩
  have hroot : zoneNumerator p β = 0 :=
    (G_eq_zero_iff_zoneNumerator_eq_zero model hgain hβclosed).mp hG
  have hG₁ : p.G 1 < 0 := by
    rw [G_eq_neg_v_add_zoneForce]
    linarith
  have hden₁ : 0 < 1 - p.s 1 - p.g :=
    zoneDenominator_pos model hgain (by exact ⟨zero_le_one, le_rfl⟩)
  have hnum₁ : zoneNumerator p 1 < 0 := by
    rw [G_eq_zoneNumerator_div p 1 hden₁.ne'] at hG₁
    rcases div_neg_iff.mp hG₁ with hbad | hgood
    · exact (not_lt_of_ge hden₁.le hbad.2).elim
    · exact hgood.1
  have hnumSlope : zoneNumeratorSlope p β < 0 :=
    zoneNumeratorSlope_neg_of_root_of_endpoint_neg model hβ hroot hnum₁
  have hdenβ := zoneDenominator_pos model hgain hβclosed
  have hGslope : p.GSlope β < 0 := by
    rw [GSlope_eq_zoneNumeratorSlope_div_at_root model hgain hβclosed hroot]
    exact (div_neg_iff.mpr (Or.inr ⟨hnumSlope, hdenβ⟩))
  exact ⟨β, hβ, hG, hGslope⟩

/-! ## Root structure: the zone numerator is an exact quadratic

`civic_loops.tex:458` lists as open the question of "conditions under which
`G_g` has at most one interior root pair (equivalently, `F` unimodal)", which
would "sharpen zone (B) from existence to uniqueness of the partial-capture
equilibrium"; `civic_drift.tex:553` lists the matching question for the
root-uniqueness clause of Paper II's assumption `(H)`.

Both are unconditional consequences of structure already proved above:
`zoneNumerator` is a quadratic in the policy (`zoneNumerator_eq_quadratic`)
whose leading coefficient `v(1-λ₀)η²` is strictly positive
(`zoneQuadraticCoefficient_pos`).  A real quadratic has at most two roots, and
the two endpoint signs place them.  No condition on `(η, c, λ₀)` is needed.
-/

/-- Two distinct roots factor the numerator's value at the captured endpoint. -/
theorem zoneNumerator_one_eq_of_two_roots (p : LoopParams) {r r' : ℝ} (hne : r ≠ r')
    (hr : zoneNumerator p r = 0) (hr' : zoneNumerator p r' = 0) :
    zoneNumerator p 1 = zoneQuadraticCoefficient p * (1 - r) * (1 - r') := by
  rw [zoneNumerator_eq_quadratic] at hr hr' ⊢
  have hdiff : (r - r') *
      (zoneQuadraticCoefficient p * (r + r') +
        (2 * p.v * (1 - p.lambda₀) * p.η * (1 - p.η) - 2 * p.c ^ 2 * p.I)) = 0 := by
    linear_combination hr - hr'
  have hkey : zoneQuadraticCoefficient p * (r + r') +
      (2 * p.v * (1 - p.lambda₀) * p.η * (1 - p.η) - 2 * p.c ^ 2 * p.I) = 0 := by
    rcases mul_eq_zero.mp hdiff with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact h
  linear_combination hr + (1 - r) * hkey

/-- Two distinct roots factor the numerator's value at the calibrated endpoint. -/
theorem zoneNumerator_zero_eq_of_two_roots (p : LoopParams) {r r' : ℝ} (hne : r ≠ r')
    (hr : zoneNumerator p r = 0) (hr' : zoneNumerator p r' = 0) :
    zoneNumerator p 0 = zoneQuadraticCoefficient p * r * r' := by
  rw [zoneNumerator_eq_quadratic] at hr hr' ⊢
  have hdiff : (r - r') *
      (zoneQuadraticCoefficient p * (r + r') +
        (2 * p.v * (1 - p.lambda₀) * p.η * (1 - p.η) - 2 * p.c ^ 2 * p.I)) = 0 := by
    linear_combination hr - hr'
  have hkey : zoneQuadraticCoefficient p * (r + r') +
      (2 * p.v * (1 - p.lambda₀) * p.η * (1 - p.η) - 2 * p.c ^ 2 * p.I) = 0 := by
    rcases mul_eq_zero.mp hdiff with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact h
  linear_combination hr - r * hkey

/-- Difference identity at the calibrated endpoint, mirroring `zoneNumerator_one_sub`. -/
theorem zoneNumerator_zero_sub (p : LoopParams) (r : ℝ) :
    zoneNumerator p 0 - zoneNumerator p r =
      -r * (zoneNumeratorSlope p r - zoneQuadraticCoefficient p * r) := by
  simp only [zoneNumerator, zoneNumeratorSlope, zoneQuadraticCoefficient,
    LoopParams.s, LoopParams.sSlope]
  ring

/-- An interior root preceded by a negative calibrated endpoint is an ascending crossing. -/
theorem zoneNumeratorSlope_pos_of_root_of_calibrated_neg
    {p : LoopParams} (model : LoopModelAssumptions p) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (hroot : zoneNumerator p r = 0)
    (hzero : zoneNumerator p 0 < 0) :
    0 < zoneNumeratorSlope p r := by
  have hcoefficient := zoneQuadraticCoefficient_pos model
  have hidentity := zoneNumerator_zero_sub p r
  rw [hroot, sub_zero] at hidentity
  have hprod : 0 < r * (zoneNumeratorSlope p r - zoneQuadraticCoefficient p * r) := by
    have hneg : -r * (zoneNumeratorSlope p r - zoneQuadraticCoefficient p * r) < 0 := by
      rw [← hidentity]; exact hzero
    linarith
  have hbracket : 0 < zoneNumeratorSlope p r - zoneQuadraticCoefficient p * r := by
    nlinarith [hprod, hr.1]
  linarith [mul_pos hcoefficient hr.1]

/-- Below the gain ceiling the numerator inherits the stationary gradient's sign. -/
theorem zoneNumerator_neg_of_G_neg {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) (hG : p.G β < 0) :
    zoneNumerator p β < 0 := by
  have hden := zoneDenominator_pos model hgain hβ
  by_contra hcon
  rw [G_eq_zoneNumerator_div p β hden.ne'] at hG
  exact absurd hG (not_lt.mpr (div_nonneg (not_lt.mp hcon) hden.le))

/--
Paper III, Theorem `thm:zones`, clause (B), `civic_loops.tex:287`.

With the captured endpoint *strictly* below `v` --- the strictness the boundary
counterexample below forces --- zone (B) carries **exactly one** interior
equilibrium, and it is a descending crossing: uniqueness, not merely
existence, answering the open problem of `civic_loops.tex:458` with no
extra hypothesis.
-/
theorem partialCaptureBand_unique_descending_root
    {p : LoopParams} (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hzone : PartialCaptureBand p) (hstrict : zoneForce p 1 < p.v) :
    ∃ β ∈ Ioo (0 : ℝ) 1,
      p.G β = 0 ∧ p.GSlope β < 0 ∧
        ∀ β' ∈ Ioo (0 : ℝ) 1, p.G β' = 0 → β' = β := by
  obtain ⟨β, hβ, hG⟩ :=
    partialCaptureBand_exists_interior_root_of_strict_endpoint model hgain hzone hstrict
  have hβunit : β ∈ Icc (0 : ℝ) 1 := ⟨hβ.1.le, hβ.2.le⟩
  have hone : zoneNumerator p 1 < 0 := by
    refine zoneNumerator_neg_of_G_neg model hgain (right_mem_Icc.mpr zero_le_one) ?_
    rw [G_eq_neg_v_add_zoneForce]
    linarith
  have hroot : zoneNumerator p β = 0 :=
    (G_eq_zero_iff_zoneNumerator_eq_zero model hgain hβunit).mp hG
  refine ⟨β, hβ, hG, ?_, ?_⟩
  · have hslope := zoneNumeratorSlope_neg_of_root_of_endpoint_neg model hβ hroot hone
    rw [GSlope_eq_zoneNumeratorSlope_div_at_root model hgain hβunit hroot]
    exact div_neg_of_neg_of_pos hslope (zoneDenominator_pos model hgain hβunit)
  · intro β' hβ' hG'
    by_contra hne
    have hβ'unit : β' ∈ Icc (0 : ℝ) 1 := ⟨hβ'.1.le, hβ'.2.le⟩
    have hroot' : zoneNumerator p β' = 0 :=
      (G_eq_zero_iff_zoneNumerator_eq_zero model hgain hβ'unit).mp hG'
    have hfactor := zoneNumerator_one_eq_of_two_roots p hne hroot' hroot
    have hpos : 0 < zoneQuadraticCoefficient p * (1 - β') * (1 - β) :=
      mul_pos (mul_pos (zoneQuadraticCoefficient_pos model) (sub_pos.mpr hβ'.2))
        (sub_pos.mpr hβ.2)
    linarith [hfactor ▸ hpos]

/--
The zone-(B) root is an actual interior equilibrium of the projected
two-dimensional loop, not merely a zero of the stationary scalar equation.
-/
theorem partialCaptureBand_unique_descending_equilibrium
    {p : LoopParams} (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hzone : PartialCaptureBand p) (hstrict : zoneForce p 1 < p.v) :
    ∃ β ∈ Ioo (0 : ℝ) 1,
      IsLoopEquilibrium p β (p.stationaryStock β) ∧
        p.G β = 0 ∧ p.GSlope β < 0 ∧
          ∀ β' ∈ Ioo (0 : ℝ) 1, p.G β' = 0 → β' = β := by
  obtain ⟨β, hβ, hG, hslope, hunique⟩ :=
    partialCaptureBand_unique_descending_root model hgain hzone hstrict
  exact ⟨β, hβ, stationaryRoot_equilibrium model hgain ⟨hβ.1.le, hβ.2.le⟩ hG,
    hG, hslope, hunique⟩

/--
Papers II--III: the root-uniqueness clause of `(H)` is not an assumption.

`civic_drift.tex:210` assumes that `G` "has a single sign change on `(0,1)`,
at `β†`, with `G'(β†) > 0`" alongside `G(0) < 0 < G(1)`.  The endpoint signs
alone force it: the numerator is an upward parabola, so a negative calibrated
endpoint and a positive captured endpoint admit exactly one interior root, and
it is necessarily ascending.  This removes the clause `civic_drift.tex:553`
lists as open.
-/
theorem exists_unique_ascending_root_of_endpoint_signs
    {p : LoopParams} (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (h0 : p.G 0 < 0) (h1 : 0 < p.G 1) :
    ∃ β ∈ Ioo (0 : ℝ) 1,
      p.G β = 0 ∧ 0 < p.GSlope β ∧
        ∀ β' ∈ Ioo (0 : ℝ) 1, p.G β' = 0 → β' = β := by
  have hzero : zoneNumerator p 0 < 0 :=
    zoneNumerator_neg_of_G_neg model hgain (left_mem_Icc.mpr zero_le_one) h0
  have hcont : ContinuousOn p.G (Icc (0 : ℝ) 1) := by
    intro β hβ
    exact (p.hasDerivAt_G β (zoneDenominator_pos model hgain hβ).ne').continuousAt
      |>.continuousWithinAt
  obtain ⟨β, hβmem, hG⟩ :=
    intermediate_value_Icc (zero_le_one (α := ℝ)) hcont ⟨h0.le, h1.le⟩
  have hne₀ : β ≠ 0 := by
    intro h; subst β; linarith
  have hne₁ : β ≠ 1 := by
    intro h; subst β; linarith
  have hβ : β ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hβmem.1 (Ne.symm hne₀), lt_of_le_of_ne hβmem.2 hne₁⟩
  have hroot : zoneNumerator p β = 0 :=
    (G_eq_zero_iff_zoneNumerator_eq_zero model hgain hβmem).mp hG
  refine ⟨β, hβ, hG, ?_, ?_⟩
  · have hslope := zoneNumeratorSlope_pos_of_root_of_calibrated_neg model hβ hroot hzero
    rw [GSlope_eq_zoneNumeratorSlope_div_at_root model hgain hβmem hroot]
    exact div_pos hslope (zoneDenominator_pos model hgain hβmem)
  · intro β' hβ' hG'
    by_contra hne
    have hβ'unit : β' ∈ Icc (0 : ℝ) 1 := ⟨hβ'.1.le, hβ'.2.le⟩
    have hroot' : zoneNumerator p β' = 0 :=
      (G_eq_zero_iff_zoneNumerator_eq_zero model hgain hβ'unit).mp hG'
    have hfactor := zoneNumerator_zero_eq_of_two_roots p hne hroot' hroot
    have hpos : 0 < zoneQuadraticCoefficient p * β' * β :=
      mul_pos (mul_pos (zoneQuadraticCoefficient_pos model) hβ'.1) hβ.1
    linarith [hfactor ▸ hpos]

/-! ## Exact boundary counterexample to clause (B) -/

/-- Exact rational parameters at the weak lower boundary `v=F(1)` of zone (B). -/
def zoneBoundaryParams : LoopParams where
  η := 1 / 2
  lambda₀ := 3 / 20
  I := 3 / 100
  v := 9 / 200
  c := 9 / 10
  α := 1
  g := 3 / 100

/-- The counterexample satisfies every standing primitive restriction. -/
theorem zoneBoundary_model : LoopModelAssumptions zoneBoundaryParams := by
  constructor <;> norm_num [zoneBoundaryParams]

/-- The counterexample lies strictly below the divergence wall. -/
theorem zoneBoundary_gain_lt_lambda :
    zoneBoundaryParams.g < zoneBoundaryParams.lambda₀ := by
  norm_num [zoneBoundaryParams]

/-- It also satisfies strict `(SS_g)`, so the issue is not a step-size failure. -/
theorem zoneBoundary_strictStepSize : StrictStepSize zoneBoundaryParams := by
  constructor
  norm_num [zoneBoundaryParams]

/-- Its stationary gradient has an exact factorization after clearing the positive denominator. -/
theorem zoneBoundary_G_factor {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    zoneBoundaryParams.G β *
        (200 * (303 - 170 * β - 85 * β ^ 2)) =
      9 * (1 - β) * (177 - 85 * β) := by
  have hden : 303 - 170 * β - 85 * β ^ 2 ≠ 0 := by
    have hproduct : 0 ≤ (1 - β) * (β + 3) :=
      mul_nonneg (sub_nonneg.mpr hβ.2) (by linarith [hβ.1])
    have : 0 < 303 - 170 * β - 85 * β ^ 2 := by nlinarith
    exact this.ne'
  have hden' : 303 - β * 170 - β ^ 2 * 85 ≠ 0 := by
    simpa only [mul_comm] using hden
  change
    (-(9 / 200 : ℝ) +
          2 * (9 / 10 : ℝ) * (1 - (9 / 10 : ℝ) * β) * (3 / 100 : ℝ) /
            (1 - (1 - (3 / 20 : ℝ)) *
              (1 - (1 / 2 : ℝ) * (1 - β)) ^ 2 - (3 / 100 : ℝ))) *
        (200 * (303 - 170 * β - 85 * β ^ 2)) =
      9 * (1 - β) * (177 - 85 * β)
  rw [show 1 - (1 - (3 / 20 : ℝ)) *
      (1 - (1 / 2 : ℝ) * (1 - β)) ^ 2 - (3 / 100 : ℝ) =
        (303 - 170 * β - 85 * β ^ 2) / 400 by ring]
  field_simp [hden, hden']
  ring

/-- At every interior policy the counterexample's stationary gradient is positive. -/
theorem zoneBoundary_G_pos {β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1) :
    0 < zoneBoundaryParams.G β := by
  have hfirst : 0 < 1 - β := sub_pos.mpr hβ.2
  have hsecond : 0 < 177 - 85 * β := by nlinarith
  have haux : 0 < (1 - β) * (β + 3) :=
    mul_pos hfirst (by linarith [hβ.1])
  have hden : 0 < 200 * (303 - 170 * β - 85 * β ^ 2) := by
    have : 0 < 303 - 170 * β - 85 * β ^ 2 := by nlinarith
    positivity
  have hproduct : 0 < zoneBoundaryParams.G β *
      (200 * (303 - 170 * β - 85 * β ^ 2)) := by
    rw [zoneBoundary_G_factor ⟨hβ.1.le, hβ.2.le⟩]
    positivity
  exact pos_of_mul_pos_left hproduct hden.le

/-- These parameters satisfy zone (B)'s displayed weak/strict inequalities. -/
theorem zoneBoundary_partialCaptureBand : PartialCaptureBand zoneBoundaryParams := by
  constructor
  · norm_num [zoneForce, LoopParams.s, zoneBoundaryParams]
  · refine ⟨1 / 2, by norm_num, ?_⟩
    have hG := zoneBoundary_G_pos (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num)
    rw [G_eq_neg_v_add_zoneForce] at hG
    linarith

/-- The paper's derivative condition for opening the band is also strict here. -/
theorem zoneBoundary_opening_condition :
    zoneBoundaryParams.c * (zoneBoundaryParams.lambda₀ - zoneBoundaryParams.g) >
      2 * zoneBoundaryParams.η * (1 - zoneBoundaryParams.lambda₀) *
        (1 - zoneBoundaryParams.c) := by
  norm_num [zoneBoundaryParams]

/-- Nevertheless there is no interior root, hence no partial-capture equilibrium. -/
theorem zoneBoundary_no_interior_root :
    ¬ ∃ β : ℝ, β ∈ Ioo (0 : ℝ) 1 ∧ zoneBoundaryParams.G β = 0 := by
  rintro ⟨β, hβ, hzero⟩
  have hpos := zoneBoundary_G_pos hβ
  linarith

/--
Paper III, Theorem `thm:zones`, clause (B), `civic_loops.tex:287--303`:
the weak boundary `F(1)≤v<Fmax` does not guarantee an interior descending
crossing. Here `v=F(1)`, `F` is larger at an interior point, and strict
`(SS_g)` plus the paper's opening condition hold, but `G>0` on all of `(0,1)`.
-/
theorem zoneStructure_boundary_counterexample :
    LoopModelAssumptions zoneBoundaryParams ∧
      zoneBoundaryParams.g < zoneBoundaryParams.lambda₀ ∧
      StrictStepSize zoneBoundaryParams ∧
      PartialCaptureBand zoneBoundaryParams ∧
      ¬ ∃ β : ℝ, β ∈ Ioo (0 : ℝ) 1 ∧ zoneBoundaryParams.G β = 0 :=
  ⟨zoneBoundary_model, zoneBoundary_gain_lt_lambda, zoneBoundary_strictStepSize,
    zoneBoundary_partialCaptureBand, zoneBoundary_no_interior_root⟩

#print axioms classificationCycle_model
#print axioms classificationCycle_strictStepSize
#print axioms classificationCycle_gain_lt_lambda
#print axioms classificationCycle_isOrbit
#print axioms classificationCycle_mem_ceilingBox
#print axioms classification_global_convergence_counterexample
#print axioms zoneDenominator_pos
#print axioms G_eq_neg_v_add_zoneForce
#print axioms zoneNumerator_eq_quadratic
#print axioms zoneQuadraticCoefficient_pos
#print axioms G_eq_zoneNumerator_div
#print axioms G_eq_zero_iff_zoneNumerator_eq_zero
#print axioms hasDerivAt_zoneNumerator
#print axioms zoneNumerator_one_sub
#print axioms zoneNumeratorSlope_neg_of_root_of_endpoint_neg
#print axioms GSlope_eq_zoneNumeratorSlope_div_at_root
#print axioms zoneForce_one
#print axioms hasDerivAt_zoneForce
#print axioms zoneForceSlope_one_neg_of_opening_condition
#print axioms continuousOn_zoneForce
#print axioms exists_zoneForce_maximizer
#print axioms zoneForce_le_policyFreeBound
#print axioms calibrationZone_of_certificate
#print axioms calibrationZone_stationaryGradient_nonpos
#print axioms captureZone_G_one_pos
#print axioms loopStationaryStock_fixed
#print axioms gradU_stationaryStock_eq_G
#print axioms stationaryRoot_equilibrium
#print axioms captureZone_capturedCorner_equilibrium
#print axioms partialCaptureBand_signs
#print axioms partialCaptureBand_exists_interior_root_of_strict_endpoint
#print axioms partialCaptureBand_exists_descending_root_of_strict_endpoint
#print axioms zoneBoundary_model
#print axioms zoneBoundary_gain_lt_lambda
#print axioms zoneBoundary_strictStepSize
#print axioms zoneBoundary_G_factor
#print axioms zoneBoundary_G_pos
#print axioms zoneBoundary_partialCaptureBand
#print axioms zoneBoundary_opening_condition
#print axioms zoneBoundary_no_interior_root
#print axioms zoneStructure_boundary_counterexample
#print axioms zoneNumerator_one_eq_of_two_roots
#print axioms zoneNumerator_zero_eq_of_two_roots
#print axioms zoneNumerator_zero_sub
#print axioms zoneNumeratorSlope_pos_of_root_of_calibrated_neg
#print axioms zoneNumerator_neg_of_G_neg
#print axioms partialCaptureBand_unique_descending_root
#print axioms partialCaptureBand_unique_descending_equilibrium
#print axioms exists_unique_ascending_root_of_endpoint_signs

end

end CivicAlignment.PaperIII
