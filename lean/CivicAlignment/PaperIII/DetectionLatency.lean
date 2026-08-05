/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.RateSeparation
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Paper III: exact discrete detection latency

This file gives the first audit-alarm time as an explicit ceiling of a real
logarithmic expression.  It also bounds the difference from the paper's
continuous leading term by a named offset plus the unit rounding interval.
-/

namespace CivicAlignment.PaperIII

open Filter Topology

noncomputable section

/-- Low-coordinate magnitude required to trigger the audit threshold. -/
def auditAlarmMagnitudeThreshold (ε piL θ : ℝ) : ℝ :=
  Real.sqrt (θ / (ε * piL))

/-- The exact real-valued crossing time before integer rounding. -/
def detectionLatencyExactReal
    (ε piL θ ζ injection x₀ : ℝ) : ℝ :=
  Real.log
      ((auditAlarmMagnitudeThreshold ε piL θ +
          |capturedLowEquilibrium ζ injection|) /
        |x₀ - capturedLowEquilibrium ζ injection|) /
    Real.log (1 + ζ)

/-- The exact discrete first-alarm candidate. -/
def detectionLatencyHorizon
    (ε piL θ ζ injection x₀ : ℝ) : ℕ :=
  Nat.ceil (detectionLatencyExactReal ε piL θ ζ injection x₀)

/-- The continuous leading term written directly in terms of the magnitude
threshold. -/
def detectionLatencyGeometricLeadingTerm
    (ε piL θ ζ injection x₀ : ℝ) : ℝ :=
  Real.log
      (auditAlarmMagnitudeThreshold ε piL θ /
        |x₀ - capturedLowEquilibrium ζ injection|) /
    Real.log (1 + ζ)

/-- Correction caused by the affine path's nonzero fixed-point offset. -/
def detectionLatencyOffset
    (ε piL θ ζ injection : ℝ) : ℝ :=
  Real.log
      (1 + |capturedLowEquilibrium ζ injection| /
        auditAlarmMagnitudeThreshold ε piL θ) /
    Real.log (1 + ζ)

/-- Sign alignment turns the absolute affine path into a positive geometric
term minus the magnitude of its fixed-point offset. -/
theorem abs_capturedLowPath_eq
    {ζ injection x₀ : ℝ} (hζ : 0 < ζ) (hinjection : injection ≠ 0)
    (hsign : 0 ≤ x₀ * injection) (t : ℕ) :
    |capturedLowPath ζ injection x₀ t| =
      |x₀ - capturedLowEquilibrium ζ injection| * (1 + ζ) ^ t -
        |capturedLowEquilibrium ζ injection| := by
  have hrOne : 1 ≤ 1 + ζ := by linarith
  have hrpow : 1 ≤ (1 + ζ) ^ t := one_le_pow₀ hrOne
  rw [capturedLowPath_closedForm hζ.ne' injection x₀ t]
  rcases lt_or_gt_of_ne hinjection with hinjectionNeg | hinjectionPos
  · have hx₀ : x₀ ≤ 0 := nonpos_of_mul_nonneg_left hsign hinjectionNeg
    have heqPos : 0 < capturedLowEquilibrium ζ injection := by
      simp only [capturedLowEquilibrium]
      exact div_pos (neg_pos.mpr hinjectionNeg) hζ
    have hampNeg : x₀ - capturedLowEquilibrium ζ injection < 0 := by linarith
    have hmul :
        (x₀ - capturedLowEquilibrium ζ injection) * (1 + ζ) ^ t ≤
          x₀ - capturedLowEquilibrium ζ injection := by
      simpa only [mul_one] using
        (mul_le_mul_of_nonpos_left hrpow hampNeg.le)
    have hpathNonpos :
        (x₀ - capturedLowEquilibrium ζ injection) * (1 + ζ) ^ t +
          capturedLowEquilibrium ζ injection ≤ 0 := by
      linarith
    rw [abs_of_nonpos hpathNonpos, abs_of_neg hampNeg, abs_of_pos heqPos]
    ring
  · have hx₀ : 0 ≤ x₀ := nonneg_of_mul_nonneg_left hsign hinjectionPos
    have heqNeg : capturedLowEquilibrium ζ injection < 0 := by
      simp only [capturedLowEquilibrium]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos hinjectionPos) hζ
    have hampPos : 0 < x₀ - capturedLowEquilibrium ζ injection := by linarith
    have hmul :
        x₀ - capturedLowEquilibrium ζ injection ≤
          (x₀ - capturedLowEquilibrium ζ injection) * (1 + ζ) ^ t := by
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hrpow hampPos.le)
    have hpathNonneg : 0 ≤
        (x₀ - capturedLowEquilibrium ζ injection) * (1 + ζ) ^ t +
          capturedLowEquilibrium ζ injection := by
      linarith
    rw [abs_of_nonneg hpathNonneg, abs_of_pos hampPos, abs_of_neg heqNeg]
    ring

/-- A positive audit alarm is equivalent to crossing the corresponding
square-root magnitude threshold. -/
theorem auditAlarmAt_iff_threshold_le_abs
    {ε piL θ ζ injection x₀ : ℝ}
    (hε : 0 < ε) (hpiL : 0 < piL) (hθ : 0 < θ) (t : ℕ) :
    auditAlarmAt ε piL θ ζ injection x₀ t ↔
      auditAlarmMagnitudeThreshold ε piL θ ≤
        |capturedLowPath ζ injection x₀ t| := by
  let x := capturedLowPath ζ injection x₀ t
  have hscale : 0 < ε * piL := mul_pos hε hpiL
  have hratio : 0 ≤ θ / (ε * piL) := (div_pos hθ hscale).le
  simp only [auditAlarmAt, auditSensorMagnitude,
    auditAlarmMagnitudeThreshold]
  change θ ≤ (ε * piL) * x ^ 2 ↔
    Real.sqrt (θ / (ε * piL)) ≤ |x|
  rw [← Real.sqrt_sq_eq_abs x,
    Real.sqrt_le_sqrt_iff (sq_nonneg x)]
  rw [div_le_iff₀ hscale]
  ring_nf

/-- Under sign alignment, the audit event is exactly the comparison between
the real logarithmic crossing time and the integer observation time. -/
theorem auditAlarmAt_iff_exactReal_le
    {ε piL θ ζ injection x₀ : ℝ}
    (hε : 0 < ε) (hpiL : 0 < piL) (hθ : 0 < θ)
    (hζ : 0 < ζ) (hinjection : injection ≠ 0)
    (hsign : 0 ≤ x₀ * injection) (t : ℕ) :
    auditAlarmAt ε piL θ ζ injection x₀ t ↔
      detectionLatencyExactReal ε piL θ ζ injection x₀ ≤ (t : ℝ) := by
  let R := auditAlarmMagnitudeThreshold ε piL θ
  let a := |x₀ - capturedLowEquilibrium ζ injection|
  let b := |capturedLowEquilibrium ζ injection|
  let r := 1 + ζ
  have hR : 0 < R := by
    dsimp only [R, auditAlarmMagnitudeThreshold]
    exact Real.sqrt_pos.2 (div_pos hθ (mul_pos hε hpiL))
  have hamplitude := capturedLowAmplitude_ne_zero hζ hinjection hsign
  have ha : 0 < a := by
    dsimp only [a]
    exact abs_pos.mpr hamplitude
  have hb : 0 ≤ b := abs_nonneg _
  have hr : 1 < r := by dsimp only [r]; linarith
  have hrpos : 0 < r := zero_lt_one.trans hr
  have hlogr : 0 < Real.log r := Real.log_pos hr
  have hratio : 0 < (R + b) / a := div_pos (add_pos_of_pos_of_nonneg hR hb) ha
  have hrpow : 0 < r ^ t := pow_pos hrpos t
  rw [auditAlarmAt_iff_threshold_le_abs hε hpiL hθ,
    abs_capturedLowPath_eq hζ hinjection hsign]
  change R ≤ a * r ^ t - b ↔
    Real.log ((R + b) / a) / Real.log r ≤ (t : ℝ)
  have hfirst : R ≤ a * r ^ t - b ↔ (R + b) / a ≤ r ^ t := by
    rw [div_le_iff₀ ha]
    constructor <;> intro h <;> linarith
  rw [hfirst, ← Real.log_le_log_iff hratio hrpow, Real.log_pow]
  exact (div_le_iff₀ hlogr).symm

/-- At time zero, sign alignment identifies the growing amplitude as the sum
of the initial magnitude and the fixed-point-offset magnitude. -/
theorem abs_capturedLowAmplitude_eq
    {ζ injection x₀ : ℝ} (hζ : 0 < ζ) (hinjection : injection ≠ 0)
    (hsign : 0 ≤ x₀ * injection) :
    |x₀ - capturedLowEquilibrium ζ injection| =
      |x₀| + |capturedLowEquilibrium ζ injection| := by
  have h := abs_capturedLowPath_eq hζ hinjection hsign 0
  simp only [capturedLowPath, arithGeom_zero, pow_zero, mul_one] at h
  linarith

/-- The exact real crossing time is nonnegative once the audit magnitude
threshold is at least the initial low-coordinate magnitude. -/
theorem detectionLatencyExactReal_nonneg
    {ε piL θ ζ injection x₀ : ℝ}
    (_hε : 0 < ε) (_hpiL : 0 < piL) (_hθ : 0 < θ)
    (hζ : 0 < ζ) (hinjection : injection ≠ 0)
    (hsign : 0 ≤ x₀ * injection)
    (hinitial : |x₀| ≤ auditAlarmMagnitudeThreshold ε piL θ) :
    0 ≤ detectionLatencyExactReal ε piL θ ζ injection x₀ := by
  let R := auditAlarmMagnitudeThreshold ε piL θ
  let a := |x₀ - capturedLowEquilibrium ζ injection|
  let b := |capturedLowEquilibrium ζ injection|
  let r := 1 + ζ
  have ha : 0 < a := by
    dsimp only [a]
    exact abs_pos.mpr (capturedLowAmplitude_ne_zero hζ hinjection hsign)
  have hamp : a = |x₀| + b := by
    simpa only [a, b] using abs_capturedLowAmplitude_eq hζ hinjection hsign
  have hratio : 1 ≤ (R + b) / a := by
    apply (le_div_iff₀ ha).2
    simpa only [one_mul, hamp, add_comm] using add_le_add_right hinitial b
  have hlogr : 0 < Real.log r := by
    apply Real.log_pos
    dsimp only [r]
    linarith
  change 0 ≤ Real.log ((R + b) / a) / Real.log r
  exact div_nonneg (Real.log_nonneg hratio) hlogr.le

/-- The ceiling formula is the first integer audit alarm. -/
theorem detectionLatencyHorizon_is_first_alarm
    {ε piL θ ζ injection x₀ : ℝ}
    (hε : 0 < ε) (hpiL : 0 < piL) (hθ : 0 < θ)
    (hζ : 0 < ζ) (hinjection : injection ≠ 0)
    (hsign : 0 ≤ x₀ * injection)
    (hinitial : |x₀| ≤ auditAlarmMagnitudeThreshold ε piL θ) :
    auditAlarmAt ε piL θ ζ injection x₀
        (detectionLatencyHorizon ε piL θ ζ injection x₀) ∧
      ∀ t < detectionLatencyHorizon ε piL θ ζ injection x₀,
        ¬auditAlarmAt ε piL θ ζ injection x₀ t := by
  let q := detectionLatencyExactReal ε piL θ ζ injection x₀
  let H := detectionLatencyHorizon ε piL θ ζ injection x₀
  have hq : 0 ≤ q := by
    simpa only [q] using detectionLatencyExactReal_nonneg
      hε hpiL hθ hζ hinjection hsign hinitial
  have hceil : q ≤ (H : ℝ) := by
    simpa only [H, detectionLatencyHorizon, q] using Nat.le_ceil q
  constructor
  · exact (auditAlarmAt_iff_exactReal_le
      hε hpiL hθ hζ hinjection hsign H).2 hceil
  · intro t ht
    have htq : (t : ℝ) < q := by
      exact Nat.lt_ceil.mp (by
        simpa only [H, detectionLatencyHorizon, q] using ht)
    exact (auditAlarmAt_iff_exactReal_le
      hε hpiL hθ hζ hinjection hsign t).not.mpr (not_le_of_gt htq)

/-- The exact real crossing time splits into the geometric leading term and
the fixed-point-offset correction. -/
theorem detectionLatencyExactReal_eq_leading_add_offset
    {ε piL θ ζ injection x₀ : ℝ}
    (hε : 0 < ε) (hpiL : 0 < piL) (hθ : 0 < θ)
    (hζ : 0 < ζ) (hinjection : injection ≠ 0)
    (hsign : 0 ≤ x₀ * injection) :
    detectionLatencyExactReal ε piL θ ζ injection x₀ =
      detectionLatencyGeometricLeadingTerm ε piL θ ζ injection x₀ +
        detectionLatencyOffset ε piL θ ζ injection := by
  let R := auditAlarmMagnitudeThreshold ε piL θ
  let a := |x₀ - capturedLowEquilibrium ζ injection|
  let b := |capturedLowEquilibrium ζ injection|
  let r := 1 + ζ
  have hR : 0 < R := by
    dsimp only [R, auditAlarmMagnitudeThreshold]
    exact Real.sqrt_pos.2 (div_pos hθ (mul_pos hε hpiL))
  have ha : 0 < a := by
    dsimp only [a]
    exact abs_pos.mpr (capturedLowAmplitude_ne_zero hζ hinjection hsign)
  have hsecond : 0 < 1 + b / R := by
    have : 0 ≤ b / R := div_nonneg (abs_nonneg _) hR.le
    linarith
  have hfactor : (R + b) / a = (R / a) * (1 + b / R) := by
    field_simp [hR.ne', ha.ne']
  change Real.log ((R + b) / a) / Real.log r =
    Real.log (R / a) / Real.log r +
      Real.log (1 + b / R) / Real.log r
  rw [hfactor, Real.log_mul (div_ne_zero hR.ne' ha.ne') hsecond.ne']
  ring

/-- The square-root form of the leading term is exactly the leading term
printed in the paper. -/
theorem detectionLatencyGeometricLeadingTerm_eq_leadingTerm
    {ε piL θ ζ injection x₀ : ℝ}
    (hε : 0 < ε) (hpiL : 0 < piL) (hθ : 0 < θ)
    (hζ : 0 < ζ) (hinjection : injection ≠ 0)
    (hsign : 0 ≤ x₀ * injection) :
    detectionLatencyGeometricLeadingTerm ε piL θ ζ injection x₀ =
      detectionLatencyLeadingTerm ε piL θ
        (x₀ - capturedLowEquilibrium ζ injection) ζ := by
  let R := auditAlarmMagnitudeThreshold ε piL θ
  let a := |x₀ - capturedLowEquilibrium ζ injection|
  let amplitude := x₀ - capturedLowEquilibrium ζ injection
  let r := 1 + ζ
  have hamplitude : amplitude ≠ 0 := by
    simpa only [amplitude] using capturedLowAmplitude_ne_zero hζ hinjection hsign
  have hratio : 0 ≤ θ / (ε * piL) :=
    (div_pos hθ (mul_pos hε hpiL)).le
  have hR2 : R ^ 2 = θ / (ε * piL) := by
    dsimp only [R, auditAlarmMagnitudeThreshold]
    exact Real.sq_sqrt hratio
  have ha2 : a ^ 2 = amplitude ^ 2 := by
    dsimp only [a, amplitude]
    exact sq_abs _
  have harg : θ / (ε * piL * amplitude ^ 2) = (R / a) ^ 2 := by
    rw [div_pow, hR2, ha2]
    field_simp [hε.ne', hpiL.ne', hamplitude]
  change Real.log (R / a) / Real.log r =
    Real.log (θ / (ε * piL * amplitude ^ 2)) / (2 * Real.log r)
  rw [harg, Real.log_pow]
  ring

/-- The fixed-point offset correction is nonnegative. -/
theorem detectionLatencyOffset_nonneg
    {ε piL θ ζ injection : ℝ}
    (hε : 0 < ε) (hpiL : 0 < piL) (hθ : 0 < θ) (hζ : 0 < ζ) :
    0 ≤ detectionLatencyOffset ε piL θ ζ injection := by
  let R := auditAlarmMagnitudeThreshold ε piL θ
  let b := |capturedLowEquilibrium ζ injection|
  let r := 1 + ζ
  have hR : 0 < R := by
    dsimp only [R, auditAlarmMagnitudeThreshold]
    exact Real.sqrt_pos.2 (div_pos hθ (mul_pos hε hpiL))
  have hratio : 1 ≤ 1 + b / R := by
    exact le_add_of_nonneg_right (div_nonneg (abs_nonneg _) hR.le)
  have hlogr : 0 < Real.log r := by
    apply Real.log_pos
    dsimp only [r]
    linarith
  change 0 ≤ Real.log (1 + b / R) / Real.log r
  exact div_nonneg (Real.log_nonneg hratio) hlogr.le

/-- Once the alarm magnitude exceeds the offset magnitude, the offset
correction is at most `log 2 / log (1 + ζ)`. -/
theorem detectionLatencyOffset_le_log_two
    {ε piL θ ζ injection : ℝ}
    (hε : 0 < ε) (hpiL : 0 < piL) (hθ : 0 < θ) (hζ : 0 < ζ)
    (hoffset : |capturedLowEquilibrium ζ injection| ≤
      auditAlarmMagnitudeThreshold ε piL θ) :
    detectionLatencyOffset ε piL θ ζ injection ≤
      Real.log 2 / Real.log (1 + ζ) := by
  let R := auditAlarmMagnitudeThreshold ε piL θ
  let b := |capturedLowEquilibrium ζ injection|
  let r := 1 + ζ
  have hR : 0 < R := by
    dsimp only [R, auditAlarmMagnitudeThreshold]
    exact Real.sqrt_pos.2 (div_pos hθ (mul_pos hε hpiL))
  have hratioPos : 0 < 1 + b / R := by
    have : 0 ≤ b / R := div_nonneg (abs_nonneg _) hR.le
    linarith
  have hratioLe : 1 + b / R ≤ 2 := by
    have hdiv : b / R ≤ 1 := (div_le_iff₀ hR).2 (by
      simpa only [one_mul, b, R] using hoffset)
    linarith
  have hlogLe : Real.log (1 + b / R) ≤ Real.log 2 :=
    Real.log_le_log hratioPos hratioLe
  have hlogr : 0 < Real.log r := by
    apply Real.log_pos
    dsimp only [r]
    linarith
  change Real.log (1 + b / R) / Real.log r ≤ Real.log 2 / Real.log r
  exact div_le_div_of_nonneg_right hlogLe hlogr.le

/-- Exact first-alarm formula and explicit rounding remainder.  The range
condition names a finite small-weight regime through its equivalent magnitude
threshold. -/
theorem detectionLatency_exact
    {ε piL θ ζ injection x₀ : ℝ}
    (hε : 0 < ε) (hpiL : 0 < piL) (hθ : 0 < θ)
    (hζ : 0 < ζ) (hinjection : injection ≠ 0)
    (hsign : 0 ≤ x₀ * injection)
    (hrange : max |capturedLowEquilibrium ζ injection| |x₀| ≤
      auditAlarmMagnitudeThreshold ε piL θ) :
    let H := detectionLatencyHorizon ε piL θ ζ injection x₀
    let L := detectionLatencyLeadingTerm ε piL θ
      (x₀ - capturedLowEquilibrium ζ injection) ζ
    let δ := detectionLatencyOffset ε piL θ ζ injection
    auditAlarmAt ε piL θ ζ injection x₀ H ∧
      (∀ t < H, ¬auditAlarmAt ε piL θ ζ injection x₀ t) ∧
      δ ≤ (H : ℝ) - L ∧
      (H : ℝ) - L < δ + 1 ∧
      0 ≤ δ ∧
      δ ≤ Real.log 2 / Real.log (1 + ζ) := by
  dsimp only
  let q := detectionLatencyExactReal ε piL θ ζ injection x₀
  let H := detectionLatencyHorizon ε piL θ ζ injection x₀
  let L := detectionLatencyLeadingTerm ε piL θ
    (x₀ - capturedLowEquilibrium ζ injection) ζ
  let δ := detectionLatencyOffset ε piL θ ζ injection
  have hinitial : |x₀| ≤ auditAlarmMagnitudeThreshold ε piL θ :=
    (le_max_right _ _).trans hrange
  have hoffset : |capturedLowEquilibrium ζ injection| ≤
      auditAlarmMagnitudeThreshold ε piL θ :=
    (le_max_left _ _).trans hrange
  have hfirst := detectionLatencyHorizon_is_first_alarm
    hε hpiL hθ hζ hinjection hsign hinitial
  have hq : 0 ≤ q := by
    simpa only [q] using detectionLatencyExactReal_nonneg
      hε hpiL hθ hζ hinjection hsign hinitial
  have hdecompose : q = L + δ := by
    calc
      q = detectionLatencyGeometricLeadingTerm ε piL θ ζ injection x₀ +
          detectionLatencyOffset ε piL θ ζ injection := by
        simpa only [q] using detectionLatencyExactReal_eq_leading_add_offset
          hε hpiL hθ hζ hinjection hsign
      _ = L + δ := by
        rw [detectionLatencyGeometricLeadingTerm_eq_leadingTerm
          hε hpiL hθ hζ hinjection hsign]
  have hceilLower : q ≤ (H : ℝ) := by
    simpa only [H, detectionLatencyHorizon, q] using Nat.le_ceil q
  have hceilUpper : (H : ℝ) < q + 1 := by
    simpa only [H, detectionLatencyHorizon, q] using Nat.ceil_lt_add_one hq
  have hδnonneg : 0 ≤ δ := by
    simpa only [δ] using detectionLatencyOffset_nonneg hε hpiL hθ hζ
  have hδupper : δ ≤ Real.log 2 / Real.log (1 + ζ) := by
    simpa only [δ] using detectionLatencyOffset_le_log_two
      hε hpiL hθ hζ hoffset
  refine ⟨hfirst.1, hfirst.2, ?_, ?_, hδnonneg, hδupper⟩
  · linarith
  · linarith

#print axioms abs_capturedLowPath_eq
#print axioms auditAlarmAt_iff_threshold_le_abs
#print axioms auditAlarmAt_iff_exactReal_le
#print axioms detectionLatencyHorizon_is_first_alarm
#print axioms detectionLatencyExactReal_eq_leading_add_offset
#print axioms detectionLatencyGeometricLeadingTerm_eq_leadingTerm
#print axioms detectionLatencyOffset_nonneg
#print axioms detectionLatencyOffset_le_log_two
#print axioms detectionLatency_exact

end

end CivicAlignment.PaperIII
