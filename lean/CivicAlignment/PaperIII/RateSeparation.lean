/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.Observability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Find

/-!
# Paper III: audit-sensor detection latency

This file formalizes the exact mathematical core of `prop:latency`.  The
captured low coordinate is an affine recursion, its audit signal eventually
crosses every fixed threshold, and the displayed continuous leading term is
affine in `log (1 / ε)` with slope `1 / (2 * log (1 + ζ))`.

The exact ceiling formula and explicit integer-rounding remainder are proved
in `PaperIII/DetectionLatency.lean`; fitted numerical slopes remain battery
measurements.
-/

namespace CivicAlignment.PaperIII

open Filter Topology

/-! ## Exact captured-face path and alarm event -/

/-- The low coordinate on the captured face. -/
def capturedLowPath (ζ injection x₀ : ℝ) : ℕ → ℝ :=
  arithGeom (1 + ζ) injection x₀

/-- The affine recursion's (unstable) fixed point, denoted `bar x` in the paper. -/
noncomputable def capturedLowEquilibrium (ζ injection : ℝ) : ℝ :=
  -injection / ζ

/-- Magnitude of the low-coordinate contribution to the audit sensor. -/
def auditSensorMagnitude (ε piL x : ℝ) : ℝ :=
  (ε * piL) * x ^ 2

/-- The audit alarm has fired at time `t` when its magnitude reaches `θ`. -/
def auditAlarmAt (ε piL θ ζ injection x₀ : ℝ) (t : ℕ) : Prop :=
  θ ≤ auditSensorMagnitude ε piL (capturedLowPath ζ injection x₀ t)

/-- The exact affine-recursion closed form used in `prop:latency`. -/
theorem capturedLowPath_closedForm
    {ζ : ℝ} (hζ : ζ ≠ 0) (injection x₀ : ℝ) (t : ℕ) :
    capturedLowPath ζ injection x₀ t =
      (x₀ - capturedLowEquilibrium ζ injection) * (1 + ζ) ^ t +
        capturedLowEquilibrium ζ injection := by
  simp only [capturedLowPath, capturedLowEquilibrium]
  rw [arithGeom_eq (by
    intro h
    apply hζ
    linarith) t]
  field_simp [hζ]
  ring

/-- The exact discrete alarm condition after substituting the closed form. -/
theorem auditAlarmAt_iff_closedForm
    {ζ : ℝ} (hζ : ζ ≠ 0) (ε piL θ injection x₀ : ℝ) (t : ℕ) :
    auditAlarmAt ε piL θ ζ injection x₀ t ↔
      θ ≤ auditSensorMagnitude ε piL
        ((x₀ - capturedLowEquilibrium ζ injection) * (1 + ζ) ^ t +
          capturedLowEquilibrium ζ injection) := by
  simp only [auditAlarmAt]
  rw [capturedLowPath_closedForm hζ]

/-- Sign alignment makes the coefficient of the growing geometric term nonzero. -/
theorem capturedLowAmplitude_ne_zero
    {ζ injection x₀ : ℝ} (hζ : 0 < ζ) (hinjection : injection ≠ 0)
    (hsign : 0 ≤ x₀ * injection) :
    x₀ - capturedLowEquilibrium ζ injection ≠ 0 := by
  simp only [capturedLowEquilibrium]
  rw [neg_div, sub_neg_eq_add]
  rcases lt_or_gt_of_ne hinjection with hinjection_neg | hinjection_pos
  · have hx₀ : x₀ ≤ 0 := nonpos_of_mul_nonneg_left hsign hinjection_neg
    have hquotient : injection / ζ < 0 := div_neg_of_neg_of_pos hinjection_neg hζ
    apply ne_of_lt
    linarith
  · have hx₀ : 0 ≤ x₀ := nonneg_of_mul_nonneg_left hsign hinjection_pos
    have hquotient : 0 < injection / ζ := div_pos hinjection_pos hζ
    apply ne_of_gt
    linarith

/-- Under the paper's assumptions, the audit magnitude crosses every fixed threshold. -/
theorem tendsto_auditSensorMagnitude_atTop
    {ε piL ζ injection x₀ : ℝ} (hε : 0 < ε) (hpiL : 0 < piL)
    (hζ : 0 < ζ) (hinjection : injection ≠ 0) (hsign : 0 ≤ x₀ * injection) :
    Tendsto
      (fun t ↦ auditSensorMagnitude ε piL (capturedLowPath ζ injection x₀ t))
      atTop atTop := by
  have habs : Tendsto (fun t ↦ |capturedLowPath ζ injection x₀ t|) atTop atTop := by
    simpa only [capturedLowPath] using
      tendsto_abs_arithGeom_of_signAligned (by linarith) hinjection hsign
  have hsquare : Tendsto (fun t ↦ |capturedLowPath ζ injection x₀ t| ^ 2)
      atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).comp habs
  have hscaled := hsquare.const_mul_atTop (mul_pos hε hpiL)
  simpa only [auditSensorMagnitude, sq_abs] using hscaled

/-- A first discrete alarm time exists and is minimal. -/
theorem exists_firstAuditAlarm
    {ε piL θ ζ injection x₀ : ℝ} (hε : 0 < ε) (hpiL : 0 < piL)
    (hζ : 0 < ζ) (hinjection : injection ≠ 0) (hsign : 0 ≤ x₀ * injection) :
    ∃ t, auditAlarmAt ε piL θ ζ injection x₀ t ∧
      ∀ s < t, ¬auditAlarmAt ε piL θ ζ injection x₀ s := by
  classical
  have htend := tendsto_auditSensorMagnitude_atTop hε hpiL hζ hinjection hsign
  obtain ⟨t, ht⟩ := (htend.eventually_ge_atTop θ).exists
  have hex : ∃ t, auditAlarmAt ε piL θ ζ injection x₀ t := ⟨t, ht⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro s hs
  exact Nat.find_min hex hs

/-! ## Continuous leading term and its exact logarithmic slope -/

/-- The continuous leading term displayed in `prop:latency`. -/
noncomputable def detectionLatencyLeadingTerm
    (ε piL θ amplitude ζ : ℝ) : ℝ :=
  Real.log (θ / (ε * piL * amplitude ^ 2)) /
    (2 * Real.log (1 + ζ))

/-- The coefficient of `log (1 / ε)` in the latency leading term. -/
noncomputable def detectionLatencySlope (ζ : ℝ) : ℝ :=
  1 / (2 * Real.log (1 + ζ))

/-- The part of the leading term independent of the audit weight. -/
noncomputable def detectionLatencyIntercept
    (piL θ amplitude ζ : ℝ) : ℝ :=
  Real.log (θ / (piL * amplitude ^ 2)) /
    (2 * Real.log (1 + ζ))

/-- The displayed leading term is exactly affine in `log (1 / ε)`. -/
theorem detectionLatencyLeadingTerm_affine
    {ε piL θ amplitude ζ : ℝ}
    (hε : ε ≠ 0) (hpiL : piL ≠ 0) (hθ : θ ≠ 0) (hamplitude : amplitude ≠ 0) :
    detectionLatencyLeadingTerm ε piL θ amplitude ζ =
      detectionLatencySlope ζ * Real.log (1 / ε) +
        detectionLatencyIntercept piL θ amplitude ζ := by
  have hfactor :
      θ / (ε * piL * amplitude ^ 2) =
        (1 / ε) * (θ / (piL * amplitude ^ 2)) := by
    field_simp [hε, hpiL, hamplitude]
  have hinverse : (1 / ε : ℝ) ≠ 0 := one_div_ne_zero hε
  have hconstant : θ / (piL * amplitude ^ 2) ≠ 0 :=
    div_ne_zero hθ (mul_ne_zero hpiL (pow_ne_zero 2 hamplitude))
  simp only [detectionLatencyLeadingTerm, detectionLatencySlope,
    detectionLatencyIntercept, hfactor, Real.log_mul hinverse hconstant]
  ring

/-- Positive feedback makes the logarithmic latency slope strictly positive. -/
theorem detectionLatencySlope_pos {ζ : ℝ} (hζ : 0 < ζ) :
    0 < detectionLatencySlope ζ := by
  have hlog : 0 < Real.log (1 + ζ) := Real.log_pos (by linarith)
  simp only [detectionLatencySlope]
  positivity

/-- Finite differences have exactly the claimed slope in inverse-log weight. -/
theorem detectionLatencyLeadingTerm_sub
    {ε₁ ε₂ piL θ amplitude ζ : ℝ}
    (hε₁ : ε₁ ≠ 0) (hε₂ : ε₂ ≠ 0) (hpiL : piL ≠ 0)
    (hθ : θ ≠ 0) (hamplitude : amplitude ≠ 0) :
    detectionLatencyLeadingTerm ε₁ piL θ amplitude ζ -
        detectionLatencyLeadingTerm ε₂ piL θ amplitude ζ =
      detectionLatencySlope ζ *
        (Real.log (1 / ε₁) - Real.log (1 / ε₂)) := by
  rw [detectionLatencyLeadingTerm_affine hε₁ hpiL hθ hamplitude,
    detectionLatencyLeadingTerm_affine hε₂ hpiL hθ hamplitude]
  ring

/-! ## Sensor growth and parity -/

/-- The audit signal's successive ratio tends to `(1 + ζ)²`. -/
theorem tendsto_auditSensor_ratio
    {ε piL ζ injection x₀ : ℝ} (hε : ε ≠ 0) (hpiL : piL ≠ 0)
    (hζ : 0 < ζ) (hinjection : injection ≠ 0) (hsign : 0 ≤ x₀ * injection) :
    Tendsto
      (fun t ↦
        auditSensorMagnitude ε piL (capturedLowPath ζ injection x₀ (t + 1)) /
          auditSensorMagnitude ε piL (capturedLowPath ζ injection x₀ t))
      atTop (nhds ((1 + ζ) ^ 2)) := by
  have hratio := tendsto_arithGeom_ratio_of_signAligned
    (by linarith : 1 < 1 + ζ) hinjection hsign
  have hsquared := hratio.pow 2
  have habs := tendsto_abs_arithGeom_of_signAligned
    (by linarith : 1 < 1 + ζ) hinjection hsign
  apply hsquared.congr'
  filter_upwards [habs.eventually_gt_atTop 0] with t ht
  have hpath : capturedLowPath ζ injection x₀ t ≠ 0 := by
    simpa only [capturedLowPath] using (abs_pos.mp ht)
  simp only [auditSensorMagnitude, capturedLowPath]
  field_simp [hε, hpiL, hpath]

/-- The exact asymptotic logarithmic sensor-growth rate is `2 log (1 + ζ)`. -/
theorem tendsto_log_auditSensor_ratio
    {ε piL ζ injection x₀ : ℝ} (hε : ε ≠ 0) (hpiL : piL ≠ 0)
    (hζ : 0 < ζ) (hinjection : injection ≠ 0) (hsign : 0 ≤ x₀ * injection) :
    Tendsto
      (fun t ↦ Real.log
        (auditSensorMagnitude ε piL (capturedLowPath ζ injection x₀ (t + 1)) /
          auditSensorMagnitude ε piL (capturedLowPath ζ injection x₀ t)))
      atTop (nhds (2 * Real.log (1 + ζ))) := by
  have hratio := tendsto_auditSensor_ratio hε hpiL hζ hinjection hsign
  have hlimit : (1 + ζ) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith)
  have hlog := (Real.continuousAt_log hlimit).tendsto.comp hratio
  have hlog' :
      Tendsto
        (fun t ↦ Real.log
          (auditSensorMagnitude ε piL (capturedLowPath ζ injection x₀ (t + 1)) /
            auditSensorMagnitude ε piL (capturedLowPath ζ injection x₀ t)))
        atTop (nhds (Real.log ((1 + ζ) ^ 2))) := by
    apply hlog.congr'
    exact Eventually.of_forall fun _ ↦ rfl
  simpa only [Real.log_pow, Nat.cast_ofNat] using hlog'

/-- The squared audit sensor identifies magnitude exactly and is blind only to sign. -/
theorem auditSensorMagnitude_eq_iff_abs_eq
    {ε piL x y : ℝ} (hε : ε ≠ 0) (hpiL : piL ≠ 0) :
    auditSensorMagnitude ε piL x = auditSensorMagnitude ε piL y ↔ |x| = |y| := by
  simp only [auditSensorMagnitude]
  constructor
  · intro h
    exact (sq_eq_sq_iff_abs_eq_abs x y).mp
      (mul_left_cancel₀ (mul_ne_zero hε hpiL) h)
  · intro h
    exact congrArg (fun z : ℝ ↦ (ε * piL) * z)
      ((sq_eq_sq_iff_abs_eq_abs x y).mpr h)

/-- The exact conclusions of Paper III's detection-latency proposition. -/
structure DetectionLatencyConclusions
    (ε piL θ ζ injection x₀ : ℝ) : Prop where
  path_closed_form : ∀ t,
    capturedLowPath ζ injection x₀ t =
      (x₀ - capturedLowEquilibrium ζ injection) * (1 + ζ) ^ t +
        capturedLowEquilibrium ζ injection
  first_alarm : ∃ t, auditAlarmAt ε piL θ ζ injection x₀ t ∧
    ∀ s < t, ¬auditAlarmAt ε piL θ ζ injection x₀ s
  leading_term_affine :
    detectionLatencyLeadingTerm ε piL θ
        (x₀ - capturedLowEquilibrium ζ injection) ζ =
      detectionLatencySlope ζ * Real.log (1 / ε) +
        detectionLatencyIntercept piL θ
          (x₀ - capturedLowEquilibrium ζ injection) ζ
  slope_positive : 0 < detectionLatencySlope ζ
  sensor_ratio :
    Tendsto
      (fun t ↦
        auditSensorMagnitude ε piL (capturedLowPath ζ injection x₀ (t + 1)) /
          auditSensorMagnitude ε piL (capturedLowPath ζ injection x₀ t))
      atTop (nhds ((1 + ζ) ^ 2))
  log_sensor_ratio :
    Tendsto
      (fun t ↦ Real.log
        (auditSensorMagnitude ε piL (capturedLowPath ζ injection x₀ (t + 1)) /
          auditSensorMagnitude ε piL (capturedLowPath ζ injection x₀ t)))
      atTop (nhds (2 * Real.log (1 + ζ)))
  parity_blindness : ∀ x y,
    auditSensorMagnitude ε piL x = auditSensorMagnitude ε piL y ↔ |x| = |y|

/--
Paper III, Theorem 6.3 (`prop:latency`), `civic_loops.tex:376`.

The captured low coordinate has the paper's exact affine closed form, its
positive-weight audit signal has a first threshold-crossing time, and the
displayed continuous leading term is affine in `log (1 / ε)` with the claimed
positive slope.  The signal ratio and its logarithm converge to `(1 + ζ)²`
and `2 log (1 + ζ)`, respectively, and squaring loses exactly the sign.

The exact discrete first-alarm formula and rounding remainder are proved in
`PaperIII/DetectionLatency.lean`. Numerical regression statistics remain
battery measurements.
-/
theorem detectionLatency
    {ε piL θ ζ injection x₀ : ℝ}
    (hε : 0 < ε) (hpiL : 0 < piL) (hθ : 0 < θ) (hζ : 0 < ζ)
    (hinjection : injection ≠ 0) (hsign : 0 ≤ x₀ * injection) :
    DetectionLatencyConclusions ε piL θ ζ injection x₀ := by
  have hamplitude : x₀ - capturedLowEquilibrium ζ injection ≠ 0 :=
    capturedLowAmplitude_ne_zero hζ hinjection hsign
  constructor
  · exact capturedLowPath_closedForm hζ.ne' injection x₀
  · exact exists_firstAuditAlarm hε hpiL hζ hinjection hsign
  · exact detectionLatencyLeadingTerm_affine hε.ne' hpiL.ne' hθ.ne' hamplitude
  · exact detectionLatencySlope_pos hζ
  · exact tendsto_auditSensor_ratio hε.ne' hpiL.ne' hζ hinjection hsign
  · exact tendsto_log_auditSensor_ratio hε.ne' hpiL.ne' hζ hinjection hsign
  · intro x y
    exact auditSensorMagnitude_eq_iff_abs_eq hε.ne' hpiL.ne'

#print axioms capturedLowPath_closedForm
#print axioms auditAlarmAt_iff_closedForm
#print axioms capturedLowAmplitude_ne_zero
#print axioms tendsto_auditSensorMagnitude_atTop
#print axioms exists_firstAuditAlarm
#print axioms detectionLatencyLeadingTerm_affine
#print axioms detectionLatencySlope_pos
#print axioms detectionLatencyLeadingTerm_sub
#print axioms tendsto_auditSensor_ratio
#print axioms tendsto_log_auditSensor_ratio
#print axioms auditSensorMagnitude_eq_iff_abs_eq
#print axioms detectionLatency

end CivicAlignment.PaperIII
