/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.ClippedStep
import CivicAlignment.PaperII.Bistability
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Satisfaction--capacity decoupling

This file formalizes Paper II's two-type pure-agreement loop.  It separates
the exact sign-alignment and gradient arguments from the claims that require
eventual capture, and states the residual-deference contraction with its
mathematically valid truncated factor `max 0 (1-k)`.
-/

namespace CivicAlignment.PaperII

noncomputable section

open Filter Set Topology

/-- Parameters of Paper II's two-type laundering model. -/
structure LaunderingParams where
  πH : ℝ
  πL : ℝ
  ηH : ℝ
  ηL : ℝ
  κ : ℝ
  ζ : ℝ
  α : ℝ
  ιH : ℝ
  ιL : ℝ

/-- The standing restrictions in the model paragraph preceding `thm:launder`. -/
structure LaunderingAssumptions (q : LaunderingParams) : Prop where
  πH_nonneg : 0 ≤ q.πH
  πL_pos : 0 < q.πL
  ηH_pos : 0 < q.ηH
  ηH_le_one : q.ηH ≤ 1
  ηL_pos : 0 < q.ηL
  ηL_le_one : q.ηL ≤ 1
  κ_pos : 0 < q.κ
  κ_le_one : q.κ ≤ 1
  ζ_pos : 0 < q.ζ
  ζ_lt_honest_contraction : q.ζ < q.ηH * q.κ
  α_pos : 0 < q.α
  ιL_ne_zero : q.ιL ≠ 0

namespace LaunderingParams

/-- Residual output-to-prior weight of the high type. -/
def highResidual (q : LaunderingParams) (β : ℝ) : ℝ :=
  1 - (1 - q.κ) * β

/-- Residual output-to-prior weight of the low type. -/
def lowResidual (β : ℝ) : ℝ :=
  1 - β

/-- Evidence weight of the high type. -/
def highEvidenceWeight (q : LaunderingParams) (β : ℝ) : ℝ :=
  q.ηH * q.highResidual β

/-- Evidence weight of the low type. -/
def lowEvidenceWeight (q : LaunderingParams) (β : ℝ) : ℝ :=
  q.ηL * lowResidual β

/-- High-type deviation multiplier, including stratification feedback. -/
def highDeviationMultiplier (q : LaunderingParams) (β : ℝ) : ℝ :=
  1 - q.highEvidenceWeight β + q.ζ

/-- Low-type deviation multiplier, including stratification feedback. -/
def lowDeviationMultiplier (q : LaunderingParams) (β : ℝ) : ℝ :=
  1 - q.lowEvidenceWeight β + q.ζ

/-- Pure measured agreement satisfaction at held-fixed deviations. -/
def launderingSatisfaction (q : LaunderingParams) (β xH xL : ℝ) : ℝ :=
  -q.πH * q.highResidual β ^ 2 * xH ^ 2 -
    q.πL * lowResidual β ^ 2 * xL ^ 2

/-- The exact instantaneous gradient displayed in `thm:launder(i)`. -/
def launderingGradient (q : LaunderingParams) (β xH xL : ℝ) : ℝ :=
  2 * q.πH * (1 - q.κ) * q.highResidual β * xH ^ 2 +
    2 * q.πL * lowResidual β * xL ^ 2

end LaunderingParams

open LaunderingParams

/-- The exact conclusion of Paper II's `prop:myopia` on the interval from zero to `B`. -/
def MyopiaTrapOn (η e ζ ι B : ℝ) : Prop :=
  (∀ β ∈ Icc (0 : ℝ) B,
    feedbackDeviationStep η e ζ ι β (feedbackStationaryDeviation η e ζ ι β) =
      feedbackStationaryDeviation η e ζ ι β) ∧
    StrictMonoOn (feedbackStationaryGap η e ζ ι) (Icc (0 : ℝ) B) ∧
    StrictAntiOn (fun β ↦ -feedbackStationaryGap η e ζ ι β) (Icc (0 : ℝ) B) ∧
    ∀ β ∈ Icc (0 : ℝ) B,
      0 < instantaneousAgreementGradient e β
        (feedbackStationaryDeviation η e ζ ι β)

/-- The displayed gradient is the derivative of measured satisfaction at fixed deviations. -/
theorem hasDerivAt_launderingSatisfaction (q : LaunderingParams) (β xH xL : ℝ) :
    HasDerivAt (fun policy ↦ q.launderingSatisfaction policy xH xL)
      (q.launderingGradient β xH xL) β := by
  have hHigh : HasDerivAt q.highResidual (-(1 - q.κ)) β := by
    have hlinear : HasDerivAt (fun x : ℝ ↦ (1 - q.κ) * x) (1 - q.κ) β := by
      simpa using (hasDerivAt_id β).const_mul (1 - q.κ)
    change HasDerivAt (fun x : ℝ ↦ 1 - (1 - q.κ) * x) (-(1 - q.κ)) β
    exact hlinear.const_sub 1
  have hLow : HasDerivAt lowResidual (-1) β := by
    change HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) β
    simpa using (hasDerivAt_id β).const_sub 1
  have hHighTerm : HasDerivAt
      (fun policy ↦ -q.πH * q.highResidual policy ^ 2 * xH ^ 2)
      (2 * q.πH * (1 - q.κ) * q.highResidual β * xH ^ 2) β := by
    exact (((hHigh.pow 2).const_mul (-q.πH)).mul_const (xH ^ 2)).congr_deriv
      (by ring)
  have hLowTerm : HasDerivAt
      (fun policy ↦ q.πL * lowResidual policy ^ 2 * xL ^ 2)
      (-2 * q.πL * lowResidual β * xL ^ 2) β := by
    exact (((hLow.pow 2).const_mul q.πL).mul_const (xL ^ 2)).congr_deriv
      (by ring)
  exact (hHighTerm.sub hLowTerm).congr_deriv (by
    simp only [launderingGradient]
    ring)

/-- Both type-specific residual weights are nonnegative on the policy interval. -/
theorem launderingResiduals_nonnegative {q : LaunderingParams}
    (model : LaunderingAssumptions q) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 ≤ q.highResidual β ∧ 0 ≤ lowResidual β := by
  have hExtract : 0 ≤ 1 - q.κ := sub_nonneg.mpr model.κ_le_one
  have hProduct : (1 - q.κ) * β ≤ 1 := calc
    (1 - q.κ) * β ≤ (1 - q.κ) * 1 := mul_le_mul_of_nonneg_left hβ.2 hExtract
    _ = 1 - q.κ := mul_one _
    _ ≤ 1 := by linarith [model.κ_pos]
  exact ⟨by simp only [highResidual]; linarith,
    by simp only [lowResidual]; linarith [hβ.2]⟩

/-- The pure-agreement gradient is nonnegative everywhere on the policy interval. -/
theorem launderingGradient_nonnegative {q : LaunderingParams}
    (model : LaunderingAssumptions q) {β xH xL : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 ≤ q.launderingGradient β xH xL := by
  have hresidual := launderingResiduals_nonnegative model hβ
  have hExtract : 0 ≤ 1 - q.κ := sub_nonneg.mpr model.κ_le_one
  simp only [launderingGradient]
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) model.πH_nonneg) hExtract)
        hresidual.1)
      (sq_nonneg xH))
    (mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) model.πL_pos.le) hresidual.2)
      (sq_nonneg xL))

/-- The low-type multiplier is strictly positive on the policy interval. -/
theorem lowDeviationMultiplier_pos {q : LaunderingParams}
    (model : LaunderingAssumptions q) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 < q.lowDeviationMultiplier β := by
  have hresidual : 0 ≤ lowResidual β := (launderingResiduals_nonnegative model hβ).2
  have hweight_le_one : q.lowEvidenceWeight β ≤ 1 := by
    have hresidual_le : lowResidual β ≤ 1 := by
      simp only [lowResidual]
      linarith [hβ.1]
    calc
      q.lowEvidenceWeight β ≤ q.ηL * 1 := by
        simp only [lowEvidenceWeight]
        exact mul_le_mul_of_nonneg_left hresidual_le model.ηL_pos.le
      _ = q.ηL := mul_one _
      _ ≤ 1 := model.ηL_le_one
  simp only [lowDeviationMultiplier]
  linarith [model.ζ_pos]

/-- A low-type sequence obeys the paper's affine deviation recursion. -/
def IsLowDeviationTrajectory (q : LaunderingParams) (β xL : ℕ → ℝ) : Prop :=
  ∀ t, xL (t + 1) = q.lowDeviationMultiplier (β t) * xL t + q.ιL

/-- Sign alignment is invariant and gives the claimed one-step absolute lower bound. -/
theorem low_sign_alignment {q : LaunderingParams} (model : LaunderingAssumptions q)
    {β xL : ℕ → ℝ} (hβ : ∀ t, β t ∈ Icc (0 : ℝ) 1)
    (hstep : IsLowDeviationTrajectory q β xL) (haligned : 0 ≤ xL 0 * q.ιL) :
    (∀ t, 0 ≤ xL t * q.ιL) ∧ ∀ t, |q.ιL| ≤ |xL (t + 1)| := by
  have hmultiplier : ∀ t, 0 < q.lowDeviationMultiplier (β t) :=
    fun t ↦ lowDeviationMultiplier_pos model (hβ t)
  have hsign : ∀ t, 0 ≤ xL t * q.ιL := by
    intro t
    induction t with
    | zero => exact haligned
    | succ t ih =>
        rw [hstep t]
        nlinarith [mul_nonneg (hmultiplier t).le ih, sq_nonneg q.ιL]
  refine ⟨hsign, ?_⟩
  intro t
  rcases lt_or_gt_of_ne model.ιL_ne_zero with hιneg | hιpos
  · have hsign' : 0 ≤ q.ιL * xL t := by simpa only [mul_comm] using hsign t
    have hxnonpos : xL t ≤ 0 := nonpos_of_mul_nonneg_right hsign' hιneg
    have hnext : xL (t + 1) ≤ q.ιL := by
      rw [hstep t]
      exact add_le_of_nonpos_left (mul_nonpos_of_nonneg_of_nonpos (hmultiplier t).le hxnonpos)
    rw [abs_of_neg hιneg, abs_of_neg (lt_of_le_of_lt hnext hιneg)]
    linarith
  · have hsign' : 0 ≤ q.ιL * xL t := by simpa only [mul_comm] using hsign t
    have hxnonneg : 0 ≤ xL t := nonneg_of_mul_nonneg_right hsign' hιpos
    have hnext : q.ιL ≤ xL (t + 1) := by
      rw [hstep t]
      exact le_add_of_nonneg_left (mul_nonneg (hmultiplier t).le hxnonneg)
    rw [abs_of_pos hιpos, abs_of_pos (lt_of_lt_of_le hιpos hnext)]
    exact hnext

/-- A triple of paths obeys the two deviation recursions and projected-gradient policy update. -/
structure IsLaunderingTrajectory (q : LaunderingParams)
    (β xH xL : ℕ → ℝ) : Prop where
  policy_mem : ∀ t, β t ∈ Icc (0 : ℝ) 1
  high_step : ∀ t,
    xH (t + 1) = q.highDeviationMultiplier (β t) * xH t + q.ιH
  low_step : IsLowDeviationTrajectory q β xL
  policy_step : ∀ t,
    β (t + 1) = LoopParams.clipUnit
      (β t + q.α * q.launderingGradient (β t) (xH t) (xL t))

/-- Projection is the identity on its target interval: `lem:clip`(ii), inactive case. -/
theorem laundering_clipUnit_eq_self {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    LoopParams.clipUnit x = x :=
  clipUnit_eq_self' hx

/-- The policy path is nondecreasing because every instantaneous gradient is nonnegative. -/
theorem laundering_policy_monotone {q : LaunderingParams}
    (model : LaunderingAssumptions q) {β xH xL : ℕ → ℝ}
    (trajectory : IsLaunderingTrajectory q β xH xL) : Monotone β := by
  apply monotone_nat_of_le_succ
  intro t
  rw [trajectory.policy_step t]
  have hgradient := launderingGradient_nonnegative model
    (xH := xH t) (xL := xL t) (trajectory.policy_mem t)
  have hinput : β t ≤ β t + q.α * q.launderingGradient (β t) (xH t) (xL t) :=
    le_add_of_nonneg_right (mul_nonneg model.α_pos.le hgradient)
  have hclip := LoopParams.monotone_clipUnit hinput
  rw [laundering_clipUnit_eq_self (trajectory.policy_mem t)] at hclip
  exact hclip

/-- After the first update, the instantaneous gradient has the paper's low-channel floor. -/
theorem launderingGradient_floor {q : LaunderingParams}
    (model : LaunderingAssumptions q) {β xH xL : ℕ → ℝ}
    (trajectory : IsLaunderingTrajectory q β xH xL)
    (haligned : 0 ≤ xL 0 * q.ιL) (t : ℕ) :
    2 * q.πL * lowResidual (β (t + 1)) * q.ιL ^ 2 ≤
      q.launderingGradient (β (t + 1)) (xH (t + 1)) (xL (t + 1)) := by
  have habs := (low_sign_alignment model trajectory.policy_mem trajectory.low_step haligned).2 t
  have hsquare : q.ιL ^ 2 ≤ xL (t + 1) ^ 2 := by
    have := (sq_le_sq₀ (abs_nonneg q.ιL) (abs_nonneg (xL (t + 1)))).2 habs
    simpa only [sq_abs] using this
  have hresidual := launderingResiduals_nonnegative model (trajectory.policy_mem (t + 1))
  have hlowCoefficient : 0 ≤ 2 * q.πL * lowResidual (β (t + 1)) :=
    mul_nonneg (mul_nonneg (by norm_num) model.πL_pos.le) hresidual.2
  have hlow := mul_le_mul_of_nonneg_left hsquare hlowCoefficient
  have hExtract : 0 ≤ 1 - q.κ := sub_nonneg.mpr model.κ_le_one
  have hhigh : 0 ≤
      2 * q.πH * (1 - q.κ) * q.highResidual (β (t + 1)) * xH (t + 1) ^ 2 :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) model.πH_nonneg) hExtract)
        hresidual.1)
      (sq_nonneg _)
  simp only [launderingGradient]
  linarith

namespace LaunderingParams

/-- The low-channel feedback coefficient in the residual-policy recursion. -/
def captureRate (q : LaunderingParams) : ℝ :=
  2 * q.α * q.πL * q.ιL ^ 2

/-- The valid contraction factor, including the finite-clipping regime. -/
def captureFactor (q : LaunderingParams) : ℝ :=
  max 0 (1 - q.captureRate)

end LaunderingParams

/-- The capture rate is strictly positive. -/
theorem captureRate_pos {q : LaunderingParams} (model : LaunderingAssumptions q) :
    0 < q.captureRate := by
  simp only [captureRate]
  exact mul_pos
    (mul_pos (mul_pos two_pos model.α_pos) model.πL_pos)
    (sq_pos_of_ne_zero model.ιL_ne_zero)

/-- The truncated contraction factor lies in `[0,1)`. -/
theorem captureFactor_nonneg_lt_one {q : LaunderingParams}
    (model : LaunderingAssumptions q) :
    0 ≤ q.captureFactor ∧ q.captureFactor < 1 := by
  have hk := captureRate_pos model
  simp only [captureFactor]
  exact ⟨le_max_left _ _, max_lt zero_lt_one (by linarith)⟩

/-- Exact residual after clipping an ideal floor-sized gradient step. -/
theorem one_sub_clip_captureTarget {β k : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1)
    (hk : 0 ≤ k) :
    1 - LoopParams.clipUnit (β + k * (1 - β)) =
      max 0 (1 - k) * (1 - β) := by
  by_cases hk₁ : k ≤ 1
  · have htargetLower : 0 ≤ β + k * (1 - β) := by
      exact add_nonneg hβ.1 (mul_nonneg hk (sub_nonneg.mpr hβ.2))
    have htargetUpper : β + k * (1 - β) ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hk₁) (sub_nonneg.mpr hβ.2)]
    rw [laundering_clipUnit_eq_self ⟨htargetLower, htargetUpper⟩,
      max_eq_right (sub_nonneg.mpr hk₁)]
    ring
  · have hkgt : 1 < k := lt_of_not_ge hk₁
    have htarget : 1 ≤ β + k * (1 - β) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hβ.2) (sub_nonneg.mpr hkgt.le)]
    rw [clipUnit_eq_one_of_le htarget, max_eq_left (by linarith : 1 - k ≤ 0)]
    ring

/-- The corrected geometric contraction of residual deference after time one. -/
theorem laundering_residual_contraction {q : LaunderingParams}
    (model : LaunderingAssumptions q) {β xH xL : ℕ → ℝ}
    (trajectory : IsLaunderingTrajectory q β xH xL)
    (haligned : 0 ≤ xL 0 * q.ιL) (t : ℕ) :
    1 - β (t + 2) ≤ q.captureFactor * (1 - β (t + 1)) := by
  have hfloor := launderingGradient_floor model trajectory haligned t
  have hscaled : q.captureRate * lowResidual (β (t + 1)) ≤
      q.α * q.launderingGradient (β (t + 1)) (xH (t + 1)) (xL (t + 1)) := by
    simp only [captureRate]
    nlinarith [mul_nonneg model.α_pos.le
      (sub_nonneg.mpr hfloor)]
  have hinput : β (t + 1) + q.captureRate * (1 - β (t + 1)) ≤
      β (t + 1) + q.α * q.launderingGradient (β (t + 1))
        (xH (t + 1)) (xL (t + 1)) := by
    simpa only [lowResidual, add_comm] using add_le_add_left hscaled (β (t + 1))
  have hclip := LoopParams.monotone_clipUnit hinput
  rw [← trajectory.policy_step (t + 1)] at hclip
  have hresidual : 1 - β (t + 2) ≤
      1 - LoopParams.clipUnit
        (β (t + 1) + q.captureRate * (1 - β (t + 1))) := by
    linarith
  rw [one_sub_clip_captureTarget (trajectory.policy_mem (t + 1))
    (captureRate_pos model).le] at hresidual
  exact hresidual

/-- Under the omitted small-update condition, the paper's untruncated factor is valid. -/
theorem laundering_residual_contraction_of_rate_le_one {q : LaunderingParams}
    (model : LaunderingAssumptions q) {β xH xL : ℕ → ℝ}
    (trajectory : IsLaunderingTrajectory q β xH xL)
    (haligned : 0 ≤ xL 0 * q.ιL) (hrate : q.captureRate ≤ 1) (t : ℕ) :
    1 - β (t + 2) ≤ (1 - q.captureRate) * (1 - β (t + 1)) := by
  simpa only [LaunderingParams.captureFactor,
    max_eq_right (sub_nonneg.mpr hrate)] using
    laundering_residual_contraction model trajectory haligned t

/-- A negative untruncated factor cannot bound a nonzero residual-policy distance. -/
theorem laundering_untruncated_contraction_impossible_of_rate_gt_one
    {q : LaunderingParams} {β xH xL : ℕ → ℝ}
    (trajectory : IsLaunderingTrajectory q β xH xL)
    (hrate : 1 < q.captureRate) {t : ℕ} (hinterior : β (t + 1) < 1) :
    ¬1 - β (t + 2) ≤ (1 - q.captureRate) * (1 - β (t + 1)) := by
  have hleft : 0 ≤ 1 - β (t + 2) := sub_nonneg.mpr (trajectory.policy_mem (t + 2)).2
  have hright : (1 - q.captureRate) * (1 - β (t + 1)) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (sub_pos.mpr hinterior)
  linarith

/-- Iterating the corrected contraction gives an explicit geometric upper bound. -/
theorem laundering_residual_geometric_bound {q : LaunderingParams}
    (model : LaunderingAssumptions q) {β xH xL : ℕ → ℝ}
    (trajectory : IsLaunderingTrajectory q β xH xL)
    (haligned : 0 ≤ xL 0 * q.ιL) :
    ∀ n, 1 - β (n + 1) ≤ q.captureFactor ^ n * (1 - β 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep := laundering_residual_contraction model trajectory haligned n
      have hfactor := (captureFactor_nonneg_lt_one model).1
      have hmul := mul_le_mul_of_nonneg_left ih hfactor
      rw [pow_succ]
      nlinarith

/-- The deference policy converges globally to the capture face. -/
theorem laundering_policy_tendsto_one {q : LaunderingParams}
    (model : LaunderingAssumptions q) {β xH xL : ℕ → ℝ}
    (trajectory : IsLaunderingTrajectory q β xH xL)
    (haligned : 0 ≤ xL 0 * q.ιL) :
    Tendsto β atTop (nhds 1) := by
  have hfactor := captureFactor_nonneg_lt_one model
  have hupper := laundering_residual_geometric_bound model trajectory haligned
  have hpow : Tendsto
      (fun n : ℕ ↦ q.captureFactor ^ n * (1 - β 1)) atTop (nhds 0) :=
    by simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hfactor.1 hfactor.2).mul_const (1 - β 1)
  have hresidualTail : Tendsto (fun n : ℕ ↦ 1 - β (n + 1)) atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun n ↦ sub_nonneg.mpr (trajectory.policy_mem (n + 1)).2
    · exact hupper
    · exact hpow
  have htail : Tendsto (fun n : ℕ ↦ β (n + 1)) atTop (nhds 1) := by
    have hconst : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have h := hconst.sub hresidualTail
    convert h using 1 <;> norm_num
  exact (tendsto_add_atTop_iff_nat 1).mp htail

/-- The low feedback channel eventually leaves the contracting regime required by `prop:myopia`. -/
theorem laundering_low_feedback_eventually_noncontracting {q : LaunderingParams}
    (model : LaunderingAssumptions q) {β xH xL : ℕ → ℝ}
    (trajectory : IsLaunderingTrajectory q β xH xL)
    (haligned : 0 ≤ xL 0 * q.ιL) :
    ∀ᶠ t in atTop, q.lowEvidenceWeight (β t) < q.ζ := by
  have hβ := laundering_policy_tendsto_one model trajectory haligned
  have hresidual : Tendsto (fun t ↦ 1 - β t) atTop (nhds 0) := by
    simpa only [sub_self] using
      (show Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) from
        tendsto_const_nhds).sub hβ
  have hweight : Tendsto (fun t ↦ q.lowEvidenceWeight (β t)) atTop (nhds 0) := by
    simpa only [lowEvidenceWeight, lowResidual, mul_zero] using
      hresidual.const_mul q.ηL
  exact (tendsto_order.1 hweight).2 q.ζ model.ζ_pos

/-- On every contracting low-type prefix, the clause (iii) invokes `prop:myopia`. -/
theorem laundering_low_myopiaTrapOn {q : LaunderingParams}
    (model : LaunderingAssumptions q) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1)
    (hcontract : q.ζ < q.lowEvidenceWeight β) :
    MyopiaTrapOn q.ηL 0 q.ζ q.ιL β := by
  simpa only [MyopiaTrapOn] using
    myopiaTrap q.ηL 0 q.ζ q.ιL β model.ηL_pos (by norm_num) (by norm_num)
      model.ζ_pos model.ιL_ne_zero hβ.1 hβ.2 (by
        simpa only [lowEvidenceWeight, lowResidual, remainingExposure, sub_zero,
          one_mul] using hcontract)

/-- The high-type use of `prop:myopia` is valid with its two missing nondegeneracy hypotheses. -/
theorem laundering_high_myopiaTrapOn {q : LaunderingParams}
    (model : LaunderingAssumptions q) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1)
    (hκ : q.κ < 1) (hιH : q.ιH ≠ 0)
    (hcontract : q.ζ < q.highEvidenceWeight β) :
    MyopiaTrapOn q.ηH q.κ q.ζ q.ιH β := by
  simpa only [MyopiaTrapOn] using
    myopiaTrap q.ηH q.κ q.ζ q.ιH β model.ηH_pos model.κ_pos.le hκ
      model.ζ_pos hιH hβ.1 hβ.2 (by
        simpa only [highEvidenceWeight, highResidual, remainingExposure] using hcontract)

/-- With zero injection, the stationary reward gradient in `prop:myopia` is exactly zero. -/
theorem myopia_stationaryGradient_eq_zero_of_injection_zero (η e ζ β : ℝ) :
    instantaneousAgreementGradient e β
      (feedbackStationaryDeviation η e ζ 0 β) = 0 := by
  simp [instantaneousAgreementGradient, feedbackStationaryDeviation]

/-- At full extraction, policy cannot change agreement, so the myopic reward gradient is zero. -/
theorem myopia_stationaryGradient_eq_zero_of_full_extraction (η ζ ι β : ℝ) :
    instantaneousAgreementGradient 1 β
      (feedbackStationaryDeviation η 1 ζ ι β) = 0 := by
  simp [instantaneousAgreementGradient]

/-- The permitted `ιH = 0` endpoint is contracting at `β = 0`, but its stationary
high-channel reward gradient vanishes at every policy. -/
theorem laundering_high_zero_injection_myopia_counterexample {q : LaunderingParams}
    (model : LaunderingAssumptions q) (hιH : q.ιH = 0) :
    q.ζ < q.highEvidenceWeight 0 ∧
      ∀ β, instantaneousAgreementGradient q.κ β
        (feedbackStationaryDeviation q.ηH q.κ q.ζ q.ιH β) = 0 := by
  constructor
  · have hκle : q.ηH * q.κ ≤ q.ηH := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left model.κ_le_one model.ηH_pos.le
    simpa only [highEvidenceWeight, highResidual, mul_zero, sub_zero, mul_one] using
      lt_of_lt_of_le model.ζ_lt_honest_contraction hκle
  · intro β
    rw [hιH]
    exact myopia_stationaryGradient_eq_zero_of_injection_zero q.ηH q.κ q.ζ β

/-- The permitted `κ = 1` endpoint is contracting at `β = 0`, but its
high-channel reward gradient vanishes at every belief and policy. -/
theorem laundering_high_full_extraction_myopia_counterexample {q : LaunderingParams}
    (model : LaunderingAssumptions q) (hκ : q.κ = 1) :
    q.ζ < q.highEvidenceWeight 0 ∧
      ∀ β x, instantaneousAgreementGradient q.κ β x = 0 := by
  constructor
  · simpa only [highEvidenceWeight, highResidual, mul_zero, sub_zero, hκ, mul_one] using
      model.ζ_lt_honest_contraction
  · intro β x
    simp [hκ, instantaneousAgreementGradient]

/-- Once the capture face is reached, nonnegative gradient makes it absorbing. -/
theorem laundering_capture_absorbing {q : LaunderingParams}
    (model : LaunderingAssumptions q) {xH xL : ℝ} :
    LoopParams.clipUnit (1 + q.α * q.launderingGradient 1 xH xL) = 1 := by
  have hgradient := launderingGradient_nonnegative model
    (xH := xH) (xL := xL) (right_mem_Icc.mpr zero_le_one)
  have hright : 1 ≤ 1 + q.α * q.launderingGradient 1 xH xL :=
    le_add_of_nonneg_right (mul_nonneg model.α_pos.le hgradient)
  exact clipUnit_eq_one_of_le hright

/-- Under sign alignment, the absolute low deviation obeys an exact positive affine law. -/
theorem low_abs_step {q : LaunderingParams} (model : LaunderingAssumptions q)
    {β xL : ℕ → ℝ} (hβ : ∀ t, β t ∈ Icc (0 : ℝ) 1)
    (hstep : IsLowDeviationTrajectory q β xL) (haligned : 0 ≤ xL 0 * q.ιL)
    (t : ℕ) :
    |xL (t + 1)| = q.lowDeviationMultiplier (β t) * |xL t| + |q.ιL| := by
  have hsign := (low_sign_alignment model hβ hstep haligned).1 t
  have hmultiplier := lowDeviationMultiplier_pos model (hβ t)
  rcases lt_or_gt_of_ne model.ιL_ne_zero with hιneg | hιpos
  · have hsign' : 0 ≤ q.ιL * xL t := by simpa only [mul_comm] using hsign
    have hx : xL t ≤ 0 := nonpos_of_mul_nonneg_right hsign' hιneg
    have hnext : xL (t + 1) < 0 := by
      rw [hstep t]
      have := mul_nonpos_of_nonneg_of_nonpos hmultiplier.le hx
      linarith
    rw [abs_of_nonpos hx, abs_of_neg hιneg, abs_of_neg hnext, hstep t]
    ring
  · have hsign' : 0 ≤ q.ιL * xL t := by simpa only [mul_comm] using hsign
    have hx : 0 ≤ xL t := nonneg_of_mul_nonneg_right hsign' hιpos
    have hnext : 0 < xL (t + 1) := by
      rw [hstep t]
      have := mul_nonneg hmultiplier.le hx
      linarith
    rw [abs_of_nonneg hx, abs_of_pos hιpos, abs_of_pos hnext, hstep t]

/-- The low deviation diverges in magnitude as the policy approaches capture. -/
theorem laundering_low_abs_tendsto_atTop {q : LaunderingParams}
    (model : LaunderingAssumptions q) {β xH xL : ℕ → ℝ}
    (trajectory : IsLaunderingTrajectory q β xH xL)
    (haligned : 0 ≤ xL 0 * q.ιL) :
    Tendsto (fun t ↦ |xL t|) atTop atTop := by
  have hβlimit := laundering_policy_tendsto_one model trajectory haligned
  have hresidual : Tendsto (fun t ↦ 1 - β t) atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    simpa only [sub_self] using hconst.sub hβlimit
  have hweight : Tendsto (fun t ↦ q.ηL * (1 - β t)) atTop (nhds 0) := by
    simpa only [mul_zero] using hresidual.const_mul q.ηL
  have hevent : ∀ᶠ t in atTop, q.ηL * (1 - β t) < q.ζ / 2 :=
    (tendsto_order.1 hweight).2 (q.ζ / 2) (by linarith [model.ζ_pos])
  rcases (eventually_atTop.1 hevent) with ⟨N, hN⟩
  let a : ℝ := 1 + q.ζ / 2
  have ha : 1 < a := by dsimp only [a]; linarith [model.ζ_pos]
  have hmultiplier : ∀ t, N ≤ t → a ≤ q.lowDeviationMultiplier (β t) := by
    intro t ht
    have hw := hN t ht
    simp only [a, lowDeviationMultiplier, lowEvidenceWeight, lowResidual]
    linarith
  have hbound : ∀ n, a ^ n * |q.ιL| ≤ |xL (N + 1 + n)| := by
    intro n
    induction n with
    | zero =>
        simpa only [pow_zero, one_mul, add_zero] using
          (low_sign_alignment model trajectory.policy_mem trajectory.low_step haligned).2 N
    | succ n ih =>
        have htime : N ≤ N + 1 + n := by omega
        have hmul := mul_le_mul_of_nonneg_right (hmultiplier (N + 1 + n) htime)
          (abs_nonneg (xL (N + 1 + n)))
        have habs := low_abs_step model trajectory.policy_mem trajectory.low_step haligned
          (N + 1 + n)
        have hscaled : a * (a ^ n * |q.ιL|) ≤ a * |xL (N + 1 + n)| :=
          mul_le_mul_of_nonneg_left ih (le_trans zero_le_one ha.le)
        rw [show N + 1 + (n + 1) = (N + 1 + n) + 1 by omega, habs]
        rw [pow_succ]
        nlinarith [hscaled, abs_nonneg q.ιL]
  have hlower : Tendsto (fun n : ℕ ↦ a ^ n * |q.ιL|) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt ha).atTop_mul_const
      (abs_pos.mpr model.ιL_ne_zero)
  have htail : Tendsto (fun n : ℕ ↦ |xL (N + 1 + n)|) atTop atTop :=
    tendsto_atTop_mono' atTop (Eventually.of_forall hbound) hlower
  have htail' : Tendsto (fun n : ℕ ↦ |xL (n + (N + 1))|) atTop atTop := by
    simpa only [add_comm] using htail
  exact (tendsto_add_atTop_iff_nat (N + 1)).mp htail'

/-- Any capacity path dominated by the unweighted low-channel error tends to `-∞`. -/
theorem laundering_capacity_tendsto_atBot {q : LaunderingParams}
    (model : LaunderingAssumptions q) {β xH xL : ℕ → ℝ}
    (trajectory : IsLaunderingTrajectory q β xH xL)
    (haligned : 0 ≤ xL 0 * q.ιL) (capacity : ℕ → ℝ)
    (hcapacity : ∀ t, capacity t ≤ -q.πL * xL t ^ 2) :
    Tendsto capacity atTop atBot := by
  rw [tendsto_atBot]
  intro b
  let M : ℝ := max 1 ((-b) / q.πL)
  have hevent := (tendsto_atTop.1
    (laundering_low_abs_tendsto_atTop model trajectory haligned)) M
  filter_upwards [hevent] with t ht
  have habsOne : 1 ≤ |xL t| := le_trans (le_max_left _ _) ht
  have habsSq : |xL t| ≤ |xL t| ^ 2 := by
    nlinarith [abs_nonneg (xL t)]
  have hdiv : (-b) / q.πL ≤ |xL t| := le_trans (le_max_right _ _) ht
  have hmassAbs : -b ≤ q.πL * |xL t| ^ 2 := calc
    -b ≤ |xL t| * q.πL := (div_le_iff₀ model.πL_pos).mp hdiv
    _ = q.πL * |xL t| := mul_comm _ _
    _ ≤ q.πL * |xL t| ^ 2 := mul_le_mul_of_nonneg_left habsSq model.πL_pos.le
  calc
    capacity t ≤ -q.πL * xL t ^ 2 := hcapacity t
    _ ≤ b := by rw [← sq_abs]; linarith

/-- The instantaneous gradient dominates its entire low-channel term. -/
theorem launderingGradient_low_term_le {q : LaunderingParams}
    (model : LaunderingAssumptions q) {β xH xL : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) :
    2 * q.πL * lowResidual β * xL ^ 2 ≤ q.launderingGradient β xH xL := by
  have hresidual := launderingResiduals_nonnegative model hβ
  have hExtract : 0 ≤ 1 - q.κ := sub_nonneg.mpr model.κ_le_one
  have hhigh : 0 ≤ 2 * q.πH * (1 - q.κ) * q.highResidual β * xH ^ 2 :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) model.πH_nonneg) hExtract)
        hresidual.1)
      (sq_nonneg _)
  simp only [launderingGradient]
  linarith

/-- In the unbounded idealization, the projected policy reaches capture in finite time. -/
theorem laundering_finite_capture {q : LaunderingParams}
    (model : LaunderingAssumptions q) {β xH xL : ℕ → ℝ}
    (trajectory : IsLaunderingTrajectory q β xH xL)
    (haligned : 0 ≤ xL 0 * q.ιL) :
    ∃ N, ∀ n, β (N + n) = 1 := by
  let c : ℝ := 2 * q.α * q.πL
  have hc : 0 < c := by
    dsimp only [c]
    exact mul_pos (mul_pos two_pos model.α_pos) model.πL_pos
  let M : ℝ := max 1 (1 / c)
  have habsTop := laundering_low_abs_tendsto_atTop model trajectory haligned
  have heventLarge : ∀ᶠ t in atTop, M ≤ |xL t| := tendsto_atTop.1 habsTop M
  have heventOne : ∀ᶠ t : ℕ in atTop, 1 ≤ t := Ici_mem_atTop 1
  rcases (heventLarge.and heventOne).exists with ⟨T, hlargeAbs, hT⟩
  have habsOne : 1 ≤ |xL T| := le_trans (le_max_left _ _) hlargeAbs
  have habsInv : 1 / c ≤ |xL T| := le_trans (le_max_right _ _) hlargeAbs
  have hcabs : 1 ≤ c * |xL T| := by
    have := (div_le_iff₀ hc).mp habsInv
    simpa only [one_mul, mul_comm] using this
  have habsSq : |xL T| ≤ |xL T| ^ 2 := by
    nlinarith [abs_nonneg (xL T)]
  have hlargeSq : 1 ≤ c * xL T ^ 2 := by
    have := mul_le_mul_of_nonneg_left habsSq hc.le
    rw [sq_abs] at this
    exact le_trans hcabs this
  have hresidual : 0 ≤ 1 - β T := sub_nonneg.mpr (trajectory.policy_mem T).2
  have hcoefficient : 1 - β T ≤ c * xL T ^ 2 * (1 - β T) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hlargeSq hresidual
  have hterm := launderingGradient_low_term_le model
    (xH := xH T) (xL := xL T) (trajectory.policy_mem T)
  have hscaled := mul_le_mul_of_nonneg_left hterm model.α_pos.le
  have hstepSize : 1 - β T ≤
      q.α * q.launderingGradient (β T) (xH T) (xL T) := by
    dsimp only [c] at hcoefficient
    simp only [lowResidual] at hscaled
    nlinarith
  have hinput : 1 ≤ β T + q.α * q.launderingGradient (β T) (xH T) (xL T) := by
    linarith
  have hcapture : β (T + 1) = 1 := by
    rw [trajectory.policy_step T]
    exact clipUnit_eq_one_of_le hinput
  refine ⟨T + 1, ?_⟩
  intro n
  induction n with
  | zero => simpa only [add_zero] using hcapture
  | succ n ih =>
      rw [show T + 1 + (n + 1) = (T + 1 + n) + 1 by omega,
        trajectory.policy_step (T + 1 + n), ih]
      exact laundering_capture_absorbing model

namespace LaunderingParams

/-- The high-channel multiplier on the capture face. -/
def honestCaptureMultiplier (q : LaunderingParams) : ℝ :=
  1 - q.ηH * q.κ + q.ζ

end LaunderingParams

/-- The high channel remains an honest affine contraction on the capture face. -/
theorem honestCaptureMultiplier_nonneg_lt_one {q : LaunderingParams}
    (model : LaunderingAssumptions q) :
    0 ≤ q.honestCaptureMultiplier ∧ q.honestCaptureMultiplier < 1 := by
  have hproduct : q.ηH * q.κ ≤ 1 := calc
    q.ηH * q.κ ≤ 1 * q.κ := mul_le_mul_of_nonneg_right model.ηH_le_one model.κ_pos.le
    _ = q.κ := one_mul _
    _ ≤ 1 := model.κ_le_one
  simp only [honestCaptureMultiplier]
  constructor <;> linarith [model.ζ_pos, model.ζ_lt_honest_contraction]

/-- Once captured, the high coordinate is exactly an `arithGeom` path. -/
theorem high_after_capture_eq_arithGeom {q : LaunderingParams}
    {β xH xL : ℕ → ℝ} (trajectory : IsLaunderingTrajectory q β xH xL)
    {N : ℕ} (hcapture : ∀ n, β (N + n) = 1) :
    ∀ n, xH (N + n) = arithGeom q.honestCaptureMultiplier q.ιH (xH N) n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show N + (n + 1) = (N + n) + 1 by omega, trajectory.high_step (N + n),
        hcapture n, ih, arithGeom_succ]
      simp only [highDeviationMultiplier, highEvidenceWeight, highResidual,
        honestCaptureMultiplier]
      ring

/-- The high deviation converges to the finite honest-channel stationary value. -/
theorem laundering_high_tendsto_stationary {q : LaunderingParams}
    (model : LaunderingAssumptions q) {β xH xL : ℕ → ℝ}
    (trajectory : IsLaunderingTrajectory q β xH xL)
    {N : ℕ} (hcapture : ∀ n, β (N + n) = 1) :
    Tendsto xH atTop (nhds (q.ιH / (q.ηH * q.κ - q.ζ))) := by
  have ha := honestCaptureMultiplier_nonneg_lt_one model
  have hlimit := tendsto_affineRecursion q.honestCaptureMultiplier q.ιH (xH N) ha.1 ha.2
  have hdenominator : 1 - q.honestCaptureMultiplier = q.ηH * q.κ - q.ζ := by
    simp only [honestCaptureMultiplier]
    ring
  rw [hdenominator] at hlimit
  have htail : Tendsto (fun n ↦ xH (N + n)) atTop
      (nhds (q.ιH / (q.ηH * q.κ - q.ζ))) := by
    simpa only [high_after_capture_eq_arithGeom trajectory hcapture] using hlimit
  have htail' : Tendsto (fun n ↦ xH (n + N)) atTop
      (nhds (q.ιH / (q.ηH * q.κ - q.ζ))) := by
    simpa only [add_comm] using htail
  exact (tendsto_add_atTop_iff_nat N).mp htail'

/-- On the capture face, measured satisfaction depends only on the high channel. -/
theorem launderingSatisfaction_at_capture (q : LaunderingParams) (xH xL : ℝ) :
    q.launderingSatisfaction 1 xH xL = -q.πH * q.κ ^ 2 * xH ^ 2 := by
  simp only [launderingSatisfaction, highResidual, lowResidual, sub_self, pow_succ,
    mul_zero, mul_one]
  ring

/-- Captured measured satisfaction has the paper's finite high-channel limit. -/
theorem laundering_satisfaction_tendsto_captured_limit {q : LaunderingParams}
    (model : LaunderingAssumptions q) {β xH xL : ℕ → ℝ}
    (trajectory : IsLaunderingTrajectory q β xH xL)
    {N : ℕ} (hcapture : ∀ n, β (N + n) = 1) :
    Tendsto (fun t ↦ q.launderingSatisfaction (β t) (xH t) (xL t)) atTop
      (nhds (-q.πH * q.κ ^ 2 *
        (q.ιH / (q.ηH * q.κ - q.ζ)) ^ 2)) := by
  have hHigh := laundering_high_tendsto_stationary model trajectory hcapture
  have hscaled := (hHigh.pow 2).const_mul (-q.πH * q.κ ^ 2)
  have htail : Tendsto
      (fun n ↦ q.launderingSatisfaction (β (N + n)) (xH (N + n)) (xL (N + n)))
      atTop (nhds (-q.πH * q.κ ^ 2 *
        (q.ιH / (q.ηH * q.κ - q.ζ)) ^ 2)) := by
    have hHighTail : Tendsto (fun n ↦ xH (N + n)) atTop
        (nhds (q.ιH / (q.ηH * q.κ - q.ζ))) := by
      have hShift := (tendsto_add_atTop_iff_nat N).mpr hHigh
      simpa only [add_comm] using hShift
    have hscaledTail := (hHighTail.pow 2).const_mul (-q.πH * q.κ ^ 2)
    convert hscaledTail using 1
    funext n
    rw [hcapture n, launderingSatisfaction_at_capture]
  have htail' : Tendsto
      (fun n ↦ q.launderingSatisfaction (β (n + N)) (xH (n + N)) (xL (n + N)))
      atTop (nhds (-q.πH * q.κ ^ 2 *
        (q.ιH / (q.ηH * q.κ - q.ζ)) ^ 2)) := by
    simpa only [add_comm] using htail
  exact (tendsto_add_atTop_iff_nat N).mp htail'

/-- After finite capture, the low channel's successive absolute-value ratio tends to `1+ζ`. -/
theorem laundering_low_abs_ratio_tendsto {q : LaunderingParams}
    (model : LaunderingAssumptions q) {β xH xL : ℕ → ℝ}
    (trajectory : IsLaunderingTrajectory q β xH xL)
    (haligned : 0 ≤ xL 0 * q.ιL)
    {N : ℕ} (hcapture : ∀ n, β (N + n) = 1) :
    Tendsto (fun t ↦ |xL (t + 1)| / |xL t|) atTop (nhds (1 + q.ζ)) := by
  have habsTop := laundering_low_abs_tendsto_atTop model trajectory haligned
  have hinv : Tendsto (fun t ↦ (|xL t|)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp habsTop
  have herror : Tendsto (fun t ↦ |q.ιL| * (|xL t|)⁻¹) atTop (nhds 0) := by
    simpa only [mul_zero] using hinv.const_mul |q.ιL|
  have hformulaLimit : Tendsto
      (fun t ↦ (1 + q.ζ) + |q.ιL| * (|xL t|)⁻¹) atTop (nhds (1 + q.ζ)) := by
    simpa only [add_zero] using
      (show Tendsto (fun _ : ℕ ↦ 1 + q.ζ) atTop (nhds (1 + q.ζ)) from
        tendsto_const_nhds).add herror
  apply hformulaLimit.congr'
  filter_upwards [Ici_mem_atTop (max N 1)] with t ht
  have hN : N ≤ t := le_trans (le_max_left _ _) ht
  have hOne : 1 ≤ t := le_trans (le_max_right _ _) ht
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hN
  have hnonzero : |xL (N + n)| ≠ 0 := by
    have habs := (low_sign_alignment model trajectory.policy_mem trajectory.low_step haligned).2
      (N + n - 1)
    have hindex : (N + n - 1) + 1 = N + n := by omega
    rw [hindex] at habs
    exact ne_of_gt (lt_of_lt_of_le (abs_pos.mpr model.ιL_ne_zero) habs)
  rw [low_abs_step model trajectory.policy_mem trajectory.low_step haligned,
    hcapture n]
  simp only [lowDeviationMultiplier, lowEvidenceWeight, lowResidual, sub_self, mul_zero,
    sub_zero, div_eq_mul_inv]
  field_simp [hnonzero]

/-- The machine-checked conclusions of the satisfaction--capacity decoupling argument.

The residual contraction uses the valid clipped factor `max 0 (1-k)`.  The
paper's literal factor is exposed conditionally in `residual_contraction_as_written`.
-/
structure SatisfactionCapacityDecouplingConclusions (q : LaunderingParams)
    (β xH xL : ℕ → ℝ) : Prop where
  gradient_formula : ∀ t,
    HasDerivAt (fun policy ↦ q.launderingSatisfaction policy (xH t) (xL t))
      (q.launderingGradient (β t) (xH t) (xL t)) (β t)
  gradient_nonnegative : ∀ t, 0 ≤ q.launderingGradient (β t) (xH t) (xL t)
  policy_monotone : Monotone β
  low_sign_aligned : ∀ t, 0 ≤ xL t * q.ιL
  low_abs_floor : ∀ t, |q.ιL| ≤ |xL (t + 1)|
  gradient_floor : ∀ t,
    2 * q.πL * lowResidual (β (t + 1)) * q.ιL ^ 2 ≤
      q.launderingGradient (β (t + 1)) (xH (t + 1)) (xL (t + 1))
  residual_contraction : ∀ t,
    1 - β (t + 2) ≤ q.captureFactor * (1 - β (t + 1))
  residual_contraction_as_written : q.captureRate ≤ 1 → ∀ t,
    1 - β (t + 2) ≤ (1 - q.captureRate) * (1 - β (t + 1))
  policy_tendsto_capture : Tendsto β atTop (nhds 1)
  finite_capture : ∃ N, ∀ n, β (N + n) = 1
  capture_absorbing : ∀ yH yL : ℝ,
    LoopParams.clipUnit (1 + q.α * q.launderingGradient 1 yH yL) = 1
  high_tendsto_stationary :
    Tendsto xH atTop (nhds (q.ιH / (q.ηH * q.κ - q.ζ)))
  satisfaction_tendsto_captured_limit :
    Tendsto (fun t ↦ q.launderingSatisfaction (β t) (xH t) (xL t)) atTop
      (nhds (-q.πH * q.κ ^ 2 * (q.ιH / (q.ηH * q.κ - q.ζ)) ^ 2))
  low_abs_tendsto_atTop : Tendsto (fun t ↦ |xL t|) atTop atTop
  low_abs_ratio_tendsto :
    Tendsto (fun t ↦ |xL (t + 1)| / |xL t|) atTop (nhds (1 + q.ζ))
  dominated_capacity_tendsto_atBot : ∀ capacity : ℕ → ℝ,
    (∀ t, capacity t ≤ -q.πL * xL t ^ 2) → Tendsto capacity atTop atBot
  low_feedback_eventually_noncontracting :
    ∀ᶠ t in atTop, q.lowEvidenceWeight (β t) < q.ζ
  low_myopia_on_contracting_prefix : ∀ t,
    q.ζ < q.lowEvidenceWeight (β t) →
      MyopiaTrapOn q.ηL 0 q.ζ q.ιL (β t)
  high_myopia_on_contracting_prefix : q.κ < 1 → q.ιH ≠ 0 → ∀ t,
    q.ζ < q.highEvidenceWeight (β t) →
      MyopiaTrapOn q.ηH q.κ q.ζ q.ιH (β t)
  high_zero_injection_endpoint : q.ιH = 0 →
    q.ζ < q.highEvidenceWeight 0 ∧
      ∀ policy, instantaneousAgreementGradient q.κ policy
        (feedbackStationaryDeviation q.ηH q.κ q.ζ q.ιH policy) = 0
  high_full_extraction_endpoint : q.κ = 1 →
    q.ζ < q.highEvidenceWeight 0 ∧
      ∀ policy belief, instantaneousAgreementGradient q.κ policy belief = 0

/--
Paper II, Theorem 3.32 (`thm:launder`), `civic_drift.tex:694`.

This packages every clause of the theorem.  Clause (iii)'s typewise
quantifier is split into the low and high fields: the standing assumptions
discharge the low type's nondegeneracy conditions, while the high field retains
the printed `κ < 1` and `ιH ≠ 0` hypotheses.  The final two fields export the
two endpoint obstructions stated in the paper.
-/
theorem satisfactionCapacityDecoupling {q : LaunderingParams}
    (model : LaunderingAssumptions q) {β xH xL : ℕ → ℝ}
    (trajectory : IsLaunderingTrajectory q β xH xL)
    (_halignedHigh : 0 ≤ xH 0 * q.ιH) (halignedLow : 0 ≤ xL 0 * q.ιL) :
    SatisfactionCapacityDecouplingConclusions q β xH xL := by
  have hsign := low_sign_alignment model trajectory.policy_mem trajectory.low_step halignedLow
  obtain ⟨N, hcaptured⟩ := laundering_finite_capture model trajectory halignedLow
  refine
    { gradient_formula := fun t ↦
        hasDerivAt_launderingSatisfaction q (β t) (xH t) (xL t)
      gradient_nonnegative := fun t ↦
        launderingGradient_nonnegative model (trajectory.policy_mem t)
      policy_monotone := laundering_policy_monotone model trajectory
      low_sign_aligned := hsign.1
      low_abs_floor := hsign.2
      gradient_floor := launderingGradient_floor model trajectory halignedLow
      residual_contraction := laundering_residual_contraction model trajectory halignedLow
      residual_contraction_as_written := fun hrate t ↦
        laundering_residual_contraction_of_rate_le_one model trajectory halignedLow hrate t
      policy_tendsto_capture := laundering_policy_tendsto_one model trajectory halignedLow
      finite_capture := ⟨N, hcaptured⟩
      capture_absorbing := fun _ _ ↦ laundering_capture_absorbing model
      high_tendsto_stationary :=
        laundering_high_tendsto_stationary model trajectory hcaptured
      satisfaction_tendsto_captured_limit :=
        laundering_satisfaction_tendsto_captured_limit model trajectory hcaptured
      low_abs_tendsto_atTop :=
        laundering_low_abs_tendsto_atTop model trajectory halignedLow
      low_abs_ratio_tendsto :=
        laundering_low_abs_ratio_tendsto model trajectory halignedLow hcaptured
      dominated_capacity_tendsto_atBot := fun capacity hcapacity ↦
        laundering_capacity_tendsto_atBot model trajectory halignedLow capacity hcapacity
      low_feedback_eventually_noncontracting :=
        laundering_low_feedback_eventually_noncontracting model trajectory halignedLow
      low_myopia_on_contracting_prefix := fun t ↦
        laundering_low_myopiaTrapOn model (trajectory.policy_mem t)
      high_myopia_on_contracting_prefix := fun hκ hιH t ↦
        laundering_high_myopiaTrapOn model (trajectory.policy_mem t) hκ hιH
      high_zero_injection_endpoint :=
        laundering_high_zero_injection_myopia_counterexample model
      high_full_extraction_endpoint :=
        laundering_high_full_extraction_myopia_counterexample model }

#print axioms hasDerivAt_launderingSatisfaction
#print axioms launderingResiduals_nonnegative
#print axioms launderingGradient_nonnegative
#print axioms lowDeviationMultiplier_pos
#print axioms low_sign_alignment
#print axioms laundering_clipUnit_eq_self
#print axioms laundering_policy_monotone
#print axioms launderingGradient_floor
#print axioms captureRate_pos
#print axioms captureFactor_nonneg_lt_one
#print axioms one_sub_clip_captureTarget
#print axioms laundering_residual_contraction
#print axioms laundering_residual_contraction_of_rate_le_one
#print axioms laundering_untruncated_contraction_impossible_of_rate_gt_one
#print axioms laundering_residual_geometric_bound
#print axioms laundering_policy_tendsto_one
#print axioms laundering_low_feedback_eventually_noncontracting
#print axioms laundering_low_myopiaTrapOn
#print axioms laundering_high_myopiaTrapOn
#print axioms myopia_stationaryGradient_eq_zero_of_injection_zero
#print axioms myopia_stationaryGradient_eq_zero_of_full_extraction
#print axioms laundering_high_zero_injection_myopia_counterexample
#print axioms laundering_high_full_extraction_myopia_counterexample
#print axioms laundering_capture_absorbing
#print axioms low_abs_step
#print axioms laundering_low_abs_tendsto_atTop
#print axioms laundering_capacity_tendsto_atBot
#print axioms launderingGradient_low_term_le
#print axioms laundering_finite_capture
#print axioms honestCaptureMultiplier_nonneg_lt_one
#print axioms high_after_capture_eq_arithGeom
#print axioms laundering_high_tendsto_stationary
#print axioms launderingSatisfaction_at_capture
#print axioms laundering_satisfaction_tendsto_captured_limit
#print axioms laundering_low_abs_ratio_tendsto
#print axioms satisfactionCapacityDecoupling

end


end CivicAlignment.PaperII
