/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.Laundering

/-!
# Bounded-belief saturation

This file audits Paper II's bounded-belief corollary.  It proves the
saturation-robust sign, gradient, and convergence core, then isolates two
endpoint failures in the printed finite-attainment and high-channel-limit
claims.
-/

namespace CivicAlignment.PaperII

noncomputable section

open Filter Set Topology
open LaunderingParams

/-- Symmetric clipping of a deviation to `[-bound, bound]`. -/
def clipDeviation (bound x : ℝ) : ℝ :=
  max (-bound) (min bound x)

/-- Symmetric clipping lands in its advertised interval. -/
theorem clipDeviation_mem {bound x : ℝ} (hbound : 0 ≤ bound) :
    clipDeviation bound x ∈ Icc (-bound) bound := by
  constructor
  · exact le_max_left _ _
  · apply max_le
    · linarith
    · exact min_le_left _ _

/-- Symmetric clipping is the identity inside the bounded state space. -/
theorem clipDeviation_eq_self {bound x : ℝ} (hx : x ∈ Icc (-bound) bound) :
    clipDeviation bound x = x := by
  simp only [clipDeviation]
  rw [min_eq_right hx.2, max_eq_right hx.1]

/-- Values above the upper face clip to the upper face. -/
theorem clipDeviation_eq_top {bound x : ℝ} (hbound : 0 ≤ bound) (hx : bound ≤ x) :
    clipDeviation bound x = bound := by
  simp only [clipDeviation]
  rw [min_eq_left hx, max_eq_right (by linarith)]

/-- Values below the lower face clip to the lower face. -/
theorem clipDeviation_eq_bot {bound x : ℝ} (hbound : 0 ≤ bound) (hx : x ≤ -bound) :
    clipDeviation bound x = -bound := by
  have hx' : x ≤ bound := by linarith
  simp only [clipDeviation]
  rw [min_eq_right hx', max_eq_left hx]

/-- Symmetric clipping is monotone. -/
theorem monotone_clipDeviation (bound : ℝ) : Monotone (clipDeviation bound) := by
  intro x y hxy
  simp only [clipDeviation]
  gcongr

/-- Symmetric clipping truncates absolute value at the radius. -/
theorem abs_clipDeviation {bound x : ℝ} (hbound : 0 ≤ bound) :
    |clipDeviation bound x| = min bound |x| := by
  by_cases hlo : x ≤ -bound
  · rw [clipDeviation_eq_bot hbound hlo, abs_neg, abs_of_nonneg hbound,
      abs_of_nonpos (by linarith), min_eq_left (by linarith)]
  by_cases hhi : bound ≤ x
  · rw [clipDeviation_eq_top hbound hhi, abs_of_nonneg hbound,
      abs_of_nonneg (by linarith), min_eq_left hhi]
  · have hxmem : x ∈ Icc (-bound) bound := ⟨le_of_not_ge hlo, le_of_not_ge hhi⟩
    rw [clipDeviation_eq_self hxmem, min_eq_right (abs_le.mpr hxmem)]

/-- Symmetric clipping is nonexpansive. -/
theorem abs_clipDeviation_sub_le {bound x y : ℝ} (_hbound : 0 ≤ bound) :
    |clipDeviation bound x - clipDeviation bound y| ≤ |x - y| :=
  clipTo_dist_le (lo := -bound) (hi := bound) x y

/-- The bounded high-type deviation update. -/
def boundedHighStep (q : LaunderingParams) (bound β xH : ℝ) : ℝ :=
  clipDeviation bound (q.highDeviationMultiplier β * xH + q.ιH)

/-- The bounded low-type deviation update. -/
def boundedLowStep (q : LaunderingParams) (bound β xL : ℝ) : ℝ :=
  clipDeviation bound (q.lowDeviationMultiplier β * xL + q.ιL)

/-- The policy update is unchanged when the belief coordinates are bounded. -/
def boundedPolicyStep (q : LaunderingParams) (β xH xL : ℝ) : ℝ :=
  LoopParams.clipUnit (β + q.α * q.launderingGradient β xH xL)

/-- A trajectory of the bounded two-type laundering loop. -/
structure IsBoundedLaunderingTrajectory (q : LaunderingParams) (bound : ℝ)
    (β xH xL : ℕ → ℝ) : Prop where
  policy_mem : ∀ t, β t ∈ Icc (0 : ℝ) 1
  high_mem : ∀ t, xH t ∈ Icc (-bound) bound
  low_mem : ∀ t, xL t ∈ Icc (-bound) bound
  high_step : ∀ t, xH (t + 1) = boundedHighStep q bound (β t) (xH t)
  low_step : ∀ t, xL (t + 1) = boundedLowStep q bound (β t) (xL t)
  policy_step : ∀ t, β (t + 1) = boundedPolicyStep q (β t) (xH t) (xL t)

/-- Symmetric clipping preserves low-type sign alignment and the injection floor. -/
theorem boundedLowStep_sign_alignment {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound β xL : ℝ}
    (hbound : |q.ιL| ≤ bound) (hβ : β ∈ Icc (0 : ℝ) 1)
    (haligned : 0 ≤ xL * q.ιL) :
    0 ≤ boundedLowStep q bound β xL * q.ιL ∧
      |q.ιL| ≤ |boundedLowStep q bound β xL| := by
  have hbound_nonneg : 0 ≤ bound := le_trans (abs_nonneg q.ιL) hbound
  have hmultiplier := lowDeviationMultiplier_pos model hβ
  rcases lt_or_gt_of_ne model.ιL_ne_zero with hιneg | hιpos
  · have hsign' : 0 ≤ q.ιL * xL := by simpa only [mul_comm] using haligned
    have hx : xL ≤ 0 := nonpos_of_mul_nonneg_right hsign' hιneg
    have hraw : q.lowDeviationMultiplier β * xL + q.ιL ≤ q.ιL := by
      have := mul_nonpos_of_nonneg_of_nonpos hmultiplier.le hx
      linarith
    have hιmem : q.ιL ∈ Icc (-bound) bound := by
      rw [abs_of_neg hιneg] at hbound
      constructor <;> linarith
    have hclip := monotone_clipDeviation bound hraw
    rw [clipDeviation_eq_self hιmem] at hclip
    have hout : boundedLowStep q bound β xL ≤ q.ιL := by
      simpa only [boundedLowStep] using hclip
    have houtneg : boundedLowStep q bound β xL < 0 := lt_of_le_of_lt hout hιneg
    constructor
    · exact mul_nonneg_of_nonpos_of_nonpos houtneg.le hιneg.le
    · rw [abs_of_neg hιneg, abs_of_neg houtneg]
      linarith
  · have hsign' : 0 ≤ q.ιL * xL := by simpa only [mul_comm] using haligned
    have hx : 0 ≤ xL := nonneg_of_mul_nonneg_right hsign' hιpos
    have hraw : q.ιL ≤ q.lowDeviationMultiplier β * xL + q.ιL := by
      have := mul_nonneg hmultiplier.le hx
      linarith
    have hιmem : q.ιL ∈ Icc (-bound) bound := by
      rw [abs_of_pos hιpos] at hbound
      constructor <;> linarith
    have hclip := monotone_clipDeviation bound hraw
    rw [clipDeviation_eq_self hιmem] at hclip
    have hout : q.ιL ≤ boundedLowStep q bound β xL := by
      simpa only [boundedLowStep] using hclip
    have houtpos : 0 < boundedLowStep q bound β xL := lt_of_lt_of_le hιpos hout
    constructor
    · exact mul_nonneg houtpos.le hιpos.le
    · rw [abs_of_pos hιpos, abs_of_pos houtpos]
      exact hout

/-- Low-type sign alignment and the injection floor persist along every bounded path. -/
theorem bounded_low_sign_alignment {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    (hbound : |q.ιL| ≤ bound) (haligned : 0 ≤ xL 0 * q.ιL) :
    (∀ t, 0 ≤ xL t * q.ιL) ∧ (∀ t, |q.ιL| ≤ |xL (t + 1)|) := by
  have hsign : ∀ t, 0 ≤ xL t * q.ιL := by
    intro t
    induction t with
    | zero => exact haligned
    | succ t iht =>
        rw [trajectory.low_step t]
        exact (boundedLowStep_sign_alignment model hbound
          (trajectory.policy_mem t) iht).1
  refine ⟨hsign, ?_⟩
  intro t
  rw [trajectory.low_step t]
  exact (boundedLowStep_sign_alignment model hbound
    (trajectory.policy_mem t) (hsign t)).2

/-- The bounded policy path is nondecreasing. -/
theorem bounded_laundering_policy_monotone {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL) : Monotone β := by
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

/-- The low injection floor yields the same pointwise gradient floor after clipping. -/
theorem bounded_launderingGradient_floor {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    (hbound : |q.ιL| ≤ bound) (haligned : 0 ≤ xL 0 * q.ιL) (t : ℕ) :
    2 * q.πL * lowResidual (β (t + 1)) * q.ιL ^ 2 ≤
      q.launderingGradient (β (t + 1)) (xH (t + 1)) (xL (t + 1)) := by
  have habs := (bounded_low_sign_alignment model trajectory hbound haligned).2 t
  have hsquare : q.ιL ^ 2 ≤ xL (t + 1) ^ 2 := by
    have := (sq_le_sq₀ (abs_nonneg q.ιL) (abs_nonneg (xL (t + 1)))).2 habs
    simpa only [sq_abs] using this
  have hresidual := launderingResiduals_nonnegative model (trajectory.policy_mem (t + 1))
  have hcoefficient : 0 ≤ 2 * q.πL * lowResidual (β (t + 1)) :=
    mul_nonneg (mul_nonneg (by norm_num) model.πL_pos.le) hresidual.2
  exact le_trans (mul_le_mul_of_nonneg_left hsquare hcoefficient)
    (launderingGradient_low_term_le model (trajectory.policy_mem (t + 1)))

/-- The clipped-factor contraction survives bounded belief updates. -/
theorem bounded_laundering_residual_contraction {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    (hbound : |q.ιL| ≤ bound) (haligned : 0 ≤ xL 0 * q.ιL) (t : ℕ) :
    1 - β (t + 2) ≤ q.captureFactor * (1 - β (t + 1)) := by
  have hfloor := bounded_launderingGradient_floor model trajectory hbound haligned t
  have hscaled : q.captureRate * lowResidual (β (t + 1)) ≤
      q.α * q.launderingGradient (β (t + 1)) (xH (t + 1)) (xL (t + 1)) := by
    simp only [LaunderingParams.captureRate]
    nlinarith [mul_nonneg model.α_pos.le (sub_nonneg.mpr hfloor)]
  have hinput : β (t + 1) + q.captureRate * (1 - β (t + 1)) ≤
      β (t + 1) + q.α * q.launderingGradient (β (t + 1))
        (xH (t + 1)) (xL (t + 1)) := by
    simpa only [lowResidual, add_comm] using add_le_add_left hscaled (β (t + 1))
  have hclip := LoopParams.monotone_clipUnit hinput
  have hpolicyStep := trajectory.policy_step (t + 1)
  simp only [boundedPolicyStep] at hpolicyStep
  rw [← hpolicyStep] at hclip
  have hresidual : 1 - β (t + 2) ≤
      1 - LoopParams.clipUnit
        (β (t + 1) + q.captureRate * (1 - β (t + 1))) := by
    linarith
  rw [one_sub_clip_captureTarget (trajectory.policy_mem (t + 1))
    (captureRate_pos model).le] at hresidual
  exact hresidual

/-- The bounded policy still converges to capture, although finite attainment can fail. -/
theorem bounded_laundering_policy_tendsto_one {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    (hbound : |q.ιL| ≤ bound) (haligned : 0 ≤ xL 0 * q.ιL) :
    Tendsto β atTop (nhds 1) := by
  have hfactor := captureFactor_nonneg_lt_one model
  have hupper : ∀ n,
      1 - β (n + 1) ≤ q.captureFactor ^ n * (1 - β 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          1 - β (n + 1 + 1) ≤ q.captureFactor * (1 - β (n + 1)) := by
            simpa only [Nat.add_assoc] using
              bounded_laundering_residual_contraction model trajectory hbound haligned n
          _ ≤ q.captureFactor * (q.captureFactor ^ n * (1 - β 1)) :=
            mul_le_mul_of_nonneg_left ih hfactor.1
          _ = q.captureFactor ^ (n + 1) * (1 - β 1) := by
            rw [pow_succ]
            ring
  have hpow : Tendsto (fun n : ℕ ↦ q.captureFactor ^ n * (1 - β 1)) atTop (nhds 0) :=
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

/-- Along every bounded laundering path, the low channel eventually enters the
noncontracting region `wL < ζ`. -/
theorem bounded_low_feedback_eventually_noncontracting {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    (hbound : |q.ιL| ≤ bound) (haligned : 0 ≤ xL 0 * q.ιL) :
    ∀ᶠ t in atTop, q.lowEvidenceWeight (β t) < q.ζ := by
  have hβ := bounded_laundering_policy_tendsto_one model trajectory hbound haligned
  have hresidual : Tendsto (fun t ↦ 1 - β t) atTop (nhds 0) := by
    simpa only [sub_self] using
      (show Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) from
        tendsto_const_nhds).sub hβ
  have hweight : Tendsto (fun t ↦ q.lowEvidenceWeight (β t)) atTop (nhds 0) := by
    simpa only [lowEvidenceWeight, lowResidual, mul_zero] using
      hresidual.const_mul q.ηL
  exact (tendsto_order.1 hweight).2 q.ζ model.ζ_pos

/-- A positive saturated low face is fixed whenever feedback is noncontracting. -/
theorem boundedLowStep_positive_face_fixed_of_weight_le {q : LaunderingParams}
    {bound β : ℝ} (hbound : 0 ≤ bound) (hιL : 0 < q.ιL)
    (hweight : q.lowEvidenceWeight β ≤ q.ζ) :
    boundedLowStep q bound β bound = bound := by
  apply clipDeviation_eq_top hbound
  simp only [lowDeviationMultiplier]
  nlinarith [mul_nonneg hbound (sub_nonneg.mpr hweight)]

/-- A negative saturated low face is fixed whenever feedback is noncontracting. -/
theorem boundedLowStep_negative_face_fixed_of_weight_le {q : LaunderingParams}
    {bound β : ℝ} (hbound : 0 ≤ bound) (hιL : q.ιL < 0)
    (hweight : q.lowEvidenceWeight β ≤ q.ζ) :
    boundedLowStep q bound β (-bound) = -bound := by
  apply clipDeviation_eq_bot hbound
  simp only [lowDeviationMultiplier]
  nlinarith [mul_nonneg hbound (sub_nonneg.mpr hweight)]

/-- The sign-aligned bounded low coordinate reaches its corresponding face in
finite time and remains there. -/
theorem bounded_low_eventually_saturated {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    (hbound : |q.ιL| ≤ bound) (haligned : 0 ≤ xL 0 * q.ιL) :
    ∃ N, ∀ n, |xL (N + n)| = bound := by
  have hbound0 : 0 ≤ bound := le_trans (abs_nonneg q.ιL) hbound
  have hsign := (bounded_low_sign_alignment model trajectory hbound haligned).1
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (bounded_low_feedback_eventually_noncontracting model trajectory hbound haligned)
  rcases lt_or_gt_of_ne model.ιL_ne_zero with hιneg | hιpos
  · have hnonpos : ∀ t, xL t ≤ 0 := by
      intro t
      have hsign' : 0 ≤ q.ιL * xL t := by simpa only [mul_comm] using hsign t
      exact nonpos_of_mul_nonneg_right hsign' hιneg
    have hface : ∃ k, xL (N + k) = -bound := by
      by_contra hno
      simp only [not_exists] at hno
      have hgt : ∀ k, -bound < xL (N + k) := by
        intro k
        exact lt_of_le_of_ne (trajectory.low_mem (N + k)).1 (Ne.symm (hno k))
      have hdecrease : ∀ k,
          xL (N + (k + 1)) ≤ xL (N + k) + q.ιL := by
        intro k
        let t := N + k
        have ht : N ≤ t := by omega
        have hmult : 1 ≤ q.lowDeviationMultiplier (β t) := by
          simp only [lowDeviationMultiplier]
          linarith [hN t ht]
        have hraw_le :
            q.lowDeviationMultiplier (β t) * xL t + q.ιL ≤ xL t + q.ιL := by
          have hx := hnonpos t
          nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hmult) hx]
        have hraw_gt : -bound <
            q.lowDeviationMultiplier (β t) * xL t + q.ιL := by
          by_contra hnot
          have hraw : q.lowDeviationMultiplier (β t) * xL t + q.ιL ≤ -bound :=
            le_of_not_gt hnot
          have hclip := clipDeviation_eq_bot hbound0 hraw
          have hstep := trajectory.low_step t
          simp only [boundedLowStep] at hstep
          have : xL (N + (k + 1)) = -bound := by
            rw [show N + (k + 1) = t + 1 by omega, hstep, hclip]
          exact hno (k + 1) this
        have hraw_mem :
            q.lowDeviationMultiplier (β t) * xL t + q.ιL ∈ Icc (-bound) bound :=
          ⟨hraw_gt.le, by linarith [hnonpos t, hιneg]⟩
        rw [show N + (k + 1) = t + 1 by omega, trajectory.low_step t]
        simp only [boundedLowStep, clipDeviation_eq_self hraw_mem]
        exact hraw_le
      have hlinear : ∀ k,
          xL (N + k) ≤ xL N + (k : ℝ) * q.ιL := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
            calc
              xL (N + (k + 1)) ≤ xL (N + k) + q.ιL := hdecrease k
              _ ≤ (xL N + (k : ℝ) * q.ιL) + q.ιL := by linarith
              _ = xL N + ((k + 1 : ℕ) : ℝ) * q.ιL := by
                push_cast
                ring
      obtain ⟨k, hk⟩ := exists_nat_gt ((bound + xL N) / (-q.ιL))
      have hcross : xL N + (k : ℝ) * q.ιL < -bound := by
        have hδ : 0 < -q.ιL := neg_pos.mpr hιneg
        have := (div_lt_iff₀ hδ).mp hk
        nlinarith
      have := hlinear k
      linarith [(trajectory.low_mem (N + k)).1]
    obtain ⟨k, hk⟩ := hface
    have hstay : ∀ n, xL (N + k + n) = -bound := by
      intro n
      induction n with
      | zero => simpa only [add_zero] using hk
      | succ n ih =>
          let t := N + k + n
          have ht : N ≤ t := by omega
          rw [show N + k + (n + 1) = t + 1 by omega, trajectory.low_step t, ih]
          exact boundedLowStep_negative_face_fixed_of_weight_le hbound0 hιneg (hN t ht).le
    refine ⟨N + k, fun n ↦ ?_⟩
    rw [hstay n, abs_neg, abs_of_nonneg hbound0]
  · have hnonneg : ∀ t, 0 ≤ xL t := by
      intro t
      have hsign' : 0 ≤ q.ιL * xL t := by simpa only [mul_comm] using hsign t
      exact nonneg_of_mul_nonneg_right hsign' hιpos
    have hface : ∃ k, xL (N + k) = bound := by
      by_contra hno
      simp only [not_exists] at hno
      have hlt : ∀ k, xL (N + k) < bound := by
        intro k
        exact lt_of_le_of_ne (trajectory.low_mem (N + k)).2 (hno k)
      have hincrease : ∀ k,
          xL (N + k) + q.ιL ≤ xL (N + (k + 1)) := by
        intro k
        let t := N + k
        have ht : N ≤ t := by omega
        have hmult : 1 ≤ q.lowDeviationMultiplier (β t) := by
          simp only [lowDeviationMultiplier]
          linarith [hN t ht]
        have hraw_ge : xL t + q.ιL ≤
            q.lowDeviationMultiplier (β t) * xL t + q.ιL := by
          have hx := hnonneg t
          nlinarith [mul_nonneg (sub_nonneg.mpr hmult) hx]
        have hraw_lt :
            q.lowDeviationMultiplier (β t) * xL t + q.ιL < bound := by
          by_contra hnot
          have hraw : bound ≤ q.lowDeviationMultiplier (β t) * xL t + q.ιL :=
            le_of_not_gt hnot
          have hclip := clipDeviation_eq_top hbound0 hraw
          have hstep := trajectory.low_step t
          simp only [boundedLowStep] at hstep
          have : xL (N + (k + 1)) = bound := by
            rw [show N + (k + 1) = t + 1 by omega, hstep, hclip]
          exact hno (k + 1) this
        have hraw_mem :
            q.lowDeviationMultiplier (β t) * xL t + q.ιL ∈ Icc (-bound) bound :=
          ⟨by linarith [hnonneg t, hιpos], hraw_lt.le⟩
        rw [show N + (k + 1) = t + 1 by omega, trajectory.low_step t]
        simp only [boundedLowStep, clipDeviation_eq_self hraw_mem]
        exact hraw_ge
      have hlinear : ∀ k : ℕ,
          xL N + (k : ℝ) * q.ιL ≤ xL (N + k) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
            calc
              xL N + ((k + 1 : ℕ) : ℝ) * q.ιL =
                  (xL N + (k : ℝ) * q.ιL) + q.ιL := by
                    push_cast
                    ring
              _ ≤ xL (N + k) + q.ιL := by linarith
              _ ≤ xL (N + (k + 1)) := hincrease k
      obtain ⟨k, hk⟩ := exists_nat_gt ((bound - xL N) / q.ιL)
      have hcross : bound < xL N + (k : ℝ) * q.ιL := by
        have := (div_lt_iff₀ hιpos).mp hk
        nlinarith
      have := hlinear k
      linarith [(trajectory.low_mem (N + k)).2]
    obtain ⟨k, hk⟩ := hface
    have hstay : ∀ n, xL (N + k + n) = bound := by
      intro n
      induction n with
      | zero => simpa only [add_zero] using hk
      | succ n ih =>
          let t := N + k + n
          have ht : N ≤ t := by omega
          rw [show N + k + (n + 1) = t + 1 by omega, trajectory.low_step t, ih]
          exact boundedLowStep_positive_face_fixed_of_weight_le hbound0 hιpos (hN t ht).le
    refine ⟨N + k, fun n ↦ ?_⟩
    rw [hstay n, abs_of_nonneg hbound0]

/-- If the saturated low-channel policy increment reaches the remaining unit
interval in one step, bounded trajectories attain capture in finite time. -/
theorem bounded_finite_capture_of_low_saturation_rate {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    (hbound : |q.ιL| ≤ bound) (haligned : 0 ≤ xL 0 * q.ιL)
    (hrate : 1 ≤ 2 * q.α * q.πL * bound ^ 2) :
    ∃ N, ∀ n, β (N + n) = 1 := by
  obtain ⟨T, hsaturated⟩ :=
    bounded_low_eventually_saturated model trajectory hbound haligned
  have habs : |xL T| = bound := by simpa only [add_zero] using hsaturated 0
  have hsquare : xL T ^ 2 = bound ^ 2 := by
    rw [← sq_abs, habs]
  have hresidual : 0 ≤ 1 - β T := sub_nonneg.mpr (trajectory.policy_mem T).2
  have hcoefficient : 1 - β T ≤
      (2 * q.α * q.πL * bound ^ 2) * (1 - β T) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hrate hresidual
  have hterm := launderingGradient_low_term_le model
    (xH := xH T) (xL := xL T) (trajectory.policy_mem T)
  have hscaled := mul_le_mul_of_nonneg_left hterm model.α_pos.le
  have hstepSize : 1 - β T ≤
      q.α * q.launderingGradient (β T) (xH T) (xL T) := by
    simp only [lowResidual] at hscaled
    rw [hsquare] at hscaled
    nlinarith
  have hinput : 1 ≤ β T + q.α * q.launderingGradient (β T) (xH T) (xL T) := by
    linarith
  have hcapture : β (T + 1) = 1 := by
    rw [trajectory.policy_step T]
    simp only [boundedPolicyStep]
    exact clipUnit_eq_one_of_le hinput
  refine ⟨T + 1, ?_⟩
  intro n
  induction n with
  | zero => simpa only [add_zero] using hcapture
  | succ n ih =>
      rw [show T + 1 + (n + 1) = (T + 1 + n) + 1 by omega,
        trajectory.policy_step (T + 1 + n), ih]
      exact laundering_capture_absorbing model

/-- The bounded high multiplier is strictly positive throughout the policy interval. -/
theorem highDeviationMultiplier_pos {q : LaunderingParams}
    (model : LaunderingAssumptions q) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 < q.highDeviationMultiplier β := by
  have hextract : 0 ≤ 1 - q.κ := sub_nonneg.mpr model.κ_le_one
  have hresidual_le : q.highResidual β ≤ 1 := by
    simp only [highResidual]
    exact sub_le_self _ (mul_nonneg hextract hβ.1)
  have hweight_le : q.highEvidenceWeight β ≤ 1 := calc
    q.highEvidenceWeight β ≤ q.ηH * 1 := by
      simp only [highEvidenceWeight]
      exact mul_le_mul_of_nonneg_left hresidual_le model.ηH_pos.le
    _ = q.ηH := mul_one _
    _ ≤ 1 := model.ηH_le_one
  simp only [highDeviationMultiplier]
  linarith [model.ζ_pos]

/-- Symmetric clipping preserves high-channel sign alignment and leaves a
uniform positive injection floor when both the bound and injection are nonzero. -/
theorem boundedHighStep_sign_alignment {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound β xH : ℝ}
    (hbound : 0 < bound) (hβ : β ∈ Icc (0 : ℝ) 1) (hιH : q.ιH ≠ 0)
    (haligned : 0 ≤ xH * q.ιH) :
    0 ≤ boundedHighStep q bound β xH * q.ιH ∧
      min bound |q.ιH| ≤ |boundedHighStep q bound β xH| := by
  have hmultiplier := highDeviationMultiplier_pos model hβ
  rcases lt_or_gt_of_ne hιH with hιneg | hιpos
  · have hsign' : 0 ≤ q.ιH * xH := by simpa only [mul_comm] using haligned
    have hx : xH ≤ 0 := nonpos_of_mul_nonneg_right hsign' hιneg
    have hraw : q.highDeviationMultiplier β * xH + q.ιH ≤ q.ιH := by
      have := mul_nonpos_of_nonneg_of_nonpos hmultiplier.le hx
      linarith
    have hrawneg : q.highDeviationMultiplier β * xH + q.ιH < 0 :=
      lt_of_le_of_lt hraw hιneg
    have houtneg : boundedHighStep q bound β xH < 0 := by
      simp only [boundedHighStep, clipDeviation]
      rw [min_eq_right (by linarith)]
      exact max_lt (by linarith) hrawneg
    constructor
    · exact mul_nonneg_of_nonpos_of_nonpos houtneg.le hιneg.le
    · rw [boundedHighStep, abs_clipDeviation hbound.le]
      have habs : |q.ιH| ≤ |q.highDeviationMultiplier β * xH + q.ιH| := by
        rw [abs_of_neg hιneg, abs_of_neg hrawneg]
        linarith
      exact min_le_min_left bound habs
  · have hsign' : 0 ≤ q.ιH * xH := by simpa only [mul_comm] using haligned
    have hx : 0 ≤ xH := nonneg_of_mul_nonneg_right hsign' hιpos
    have hraw : q.ιH ≤ q.highDeviationMultiplier β * xH + q.ιH := by
      have := mul_nonneg hmultiplier.le hx
      linarith
    have hrawpos : 0 < q.highDeviationMultiplier β * xH + q.ιH :=
      lt_of_lt_of_le hιpos hraw
    have houtpos : 0 < boundedHighStep q bound β xH := by
      simp only [boundedHighStep, clipDeviation]
      have hminpos : 0 < min bound (q.highDeviationMultiplier β * xH + q.ιH) :=
        lt_min hbound hrawpos
      exact lt_of_lt_of_le hminpos (le_max_right _ _)
    constructor
    · exact mul_nonneg houtpos.le hιpos.le
    · rw [boundedHighStep, abs_clipDeviation hbound.le]
      have habs : |q.ιH| ≤ |q.highDeviationMultiplier β * xH + q.ιH| := by
        rw [abs_of_pos hιpos, abs_of_pos hrawpos]
        exact hraw
      exact min_le_min_left bound habs

/-- High-channel sign alignment and the clipped injection floor persist along
every bounded trajectory. -/
theorem bounded_high_sign_alignment {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    (hbound : 0 < bound) (hιH : q.ιH ≠ 0) (haligned : 0 ≤ xH 0 * q.ιH) :
    (∀ t, 0 ≤ xH t * q.ιH) ∧
      ∀ t, min bound |q.ιH| ≤ |xH (t + 1)| := by
  have hsign : ∀ t, 0 ≤ xH t * q.ιH := by
    intro t
    induction t with
    | zero => exact haligned
    | succ t ih =>
        rw [trajectory.high_step t]
        exact (boundedHighStep_sign_alignment model hbound
          (trajectory.policy_mem t) hιH ih).1
  refine ⟨hsign, ?_⟩
  intro t
  rw [trajectory.high_step t]
  exact (boundedHighStep_sign_alignment model hbound
    (trajectory.policy_mem t) hιH (hsign t)).2

/-- The instantaneous gradient dominates its high-channel term. -/
theorem launderingGradient_high_term_le {q : LaunderingParams}
    (model : LaunderingAssumptions q) {β xH xL : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) :
    2 * q.πH * (1 - q.κ) * q.highResidual β * xH ^ 2 ≤
      q.launderingGradient β xH xL := by
  have hresidual := (launderingResiduals_nonnegative model hβ).2
  have hlow : 0 ≤ 2 * q.πL * lowResidual β * xL ^ 2 :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) model.πL_pos.le) hresidual)
      (sq_nonneg _)
  simp only [launderingGradient]
  linarith

/-- Positive mass, policy-sensitive extraction, and persistent honest injection
force bounded trajectories to attain the capture face in finite time. -/
theorem bounded_finite_capture_of_honest_channel {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    (hbound : |q.ιL| ≤ bound) (halignedLow : 0 ≤ xL 0 * q.ιL)
    (halignedHigh : 0 ≤ xH 0 * q.ιH) (hπH : 0 < q.πH)
    (hκ : q.κ < 1) (hιH : q.ιH ≠ 0) :
    ∃ N, ∀ n, β (N + n) = 1 := by
  have hboundpos : 0 < bound := lt_of_lt_of_le (abs_pos.mpr model.ιL_ne_zero) hbound
  let δ : ℝ := min bound |q.ιH|
  have hδ : 0 < δ := lt_min hboundpos (abs_pos.mpr hιH)
  have hhighFloor :=
    (bounded_high_sign_alignment model trajectory hboundpos hιH halignedHigh).2
  let c : ℝ := 2 * q.α * q.πH * (1 - q.κ) * q.κ * δ ^ 2
  have hc : 0 < c := by
    dsimp only [c]
    exact mul_pos
      (mul_pos
        (mul_pos
          (mul_pos (mul_pos two_pos model.α_pos) hπH) (sub_pos.mpr hκ))
        model.κ_pos)
      (sq_pos_of_pos hδ)
  have hβ := bounded_laundering_policy_tendsto_one model trajectory hbound halignedLow
  have hβtail : Tendsto (fun t ↦ β (t + 1)) atTop (nhds 1) :=
    (tendsto_add_atTop_iff_nat 1).mpr hβ
  have heventClose : ∀ᶠ t in atTop, 1 - c < β (t + 1) :=
    (tendsto_order.1 hβtail).1 (1 - c) (by linarith)
  obtain ⟨t, htclose⟩ := heventClose.exists
  let T := t + 1
  have habs : δ ≤ |xH T| := hhighFloor t
  have hsquare : δ ^ 2 ≤ xH T ^ 2 := by
    have := (sq_le_sq₀ (abs_nonneg δ) (abs_nonneg (xH T))).2 (by
      simpa only [abs_of_pos hδ] using habs)
    simpa only [sq_abs] using this
  have hresidual : q.κ ≤ q.highResidual (β T) := by
    have hβT := trajectory.policy_mem T
    have hextract : 0 ≤ 1 - q.κ := sub_nonneg.mpr model.κ_le_one
    simp only [highResidual]
    nlinarith [mul_le_mul_of_nonneg_left hβT.2 hextract]
  have hproduct : q.κ * δ ^ 2 ≤ q.highResidual (β T) * xH T ^ 2 :=
    mul_le_mul hresidual hsquare (sq_nonneg _)
      (le_trans model.κ_pos.le hresidual)
  have hcoefficient : 0 ≤ 2 * q.α * q.πH * (1 - q.κ) := by
    exact (mul_pos
      (mul_pos (mul_pos two_pos model.α_pos) hπH) (sub_pos.mpr hκ)).le
  have hhighTerm : c ≤ q.α *
      (2 * q.πH * (1 - q.κ) * q.highResidual (β T) * xH T ^ 2) := by
    dsimp only [c]
    have := mul_le_mul_of_nonneg_left hproduct hcoefficient
    nlinarith
  have hgradientTerm := launderingGradient_high_term_le model
    (xH := xH T) (xL := xL T) (trajectory.policy_mem T)
  have hscaledGradient := mul_le_mul_of_nonneg_left hgradientTerm model.α_pos.le
  have hstepSize : 1 - β T ≤
      q.α * q.launderingGradient (β T) (xH T) (xL T) := by
    have hclose : 1 - β T < c := by
      dsimp only [T]
      linarith
    linarith
  have hinput : 1 ≤ β T + q.α * q.launderingGradient (β T) (xH T) (xL T) := by
    linarith
  have hcapture : β (T + 1) = 1 := by
    rw [trajectory.policy_step T]
    simp only [boundedPolicyStep]
    exact clipUnit_eq_one_of_le hinput
  refine ⟨T + 1, ?_⟩
  intro n
  induction n with
  | zero => simpa only [add_zero] using hcapture
  | succ n ih =>
      rw [show T + 1 + (n + 1) = (T + 1 + n) + 1 by omega,
        trajectory.policy_step (T + 1 + n), ih]
      exact laundering_capture_absorbing model

/-- The limiting high-channel fixed point, clipped to the bounded state space. -/
def boundedHighStationaryTarget (q : LaunderingParams) (bound : ℝ) : ℝ :=
  clipDeviation bound (q.ιH / (q.ηH * q.κ - q.ζ))

/-- At captured policy, the high multiplier is the honest-channel contraction factor. -/
theorem highDeviationMultiplier_one (q : LaunderingParams) :
    q.highDeviationMultiplier 1 = q.honestCaptureMultiplier := by
  simp only [highDeviationMultiplier, highEvidenceWeight, highResidual,
    honestCaptureMultiplier]
  ring

/-- The clipped high stationary target is a fixed point of the captured bounded update. -/
theorem boundedHighStationaryTarget_fixed {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} (hbound : 0 ≤ bound) :
    boundedHighStep q bound 1 (boundedHighStationaryTarget q bound) =
      boundedHighStationaryTarget q bound := by
  let a : ℝ := q.honestCaptureMultiplier
  let d : ℝ := q.ηH * q.κ - q.ζ
  let xstar : ℝ := q.ιH / d
  have hd : 0 < d := by
    dsimp only [d]
    exact sub_pos.mpr model.ζ_lt_honest_contraction
  have ha := honestCaptureMultiplier_nonneg_lt_one model
  have had : a + d = 1 := by
    dsimp only [a, d, honestCaptureMultiplier]
    ring
  have hιH : q.ιH = d * xstar := by
    dsimp only [xstar]
    field_simp [ne_of_gt hd]
  change boundedHighStep q bound 1 (clipDeviation bound xstar) =
    clipDeviation bound xstar
  by_cases hlo : xstar ≤ -bound
  · rw [clipDeviation_eq_bot hbound hlo]
    simp only [boundedHighStep, highDeviationMultiplier_one]
    change clipDeviation bound (a * (-bound) + q.ιH) = -bound
    apply clipDeviation_eq_bot hbound
    rw [hιH]
    have hx := mul_le_mul_of_nonneg_left hlo hd.le
    nlinarith
  by_cases hhi : bound ≤ xstar
  · rw [clipDeviation_eq_top hbound hhi]
    simp only [boundedHighStep, highDeviationMultiplier_one]
    change clipDeviation bound (a * bound + q.ιH) = bound
    apply clipDeviation_eq_top hbound
    rw [hιH]
    have hx := mul_le_mul_of_nonneg_left hhi hd.le
    nlinarith
  · have hxmem : xstar ∈ Icc (-bound) bound := ⟨le_of_not_ge hlo, le_of_not_ge hhi⟩
    rw [clipDeviation_eq_self hxmem]
    simp only [boundedHighStep, highDeviationMultiplier_one]
    change clipDeviation bound (a * xstar + q.ιH) = xstar
    have hraw : a * xstar + q.ιH = xstar := by
      rw [hιH]
      nlinarith
    rw [hraw, clipDeviation_eq_self hxmem]

/-- One captured bounded high step contracts distance to its clipped stationary target. -/
theorem boundedHighStep_capture_contraction {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound x : ℝ} (hbound : 0 ≤ bound) :
    |boundedHighStep q bound 1 x - boundedHighStationaryTarget q bound| ≤
      q.honestCaptureMultiplier * |x - boundedHighStationaryTarget q bound| := by
  have hfixed := boundedHighStationaryTarget_fixed model hbound
  calc
    |boundedHighStep q bound 1 x - boundedHighStationaryTarget q bound| =
        |boundedHighStep q bound 1 x -
          boundedHighStep q bound 1 (boundedHighStationaryTarget q bound)| := by
            rw [hfixed]
    _ = |clipDeviation bound (q.honestCaptureMultiplier * x + q.ιH) -
        clipDeviation bound
          (q.honestCaptureMultiplier * boundedHighStationaryTarget q bound + q.ιH)| := by
            simp only [boundedHighStep, highDeviationMultiplier_one]
    _ ≤ |(q.honestCaptureMultiplier * x + q.ιH) -
            (q.honestCaptureMultiplier * boundedHighStationaryTarget q bound + q.ιH)| :=
          abs_clipDeviation_sub_le hbound
    _ = q.honestCaptureMultiplier *
        |x - boundedHighStationaryTarget q bound| := by
      rw [show (q.honestCaptureMultiplier * x + q.ιH) -
          (q.honestCaptureMultiplier * boundedHighStationaryTarget q bound + q.ιH) =
          q.honestCaptureMultiplier *
            (x - boundedHighStationaryTarget q bound) by ring,
        abs_mul, abs_of_nonneg (honestCaptureMultiplier_nonneg_lt_one model).1]

/-- Any sequence following the captured bounded high recursion converges geometrically
to the clipped stationary target. -/
theorem bounded_high_tendsto_target_of_capture_recursion {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} (hbound : 0 ≤ bound)
    {x : ℕ → ℝ} (hstep : ∀ t, x (t + 1) = boundedHighStep q bound 1 (x t)) :
    Tendsto x atTop (nhds (boundedHighStationaryTarget q bound)) := by
  have ha := honestCaptureMultiplier_nonneg_lt_one model
  have herror : ∀ n,
      |x n - boundedHighStationaryTarget q bound| ≤
        q.honestCaptureMultiplier ^ n *
          |x 0 - boundedHighStationaryTarget q bound| := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [hstep n]
        calc
          |boundedHighStep q bound 1 (x n) - boundedHighStationaryTarget q bound| ≤
              q.honestCaptureMultiplier *
                |x n - boundedHighStationaryTarget q bound| :=
            boundedHighStep_capture_contraction model hbound
          _ ≤ q.honestCaptureMultiplier *
              (q.honestCaptureMultiplier ^ n *
                |x 0 - boundedHighStationaryTarget q bound|) :=
            mul_le_mul_of_nonneg_left ih ha.1
          _ = q.honestCaptureMultiplier ^ (n + 1) *
              |x 0 - boundedHighStationaryTarget q bound| := by
            rw [pow_succ]
            ring
  have hright : Tendsto
      (fun n : ℕ ↦ q.honestCaptureMultiplier ^ n *
        |x 0 - boundedHighStationaryTarget q bound|) atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one ha.1 ha.2).mul_const
        |x 0 - boundedHighStationaryTarget q bound|
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [Real.dist_eq] using
    (squeeze_zero (fun n ↦ abs_nonneg (x n - boundedHighStationaryTarget q bound))
      herror hright)

/-- Once a bounded trajectory captures, its high coordinate converges to the
clipped honest-channel stationary value. -/
theorem bounded_high_tendsto_target_of_capture {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    (hbound : 0 ≤ bound) {N : ℕ} (hcapture : ∀ n, β (N + n) = 1) :
    Tendsto xH atTop (nhds (boundedHighStationaryTarget q bound)) := by
  have htail : Tendsto (fun n ↦ xH (N + n)) atTop
      (nhds (boundedHighStationaryTarget q bound)) := by
    apply bounded_high_tendsto_target_of_capture_recursion model hbound
    intro n
    rw [show N + (n + 1) = (N + n) + 1 by omega,
      trajectory.high_step (N + n), hcapture n]
  have htail' : Tendsto (fun n ↦ xH (n + N)) atTop
      (nhds (boundedHighStationaryTarget q bound)) := by
    simpa only [add_comm] using htail
  exact (tendsto_add_atTop_iff_nat N).mp htail'

/-- At full high extraction, the bounded high recursion is autonomous and converges
to the clipped stationary target even when policy capture is only asymptotic. -/
theorem bounded_high_tendsto_target_of_full_extraction {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    (hbound : 0 ≤ bound) (hκ : q.κ = 1) :
    Tendsto xH atTop (nhds (boundedHighStationaryTarget q bound)) := by
  apply bounded_high_tendsto_target_of_capture_recursion model hbound
  intro t
  rw [trajectory.high_step t]
  simp only [boundedHighStep, highDeviationMultiplier, highEvidenceWeight,
    highResidual, hκ, sub_self, zero_mul, sub_zero]

/-- The high multiplier is bounded above by its captured contraction factor. -/
theorem highDeviationMultiplier_nonneg_le_capture {q : LaunderingParams}
    (model : LaunderingAssumptions q) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 ≤ q.highDeviationMultiplier β ∧
      q.highDeviationMultiplier β ≤ q.honestCaptureMultiplier := by
  have hresidual : q.κ ≤ q.highResidual β := by
    have hextract : 0 ≤ 1 - q.κ := sub_nonneg.mpr model.κ_le_one
    simp only [highResidual]
    nlinarith [mul_le_mul_of_nonneg_left hβ.2 hextract]
  have hweight : q.ηH * q.κ ≤ q.highEvidenceWeight β := by
    simp only [highEvidenceWeight]
    exact mul_le_mul_of_nonneg_left hresidual model.ηH_pos.le
  constructor
  · exact (highDeviationMultiplier_pos model hβ).le
  · simp only [highDeviationMultiplier, honestCaptureMultiplier]
    linarith

/-- A bounded high step is a uniform contraction toward the limiting target,
up to the vanishing change in its policy-dependent multiplier. -/
theorem boundedHighStep_target_error_le {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound β x : ℝ} (hbound : 0 ≤ bound)
    (hβ : β ∈ Icc (0 : ℝ) 1) :
    |boundedHighStep q bound β x - boundedHighStationaryTarget q bound| ≤
      q.honestCaptureMultiplier * |x - boundedHighStationaryTarget q bound| +
        |(q.highDeviationMultiplier β - q.honestCaptureMultiplier) *
          boundedHighStationaryTarget q bound| := by
  have hfixed := boundedHighStationaryTarget_fixed model hbound
  have hmult := highDeviationMultiplier_nonneg_le_capture model hβ
  calc
    |boundedHighStep q bound β x - boundedHighStationaryTarget q bound| =
        |boundedHighStep q bound β x -
          boundedHighStep q bound 1 (boundedHighStationaryTarget q bound)| := by
            rw [hfixed]
    _ = |clipDeviation bound (q.highDeviationMultiplier β * x + q.ιH) -
        clipDeviation bound
          (q.honestCaptureMultiplier * boundedHighStationaryTarget q bound + q.ιH)| := by
            simp only [boundedHighStep, highDeviationMultiplier_one]
    _ ≤ |(q.highDeviationMultiplier β * x + q.ιH) -
        (q.honestCaptureMultiplier * boundedHighStationaryTarget q bound + q.ιH)| :=
      abs_clipDeviation_sub_le hbound
    _ = |q.highDeviationMultiplier β *
          (x - boundedHighStationaryTarget q bound) +
        (q.highDeviationMultiplier β - q.honestCaptureMultiplier) *
          boundedHighStationaryTarget q bound| := by
      congr 1
      ring
    _ ≤ |q.highDeviationMultiplier β *
          (x - boundedHighStationaryTarget q bound)| +
        |(q.highDeviationMultiplier β - q.honestCaptureMultiplier) *
          boundedHighStationaryTarget q bound| := abs_add_le _ _
    _ = q.highDeviationMultiplier β *
          |x - boundedHighStationaryTarget q bound| +
        |(q.highDeviationMultiplier β - q.honestCaptureMultiplier) *
          boundedHighStationaryTarget q bound| := by
      rw [abs_mul, abs_of_nonneg hmult.1]
    _ ≤ q.honestCaptureMultiplier *
          |x - boundedHighStationaryTarget q bound| +
          |(q.highDeviationMultiplier β - q.honestCaptureMultiplier) *
          boundedHighStationaryTarget q bound| := by
      have hproduct := mul_le_mul_of_nonneg_right hmult.2
        (abs_nonneg (x - boundedHighStationaryTarget q bound))
      linarith

/-- Every bounded high coordinate converges to the clipped stationary target,
including trajectories whose policy approaches capture without attaining it. -/
theorem bounded_high_tendsto_stationary_target {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    (hbound : |q.ιL| ≤ bound) (halignedLow : 0 ≤ xL 0 * q.ιL) :
    Tendsto xH atTop (nhds (boundedHighStationaryTarget q bound)) := by
  have hbound0 : 0 ≤ bound := le_trans (abs_nonneg q.ιL) hbound
  have ha := honestCaptureMultiplier_nonneg_lt_one model
  have hβ := bounded_laundering_policy_tendsto_one model trajectory hbound halignedLow
  have hscaled : Tendsto (fun t ↦ (1 - q.κ) * β t) atTop
      (nhds ((1 - q.κ) * 1)) := hβ.const_mul (1 - q.κ)
  have hresidual : Tendsto (fun t ↦ q.highResidual (β t)) atTop (nhds q.κ) := by
    have h := (show Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) from
      tendsto_const_nhds).sub hscaled
    have hlimit : 1 - (1 - q.κ) * 1 = q.κ := by ring
    rw [hlimit] at h
    simpa only [highResidual] using h
  have hweight : Tendsto (fun t ↦ q.highEvidenceWeight (β t)) atTop
      (nhds (q.ηH * q.κ)) := by
    simpa only [highEvidenceWeight] using hresidual.const_mul q.ηH
  have hmultiplier : Tendsto (fun t ↦ q.highDeviationMultiplier (β t)) atTop
      (nhds q.honestCaptureMultiplier) := by
    have h := (show Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) from
      tendsto_const_nhds).sub hweight |>.add_const q.ζ
    simpa only [highDeviationMultiplier, honestCaptureMultiplier] using h
  let target := boundedHighStationaryTarget q bound
  let perturb : ℕ → ℝ := fun t ↦
    |(q.highDeviationMultiplier (β t) - q.honestCaptureMultiplier) * target|
  have hperturb : Tendsto perturb atTop (nhds 0) := by
    have hdiff := hmultiplier.sub
      (show Tendsto (fun _ : ℕ ↦ q.honestCaptureMultiplier) atTop
        (nhds q.honestCaptureMultiplier) from tendsto_const_nhds)
    have hproduct := hdiff.mul_const target
    simpa only [perturb, sub_self, zero_mul, abs_zero] using hproduct.abs
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  let δ := (1 - q.honestCaptureMultiplier) * ε / 2
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact div_pos (mul_pos (sub_pos.mpr ha.2) hε) two_pos
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hperturb δ hδ
  have hperturb_le : ∀ t, N ≤ t → perturb t ≤ δ := by
    intro t ht
    have hdist := hN t ht
    simp only [Real.dist_eq, sub_zero] at hdist
    exact le_trans (le_abs_self (perturb t)) hdist.le
  have herror : ∀ n,
      |xH (N + n) - target| ≤
        arithGeom q.honestCaptureMultiplier δ |xH N - target| n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hstep := boundedHighStep_target_error_le model hbound0
          (trajectory.policy_mem (N + n)) (x := xH (N + n))
        rw [← trajectory.high_step (N + n)] at hstep
        change |xH (N + (n + 1)) - target| ≤ _
        calc
          |xH (N + (n + 1)) - target| =
              |xH ((N + n) + 1) - target| := by simp only [Nat.add_assoc]
          _ ≤ q.honestCaptureMultiplier * |xH (N + n) - target| +
              perturb (N + n) := by simpa only [target, perturb] using hstep
          _ ≤ q.honestCaptureMultiplier *
                arithGeom q.honestCaptureMultiplier δ |xH N - target| n + δ :=
            add_le_add
              (mul_le_mul_of_nonneg_left ih ha.1)
              (hperturb_le (N + n) (by omega))
          _ = arithGeom q.honestCaptureMultiplier δ |xH N - target| (n + 1) := by
            rw [arithGeom_succ]
  have hcomparison := tendsto_affineRecursion q.honestCaptureMultiplier δ
    |xH N - target| ha.1 ha.2
  have hδlimit : δ / (1 - q.honestCaptureMultiplier) = ε / 2 := by
    dsimp only [δ]
    field_simp [ne_of_gt (sub_pos.mpr ha.2)]
  rw [hδlimit] at hcomparison
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hcomparison (ε / 2) (by positivity)
  refine ⟨N + M, ?_⟩
  intro t ht
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (le_trans (Nat.le_add_right N M) ht)
  have hMn : M ≤ n := by omega
  have hcomparison_lt :
      arithGeom q.honestCaptureMultiplier δ |xH N - target| n < ε := by
    have hdist := hM n hMn
    rw [Real.dist_eq] at hdist
    nlinarith [le_abs_self
      (arithGeom q.honestCaptureMultiplier δ |xH N - target| n - ε / 2)]
  simpa only [Real.dist_eq, target] using lt_of_le_of_lt (herror n) hcomparison_lt

/-- With zero honest injection, the bounded high coordinate contracts to zero
without requiring finite policy capture. -/
theorem bounded_high_tendsto_zero_of_zero_injection {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    (hbound : 0 ≤ bound) (hιH : q.ιH = 0) : Tendsto xH atTop (nhds 0) := by
  have ha := honestCaptureMultiplier_nonneg_lt_one model
  have herror : ∀ n,
      |xH n| ≤ q.honestCaptureMultiplier ^ n * |xH 0| := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [show xH (n + 1) = boundedHighStep q bound (β n) (xH n) by
          exact trajectory.high_step n]
        have hmult := highDeviationMultiplier_nonneg_le_capture model
          (trajectory.policy_mem n)
        calc
          |boundedHighStep q bound (β n) (xH n)| =
              min bound |q.highDeviationMultiplier (β n) * xH n| := by
            simp only [boundedHighStep, hιH, add_zero, abs_clipDeviation hbound]
          _ ≤ |q.highDeviationMultiplier (β n) * xH n| := min_le_right _ _
          _ = q.highDeviationMultiplier (β n) * |xH n| := by
            rw [abs_mul, abs_of_nonneg hmult.1]
          _ ≤ q.honestCaptureMultiplier * |xH n| :=
            mul_le_mul_of_nonneg_right hmult.2 (abs_nonneg _)
          _ ≤ q.honestCaptureMultiplier *
              (q.honestCaptureMultiplier ^ n * |xH 0|) :=
            mul_le_mul_of_nonneg_left ih ha.1
          _ = q.honestCaptureMultiplier ^ (n + 1) * |xH 0| := by
            rw [pow_succ]
            ring
  have hright : Tendsto
      (fun n : ℕ ↦ q.honestCaptureMultiplier ^ n * |xH 0|) atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one ha.1 ha.2).mul_const |xH 0|
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [Real.dist_eq, sub_zero] using
    (squeeze_zero (fun n ↦ abs_nonneg (xH n)) herror hright)

/-- Zero honest injection makes the clipped stationary target exactly zero. -/
theorem boundedHighStationaryTarget_eq_zero_of_injection_zero (q : LaunderingParams)
    {bound : ℝ} (hbound : 0 ≤ bound) (hιH : q.ιH = 0) :
    boundedHighStationaryTarget q bound = 0 := by
  simp [boundedHighStationaryTarget, hιH, clipDeviation_eq_self,
    show (0 : ℝ) ∈ Icc (-bound) bound by constructor <;> linarith]

/-- If the unbounded honest stationary value is feasible, clipping leaves it unchanged. -/
theorem boundedHighStationaryTarget_eq_of_feasible (q : LaunderingParams)
    {bound : ℝ}
    (hfeasible : |q.ιH / (q.ηH * q.κ - q.ζ)| ≤ bound) :
    boundedHighStationaryTarget q bound =
      q.ιH / (q.ηH * q.κ - q.ζ) := by
  apply clipDeviation_eq_self
  exact abs_le.mp hfeasible

/-- If the unbounded honest stationary value lies outside the belief interval,
the clipped target has squared magnitude exactly `bound²`. -/
theorem boundedHighStationaryTarget_sq_eq_bound_sq_of_lt_abs
    (q : LaunderingParams) {bound : ℝ} (hbound : 0 ≤ bound)
    (houtside : bound < |q.ιH / (q.ηH * q.κ - q.ζ)|) :
    boundedHighStationaryTarget q bound ^ 2 = bound ^ 2 := by
  have habs := abs_clipDeviation
    (x := q.ιH / (q.ηH * q.κ - q.ζ)) hbound
  change |boundedHighStationaryTarget q bound| =
    min bound |q.ιH / (q.ηH * q.κ - q.ζ)| at habs
  rw [min_eq_left houtside.le] at habs
  rw [← sq_abs, habs]

/-- In the outside branch, the high coordinate's absolute value converges to
the saturation radius. -/
theorem bounded_high_abs_tendsto_bound_of_outside {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    (hbound : |q.ιL| ≤ bound) (halignedLow : 0 ≤ xL 0 * q.ιL)
    (houtside : bound < |q.ιH / (q.ηH * q.κ - q.ζ)|) :
    Tendsto (fun t ↦ |xH t|) atTop (nhds bound) := by
  have hbound0 : 0 ≤ bound := le_trans (abs_nonneg q.ιL) hbound
  have hhigh := bounded_high_tendsto_stationary_target model trajectory hbound halignedLow
  have htargetAbs := abs_clipDeviation
    (x := q.ιH / (q.ηH * q.κ - q.ζ)) hbound0
  change |boundedHighStationaryTarget q bound| =
    min bound |q.ιH / (q.ηH * q.κ - q.ζ)| at htargetAbs
  rw [min_eq_left houtside.le] at htargetAbs
  simpa only [htargetAbs] using hhigh.abs

/-- Saturation makes the low channel's satisfaction-weighted squared error vanish
even though its unweighted error is maximal. -/
theorem bounded_low_weighted_error_tendsto_zero {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    (hbound : |q.ιL| ≤ bound) (haligned : 0 ≤ xL 0 * q.ιL) :
    Tendsto (fun t ↦ lowResidual (β t) ^ 2 * xL t ^ 2) atTop (nhds 0) := by
  have hβ := bounded_laundering_policy_tendsto_one model trajectory hbound haligned
  have hresidual : Tendsto (fun t ↦ lowResidual (β t)) atTop (nhds 0) := by
    simpa only [lowResidual, sub_self] using
      (show Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) from
        tendsto_const_nhds).sub hβ
  have hbase : Tendsto (fun t ↦ lowResidual (β t) ^ 2 * bound ^ 2)
      atTop (nhds 0) := by
    simpa only [zero_pow (show (2 : ℕ) ≠ 0 by decide), zero_mul] using
      (hresidual.pow 2).mul_const (bound ^ 2)
  obtain ⟨N, hsaturated⟩ :=
    bounded_low_eventually_saturated model trajectory hbound haligned
  have heventAbs : ∀ᶠ t in atTop, |xL t| = bound := by
    refine eventually_atTop.2 ⟨N, ?_⟩
    intro t ht
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
    exact hsaturated n
  apply Tendsto.congr' _ hbase
  filter_upwards [heventAbs] with t ht
  have hxSquare : xL t ^ 2 = bound ^ 2 := by rw [← sq_abs, ht]
  rw [hxSquare]

/-- Given convergence of the high coordinate to the clipped stationary target,
measured satisfaction converges to the corresponding high-only value. -/
theorem bounded_laundering_satisfaction_tendsto_of_high_limit
    {q : LaunderingParams} (model : LaunderingAssumptions q)
    {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    (hbound : |q.ιL| ≤ bound) (halignedLow : 0 ≤ xL 0 * q.ιL)
    (hhigh : Tendsto xH atTop (nhds (boundedHighStationaryTarget q bound))) :
    Tendsto (fun t ↦ q.launderingSatisfaction (β t) (xH t) (xL t)) atTop
      (nhds (-q.πH * q.κ ^ 2 * boundedHighStationaryTarget q bound ^ 2)) := by
  have hβ := bounded_laundering_policy_tendsto_one model trajectory hbound halignedLow
  have hscaled : Tendsto (fun t ↦ (1 - q.κ) * β t) atTop
      (nhds ((1 - q.κ) * 1)) := hβ.const_mul (1 - q.κ)
  have hresidual : Tendsto (fun t ↦ q.highResidual (β t)) atTop (nhds q.κ) := by
    have h := (show Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) from
      tendsto_const_nhds).sub hscaled
    have hlimit : 1 - (1 - q.κ) * 1 = q.κ := by ring
    rw [hlimit] at h
    simpa only [highResidual] using h
  have hhighTerm : Tendsto
      (fun t ↦ -q.πH * q.highResidual (β t) ^ 2 * xH t ^ 2) atTop
      (nhds (-q.πH * q.κ ^ 2 * boundedHighStationaryTarget q bound ^ 2)) := by
    simpa only [mul_assoc] using
      ((hresidual.pow 2).mul (hhigh.pow 2)).const_mul (-q.πH)
  have hlow :=
    bounded_low_weighted_error_tendsto_zero model trajectory hbound halignedLow
  have hlowTerm : Tendsto
      (fun t ↦ q.πL * lowResidual (β t) ^ 2 * xL t ^ 2) atTop (nhds 0) := by
    simpa only [mul_assoc, mul_zero] using hlow.const_mul q.πL
  simpa only [launderingSatisfaction, sub_zero] using hhighTerm.sub hlowTerm

/-- The bounded-belief satisfaction limit holds for every trajectory:
the honest stationary value is clipped exactly when it lies outside the state space. -/
theorem bounded_laundering_satisfaction_tendsto_clipped_limit
    {q : LaunderingParams} (model : LaunderingAssumptions q)
    {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    (hbound : |q.ιL| ≤ bound) (halignedLow : 0 ≤ xL 0 * q.ιL) :
    Tendsto (fun t ↦ q.launderingSatisfaction (β t) (xH t) (xL t)) atTop
      (nhds (-q.πH * q.κ ^ 2 * boundedHighStationaryTarget q bound ^ 2)) := by
  have hhigh := bounded_high_tendsto_stationary_target model trajectory hbound halignedLow
  exact bounded_laundering_satisfaction_tendsto_of_high_limit model trajectory
    hbound halignedLow hhigh

/-- In the feasible branch, the bounded satisfaction limit is the unbounded
honest-channel formula printed in `thm:launder(ii)`. -/
theorem bounded_laundering_satisfaction_tendsto_feasible_limit
    {q : LaunderingParams} (model : LaunderingAssumptions q)
    {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    (hbound : |q.ιL| ≤ bound) (halignedLow : 0 ≤ xL 0 * q.ιL)
    (hfeasible : |q.ιH / (q.ηH * q.κ - q.ζ)| ≤ bound) :
    Tendsto (fun t ↦ q.launderingSatisfaction (β t) (xH t) (xL t)) atTop
      (nhds (-q.πH * q.κ ^ 2 *
        (q.ιH / (q.ηH * q.κ - q.ζ)) ^ 2)) := by
  simpa only [boundedHighStationaryTarget_eq_of_feasible q hfeasible] using
    bounded_laundering_satisfaction_tendsto_clipped_limit model trajectory
      hbound halignedLow

/-- In the infeasible branch, the honest coordinate saturates and measured
satisfaction converges to `-πH κ² bound²`. -/
theorem bounded_laundering_satisfaction_tendsto_saturated_limit
    {q : LaunderingParams} (model : LaunderingAssumptions q)
    {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    (hbound : |q.ιL| ≤ bound) (halignedLow : 0 ≤ xL 0 * q.ιL)
    (houtside : bound < |q.ιH / (q.ηH * q.κ - q.ζ)|) :
    Tendsto (fun t ↦ q.launderingSatisfaction (β t) (xH t) (xL t)) atTop
      (nhds (-q.πH * q.κ ^ 2 * bound ^ 2)) := by
  have hbound0 : 0 ≤ bound := le_trans (abs_nonneg q.ιL) hbound
  have hsquare :=
    boundedHighStationaryTarget_sq_eq_bound_sq_of_lt_abs q hbound0 houtside
  simpa only [hsquare] using
    bounded_laundering_satisfaction_tendsto_clipped_limit model trajectory
      hbound halignedLow

namespace LaunderingParams

/-- The saturated low-channel policy rate in the bounded model. -/
def boundedCaptureRate (q : LaunderingParams) (bound : ℝ) : ℝ :=
  2 * q.α * q.πL * bound ^ 2

/-- The corresponding projected residual contraction factor. -/
def boundedCaptureFactor (q : LaunderingParams) (bound : ℝ) : ℝ :=
  max 0 (1 - q.boundedCaptureRate bound)

end LaunderingParams

/-- The saturated low-channel rate is nonnegative. -/
theorem boundedCaptureRate_nonneg {q : LaunderingParams}
    (model : LaunderingAssumptions q) (bound : ℝ) :
    0 ≤ q.boundedCaptureRate bound := by
  simp only [LaunderingParams.boundedCaptureRate]
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) model.πL_pos.le)
    (sq_nonneg bound)

/-- At every saturated low state, residual policy contracts by at most the
clipped factor based on the belief bound. -/
theorem bounded_post_saturation_residual_contraction {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    {t : ℕ} (hsaturated : |xL t| = bound) :
    1 - β (t + 1) ≤ q.boundedCaptureFactor bound * (1 - β t) := by
  have hsquare : xL t ^ 2 = bound ^ 2 := by rw [← sq_abs, hsaturated]
  have hterm := launderingGradient_low_term_le model
    (xH := xH t) (xL := xL t) (trajectory.policy_mem t)
  have hscaledTerm := mul_le_mul_of_nonneg_left hterm model.α_pos.le
  have hscaled : q.boundedCaptureRate bound * (1 - β t) ≤
      q.α * q.launderingGradient (β t) (xH t) (xL t) := by
    simp only [LaunderingParams.boundedCaptureRate, lowResidual] at hscaledTerm ⊢
    rw [hsquare] at hscaledTerm
    nlinarith
  have hinput : β t + q.boundedCaptureRate bound * (1 - β t) ≤
      β t + q.α * q.launderingGradient (β t) (xH t) (xL t) :=
    by linarith
  have hclip := LoopParams.monotone_clipUnit hinput
  have hstep := trajectory.policy_step t
  simp only [boundedPolicyStep] at hstep
  rw [← hstep] at hclip
  have hresidual : 1 - β (t + 1) ≤
      1 - LoopParams.clipUnit
        (β t + q.boundedCaptureRate bound * (1 - β t)) := by
    linarith
  rw [one_sub_clip_captureTarget (trajectory.policy_mem t)
    (boundedCaptureRate_nonneg model bound)] at hresidual
  exact hresidual

/-- When the high gradient vanishes, the post-saturation residual factor is exact. -/
theorem bounded_post_saturation_residual_exact_of_high_gradient_zero
    {q : LaunderingParams} (model : LaunderingAssumptions q)
    {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    {t : ℕ} (hsaturated : |xL t| = bound)
    (hhigh : 2 * q.πH * (1 - q.κ) * q.highResidual (β t) * xH t ^ 2 = 0) :
    1 - β (t + 1) = q.boundedCaptureFactor bound * (1 - β t) := by
  have hsquare : xL t ^ 2 = bound ^ 2 := by rw [← sq_abs, hsaturated]
  have hgradient : q.launderingGradient (β t) (xH t) (xL t) =
      2 * q.πL * lowResidual (β t) * bound ^ 2 := by
    simp only [launderingGradient]
    rw [hhigh, zero_add, hsquare]
  rw [trajectory.policy_step t]
  simp only [boundedPolicyStep, hgradient, lowResidual,
    LaunderingParams.boundedCaptureFactor]
  rw [show β t + q.α * (2 * q.πL * (1 - β t) * bound ^ 2) =
      β t + q.boundedCaptureRate bound * (1 - β t) by
        simp only [LaunderingParams.boundedCaptureRate]
        ring,
    one_sub_clip_captureTarget (trajectory.policy_mem t)
      (boundedCaptureRate_nonneg model bound)]

/-- With a positive transient high gradient and a subunit low-only rate,
post-saturation contraction is strictly faster than the low-only factor. -/
theorem bounded_post_saturation_residual_strict_of_high_gradient_pos
    {q : LaunderingParams} (model : LaunderingAssumptions q)
    {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    {t : ℕ} (hsaturated : |xL t| = bound)
    (hrate : q.boundedCaptureRate bound < 1) (hpolicy : β t < 1)
    (hhigh : 0 < 2 * q.πH * (1 - q.κ) * q.highResidual (β t) * xH t ^ 2) :
    1 - β (t + 1) < q.boundedCaptureFactor bound * (1 - β t) := by
  let k := q.boundedCaptureRate bound
  let base := β t + k * (1 - β t)
  let actual := β t + q.α * q.launderingGradient (β t) (xH t) (xL t)
  have hk0 : 0 ≤ k := boundedCaptureRate_nonneg model bound
  have hβ := trajectory.policy_mem t
  have hbase0 : 0 ≤ base := by
    dsimp only [base]
    exact add_nonneg hβ.1 (mul_nonneg hk0 (sub_nonneg.mpr hβ.2))
  have hbase1 : base < 1 := by
    dsimp only [base]
    nlinarith [mul_pos (sub_pos.mpr hrate) (sub_pos.mpr hpolicy)]
  have hsquare : xL t ^ 2 = bound ^ 2 := by rw [← sq_abs, hsaturated]
  have hactual : base < actual := by
    dsimp only [base, actual, k]
    simp only [launderingGradient, lowResidual,
      LaunderingParams.boundedCaptureRate]
    rw [hsquare]
    nlinarith [mul_pos model.α_pos hhigh]
  have hclip : base < LoopParams.clipUnit actual := by
    simp only [clipUnit_eq_clipTo]
    exact lt_clipTo hactual hbase1
  have hstep := trajectory.policy_step t
  simp only [boundedPolicyStep] at hstep
  have hnext : base < β (t + 1) := by simpa only [actual] using hstep ▸ hclip
  have hfactor : q.boundedCaptureFactor bound = 1 - k := by
    simp only [LaunderingParams.boundedCaptureFactor]
    rw [max_eq_right (sub_nonneg.mpr hrate.le)]
  rw [hfactor]
  dsimp only [base] at hnext
  linarith

/-- Once the low coordinate saturates, every capacity functional dominated by
its unweighted error is eventually no greater than the bounded floor. -/
theorem bounded_capacity_eventually_le_floor {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    (hbound : |q.ιL| ≤ bound) (haligned : 0 ≤ xL 0 * q.ιL)
    (capacity : ℕ → ℝ) (hcapacity : ∀ t, capacity t ≤ -q.πL * xL t ^ 2) :
    ∀ᶠ t in atTop, capacity t ≤ -q.πL * bound ^ 2 := by
  obtain ⟨N, hsaturated⟩ :=
    bounded_low_eventually_saturated model trajectory hbound haligned
  refine eventually_atTop.2 ⟨N, ?_⟩
  intro t ht
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
  have hsquare : xL (N + n) ^ 2 = bound ^ 2 := by
    rw [← sq_abs, hsaturated n]
  simpa only [hsquare] using hcapacity (N + n)

/-- If that bounded value is also a lower floor for the capacity functional,
the functional is eventually equal to it. -/
theorem bounded_capacity_eventually_eq_floor {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    (hbound : |q.ιL| ≤ bound) (haligned : 0 ≤ xL 0 * q.ιL)
    (capacity : ℕ → ℝ) (hcapacity : ∀ t, capacity t ≤ -q.πL * xL t ^ 2)
    (hfloor : ∀ t, -q.πL * bound ^ 2 ≤ capacity t) :
    ∀ᶠ t in atTop, capacity t = -q.πL * bound ^ 2 := by
  filter_upwards [bounded_capacity_eventually_le_floor model trajectory hbound haligned
    capacity hcapacity] with t ht
  exact le_antisymm ht (hfloor t)

/-- At captured policy, a positive low injection pins the positive saturated face. -/
theorem boundedLowStep_positive_face_fixed {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} (hbound : 0 ≤ bound)
    (hιL : 0 < q.ιL) : boundedLowStep q bound 1 bound = bound := by
  apply clipDeviation_eq_top hbound
  simp only [lowDeviationMultiplier, lowEvidenceWeight, lowResidual,
    sub_self, mul_zero, sub_zero]
  nlinarith [mul_nonneg model.ζ_pos.le hbound]

/-- At captured policy, a negative low injection pins the negative saturated face. -/
theorem boundedLowStep_negative_face_fixed {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} (hbound : 0 ≤ bound)
    (hιL : q.ιL < 0) : boundedLowStep q bound 1 (-bound) = -bound := by
  apply clipDeviation_eq_bot hbound
  simp only [lowDeviationMultiplier, lowEvidenceWeight, lowResidual, sub_self, mul_zero,
    sub_zero]
  nlinarith [mul_nonneg model.ζ_pos.le hbound]

/-- On either bounded low face, captured satisfaction remains exactly blind to that coordinate. -/
theorem bounded_capture_satisfaction_blind (q : LaunderingParams) (bound xH : ℝ) :
    q.launderingSatisfaction 1 xH bound =
        q.launderingSatisfaction 1 xH (-bound) ∧
      q.launderingSatisfaction 1 xH bound = -q.πH * q.κ ^ 2 * xH ^ 2 := by
  rw [launderingSatisfaction_at_capture, launderingSatisfaction_at_capture]
  exact ⟨rfl, rfl⟩

/-- The sign, gradient, and asymptotic-policy core used by the bounded-belief corollary. -/
structure BoundedBeliefsSaturationCore (q : LaunderingParams) (bound : ℝ)
    (β xH xL : ℕ → ℝ) : Prop where
  low_sign_aligned : ∀ t, 0 ≤ xL t * q.ιL
  low_abs_floor : ∀ t, |q.ιL| ≤ |xL (t + 1)|
  policy_monotone : Monotone β
  gradient_floor : ∀ t,
    2 * q.πL * lowResidual (β (t + 1)) * q.ιL ^ 2 ≤
      q.launderingGradient (β (t + 1)) (xH (t + 1)) (xL (t + 1))
  residual_contraction : ∀ t,
    1 - β (t + 2) ≤ q.captureFactor * (1 - β (t + 1))
  policy_tendsto_capture : Tendsto β atTop (nhds 1)

/-- Bounding beliefs preserves sign alignment, the low-channel gradient floor,
monotonicity, the clipped-factor contraction, and asymptotic capture. -/
theorem boundedBeliefsSaturation_core {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    (hbound : |q.ιL| ≤ bound) (haligned : 0 ≤ xL 0 * q.ιL) :
    BoundedBeliefsSaturationCore q bound β xH xL := by
  have hsign := bounded_low_sign_alignment model trajectory hbound haligned
  exact
    { low_sign_aligned := hsign.1
      low_abs_floor := hsign.2
      policy_monotone := bounded_laundering_policy_monotone model trajectory
      gradient_floor := bounded_launderingGradient_floor model trajectory hbound haligned
      residual_contraction :=
        bounded_laundering_residual_contraction model trajectory hbound haligned
      policy_tendsto_capture :=
        bounded_laundering_policy_tendsto_one model trajectory hbound haligned }

/-- The complete machine-checked conclusions of the bounded-belief corollary. -/
structure BoundedBeliefsSaturationConclusions (q : LaunderingParams) (bound : ℝ)
    (β xH xL : ℕ → ℝ) : Prop where
  core : BoundedBeliefsSaturationCore q bound β xH xL
  low_eventually_saturated : ∃ N, ∀ n, |xL (N + n)| = bound
  post_saturation_residual_contraction : ∀ t, |xL t| = bound →
    1 - β (t + 1) ≤ q.boundedCaptureFactor bound * (1 - β t)
  post_saturation_residual_exact_of_high_gradient_zero : ∀ t, |xL t| = bound →
    2 * q.πH * (1 - q.κ) * q.highResidual (β t) * xH t ^ 2 = 0 →
      1 - β (t + 1) = q.boundedCaptureFactor bound * (1 - β t)
  post_saturation_residual_strict_of_high_gradient_pos : ∀ t, |xL t| = bound →
    q.boundedCaptureRate bound < 1 → β t < 1 →
      0 < 2 * q.πH * (1 - q.κ) * q.highResidual (β t) * xH t ^ 2 →
        1 - β (t + 1) < q.boundedCaptureFactor bound * (1 - β t)
  finite_capture_of_low_rate : 1 ≤ q.boundedCaptureRate bound →
    ∃ N, ∀ n, β (N + n) = 1
  finite_capture_of_honest_channel : 0 < q.πH → q.κ < 1 → q.ιH ≠ 0 →
    ∃ N, ∀ n, β (N + n) = 1
  satisfaction_blind_to_low_face : ∀ yH,
    q.launderingSatisfaction 1 yH bound =
        q.launderingSatisfaction 1 yH (-bound) ∧
      q.launderingSatisfaction 1 yH bound = -q.πH * q.κ ^ 2 * yH ^ 2
  high_tendsto_stationary_target :
    Tendsto xH atTop (nhds (boundedHighStationaryTarget q bound))
  high_abs_tendsto_bound_of_outside :
    bound < |q.ιH / (q.ηH * q.κ - q.ζ)| →
      Tendsto (fun t ↦ |xH t|) atTop (nhds bound)
  satisfaction_tendsto_clipped_limit :
    Tendsto (fun t ↦ q.launderingSatisfaction (β t) (xH t) (xL t)) atTop
      (nhds (-q.πH * q.κ ^ 2 * boundedHighStationaryTarget q bound ^ 2))
  satisfaction_tendsto_feasible_limit :
    |q.ιH / (q.ηH * q.κ - q.ζ)| ≤ bound →
      Tendsto (fun t ↦ q.launderingSatisfaction (β t) (xH t) (xL t)) atTop
        (nhds (-q.πH * q.κ ^ 2 *
          (q.ιH / (q.ηH * q.κ - q.ζ)) ^ 2))
  satisfaction_tendsto_saturated_limit :
    bound < |q.ιH / (q.ηH * q.κ - q.ζ)| →
      Tendsto (fun t ↦ q.launderingSatisfaction (β t) (xH t) (xL t)) atTop
        (nhds (-q.πH * q.κ ^ 2 * bound ^ 2))
  capacity_eventually_le_floor : ∀ capacity : ℕ → ℝ,
    (∀ t, capacity t ≤ -q.πL * xL t ^ 2) →
      ∀ᶠ t in atTop, capacity t ≤ -q.πL * bound ^ 2
  capacity_eventually_eq_floor : ∀ capacity : ℕ → ℝ,
    (∀ t, capacity t ≤ -q.πL * xL t ^ 2) →
      (∀ t, -q.πL * bound ^ 2 ≤ capacity t) →
        ∀ᶠ t in atTop, capacity t = -q.πL * bound ^ 2

/--
Paper II, Corollary 3.33 (`cor:sat`), `civic_drift.tex:712`.

This packages both clauses: the unbounded theorem's policy core short
of unconditional finite attainment, finite low saturation and its sharper
post-saturation factor, both sufficient finite-capture conditions, structural
blindness to the low face, and the feasible/saturated high-limit split.  The
three sharp endpoint witnesses printed in the corollary are proved below.
-/
theorem boundedBeliefsSaturation {q : LaunderingParams}
    (model : LaunderingAssumptions q) {bound : ℝ} {β xH xL : ℕ → ℝ}
    (trajectory : IsBoundedLaunderingTrajectory q bound β xH xL)
    (hbound : |q.ιL| ≤ bound) (halignedHigh : 0 ≤ xH 0 * q.ιH)
    (halignedLow : 0 ≤ xL 0 * q.ιL) :
    BoundedBeliefsSaturationConclusions q bound β xH xL := by
  exact
    { core := boundedBeliefsSaturation_core model trajectory hbound halignedLow
      low_eventually_saturated :=
        bounded_low_eventually_saturated model trajectory hbound halignedLow
      post_saturation_residual_contraction := fun t hsaturated ↦
        bounded_post_saturation_residual_contraction model trajectory hsaturated
      post_saturation_residual_exact_of_high_gradient_zero :=
        fun t hsaturated hhigh ↦
          bounded_post_saturation_residual_exact_of_high_gradient_zero model trajectory
            hsaturated hhigh
      post_saturation_residual_strict_of_high_gradient_pos :=
        fun t hsaturated hrate hpolicy hhigh ↦
          bounded_post_saturation_residual_strict_of_high_gradient_pos model trajectory
            hsaturated hrate hpolicy hhigh
      finite_capture_of_low_rate := fun hrate ↦
        bounded_finite_capture_of_low_saturation_rate model trajectory hbound halignedLow
          (by simpa only [LaunderingParams.boundedCaptureRate] using hrate)
      finite_capture_of_honest_channel := fun hπH hκ hιH ↦
        bounded_finite_capture_of_honest_channel model trajectory hbound halignedLow
          halignedHigh hπH hκ hιH
      satisfaction_blind_to_low_face := fun yH ↦
        bounded_capture_satisfaction_blind q bound yH
      high_tendsto_stationary_target :=
        bounded_high_tendsto_stationary_target model trajectory hbound halignedLow
      high_abs_tendsto_bound_of_outside := fun houtside ↦
        bounded_high_abs_tendsto_bound_of_outside model trajectory hbound halignedLow
          houtside
      satisfaction_tendsto_clipped_limit :=
        bounded_laundering_satisfaction_tendsto_clipped_limit model trajectory hbound
          halignedLow
      satisfaction_tendsto_feasible_limit := fun hfeasible ↦
        bounded_laundering_satisfaction_tendsto_feasible_limit model trajectory hbound
          halignedLow hfeasible
      satisfaction_tendsto_saturated_limit := fun houtside ↦
        bounded_laundering_satisfaction_tendsto_saturated_limit model trajectory hbound
          halignedLow houtside
      capacity_eventually_le_floor := fun capacity hcapacity ↦
        bounded_capacity_eventually_le_floor model trajectory hbound halignedLow
          capacity hcapacity
      capacity_eventually_eq_floor := fun capacity hcapacity hfloor ↦
        bounded_capacity_eventually_eq_floor model trajectory hbound halignedLow
          capacity hcapacity hfloor }

/-! ## Exact endpoint counterexamples -/

/-- A bounded model with persistent high injection but policy-insensitive high extraction. -/
def boundedAttainmentCounterexample : LaunderingParams where
  πH := 1 / 2
  πL := 1 / 2
  ηH := 1 / 2
  ηL := 1 / 2
  κ := 1
  ζ := 1 / 4
  α := 1 / 4
  ιH := 1
  ιL := -1

/-- The finite-attainment counterexample satisfies every standing laundering assumption. -/
theorem boundedAttainmentCounterexample_model :
    LaunderingAssumptions boundedAttainmentCounterexample := by
  constructor <;> norm_num [boundedAttainmentCounterexample]

/-- Its exact bounded policy path. -/
def boundedAttainmentPolicy (t : ℕ) : ℝ :=
  1 - (3 / 4 : ℝ) ^ t

/-- Persistent high and saturated low coordinates for the counterexample. -/
def boundedAttainmentHigh (_t : ℕ) : ℝ := 1

def boundedAttainmentLow (_t : ℕ) : ℝ := -1

/-- The three explicit paths form a genuine bounded simultaneous trajectory. -/
theorem boundedAttainmentCounterexample_trajectory :
    IsBoundedLaunderingTrajectory boundedAttainmentCounterexample 1
      boundedAttainmentPolicy boundedAttainmentHigh boundedAttainmentLow := by
  have hpolicy : ∀ t, boundedAttainmentPolicy t ∈ Icc (0 : ℝ) 1 := by
    intro t
    have hpow_nonneg : 0 ≤ (3 / 4 : ℝ) ^ t := by positivity
    have hpow_le : (3 / 4 : ℝ) ^ t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    exact ⟨by simp only [boundedAttainmentPolicy]; linarith,
      by simp only [boundedAttainmentPolicy]; linarith⟩
  refine
    { policy_mem := hpolicy
      high_mem := fun _ ↦ by norm_num [boundedAttainmentHigh]
      low_mem := fun _ ↦ by norm_num [boundedAttainmentLow]
      high_step := ?_
      low_step := ?_
      policy_step := ?_ }
  · intro t
    norm_num [boundedAttainmentHigh, boundedHighStep, boundedAttainmentCounterexample,
      LaunderingParams.highDeviationMultiplier, LaunderingParams.highEvidenceWeight,
      LaunderingParams.highResidual, clipDeviation]
  · intro t
    have hβ := hpolicy t
    have hraw : boundedAttainmentCounterexample.lowDeviationMultiplier
        (boundedAttainmentPolicy t) * boundedAttainmentLow t +
          boundedAttainmentCounterexample.ιL ≤ -(1 : ℝ) := by
      have hmult := lowDeviationMultiplier_pos boundedAttainmentCounterexample_model hβ
      change boundedAttainmentCounterexample.lowDeviationMultiplier
          (boundedAttainmentPolicy t) * (-1) + (-1) ≤ -1
      have hprod : boundedAttainmentCounterexample.lowDeviationMultiplier
          (boundedAttainmentPolicy t) * (-1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hmult.le (by norm_num)
      linarith
    simp only [boundedAttainmentLow, boundedLowStep]
    exact (clipDeviation_eq_bot zero_le_one hraw).symm
  · intro t
    have hβ := hpolicy t
    have hinput : boundedAttainmentPolicy t + (1 / 4 : ℝ) *
        (1 - boundedAttainmentPolicy t) ∈ Icc (0 : ℝ) 1 := by
      constructor <;> nlinarith [hβ.1, hβ.2]
    have hclip := laundering_clipUnit_eq_self hinput
    have hstep_eq : boundedPolicyStep boundedAttainmentCounterexample
        (boundedAttainmentPolicy t) (boundedAttainmentHigh t) (boundedAttainmentLow t) =
        LoopParams.clipUnit
          (boundedAttainmentPolicy t + (1 / 4 : ℝ) * (1 - boundedAttainmentPolicy t)) := by
      simp only [boundedPolicyStep]
      apply congrArg LoopParams.clipUnit
      simp only [boundedAttainmentCounterexample, LaunderingParams.launderingGradient,
        LaunderingParams.highResidual, LaunderingParams.lowResidual,
        boundedAttainmentHigh, boundedAttainmentLow, one_pow]
      ring
    rw [hstep_eq, hclip]
    simp only [boundedAttainmentPolicy, pow_succ]
    ring

/-- The counterexample approaches capture but never attains it at finite time. -/
theorem boundedAttainmentPolicy_lt_one (t : ℕ) : boundedAttainmentPolicy t < 1 := by
  simp only [boundedAttainmentPolicy, sub_lt_self_iff]
  positivity

/-- The nonattaining counterexample nevertheless converges asymptotically to capture. -/
theorem boundedAttainmentPolicy_tendsto_one :
    Tendsto boundedAttainmentPolicy atTop (nhds 1) := by
  exact bounded_laundering_policy_tendsto_one boundedAttainmentCounterexample_model
    boundedAttainmentCounterexample_trajectory (by norm_num [boundedAttainmentCounterexample])
      (by norm_num [boundedAttainmentLow, boundedAttainmentCounterexample])

/-- Thus `ιH ≠ 0` alone does not guarantee finite capture in the bounded model. -/
theorem bounded_persistent_high_injection_no_finite_capture :
    boundedAttainmentCounterexample.ιH ≠ 0 ∧
      boundedAttainmentCounterexample.captureRate < 1 ∧
      ¬∃ N, boundedAttainmentPolicy N = 1 := by
  refine ⟨by norm_num [boundedAttainmentCounterexample], ?_, ?_⟩
  · norm_num [boundedAttainmentCounterexample, LaunderingParams.captureRate]
  · rintro ⟨N, hN⟩
    exact (ne_of_lt (boundedAttainmentPolicy_lt_one N)) hN

/-- A boundary model with `ιH = 0` but a nonzero current high deviation. -/
def boundedGeometricCounterexample : LaunderingParams where
  πH := 1 / 2
  πL := 1 / 2
  ηH := 1 / 2
  ηL := 1 / 2
  κ := 1 / 2
  ζ := 1 / 8
  α := 1 / 10
  ιH := 0
  ιL := -1

/-- The exact-geometric counterexample satisfies all standing assumptions. -/
theorem boundedGeometricCounterexample_model :
    LaunderingAssumptions boundedGeometricCounterexample := by
  constructor <;> norm_num [boundedGeometricCounterexample]

/-- With `ιH = 0`, a nonzero high state makes post-saturation contraction strictly faster. -/
theorem bounded_zero_high_injection_not_exact_geometric :
    boundedGeometricCounterexample.ιH = 0 ∧
      2 * boundedGeometricCounterexample.α * boundedGeometricCounterexample.πL *
          (1 : ℝ) ^ 2 < 1 ∧
      boundedPolicyStep boundedGeometricCounterexample 0 1 (-1) = 3 / 20 ∧
      1 - boundedPolicyStep boundedGeometricCounterexample 0 1 (-1) ≠
        (1 - 2 * boundedGeometricCounterexample.α * boundedGeometricCounterexample.πL *
          (1 : ℝ) ^ 2) * (1 - 0) := by
  have hstep : boundedPolicyStep boundedGeometricCounterexample 0 1 (-1) = 3 / 20 := by
    simp only [boundedPolicyStep, boundedGeometricCounterexample,
      LaunderingParams.launderingGradient, LaunderingParams.highResidual,
      LaunderingParams.lowResidual, sub_zero, mul_one, one_pow]
    rw [show (0 : ℝ) + 1 / 10 *
      (2 * (1 / 2) * (1 - 1 / 2) * (1 - (1 - 1 / 2) * 0) +
        2 * (1 / 2) * (-1) ^ 2) = 3 / 20 by norm_num]
    exact laundering_clipUnit_eq_self (show (3 / 20 : ℝ) ∈ Icc 0 1 by norm_num)
  refine ⟨by norm_num [boundedGeometricCounterexample],
    by norm_num [boundedGeometricCounterexample], hstep, ?_⟩
  rw [hstep]
  norm_num [boundedGeometricCounterexample]

/-- A bounded model whose printed unbounded high-channel limit lies outside the state space. -/
def boundedHighLimitCounterexample : LaunderingParams where
  πH := 1 / 2
  πL := 1 / 2
  ηH := 1
  ηL := 1
  κ := 1 / 2
  ζ := 1 / 4
  α := 1
  ιH := 1
  ιL := -1

/-- The high-limit counterexample satisfies every standing laundering assumption. -/
theorem boundedHighLimitCounterexample_model :
    LaunderingAssumptions boundedHighLimitCounterexample := by
  constructor <;> norm_num [boundedHighLimitCounterexample]

/-- At capture, the bounded high coordinate is fixed at one rather than the printed value four. -/
theorem boundedHighLimitCounterexample_fixed_and_formula :
    boundedHighStep boundedHighLimitCounterexample 1 1 1 = 1 ∧
      boundedHighLimitCounterexample.ιH /
        (boundedHighLimitCounterexample.ηH * boundedHighLimitCounterexample.κ -
          boundedHighLimitCounterexample.ζ) = 4 := by
  constructor <;> norm_num [boundedHighStep, boundedHighLimitCounterexample,
    LaunderingParams.highDeviationMultiplier, LaunderingParams.highEvidenceWeight,
    LaunderingParams.highResidual, clipDeviation]

/-- The bounded captured state used in the limit counterexample is a full one-step fixed point. -/
theorem boundedHighLimitCounterexample_captured_state_fixed :
    boundedHighStep boundedHighLimitCounterexample 1 1 1 = 1 ∧
      boundedLowStep boundedHighLimitCounterexample 1 1 (-1) = -1 ∧
      boundedPolicyStep boundedHighLimitCounterexample 1 1 (-1) = 1 := by
  constructor
  · exact boundedHighLimitCounterexample_fixed_and_formula.1
  constructor <;> norm_num [boundedLowStep, boundedPolicyStep, boundedHighLimitCounterexample,
    LaunderingParams.lowDeviationMultiplier, LaunderingParams.lowEvidenceWeight,
    LaunderingParams.launderingGradient, LaunderingParams.highResidual,
    LaunderingParams.lowResidual, clipDeviation, LoopParams.clipUnit]

/-- Consequently the bounded captured satisfaction is not the paper's unbounded formula. -/
theorem boundedHighLimitCounterexample_satisfaction_ne :
    boundedHighLimitCounterexample.launderingSatisfaction 1 1 (-1) ≠
      -boundedHighLimitCounterexample.πH * boundedHighLimitCounterexample.κ ^ 2 *
        (boundedHighLimitCounterexample.ιH /
          (boundedHighLimitCounterexample.ηH * boundedHighLimitCounterexample.κ -
            boundedHighLimitCounterexample.ζ)) ^ 2 := by
  norm_num [boundedHighLimitCounterexample, LaunderingParams.launderingSatisfaction,
    LaunderingParams.highResidual, LaunderingParams.lowResidual]

#print axioms clipDeviation_mem
#print axioms clipDeviation_eq_self
#print axioms clipDeviation_eq_top
#print axioms clipDeviation_eq_bot
#print axioms monotone_clipDeviation
#print axioms abs_clipDeviation
#print axioms abs_clipDeviation_sub_le
#print axioms boundedLowStep_sign_alignment
#print axioms bounded_low_sign_alignment
#print axioms bounded_laundering_policy_monotone
#print axioms bounded_launderingGradient_floor
#print axioms bounded_laundering_residual_contraction
#print axioms bounded_laundering_policy_tendsto_one
#print axioms bounded_low_feedback_eventually_noncontracting
#print axioms boundedLowStep_positive_face_fixed_of_weight_le
#print axioms boundedLowStep_negative_face_fixed_of_weight_le
#print axioms bounded_low_eventually_saturated
#print axioms bounded_finite_capture_of_low_saturation_rate
#print axioms highDeviationMultiplier_pos
#print axioms boundedHighStep_sign_alignment
#print axioms bounded_high_sign_alignment
#print axioms launderingGradient_high_term_le
#print axioms bounded_finite_capture_of_honest_channel
#print axioms highDeviationMultiplier_one
#print axioms boundedHighStationaryTarget_fixed
#print axioms boundedHighStep_capture_contraction
#print axioms bounded_high_tendsto_target_of_capture_recursion
#print axioms bounded_high_tendsto_target_of_capture
#print axioms bounded_high_tendsto_target_of_full_extraction
#print axioms highDeviationMultiplier_nonneg_le_capture
#print axioms boundedHighStep_target_error_le
#print axioms bounded_high_tendsto_stationary_target
#print axioms bounded_high_tendsto_zero_of_zero_injection
#print axioms boundedHighStationaryTarget_eq_zero_of_injection_zero
#print axioms boundedHighStationaryTarget_eq_of_feasible
#print axioms boundedHighStationaryTarget_sq_eq_bound_sq_of_lt_abs
#print axioms bounded_high_abs_tendsto_bound_of_outside
#print axioms bounded_low_weighted_error_tendsto_zero
#print axioms bounded_laundering_satisfaction_tendsto_of_high_limit
#print axioms bounded_laundering_satisfaction_tendsto_clipped_limit
#print axioms bounded_laundering_satisfaction_tendsto_feasible_limit
#print axioms bounded_laundering_satisfaction_tendsto_saturated_limit
#print axioms boundedCaptureRate_nonneg
#print axioms bounded_post_saturation_residual_contraction
#print axioms bounded_post_saturation_residual_exact_of_high_gradient_zero
#print axioms bounded_post_saturation_residual_strict_of_high_gradient_pos
#print axioms bounded_capacity_eventually_le_floor
#print axioms bounded_capacity_eventually_eq_floor
#print axioms boundedLowStep_positive_face_fixed
#print axioms boundedLowStep_negative_face_fixed
#print axioms bounded_capture_satisfaction_blind
#print axioms boundedBeliefsSaturation_core
#print axioms boundedBeliefsSaturation
#print axioms boundedAttainmentCounterexample_model
#print axioms boundedAttainmentCounterexample_trajectory
#print axioms boundedAttainmentPolicy_lt_one
#print axioms boundedAttainmentPolicy_tendsto_one
#print axioms bounded_persistent_high_injection_no_finite_capture
#print axioms boundedGeometricCounterexample_model
#print axioms bounded_zero_high_injection_not_exact_geometric
#print axioms boundedHighLimitCounterexample_model
#print axioms boundedHighLimitCounterexample_fixed_and_formula
#print axioms boundedHighLimitCounterexample_captured_state_fixed
#print axioms boundedHighLimitCounterexample_satisfaction_ne

end

end CivicAlignment.PaperII
