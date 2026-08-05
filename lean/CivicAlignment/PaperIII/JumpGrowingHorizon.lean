/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.JumpRate
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Paper III: uniform growing-horizon jump approximation

The projected jump excess contracts geometrically.  A weighted error absorbs
the excess coordinate into the neutral policy coordinate, while summability of
the decaying feedback gives horizon-independent amplification.  Consequently,
the rescaled full loop and projected jump orbit differ by at most
`C * |alpha| * n` at every finite horizon.  At the explicit projected transit
horizon, this yields a uniform logarithmic-transit estimate and a quantified
joint range placing the rescaled full orbit below the prescribed excess
tolerance.
-/

namespace CivicAlignment.PaperIII

open Filter Function Set Topology
open scoped BigOperators

noncomputable section

/-! ## Constants and the projected excess decay -/

/-- The uniform contraction gap `lambda_0-g`. -/
def jumpRateGap (p : LoopParams) : ℝ :=
  p.lambda₀ - p.g

/-- The uniform persistence ceiling `1-lambda_0+g`. -/
def jumpPersistenceCeiling (p : LoopParams) : ℝ :=
  1 - jumpRateGap p

/-- A weight large enough to absorb excess error into the neutral policy error. -/
def jumpGrowingErrorWeight (p : LoopParams) : ℝ :=
  1 + 2 * p.c / jumpRateGap p

/-- Weighted coordinate error between a rescaled full-loop state and a jump state. -/
def jumpWeightedError (p : LoopParams) (z y : LoopState) : ℝ :=
  |z.1 - y.1| + jumpGrowingErrorWeight p * |z.2 - y.2|

/-- Summable coupling of policy error back through the decaying jump excess. -/
def jumpGrowingFeedback (p : LoopParams) : ℝ :=
  2 * p.c ^ 2 + jumpGrowingErrorWeight p *
    (2 * p.η * (1 - p.lambda₀))

/-- Total summable feedback along the projected orbit. -/
def jumpGrowingCoupling (p : LoopParams) (x : LoopState) : ℝ :=
  jumpGrowingFeedback p * |x.2|

/-- Rate-linear forcing in the weighted error recurrence. -/
def jumpGrowingForcing (p : LoopParams) : ℝ :=
  jumpGradientBound p + jumpGrowingErrorWeight p * jumpStationaryBound p

/-- Finite product of the summable one-step amplification factors. -/
def jumpGrowingAmplification
    (p : LoopParams) (x : LoopState) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n,
    (1 + jumpGrowingCoupling p x * jumpPersistenceCeiling p ^ k)

/-- A horizon-independent upper bound for `jumpGrowingAmplification`. -/
def jumpGrowingHorizonConstant (p : LoopParams) (x : LoopState) : ℝ :=
  jumpGrowingForcing p *
    Real.exp (jumpGrowingCoupling p x / jumpRateGap p)

/-- Explicit projected-orbit horizon for reducing positive excess `E₀` to
tolerance `epsilon`. -/
def projectedJumpTransitHorizon (p : LoopParams) (E₀ ε : ℝ) : ℕ :=
  ⌈Real.log (E₀ / ε) /
    Real.log (1 / jumpPersistenceCeiling p)⌉₊

/-- The real logarithmic upper bound on `projectedJumpTransitHorizon`. -/
def projectedJumpTransitLogBound (p : LoopParams) (E₀ ε : ℝ) : ℝ :=
  Real.log (E₀ / ε) /
      Real.log (1 / jumpPersistenceCeiling p) + 1

theorem jumpRateGap_pos {p : LoopParams}
    (_model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀) :
    0 < jumpRateGap p := by
  exact sub_pos.mpr hgain

theorem jumpPersistenceCeiling_nonneg_lt_one {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀) :
    0 ≤ jumpPersistenceCeiling p ∧ jumpPersistenceCeiling p < 1 := by
  constructor
  · dsimp only [jumpPersistenceCeiling, jumpRateGap]
    linarith [model.lambda₀_lt_one, model.g_nonneg]
  · dsimp only [jumpPersistenceCeiling, jumpRateGap]
    linarith

theorem abs_jumpPersistence_le_ceiling {p : LoopParams}
    (model : LoopModelAssumptions p) (_hgain : p.g < p.lambda₀)
    {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    |jumpPersistence p β| ≤ jumpPersistenceCeiling p := by
  have hs := stockMultiplier_nonneg_le model hβ
  have hnonneg : 0 ≤ jumpPersistence p β := by
    simp only [jumpPersistence]
    exact add_nonneg hs.1 model.g_nonneg
  rw [abs_of_nonneg hnonneg]
  simp only [jumpPersistence, jumpPersistenceCeiling, jumpRateGap]
  linarith [hs.2]

theorem projectedJumpOrbit_excess_abs_le_geometric
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {x : LoopState}
    (hx : x.1 ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    |(((projectedJumpMap p)^[n]) x).2| ≤
      |x.2| * jumpPersistenceCeiling p ^ n := by
  have hq := jumpPersistenceCeiling_nonneg_lt_one model hgain
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iterate_succ_apply']
      simp only [projectedJumpMap, abs_mul]
      have hβ := projectedJumpMap_iterate_policy_mem (p := p) hx n
      calc
        |jumpPersistence p (((projectedJumpMap p)^[n]) x).1| *
              |(((projectedJumpMap p)^[n]) x).2| ≤
            jumpPersistenceCeiling p *
              |(((projectedJumpMap p)^[n]) x).2| :=
          mul_le_mul_of_nonneg_right
            (abs_jumpPersistence_le_ceiling model hgain hβ) (abs_nonneg _)
        _ ≤ jumpPersistenceCeiling p *
              (|x.2| * jumpPersistenceCeiling p ^ n) :=
          mul_le_mul_of_nonneg_left ih hq.1
        _ = |x.2| * jumpPersistenceCeiling p ^ (n + 1) := by
          rw [pow_succ]
          ring

theorem jumpGrowingErrorWeight_one_le {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀) :
    1 ≤ jumpGrowingErrorWeight p := by
  dsimp only [jumpGrowingErrorWeight]
  have hgap := (jumpRateGap_pos model hgain).le
  have hc : 0 ≤ 2 * p.c := mul_nonneg (by norm_num) model.c_pos.le
  exact le_add_of_nonneg_right (div_nonneg hc hgap)

theorem jumpGrowingErrorWeight_absorbs {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀) :
    2 * p.c + jumpGrowingErrorWeight p * jumpPersistenceCeiling p ≤
      jumpGrowingErrorWeight p := by
  have hgap := jumpRateGap_pos model hgain
  have hgap' : p.lambda₀ - p.g ≠ 0 := by
    dsimp only [jumpRateGap] at hgap
    linarith
  have hidentity :
      2 * p.c + jumpGrowingErrorWeight p * jumpPersistenceCeiling p =
        jumpGrowingErrorWeight p - jumpRateGap p := by
    dsimp only [jumpGrowingErrorWeight, jumpPersistenceCeiling, jumpRateGap]
    field_simp [hgap']
    ring
  rw [hidentity]
  linarith

/-! ## Refined one-step recurrence -/

/-- Coordinatewise one-step error bounds which retain contraction in the
excess coordinate and charge state dependence only against the decaying
projected excess. -/
theorem scaledLoopMap_projectedJumpMap_refined_error_le
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {z y : LoopState} {α : ℝ}
    (hz : z.1 ∈ Icc (0 : ℝ) 1) (hy : y.1 ∈ Icc (0 : ℝ) 1) :
    |(scaledLoopMap p α z).1 - (projectedJumpMap p y).1| ≤
        |z.1 - y.1| + 2 * p.c * |z.2 - y.2| +
          (2 * p.c ^ 2 * |z.1 - y.1|) * |y.2| +
            |α| * jumpGradientBound p ∧
      |(scaledLoopMap p α z).2 - (projectedJumpMap p y).2| ≤
        jumpPersistenceCeiling p * |z.2 - y.2| +
          ((2 * p.η * (1 - p.lambda₀)) * |z.1 - y.1|) * |y.2| +
            |α| * jumpStationaryBound p := by
  have hc : 0 ≤ 2 * p.c := mul_nonneg (by norm_num) model.c_pos.le
  have hcSq : 0 ≤ 2 * p.c ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg p.c)
  have hk : 0 ≤ 2 * p.η * (1 - p.lambda₀) :=
    mul_nonneg (mul_nonneg (by norm_num) model.η_pos.le)
      (sub_nonneg.mpr model.lambda₀_lt_one.le)
  have hrate : 0 ≤ |α| := abs_nonneg α
  have habsFour (a b c d : ℝ) :
      |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
    calc
      |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
      _ ≤ (|a + b| + |c|) + |d| := by
        linarith [abs_add_le (a + b) c]
      _ ≤ (|a| + |b| + |c|) + |d| := by
        linarith [abs_add_le a b]
  have hgainTerm :
      |jumpGain p z.1| * |z.2 - y.2| ≤
        (2 * p.c) * |z.2 - y.2| :=
    mul_le_mul_of_nonneg_right (abs_jumpGain_le_two_c model hz) (abs_nonneg _)
  have hgainDifferenceTerm :
      |jumpGain p z.1 - jumpGain p y.1| * |y.2| ≤
        (2 * p.c ^ 2 * |z.1 - y.1|) * |y.2| := by
    rw [abs_jumpGain_sub]
  have hgradientTerm :
      |α| * |p.G z.1| ≤ |α| * jumpGradientBound p :=
    mul_le_mul_of_nonneg_left (abs_G_le_jumpGradientBound model hgain hz) hrate
  have hpolicyIdentity :
      (z.1 + jumpGain p z.1 * z.2 + α * p.G z.1) -
          (y.1 + jumpGain p y.1 * y.2) =
        (z.1 - y.1) + jumpGain p z.1 * (z.2 - y.2) +
          (jumpGain p z.1 - jumpGain p y.1) * y.2 + α * p.G z.1 := by
    ring
  have hpolicyInput :
      |(z.1 + jumpGain p z.1 * z.2 + α * p.G z.1) -
          (y.1 + jumpGain p y.1 * y.2)| ≤
        |z.1 - y.1| + 2 * p.c * |z.2 - y.2| +
          (2 * p.c ^ 2 * |z.1 - y.1|) * |y.2| +
            |α| * jumpGradientBound p := by
    rw [hpolicyIdentity]
    calc
      |(z.1 - y.1) + jumpGain p z.1 * (z.2 - y.2) +
          (jumpGain p z.1 - jumpGain p y.1) * y.2 + α * p.G z.1| ≤
          |z.1 - y.1| + |jumpGain p z.1| * |z.2 - y.2| +
            |jumpGain p z.1 - jumpGain p y.1| * |y.2| +
              |α| * |p.G z.1| := by
        simpa only [abs_mul] using habsFour
          (z.1 - y.1) (jumpGain p z.1 * (z.2 - y.2))
          ((jumpGain p z.1 - jumpGain p y.1) * y.2) (α * p.G z.1)
      _ ≤ |z.1 - y.1| + 2 * p.c * |z.2 - y.2| +
          (2 * p.c ^ 2 * |z.1 - y.1|) * |y.2| +
            |α| * jumpGradientBound p :=
        add_le_add (add_le_add (add_le_add le_rfl hgainTerm)
          hgainDifferenceTerm) hgradientTerm
  have hpolicy :
      |(scaledLoopMap p α z).1 - (projectedJumpMap p y).1| ≤
        |z.1 - y.1| + 2 * p.c * |z.2 - y.2| +
          (2 * p.c ^ 2 * |z.1 - y.1|) * |y.2| +
            |α| * jumpGradientBound p :=
    (clipUnit_dist_le
      (z.1 + jumpGain p z.1 * z.2 + α * p.G z.1)
      (y.1 + jumpGain p y.1 * y.2)).trans hpolicyInput
  have hpersistenceTerm :
      |jumpPersistence p z.1| * |z.2 - y.2| ≤
        jumpPersistenceCeiling p * |z.2 - y.2| :=
    mul_le_mul_of_nonneg_right
      (abs_jumpPersistence_le_ceiling model hgain hz) (abs_nonneg _)
  have hpersistenceDifferenceTerm :
      |jumpPersistence p z.1 - jumpPersistence p y.1| * |y.2| ≤
        ((2 * p.η * (1 - p.lambda₀)) * |z.1 - y.1|) * |y.2| := by
    exact mul_le_mul_of_nonneg_right
      (abs_jumpPersistence_sub_le model hz hy) (abs_nonneg _)
  have hstockDifference :
      |p.stationaryStock z.1 -
          p.stationaryStock (scaledLoopMap p α z).1| ≤
        jumpStationaryBound p :=
    abs_stationaryStock_sub_le_jumpStationaryBound model hgain hz
      (scaledLoopMap_policy_mem p α z)
  have hstockDifferenceTerm :
      |α| * |p.stationaryStock z.1 -
          p.stationaryStock (scaledLoopMap p α z).1| ≤
        |α| * jumpStationaryBound p :=
    mul_le_mul_of_nonneg_left hstockDifference hrate
  have hexcessIdentity :
      (scaledLoopMap p α z).2 - (projectedJumpMap p y).2 =
        jumpPersistence p z.1 * (z.2 - y.2) +
          (jumpPersistence p z.1 - jumpPersistence p y.1) * y.2 +
            α * (p.stationaryStock z.1 -
              p.stationaryStock (scaledLoopMap p α z).1) := by
    simp only [scaledLoopMap, projectedJumpMap]
    ring
  have hexcess :
      |(scaledLoopMap p α z).2 - (projectedJumpMap p y).2| ≤
        jumpPersistenceCeiling p * |z.2 - y.2| +
          ((2 * p.η * (1 - p.lambda₀)) * |z.1 - y.1|) * |y.2| +
            |α| * jumpStationaryBound p := by
    rw [hexcessIdentity]
    calc
      |jumpPersistence p z.1 * (z.2 - y.2) +
          (jumpPersistence p z.1 - jumpPersistence p y.1) * y.2 +
            α * (p.stationaryStock z.1 -
              p.stationaryStock (scaledLoopMap p α z).1)| ≤
          |jumpPersistence p z.1| * |z.2 - y.2| +
            |jumpPersistence p z.1 - jumpPersistence p y.1| * |y.2| +
              |α| * |p.stationaryStock z.1 -
                p.stationaryStock (scaledLoopMap p α z).1| := by
        simpa only [abs_mul, add_zero, abs_zero] using habsFour
          (jumpPersistence p z.1 * (z.2 - y.2))
          ((jumpPersistence p z.1 - jumpPersistence p y.1) * y.2)
          (α * (p.stationaryStock z.1 -
            p.stationaryStock (scaledLoopMap p α z).1)) 0
      _ ≤ jumpPersistenceCeiling p * |z.2 - y.2| +
          ((2 * p.η * (1 - p.lambda₀)) * |z.1 - y.1|) * |y.2| +
            |α| * jumpStationaryBound p :=
        add_le_add (add_le_add hpersistenceTerm hpersistenceDifferenceTerm)
          hstockDifferenceTerm
  exact ⟨hpolicy, hexcess⟩

/-- The refined coordinate bounds combine into a scalar recurrence whose
time-dependent amplification is summable along the projected orbit. -/
theorem scaledLoopMap_projectedJumpMap_weighted_error_le
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {z y : LoopState} {α : ℝ}
    (hz : z.1 ∈ Icc (0 : ℝ) 1) (hy : y.1 ∈ Icc (0 : ℝ) 1) :
    jumpWeightedError p (scaledLoopMap p α z) (projectedJumpMap p y) ≤
      (1 + jumpGrowingFeedback p * |y.2|) * jumpWeightedError p z y +
        |α| * jumpGrowingForcing p := by
  have hcoord := scaledLoopMap_projectedJumpMap_refined_error_le
    model hgain (α := α) hz hy
  have hwOne := jumpGrowingErrorWeight_one_le model hgain
  have hw : 0 ≤ jumpGrowingErrorWeight p := zero_le_one.trans hwOne
  have habsorb := jumpGrowingErrorWeight_absorbs model hgain
  have hb : 0 ≤ |z.1 - y.1| := abs_nonneg _
  have he : 0 ≤ |z.2 - y.2| := abs_nonneg _
  have hyE : 0 ≤ |y.2| := abs_nonneg _
  have hfeedback : 0 ≤ jumpGrowingFeedback p := by
    dsimp only [jumpGrowingFeedback]
    have hk : 0 ≤ 2 * p.η * (1 - p.lambda₀) :=
      mul_nonneg (mul_nonneg (by norm_num) model.η_pos.le)
        (sub_nonneg.mpr model.lambda₀_lt_one.le)
    positivity
  have hpadding :
      0 ≤
        (jumpGrowingErrorWeight p -
            (2 * p.c + jumpGrowingErrorWeight p * jumpPersistenceCeiling p)) *
            |z.2 - y.2| +
          jumpGrowingFeedback p * |y.2| *
            (jumpGrowingErrorWeight p * |z.2 - y.2|) := by
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr habsorb) he)
      (mul_nonneg (mul_nonneg hfeedback hyE) (mul_nonneg hw he))
  have hcombined :
      jumpWeightedError p (scaledLoopMap p α z) (projectedJumpMap p y) ≤
        (|z.1 - y.1| + 2 * p.c * |z.2 - y.2| +
            (2 * p.c ^ 2 * |z.1 - y.1|) * |y.2| +
              |α| * jumpGradientBound p) +
          jumpGrowingErrorWeight p *
            (jumpPersistenceCeiling p * |z.2 - y.2| +
              ((2 * p.η * (1 - p.lambda₀)) * |z.1 - y.1|) * |y.2| +
                |α| * jumpStationaryBound p) := by
    dsimp only [jumpWeightedError]
    exact add_le_add hcoord.1 (mul_le_mul_of_nonneg_left hcoord.2 hw)
  calc
    jumpWeightedError p (scaledLoopMap p α z) (projectedJumpMap p y) ≤
        (|z.1 - y.1| + 2 * p.c * |z.2 - y.2| +
            (2 * p.c ^ 2 * |z.1 - y.1|) * |y.2| +
              |α| * jumpGradientBound p) +
          jumpGrowingErrorWeight p *
            (jumpPersistenceCeiling p * |z.2 - y.2| +
              ((2 * p.η * (1 - p.lambda₀)) * |z.1 - y.1|) * |y.2| +
                |α| * jumpStationaryBound p) := hcombined
    _ ≤ (|z.1 - y.1| + 2 * p.c * |z.2 - y.2| +
            (2 * p.c ^ 2 * |z.1 - y.1|) * |y.2| +
              |α| * jumpGradientBound p) +
          jumpGrowingErrorWeight p *
            (jumpPersistenceCeiling p * |z.2 - y.2| +
              ((2 * p.η * (1 - p.lambda₀)) * |z.1 - y.1|) * |y.2| +
                |α| * jumpStationaryBound p) +
          ((jumpGrowingErrorWeight p -
              (2 * p.c + jumpGrowingErrorWeight p * jumpPersistenceCeiling p)) *
              |z.2 - y.2| +
            jumpGrowingFeedback p * |y.2| *
              (jumpGrowingErrorWeight p * |z.2 - y.2|)) :=
      le_add_of_nonneg_right hpadding
    _ = (1 + jumpGrowingFeedback p * |y.2|) *
          jumpWeightedError p z y + |α| * jumpGrowingForcing p := by
      simp only [jumpWeightedError, jumpGrowingFeedback, jumpGrowingForcing]
      ring

/-! ## Summable amplification -/

theorem jumpWeightedError_nonneg {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (z y : LoopState) :
    0 ≤ jumpWeightedError p z y := by
  exact add_nonneg (abs_nonneg _)
    (mul_nonneg (zero_le_one.trans
      (jumpGrowingErrorWeight_one_le model hgain)) (abs_nonneg _))

theorem jumpGrowingFeedback_nonneg {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀) :
    0 ≤ jumpGrowingFeedback p := by
  have hw : 0 ≤ jumpGrowingErrorWeight p :=
    zero_le_one.trans (jumpGrowingErrorWeight_one_le model hgain)
  have hk : 0 ≤ 2 * p.η * (1 - p.lambda₀) :=
    mul_nonneg (mul_nonneg (by norm_num) model.η_pos.le)
      (sub_nonneg.mpr model.lambda₀_lt_one.le)
  dsimp only [jumpGrowingFeedback]
  positivity

theorem jumpGrowingCoupling_nonneg {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (x : LoopState) :
    0 ≤ jumpGrowingCoupling p x := by
  exact mul_nonneg (jumpGrowingFeedback_nonneg model hgain) (abs_nonneg _)

theorem jumpGrowingForcing_nonneg {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀) :
    0 ≤ jumpGrowingForcing p := by
  have hstationary := (jumpStationaryBound_pos model hgain).le
  have hgradient : 0 ≤ jumpGradientBound p := by
    dsimp only [jumpGradientBound]
    exact add_nonneg model.v_pos.le
      (mul_nonneg (mul_nonneg (by norm_num) model.c_pos.le) hstationary)
  have hw : 0 ≤ jumpGrowingErrorWeight p :=
    zero_le_one.trans (jumpGrowingErrorWeight_one_le model hgain)
  exact add_nonneg hgradient (mul_nonneg hw hstationary)

/-- Along matching exact and projected iterates, weighted error obeys a
nonautonomous scalar recurrence with a geometrically decaying multiplier. -/
theorem scaledLoopOrbit_weighted_error_succ_le
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {x : LoopState}
    (hx : x.1 ∈ Icc (0 : ℝ) 1) (α : ℝ) (n : ℕ) :
    jumpWeightedError p
        (((scaledLoopMap p α)^[n + 1]) x)
        (((projectedJumpMap p)^[n + 1]) x) ≤
      (1 + jumpGrowingCoupling p x * jumpPersistenceCeiling p ^ n) *
          jumpWeightedError p
            (((scaledLoopMap p α)^[n]) x)
            (((projectedJumpMap p)^[n]) x) +
        |α| * jumpGrowingForcing p := by
  let z := ((scaledLoopMap p α)^[n]) x
  let y := ((projectedJumpMap p)^[n]) x
  have hz : z.1 ∈ Icc (0 : ℝ) 1 :=
    scaledLoopMap_iterate_policy_mem (p := p) (α := α) hx n
  have hy : y.1 ∈ Icc (0 : ℝ) 1 :=
    projectedJumpMap_iterate_policy_mem (p := p) hx n
  have hstep := scaledLoopMap_projectedJumpMap_weighted_error_le
    model hgain (α := α) hz hy
  have hdecay := projectedJumpOrbit_excess_abs_le_geometric
    model hgain hx n
  have hfeedback := jumpGrowingFeedback_nonneg model hgain
  have hcoefficient :
      jumpGrowingFeedback p * |y.2| ≤
        jumpGrowingCoupling p x * jumpPersistenceCeiling p ^ n := by
    calc
      jumpGrowingFeedback p * |y.2| ≤
          jumpGrowingFeedback p *
            (|x.2| * jumpPersistenceCeiling p ^ n) :=
        mul_le_mul_of_nonneg_left hdecay hfeedback
      _ = jumpGrowingCoupling p x * jumpPersistenceCeiling p ^ n := by
        simp only [jumpGrowingCoupling]
        ring
  have herror := jumpWeightedError_nonneg model hgain z y
  have hamplification :
      (1 + jumpGrowingFeedback p * |y.2|) * jumpWeightedError p z y ≤
        (1 + jumpGrowingCoupling p x * jumpPersistenceCeiling p ^ n) *
          jumpWeightedError p z y :=
    mul_le_mul_of_nonneg_right (by linarith [hcoefficient]) herror
  have hfinal := hstep.trans (add_le_add hamplification le_rfl)
  simpa only [z, y, iterate_succ_apply'] using hfinal

theorem jumpGrowingAmplification_one_le
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) (x : LoopState) (n : ℕ) :
    1 ≤ jumpGrowingAmplification p x n := by
  apply Finset.one_le_prod
  intro k _hk
  exact le_add_of_nonneg_right
    (mul_nonneg (jumpGrowingCoupling_nonneg model hgain x)
      (pow_nonneg (jumpPersistenceCeiling_nonneg_lt_one model hgain).1 k))

theorem jumpGrowingAmplification_succ
    (p : LoopParams) (x : LoopState) (n : ℕ) :
    jumpGrowingAmplification p x (n + 1) =
      jumpGrowingAmplification p x n *
        (1 + jumpGrowingCoupling p x * jumpPersistenceCeiling p ^ n) := by
  simp only [jumpGrowingAmplification, Finset.prod_range_succ]

/-- The finite amplification product is uniformly bounded because its
nonconstant factors have a geometric, hence summable, excess. -/
theorem jumpGrowingAmplification_le_exp
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) (x : LoopState) (n : ℕ) :
    jumpGrowingAmplification p x n ≤
      Real.exp (jumpGrowingCoupling p x / jumpRateGap p) := by
  have hq := jumpPersistenceCeiling_nonneg_lt_one model hgain
  have hcoupling := jumpGrowingCoupling_nonneg model hgain x
  have hprod :
      jumpGrowingAmplification p x n ≤
        Real.exp (∑ k ∈ Finset.range n,
          jumpGrowingCoupling p x * jumpPersistenceCeiling p ^ k) := by
    dsimp only [jumpGrowingAmplification]
    exact Real.prod_one_add_le_exp_sum (Finset.range n)
      (fun k ↦ mul_nonneg hcoupling (pow_nonneg hq.1 k))
  have hgeom :
      ∑ k ∈ Finset.range n, jumpPersistenceCeiling p ^ k ≤
        1 / (1 - jumpPersistenceCeiling p) := by
    have h := geom_sum_Ico_le_of_lt_one
      (K := ℝ) (m := 0) (n := n) hq.1 hq.2
    simpa only [Nat.Ico_zero_eq_range, pow_zero, one_div] using h
  have hsum :
      ∑ k ∈ Finset.range n,
          jumpGrowingCoupling p x * jumpPersistenceCeiling p ^ k ≤
        jumpGrowingCoupling p x / jumpRateGap p := by
    calc
      ∑ k ∈ Finset.range n,
          jumpGrowingCoupling p x * jumpPersistenceCeiling p ^ k =
          jumpGrowingCoupling p x *
            (∑ k ∈ Finset.range n, jumpPersistenceCeiling p ^ k) := by
        rw [Finset.mul_sum]
      _ ≤ jumpGrowingCoupling p x *
            (1 / (1 - jumpPersistenceCeiling p)) :=
        mul_le_mul_of_nonneg_left hgeom hcoupling
      _ = jumpGrowingCoupling p x / jumpRateGap p := by
        simp only [jumpPersistenceCeiling]
        ring
  exact hprod.trans (Real.exp_le_exp.mpr hsum)

/-! ## Uniform linear-horizon bound -/

/-- Before replacing the finite product by its global bound, weighted orbit
error is at most the forcing times the horizon times that product. -/
theorem scaledLoopOrbit_weighted_error_le_amplification
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {x : LoopState}
    (hx : x.1 ∈ Icc (0 : ℝ) 1) (α : ℝ) (n : ℕ) :
    jumpWeightedError p
        (((scaledLoopMap p α)^[n]) x)
        (((projectedJumpMap p)^[n]) x) ≤
      |α| * jumpGrowingForcing p * (n : ℝ) *
        jumpGrowingAmplification p x n := by
  have hq := jumpPersistenceCeiling_nonneg_lt_one model hgain
  have hcoupling := jumpGrowingCoupling_nonneg model hgain x
  have hforcing := jumpGrowingForcing_nonneg model hgain
  have hrate : 0 ≤ |α| := abs_nonneg α
  have hsource : 0 ≤ |α| * jumpGrowingForcing p :=
    mul_nonneg hrate hforcing
  induction n with
  | zero => simp [jumpWeightedError, jumpGrowingAmplification]
  | succ n ih =>
      have hstep := scaledLoopOrbit_weighted_error_succ_le
        model hgain hx α n
      have hfactor :
          0 ≤ 1 + jumpGrowingCoupling p x * jumpPersistenceCeiling p ^ n :=
        add_nonneg zero_le_one
          (mul_nonneg hcoupling (pow_nonneg hq.1 n))
      have hP := jumpGrowingAmplification_one_le model hgain x (n + 1)
      have hsourceP :
          |α| * jumpGrowingForcing p ≤
            |α| * jumpGrowingForcing p *
              jumpGrowingAmplification p x (n + 1) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hP hsource
      calc
        jumpWeightedError p
            (((scaledLoopMap p α)^[n + 1]) x)
            (((projectedJumpMap p)^[n + 1]) x) ≤
          (1 + jumpGrowingCoupling p x * jumpPersistenceCeiling p ^ n) *
              jumpWeightedError p
                (((scaledLoopMap p α)^[n]) x)
                (((projectedJumpMap p)^[n]) x) +
            |α| * jumpGrowingForcing p := hstep
        _ ≤ (1 + jumpGrowingCoupling p x * jumpPersistenceCeiling p ^ n) *
              (|α| * jumpGrowingForcing p * (n : ℝ) *
                jumpGrowingAmplification p x n) +
            |α| * jumpGrowingForcing p :=
          add_le_add (mul_le_mul_of_nonneg_left ih hfactor) le_rfl
        _ = |α| * jumpGrowingForcing p * (n : ℝ) *
              jumpGrowingAmplification p x (n + 1) +
            |α| * jumpGrowingForcing p := by
          rw [jumpGrowingAmplification_succ]
          ring
        _ ≤ |α| * jumpGrowingForcing p * (n : ℝ) *
              jumpGrowingAmplification p x (n + 1) +
            |α| * jumpGrowingForcing p *
              jumpGrowingAmplification p x (n + 1) :=
          add_le_add le_rfl hsourceP
        _ = |α| * jumpGrowingForcing p * ((n + 1 : ℕ) : ℝ) *
              jumpGrowingAmplification p x (n + 1) := by
          norm_num
          ring

/-- Paper III's growing-horizon strengthening of `thm:jump`: at every time,
both rescaled coordinates are within `C * |alpha| * n` of the projected jump
orbit, with one explicit constant independent of `alpha` and `n`. -/
theorem scaledLoopOrbit_error_le_linearHorizon
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {x : LoopState}
    (hx : x.1 ∈ Icc (0 : ℝ) 1) (α : ℝ) (n : ℕ) :
    |(((scaledLoopMap p α)^[n]) x).1 -
        (((projectedJumpMap p)^[n]) x).1| ≤
        jumpGrowingHorizonConstant p x * |α| * (n : ℝ) ∧
      |(((scaledLoopMap p α)^[n]) x).2 -
        (((projectedJumpMap p)^[n]) x).2| ≤
        jumpGrowingHorizonConstant p x * |α| * (n : ℝ) := by
  have hweighted := scaledLoopOrbit_weighted_error_le_amplification
    model hgain hx α n
  have hamp := jumpGrowingAmplification_le_exp model hgain x n
  have hsource :
      0 ≤ |α| * jumpGrowingForcing p * (n : ℝ) := by
    exact mul_nonneg
      (mul_nonneg (abs_nonneg α) (jumpGrowingForcing_nonneg model hgain))
      (Nat.cast_nonneg n)
  have hglobal :
      jumpWeightedError p
          (((scaledLoopMap p α)^[n]) x)
          (((projectedJumpMap p)^[n]) x) ≤
        jumpGrowingHorizonConstant p x * |α| * (n : ℝ) := by
    calc
      jumpWeightedError p
          (((scaledLoopMap p α)^[n]) x)
          (((projectedJumpMap p)^[n]) x) ≤
        |α| * jumpGrowingForcing p * (n : ℝ) *
          jumpGrowingAmplification p x n := hweighted
      _ ≤ |α| * jumpGrowingForcing p * (n : ℝ) *
          Real.exp (jumpGrowingCoupling p x / jumpRateGap p) :=
        mul_le_mul_of_nonneg_left hamp hsource
      _ = jumpGrowingHorizonConstant p x * |α| * (n : ℝ) := by
        simp only [jumpGrowingHorizonConstant]
        ring
  have hpolicy :
      |(((scaledLoopMap p α)^[n]) x).1 -
          (((projectedJumpMap p)^[n]) x).1| ≤
        jumpWeightedError p
          (((scaledLoopMap p α)^[n]) x)
          (((projectedJumpMap p)^[n]) x) := by
    dsimp only [jumpWeightedError]
    exact le_add_of_nonneg_right
      (mul_nonneg
        (zero_le_one.trans (jumpGrowingErrorWeight_one_le model hgain))
        (abs_nonneg _))
  have hexcess :
      |(((scaledLoopMap p α)^[n]) x).2 -
          (((projectedJumpMap p)^[n]) x).2| ≤
        jumpWeightedError p
          (((scaledLoopMap p α)^[n]) x)
          (((projectedJumpMap p)^[n]) x) := by
    have hweightedExcess :
        |(((scaledLoopMap p α)^[n]) x).2 -
            (((projectedJumpMap p)^[n]) x).2| ≤
          jumpGrowingErrorWeight p *
            |(((scaledLoopMap p α)^[n]) x).2 -
              (((projectedJumpMap p)^[n]) x).2| := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (jumpGrowingErrorWeight_one_le model hgain) (abs_nonneg _)
    exact hweightedExcess.trans (le_add_of_nonneg_left (abs_nonneg _))
  exact ⟨hpolicy.trans hglobal, hexcess.trans hglobal⟩

/-- The original full-loop orbit inherits the same all-horizon estimate after
the paper's excess-stock rescaling. -/
theorem rescaledFullLoopOrbit_error_le_linearHorizon
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {x : LoopState}
    (hx : x.1 ∈ Icc (0 : ℝ) 1) {α : ℝ} (hα : α ≠ 0) (n : ℕ) :
    |(rescaledFullLoopOrbit p α x n).1 -
        (((projectedJumpMap p)^[n]) x).1| ≤
        jumpGrowingHorizonConstant p x * |α| * (n : ℝ) ∧
      |(rescaledFullLoopOrbit p α x n).2 -
        (((projectedJumpMap p)^[n]) x).2| ≤
        jumpGrowingHorizonConstant p x * |α| * (n : ℝ) := by
  rw [rescaledFullLoopOrbit_eq_scaledLoopOrbit model hgain hα hx n]
  exact scaledLoopOrbit_error_le_linearHorizon model hgain hx α n

/-! ## The logarithmic projected-transit horizon -/

theorem jumpPersistenceCeiling_pos {p : LoopParams}
    (model : LoopModelAssumptions p) (_hgain : p.g < p.lambda₀) :
    0 < jumpPersistenceCeiling p := by
  dsimp only [jumpPersistenceCeiling, jumpRateGap]
  linarith [model.lambda₀_lt_one, model.g_nonneg]

theorem jumpGrowingHorizonConstant_nonneg {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (x : LoopState) :
    0 ≤ jumpGrowingHorizonConstant p x := by
  exact mul_nonneg (jumpGrowingForcing_nonneg model hgain) (Real.exp_pos _).le

/-- The ceiling-defined transit horizon is strictly below its real logarithmic
value plus one. -/
theorem projectedJumpTransitHorizon_cast_lt
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {E₀ ε : ℝ}
    (_hE₀ : 0 < E₀) (hε : 0 < ε) (hεE₀ : ε ≤ E₀) :
    (projectedJumpTransitHorizon p E₀ ε : ℝ) <
      projectedJumpTransitLogBound p E₀ ε := by
  have hq := jumpPersistenceCeiling_nonneg_lt_one model hgain
  have hqpos := jumpPersistenceCeiling_pos model hgain
  have hbase : 1 < 1 / jumpPersistenceCeiling p :=
    one_lt_one_div hqpos hq.2
  have hratio : 1 ≤ E₀ / ε := by
    apply (le_div_iff₀ hε).2
    simpa only [one_mul] using hεE₀
  have hquotient :
      0 ≤ Real.log (E₀ / ε) /
        Real.log (1 / jumpPersistenceCeiling p) :=
    div_nonneg (Real.log_nonneg hratio) (Real.log_pos hbase).le
  exact Nat.ceil_lt_add_one hquotient

/-- At the explicit logarithmic horizon, the projected jump excess has fallen
to the requested positive tolerance. -/
theorem projectedJumpOrbit_excess_at_transitHorizon_le
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β₀ E₀ ε : ℝ}
    (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1)
    (hE₀ : 0 < E₀) (hε : 0 < ε) (_hεE₀ : ε ≤ E₀) :
    |(((projectedJumpMap p)^[projectedJumpTransitHorizon p E₀ ε])
        (β₀, E₀)).2| ≤ ε := by
  let q := jumpPersistenceCeiling p
  let H := projectedJumpTransitHorizon p E₀ ε
  have hq := jumpPersistenceCeiling_nonneg_lt_one model hgain
  have hqpos := jumpPersistenceCeiling_pos model hgain
  have hbase : 1 < 1 / q := by
    dsimp only [q]
    exact one_lt_one_div hqpos hq.2
  have hlogBase : 0 < Real.log (1 / q) := Real.log_pos hbase
  have hceil : Real.log (E₀ / ε) / Real.log (1 / q) ≤ (H : ℝ) := by
    exact Nat.le_ceil _
  have hlog :
      Real.log (E₀ / ε) ≤ (H : ℝ) * Real.log (1 / q) :=
    (div_le_iff₀ hlogBase).1 hceil
  have hratioPow : E₀ / ε ≤ (1 / q) ^ H := by
    apply (Real.log_le_log_iff (div_pos hE₀ hε)
      (pow_pos (zero_lt_one.trans hbase) _)).1
    rw [Real.log_pow]
    exact hlog
  have hreciprocal : (1 / q) ^ H * q ^ H = 1 := by
    rw [← mul_pow]
    have hqne : q ≠ 0 := by dsimp only [q]; exact hqpos.ne'
    rw [div_mul_cancel₀ 1 hqne, one_pow]
  have hscaled : (E₀ / ε) * q ^ H ≤ 1 := by
    calc
      (E₀ / ε) * q ^ H ≤ (1 / q) ^ H * q ^ H :=
        mul_le_mul_of_nonneg_right hratioPow (pow_nonneg hq.1 H)
      _ = 1 := hreciprocal
  have hscaled' : E₀ * q ^ H / ε ≤ 1 := by
    calc
      E₀ * q ^ H / ε = (E₀ / ε) * q ^ H := by ring
      _ ≤ 1 := hscaled
  have hgeom := projectedJumpOrbit_excess_abs_le_geometric
    model hgain (x := (β₀, E₀)) hβ₀ H
  have hpower : E₀ * q ^ H ≤ ε := by
    have := (div_le_iff₀ hε).1 hscaled'
    simpa only [one_mul] using this
  calc
    |(((projectedJumpMap p)^[projectedJumpTransitHorizon p E₀ ε])
        (β₀, E₀)).2| ≤ E₀ * q ^ H := by
      simpa only [H, q, abs_of_pos hE₀] using hgeom
    _ ≤ ε := hpower

/-- Uniform growing-horizon estimate: every point of the projected transit up
to its named logarithmic horizon has coordinate error bounded by one constant
times `|alpha|` times the displayed logarithmic factor.  The constant is
independent of `alpha`, `epsilon`, and the time inside the transit. -/
theorem scaledLoopOrbit_error_le_logTransit
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {x : LoopState}
    (hx : x.1 ∈ Icc (0 : ℝ) 1) (hxE : 0 < x.2)
    {ε : ℝ} (hε : 0 < ε) (hεE : ε ≤ x.2)
    (α : ℝ) {n : ℕ}
    (hn : n ≤ projectedJumpTransitHorizon p x.2 ε) :
    |(((scaledLoopMap p α)^[n]) x).1 -
        (((projectedJumpMap p)^[n]) x).1| ≤
        jumpGrowingHorizonConstant p x * |α| *
          projectedJumpTransitLogBound p x.2 ε ∧
      |(((scaledLoopMap p α)^[n]) x).2 -
        (((projectedJumpMap p)^[n]) x).2| ≤
        jumpGrowingHorizonConstant p x * |α| *
          projectedJumpTransitLogBound p x.2 ε := by
  have hlinear := scaledLoopOrbit_error_le_linearHorizon
    model hgain hx α n
  have hH := projectedJumpTransitHorizon_cast_lt
    model hgain hxE hε hεE
  have hnCast : (n : ℝ) ≤
      (projectedJumpTransitHorizon p x.2 ε : ℝ) := by
    exact_mod_cast hn
  have hnLog : (n : ℝ) ≤ projectedJumpTransitLogBound p x.2 ε :=
    hnCast.trans hH.le
  have hcoefficient :
      0 ≤ jumpGrowingHorizonConstant p x * |α| :=
    mul_nonneg (jumpGrowingHorizonConstant_nonneg model hgain x) (abs_nonneg α)
  have hscale := mul_le_mul_of_nonneg_left hnLog hcoefficient
  exact ⟨hlinear.1.trans hscale, hlinear.2.trans hscale⟩

/-- The rescaled original loop satisfies the same uniform logarithmic-transit
bound at every positive, nonzero adaptation rate. -/
theorem rescaledFullLoopOrbit_error_le_logTransit
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {x : LoopState}
    (hx : x.1 ∈ Icc (0 : ℝ) 1) (hxE : 0 < x.2)
    {ε : ℝ} (hε : 0 < ε) (hεE : ε ≤ x.2)
    {α : ℝ} (hα : α ≠ 0) {n : ℕ}
    (hn : n ≤ projectedJumpTransitHorizon p x.2 ε) :
    |(rescaledFullLoopOrbit p α x n).1 -
        (((projectedJumpMap p)^[n]) x).1| ≤
        jumpGrowingHorizonConstant p x * |α| *
          projectedJumpTransitLogBound p x.2 ε ∧
      |(rescaledFullLoopOrbit p α x n).2 -
        (((projectedJumpMap p)^[n]) x).2| ≤
        jumpGrowingHorizonConstant p x * |α| *
          projectedJumpTransitLogBound p x.2 ε := by
  rw [rescaledFullLoopOrbit_eq_scaledLoopOrbit model hgain hα hx n]
  exact scaledLoopOrbit_error_le_logTransit
    model hgain hx hxE hε hεE α hn

/-- At the projected stopping horizon, the exact rescaled excess is within the
same growing-horizon error of the requested tolerance. -/
theorem rescaledFullLoopOrbit_excess_at_transitHorizon_le
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β₀ E₀ ε α : ℝ}
    (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1)
    (hE₀ : 0 < E₀) (hε : 0 < ε) (hεE₀ : ε ≤ E₀)
    (hα : α ≠ 0) :
    |(rescaledFullLoopOrbit p α (β₀, E₀)
        (projectedJumpTransitHorizon p E₀ ε)).2| ≤
      ε + jumpGrowingHorizonConstant p (β₀, E₀) * |α| *
        projectedJumpTransitLogBound p E₀ ε := by
  let H := projectedJumpTransitHorizon p E₀ ε
  let exactE := (rescaledFullLoopOrbit p α (β₀, E₀) H).2
  let jumpE := (((projectedJumpMap p)^[H]) (β₀, E₀)).2
  have herror := (rescaledFullLoopOrbit_error_le_logTransit
    model hgain (x := (β₀, E₀)) hβ₀ hE₀ hε hεE₀ hα
      (n := H) le_rfl).2
  have hjump := projectedJumpOrbit_excess_at_transitHorizon_le
    model hgain hβ₀ hE₀ hε hεE₀
  have htriangle : |exactE| ≤ |exactE - jumpE| + |jumpE| := by
    calc
      |exactE| = |(exactE - jumpE) + jumpE| := by
        congr 1
        ring
      _ ≤ |exactE - jumpE| + |jumpE| := abs_add_le _ _
  exact htriangle.trans (add_le_add herror hjump) |>.trans_eq (add_comm _ _)

/-- A concrete joint-limit range: if the growing-horizon error budget is at
most the tolerance, then the exact rescaled excess is at most twice that
tolerance when the projected orbit reaches it. -/
theorem rescaledFullLoopOrbit_excess_at_transitHorizon_le_two_mul
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β₀ E₀ ε α : ℝ}
    (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1)
    (hE₀ : 0 < E₀) (hε : 0 < ε) (hεE₀ : ε ≤ E₀)
    (hα : α ≠ 0)
    (hjoint :
      jumpGrowingHorizonConstant p (β₀, E₀) * |α| *
        projectedJumpTransitLogBound p E₀ ε ≤ ε) :
    |(rescaledFullLoopOrbit p α (β₀, E₀)
        (projectedJumpTransitHorizon p E₀ ε)).2| ≤ 2 * ε := by
  have h := rescaledFullLoopOrbit_excess_at_transitHorizon_le
    model hgain hβ₀ hE₀ hε hεE₀ hα
  linarith

/-- Exact stopping consequence.  Run the projected orbit to half the target
tolerance.  On the displayed joint `(alpha, epsilon)` range, the rescaled
original orbit has entered the target tolerance by that same time. -/
theorem rescaledFullLoopOrbit_excess_lt_at_halfToleranceHorizon
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β₀ E₀ ε α : ℝ}
    (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1)
    (hE₀ : 0 < E₀) (hε : 0 < ε) (hεE₀ : ε ≤ E₀)
    (hα : α ≠ 0)
    (hjoint :
      jumpGrowingHorizonConstant p (β₀, E₀) * |α| *
        projectedJumpTransitLogBound p E₀ (ε / 2) < ε / 2) :
    |(rescaledFullLoopOrbit p α (β₀, E₀)
        (projectedJumpTransitHorizon p E₀ (ε / 2))).2| < ε := by
  have hhalfPos : 0 < ε / 2 := half_pos hε
  have hhalfLe : ε / 2 ≤ E₀ := by linarith
  have h := rescaledFullLoopOrbit_excess_at_transitHorizon_le
    model hgain hβ₀ hE₀ hhalfPos hhalfLe hα
  linarith

#print axioms scaledLoopMap_projectedJumpMap_refined_error_le
#print axioms scaledLoopMap_projectedJumpMap_weighted_error_le
#print axioms scaledLoopOrbit_error_le_linearHorizon
#print axioms rescaledFullLoopOrbit_error_le_linearHorizon
#print axioms projectedJumpOrbit_excess_at_transitHorizon_le
#print axioms scaledLoopOrbit_error_le_logTransit
#print axioms rescaledFullLoopOrbit_error_le_logTransit
#print axioms rescaledFullLoopOrbit_excess_at_transitHorizon_le_two_mul
#print axioms rescaledFullLoopOrbit_excess_lt_at_halfToleranceHorizon

end

end CivicAlignment.PaperIII
