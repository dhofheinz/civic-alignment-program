/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.Trap
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Paper III: quantitative fixed-horizon jump approximation

`thm:jump` states convergence to the projected jump map at every fixed finite
horizon.  Its proof also says that the finite-horizon error is `O(α)`.  This
file makes that rate literal: an explicit affine-geometric constant bounds both
rescaled coordinates at every rate.  No differentiability of the policy clip
is needed; its `1`-Lipschitz property is the decisive estimate.
-/

namespace CivicAlignment.PaperIII

open Asymptotics Filter Function Set Topology

noncomputable section

/-! ## Uniform primitive bounds -/

/-- The policy-free upper bound for the stationary characteristic. -/
def jumpStationaryBound (p : LoopParams) : ℝ :=
  p.I / (p.lambda₀ - p.g)

/-- A uniform bound for `|G_g|` on the policy interval. -/
def jumpGradientBound (p : LoopParams) : ℝ :=
  p.v + 2 * p.c * jumpStationaryBound p

/-- One-step amplification used by the fixed-horizon error recurrence. -/
def jumpErrorGrowth (p : LoopParams) (x : LoopState) : ℝ :=
  2 + 2 * p.c +
    (2 * p.c ^ 2 + 2 * p.η * (1 - p.lambda₀)) * |x.2|

/-- The rate-linear forcing in the fixed-horizon error recurrence. -/
def jumpErrorForcing (p : LoopParams) : ℝ :=
  jumpGradientBound p + jumpStationaryBound p

/-- The explicit error constant after `n` steps. -/
def jumpFixedHorizonError (p : LoopParams) (x : LoopState) (n : ℕ) : ℝ :=
  arithGeom (jumpErrorGrowth p x) (jumpErrorForcing p) 0 n

/-- The policy-free stationary bound is strictly positive. -/
theorem jumpStationaryBound_pos {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀) :
    0 < jumpStationaryBound p := by
  exact div_pos model.I_pos (sub_pos.mpr hgain)

/-- The stationary characteristic lies between zero and its policy-free bound. -/
theorem stationaryStock_mem_jumpStationaryBound {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    p.stationaryStock β ∈ Icc 0 (jumpStationaryBound p) := by
  exact ⟨(div_pos model.I_pos (zoneDenominator_pos model hgain hβ)).le,
    stationaryStock_le_policyFreeBound model hgain hβ⟩

/-- Two stationary-stock values on the policy interval differ by at most the
policy-free bound. -/
theorem abs_stationaryStock_sub_le_jumpStationaryBound {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {β₁ β₂ : ℝ} (hβ₁ : β₁ ∈ Icc (0 : ℝ) 1)
    (hβ₂ : β₂ ∈ Icc (0 : ℝ) 1) :
    |p.stationaryStock β₁ - p.stationaryStock β₂| ≤
      jumpStationaryBound p := by
  have h₁ := stationaryStock_mem_jumpStationaryBound model hgain hβ₁
  have h₂ := stationaryStock_mem_jumpStationaryBound model hgain hβ₂
  rcases h₁ with ⟨h₁lo, h₁hi⟩
  rcases h₂ with ⟨h₂lo, h₂hi⟩
  rw [abs_le]
  constructor <;> linarith

/-- The stationary gradient has the displayed uniform absolute bound. -/
theorem abs_G_le_jumpGradientBound {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    |p.G β| ≤ jumpGradientBound p := by
  have hD := stationaryStock_mem_jumpStationaryBound model hgain hβ
  have hA := jumpGain_nonneg_le model hβ
  have hprod : 0 ≤ jumpGain p β * p.stationaryStock β :=
    mul_nonneg hA.1 hD.1
  have hprodUpper :
      jumpGain p β * p.stationaryStock β ≤
        2 * p.c * jumpStationaryBound p := by
    calc
      jumpGain p β * p.stationaryStock β ≤
          (2 * p.c) * p.stationaryStock β :=
        mul_le_mul_of_nonneg_right hA.2 hD.1
      _ ≤ (2 * p.c) * jumpStationaryBound p :=
        mul_le_mul_of_nonneg_left hD.2
          (mul_nonneg (by norm_num) model.c_pos.le)
  have hG : p.G β = -p.v + jumpGain p β * p.stationaryStock β := by
    simp only [LoopParams.G, LoopParams.stationaryStock, jumpGain]
    ring
  rw [hG, abs_le]
  constructor
  · dsimp only [jumpGradientBound]
    nlinarith [model.v_pos, jumpStationaryBound_pos model hgain]
  · dsimp only [jumpGradientBound]
    nlinarith [model.v_pos]

/-- Persistence has absolute value at most one on the policy interval. -/
theorem abs_jumpPersistence_le_one {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    |jumpPersistence p β| ≤ 1 := by
  have hs := stockMultiplier_nonneg_le model hβ
  have hσnonneg : 0 ≤ jumpPersistence p β := by
    simp only [jumpPersistence]
    exact add_nonneg hs.1 model.g_nonneg
  have hσle : jumpPersistence p β ≤ 1 := by
    simp only [jumpPersistence]
    linarith
  simpa only [abs_of_nonneg hσnonneg] using hσle

/-- The jump gain has absolute value at most `2c` on the policy interval. -/
theorem abs_jumpGain_le_two_c {p : LoopParams}
    (model : LoopModelAssumptions p) {β : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) :
    |jumpGain p β| ≤ 2 * p.c := by
  have hA := jumpGain_nonneg_le model hβ
  simpa only [abs_of_nonneg hA.1] using hA.2

/-- Exact Lipschitz constant of the affine jump gain. -/
theorem abs_jumpGain_sub (p : LoopParams) (β₁ β₂ : ℝ) :
    |jumpGain p β₁ - jumpGain p β₂| =
      2 * p.c ^ 2 * |β₁ - β₂| := by
  have hidentity : jumpGain p β₁ - jumpGain p β₂ =
      -(2 * p.c ^ 2) * (β₁ - β₂) := by
    simp only [jumpGain]
    ring
  rw [hidentity, abs_mul, abs_neg, abs_of_nonneg (by positivity)]

/-- The stock multiplier, hence persistence, is uniformly Lipschitz on the
policy interval. -/
theorem abs_jumpPersistence_sub_le {p : LoopParams}
    (model : LoopModelAssumptions p) {β₁ β₂ : ℝ}
    (hβ₁ : β₁ ∈ Icc (0 : ℝ) 1) (hβ₂ : β₂ ∈ Icc (0 : ℝ) 1) :
    |jumpPersistence p β₁ - jumpPersistence p β₂| ≤
      2 * p.η * (1 - p.lambda₀) * |β₁ - β₂| := by
  have hk : 0 ≤ 2 * p.η * (1 - p.lambda₀) := by
    exact mul_nonneg (mul_nonneg (by norm_num) model.η_pos.le)
      (sub_nonneg.mpr model.lambda₀_lt_one.le)
  rcases le_total β₁ β₂ with hβ | hβ
  · have hsmono := (stockMultiplier_strictMonoOn model).monotoneOn hβ₁ hβ₂ hβ
    have hslope := stockMultiplier_sub_le model hβ₁ hβ₂ hβ
    simp only [jumpPersistence, add_sub_add_right_eq_sub]
    rw [abs_of_nonpos (sub_nonpos.mpr hsmono),
      abs_of_nonpos (sub_nonpos.mpr hβ)]
    simpa only [neg_sub] using hslope
  · have hsmono := (stockMultiplier_strictMonoOn model).monotoneOn hβ₂ hβ₁ hβ
    have hslope := stockMultiplier_sub_le model hβ₂ hβ₁ hβ
    simp only [jumpPersistence, add_sub_add_right_eq_sub]
    rw [abs_of_nonneg (sub_nonneg.mpr hsmono),
      abs_of_nonneg (sub_nonneg.mpr hβ)]
    exact hslope

/-! ## Projected-orbit bounds -/

/-- Along a projected jump orbit, excess magnitude never exceeds its initial
magnitude, without a sign restriction on the initial excess. -/
theorem projectedJumpOrbit_excess_abs_le_initial {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {x : LoopState} (hx : x.1 ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    |(((projectedJumpMap p)^[n]) x).2| ≤ |x.2| := by
  induction n with
  | zero => simp only [iterate_zero_apply, le_refl]
  | succ n ih =>
      rw [iterate_succ_apply']
      simp only [projectedJumpMap, abs_mul]
      have hβ := projectedJumpMap_iterate_policy_mem (p := p) hx n
      calc
        |jumpPersistence p (((projectedJumpMap p)^[n]) x).1| *
              |(((projectedJumpMap p)^[n]) x).2| ≤
            1 * |(((projectedJumpMap p)^[n]) x).2| :=
          mul_le_mul_of_nonneg_right
            (abs_jumpPersistence_le_one model hgain hβ) (abs_nonneg _)
        _ ≤ 1 * |x.2| := mul_le_mul_of_nonneg_left ih zero_le_one
        _ = |x.2| := one_mul _

/-- The fixed-horizon error constants are nonnegative. -/
theorem jumpFixedHorizonError_nonneg {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (x : LoopState) (n : ℕ) :
    0 ≤ jumpFixedHorizonError p x n := by
  have hgrowth : 0 ≤ jumpErrorGrowth p x := by
    dsimp only [jumpErrorGrowth]
    have hcoefficient :
        0 ≤ 2 * p.c ^ 2 + 2 * p.η * (1 - p.lambda₀) := by
      exact add_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg p.c))
        (mul_nonneg (mul_nonneg (by norm_num) model.η_pos.le)
          (sub_nonneg.mpr model.lambda₀_lt_one.le))
    exact add_nonneg
      (add_nonneg (by norm_num) (mul_nonneg (by norm_num) model.c_pos.le))
      (mul_nonneg hcoefficient (abs_nonneg x.2))
  have hforcing : 0 ≤ jumpErrorForcing p := by
    have hbound := (jumpStationaryBound_pos model hgain).le
    dsimp only [jumpErrorForcing, jumpGradientBound]
    exact add_nonneg
      (add_nonneg model.v_pos.le
        (mul_nonneg (mul_nonneg (by norm_num) model.c_pos.le) hbound))
      hbound
  induction n with
  | zero => simp [jumpFixedHorizonError]
  | succ n ih =>
      rw [jumpFixedHorizonError, arithGeom_succ]
      exact add_nonneg (mul_nonneg hgrowth ih) hforcing

/-! ## Coordinatewise finite-horizon rate -/

/-- One rescaled step and one limiting step preserve a common coordinatewise
`C|α|` error bound, with the displayed affine update of `C`. -/
theorem scaledLoopMap_projectedJumpMap_error_le
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {x z y : LoopState} {C α : ℝ}
    (hz : z.1 ∈ Icc (0 : ℝ) 1) (hy : y.1 ∈ Icc (0 : ℝ) 1)
    (hyexcess : |y.2| ≤ |x.2|) (hC : 0 ≤ C)
    (hpolicy : |z.1 - y.1| ≤ C * |α|)
    (hexcess : |z.2 - y.2| ≤ C * |α|) :
    |(scaledLoopMap p α z).1 - (projectedJumpMap p y).1| ≤
        (jumpErrorGrowth p x * C + jumpErrorForcing p) * |α| ∧
      |(scaledLoopMap p α z).2 - (projectedJumpMap p y).2| ≤
        (jumpErrorGrowth p x * C + jumpErrorForcing p) * |α| := by
  have hc : 0 ≤ 2 * p.c := mul_nonneg (by norm_num) model.c_pos.le
  have hcSq : 0 ≤ 2 * p.c ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg p.c)
  have hk : 0 ≤ 2 * p.η * (1 - p.lambda₀) :=
    mul_nonneg (mul_nonneg (by norm_num) model.η_pos.le)
      (sub_nonneg.mpr model.lambda₀_lt_one.le)
  have hrate : 0 ≤ |α| := abs_nonneg α
  have hCRate : 0 ≤ C * |α| := mul_nonneg hC hrate
  have hbound : 0 ≤ jumpStationaryBound p :=
    (jumpStationaryBound_pos model hgain).le
  have hgradient : 0 ≤ jumpGradientBound p := by
    dsimp only [jumpGradientBound]
    exact add_nonneg model.v_pos.le (mul_nonneg hc hbound)
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
        (2 * p.c) * (C * |α|) := by
    calc
      |jumpGain p z.1| * |z.2 - y.2| ≤
          (2 * p.c) * |z.2 - y.2| :=
        mul_le_mul_of_nonneg_right (abs_jumpGain_le_two_c model hz)
          (abs_nonneg _)
      _ ≤ (2 * p.c) * (C * |α|) :=
        mul_le_mul_of_nonneg_left hexcess hc
  have hgainDifference :
      |jumpGain p z.1 - jumpGain p y.1| ≤
        (2 * p.c ^ 2) * (C * |α|) := by
    rw [abs_jumpGain_sub]
    exact mul_le_mul_of_nonneg_left hpolicy hcSq
  have hgainDifferenceTerm :
      |jumpGain p z.1 - jumpGain p y.1| * |y.2| ≤
        ((2 * p.c ^ 2) * (C * |α|)) * |x.2| := by
    calc
      |jumpGain p z.1 - jumpGain p y.1| * |y.2| ≤
          ((2 * p.c ^ 2) * (C * |α|)) * |y.2| :=
        mul_le_mul_of_nonneg_right hgainDifference (abs_nonneg _)
      _ ≤ ((2 * p.c ^ 2) * (C * |α|)) * |x.2| :=
        mul_le_mul_of_nonneg_left hyexcess (mul_nonneg hcSq hCRate)
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
        C * |α| + (2 * p.c) * (C * |α|) +
          ((2 * p.c ^ 2) * (C * |α|)) * |x.2| +
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
      _ ≤ C * |α| + (2 * p.c) * (C * |α|) +
          ((2 * p.c ^ 2) * (C * |α|)) * |x.2| +
            |α| * jumpGradientBound p :=
        add_le_add (add_le_add (add_le_add hpolicy hgainTerm)
          hgainDifferenceTerm) hgradientTerm
  have hpolicyCoarse :
      |(scaledLoopMap p α z).1 - (projectedJumpMap p y).1| ≤
        C * |α| + (2 * p.c) * (C * |α|) +
          ((2 * p.c ^ 2) * (C * |α|)) * |x.2| +
            |α| * jumpGradientBound p := by
    exact (clipUnit_dist_le
      (z.1 + jumpGain p z.1 * z.2 + α * p.G z.1)
      (y.1 + jumpGain p y.1 * y.2)).trans hpolicyInput
  have hpolicyPadding :
      0 ≤ C * |α| +
        (2 * p.η * (1 - p.lambda₀) * (C * |α|)) * |x.2| +
          jumpStationaryBound p * |α| := by
    positivity
  have hpolicyAccounting :
      (jumpErrorGrowth p x * C + jumpErrorForcing p) * |α| =
        (C * |α| + (2 * p.c) * (C * |α|) +
          ((2 * p.c ^ 2) * (C * |α|)) * |x.2| +
            |α| * jumpGradientBound p) +
        (C * |α| +
          (2 * p.η * (1 - p.lambda₀) * (C * |α|)) * |x.2| +
            jumpStationaryBound p * |α|) := by
    simp only [jumpErrorGrowth, jumpErrorForcing]
    ring
  have hpolicyFinal :
      |(scaledLoopMap p α z).1 - (projectedJumpMap p y).1| ≤
        (jumpErrorGrowth p x * C + jumpErrorForcing p) * |α| := by
    rw [hpolicyAccounting]
    exact hpolicyCoarse.trans (le_add_of_nonneg_right hpolicyPadding)
  have hpersistenceTerm :
      |jumpPersistence p z.1| * |z.2 - y.2| ≤ C * |α| := by
    calc
      |jumpPersistence p z.1| * |z.2 - y.2| ≤
          1 * |z.2 - y.2| :=
        mul_le_mul_of_nonneg_right
          (abs_jumpPersistence_le_one model hgain hz) (abs_nonneg _)
      _ ≤ C * |α| := by simpa only [one_mul] using hexcess
  have hpersistenceDifference :
      |jumpPersistence p z.1 - jumpPersistence p y.1| ≤
        (2 * p.η * (1 - p.lambda₀)) * (C * |α|) := by
    exact (abs_jumpPersistence_sub_le model hz hy).trans
      (mul_le_mul_of_nonneg_left hpolicy hk)
  have hpersistenceDifferenceTerm :
      |jumpPersistence p z.1 - jumpPersistence p y.1| * |y.2| ≤
        ((2 * p.η * (1 - p.lambda₀)) * (C * |α|)) * |x.2| := by
    calc
      |jumpPersistence p z.1 - jumpPersistence p y.1| * |y.2| ≤
          ((2 * p.η * (1 - p.lambda₀)) * (C * |α|)) * |y.2| :=
        mul_le_mul_of_nonneg_right hpersistenceDifference (abs_nonneg _)
      _ ≤ ((2 * p.η * (1 - p.lambda₀)) * (C * |α|)) * |x.2| :=
        mul_le_mul_of_nonneg_left hyexcess (mul_nonneg hk hCRate)
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
  have hexcessCoarse :
      |(scaledLoopMap p α z).2 - (projectedJumpMap p y).2| ≤
        C * |α| +
          ((2 * p.η * (1 - p.lambda₀)) * (C * |α|)) * |x.2| +
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
      _ ≤ C * |α| +
          ((2 * p.η * (1 - p.lambda₀)) * (C * |α|)) * |x.2| +
            |α| * jumpStationaryBound p := by
        simpa only [add_zero, abs_zero] using
          add_le_add (add_le_add hpersistenceTerm hpersistenceDifferenceTerm)
            hstockDifferenceTerm
  have hexcessPadding :
      0 ≤ C * |α| + (2 * p.c) * (C * |α|) +
        ((2 * p.c ^ 2) * (C * |α|)) * |x.2| +
          jumpGradientBound p * |α| := by
    positivity
  have hexcessAccounting :
      (jumpErrorGrowth p x * C + jumpErrorForcing p) * |α| =
        (C * |α| +
          ((2 * p.η * (1 - p.lambda₀)) * (C * |α|)) * |x.2| +
            |α| * jumpStationaryBound p) +
        (C * |α| + (2 * p.c) * (C * |α|) +
          ((2 * p.c ^ 2) * (C * |α|)) * |x.2| +
            jumpGradientBound p * |α|) := by
    simp only [jumpErrorGrowth, jumpErrorForcing]
    ring
  refine ⟨hpolicyFinal, ?_⟩
  rw [hexcessAccounting]
  exact hexcessCoarse.trans (le_add_of_nonneg_right hexcessPadding)

/--
Paper III, Theorem 7.1 (`thm:jump`), quantitative fixed-horizon clause,
`civic_loops.tex:463--533`.

Both rescaled coordinates differ from the projected jump orbit by at most an
explicit constant times `|α|` at every fixed finite horizon.
-/
theorem scaledLoopOrbit_error_le_fixedHorizon
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {x : LoopState}
    (hx : x.1 ∈ Icc (0 : ℝ) 1) (n : ℕ) (α : ℝ) :
    |(((scaledLoopMap p α)^[n]) x).1 -
        (((projectedJumpMap p)^[n]) x).1| ≤
        jumpFixedHorizonError p x n * |α| ∧
      |(((scaledLoopMap p α)^[n]) x).2 -
        (((projectedJumpMap p)^[n]) x).2| ≤
        jumpFixedHorizonError p x n * |α| := by
  induction n with
  | zero => simp [jumpFixedHorizonError]
  | succ n ih =>
      have hstep := scaledLoopMap_projectedJumpMap_error_le model hgain
        (x := x)
        (z := ((scaledLoopMap p α)^[n]) x)
        (y := ((projectedJumpMap p)^[n]) x)
        (C := jumpFixedHorizonError p x n) (α := α)
        (scaledLoopMap_iterate_policy_mem (p := p) (α := α) hx n)
        (projectedJumpMap_iterate_policy_mem (p := p) hx n)
        (projectedJumpOrbit_excess_abs_le_initial model hgain hx n)
        (jumpFixedHorizonError_nonneg model hgain x n) ih.1 ih.2
      simpa only [iterate_succ_apply', jumpFixedHorizonError,
        arithGeom_succ] using hstep

/-- The fixed-horizon rescaled-map error is literally `O(α)` at zero. -/
theorem scaledLoopOrbit_sub_isBigO_fixedHorizon
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {x : LoopState}
    (hx : x.1 ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    (fun α : ℝ ↦ ((scaledLoopMap p α)^[n]) x -
        ((projectedJumpMap p)^[n]) x) =O[nhds 0] (fun α : ℝ ↦ α) := by
  refine IsBigO.of_bound (jumpFixedHorizonError p x n) ?_
  filter_upwards [] with α
  have h := scaledLoopOrbit_error_le_fixedHorizon model hgain hx n α
  rw [Prod.norm_def, Real.norm_eq_abs]
  change max
    |(((scaledLoopMap p α)^[n]) x).1 - (((projectedJumpMap p)^[n]) x).1|
    |(((scaledLoopMap p α)^[n]) x).2 - (((projectedJumpMap p)^[n]) x).2| ≤
      jumpFixedHorizonError p x n * |α|
  exact max_le h.1 h.2

/-- The original full-loop orbit has the same `O(α)` rate on the positive-rate
side after applying the paper's excess-stock rescaling. -/
theorem rescaledFullLoopOrbit_sub_isBigO_fixedHorizon
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {x : LoopState}
    (hx : x.1 ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    (fun α : ℝ ↦ rescaledFullLoopOrbit p α x n -
        ((projectedJumpMap p)^[n]) x) =O[nhdsWithin 0 (Ioi 0)]
      (fun α : ℝ ↦ α) := by
  refine IsBigO.of_bound (jumpFixedHorizonError p x n) ?_
  filter_upwards [self_mem_nhdsWithin] with α hα
  rw [rescaledFullLoopOrbit_eq_scaledLoopOrbit model hgain hα.ne' hx n]
  have h := scaledLoopOrbit_error_le_fixedHorizon model hgain hx n α
  rw [Prod.norm_def, Real.norm_eq_abs]
  change max
    |(((scaledLoopMap p α)^[n]) x).1 - (((projectedJumpMap p)^[n]) x).1|
    |(((scaledLoopMap p α)^[n]) x).2 - (((projectedJumpMap p)^[n]) x).2| ≤
      jumpFixedHorizonError p x n * |α|
  exact max_le h.1 h.2

#print axioms jumpStationaryBound_pos
#print axioms stationaryStock_mem_jumpStationaryBound
#print axioms abs_stationaryStock_sub_le_jumpStationaryBound
#print axioms abs_G_le_jumpGradientBound
#print axioms abs_jumpPersistence_le_one
#print axioms abs_jumpGain_le_two_c
#print axioms abs_jumpGain_sub
#print axioms abs_jumpPersistence_sub_le
#print axioms projectedJumpOrbit_excess_abs_le_initial
#print axioms jumpFixedHorizonError_nonneg
#print axioms scaledLoopMap_projectedJumpMap_error_le
#print axioms scaledLoopOrbit_error_le_fixedHorizon
#print axioms scaledLoopOrbit_sub_isBigO_fixedHorizon
#print axioms rescaledFullLoopOrbit_sub_isBigO_fixedHorizon

end

end CivicAlignment.PaperIII
