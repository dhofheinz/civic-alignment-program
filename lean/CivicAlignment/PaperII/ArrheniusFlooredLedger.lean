/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.ArrheniusFunnel

/-!
# Paper II: the last-exit ledger with a floored running maximum

At a last exit from the calibrated home rectangle, the restart satisfies
`beta_0 <= beta_out` and `D_0 <= D*(beta_out)`, not necessarily
`D_0 <= D*(beta_0)`.  The correct stock comparison therefore evaluates the
stationary characteristic at a running maximum floored at `beta_out`.  This
file re-runs the capped-maximum action ledger with that floor and proves
the resulting localized barrier bound.
-/

namespace CivicAlignment.PaperII

open Set
open scoped BigOperators Interval

noncomputable section

/-! ## Floored running maxima -/

/-- Policy running maximum with an externally supplied lower floor. -/
def flooredPolicyRunningMax (floor : ℝ) (x : ℕ → LoopState) (n : ℕ) : ℝ :=
  max floor (policyRunningMax x n)

/-- A floored running maximum capped at the weighted saddle. -/
def flooredCappedPolicyRunningMax (floor cap : ℝ)
    (x : ℕ → LoopState) (n : ℕ) : ℝ :=
  min cap (flooredPolicyRunningMax floor x n)

/-- A floored policy maximum is monotone in time. -/
theorem monotone_flooredPolicyRunningMax (floor : ℝ)
    (x : ℕ → LoopState) :
    Monotone (flooredPolicyRunningMax floor x) := by
  intro m n hmn
  exact max_le_max_left floor ((monotone_runningMax
    fun k ↦ (x k).1) hmn)

/-- A floored-and-capped policy maximum is monotone in time. -/
theorem monotone_flooredCappedPolicyRunningMax (floor cap : ℝ)
    (x : ℕ → LoopState) :
    Monotone (flooredCappedPolicyRunningMax floor cap x) := by
  intro m n hmn
  exact min_le_min_left cap
    (monotone_flooredPolicyRunningMax floor x hmn)

/-- Current policy is below every floored running maximum. -/
theorem policy_le_flooredPolicyRunningMax (floor : ℝ)
    (x : ℕ → LoopState) (n : ℕ) :
    (x n).1 ≤ flooredPolicyRunningMax floor x n :=
  (policy_le_runningMax x n).trans (le_max_right _ _)

/-- If the initial policy is below the floor, the initial floored maximum is
exactly that floor. -/
theorem IsControlledCivicWeightedPathFrom.flooredRunningMax_zero
    {p : LoopParams} {rho floor : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hstart : x₀.1 ≤ floor) :
    flooredPolicyRunningMax floor x 0 = floor := by
  simp only [flooredPolicyRunningMax, policyRunningMax, runningMax]
  rw [path.initial]
  exact max_eq_left hstart

/-- With the floor and all policies in `[0,1]`, so is the floored maximum. -/
theorem IsControlledCivicWeightedPathFrom.flooredRunningMax_mem
    {p : LoopParams} {rho floor : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hfloor : floor ∈ Icc (0 : ℝ) 1)
    (n : ℕ) : flooredPolicyRunningMax floor x n ∈ Icc (0 : ℝ) 1 := by
  have hrun := path.runningMax_mem hx₀ n
  exact ⟨le_max_of_le_left hfloor.1, max_le hfloor.2 hrun.2⟩

/-- A floored-and-capped maximum lies on the localized barrier segment. -/
theorem IsControlledCivicWeightedPathFrom.flooredCappedRunningMax_mem
    {p : LoopParams} {rho floor : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1)
    (hfloor : floor ∈ Icc (0 : ℝ) weighted.βdagger) (n : ℕ) :
    flooredCappedPolicyRunningMax floor weighted.βdagger x n ∈
      Icc floor weighted.βdagger := by
  have hfloorUnit : floor ∈ Icc (0 : ℝ) 1 :=
    ⟨hfloor.1, hfloor.2.trans weighted.βdagger_mem.2.le⟩
  have hrun := path.flooredRunningMax_mem hx₀ hfloorUnit n
  exact ⟨le_min hfloor.2 (le_max_left _ _), min_le_left _ _⟩

/-- The localized stopped maximum starts at the floor. -/
theorem IsControlledCivicWeightedPathFrom.flooredCappedRunningMax_zero
    {p : LoopParams} {rho floor : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hfloor : floor ≤ weighted.βdagger) (hstart : x₀.1 ≤ floor) :
    flooredCappedPolicyRunningMax floor weighted.βdagger x 0 = floor := by
  rw [flooredCappedPolicyRunningMax,
    path.flooredRunningMax_zero hstart]
  exact min_eq_right hfloor

/-- Reaching the saddle in the ordinary running maximum makes the localized
stopped maximum equal the saddle. -/
theorem flooredCappedRunningMax_eq_target
    {floor cap : ℝ} {x : ℕ → LoopState} {N : ℕ}
    (hreach : cap ≤ policyRunningMax x N) :
    flooredCappedPolicyRunningMax floor cap x N = cap := by
  exact min_eq_left (hreach.trans (le_max_right _ _))

/-- Successive localized stopped-maximum increments are nonnegative. -/
theorem flooredCappedRunningMax_increment_nonneg
    (floor cap : ℝ) (x : ℕ → LoopState) (n : ℕ) :
    0 ≤ flooredCappedPolicyRunningMax floor cap x (n + 1) -
      flooredCappedPolicyRunningMax floor cap x n :=
  sub_nonneg.mpr
    (monotone_flooredCappedPolicyRunningMax floor cap x n.le_succ)

/-- On an advancing localized-maximum step, the old stopped value is the old
floored maximum, dominates current policy, and the new stopped value is no
larger than the new policy. -/
theorem flooredCappedRunningMax_advance_structure
    {floor cap : ℝ} {x : ℕ → LoopState} {n : ℕ}
    (hadvance : flooredCappedPolicyRunningMax floor cap x n <
      flooredCappedPolicyRunningMax floor cap x (n + 1)) :
    flooredCappedPolicyRunningMax floor cap x n =
        flooredPolicyRunningMax floor x n ∧
      (x n).1 ≤ flooredCappedPolicyRunningMax floor cap x n ∧
      flooredCappedPolicyRunningMax floor cap x (n + 1) ≤ (x (n + 1)).1 := by
  let m := flooredPolicyRunningMax floor x n
  let m' := flooredPolicyRunningMax floor x (n + 1)
  have hnewLeCap : flooredCappedPolicyRunningMax floor cap x (n + 1) ≤ cap :=
    min_le_left _ _
  have holdLtCap : flooredCappedPolicyRunningMax floor cap x n < cap :=
    hadvance.trans_le hnewLeCap
  have hmLtCap : m < cap := by
    by_contra hnot
    have hcap : cap ≤ m := not_lt.mp hnot
    rw [flooredCappedPolicyRunningMax, min_eq_left hcap] at holdLtCap
    exact lt_irrefl cap holdLtCap
  have hold : flooredCappedPolicyRunningMax floor cap x n = m :=
    min_eq_right hmLtCap.le
  have hmm' : m < m' := by
    calc
      m = flooredCappedPolicyRunningMax floor cap x n := hold.symm
      _ < flooredCappedPolicyRunningMax floor cap x (n + 1) := hadvance
      _ ≤ m' := min_le_right _ _
  have hmFormula : m' = max m (x (n + 1)).1 := by
    simp only [m, m', flooredPolicyRunningMax, policyRunningMax,
      runningMax_succ, max_assoc]
  have hnext : m < (x (n + 1)).1 := by
    by_contra hnot
    have hle : (x (n + 1)).1 ≤ m := not_lt.mp hnot
    rw [hmFormula, max_eq_left hle] at hmm'
    exact lt_irrefl m hmm'
  have hm'Eq : m' = (x (n + 1)).1 := by
    rw [hmFormula, max_eq_right hnext.le]
  refine ⟨hold, ?_, ?_⟩
  · rw [hold]
    exact policy_le_flooredPolicyRunningMax floor x n
  · exact (min_le_right _ _).trans_eq hm'Eq

/-! ## Stock and gradient bounds at the floored maximum -/

/-- If `D₀ ≤ D*(floor)` and `β₀ ≤ floor`, stock remains below the stationary
characteristic at the floored running maximum. -/
theorem IsControlledCivicWeightedPathFrom.stock_le_stationary_flooredRunningMax
    {p : LoopParams} {rho floor : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p) (hfloor : floor ∈ Icc (0 : ℝ) 1)
    (hstart : x₀.1 ≤ floor)
    (hstock₀ : x₀.2 ≤ p.stationaryStock floor) (n : ℕ) :
    (x n).2 ≤ p.stationaryStock (flooredPolicyRunningMax floor x n) := by
  induction n with
  | zero =>
      rw [path.initial, path.flooredRunningMax_zero hstart]
      exact hstock₀
  | succ n ih =>
      let m := flooredPolicyRunningMax floor x n
      let m' := flooredPolicyRunningMax floor x (n + 1)
      have hm := path.flooredRunningMax_mem hx₀.1 hfloor n
      have hm' := path.flooredRunningMax_mem hx₀.1 hfloor (n + 1)
      have hxmem := path.mem_absorbingBox model hx₀ n
      have hupperMem : (m, p.stationaryStock m) ∈ absorbingBox p :=
        ⟨hm, stationaryStock_mem_stockInterval model hm⟩
      have hxle : x n ≤ (m, p.stationaryStock m) :=
        ⟨policy_le_flooredPolicyRunningMax floor x n, ih⟩
      have hstep := (loopMap_monotoneOn_box model ss hxmem hupperMem hxle).2
      have hfixed := stationaryStock_fixed model hm
      have hstockToM :
          p.stockStep (x n).1 (x n).2 ≤ p.stationaryStock m := by
        calc
          p.stockStep (x n).1 (x n).2 ≤
              p.stockStep m (p.stationaryStock m) := by
            simpa only [LoopParams.loopMap] using hstep
          _ = p.stationaryStock m := hfixed
      have hmm' : m ≤ m' :=
        monotone_flooredPolicyRunningMax floor x n.le_succ
      have hcharacteristic : p.stationaryStock m ≤ p.stationaryStock m' :=
        (stationaryStock_strictMonoOn model).monotoneOn hm hm' hmm'
      rw [path.step n]
      exact hstockToM.trans hcharacteristic

/-- Gradient upper bound evaluated at the floored running maximum. -/
theorem IsControlledCivicWeightedPathFrom.gradient_le_flooredRunningMax
    {p : LoopParams} {rho floor : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p) (hfloor : floor ∈ Icc (0 : ℝ) 1)
    (hstart : x₀.1 ≤ floor)
    (hstock₀ : x₀.2 ≤ p.stationaryStock floor) (n : ℕ) :
    civicWeightedGradient p rho (x n).1 (x n).2 ≤
      weightedStationaryGradient p rho
          (flooredPolicyRunningMax floor x n) +
        2 * p.c ^ 2 *
          p.stationaryStock (flooredPolicyRunningMax floor x n) *
          (flooredPolicyRunningMax floor x n - (x n).1) := by
  let beta := (x n).1
  let D := (x n).2
  let b := flooredPolicyRunningMax floor x n
  have hbeta := path.policy_mem hx₀.1 n
  have hb := path.flooredRunningMax_mem hx₀.1 hfloor n
  have hD := path.stock_le_stationary_flooredRunningMax
    model ss hx₀ hfloor hstart hstock₀ n
  have hcoef := weighted_stock_coefficient_nonnegative model hcoop hbeta
  have hmul :
      (2 * p.c * (1 - p.c * beta) - rho) * D ≤
        (2 * p.c * (1 - p.c * beta) - rho) * p.stationaryStock b :=
    mul_le_mul_of_nonneg_left hD hcoef
  calc
    civicWeightedGradient p rho beta D =
        -p.v + (2 * p.c * (1 - p.c * beta) - rho) * D := by
      simp only [civicWeightedGradient, LoopParams.gradU]
      ring
    _ ≤ -p.v + (2 * p.c * (1 - p.c * beta) - rho) *
        p.stationaryStock b := by linarith
    _ = weightedStationaryGradient p rho b +
        2 * p.c ^ 2 * p.stationaryStock b * (b - beta) := by
      rw [← civicWeightedGradient_stationary_eq_weightedStationaryGradient
        rho hb]
      simp only [civicWeightedGradient, LoopParams.gradU]
      ring

/-! ## Localized per-advance action ledger -/

/-- On each localized-maximum advance, control pays the barrier height plus
the policy advance divided by the adaptation rate. -/
theorem IsControlledCivicWeightedPathFrom.control_ge_flooredBarrier_add_advance
    {p : LoopParams} {rho floor : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hfloor : floor ∈ Icc (0 : ℝ) weighted.βdagger)
    (hstart : x₀.1 ≤ floor)
    (hstock₀ : x₀.2 ≤ p.stationaryStock floor) {n : ℕ}
    (hadvance :
      flooredCappedPolicyRunningMax floor weighted.βdagger x n <
        flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1)) :
    weightedBarrierIntegrand p rho
        (flooredCappedPolicyRunningMax floor weighted.βdagger x n) +
      (flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1) -
        flooredCappedPolicyRunningMax floor weighted.βdagger x n) / p.α ≤
      u n := by
  let b := flooredCappedPolicyRunningMax floor weighted.βdagger x n
  let b' := flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1)
  let beta := (x n).1
  let D := (x n).2
  obtain ⟨hold, hbetaB, hnewPolicy⟩ :=
    flooredCappedRunningMax_advance_structure hadvance
  have hfloorUnit : floor ∈ Icc (0 : ℝ) 1 :=
    ⟨hfloor.1, hfloor.2.trans weighted.βdagger_mem.2.le⟩
  have hbmem : b ∈ Icc (0 : ℝ) 1 := by
    have hbsegment := path.flooredCappedRunningMax_mem
      weighted hx₀.1 hfloor n
    exact ⟨hfloor.1.trans hbsegment.1,
      hbsegment.2.trans weighted.βdagger_mem.2.le⟩
  have hbnonneg : 0 ≤ b := hbmem.1
  have hb'pos : 0 < b' := hbnonneg.trans_lt hadvance
  have hxnextPos : 0 < (x (n + 1)).1 := hb'pos.trans_le hnewPolicy
  have hxnext : (x (n + 1)).1 = LoopParams.clipUnit
      (beta + p.α * (civicWeightedGradient p rho beta D + u n)) := by
    have hstep := congrArg Prod.fst (path.step n)
    simpa only [controlledCivicWeightedStep] using hstep
  have hinput : b' ≤ beta + p.α *
      (civicWeightedGradient p rho beta D + u n) := by
    calc
      b' ≤ (x (n + 1)).1 := hnewPolicy
      _ = LoopParams.clipUnit
          (beta + p.α * (civicWeightedGradient p rho beta D + u n)) := hxnext
      _ ≤ beta + p.α * (civicWeightedGradient p rho beta D + u n) :=
        clipUnit_le_input_of_pos (by rwa [← hxnext])
  have hgradient : civicWeightedGradient p rho beta D ≤
      weightedStationaryGradient p rho b +
        2 * p.c ^ 2 * p.stationaryStock b * (b - beta) := by
    have h := path.gradient_le_flooredRunningMax model ss hcoop hx₀
      hfloorUnit hstart hstock₀ n
    rw [← hold] at h
    exact h
  have hsmall := two_alpha_c_sq_stationaryStock_le_one model ss hbmem
  have hdip : 0 ≤ b - beta := sub_nonneg.mpr hbetaB
  have hdipCoefficient :
      0 ≤ 1 - 2 * p.α * p.c ^ 2 * p.stationaryStock b := by linarith
  have hdipProduct := mul_nonneg hdipCoefficient hdip
  have halphaGradient :=
    mul_le_mul_of_nonneg_left hgradient model.α_pos.le
  have hcross :
      p.α * weightedBarrierIntegrand p rho b + (b' - b) ≤ p.α * u n := by
    simp only [weightedBarrierIntegrand]
    nlinarith
  have hdivide : p.α * ((b' - b) / p.α) = b' - b := by
    field_simp [model.α_pos.ne']
  nlinarith [model.α_pos]

/-- Each advancing localized cell pays its left-rectangle charge. -/
theorem IsControlledCivicWeightedPathFrom.floored_advance_barrier_le_half_control_sq
    {p : LoopParams} {rho floor : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hfloor : floor ∈ Icc (0 : ℝ) weighted.βdagger)
    (hstart : x₀.1 ≤ floor)
    (hstock₀ : x₀.2 ≤ p.stationaryStock floor) {n : ℕ}
    (hadvance :
      flooredCappedPolicyRunningMax floor weighted.βdagger x n <
        flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1)) :
    (2 / p.α) * weightedBarrierIntegrand p rho
        (flooredCappedPolicyRunningMax floor weighted.βdagger x n) *
      (flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1) -
        flooredCappedPolicyRunningMax floor weighted.βdagger x n) ≤
      (u n) ^ 2 / 2 := by
  let b := flooredCappedPolicyRunningMax floor weighted.βdagger x n
  let b' := flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1)
  let a := weightedBarrierIntegrand p rho b
  let d := (b' - b) / p.α
  have hbsegment := path.flooredCappedRunningMax_mem
    weighted hx₀.1 hfloor n
  have hbBelow : b < weighted.βdagger :=
    hadvance.trans_le (min_le_left _ _)
  have ha : 0 < a := weighted.barrier_pos_before
    ⟨hfloor.1.trans hbsegment.1, hbsegment.2⟩ hbBelow
  have hdelta : 0 < b' - b := sub_pos.mpr hadvance
  have hd : 0 < d := div_pos hdelta model.α_pos
  have hu := path.control_ge_flooredBarrier_add_advance
    model ss hcoop weighted hx₀ hfloor hstart hstock₀ hadvance
  have hsum : 0 ≤ a + d := by positivity
  have huNonneg : 0 ≤ u n := hsum.trans hu
  have hproduct : 0 ≤ (u n - (a + d)) * (u n + (a + d)) :=
    mul_nonneg (sub_nonneg.mpr hu) (add_nonneg huNonneg hsum)
  have hsquare := sq_nonneg (a - d)
  have hcore : 2 * a * d ≤ (u n) ^ 2 / 2 := by nlinarith
  calc
    (2 / p.α) * a * (b' - b) = 2 * a * d := by
      simp only [d]
      field_simp [model.α_pos.ne']
    _ ≤ (u n) ^ 2 / 2 := hcore

/-- The localized advance ledger remains valid on nonadvancing steps. -/
theorem IsControlledCivicWeightedPathFrom.floored_barrier_increment_le_half_control_sq
    {p : LoopParams} {rho floor : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hfloor : floor ∈ Icc (0 : ℝ) weighted.βdagger)
    (hstart : x₀.1 ≤ floor)
    (hstock₀ : x₀.2 ≤ p.stationaryStock floor) (n : ℕ) :
    (2 / p.α) * weightedBarrierIntegrand p rho
        (flooredCappedPolicyRunningMax floor weighted.βdagger x n) *
      (flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1) -
        flooredCappedPolicyRunningMax floor weighted.βdagger x n) ≤
      (u n) ^ 2 / 2 := by
  have hmono := monotone_flooredCappedPolicyRunningMax
    floor weighted.βdagger x n.le_succ
  rcases hmono.lt_or_eq with hadvance | heq
  · exact path.floored_advance_barrier_le_half_control_sq
      model ss hcoop weighted hx₀ hfloor hstart hstock₀ hadvance
  · rw [heq]
    simp only [sub_self, mul_zero]
    positivity

/-- Sum of localized left rectangles is bounded by the finite action. -/
theorem IsControlledCivicWeightedPathFrom.sum_floored_barrier_increments_le_action
    {p : LoopParams} {rho floor : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hfloor : floor ∈ Icc (0 : ℝ) weighted.βdagger)
    (hstart : x₀.1 ≤ floor)
    (hstock₀ : x₀.2 ≤ p.stationaryStock floor) (N : ℕ) :
    (2 / p.α) * ∑ n ∈ Finset.range N,
        weightedBarrierIntegrand p rho
            (flooredCappedPolicyRunningMax floor weighted.βdagger x n) *
          (flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1) -
            flooredCappedPolicyRunningMax floor weighted.βdagger x n) ≤
      controlAction u N := by
  rw [Finset.mul_sum]
  have hsum :
      ∑ n ∈ Finset.range N,
          (2 / p.α) *
            (weightedBarrierIntegrand p rho
                (flooredCappedPolicyRunningMax floor weighted.βdagger x n) *
              (flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1) -
                flooredCappedPolicyRunningMax floor weighted.βdagger x n)) ≤
        ∑ n ∈ Finset.range N, (u n) ^ 2 / 2 := by
    exact Finset.sum_le_sum fun n _hn ↦ by
      simpa only [mul_assoc] using
        path.floored_barrier_increment_le_half_control_sq
          model ss hcoop weighted hx₀ hfloor hstart hstock₀ n
  calc
    ∑ n ∈ Finset.range N,
        (2 / p.α) *
          (weightedBarrierIntegrand p rho
              (flooredCappedPolicyRunningMax floor weighted.βdagger x n) *
            (flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1) -
              flooredCappedPolicyRunningMax floor weighted.βdagger x n)) ≤
        ∑ n ∈ Finset.range N, (u n) ^ 2 / 2 := hsum
    _ = controlAction u N := by
      simp only [controlAction, div_eq_mul_inv, Finset.mul_sum]
      ring_nf

/-- Squared increments of the localized stopped maximum are controlled by
squared controls. -/
theorem IsControlledCivicWeightedPathFrom.floored_increment_sq_le_control_sq
    {p : LoopParams} {rho floor : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hfloor : floor ∈ Icc (0 : ℝ) weighted.βdagger)
    (hstart : x₀.1 ≤ floor)
    (hstock₀ : x₀.2 ≤ p.stationaryStock floor) (n : ℕ) :
    (flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1) -
        flooredCappedPolicyRunningMax floor weighted.βdagger x n) ^ 2 ≤
      p.α ^ 2 * (u n) ^ 2 := by
  let b := flooredCappedPolicyRunningMax floor weighted.βdagger x n
  let b' := flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1)
  change (b' - b) ^ 2 ≤ p.α ^ 2 * (u n) ^ 2
  have hmono : b ≤ b' :=
    monotone_flooredCappedPolicyRunningMax
      floor weighted.βdagger x n.le_succ
  rcases hmono.lt_or_eq with hadvance | heq
  · have hbsegment := path.flooredCappedRunningMax_mem
      weighted hx₀.1 hfloor n
    have hbarrier : 0 < weightedBarrierIntegrand p rho b :=
      weighted.barrier_pos_before
        ⟨hfloor.1.trans hbsegment.1, hbsegment.2⟩
        (hadvance.trans_le (min_le_left _ _))
    have hu := path.control_ge_flooredBarrier_add_advance
      model ss hcoop weighted hx₀ hfloor hstart hstock₀ hadvance
    have hdiv : (b' - b) / p.α ≤ u n := by linarith [hbarrier.le]
    have hdelta : b' - b ≤ p.α * u n := by
      have := (div_le_iff₀ model.α_pos).mp hdiv
      simpa only [mul_comm] using this
    have hdeltaNonneg : 0 ≤ b' - b := sub_nonneg.mpr hmono
    have huNonneg : 0 ≤ u n := by
      have hdivPos : 0 < (b' - b) / p.α :=
        div_pos (sub_pos.mpr hadvance) model.α_pos
      linarith
    have halphaUNonneg : 0 ≤ p.α * u n :=
      mul_nonneg model.α_pos.le huNonneg
    have hsquare : (b' - b) ^ 2 ≤ (p.α * u n) ^ 2 :=
      (sq_le_sq₀ hdeltaNonneg halphaUNonneg).2 hdelta
    nlinarith
  · rw [heq]
    simpa only [sub_self, pow_two, zero_mul] using
      mul_nonneg (sq_nonneg p.α) (sq_nonneg (u n))

/-- Sum of squared localized increments is controlled by finite action. -/
theorem IsControlledCivicWeightedPathFrom.sum_floored_increment_sq_le_action
    {p : LoopParams} {rho floor : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hfloor : floor ∈ Icc (0 : ℝ) weighted.βdagger)
    (hstart : x₀.1 ≤ floor)
    (hstock₀ : x₀.2 ≤ p.stationaryStock floor) (N : ℕ) :
    ∑ n ∈ Finset.range N,
        (flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1) -
          flooredCappedPolicyRunningMax floor weighted.βdagger x n) ^ 2 ≤
      2 * p.α ^ 2 * controlAction u N := by
  calc
    ∑ n ∈ Finset.range N,
        (flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1) -
          flooredCappedPolicyRunningMax floor weighted.βdagger x n) ^ 2 ≤
        ∑ n ∈ Finset.range N, p.α ^ 2 * (u n) ^ 2 := by
      exact Finset.sum_le_sum fun n _hn ↦
        path.floored_increment_sq_le_control_sq
          model ss hcoop weighted hx₀ hfloor hstart hstock₀ n
    _ = 2 * p.α ^ 2 * controlAction u N := by
      simp only [controlAction, Finset.mul_sum]
      ring_nf

/-! ## The corrected localized crossing bound -/

/-- A saddle crossing partitions the complete localized barrier interval
`[floor,betaDagger]`. -/
theorem IsControlledCivicWeightedPathFrom.floored_barrier_integral_le_partition
    {p : LoopParams} {rho floor L : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p)
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1)
    (hfloor : floor ∈ Icc (0 : ℝ) weighted.βdagger)
    (hstart : x₀.1 ≤ floor) {N : ℕ}
    (hcross : weighted.βdagger ≤ policyRunningMax x N) :
    (∫ b in floor..weighted.βdagger,
        weightedBarrierIntegrand p rho b) ≤
      (∑ n ∈ Finset.range N,
        weightedBarrierIntegrand p rho
            (flooredCappedPolicyRunningMax floor weighted.βdagger x n) *
          (flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1) -
            flooredCappedPolicyRunningMax floor weighted.βdagger x n)) +
      (L / 2) * ∑ n ∈ Finset.range N,
        (flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1) -
          flooredCappedPolicyRunningMax floor weighted.βdagger x n) ^ 2 := by
  let b : ℕ → ℝ := fun n ↦
    flooredCappedPolicyRunningMax floor weighted.βdagger x n
  let f := weightedBarrierIntegrand p rho
  have hcont : ContinuousOn f (Icc (0 : ℝ) weighted.βdagger) :=
    continuousOn_weightedBarrierIntegrand model rho weighted
  have hbmem : ∀ n, b n ∈ Icc floor weighted.βdagger :=
    fun n ↦ path.flooredCappedRunningMax_mem weighted hx₀ hfloor n
  have hbmemFull : ∀ n, b n ∈ Icc (0 : ℝ) weighted.βdagger :=
    fun n ↦ ⟨hfloor.1.trans (hbmem n).1, (hbmem n).2⟩
  have hbmono : ∀ n, b n ≤ b (n + 1) := fun n ↦
    monotone_flooredCappedPolicyRunningMax
      floor weighted.βdagger x n.le_succ
  have hcellInt : ∀ n < N, IntervalIntegrable f MeasureTheory.volume
      (b n) (b (n + 1)) := by
    intro n _hn
    have hsubset : [[b n, b (n + 1)]] ⊆
        Icc (0 : ℝ) weighted.βdagger := by
      rw [uIcc_of_le (hbmono n)]
      intro z hz
      exact ⟨(hbmemFull n).1.trans hz.1,
        hz.2.trans (hbmemFull (n + 1)).2⟩
    exact (hcont.mono hsubset).intervalIntegrable
  have hadjacent :
      ∑ n ∈ Finset.range N, ∫ z in b n..b (n + 1), f z =
        ∫ z in b 0..b N, f z :=
    intervalIntegral.sum_integral_adjacent_intervals hcellInt
  have hbegin : b 0 = floor :=
    path.flooredCappedRunningMax_zero weighted hfloor.2 hstart
  have hend : b N = weighted.βdagger :=
    flooredCappedRunningMax_eq_target hcross
  have hcells :
      ∑ n ∈ Finset.range N, ∫ z in b n..b (n + 1), f z ≤
        ∑ n ∈ Finset.range N,
          (f (b n) * (b (n + 1) - b n) +
            (L / 2) * (b (n + 1) - b n) ^ 2) := by
    exact Finset.sum_le_sum fun n _hn ↦
      integral_le_left_rectangle_add_lipschitz hcont hL
        (hbmemFull n) (hbmemFull (n + 1)) (hbmono n)
  change (∫ z in floor..weighted.βdagger, f z) ≤ _
  calc
    (∫ z in floor..weighted.βdagger, f z) =
        ∑ n ∈ Finset.range N, ∫ z in b n..b (n + 1), f z := by
      rw [hadjacent, hbegin, hend]
    _ ≤ ∑ n ∈ Finset.range N,
        (f (b n) * (b (n + 1) - b n) +
          (L / 2) * (b (n + 1) - b n) ^ 2) := hcells
    _ = (∑ n ∈ Finset.range N,
        f (b n) * (b (n + 1) - b n)) +
        (L / 2) * ∑ n ∈ Finset.range N,
          (b (n + 1) - b n) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- The last-exit crossing action pays the corrected localized barrier under
exactly the home-rectangle hypotheses `beta_0 ≤ floor` and
`D_0 ≤ D*(floor)`. -/
theorem IsControlledCivicWeightedPathFrom.floored_action_lower_bound_of_crossing
    {p : LoopParams} {rho floor L : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hfloor : floor ∈ Icc (0 : ℝ) weighted.βdagger)
    (hstart : x₀.1 ≤ floor)
    (hstock₀ : x₀.2 ≤ p.stationaryStock floor) {N : ℕ}
    (hcross : weighted.βdagger ≤ policyRunningMax x N) :
    (2 / (p.α * (1 + 2 * p.α * L))) *
        (∫ b in floor..weighted.βdagger,
          weightedBarrierIntegrand p rho b) ≤
      controlAction u N := by
  let R : ℝ := ∑ n ∈ Finset.range N,
    weightedBarrierIntegrand p rho
        (flooredCappedPolicyRunningMax floor weighted.βdagger x n) *
      (flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1) -
        flooredCappedPolicyRunningMax floor weighted.βdagger x n)
  let Q : ℝ := ∑ n ∈ Finset.range N,
    (flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1) -
      flooredCappedPolicyRunningMax floor weighted.βdagger x n) ^ 2
  let A : ℝ := controlAction u N
  let Ibar : ℝ := ∫ b in floor..weighted.βdagger,
    weightedBarrierIntegrand p rho b
  have hpartition : Ibar ≤ R + (L / 2) * Q :=
    path.floored_barrier_integral_le_partition
      model weighted hL hx₀.1 hfloor hstart hcross
  have hRscaled : (2 / p.α) * R ≤ A :=
    path.sum_floored_barrier_increments_le_action
      model ss hcoop weighted hx₀ hfloor hstart hstock₀ N
  have hQ : Q ≤ 2 * p.α ^ 2 * A :=
    path.sum_floored_increment_sq_le_action
      model ss hcoop weighted hx₀ hfloor hstart hstock₀ N
  have hhalfAlpha : 0 ≤ p.α / 2 :=
    div_nonneg model.α_pos.le (by norm_num)
  have hR : R ≤ (p.α / 2) * A := by
    have hmul := mul_le_mul_of_nonneg_left hRscaled hhalfAlpha
    calc
      R = (p.α / 2) * ((2 / p.α) * R) := by
        field_simp [model.α_pos.ne']
      _ ≤ (p.α / 2) * A := hmul
  have hLhalf : 0 ≤ L / 2 := div_nonneg hL.nonneg (by norm_num)
  have hmeshMul := mul_le_mul_of_nonneg_left hQ hLhalf
  have hmesh : (L / 2) * Q ≤ L * p.α ^ 2 * A := by
    calc
      (L / 2) * Q ≤ (L / 2) * (2 * p.α ^ 2 * A) := hmeshMul
      _ = L * p.α ^ 2 * A := by ring
  have hI : Ibar ≤ (p.α / 2) * (1 + 2 * p.α * L) * A := by
    calc
      Ibar ≤ R + (L / 2) * Q := hpartition
      _ ≤ (p.α / 2) * A + L * p.α ^ 2 * A := add_le_add hR hmesh
      _ = (p.α / 2) * (1 + 2 * p.α * L) * A := by ring
  have hcorrectionPos : 0 < 1 + 2 * p.α * L := by
    have hterm : 0 ≤ 2 * p.α * L :=
      mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) hL.nonneg
    linarith
  have hdenPos : 0 < (p.α / 2) * (1 + 2 * p.α * L) :=
    mul_pos (div_pos model.α_pos (by norm_num)) hcorrectionPos
  have hdiv : Ibar / ((p.α / 2) * (1 + 2 * p.α * L)) ≤ A :=
    (div_le_iff₀ hdenPos).2 (by simpa only [mul_comm] using hI)
  change (2 / (p.α * (1 + 2 * p.α * L))) * Ibar ≤ A
  convert hdiv using 1
  field_simp [model.α_pos.ne', hcorrectionPos.ne']

#print axioms monotone_flooredPolicyRunningMax
#print axioms monotone_flooredCappedPolicyRunningMax
#print axioms policy_le_flooredPolicyRunningMax
#print axioms IsControlledCivicWeightedPathFrom.flooredRunningMax_zero
#print axioms IsControlledCivicWeightedPathFrom.flooredRunningMax_mem
#print axioms IsControlledCivicWeightedPathFrom.flooredCappedRunningMax_mem
#print axioms IsControlledCivicWeightedPathFrom.flooredCappedRunningMax_zero
#print axioms flooredCappedRunningMax_eq_target
#print axioms flooredCappedRunningMax_increment_nonneg
#print axioms flooredCappedRunningMax_advance_structure
#print axioms IsControlledCivicWeightedPathFrom.stock_le_stationary_flooredRunningMax
#print axioms IsControlledCivicWeightedPathFrom.gradient_le_flooredRunningMax
#print axioms IsControlledCivicWeightedPathFrom.control_ge_flooredBarrier_add_advance
#print axioms IsControlledCivicWeightedPathFrom.floored_advance_barrier_le_half_control_sq
#print axioms IsControlledCivicWeightedPathFrom.floored_barrier_increment_le_half_control_sq
#print axioms IsControlledCivicWeightedPathFrom.sum_floored_barrier_increments_le_action
#print axioms IsControlledCivicWeightedPathFrom.floored_increment_sq_le_control_sq
#print axioms IsControlledCivicWeightedPathFrom.sum_floored_increment_sq_le_action
#print axioms IsControlledCivicWeightedPathFrom.floored_barrier_integral_le_partition
#print axioms IsControlledCivicWeightedPathFrom.floored_action_lower_bound_of_crossing

end

end CivicAlignment.PaperII
