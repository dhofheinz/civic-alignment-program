/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.Root
import CivicAlignment.PaperII.Hysteresis
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Paper II: controlled escape and quasipotential bounds

This file formalizes the finite-action controlled paths underlying
`prop:qpbounds`.  The stock coordinate remains exact; only the policy gradient
receives a control.  The running-maximum formulation isolates the deterministic
pathwise estimate used again by `prop:arrwindow`.
-/

namespace CivicAlignment.PaperII

open Filter Function Set Topology
open scoped BigOperators Interval

noncomputable section

/-! ## Controlled paths and their action -/

/-- One civic-weighted step with an additive gradient control `u`. -/
def controlledCivicWeightedStep (p : LoopParams) (ρ u : ℝ)
    (x : LoopState) : LoopState :=
  (LoopParams.clipUnit
      (x.1 + p.α * (civicWeightedGradient p ρ x.1 x.2 + u)),
    p.stockStep x.1 x.2)

/-- A controlled path starts at the calibrated corner, modifies only the
policy gradient, and leaves the stock recursion exact. -/
structure IsControlledCivicWeightedPath (p : LoopParams) (ρ : ℝ)
    (u : ℕ → ℝ) (x : ℕ → LoopState) : Prop where
  initial : x 0 = calibratedPoint p
  step : ∀ n, x (n + 1) = controlledCivicWeightedStep p ρ (u n) (x n)

/-- The finite-horizon Freidlin--Wentzell action `1/2 * Σ u_t²`. -/
def controlAction (u : ℕ → ℝ) (N : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∑ n ∈ Finset.range N, (u n) ^ 2

/-- A finite control action is nonnegative. -/
theorem controlAction_nonneg (u : ℕ → ℝ) (N : ℕ) :
    0 ≤ controlAction u N := by
  simp only [controlAction]
  positivity

/-- The canonical unforced orbit defines the calibrated basin of the
constant-weight map. -/
def civicWeightedCalibratedBasin (p : LoopParams) (ρ : ℝ) : Set LoopState :=
  {x | Tendsto (civicWeightedOrbit p ρ x) atTop (𝓝 (calibratedPoint p))}

/-- Actions of finite controlled paths which have left the calibrated basin. -/
def quasipotentialActionSet (p : LoopParams) (ρ : ℝ) : Set ℝ :=
  {a | ∃ (N : ℕ) (u : ℕ → ℝ) (x : ℕ → LoopState),
    IsControlledCivicWeightedPath p ρ u x ∧
      x N ∉ civicWeightedCalibratedBasin p ρ ∧
      a = controlAction u N}

/-- Paper II's finite-path quasipotential.  Nonemptiness of the action set is
proved below under the hypotheses of `prop:qpbounds`. -/
def civicQuasipotential (p : LoopParams) (ρ : ℝ) : ℝ :=
  sInf (quasipotentialActionSet p ρ)

/-! ## Running maxima -/

/-- Running maximum of a real sequence, including time zero. -/
def runningMax (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => a 0
  | n + 1 => max (runningMax a n) (a (n + 1))

@[simp]
theorem runningMax_zero (a : ℕ → ℝ) : runningMax a 0 = a 0 := rfl

@[simp]
theorem runningMax_succ (a : ℕ → ℝ) (n : ℕ) :
    runningMax a (n + 1) = max (runningMax a n) (a (n + 1)) := rfl

/-- The current value is bounded by its running maximum. -/
theorem le_runningMax (a : ℕ → ℝ) (n : ℕ) : a n ≤ runningMax a n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_right _ _

/-- A running maximum is monotone in time. -/
theorem monotone_runningMax (a : ℕ → ℝ) : Monotone (runningMax a) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_max_left _ _

/-- A pointwise upper bound through time bounds the running maximum. -/
theorem runningMax_le_of_forall_le {a : ℕ → ℝ} {C : ℝ} {n : ℕ}
    (h : ∀ k ≤ n, a k ≤ C) : runningMax a n ≤ C := by
  induction n with
  | zero => simpa using h 0 le_rfl
  | succ n ih =>
      rw [runningMax_succ, max_le_iff]
      exact ⟨ih (fun k hk => h k (hk.trans n.le_succ)), h (n + 1) le_rfl⟩

/-- A pointwise lower bound at time zero bounds every running maximum. -/
theorem le_runningMax_of_le_zero {a : ℕ → ℝ} {c : ℝ}
    (h : c ≤ a 0) (n : ℕ) : c ≤ runningMax a n :=
  h.trans ((monotone_runningMax a) (Nat.zero_le n))

/-- The policy running maximum of a controlled path. -/
def policyRunningMax (x : ℕ → LoopState) (n : ℕ) : ℝ :=
  runningMax (fun k ↦ (x k).1) n

/-- Every policy along a controlled path lies in `[0,1]`. -/
theorem IsControlledCivicWeightedPath.policy_mem {p : LoopParams} {ρ : ℝ}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (path : IsControlledCivicWeightedPath p ρ u x) (n : ℕ) :
    (x n).1 ∈ Icc (0 : ℝ) 1 := by
  cases n with
  | zero =>
      rw [path.initial]
      simp [calibratedPoint]
  | succ n =>
      rw [path.step n]
      exact LoopParams.clipUnit_mem _

/-- The policy running maximum remains in `[0,1]`. -/
theorem IsControlledCivicWeightedPath.runningMax_mem {p : LoopParams} {ρ : ℝ}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (path : IsControlledCivicWeightedPath p ρ u x) (n : ℕ) :
    policyRunningMax x n ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact le_runningMax_of_le_zero
      (show (0 : ℝ) ≤ (x 0).1 by rw [path.initial]; simp [calibratedPoint]) n
  · apply runningMax_le_of_forall_le
    intro k _hk
    exact (path.policy_mem k).2

/-- The current policy is no larger than its running maximum. -/
theorem policy_le_runningMax (x : ℕ → LoopState) (n : ℕ) :
    (x n).1 ≤ policyRunningMax x n :=
  le_runningMax (fun k ↦ (x k).1) n

/-! ## Controlled stock envelopes -/

/-- Every controlled path remains in the paper's invariant box: the policy is
projected and the stock update is unchanged. -/
theorem IsControlledCivicWeightedPath.mem_absorbingBox {p : LoopParams}
    {ρ : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p)
    (path : IsControlledCivicWeightedPath p ρ u x) (n : ℕ) :
    x n ∈ absorbingBox p := by
  induction n with
  | zero =>
      rw [path.initial]
      exact ⟨by simp [calibratedPoint],
        stationaryStock_mem_stockInterval model (by norm_num)⟩
  | succ n ih =>
      rw [path.step n]
      constructor
      · exact LoopParams.clipUnit_mem _
      · have hnext := civicWeightedInvariantBox model ρ ih
        simpa only [controlledCivicWeightedStep, civicWeightedLoopMap,
          Prod.snd] using hnext.2

/-- The calibrated stock is a lower envelope for every controlled path from
the calibrated corner. -/
theorem IsControlledCivicWeightedPath.calibratedPoint_le
    {p : LoopParams} {ρ : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (path : IsControlledCivicWeightedPath p ρ u x) (n : ℕ) :
    calibratedPoint p ≤ x n := by
  have hzero : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hp₁mem : calibratedPoint p ∈ absorbingBox p :=
    ⟨by simp [calibratedPoint], stationaryStock_mem_stockInterval model hzero⟩
  have hstockFixed := stationaryStock_fixed model hzero
  induction n with
  | zero => rw [path.initial]
  | succ n ih =>
      have hxmem := path.mem_absorbingBox model n
      have hstockMono := (loopMap_monotoneOn_box model ss hp₁mem hxmem ih).2
      rw [path.step n]
      constructor
      · exact (LoopParams.clipUnit_mem _).1
      · calc
          (calibratedPoint p).2 = p.stockStep 0 (p.stationaryStock 0) := by
            simpa only [calibratedPoint] using hstockFixed.symm
          _ ≤ p.stockStep (x n).1 (x n).2 := by
            simpa only [LoopParams.loopMap, calibratedPoint] using hstockMono
          _ = (controlledCivicWeightedStep p ρ (u n) (x n)).2 := by
            rfl

/-- The exact stock is bounded by the stationary characteristic evaluated at
the policy running maximum. -/
theorem IsControlledCivicWeightedPath.stock_le_stationary_runningMax
    {p : LoopParams} {ρ : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (path : IsControlledCivicWeightedPath p ρ u x) (n : ℕ) :
    (x n).2 ≤ p.stationaryStock (policyRunningMax x n) := by
  induction n with
  | zero =>
      simp only [policyRunningMax, runningMax]
      rw [path.initial]
      simp only [calibratedPoint]
      exact le_rfl
  | succ n ih =>
      let m := policyRunningMax x n
      let m' := policyRunningMax x (n + 1)
      have hm := path.runningMax_mem n
      have hm' := path.runningMax_mem (n + 1)
      have hxmem := path.mem_absorbingBox model n
      have hupperMem : (m, p.stationaryStock m) ∈ absorbingBox p :=
        ⟨hm, stationaryStock_mem_stockInterval model hm⟩
      have hxle : x n ≤ (m, p.stationaryStock m) :=
        ⟨policy_le_runningMax x n, ih⟩
      have hstep := (loopMap_monotoneOn_box model ss hxmem hupperMem hxle).2
      have hfixed := stationaryStock_fixed model hm
      have hstockToM : p.stockStep (x n).1 (x n).2 ≤ p.stationaryStock m := by
        calc
          p.stockStep (x n).1 (x n).2 ≤ p.stockStep m (p.stationaryStock m) := by
            simpa only [LoopParams.loopMap] using hstep
          _ = p.stationaryStock m := hfixed
      have hmm' : m ≤ m' := by
        exact (monotone_runningMax (fun k ↦ (x k).1)) n.le_succ
      have hcharacteristic : p.stationaryStock m ≤ p.stationaryStock m' :=
        (stationaryStock_strictMonoOn model).monotoneOn hm hm' hmm'
      rw [path.step n]
      exact hstockToM.trans hcharacteristic

/-- The stationary civic-weighted gradient used in the paper is the actual
weighted gradient evaluated on the stationary characteristic. -/
theorem civicWeightedGradient_stationary_eq_weightedStationaryGradient
    {p : LoopParams} (ρ : ℝ) {β : ℝ}
    (_hβ : β ∈ Icc (0 : ℝ) 1) :
    civicWeightedGradient p ρ β (p.stationaryStock β) =
      weightedStationaryGradient p ρ β := by
  rw [weightedStationaryGradient, civicWeightedGradient,
    G_eq_gradU_stationary]

/-! ## Below the weighted saddle is still in the calibrated basin -/

/-- A characteristic point strictly below the weighted saddle takes a
componentwise nonincreasing first unforced step. -/
theorem civicWeighted_characteristic_step_le_of_below
    {p : LoopParams} {ρ b : ℝ} (model : DriftModelAssumptions p)
    (weighted : WeightedThresholdAssumption p ρ)
    (hb : b ∈ Ioo (0 : ℝ) 1) (hbelow : b < weighted.βdagger) :
    civicWeightedLoopMap p ρ (b, p.stationaryStock b) ≤
      (b, p.stationaryStock b) := by
  have hbclosed : b ∈ Icc (0 : ℝ) 1 := ⟨hb.1.le, hb.2.le⟩
  have hweighted : weightedStationaryGradient p ρ b < 0 :=
    weighted.gradient_neg_before b hb hbelow
  have hgradient :
      civicWeightedGradient p ρ b (p.stationaryStock b) < 0 := by
    rw [civicWeightedGradient_stationary_eq_weightedStationaryGradient ρ hbclosed]
    exact hweighted
  have hinput : civicWeightedInput p ρ b (p.stationaryStock b) < b := by
    simp only [civicWeightedInput]
    nlinarith [model.α_pos]
  have hpolicy := LoopParams.monotone_clipUnit hinput.le
  rw [clipUnit_eq_self hbclosed] at hpolicy
  have hstock := stationaryStock_fixed model hbclosed
  exact ⟨by
    simpa only [civicWeightedLoopMap, civicWeightedDeferenceStep] using hpolicy,
    by simpa only [civicWeightedLoopMap] using hstock.le⟩

/-- The unforced orbit from a characteristic point below the weighted saddle
converges monotonically to the calibrated corner. -/
theorem civicWeighted_characteristic_below_tendsto_calibrated
    {p : LoopParams} {ρ b : ℝ} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (hb : b ∈ Ioo (0 : ℝ) 1) (hbelow : b < weighted.βdagger) :
    Tendsto (civicWeightedOrbit p ρ (b, p.stationaryStock b)) atTop
      (𝓝 (calibratedPoint p)) := by
  let x₀ : LoopState := (b, p.stationaryStock b)
  let x := civicWeightedOrbit p ρ x₀
  have hbclosed : b ∈ Icc (0 : ℝ) 1 := ⟨hb.1.le, hb.2.le⟩
  have hx₀mem : x₀ ∈ absorbingBox p :=
    ⟨hbclosed, stationaryStock_mem_stockInterval model hbclosed⟩
  have traj : IsCivicWeightedTrajectory p ρ x :=
    civicWeightedOrbit_isTrajectory p ρ x₀
  have hfirst : x 1 ≤ x 0 := by
    change civicWeightedLoopMap p ρ x₀ ≤ x₀
    exact civicWeighted_characteristic_step_le_of_below model weighted hb hbelow
  obtain ⟨q, hqmem, hlim, heq⟩ :=
    civicWeightedComparableStep_convergesToFixedPoint
      model ss hcoop traj hx₀mem (t := 0) (Or.inr hfirst)
  have hmem := civicWeightedTrajectory_mem_absorbingBox model traj hx₀mem
  have hanti := civicWeightedTrajectory_tail_antitone_of_ge
    model ss hcoop traj hmem (t := 0) hfirst
  have hq_le : q ≤ x₀ := by
    have hle : ∀ n, x n ≤ x₀ := by
      intro n
      have hn := hanti (Nat.zero_le n)
      simpa only [Nat.add_zero, x, civicWeightedOrbit,
        Function.iterate_zero_apply] using hn
    exact isClosed_Iic.mem_of_tendsto hlim (Eventually.of_forall hle)
  have hqβ : q.1 ∈ Icc (0 : ℝ) 1 := hqmem.1
  have hqD := civicWeightedEquilibrium_stock_eq_stationary model hqβ heq
  have hqBelow : q.1 < weighted.βdagger :=
    hq_le.1.trans_lt hbelow
  have hqNotOne : q.1 ≠ 1 := by
    intro hqOne
    rw [hqOne] at hqBelow
    exact (not_lt_of_ge weighted.βdagger_mem.2.le) hqBelow
  by_cases hqZero : q.1 = 0
  · have hq : q = calibratedPoint p := by
      apply Prod.ext
      · simpa only [calibratedPoint] using hqZero
      · simpa only [calibratedPoint, hqZero] using hqD
    rwa [hq] at hlim
  · have hqInterior : q.1 ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hqβ.1 (Ne.symm hqZero),
        lt_of_le_of_ne hqβ.2 hqNotOne⟩
    have hpolicy := congrArg Prod.fst heq
    simp only [civicWeightedLoopMap, civicWeightedDeferenceStep] at hpolicy
    have hinput := (clipUnit_eq_interior_iff hqInterior).mp hpolicy
    have hgradient : civicWeightedGradient p ρ q.1 q.2 = 0 := by
      simp only [civicWeightedInput] at hinput
      nlinarith [model.α_pos]
    have hstationaryGradient : weightedStationaryGradient p ρ q.1 = 0 := by
      rw [← civicWeightedGradient_stationary_eq_weightedStationaryGradient
        ρ ⟨hqInterior.1.le, hqInterior.2.le⟩]
      rwa [← hqD]
    linarith [weighted.gradient_neg_before q.1 hqInterior hqBelow]

/-- Any admissible state squeezed between the calibrated corner and a
sub-saddle characteristic point belongs to the calibrated basin. -/
theorem calibratedPoint_mem_civicWeightedCalibratedBasin
    {p : LoopParams} {ρ : ℝ} (model : DriftModelAssumptions p)
    (threshold : ThresholdAssumption p) (hρ : 0 ≤ ρ) :
    calibratedPoint p ∈ civicWeightedCalibratedBasin p ρ := by
  have hfixed : civicWeightedLoopMap p ρ (calibratedPoint p) =
      calibratedPoint p := civicWeighted_calibrated_fixed model threshold hρ
  have horbit : ∀ n, civicWeightedOrbit p ρ (calibratedPoint p) n =
      calibratedPoint p := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [civicWeightedOrbit] at ih ⊢
        rw [Function.iterate_succ_apply', ih, hfixed]
  apply tendsto_const_nhds.congr'
  exact Eventually.of_forall fun n ↦ (horbit n).symm

/-- Any admissible state squeezed between the calibrated corner and a
sub-saddle characteristic point belongs to the calibrated basin. -/
theorem mem_civicWeightedCalibratedBasin_of_le_characteristic_below
    {p : LoopParams} {ρ b : ℝ} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    (hρ : 0 ≤ ρ) (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    {z : LoopState} (hzmem : z ∈ absorbingBox p)
    (hlower : calibratedPoint p ≤ z)
    (hupper : z ≤ (b, p.stationaryStock b))
    (hb : b ∈ Ioo (0 : ℝ) 1) (hbelow : b < weighted.βdagger) :
    z ∈ civicWeightedCalibratedBasin p ρ := by
  let lower : ℕ → LoopState := fun _ ↦ calibratedPoint p
  let middle := civicWeightedOrbit p ρ z
  let upper := civicWeightedOrbit p ρ (b, p.stationaryStock b)
  have hbclosed : b ∈ Icc (0 : ℝ) 1 := ⟨hb.1.le, hb.2.le⟩
  have hp₁mem : calibratedPoint p ∈ absorbingBox p :=
    ⟨by simp [calibratedPoint], stationaryStock_mem_stockInterval model (by norm_num)⟩
  have hu₀mem : (b, p.stationaryStock b) ∈ absorbingBox p :=
    ⟨hbclosed, stationaryStock_mem_stockInterval model hbclosed⟩
  have hmapMono := civicWeightedLoopMap_monotoneOn_box model ss hcoop
  have hmiddleMem : ∀ n, middle n ∈ absorbingBox p :=
    civicWeightedTrajectory_mem_absorbingBox model
      (civicWeightedOrbit_isTrajectory p ρ z) hzmem
  have hupperMem : ∀ n, upper n ∈ absorbingBox p :=
    civicWeightedTrajectory_mem_absorbingBox model
      (civicWeightedOrbit_isTrajectory p ρ (b, p.stationaryStock b)) hu₀mem
  have hp₁fixed := civicWeighted_calibrated_fixed model threshold hρ
  have hp₁fixed' : civicWeightedLoopMap p ρ (calibratedPoint p) =
      calibratedPoint p := by
    change IsCivicWeightedEquilibrium p ρ 0 (p.stationaryStock 0)
    exact hp₁fixed
  have hlowerBound : ∀ n, lower n ≤ middle n := by
    intro n
    induction n with
    | zero => simpa only [lower, middle, civicWeightedOrbit,
        Function.iterate_zero_apply] using hlower
    | succ n ih =>
        have hstep := hmapMono hp₁mem (hmiddleMem n) ih
        simp only [lower, middle, civicWeightedOrbit,
          Function.iterate_succ_apply'] at hstep ⊢
        rw [← hp₁fixed']
        exact hstep
  have hupperBound : ∀ n, middle n ≤ upper n := by
    intro n
    induction n with
    | zero => simpa only [middle, upper, civicWeightedOrbit,
        Function.iterate_zero_apply] using hupper
    | succ n ih =>
        simpa only [middle, upper, civicWeightedOrbit,
          Function.iterate_succ_apply'] using
          hmapMono (hmiddleMem n) (hupperMem n) ih
  have hlowerLim : Tendsto lower atTop (𝓝 (calibratedPoint p)) :=
    tendsto_const_nhds
  have hupperLim : Tendsto upper atTop (𝓝 (calibratedPoint p)) :=
    civicWeighted_characteristic_below_tendsto_calibrated
      model ss hcoop weighted hb hbelow
  have hpolicyLim : Tendsto (fun n ↦ (middle n).1) atTop
      (𝓝 (calibratedPoint p).1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      ((continuous_fst.tendsto (calibratedPoint p)).comp hlowerLim)
      ((continuous_fst.tendsto (calibratedPoint p)).comp hupperLim)
      (fun n ↦ (hlowerBound n).1) (fun n ↦ (hupperBound n).1)
  have hstockLim : Tendsto (fun n ↦ (middle n).2) atTop
      (𝓝 (calibratedPoint p).2) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      ((continuous_snd.tendsto (calibratedPoint p)).comp hlowerLim)
      ((continuous_snd.tendsto (calibratedPoint p)).comp hupperLim)
      (fun n ↦ (hlowerBound n).2) (fun n ↦ (hupperBound n).2)
  exact (Prod.tendsto_iff middle (calibratedPoint p)).2 ⟨hpolicyLim, hstockLim⟩

/-- Before its running maximum reaches the weighted saddle, every controlled
state still lies in the calibrated basin of the unforced weighted map. -/
theorem IsControlledCivicWeightedPath.mem_calibratedBasin_of_runningMax_lt
    {p : LoopParams} {ρ : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (threshold : ThresholdAssumption p) (hρ : 0 ≤ ρ)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (path : IsControlledCivicWeightedPath p ρ u x) {N : ℕ}
    (hmax : policyRunningMax x N < weighted.βdagger) :
    x N ∈ civicWeightedCalibratedBasin p ρ := by
  let b := policyRunningMax x N
  have hbclosed := path.runningMax_mem N
  have hupper : x N ≤ (b, p.stationaryStock b) :=
    ⟨policy_le_runningMax x N,
      path.stock_le_stationary_runningMax model ss N⟩
  have hlower := path.calibratedPoint_le model ss N
  by_cases hbzero : b = 0
  · have hx : x N = calibratedPoint p := by
      apply le_antisymm
      · simpa only [hbzero, calibratedPoint] using hupper
      · exact hlower
    rw [hx]
    exact calibratedPoint_mem_civicWeightedCalibratedBasin model threshold hρ
  · have hb : b ∈ Ioo (0 : ℝ) 1 := by
      exact ⟨lt_of_le_of_ne hbclosed.1 (Ne.symm hbzero),
        hmax.trans weighted.βdagger_mem.2⟩
    exact mem_civicWeightedCalibratedBasin_of_le_characteristic_below
      model ss threshold hρ hcoop weighted (path.mem_absorbingBox model N)
        hlower hupper hb hmax

/-- Consequently, leaving the calibrated basin forces the policy running
maximum to reach or cross the weighted saddle. -/
theorem IsControlledCivicWeightedPath.exit_forces_runningMax_ge
    {p : LoopParams} {ρ : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (threshold : ThresholdAssumption p) (hρ : 0 ≤ ρ)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (path : IsControlledCivicWeightedPath p ρ u x) {N : ℕ}
    (hexit : x N ∉ civicWeightedCalibratedBasin p ρ) :
    weighted.βdagger ≤ policyRunningMax x N := by
  by_contra hnot
  exact hexit (path.mem_calibratedBasin_of_runningMax_lt
    model ss threshold hρ hcoop weighted (lt_of_not_ge hnot))

/-! ## Capped maximum partitions -/

/-- The running maximum stopped at a target policy `r`. -/
def cappedPolicyRunningMax (r : ℝ) (x : ℕ → LoopState) (n : ℕ) : ℝ :=
  min r (policyRunningMax x n)

/-- A stopped running maximum is monotone. -/
theorem monotone_cappedPolicyRunningMax (r : ℝ) (x : ℕ → LoopState) :
    Monotone (cappedPolicyRunningMax r x) := by
  intro m n hmn
  exact min_le_min_left r ((monotone_runningMax (fun k ↦ (x k).1)) hmn)

/-- A controlled path's stopped running maximum starts at zero when the target
is nonnegative. -/
theorem IsControlledCivicWeightedPath.cappedRunningMax_zero
    {p : LoopParams} {ρ r : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (path : IsControlledCivicWeightedPath p ρ u x) (hr : 0 ≤ r) :
    cappedPolicyRunningMax r x 0 = 0 := by
  simp only [cappedPolicyRunningMax, policyRunningMax, runningMax]
  rw [path.initial]
  simp only [calibratedPoint, min_eq_right hr]

/-- Once the actual maximum reaches the target, its stopped version equals the
target. -/
theorem cappedRunningMax_eq_target {r : ℝ} {x : ℕ → LoopState} {N : ℕ}
    (hreach : r ≤ policyRunningMax x N) :
    cappedPolicyRunningMax r x N = r :=
  min_eq_left hreach

/-- Successive stopped maxima have nonnegative increments. -/
theorem cappedRunningMax_increment_nonneg (r : ℝ) (x : ℕ → LoopState)
    (n : ℕ) :
    0 ≤ cappedPolicyRunningMax r x (n + 1) -
      cappedPolicyRunningMax r x n :=
  sub_nonneg.mpr ((monotone_cappedPolicyRunningMax r x) n.le_succ)

/-- If a stopped maximum advances, its old value is the literal old running
maximum and its new value is no larger than the new policy. -/
theorem cappedRunningMax_advance_structure {r : ℝ} {x : ℕ → LoopState}
    {n : ℕ}
    (hadvance : cappedPolicyRunningMax r x n <
      cappedPolicyRunningMax r x (n + 1)) :
    cappedPolicyRunningMax r x n = policyRunningMax x n ∧
      cappedPolicyRunningMax r x (n + 1) ≤ (x (n + 1)).1 := by
  have hnew_le_r : cappedPolicyRunningMax r x (n + 1) ≤ r := min_le_left _ _
  have hold_lt_r : cappedPolicyRunningMax r x n < r :=
    hadvance.trans_le hnew_le_r
  have hmax_lt_r : policyRunningMax x n < r := by
    by_contra hnot
    have hrle : r ≤ policyRunningMax x n := not_lt.mp hnot
    rw [cappedPolicyRunningMax, min_eq_left hrle] at hold_lt_r
    exact lt_irrefl r hold_lt_r
  have hold : cappedPolicyRunningMax r x n = policyRunningMax x n :=
    min_eq_right hmax_lt_r.le
  have hmaxAdvance : policyRunningMax x n < policyRunningMax x (n + 1) := by
    calc
      policyRunningMax x n = cappedPolicyRunningMax r x n := hold.symm
      _ < cappedPolicyRunningMax r x (n + 1) := hadvance
      _ ≤ policyRunningMax x (n + 1) := min_le_right _ _
  have hnext : policyRunningMax x n < (x (n + 1)).1 := by
    by_contra hnot
    have hle : (x (n + 1)).1 ≤ policyRunningMax x n := not_lt.mp hnot
    have heq : policyRunningMax x (n + 1) = policyRunningMax x n := by
      simp only [policyRunningMax, runningMax_succ]
      exact max_eq_left hle
    rw [heq] at hmaxAdvance
    exact (lt_irrefl _ hmaxAdvance)
  have hmaxNext : policyRunningMax x (n + 1) = (x (n + 1)).1 := by
    simp only [policyRunningMax, runningMax_succ]
    exact max_eq_right hnext.le
  exact ⟨hold, (min_le_right _ _).trans_eq hmaxNext⟩

/-- A positive projected output cannot exceed its unprojected input. -/
theorem clipUnit_le_input_of_pos {z : ℝ}
    (hpos : 0 < LoopParams.clipUnit z) :
    LoopParams.clipUnit z ≤ z := by
  by_cases hz : z ≤ 0
  · rw [(clipUnit_eq_zero_iff z).2 hz] at hpos
    exact (lt_irrefl 0 hpos).elim
  · have hzpos : 0 < z := lt_of_not_ge hz
    by_cases hone : z ≤ 1
    · rw [clipUnit_eq_self ⟨hzpos.le, hone⟩]
    · rw [(clipUnit_eq_one_iff z).2 (not_le.mp hone).le]
      exact (not_le.mp hone).le

/-! ## The per-advance action ledger -/

/-- The positive barrier integrand below the weighted saddle. -/
def weightedBarrierIntegrand (p : LoopParams) (ρ β : ℝ) : ℝ :=
  -weightedStationaryGradient p ρ β

/-- At a controlled state, the weighted gradient is bounded above by the
on-characteristic gradient at the running maximum plus the exact dip term. -/
theorem IsControlledCivicWeightedPath.gradient_le_runningMax
    {p : LoopParams} {ρ : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (path : IsControlledCivicWeightedPath p ρ u x) (n : ℕ) :
    civicWeightedGradient p ρ (x n).1 (x n).2 ≤
      weightedStationaryGradient p ρ (policyRunningMax x n) +
        2 * p.c ^ 2 * p.stationaryStock (policyRunningMax x n) *
          (policyRunningMax x n - (x n).1) := by
  let β := (x n).1
  let D := (x n).2
  let b := policyRunningMax x n
  have hβ := path.policy_mem n
  have hb := path.runningMax_mem n
  have hD := path.stock_le_stationary_runningMax model ss n
  have hcoef := weighted_stock_coefficient_nonnegative model hcoop hβ
  have hmul :
      (2 * p.c * (1 - p.c * β) - ρ) * D ≤
        (2 * p.c * (1 - p.c * β) - ρ) * p.stationaryStock b :=
    mul_le_mul_of_nonneg_left hD hcoef
  calc
    civicWeightedGradient p ρ β D =
        -p.v + (2 * p.c * (1 - p.c * β) - ρ) * D := by
      simp only [civicWeightedGradient, LoopParams.gradU]
      ring
    _ ≤ -p.v + (2 * p.c * (1 - p.c * β) - ρ) *
        p.stationaryStock b := by linarith
    _ = weightedStationaryGradient p ρ b +
        2 * p.c ^ 2 * p.stationaryStock b * (b - β) := by
      rw [← civicWeightedGradient_stationary_eq_weightedStationaryGradient ρ hb]
      simp only [civicWeightedGradient, LoopParams.gradU]
      ring

/-- `(SS)` says the characteristic dip coefficient is nonnegative at every
policy in the invariant box. -/
theorem two_alpha_c_sq_stationaryStock_le_one {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    2 * p.α * p.c ^ 2 * p.stationaryStock β ≤ 1 := by
  have hk : 0 ≤ 2 * p.α * p.c ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) (sq_nonneg p.c)
  have hstock := (stationaryStock_mem_stockInterval model hβ).2
  have hratio : 2 * p.α * p.c ^ 2 * (p.I / p.lambda₀) ≤ 1 := by
    rw [show 2 * p.α * p.c ^ 2 * (p.I / p.lambda₀) =
      (2 * p.α * p.c ^ 2 * p.I) / p.lambda₀ by ring]
    exact (div_le_iff₀ model.lambda₀_pos).2 (by
      simpa only [one_mul] using ss.bound)
  exact (mul_le_mul_of_nonneg_left hstock hk).trans hratio

/-- On every step which advances the stopped running maximum, the required
control dominates the local barrier height plus advance divided by the
adaptation rate. -/
theorem IsControlledCivicWeightedPath.control_ge_barrier_add_advance
    {p : LoopParams} {ρ : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (path : IsControlledCivicWeightedPath p ρ u x) {n : ℕ}
    (hadvance : cappedPolicyRunningMax weighted.βdagger x n <
      cappedPolicyRunningMax weighted.βdagger x (n + 1)) :
    weightedBarrierIntegrand p ρ
        (cappedPolicyRunningMax weighted.βdagger x n) +
      (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
          cappedPolicyRunningMax weighted.βdagger x n) / p.α ≤ u n := by
  let b := cappedPolicyRunningMax weighted.βdagger x n
  let b' := cappedPolicyRunningMax weighted.βdagger x (n + 1)
  let β := (x n).1
  let D := (x n).2
  obtain ⟨hold, hnewPolicy⟩ := cappedRunningMax_advance_structure hadvance
  have hbRunning : b = policyRunningMax x n := hold
  have hbmem : b ∈ Icc (0 : ℝ) 1 := by
    rw [hbRunning]
    exact path.runningMax_mem n
  have hβmem := path.policy_mem n
  have hβb : β ≤ b := by
    rw [hbRunning]
    exact policy_le_runningMax x n
  have hbnonneg : 0 ≤ b := hbmem.1
  have hb'pos : 0 < b' := hbnonneg.trans_lt hadvance
  have hxnextPos : 0 < (x (n + 1)).1 := hb'pos.trans_le hnewPolicy
  have hxnext : (x (n + 1)).1 = LoopParams.clipUnit
      (β + p.α * (civicWeightedGradient p ρ β D + u n)) := by
    have hstep := congrArg Prod.fst (path.step n)
    simpa only [controlledCivicWeightedStep] using hstep
  have hinput : b' ≤ β + p.α *
      (civicWeightedGradient p ρ β D + u n) := by
    calc
      b' ≤ (x (n + 1)).1 := hnewPolicy
      _ = LoopParams.clipUnit
          (β + p.α * (civicWeightedGradient p ρ β D + u n)) := hxnext
      _ ≤ β + p.α * (civicWeightedGradient p ρ β D + u n) :=
        clipUnit_le_input_of_pos (by rwa [← hxnext])
  have hgradient : civicWeightedGradient p ρ β D ≤
      weightedStationaryGradient p ρ b +
        2 * p.c ^ 2 * p.stationaryStock b * (b - β) := by
    simpa only [hbRunning] using path.gradient_le_runningMax model ss hcoop n
  have hsmall := two_alpha_c_sq_stationaryStock_le_one model ss hbmem
  have hdip : 0 ≤ b - β := sub_nonneg.mpr hβb
  have hdipCoefficient :
      0 ≤ 1 - 2 * p.α * p.c ^ 2 * p.stationaryStock b := by
    linarith
  have hdipProduct := mul_nonneg hdipCoefficient hdip
  have halphaGradient := mul_le_mul_of_nonneg_left hgradient model.α_pos.le
  have hcross :
      p.α * weightedBarrierIntegrand p ρ b + (b' - b) ≤ p.α * u n := by
    simp only [weightedBarrierIntegrand]
    nlinarith
  have hdivide : p.α * ((b' - b) / p.α) = b' - b := by
    field_simp [model.α_pos.ne']
  nlinarith [model.α_pos]

/-- Each advance step pays at least the left-rectangle barrier contribution
used in the corrected lower bound. -/
theorem IsControlledCivicWeightedPath.advance_barrier_le_half_control_sq
    {p : LoopParams} {ρ : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (path : IsControlledCivicWeightedPath p ρ u x) {n : ℕ}
    (hadvance : cappedPolicyRunningMax weighted.βdagger x n <
      cappedPolicyRunningMax weighted.βdagger x (n + 1)) :
    (2 / p.α) * weightedBarrierIntegrand p ρ
        (cappedPolicyRunningMax weighted.βdagger x n) *
      (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
        cappedPolicyRunningMax weighted.βdagger x n) ≤ (u n) ^ 2 / 2 := by
  let b := cappedPolicyRunningMax weighted.βdagger x n
  let b' := cappedPolicyRunningMax weighted.βdagger x (n + 1)
  let a := weightedBarrierIntegrand p ρ b
  let d := (b' - b) / p.α
  have hb_le_root : b < weighted.βdagger :=
    hadvance.trans_le (min_le_left _ _)
  have hbnonneg : 0 ≤ b := by
    have hrun := path.runningMax_mem n
    exact le_min weighted.βdagger_mem.1.le hrun.1
  have hb_lt_one : b < 1 := hb_le_root.trans weighted.βdagger_mem.2
  have ha : 0 < a := by
    simp only [a, weightedBarrierIntegrand, neg_pos]
    by_cases hbzero : b = 0
    · simpa only [hbzero] using weighted.gradient_zero_neg
    · exact weighted.gradient_neg_before b
        ⟨lt_of_le_of_ne hbnonneg (Ne.symm hbzero), hb_lt_one⟩ hb_le_root
  have hdelta : 0 < b' - b := sub_pos.mpr hadvance
  have hd : 0 < d := div_pos hdelta model.α_pos
  have hu := path.control_ge_barrier_add_advance
    model ss hcoop weighted hadvance
  have hsum : 0 ≤ a + d := by positivity
  have huNonneg : 0 ≤ u n := hsum.trans hu
  have hproduct : 0 ≤ (u n - (a + d)) * (u n + (a + d)) :=
    mul_nonneg (sub_nonneg.mpr hu) (add_nonneg huNonneg hsum)
  have hsquare := sq_nonneg (a - d)
  have hcore : 2 * a * d ≤ (u n) ^ 2 / 2 := by
    nlinarith
  calc
    (2 / p.α) * a * (b' - b) = 2 * a * d := by
      simp only [d]
      field_simp [model.α_pos.ne']
    _ ≤ (u n) ^ 2 / 2 := hcore

/-- The advance ledger remains valid on nonadvancing steps, where its left
side vanishes. -/
theorem IsControlledCivicWeightedPath.barrier_increment_le_half_control_sq
    {p : LoopParams} {ρ : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (path : IsControlledCivicWeightedPath p ρ u x) (n : ℕ) :
    (2 / p.α) * weightedBarrierIntegrand p ρ
        (cappedPolicyRunningMax weighted.βdagger x n) *
      (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
        cappedPolicyRunningMax weighted.βdagger x n) ≤ (u n) ^ 2 / 2 := by
  have hmono := (monotone_cappedPolicyRunningMax weighted.βdagger x) n.le_succ
  rcases hmono.lt_or_eq with hadvance | heq
  · exact path.advance_barrier_le_half_control_sq
      model ss hcoop weighted hadvance
  · rw [heq]
    simp only [sub_self, mul_zero]
    positivity

/-- Summing the per-step ledger bounds the stopped left-rectangle sum by the
finite control action. -/
theorem IsControlledCivicWeightedPath.sum_barrier_increments_le_action
    {p : LoopParams} {ρ : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (path : IsControlledCivicWeightedPath p ρ u x) (N : ℕ) :
    (2 / p.α) * ∑ n ∈ Finset.range N,
        weightedBarrierIntegrand p ρ
            (cappedPolicyRunningMax weighted.βdagger x n) *
          (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
            cappedPolicyRunningMax weighted.βdagger x n) ≤
      controlAction u N := by
  rw [Finset.mul_sum]
  have hsum :
      ∑ n ∈ Finset.range N,
          (2 / p.α) *
            (weightedBarrierIntegrand p ρ
                (cappedPolicyRunningMax weighted.βdagger x n) *
              (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
                cappedPolicyRunningMax weighted.βdagger x n)) ≤
        ∑ n ∈ Finset.range N, (u n) ^ 2 / 2 := by
    exact Finset.sum_le_sum fun n hn ↦ by
      simpa only [mul_assoc] using
        path.barrier_increment_le_half_control_sq model ss hcoop weighted n
  calc
    ∑ n ∈ Finset.range N,
        (2 / p.α) *
          (weightedBarrierIntegrand p ρ
              (cappedPolicyRunningMax weighted.βdagger x n) *
            (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
              cappedPolicyRunningMax weighted.βdagger x n)) ≤
        ∑ n ∈ Finset.range N, (u n) ^ 2 / 2 := hsum
    _ = controlAction u N := by
      simp only [controlAction, div_eq_mul_inv, Finset.mul_sum]
      ring_nf

/-! ## Lipschitz Riemann comparison -/

/-- `L` is a Lipschitz constant for `f` on the closed segment `[a,b]`.
The nonnegativity field makes the convention explicit. -/
structure IsLipschitzConstantOn (f : ℝ → ℝ) (L a b : ℝ) : Prop where
  nonneg : 0 ≤ L
  bound : ∀ ⦃x⦄, x ∈ Icc a b → ∀ ⦃y⦄, y ∈ Icc a b →
    |f x - f y| ≤ L * |x - y|

/-- The weighted barrier integrand is continuous on the saddle segment. -/
theorem continuousOn_weightedBarrierIntegrand {p : LoopParams}
    (model : DriftModelAssumptions p) (ρ : ℝ)
    (weighted : WeightedThresholdAssumption p ρ) :
    ContinuousOn (weightedBarrierIntegrand p ρ)
      (Icc (0 : ℝ) weighted.βdagger) := by
  intro b hb
  have hbUnit : b ∈ Icc (0 : ℝ) 1 :=
    ⟨hb.1, hb.2.trans weighted.βdagger_mem.2.le⟩
  change ContinuousWithinAt (-weightedStationaryGradient p ρ)
    (Icc (0 : ℝ) weighted.βdagger) b
  exact (hasDerivAt_weightedStationaryGradient model ρ hbUnit).continuousAt.neg.continuousWithinAt

/-- The Lipschitz constant used in the corrected quasipotential bounds is
available from the model assumptions, rather than being an additional
substantive hypothesis. -/
theorem exists_lipschitzConstantOn_weightedBarrierIntegrand
    {p : LoopParams} (model : DriftModelAssumptions p) {ρ : ℝ}
    (weighted : WeightedThresholdAssumption p ρ) :
    ∃ L, IsLipschitzConstantOn (weightedBarrierIntegrand p ρ) L
      0 weighted.βdagger := by
  let s : Set ℝ := Icc (0 : ℝ) weighted.βdagger
  have hslopeCont : ContinuousOn (weightedStationaryGradientSlope p ρ) s := by
    intro b hb
    have hbUnit : b ∈ Icc (0 : ℝ) 1 :=
      ⟨hb.1, hb.2.trans weighted.βdagger_mem.2.le⟩
    have hden : 1 - p.s b ≠ 0 :=
      (thresholdDenominator_pos model hbUnit).ne'
    have hdenCont : ContinuousAt (fun z : ℝ ↦ 1 - p.s z) b := by
      simp only [LoopParams.s]
      fun_prop
    have hdenSqCont : ContinuousAt (fun z : ℝ ↦ (1 - p.s z) ^ 2) b :=
      hdenCont.pow 2
    have hfirstNum : ContinuousAt (fun z : ℝ ↦
        2 * p.c * p.I *
          (-p.c * (1 - p.s z) + (1 - p.c * z) * p.sSlope z)) b := by
      simp only [LoopParams.s, LoopParams.sSlope]
      fun_prop
    have hsecondNum : ContinuousAt (fun z : ℝ ↦ p.I * p.sSlope z) b := by
      simp only [LoopParams.sSlope]
      fun_prop
    apply ContinuousAt.continuousWithinAt
    unfold weightedStationaryGradientSlope LoopParams.GSlope
    rw [model.no_content_gain]
    simp only [sub_zero]
    exact (hfirstNum.div hdenSqCont (pow_ne_zero 2 hden)).sub
      (continuousAt_const.mul
        (hsecondNum.div hdenSqCont (pow_ne_zero 2 hden)))
  obtain ⟨L, hL⟩ := isCompact_Icc.bddAbove_image hslopeCont.norm
  have hLbound : ∀ b ∈ s, ‖weightedStationaryGradientSlope p ρ b‖ ≤ L := by
    intro b hb
    exact hL (mem_image_of_mem _ hb)
  have hLnonneg : 0 ≤ L := by
    have hzero : (0 : ℝ) ∈ s :=
      ⟨le_rfl, weighted.βdagger_mem.1.le⟩
    exact (norm_nonneg (weightedStationaryGradientSlope p ρ 0)).trans
      (hLbound 0 hzero)
  refine ⟨L, hLnonneg, ?_⟩
  intro x hx y hy
  have hdiff : ∀ z ∈ s,
      DifferentiableAt ℝ (weightedBarrierIntegrand p ρ) z := by
    intro z hz
    have hzUnit : z ∈ Icc (0 : ℝ) 1 :=
      ⟨hz.1, hz.2.trans weighted.βdagger_mem.2.le⟩
    exact (hasDerivAt_weightedStationaryGradient model ρ hzUnit).neg.differentiableAt
  have hderiv : ∀ z ∈ s,
      ‖deriv (weightedBarrierIntegrand p ρ) z‖ ≤ L := by
    intro z hz
    have hzUnit : z ∈ Icc (0 : ℝ) 1 :=
      ⟨hz.1, hz.2.trans weighted.βdagger_mem.2.le⟩
    have hzderiv : deriv (weightedBarrierIntegrand p ρ) z =
        -weightedStationaryGradientSlope p ρ z :=
      (hasDerivAt_weightedStationaryGradient model ρ hzUnit).neg.deriv
    rw [hzderiv, norm_neg]
    exact hLbound z hz
  have hsconvex : Convex ℝ s := by
    simpa only [s] using convex_Icc (0 : ℝ) weighted.βdagger
  have hmean := Convex.norm_image_sub_le_of_norm_deriv_le
    hdiff hderiv hsconvex hx hy
  simpa only [Real.norm_eq_abs, abs_sub_comm] using hmean

/-- Every stopped running maximum lies on the saddle segment. -/
theorem IsControlledCivicWeightedPath.cappedRunningMax_mem
    {p : LoopParams} {ρ : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (weighted : WeightedThresholdAssumption p ρ)
    (path : IsControlledCivicWeightedPath p ρ u x) (n : ℕ) :
    cappedPolicyRunningMax weighted.βdagger x n ∈
      Icc (0 : ℝ) weighted.βdagger := by
  have hrun := path.runningMax_mem n
  exact ⟨le_min weighted.βdagger_mem.1.le hrun.1, min_le_left _ _⟩

/-- A Lipschitz function's integral over one increasing cell is bounded by
its left rectangle plus the quadratic cell error. -/
theorem integral_le_left_rectangle_add_lipschitz
    {f : ℝ → ℝ} {L A B a b : ℝ}
    (hcont : ContinuousOn f (Icc A B))
    (hL : IsLipschitzConstantOn f L A B)
    (ha : a ∈ Icc A B) (hb : b ∈ Icc A B) (hab : a ≤ b) :
    (∫ z in a..b, f z) ≤
      f a * (b - a) + (L / 2) * (b - a) ^ 2 := by
  have hcell : Icc a b ⊆ Icc A B := by
    intro z hz
    exact ⟨ha.1.trans hz.1, hz.2.trans hb.2⟩
  have hfcont : ContinuousOn f [[a, b]] := by
    rw [uIcc_of_le hab]
    exact hcont.mono hcell
  have hfint : IntervalIntegrable f MeasureTheory.volume a b :=
    hfcont.intervalIntegrable
  have hgcont : Continuous (fun z : ℝ ↦ f a + L * (z - a)) := by fun_prop
  have hgint : IntervalIntegrable (fun z : ℝ ↦ f a + L * (z - a))
      MeasureTheory.volume a b :=
    hgcont.intervalIntegrable a b
  have hpoint : ∀ z ∈ Icc a b, f z ≤ f a + L * (z - a) := by
    intro z hz
    have hza : 0 ≤ z - a := sub_nonneg.mpr hz.1
    have hLip := hL.bound (hcell hz) ha
    rw [abs_of_nonneg hza] at hLip
    linarith [le_abs_self (f z - f a)]
  calc
    (∫ z in a..b, f z) ≤ ∫ z in a..b, f a + L * (z - a) :=
      intervalIntegral.integral_mono_on hab hfint hgint hpoint
    _ = f a * (b - a) + (L / 2) * (b - a) ^ 2 := by
      rw [intervalIntegral.integral_add]
      · rw [intervalIntegral.integral_const]
        rw [intervalIntegral.integral_const_mul]
        rw [intervalIntegral.integral_sub]
        · rw [integral_id, intervalIntegral.integral_const]
          simp only [smul_eq_mul]
          ring
        · exact continuous_id.intervalIntegrable a b
        · exact continuous_const.intervalIntegrable a b
      · exact continuous_const.intervalIntegrable a b
      · exact (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable a b

/-- The reverse one-cell estimate: a left rectangle is bounded by the
integral plus the same quadratic Lipschitz error. -/
theorem left_rectangle_le_integral_add_lipschitz
    {f : ℝ → ℝ} {L A B a b : ℝ}
    (hcont : ContinuousOn f (Icc A B))
    (hL : IsLipschitzConstantOn f L A B)
    (ha : a ∈ Icc A B) (hb : b ∈ Icc A B) (hab : a ≤ b) :
    f a * (b - a) ≤
      (∫ z in a..b, f z) + (L / 2) * (b - a) ^ 2 := by
  have hnegL : IsLipschitzConstantOn (fun z ↦ -f z) L A B := by
    refine ⟨hL.nonneg, ?_⟩
    intro x hx y hy
    simpa only [neg_sub_neg, abs_neg, abs_sub_comm] using hL.bound hy hx
  have hneg := integral_le_left_rectangle_add_lipschitz
    hcont.neg hnegL ha hb hab
  change (∫ z in a..b, -f z) ≤
    (-f a) * (b - a) + (L / 2) * (b - a) ^ 2 at hneg
  rw [intervalIntegral.integral_neg] at hneg
  linarith

/-- A left Riemann sum on any finite increasing partition is at most the
integral over its endpoints plus the accumulated quadratic mesh error. -/
theorem leftRiemannSum_le_integral_add_lipschitz
    {f : ℝ → ℝ} {L A B : ℝ} {b : ℕ → ℝ} {N : ℕ}
    (hcont : ContinuousOn f (Icc A B))
    (hL : IsLipschitzConstantOn f L A B)
    (hbmem : ∀ n ≤ N, b n ∈ Icc A B)
    (hbmono : ∀ n < N, b n ≤ b (n + 1)) :
    (∑ n ∈ Finset.range N, f (b n) * (b (n + 1) - b n)) ≤
      (∫ z in b 0..b N, f z) +
        (L / 2) * ∑ n ∈ Finset.range N, (b (n + 1) - b n) ^ 2 := by
  have hcellInt : ∀ n < N, IntervalIntegrable f MeasureTheory.volume
      (b n) (b (n + 1)) := by
    intro n hn
    have hnle : n ≤ N := hn.le
    have hsuccle : n + 1 ≤ N := by omega
    have hsubset : [[b n, b (n + 1)]] ⊆ Icc A B := by
      rw [uIcc_of_le (hbmono n hn)]
      intro z hz
      exact ⟨(hbmem n hnle).1.trans hz.1,
        hz.2.trans (hbmem (n + 1) hsuccle).2⟩
    exact (hcont.mono hsubset).intervalIntegrable
  have hadjacent :
      ∑ n ∈ Finset.range N, ∫ z in b n..b (n + 1), f z =
        ∫ z in b 0..b N, f z :=
    intervalIntegral.sum_integral_adjacent_intervals hcellInt
  have hcells :
      ∑ n ∈ Finset.range N, f (b n) * (b (n + 1) - b n) ≤
        ∑ n ∈ Finset.range N,
          ((∫ z in b n..b (n + 1), f z) +
            (L / 2) * (b (n + 1) - b n) ^ 2) := by
    apply Finset.sum_le_sum
    intro n hn
    have hnlt : n < N := Finset.mem_range.mp hn
    exact left_rectangle_le_integral_add_lipschitz hcont hL
      (hbmem n hnlt.le) (hbmem (n + 1) (by omega))
      (hbmono n hnlt)
  calc
    (∑ n ∈ Finset.range N, f (b n) * (b (n + 1) - b n)) ≤
        ∑ n ∈ Finset.range N,
          ((∫ z in b n..b (n + 1), f z) +
            (L / 2) * (b (n + 1) - b n) ^ 2) := hcells
    _ = (∑ n ∈ Finset.range N, ∫ z in b n..b (n + 1), f z) +
        (L / 2) * ∑ n ∈ Finset.range N,
          (b (n + 1) - b n) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (∫ z in b 0..b N, f z) +
        (L / 2) * ∑ n ∈ Finset.range N,
          (b (n + 1) - b n) ^ 2 := by rw [hadjacent]

/-- Below the weighted saddle, the barrier integrand is strictly positive. -/
theorem WeightedThresholdAssumption.barrier_pos_before
    {p : LoopParams} {ρ b : ℝ}
    (weighted : WeightedThresholdAssumption p ρ)
    (hb : b ∈ Icc (0 : ℝ) weighted.βdagger)
    (hbelow : b < weighted.βdagger) :
    0 < weightedBarrierIntegrand p ρ b := by
  simp only [weightedBarrierIntegrand, neg_pos]
  by_cases hbzero : b = 0
  · simpa only [hbzero] using weighted.gradient_zero_neg
  · exact weighted.gradient_neg_before b
      ⟨lt_of_le_of_ne hb.1 (Ne.symm hbzero),
        hbelow.trans weighted.βdagger_mem.2⟩ hbelow

/-- The square of each stopped-maximum increment is controlled by the square
of that step's control.  Nonadvancing steps require no sign condition on the
control. -/
theorem IsControlledCivicWeightedPath.capped_increment_sq_le_control_sq
    {p : LoopParams} {ρ : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (path : IsControlledCivicWeightedPath p ρ u x) (n : ℕ) :
    (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
        cappedPolicyRunningMax weighted.βdagger x n) ^ 2 ≤
      p.α ^ 2 * (u n) ^ 2 := by
  let b := cappedPolicyRunningMax weighted.βdagger x n
  let b' := cappedPolicyRunningMax weighted.βdagger x (n + 1)
  change (b' - b) ^ 2 ≤ p.α ^ 2 * (u n) ^ 2
  have hmono : b ≤ b' :=
    (monotone_cappedPolicyRunningMax weighted.βdagger x) n.le_succ
  rcases hmono.lt_or_eq with hadvance | heq
  · have hbmem := path.cappedRunningMax_mem weighted n
    have hbarrier : 0 < weightedBarrierIntegrand p ρ b :=
      weighted.barrier_pos_before hbmem
        (hadvance.trans_le (min_le_left _ _))
    have hu := path.control_ge_barrier_add_advance
      model ss hcoop weighted hadvance
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

/-- The sum of squared stopped-maximum increments is at most `2α²` times the
finite action. -/
theorem IsControlledCivicWeightedPath.sum_capped_increment_sq_le_action
    {p : LoopParams} {ρ : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (path : IsControlledCivicWeightedPath p ρ u x) (N : ℕ) :
    ∑ n ∈ Finset.range N,
        (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
          cappedPolicyRunningMax weighted.βdagger x n) ^ 2 ≤
      2 * p.α ^ 2 * controlAction u N := by
  calc
    ∑ n ∈ Finset.range N,
        (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
          cappedPolicyRunningMax weighted.βdagger x n) ^ 2 ≤
        ∑ n ∈ Finset.range N, p.α ^ 2 * (u n) ^ 2 := by
      exact Finset.sum_le_sum fun n hn ↦
        path.capped_increment_sq_le_control_sq model ss hcoop weighted n
    _ = 2 * p.α ^ 2 * controlAction u N := by
      simp only [controlAction, Finset.mul_sum]
      ring_nf

/-- An exiting path's stopped maxima partition the whole barrier interval, so
the Lipschitz cell estimate compares the barrier integral with its stopped
left sum and squared mesh. -/
theorem IsControlledCivicWeightedPath.barrier_integral_le_partition
    {p : LoopParams} {ρ L : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (threshold : ThresholdAssumption p) (hρ : 0 ≤ ρ)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p ρ) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPath p ρ u x) {N : ℕ}
    (hexit : x N ∉ civicWeightedCalibratedBasin p ρ) :
    (∫ b in (0 : ℝ)..weighted.βdagger,
        weightedBarrierIntegrand p ρ b) ≤
      (∑ n ∈ Finset.range N,
        weightedBarrierIntegrand p ρ
            (cappedPolicyRunningMax weighted.βdagger x n) *
          (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
            cappedPolicyRunningMax weighted.βdagger x n)) +
      (L / 2) * ∑ n ∈ Finset.range N,
        (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
          cappedPolicyRunningMax weighted.βdagger x n) ^ 2 := by
  let b : ℕ → ℝ := fun n ↦ cappedPolicyRunningMax weighted.βdagger x n
  let f : ℝ → ℝ := weightedBarrierIntegrand p ρ
  have hcont : ContinuousOn f (Icc (0 : ℝ) weighted.βdagger) :=
    continuousOn_weightedBarrierIntegrand model ρ weighted
  have hbmem : ∀ n, b n ∈ Icc (0 : ℝ) weighted.βdagger :=
    fun n ↦ path.cappedRunningMax_mem weighted n
  have hbmono : ∀ n, b n ≤ b (n + 1) := fun n ↦
    (monotone_cappedPolicyRunningMax weighted.βdagger x) n.le_succ
  have hcellInt : ∀ n < N, IntervalIntegrable f MeasureTheory.volume
      (b n) (b (n + 1)) := by
    intro n hn
    have hsubset : [[b n, b (n + 1)]] ⊆
        Icc (0 : ℝ) weighted.βdagger := by
      rw [uIcc_of_le (hbmono n)]
      intro z hz
      exact ⟨(hbmem n).1.trans hz.1, hz.2.trans (hbmem (n + 1)).2⟩
    exact (hcont.mono hsubset).intervalIntegrable
  have hadjacent :
      ∑ n ∈ Finset.range N, ∫ z in b n..b (n + 1), f z =
        ∫ z in b 0..b N, f z :=
    intervalIntegral.sum_integral_adjacent_intervals hcellInt
  have hstart : b 0 = 0 :=
    path.cappedRunningMax_zero weighted.βdagger_mem.1.le
  have hend : b N = weighted.βdagger :=
    cappedRunningMax_eq_target
      (path.exit_forces_runningMax_ge model ss threshold hρ hcoop weighted hexit)
  have hcells :
      ∑ n ∈ Finset.range N, ∫ z in b n..b (n + 1), f z ≤
        ∑ n ∈ Finset.range N,
          (f (b n) * (b (n + 1) - b n) +
            (L / 2) * (b (n + 1) - b n) ^ 2) := by
    exact Finset.sum_le_sum fun n hn ↦
      integral_le_left_rectangle_add_lipschitz hcont hL
        (hbmem n) (hbmem (n + 1)) (hbmono n)
  change (∫ z in (0 : ℝ)..weighted.βdagger, f z) ≤ _
  calc
    (∫ z in (0 : ℝ)..weighted.βdagger, f z) =
        ∑ n ∈ Finset.range N, ∫ z in b n..b (n + 1), f z := by
      rw [hadjacent, hstart, hend]
    _ ≤ ∑ n ∈ Finset.range N,
        (f (b n) * (b (n + 1) - b n) +
          (L / 2) * (b (n + 1) - b n) ^ 2) := hcells
    _ = (∑ n ∈ Finset.range N, f (b n) * (b (n + 1) - b n)) +
        (L / 2) * ∑ n ∈ Finset.range N, (b (n + 1) - b n) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Corrected finite-path lower bound from `prop:qpbounds`: every controlled
path which exits the calibrated basin pays the Lipschitz-corrected barrier. -/
theorem IsControlledCivicWeightedPath.action_lower_bound
    {p : LoopParams} {ρ L : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (threshold : ThresholdAssumption p) (hρ : 0 ≤ ρ)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p ρ) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPath p ρ u x) {N : ℕ}
    (hexit : x N ∉ civicWeightedCalibratedBasin p ρ) :
    (2 / (p.α * (1 + 2 * p.α * L))) *
        (∫ b in (0 : ℝ)..weighted.βdagger,
          weightedBarrierIntegrand p ρ b) ≤
      controlAction u N := by
  let R : ℝ := ∑ n ∈ Finset.range N,
    weightedBarrierIntegrand p ρ
        (cappedPolicyRunningMax weighted.βdagger x n) *
      (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
        cappedPolicyRunningMax weighted.βdagger x n)
  let Q : ℝ := ∑ n ∈ Finset.range N,
    (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
      cappedPolicyRunningMax weighted.βdagger x n) ^ 2
  let A : ℝ := controlAction u N
  let Ibar : ℝ := ∫ b in (0 : ℝ)..weighted.βdagger,
    weightedBarrierIntegrand p ρ b
  have hpartition : Ibar ≤ R + (L / 2) * Q :=
    path.barrier_integral_le_partition model ss threshold hρ hcoop
      weighted hL hexit
  have hRscaled : (2 / p.α) * R ≤ A :=
    path.sum_barrier_increments_le_action model ss hcoop weighted N
  have hQ : Q ≤ 2 * p.α ^ 2 * A :=
    path.sum_capped_increment_sq_le_action model ss hcoop weighted N
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

/-! ## Nonemptiness of the finite-action escape problem -/

/-- Stock path obtained by forcing policy to one after the initial calibrated
state. -/
def forcedCapturedStockPath (p : LoopParams) (n : ℕ) : ℝ :=
  arithGeom (p.s 1) p.I (p.stationaryStock 0) n

/-- An auxiliary controlled path which jumps policy to one and holds it there
while the exact stock recursion converges to captured stock. -/
def forcedCapturedPath (p : LoopParams) : ℕ → LoopState
  | 0 => calibratedPoint p
  | n + 1 => (1, forcedCapturedStockPath p n)

/-- The exact control which realizes `forcedCapturedPath`. -/
def forcedCapturedControl (p : LoopParams) (ρ : ℝ) (n : ℕ) : ℝ :=
  (1 - (forcedCapturedPath p n).1) / p.α -
    civicWeightedGradient p ρ (forcedCapturedPath p n).1
      (forcedCapturedPath p n).2

/-- The forced stock tail obeys the exact stock recursion at full policy. -/
theorem forcedCapturedStockPath_succ {p : LoopParams}
    (model : DriftModelAssumptions p) (n : ℕ) :
    p.stockStep 1 (forcedCapturedStockPath p n) =
      forcedCapturedStockPath p (n + 1) := by
  simp only [forcedCapturedStockPath, LoopParams.stockStep,
    model.no_content_gain, add_zero, arithGeom_succ]

/-- The auxiliary path is a genuine controlled path from the calibrated
corner; its stock coordinate is never modified by control. -/
theorem forcedCapturedPath_isControlled {p : LoopParams}
    (model : DriftModelAssumptions p) (ρ : ℝ) :
    IsControlledCivicWeightedPath p ρ (forcedCapturedControl p ρ)
      (forcedCapturedPath p) := by
  constructor
  · rfl
  · intro n
    apply Prod.ext
    · simp only [controlledCivicWeightedStep, forcedCapturedControl]
      have hinput :
          (forcedCapturedPath p n).1 + p.α *
              (civicWeightedGradient p ρ (forcedCapturedPath p n).1
                  (forcedCapturedPath p n).2 +
                ((1 - (forcedCapturedPath p n).1) / p.α -
                  civicWeightedGradient p ρ (forcedCapturedPath p n).1
                    (forcedCapturedPath p n).2)) = 1 := by
        field_simp [model.α_pos.ne']
        ring
      rw [hinput, clipUnit_eq_self (by norm_num : (1 : ℝ) ∈ Icc 0 1)]
      cases n <;> rfl
    · cases n with
      | zero =>
          simp only [forcedCapturedPath, controlledCivicWeightedStep,
            forcedCapturedStockPath, arithGeom_zero]
          exact (stationaryStock_fixed model (by norm_num)).symm
      | succ n =>
          simp only [forcedCapturedPath, controlledCivicWeightedStep]
          exact (forcedCapturedStockPath_succ model n).symm

/-- Holding full policy drives the auxiliary controlled path to the captured
corner. -/
theorem forcedCapturedPath_tendsto {p : LoopParams}
    (model : DriftModelAssumptions p) :
    Tendsto (forcedCapturedPath p) atTop (𝓝 (capturedPoint p)) := by
  have hs := driftStockMultiplier_nonneg_le model
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  have hstock : Tendsto (forcedCapturedStockPath p) atTop
      (𝓝 (p.stationaryStock 1)) := by
    have hlim := tendsto_affineRecursion (p.s 1) p.I
      (p.stationaryStock 0) hs.1
      (hs.2.trans_lt (sub_lt_self 1 model.lambda₀_pos))
    change Tendsto (arithGeom (p.s 1) p.I (p.stationaryStock 0)) atTop
      (𝓝 (p.stationaryStock 1))
    simpa only [LoopParams.stationaryStock, model.no_content_gain, sub_zero] using hlim
  have hshift : Tendsto (fun n ↦ forcedCapturedPath p (n + 1)) atTop
      (𝓝 (capturedPoint p)) := by
    apply (Prod.tendsto_iff _ _).2
    constructor
    · simpa only [forcedCapturedPath, capturedPoint] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))
    · simpa only [forcedCapturedPath, capturedPoint] using hstock
  exact (tendsto_add_atTop_iff_nat 1).1 hshift

/-- Under the proposition's strict-below-release hypotheses, at least one
finite controlled path leaves the calibrated basin.  Hence the real infimum
defining the quasipotential is not an empty-set convention. -/
theorem quasipotentialActionSet_nonempty {p : LoopParams} {ρ : ℝ}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hρ : 0 ≤ ρ) (hρcure : ρ < cureThreshold p) :
    (quasipotentialActionSet p ρ).Nonempty := by
  obtain ⟨U, hUnhds, hattract⟩ :=
    civicWeighted_captured_local_attraction model ss hρ hρcure
  let x := forcedCapturedPath p
  let u := forcedCapturedControl p ρ
  have hlim : Tendsto x atTop (𝓝 (capturedPoint p)) :=
    forcedCapturedPath_tendsto model
  have hEventually : ∀ᶠ n in atTop, x n ∈ U := hlim hUnhds
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hEventually
  have path : IsControlledCivicWeightedPath p ρ u x :=
    forcedCapturedPath_isControlled model ρ
  have hcaptured : Tendsto (civicWeightedOrbit p ρ (x N)) atTop
      (𝓝 (capturedPoint p)) := by
    exact hattract (civicWeightedOrbit_isTrajectory p ρ (x N))
      (path.mem_absorbingBox model N) (hN N le_rfl)
  have hexit : x N ∉ civicWeightedCalibratedBasin p ρ := by
    intro hcalibrated
    have heq : capturedPoint p = calibratedPoint p :=
      tendsto_nhds_unique hcaptured hcalibrated
    have hfirst := congrArg Prod.fst heq
    norm_num [capturedPoint, calibratedPoint] at hfirst
  exact ⟨controlAction u N, N, u, x, path, hexit, rfl⟩

/-- Paper II, Proposition `prop:qpbounds`, `civic_drift.tex:354`: the corrected
Lipschitz lower bound passes from every exiting path to the quasipotential
infimum. -/
theorem civicQuasipotential_lower_bound
    {p : LoopParams} {ρ L : ℝ}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (threshold : ThresholdAssumption p) (hρ : 0 ≤ ρ)
    (hρcure : ρ < cureThreshold p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p ρ) L
      0 weighted.βdagger) :
    (2 / (p.α * (1 + 2 * p.α * L))) *
        (∫ b in (0 : ℝ)..weighted.βdagger,
          weightedBarrierIntegrand p ρ b) ≤
      civicQuasipotential p ρ := by
  change _ ≤ sInf (quasipotentialActionSet p ρ)
  apply le_csInf (quasipotentialActionSet_nonempty model ss hρ hρcure)
  rintro a ⟨N, u, x, path, hexit, rfl⟩
  exact path.action_lower_bound model ss threshold hρ hcoop weighted hL hexit

/-- Any exhibited basin-exiting finite controlled path supplies an upper
bound on the quasipotential. -/
theorem civicQuasipotential_le_controlAction
    {p : LoopParams} {ρ : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState} {N : ℕ}
    (path : IsControlledCivicWeightedPath p ρ u x)
    (hexit : x N ∉ civicWeightedCalibratedBasin p ρ) :
    civicQuasipotential p ρ ≤ controlAction u N := by
  have hbdd : BddBelow (quasipotentialActionSet p ρ) := by
    refine ⟨0, ?_⟩
    rintro a ⟨M, w, y, _path, _hexit, rfl⟩
    exact controlAction_nonneg w M
  exact csInf_le hbdd ⟨N, u, x, path, hexit, rfl⟩

/-- The proposition's bracket-separation implication is purely order
theoretic once the lower and strategy upper bounds are established. -/
theorem quasipotential_strictMono_of_bracket_separation
    {p : LoopParams} {ρ ρ' lowerAtRho' strategyAtRho : ℝ}
    (hlower : lowerAtRho' ≤ civicQuasipotential p ρ')
    (hupper : civicQuasipotential p ρ ≤ strategyAtRho)
    (hseparate : strategyAtRho < lowerAtRho') :
    civicQuasipotential p ρ < civicQuasipotential p ρ' :=
  hupper.trans_lt (hseparate.trans_le hlower)

/-! ## The printed doubling formula versus a holding phase -/

/-- The literal control formula called the doubling strategy in
`prop:qpbounds`. -/
def doublingControl (p : LoopParams) (ρ β D : ℝ) : ℝ :=
  2 * max (-civicWeightedGradient p ρ β D) 0

/-- At a negative-gradient interior state where projection does not bind, the
printed doubling control strictly advances policy; it does not hold policy
fixed.  A genuine holding phase instead needs control `u = -gρ`.

Paper II, Proposition `prop:qpbounds`, `civic_drift.tex:354`. -/
theorem doublingControl_strictly_advances_of_gradient_neg
    {p : LoopParams} (model : DriftModelAssumptions p)
    {ρ β D : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1)
    (hgradient : civicWeightedGradient p ρ β D < 0)
    (hupper : β + p.α *
      (civicWeightedGradient p ρ β D + doublingControl p ρ β D) ≤ 1) :
    β < (controlledCivicWeightedStep p ρ (doublingControl p ρ β D) (β, D)).1 := by
  have hmax : max (-civicWeightedGradient p ρ β D) 0 =
      -civicWeightedGradient p ρ β D :=
    max_eq_left (neg_nonneg.mpr hgradient.le)
  have hnet : civicWeightedGradient p ρ β D + doublingControl p ρ β D =
      -civicWeightedGradient p ρ β D := by
    rw [doublingControl, hmax]
    ring
  have hincrease : β < β + p.α * (-civicWeightedGradient p ρ β D) := by
    nlinarith [model.α_pos, neg_pos.mpr hgradient]
  have hinputMem : β + p.α *
      (civicWeightedGradient p ρ β D + doublingControl p ρ β D) ∈
        Icc (0 : ℝ) 1 := by
    rw [hnet]
    exact ⟨hβ.1.trans hincrease.le, by simpa only [hnet] using hupper⟩
  simp only [controlledCivicWeightedStep]
  rw [clipUnit_eq_self hinputMem]
  simpa only [hnet] using hincrease

/-! ## The ε-margin climb -/

/-- The climb phase in the statement of `prop:qpbounds`: double the
negative part of the weighted gradient and add a strictly positive margin. -/
def marginClimbControl (p : LoopParams) (ρ ε : ℝ) (x : LoopState) : ℝ :=
  doublingControl p ρ x.1 x.2 + ε

/-- The autonomous feedback step generated by `marginClimbControl`. -/
def marginClimbStep (p : LoopParams) (ρ ε : ℝ) (x : LoopState) : LoopState :=
  controlledCivicWeightedStep p ρ (marginClimbControl p ρ ε x) x

/-- The ε-margin climb, started at the calibrated corner. -/
def marginClimbPath (p : LoopParams) (ρ ε : ℝ) (n : ℕ) : LoopState :=
  ((marginClimbStep p ρ ε)^[n]) (calibratedPoint p)

/-- The feedback controls along the ε-margin climb. -/
def marginClimbControlSequence (p : LoopParams) (ρ ε : ℝ) (n : ℕ) : ℝ :=
  marginClimbControl p ρ ε (marginClimbPath p ρ ε n)

@[simp]
theorem marginClimbPath_zero (p : LoopParams) (ρ ε : ℝ) :
    marginClimbPath p ρ ε 0 = calibratedPoint p := by
  simp only [marginClimbPath, Function.iterate_zero_apply]

@[simp]
theorem marginClimbPath_succ (p : LoopParams) (ρ ε : ℝ) (n : ℕ) :
    marginClimbPath p ρ ε (n + 1) =
      controlledCivicWeightedStep p ρ
        (marginClimbControlSequence p ρ ε n) (marginClimbPath p ρ ε n) := by
  simp only [marginClimbPath, marginClimbStep, marginClimbControlSequence,
    Function.iterate_succ_apply']

/-- The feedback orbit is a controlled path in the exact sense used to define
the finite-path quasipotential. -/
theorem marginClimbPath_isControlled (p : LoopParams) (ρ ε : ℝ) :
    IsControlledCivicWeightedPath p ρ (marginClimbControlSequence p ρ ε)
      (marginClimbPath p ρ ε) := by
  constructor
  · exact marginClimbPath_zero p ρ ε
  · exact marginClimbPath_succ p ρ ε

/-- Doubling the negative part turns the controlled gradient into an absolute
gradient, so the climb's net gradient is at least its positive margin. -/
theorem marginClimb_net_gradient_ge (p : LoopParams) (ρ ε : ℝ)
    (x : LoopState) :
    ε ≤ civicWeightedGradient p ρ x.1 x.2 + marginClimbControl p ρ ε x := by
  unfold marginClimbControl doublingControl
  by_cases hgradient : 0 ≤ civicWeightedGradient p ρ x.1 x.2
  · rw [max_eq_right (neg_nonpos.mpr hgradient)]
    linarith
  · have hgradient' : civicWeightedGradient p ρ x.1 x.2 < 0 :=
      lt_of_not_ge hgradient
    rw [max_eq_left (neg_nonneg.mpr hgradient'.le)]
    linarith

/-- Policy is nondecreasing throughout the ε-margin climb. -/
theorem monotone_marginClimbPolicy {p : LoopParams}
    (model : DriftModelAssumptions p) (ρ ε : ℝ) (hε : 0 ≤ ε) :
    Monotone (fun n ↦ (marginClimbPath p ρ ε n).1) := by
  apply monotone_nat_of_le_succ
  intro n
  let x := marginClimbPath p ρ ε n
  have hx : x.1 ∈ Icc (0 : ℝ) 1 :=
    (marginClimbPath_isControlled p ρ ε).policy_mem n
  have hnet := marginClimb_net_gradient_ge p ρ ε x
  have hraw : x.1 ≤ x.1 + p.α *
      (civicWeightedGradient p ρ x.1 x.2 + marginClimbControl p ρ ε x) := by
    nlinarith [model.α_pos]
  rw [marginClimbPath_succ]
  simp only [controlledCivicWeightedStep, marginClimbControlSequence]
  calc
    (marginClimbPath p ρ ε n).1 =
        LoopParams.clipUnit (marginClimbPath p ρ ε n).1 :=
      (clipUnit_eq_self hx).symm
    _ ≤ LoopParams.clipUnit
        ((marginClimbPath p ρ ε n).1 + p.α *
          (civicWeightedGradient p ρ
              (marginClimbPath p ρ ε n).1
              (marginClimbPath p ρ ε n).2 +
            marginClimbControl p ρ ε (marginClimbPath p ρ ε n))) :=
      LoopParams.monotone_clipUnit hraw

/-- For a monotone sequence, the recursively defined running maximum is the
current value. -/
theorem runningMax_eq_of_monotone {a : ℕ → ℝ} (ha : Monotone a) (n : ℕ) :
    runningMax a n = a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [runningMax_succ, ih, max_eq_right (ha n.le_succ)]

/-- A positive climb margin forces the policy across the weighted saddle in
finite time. This is the finite-crossing content missing from the original
unmargined strategy.

Paper II, Proposition `prop:qpbounds`, civic_drift.tex:354. -/
theorem marginClimbPath_eventually_crosses
    {p : LoopParams} (model : DriftModelAssumptions p)
    {ρ ε : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (hε : 0 < ε) :
    ∃ N, weighted.βdagger < (marginClimbPath p ρ ε N).1 := by
  let β : ℕ → ℝ := fun n ↦ (marginClimbPath p ρ ε n).1
  let δ : ℝ := min (p.α * ε) ((1 - weighted.βdagger) / 2)
  have hgap : 0 < 1 - weighted.βdagger := sub_pos.mpr weighted.βdagger_mem.2
  have hδpos : 0 < δ := by
    dsimp only [δ]
    exact lt_min (mul_pos model.α_pos hε) (half_pos hgap)
  have hδα : δ ≤ p.α * ε := by
    exact min_le_left _ _
  have hδgap : δ ≤ (1 - weighted.βdagger) / 2 := by
    exact min_le_right _ _
  by_contra hnever
  push Not at hnever
  have hstep : ∀ n, β n + δ ≤ β (n + 1) := by
    intro n
    have hβmem : β n ∈ Icc (0 : ℝ) 1 :=
      (marginClimbPath_isControlled p ρ ε).policy_mem n
    have hβroot : β n ≤ weighted.βdagger := hnever n
    have htargetMem : β n + δ ∈ Icc (0 : ℝ) 1 := by
      constructor
      · nlinarith [hβmem.1, hδpos]
      · nlinarith [hβroot, hδgap, hgap]
    have hnet := marginClimb_net_gradient_ge p ρ ε
      (marginClimbPath p ρ ε n)
    have hraw : β n + δ ≤ β n + p.α *
        (civicWeightedGradient p ρ
            (marginClimbPath p ρ ε n).1
            (marginClimbPath p ρ ε n).2 +
          marginClimbControl p ρ ε (marginClimbPath p ρ ε n)) := by
      dsimp only [β]
      nlinarith [model.α_pos]
    change (marginClimbPath p ρ ε n).1 + δ ≤
      (marginClimbPath p ρ ε (n + 1)).1
    rw [marginClimbPath_succ]
    simp only [controlledCivicWeightedStep, marginClimbControlSequence]
    calc
      β n + δ = LoopParams.clipUnit (β n + δ) :=
        (clipUnit_eq_self htargetMem).symm
      _ ≤ LoopParams.clipUnit
          ((marginClimbPath p ρ ε n).1 + p.α *
            (civicWeightedGradient p ρ
                (marginClimbPath p ρ ε n).1
                (marginClimbPath p ρ ε n).2 +
              marginClimbControl p ρ ε (marginClimbPath p ρ ε n))) :=
        LoopParams.monotone_clipUnit (by simpa only [β] using hraw)
  have hlinear : ∀ n : ℕ, (n : ℝ) * δ ≤ β n := by
    intro n
    induction n with
    | zero =>
        simp only [Nat.cast_zero, zero_mul, β, marginClimbPath_zero,
          calibratedPoint]
        norm_num
    | succ n ih =>
        have hn := hstep n
        norm_num [Nat.cast_succ] at ⊢
        nlinarith
  obtain ⟨N, hN⟩ := exists_nat_gt (weighted.βdagger / δ)
  have hroot_lt : weighted.βdagger < (N : ℝ) * δ :=
    (div_lt_iff₀ hδpos).mp hN
  linarith [hlinear N, hnever N]

/-- An interior lower endpoint remains strictly below the unit-interval
projection of every strictly larger input. -/
theorem lt_clipUnit_of_mem_Ico_of_lt {a z : ℝ}
    (ha : a ∈ Ico (0 : ℝ) 1) (haz : a < z) :
    a < LoopParams.clipUnit z := by
  by_cases hz : z ≤ 1
  · rw [clipUnit_eq_self ⟨ha.1.trans haz.le, hz⟩]
    exact haz
  · rw [(clipUnit_eq_one_iff z).2 (not_le.mp hz).le]
    exact ha.2

/-- Before the weighted saddle, a climb step which has not yet crossed gains
strictly more than `αε` in policy.  The strictness comes from the negative
uncontrolled gradient: doubling its negative part adds `|gρ|` on top of the
margin. -/
theorem marginClimbPath_increment_gt_margin_of_not_crossed
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ ε : ℝ}
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε) (n : ℕ)
    (hcurrent : (marginClimbPath p ρ ε n).1 < weighted.βdagger)
    (hnext : (marginClimbPath p ρ ε (n + 1)).1 ≤ weighted.βdagger) :
    p.α * ε <
      (marginClimbPath p ρ ε (n + 1)).1 -
        (marginClimbPath p ρ ε n).1 := by
  let x := marginClimbPath p ρ ε n
  let z := x.1 + p.α *
    (civicWeightedGradient p ρ x.1 x.2 + marginClimbControl p ρ ε x)
  have path := marginClimbPath_isControlled p ρ ε
  have hmono := monotone_marginClimbPolicy model ρ ε hε.le
  have hxmem : x.1 ∈ Icc (0 : ℝ) 1 := path.policy_mem n
  have hmax : policyRunningMax (marginClimbPath p ρ ε) n = x.1 := by
    simp only [policyRunningMax, x]
    exact runningMax_eq_of_monotone hmono n
  have hgradient_le : civicWeightedGradient p ρ x.1 x.2 ≤
      weightedStationaryGradient p ρ x.1 := by
    have h := path.gradient_le_runningMax model ss hcoop n
    simpa only [hmax, sub_self, mul_zero, add_zero, x] using h
  have hstationary_neg : weightedStationaryGradient p ρ x.1 < 0 := by
    have hbarrier := weighted.barrier_pos_before
      ⟨hxmem.1, hcurrent.le⟩ hcurrent
    simpa only [weightedBarrierIntegrand, neg_pos] using hbarrier
  have hgradient_neg : civicWeightedGradient p ρ x.1 x.2 < 0 :=
    hgradient_le.trans_lt hstationary_neg
  have hcontrol : marginClimbControl p ρ ε x =
      2 * (-civicWeightedGradient p ρ x.1 x.2) + ε := by
    simp only [marginClimbControl, doublingControl]
    rw [max_eq_left (neg_nonneg.mpr hgradient_neg.le)]
  have hraw_gain : x.1 + p.α * ε < z := by
    dsimp only [z]
    rw [hcontrol]
    nlinarith [model.α_pos, neg_pos.mpr hgradient_neg]
  have hnext_eq : (marginClimbPath p ρ ε (n + 1)).1 =
      LoopParams.clipUnit z := by
    rw [marginClimbPath_succ]
    rfl
  have hzle : z ≤ 1 := by
    by_contra hz
    have hzone : LoopParams.clipUnit z = 1 :=
      (clipUnit_eq_one_iff z).2 (not_le.mp hz).le
    rw [hnext_eq, hzone] at hnext
    linarith [weighted.βdagger_mem.2]
  have hzmem : z ∈ Icc (0 : ℝ) 1 := by
    have hαε : 0 < p.α * ε := mul_pos model.α_pos hε
    have hxz : x.1 < z :=
      (lt_add_of_pos_right x.1 hαε).trans hraw_gain
    exact ⟨hxmem.1.trans hxz.le, hzle⟩
  rw [hnext_eq, clipUnit_eq_self hzmem]
  exact (lt_sub_iff_add_lt).2 (by
    simpa only [add_comm, x] using hraw_gain)

/-- The printed quantitative crossing bound: the climb has crossed
by `⌈β†ρ/(αε)⌉` steps. -/
theorem marginClimbPath_crosses_by_natCeil
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ ε : ℝ}
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε) :
    weighted.βdagger <
      (marginClimbPath p ρ ε
        (Nat.ceil (weighted.βdagger / (p.α * ε)))).1 := by
  let N : ℕ := Nat.ceil (weighted.βdagger / (p.α * ε))
  let β : ℕ → ℝ := fun n ↦ (marginClimbPath p ρ ε n).1
  have hαε : 0 < p.α * ε := mul_pos model.α_pos hε
  have hratio : 0 < weighted.βdagger / (p.α * ε) :=
    div_pos weighted.βdagger_mem.1 hαε
  have hNpos : 0 < N := by
    exact Nat.ceil_pos.mpr hratio
  have hmono := monotone_marginClimbPolicy model ρ ε hε.le
  by_contra hnot
  have hNroot : β N ≤ weighted.βdagger := by
    simpa only [β, N] using le_of_not_gt hnot
  have hbefore : ∀ k < N, β k < weighted.βdagger := by
    intro k hk
    have hkN : β k ≤ β N := hmono hk.le
    have hkle : β k ≤ weighted.βdagger := hkN.trans hNroot
    apply lt_of_le_of_ne hkle
    intro heq
    have hk1N : k + 1 ≤ N := by omega
    have hnextle : β (k + 1) ≤ weighted.βdagger :=
      (hmono hk1N).trans hNroot
    have hnet := marginClimb_net_gradient_ge p ρ ε
      (marginClimbPath p ρ ε k)
    have hraw : weighted.βdagger <
        weighted.βdagger + p.α *
          (civicWeightedGradient p ρ
              (marginClimbPath p ρ ε k).1
              (marginClimbPath p ρ ε k).2 +
            marginClimbControl p ρ ε (marginClimbPath p ρ ε k)) := by
      nlinarith [model.α_pos]
    have hclip := lt_clipUnit_of_mem_Ico_of_lt
      ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2⟩ hraw
    have heq' : (marginClimbPath p ρ ε k).1 = weighted.βdagger := by
      simpa only [β] using heq
    have hnextgt : weighted.βdagger < β (k + 1) := by
      dsimp only [β]
      rw [marginClimbPath_succ]
      simp only [controlledCivicWeightedStep, marginClimbControlSequence]
      simpa only [heq'] using hclip
    exact (not_lt_of_ge hnextle hnextgt).elim
  have hlinear : ∀ k ≤ N, (k : ℝ) * (p.α * ε) ≤ β k := by
    intro k hk
    induction k with
    | zero =>
        simp only [Nat.cast_zero, zero_mul, β, marginClimbPath_zero,
          calibratedPoint]
        norm_num
    | succ k ih =>
        have hklt : k < N := by omega
        have hnextle : β (k + 1) ≤ weighted.βdagger :=
          (hmono hk).trans hNroot
        have hinc := marginClimbPath_increment_gt_margin_of_not_crossed
          model ss hcoop weighted hε k (hbefore k hklt) (by
            simpa only [β] using hnextle)
        have ih' := ih (by omega)
        norm_num [Nat.cast_succ] at ⊢
        dsimp only [β] at ih' ⊢
        nlinarith
  let k : ℕ := N - 1
  have hNk : N = k + 1 := by
    dsimp only [k]
    omega
  have hkN : k < N := by omega
  have hklinear := hlinear k hkN.le
  have hNinc := marginClimbPath_increment_gt_margin_of_not_crossed
    model ss hcoop weighted hε k (hbefore k hkN) (by
      simpa only [β, ← hNk] using hNroot)
  have hstrict : (N : ℝ) * (p.α * ε) < β N := by
    rw [hNk]
    norm_num [Nat.cast_succ]
    dsimp only [β] at hklinear hNinc ⊢
    nlinarith
  have hceil : weighted.βdagger / (p.α * ε) ≤ (N : ℝ) := by
    simpa only [N] using
      (Nat.le_ceil (weighted.βdagger / (p.α * ε)) :
        weighted.βdagger / (p.α * ε) ≤
          (Nat.ceil (weighted.βdagger / (p.α * ε)) : ℝ))
  have hroot_le : weighted.βdagger ≤ (N : ℝ) * (p.α * ε) := by
    calc
      weighted.βdagger =
          (weighted.βdagger / (p.α * ε)) * (p.α * ε) :=
        (div_mul_cancel₀ weighted.βdagger hαε.ne').symm
      _ ≤ (N : ℝ) * (p.α * ε) :=
        mul_le_mul_of_nonneg_right hceil hαε.le
  exact (not_lt_of_ge hNroot (hroot_le.trans_lt hstrict)).elim

/-! ## The cancelling hold -/

/-- The stock path during a hold at policy `b`. -/
def cancellingHoldStockPath (p : LoopParams) (b D₀ : ℝ) (n : ℕ) : ℝ :=
  arithGeom (p.s b) p.I D₀ n

/-- The fixed-policy state path used during the cancelling hold. -/
def cancellingHoldPath (p : LoopParams) (b D₀ : ℝ) (n : ℕ) : LoopState :=
  (b, cancellingHoldStockPath p b D₀ n)

/-- The literal positive-part cancelling control printed in `prop:qpbounds`. -/
def cancellingHoldControl (p : LoopParams) (ρ b D₀ : ℝ) (n : ℕ) : ℝ :=
  max (-civicWeightedGradient p ρ b (cancellingHoldStockPath p b D₀ n)) 0

/-- The weighted gradient evaluated along the fixed-policy hold path. -/
def cancellingHoldGradient (p : LoopParams) (ρ b D₀ : ℝ) (n : ℕ) : ℝ :=
  civicWeightedGradient p ρ b (cancellingHoldStockPath p b D₀ n)

@[simp]
theorem cancellingHoldStockPath_zero (p : LoopParams) (b D₀ : ℝ) :
    cancellingHoldStockPath p b D₀ 0 = D₀ := by
  simp only [cancellingHoldStockPath, arithGeom_zero]

@[simp]
theorem cancellingHoldPath_zero (p : LoopParams) (b D₀ : ℝ) :
    cancellingHoldPath p b D₀ 0 = (b, D₀) := by
  simp only [cancellingHoldPath, cancellingHoldStockPath_zero]

/-- The held stock follows the exact, uncontrolled stock recursion. -/
theorem cancellingHoldStockPath_succ {p : LoopParams}
    (model : DriftModelAssumptions p) {b D₀ : ℝ} (n : ℕ) :
    p.stockStep b (cancellingHoldStockPath p b D₀ n) =
      cancellingHoldStockPath p b D₀ (n + 1) := by
  simp only [cancellingHoldStockPath, LoopParams.stockStep,
    model.no_content_gain, add_zero, arithGeom_succ]

/-- While the weighted gradient is nonpositive, the positive-part control is
exactly its negative and pins policy while leaving the stock law untouched. -/
theorem cancellingHoldPath_step_of_gradient_nonpos
    {p : LoopParams} (model : DriftModelAssumptions p)
    {ρ b D₀ : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (n : ℕ)
    (hgradient : cancellingHoldGradient p ρ b D₀ n ≤ 0) :
    cancellingHoldPath p b D₀ (n + 1) =
      controlledCivicWeightedStep p ρ
        (cancellingHoldControl p ρ b D₀ n) (cancellingHoldPath p b D₀ n) := by
  have hcontrol : cancellingHoldControl p ρ b D₀ n =
      -cancellingHoldGradient p ρ b D₀ n := by
    simp only [cancellingHoldControl, cancellingHoldGradient]
    exact max_eq_left (neg_nonneg.mpr hgradient)
  apply Prod.ext
  · simp only [cancellingHoldPath, controlledCivicWeightedStep,
      hcontrol, cancellingHoldGradient]
    rw [add_neg_cancel, mul_zero, add_zero, clipUnit_eq_self hb]
  · simp only [cancellingHoldPath, controlledCivicWeightedStep]
    exact (cancellingHoldStockPath_succ model n).symm

/-- A fixed-policy hold stock converges geometrically to the stationary
characteristic at that policy. -/
theorem cancellingHoldStockPath_tendsto
    {p : LoopParams} (model : DriftModelAssumptions p)
    {b D₀ : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) :
    Tendsto (cancellingHoldStockPath p b D₀) atTop
      (𝓝 (p.stationaryStock b)) := by
  have hs := driftStockMultiplier_nonneg_le model hb
  have hlim := tendsto_affineRecursion (p.s b) p.I D₀ hs.1
    (hs.2.trans_lt (sub_lt_self 1 model.lambda₀_pos))
  change Tendsto (arithGeom (p.s b) p.I D₀) atTop
    (𝓝 (p.stationaryStock b))
  simpa only [cancellingHoldStockPath, LoopParams.stationaryStock,
    model.no_content_gain, sub_zero] using hlim

/-- Above the weighted saddle, including the captured endpoint, the
stationary weighted gradient is strictly positive. -/
theorem WeightedThresholdAssumption.gradient_pos_of_mem_Ioc
    {p : LoopParams} {ρ b : ℝ}
    (weighted : WeightedThresholdAssumption p ρ)
    (hb : b ∈ Ioc weighted.βdagger 1) :
    0 < weightedStationaryGradient p ρ b := by
  by_cases hone : b = 1
  · simpa only [hone] using weighted.gradient_one_pos
  · exact weighted.gradient_pos_after b
      ⟨weighted.βdagger_mem.1.trans hb.1,
        lt_of_le_of_ne hb.2 hone⟩ hb.1

/-- The held gradient converges to the positive on-characteristic gradient. -/
theorem cancellingHoldGradient_tendsto
    {p : LoopParams} (model : DriftModelAssumptions p)
    {ρ b D₀ : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) :
    Tendsto (cancellingHoldGradient p ρ b D₀) atTop
      (𝓝 (weightedStationaryGradient p ρ b)) := by
  have hstock := cancellingHoldStockPath_tendsto model (D₀ := D₀) hb
  have hcontinuous : Continuous
      (fun D : ℝ ↦ civicWeightedGradient p ρ b D) := by
    unfold civicWeightedGradient LoopParams.gradU
    fun_prop
  have hlim := hcontinuous.continuousAt.tendsto.comp hstock
  change Tendsto
    (fun n ↦ civicWeightedGradient p ρ b (cancellingHoldStockPath p b D₀ n))
      atTop (𝓝 (civicWeightedGradient p ρ b (p.stationaryStock b))) at hlim
  rw [civicWeightedGradient_stationary_eq_weightedStationaryGradient ρ hb] at hlim
  exact hlim

/-- The cancelling hold reaches a strictly positive gradient in finite time. -/
theorem cancellingHoldGradient_eventually_positive
    {p : LoopParams} (model : DriftModelAssumptions p)
    {ρ b D₀ : ℝ} (hb : b ∈ Icc (0 : ℝ) 1)
    (hstationary : 0 < weightedStationaryGradient p ρ b) :
    ∃ n, 0 < cancellingHoldGradient p ρ b D₀ n := by
  have hlim := cancellingHoldGradient_tendsto model (ρ := ρ) (D₀ := D₀) hb
  exact (hlim.eventually_const_lt hstationary).exists

/-- The first index at which a real sequence is positive, with zero as a
total fallback when no such index exists. -/
noncomputable def firstPositiveIndex (a : ℕ → ℝ) : ℕ :=
  by
    classical
    exact if h : ∃ n, 0 < a n then Nat.find h else 0

theorem firstPositiveIndex_spec {a : ℕ → ℝ} (h : ∃ n, 0 < a n) :
    0 < a (firstPositiveIndex a) := by
  classical
  rw [firstPositiveIndex, dif_pos h]
  exact Nat.find_spec h

theorem firstPositiveIndex_nonpos_before {a : ℕ → ℝ}
    (h : ∃ n, 0 < a n) {k : ℕ} (hk : k < firstPositiveIndex a) :
    a k ≤ 0 := by
  classical
  rw [firstPositiveIndex, dif_pos h] at hk
  exact le_of_not_gt (Nat.find_min h hk)

/-- Canonical stopping time for the cancelling hold. -/
noncomputable def cancellingHoldStop
    (p : LoopParams) (ρ b D₀ : ℝ) : ℕ :=
  firstPositiveIndex (cancellingHoldGradient p ρ b D₀)

theorem cancellingHoldStop_gradient_pos
    {p : LoopParams} (model : DriftModelAssumptions p)
    {ρ b D₀ : ℝ} (hb : b ∈ Icc (0 : ℝ) 1)
    (hstationary : 0 < weightedStationaryGradient p ρ b) :
    0 < cancellingHoldGradient p ρ b D₀
      (cancellingHoldStop p ρ b D₀) := by
  apply firstPositiveIndex_spec
  exact cancellingHoldGradient_eventually_positive model hb hstationary

theorem cancellingHoldStop_gradient_nonpos_before
    {p : LoopParams} (model : DriftModelAssumptions p)
    {ρ b D₀ : ℝ} (hb : b ∈ Icc (0 : ℝ) 1)
    (hstationary : 0 < weightedStationaryGradient p ρ b)
    {k : ℕ} (hk : k < cancellingHoldStop p ρ b D₀) :
    cancellingHoldGradient p ρ b D₀ k ≤ 0 := by
  apply firstPositiveIndex_nonpos_before
  · exact cancellingHoldGradient_eventually_positive model hb hstationary
  · simpa only [cancellingHoldStop] using hk

/-- Every pre-stop hold step is exactly the printed positive-part controlled
step. -/
theorem cancellingHoldPath_step_before_stop
    {p : LoopParams} (model : DriftModelAssumptions p)
    {ρ b D₀ : ℝ} (hb : b ∈ Icc (0 : ℝ) 1)
    (hstationary : 0 < weightedStationaryGradient p ρ b)
    {k : ℕ} (hk : k < cancellingHoldStop p ρ b D₀) :
    cancellingHoldPath p b D₀ (k + 1) =
      controlledCivicWeightedStep p ρ
        (cancellingHoldControl p ρ b D₀ k)
        (cancellingHoldPath p b D₀ k) :=
  cancellingHoldPath_step_of_gradient_nonpos model hb k
    (cancellingHoldStop_gradient_nonpos_before model hb hstationary hk)

/-- At the first positive held gradient, the state dominates a point on the
stationary characteristic strictly beyond the weighted saddle.  Thus the
printed dominate-then-capture stopping condition is reached in finite time. -/
theorem cancellingHoldStop_dominates_characteristic
    {p : LoopParams} (model : DriftModelAssumptions p)
    {ρ b D₀ : ℝ} (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (hb : b ∈ Ioc weighted.βdagger 1) :
    ∃ r ∈ Ioc weighted.βdagger b,
      (r, p.stationaryStock r) ≤
        cancellingHoldPath p b D₀ (cancellingHoldStop p ρ b D₀) := by
  let T := cancellingHoldStop p ρ b D₀
  let D := cancellingHoldStockPath p b D₀ T
  have hbclosed : b ∈ Icc (0 : ℝ) 1 :=
    ⟨weighted.βdagger_mem.1.le.trans hb.1.le, hb.2⟩
  have hstationary : 0 < weightedStationaryGradient p ρ b :=
    weighted.gradient_pos_of_mem_Ioc hb
  have hgradient : 0 < civicWeightedGradient p ρ b D := by
    simpa only [cancellingHoldGradient, T, D] using
      cancellingHoldStop_gradient_pos model hbclosed hstationary
  let A : ℝ := 2 * p.c * (1 - p.c * b) - ρ
  have hA_nonneg : 0 ≤ A := by
    simpa only [A] using weighted_stock_coefficient_nonnegative model hcoop hbclosed
  have hADpos : 0 < A * D := by
    simp only [civicWeightedGradient, LoopParams.gradU] at hgradient
    nlinarith [model.v_pos]
  have hApos : 0 < A := by
    rcases lt_or_eq_of_le hA_nonneg with hpos | hzero
    · exact hpos
    · rw [← hzero, zero_mul] at hADpos
      exact (lt_irrefl 0 hADpos).elim
  let r₀ := weighted.βdagger
  let D₀root := p.stationaryStock r₀
  have hr₀closed : r₀ ∈ Icc (0 : ℝ) 1 :=
    ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩
  have hD₀root_pos : 0 < D₀root := by
    exact model.I_pos.trans_le (stationaryStock_mem_stockInterval model hr₀closed).1
  have hrootzero : civicWeightedGradient p ρ r₀ D₀root = 0 := by
    rw [civicWeightedGradient_stationary_eq_weightedStationaryGradient ρ hr₀closed]
    exact weighted.gradient_zero
  have hdrop : 0 < 2 * p.c ^ 2 * (b - r₀) * D₀root := by
    exact mul_pos (mul_pos (mul_pos two_pos (sq_pos_of_pos model.c_pos))
      (sub_pos.mpr hb.1)) hD₀root_pos
  have hbelow : civicWeightedGradient p ρ b D₀root < 0 := by
    have hid : civicWeightedGradient p ρ b D₀root =
        civicWeightedGradient p ρ r₀ D₀root -
          2 * p.c ^ 2 * (b - r₀) * D₀root := by
      simp only [civicWeightedGradient, LoopParams.gradU]
      ring
    rw [hid, hrootzero]
    linarith
  have hDroot_lt : D₀root < D := by
    have hmul : A * D₀root < A * D := by
      simp only [civicWeightedGradient, LoopParams.gradU] at hbelow hgradient
      linarith
    exact lt_of_mul_lt_mul_left hmul hApos.le
  have hcontinuous : ContinuousAt p.stationaryStock r₀ :=
    (hasDerivAt_stationaryStock_zeroGain model hr₀closed).continuousAt
  have heventually : ∀ᶠ r in 𝓝 r₀, p.stationaryStock r < D :=
    hcontinuous.tendsto.eventually_lt_const hDroot_lt
  obtain ⟨δ, hδpos, hball⟩ := Metric.mem_nhds_iff.mp heventually
  let d : ℝ := min (δ / 2) ((b - r₀) / 2)
  let r : ℝ := r₀ + d
  have hdpos : 0 < d := by
    dsimp only [d]
    exact lt_min (half_pos hδpos) (half_pos (sub_pos.mpr hb.1))
  have hdδ : d < δ := by
    have : δ / 2 < δ := by linarith
    exact (min_le_left (δ / 2) ((b - r₀) / 2)).trans_lt this
  have hdgap : d ≤ (b - r₀) / 2 := min_le_right _ _
  have hr : r ∈ Ioc r₀ b := by
    dsimp only [r]
    constructor
    · linarith
    · linarith
  have hdist : dist r r₀ < δ := by
    rw [Real.dist_eq, abs_of_nonneg]
    · simpa only [r, add_sub_cancel_left] using hdδ
    · dsimp only [r]
      linarith
  have hstock : p.stationaryStock r ≤ D := (hball hdist).le
  refine ⟨r, ?_, ?_⟩
  · simpa only [r₀] using hr
  · simpa only [cancellingHoldPath, T, D] using
      (show (r, p.stationaryStock r) ≤ (b, D) from ⟨hr.2, hstock⟩)

/-- A fixed-policy hold remains in the Paper II invariant box whenever its
initial stock does. -/
theorem cancellingHoldPath_mem_absorbingBox
    {p : LoopParams} (model : DriftModelAssumptions p)
    {b D₀ : ℝ} (hb : b ∈ Icc (0 : ℝ) 1)
    (hD₀ : D₀ ∈ Icc p.I (p.I / p.lambda₀)) (n : ℕ) :
    cancellingHoldPath p b D₀ n ∈ absorbingBox p := by
  constructor
  · exact hb
  · induction n with
    | zero =>
        simpa only [cancellingHoldPath, cancellingHoldStockPath_zero] using hD₀
    | succ n ih =>
        have hnext := (invariantBox model
          (show (b, cancellingHoldStockPath p b D₀ n) ∈ absorbingBox p from
            ⟨hb, ih⟩)).2
        simpa only [cancellingHoldPath, LoopParams.loopMap,
          cancellingHoldStockPath_succ model n] using hnext

/-- Any state in the invariant box which dominates an on-characteristic point
strictly beyond the weighted saddle converges to capture under the unforced
constant-weight map. -/
theorem civicWeightedOrbit_tendsto_captured_of_dominates_characteristic
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ r : ℝ}
    (hρcure : ρ < cureThreshold p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (hr : r ∈ Ioc weighted.βdagger 1) {x₀ : LoopState}
    (hx₀ : x₀ ∈ absorbingBox p)
    (hdom : (r, p.stationaryStock r) ≤ x₀) :
    Tendsto (civicWeightedOrbit p ρ x₀) atTop (𝓝 (capturedPoint p)) := by
  have hrclosed : r ∈ Icc (0 : ℝ) 1 :=
    ⟨weighted.βdagger_mem.1.le.trans hr.1.le, hr.2⟩
  let r' : ℝ := (weighted.βdagger + r) / 2
  have hr'root : weighted.βdagger < r' := by
    dsimp only [r']
    nlinarith [hr.1]
  have hr'r : r' < r := by
    dsimp only [r']
    nlinarith [hr.1]
  have hr'closed : r' ∈ Icc (0 : ℝ) 1 :=
    ⟨weighted.βdagger_mem.1.le.trans hr'root.le,
      hr'r.le.trans hr.2⟩
  have hcharacteristic_le :
      (r', p.stationaryStock r') ≤ (r, p.stationaryStock r) := by
    exact ⟨hr'r.le,
      (stationaryStock_strictMonoOn model hr'closed hrclosed hr'r).le⟩
  have hdom' : (r', p.stationaryStock r') ≤ x₀ :=
    hcharacteristic_le.trans hdom
  have hpositive : ∀ β ∈ Icc r' 1,
      0 < civicWeightedGradient p ρ β (p.stationaryStock β) := by
    intro β hβ
    have hβclosed : β ∈ Icc (0 : ℝ) 1 :=
      ⟨hr'closed.1.trans hβ.1, hβ.2⟩
    rw [civicWeightedGradient_stationary_eq_weightedStationaryGradient ρ hβclosed]
    exact weighted.gradient_pos_of_mem_Ioc ⟨hr'root.trans_le hβ.1, hβ.2⟩
  let lower : LoopState := (r', p.stationaryStock r')
  let lowerOrbit := civicWeightedOrbit p ρ lower
  let upperOrbit := civicWeightedOrbit p ρ x₀
  have hlowerMem : lower ∈ absorbingBox p :=
    ⟨hr'closed, stationaryStock_mem_stockInterval model hr'closed⟩
  have hlowerTraj : IsCivicWeightedTrajectory p ρ lowerOrbit :=
    civicWeightedOrbit_isTrajectory p ρ lower
  have hupperTraj : IsCivicWeightedTrajectory p ρ upperOrbit :=
    civicWeightedOrbit_isTrajectory p ρ x₀
  have hlowerBox := civicWeightedTrajectory_mem_absorbingBox model hlowerTraj hlowerMem
  have hupperBox := civicWeightedTrajectory_mem_absorbingBox model hupperTraj hx₀
  have hmapMono := civicWeightedLoopMap_monotoneOn_box model ss hcoop
  have hlower_le : ∀ n, lowerOrbit n ≤ upperOrbit n := by
    intro n
    induction n with
    | zero => simpa only [lowerOrbit, upperOrbit, civicWeightedOrbit,
        Function.iterate_zero_apply, lower] using hdom'
    | succ n ih =>
        rw [hlowerTraj n, hupperTraj n]
        exact hmapMono (hlowerBox n) (hupperBox n) ih
  have hcapturedMem : capturedPoint p ∈ absorbingBox p := by
    exact ⟨by simp [capturedPoint], by
      simpa only [capturedPoint] using
        stationaryStock_mem_stockInterval model
          (show (1 : ℝ) ∈ Icc 0 1 by norm_num)⟩
  have hcapturedFixed : IsCivicWeightedEquilibrium p ρ 1
      (p.stationaryStock 1) :=
    (civicWeighted_captured_fixed_iff model ρ).2 hρcure.le
  have hstationaryOne : p.stationaryStock 1 = p.I / p.lambda₀ := by
    simp only [LoopParams.stationaryStock, model.no_content_gain,
      LoopParams.s, mul_one, sub_self, mul_zero, sub_zero, one_pow]
    congr 1
    ring
  have hupper_le : ∀ n, upperOrbit n ≤ capturedPoint p := by
    intro n
    induction n with
    | zero =>
        constructor
        · simpa only [upperOrbit, civicWeightedOrbit,
            Function.iterate_zero_apply, capturedPoint] using hx₀.1.2
        · simpa only [upperOrbit, civicWeightedOrbit,
            Function.iterate_zero_apply, capturedPoint, hstationaryOne] using hx₀.2.2
    | succ n ih =>
        rw [hupperTraj n]
        have hstep := hmapMono (hupperBox n) hcapturedMem ih
        simpa only [IsCivicWeightedEquilibrium, capturedPoint] using
          hstep.trans_eq hcapturedFixed
  have hlowerLim : Tendsto lowerOrbit atTop (𝓝 (capturedPoint p)) :=
    civicWeightedOrbit_lower_tendsto_captured model ss
      ⟨weighted.βdagger_mem.1.trans hr'root,
        hr'r.trans_le hr.2⟩ hcoop hpositive
  have hpolicyLim : Tendsto (fun n ↦ (upperOrbit n).1) atTop
        (𝓝 (capturedPoint p).1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      ((continuous_fst.tendsto (capturedPoint p)).comp hlowerLim)
      tendsto_const_nhds (fun n ↦ (hlower_le n).1) (fun n ↦ (hupper_le n).1)
  have hstockLim : Tendsto (fun n ↦ (upperOrbit n).2) atTop
      (𝓝 (capturedPoint p).2) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      ((continuous_snd.tendsto (capturedPoint p)).comp hlowerLim)
      tendsto_const_nhds (fun n ↦ (hlower_le n).2) (fun n ↦ (hupper_le n).2)
  exact (Prod.tendsto_iff _ _).2 ⟨hpolicyLim, hstockLim⟩

/-- At every climb time, the exact stock lies below the stationary
characteristic at the current (monotone) policy. -/
theorem marginClimbPath_stock_le_stationaryStock
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    (marginClimbPath p ρ ε n).2 ≤
      p.stationaryStock (marginClimbPath p ρ ε n).1 := by
  let path := marginClimbPath_isControlled p ρ ε
  have hstock := path.stock_le_stationary_runningMax model ss n
  have hmax : policyRunningMax (marginClimbPath p ρ ε) n =
      (marginClimbPath p ρ ε n).1 := by
    simp only [policyRunningMax]
    exact runningMax_eq_of_monotone
      (monotone_marginClimbPolicy model ρ ε hε) n
  rwa [hmax] at hstock

/-! ## The complete two-phase upper strategy -/

/-- The first time the margin climb strictly exceeds the weighted saddle. -/
noncomputable def upperStrategyClimbStop
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (ε : ℝ) : ℕ :=
  firstPositiveIndex (fun n ↦
    (marginClimbPath p ρ ε n).1 - weighted.βdagger)

/-- The climb phase stops exactly at its first strict saddle crossing. -/
theorem upperStrategyClimbStop_crosses
    {p : LoopParams} (model : DriftModelAssumptions p)
    {ρ ε : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (hε : 0 < ε) :
    weighted.βdagger <
      (marginClimbPath p ρ ε (upperStrategyClimbStop weighted ε)).1 := by
  have hexists : ∃ n, 0 <
      (marginClimbPath p ρ ε n).1 - weighted.βdagger := by
    obtain ⟨n, hn⟩ := marginClimbPath_eventually_crosses model weighted hε
    exact ⟨n, sub_pos.mpr hn⟩
  have hfirst := firstPositiveIndex_spec hexists
  simpa only [upperStrategyClimbStop, sub_pos] using hfirst

/-- The first crossing occurs no later than the paper's quantitative
ceiling `⌈β†ρ/(αε)⌉`. -/
theorem upperStrategyClimbStop_le_natCeil
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ ε : ℝ}
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε) :
    upperStrategyClimbStop weighted ε ≤
      Nat.ceil (weighted.βdagger / (p.α * ε)) := by
  let N := Nat.ceil (weighted.βdagger / (p.α * ε))
  have hcross := marginClimbPath_crosses_by_natCeil
    model ss hcoop weighted hε
  have hexists : ∃ n, 0 <
      (marginClimbPath p ρ ε n).1 - weighted.βdagger :=
    ⟨N, by simpa only [N, sub_pos] using hcross⟩
  by_contra hnot
  have hNlt : N < upperStrategyClimbStop weighted ε :=
    Nat.lt_of_not_ge hnot
  have hbefore := firstPositiveIndex_nonpos_before hexists
    (by simpa only [upperStrategyClimbStop] using hNlt)
  have : (marginClimbPath p ρ ε N).1 ≤ weighted.βdagger := by
    linarith
  exact (not_lt_of_ge this (by simpa only [N] using hcross)).elim

/-- The state reached at the printed climb horizon. -/
def upperStrategyClimbState
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (ε : ℝ) : LoopState :=
  marginClimbPath p ρ ε (upperStrategyClimbStop weighted ε)

/-- The canonical length of the cancelling hold following the climb. -/
noncomputable def upperStrategyHoldStop
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (ε : ℝ) : ℕ :=
  cancellingHoldStop p ρ (upperStrategyClimbState weighted ε).1
    (upperStrategyClimbState weighted ε).2

/-- The finite stopping horizon of the complete climb-then-hold strategy. -/
noncomputable def upperStrategyTotalStop
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (ε : ℝ) : ℕ :=
  upperStrategyClimbStop weighted ε + upperStrategyHoldStop weighted ε

/-- Time-dependent feedback control: ε-margin climb, positive-part cancelling
hold, then zero control after the finite escape witness has been reached. -/
noncomputable def twoPhaseUpperControlAt
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (ε : ℝ) (n : ℕ) (x : LoopState) : ℝ :=
  if n < upperStrategyClimbStop weighted ε then
    marginClimbControl p ρ ε x
  else if n < upperStrategyTotalStop weighted ε then
    cancellingHoldControl p ρ (upperStrategyClimbState weighted ε).1
      (upperStrategyClimbState weighted ε).2
      (n - upperStrategyClimbStop weighted ε)
  else 0

/-- The full controlled trajectory generated by the two-phase
feedback, continued with zero control after its finite stopping horizon. -/
noncomputable def twoPhaseUpperPath
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (ε : ℝ) : ℕ → LoopState
  | 0 => calibratedPoint p
  | n + 1 =>
      let x := twoPhaseUpperPath weighted ε n
      controlledCivicWeightedStep p ρ
        (twoPhaseUpperControlAt weighted ε n x) x

/-- The realized control sequence along `twoPhaseUpperPath`. -/
noncomputable def twoPhaseUpperControl
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (ε : ℝ) (n : ℕ) : ℝ :=
  twoPhaseUpperControlAt weighted ε n (twoPhaseUpperPath weighted ε n)

@[simp]
theorem twoPhaseUpperPath_zero
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (ε : ℝ) :
    twoPhaseUpperPath weighted ε 0 = calibratedPoint p := rfl

@[simp]
theorem twoPhaseUpperPath_succ
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (ε : ℝ) (n : ℕ) :
    twoPhaseUpperPath weighted ε (n + 1) =
      controlledCivicWeightedStep p ρ (twoPhaseUpperControl weighted ε n)
        (twoPhaseUpperPath weighted ε n) := rfl

/-- The spliced feedback orbit is a genuine controlled path from the
calibrated corner. -/
theorem twoPhaseUpperPath_isControlled
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (ε : ℝ) :
    IsControlledCivicWeightedPath p ρ (twoPhaseUpperControl weighted ε)
      (twoPhaseUpperPath weighted ε) := by
  constructor
  · exact twoPhaseUpperPath_zero weighted ε
  · exact twoPhaseUpperPath_succ weighted ε

/-- Up to and including the climb horizon, the spliced path is exactly the
autonomous ε-margin climb. -/
theorem twoPhaseUpperPath_eq_marginClimb_of_le
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (ε : ℝ) {n : ℕ} (hn : n ≤ upperStrategyClimbStop weighted ε) :
    twoPhaseUpperPath weighted ε n = marginClimbPath p ρ ε n := by
  induction n with
  | zero => simp only [twoPhaseUpperPath_zero, marginClimbPath_zero]
  | succ n ih =>
      have hnlt : n < upperStrategyClimbStop weighted ε := by omega
      have ihn : n ≤ upperStrategyClimbStop weighted ε := by omega
      rw [twoPhaseUpperPath_succ, marginClimbPath_succ,
        twoPhaseUpperControl]
      simp only [twoPhaseUpperControlAt, if_pos hnlt,
        marginClimbControlSequence]
      rw [ih ihn]

/-- During the second phase, the spliced path is exactly the fixed-policy
cancelling hold through its canonical first-positive-gradient stop. -/
theorem twoPhaseUpperPath_eq_cancellingHold
    {p : LoopParams} (model : DriftModelAssumptions p)
    (_ss : SmallStepAssumption p) {ρ ε : ℝ}
    (_hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε)
    {k : ℕ} (hk : k ≤ upperStrategyHoldStop weighted ε) :
    twoPhaseUpperPath weighted ε
        (upperStrategyClimbStop weighted ε + k) =
      cancellingHoldPath p (upperStrategyClimbState weighted ε).1
        (upperStrategyClimbState weighted ε).2 k := by
  let N := upperStrategyClimbStop weighted ε
  let y := upperStrategyClimbState weighted ε
  let T := upperStrategyHoldStop weighted ε
  have hyAbove : weighted.βdagger < y.1 := by
    simpa only [y, upperStrategyClimbState, N] using
      upperStrategyClimbStop_crosses model weighted hε
  have hyMem : y.1 ∈ Icc (0 : ℝ) 1 := by
    dsimp only [y, upperStrategyClimbState]
    exact (marginClimbPath_isControlled p ρ ε).policy_mem
      (upperStrategyClimbStop weighted ε)
  have hyIoc : y.1 ∈ Ioc weighted.βdagger 1 := ⟨hyAbove, hyMem.2⟩
  have hstationary : 0 < weightedStationaryGradient p ρ y.1 :=
    weighted.gradient_pos_of_mem_Ioc hyIoc
  change twoPhaseUpperPath weighted ε (N + k) =
    cancellingHoldPath p y.1 y.2 k
  induction k with
  | zero =>
      have hprefix := twoPhaseUpperPath_eq_marginClimb_of_le weighted ε
        (n := N) (le_refl N)
      simpa only [Nat.add_zero, N, y, upperStrategyClimbState,
        cancellingHoldPath_zero] using hprefix
  | succ k ih =>
      have hklt : k < T := by
        dsimp only [T] at hk ⊢
        omega
      have hkT : k ≤ T := hklt.le
      have hNnot : ¬ N + k < N := by omega
      have hNnot' : ¬ N + k < upperStrategyClimbStop weighted ε := by
        simpa only [N] using hNnot
      have hphase : N + k < upperStrategyTotalStop weighted ε := by
        dsimp only [N, T, upperStrategyTotalStop]
        omega
      rw [Nat.add_succ, twoPhaseUpperPath_succ, twoPhaseUpperControl]
      simp only [twoPhaseUpperControlAt, if_neg hNnot', if_pos hphase]
      have hsub : N + k - upperStrategyClimbStop weighted ε = k := by
        dsimp only [N]
        omega
      rw [hsub, ih hkT]
      have hkStop : k < cancellingHoldStop p ρ y.1 y.2 := by
        simpa only [T, y, upperStrategyHoldStop] using hklt
      have hstep := cancellingHoldPath_step_before_stop
        (p := p) model (ρ := ρ) (b := y.1) (D₀ := y.2)
        hyMem hstationary hkStop
      simpa only [y] using hstep.symm

/-- The complete finite stopping state is the terminal cancelling-hold state. -/
theorem twoPhaseUpperPath_at_totalStop
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ ε : ℝ}
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε) :
    twoPhaseUpperPath weighted ε (upperStrategyTotalStop weighted ε) =
      cancellingHoldPath p (upperStrategyClimbState weighted ε).1
        (upperStrategyClimbState weighted ε).2
        (upperStrategyHoldStop weighted ε) := by
  simpa only [upperStrategyTotalStop] using
    twoPhaseUpperPath_eq_cancellingHold model ss hcoop weighted hε
      (k := upperStrategyHoldStop weighted ε) (le_refl _)

/-- The finite two-phase stopping state remains inside the invariant box. -/
theorem twoPhaseUpperPath_totalStop_mem_absorbingBox
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ ε : ℝ}
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε) :
    twoPhaseUpperPath weighted ε (upperStrategyTotalStop weighted ε) ∈
      absorbingBox p := by
  let y := upperStrategyClimbState weighted ε
  have hyMem : y ∈ absorbingBox p := by
    dsimp only [y, upperStrategyClimbState]
    exact (marginClimbPath_isControlled p ρ ε).mem_absorbingBox model
      (upperStrategyClimbStop weighted ε)
  have hhold := cancellingHoldPath_mem_absorbingBox model hyMem.1 hyMem.2
    (upperStrategyHoldStop weighted ε)
  rw [twoPhaseUpperPath_at_totalStop model ss hcoop weighted hε]
  simpa only [y] using hhold

/-- The finite two-phase stopping state satisfies the paper's literal
dominate-an-above-saddle-characteristic stopping condition. -/
theorem twoPhaseUpperPath_totalStop_dominates_characteristic
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ ε : ℝ}
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε) :
    ∃ r ∈ Ioc weighted.βdagger
        (twoPhaseUpperPath weighted ε (upperStrategyTotalStop weighted ε)).1,
      (r, p.stationaryStock r) ≤
        twoPhaseUpperPath weighted ε (upperStrategyTotalStop weighted ε) := by
  let y := upperStrategyClimbState weighted ε
  have hyAbove : weighted.βdagger < y.1 := by
    simpa only [y, upperStrategyClimbState] using
      upperStrategyClimbStop_crosses model weighted hε
  have hyMem : y.1 ∈ Icc (0 : ℝ) 1 := by
    dsimp only [y, upperStrategyClimbState]
    exact (marginClimbPath_isControlled p ρ ε).policy_mem
      (upperStrategyClimbStop weighted ε)
  obtain ⟨r, hr, hdom⟩ := cancellingHoldStop_dominates_characteristic
    model hcoop weighted (D₀ := y.2) ⟨hyAbove, hyMem.2⟩
  have hterminal := twoPhaseUpperPath_at_totalStop model ss hcoop weighted hε
  refine ⟨r, ?_, ?_⟩
  · rw [hterminal]
    simpa only [cancellingHoldPath, y] using hr
  · rw [hterminal]
    simpa only [y, upperStrategyHoldStop] using hdom

/-- After the finite controlled phases, the stopping state lies in the
captured basin of the unforced constant-weight dynamics. -/
theorem twoPhaseUpperPath_totalStop_tendsto_captured
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ ε : ℝ}
    (hρcure : ρ < cureThreshold p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε) :
    Tendsto
      (civicWeightedOrbit p ρ
        (twoPhaseUpperPath weighted ε (upperStrategyTotalStop weighted ε)))
      atTop (𝓝 (capturedPoint p)) := by
  obtain ⟨r, hr, hdom⟩ :=
    twoPhaseUpperPath_totalStop_dominates_characteristic
      model ss hcoop weighted hε
  have hterminalBox := twoPhaseUpperPath_totalStop_mem_absorbingBox
    model ss hcoop weighted hε
  have hr' : r ∈ Ioc weighted.βdagger 1 :=
    ⟨hr.1, hr.2.trans hterminalBox.1.2⟩
  exact civicWeightedOrbit_tendsto_captured_of_dominates_characteristic
    model ss hρcure hcoop weighted hr' hterminalBox hdom

/-- The finite two-phase terminal state has left the calibrated basin. -/
theorem twoPhaseUpperPath_exits_calibratedBasin
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ ε : ℝ}
    (hρcure : ρ < cureThreshold p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε) :
    twoPhaseUpperPath weighted ε (upperStrategyTotalStop weighted ε) ∉
      civicWeightedCalibratedBasin p ρ := by
  intro hcalibrated
  have hcaptured := twoPhaseUpperPath_totalStop_tendsto_captured
    model ss hρcure hcoop weighted hε
  have heq : capturedPoint p = calibratedPoint p :=
    tendsto_nhds_unique hcaptured hcalibrated
  have hfirst := congrArg Prod.fst heq
  norm_num [capturedPoint, calibratedPoint] at hfirst

/-- The exact finite action `S↑_ε(ρ)` of the two-phase strategy. -/
noncomputable def upwardStrategyCostEpsilon
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (ε : ℝ) : ℝ :=
  controlAction (twoPhaseUpperControl weighted ε)
    (upperStrategyTotalStop weighted ε)

/-- The set of positive-margin two-phase strategy costs. -/
def upwardStrategyCostSet
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ) :
    Set ℝ :=
  {a | ∃ ε, 0 < ε ∧ a = upwardStrategyCostEpsilon weighted ε}

/-- The upper object `S↑(ρ) := inf_{ε>0} S↑_ε(ρ)`. -/
noncomputable def upwardStrategyCost
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ) : ℝ :=
  sInf (upwardStrategyCostSet weighted)

/-- Every positive-margin strategy cost is an actual member of the finite
escape-action set, not merely a numerical trajectory. -/
theorem upwardStrategyCostEpsilon_mem_quasipotentialActionSet
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ ε : ℝ}
    (hρcure : ρ < cureThreshold p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε) :
    upwardStrategyCostEpsilon weighted ε ∈
      quasipotentialActionSet p ρ := by
  refine ⟨upperStrategyTotalStop weighted ε,
    twoPhaseUpperControl weighted ε, twoPhaseUpperPath weighted ε,
    twoPhaseUpperPath_isControlled weighted ε,
    twoPhaseUpperPath_exits_calibratedBasin
      model ss hρcure hcoop weighted hε, rfl⟩

/-- Each printed finite action `S↑_ε` upper-bounds the quasipotential. -/
theorem civicQuasipotential_le_upwardStrategyCostEpsilon
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ ε : ℝ}
    (hρcure : ρ < cureThreshold p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε) :
    civicQuasipotential p ρ ≤ upwardStrategyCostEpsilon weighted ε := by
  exact civicQuasipotential_le_controlAction
    (twoPhaseUpperPath_isControlled weighted ε)
    (twoPhaseUpperPath_exits_calibratedBasin
      model ss hρcure hcoop weighted hε)

/-- The infimum of the explicit positive-margin strategy costs remains an
upper bound on the quasipotential, exactly as stated in `prop:qpbounds`. -/
theorem civicQuasipotential_le_upwardStrategyCost
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ : ℝ}
    (hρcure : ρ < cureThreshold p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) :
    civicQuasipotential p ρ ≤ upwardStrategyCost weighted := by
  change civicQuasipotential p ρ ≤ sInf (upwardStrategyCostSet weighted)
  apply le_csInf
  · exact ⟨upwardStrategyCostEpsilon weighted 1, 1, by norm_num, rfl⟩
  · rintro a ⟨ε, hε, rfl⟩
    exact civicQuasipotential_le_upwardStrategyCostEpsilon
      model ss hρcure hcoop weighted hε

/-! ## The fixed-primitives small-adaptation-rate family -/

/-- Replace only the operator adaptation rate, leaving every other Paper II
primitive literally fixed. -/
def withOperatorRate (p : LoopParams) (α : ℝ) : LoopParams :=
  { η := p.η
    lambda₀ := p.lambda₀
    I := p.I
    v := p.v
    c := p.c
    α := α
    g := p.g }

@[simp] theorem withOperatorRate_eta (p : LoopParams) (α : ℝ) :
    (withOperatorRate p α).η = p.η := rfl

@[simp] theorem withOperatorRate_lambda₀ (p : LoopParams) (α : ℝ) :
    (withOperatorRate p α).lambda₀ = p.lambda₀ := rfl

@[simp] theorem withOperatorRate_I (p : LoopParams) (α : ℝ) :
    (withOperatorRate p α).I = p.I := rfl

@[simp] theorem withOperatorRate_v (p : LoopParams) (α : ℝ) :
    (withOperatorRate p α).v = p.v := rfl

@[simp] theorem withOperatorRate_c (p : LoopParams) (α : ℝ) :
    (withOperatorRate p α).c = p.c := rfl

@[simp] theorem withOperatorRate_alpha (p : LoopParams) (α : ℝ) :
    (withOperatorRate p α).α = α := rfl

@[simp] theorem withOperatorRate_g (p : LoopParams) (α : ℝ) :
    (withOperatorRate p α).g = p.g := rfl

@[simp] theorem withOperatorRate_s (p : LoopParams) (α β : ℝ) :
    (withOperatorRate p α).s β = p.s β := rfl

@[simp] theorem withOperatorRate_sSlope (p : LoopParams) (α β : ℝ) :
    (withOperatorRate p α).sSlope β = p.sSlope β := rfl

@[simp] theorem withOperatorRate_gradU (p : LoopParams) (α β D : ℝ) :
    (withOperatorRate p α).gradU β D = p.gradU β D := rfl

@[simp] theorem withOperatorRate_stationaryStock
    (p : LoopParams) (α β : ℝ) :
    (withOperatorRate p α).stationaryStock β = p.stationaryStock β := rfl

@[simp] theorem withOperatorRate_G (p : LoopParams) (α β : ℝ) :
    (withOperatorRate p α).G β = p.G β := rfl

@[simp] theorem withOperatorRate_GSlope (p : LoopParams) (α β : ℝ) :
    (withOperatorRate p α).GSlope β = p.GSlope β := rfl

@[simp] theorem withOperatorRate_civicWeightedGradient
    (p : LoopParams) (α ρ β D : ℝ) :
    civicWeightedGradient (withOperatorRate p α) ρ β D =
      civicWeightedGradient p ρ β D := rfl

@[simp] theorem withOperatorRate_weightedStationaryGradient
    (p : LoopParams) (α ρ β : ℝ) :
    weightedStationaryGradient (withOperatorRate p α) ρ β =
      weightedStationaryGradient p ρ β := rfl

@[simp] theorem withOperatorRate_weightedStationaryGradientSlope
    (p : LoopParams) (α ρ β : ℝ) :
    weightedStationaryGradientSlope (withOperatorRate p α) ρ β =
      weightedStationaryGradientSlope p ρ β := rfl

@[simp] theorem withOperatorRate_weightedBarrierIntegrand
    (p : LoopParams) (α ρ β : ℝ) :
    weightedBarrierIntegrand (withOperatorRate p α) ρ β =
      weightedBarrierIntegrand p ρ β := rfl

@[simp] theorem withOperatorRate_cureThreshold (p : LoopParams) (α : ℝ) :
    cureThreshold (withOperatorRate p α) = cureThreshold p := rfl

/-- Primitive model assumptions transport along the fixed-primitives family
as soon as the replacement adaptation rate is positive. -/
theorem DriftModelAssumptions.withOperatorRate
    {p : LoopParams} (model : DriftModelAssumptions p) {α : ℝ}
    (hα : 0 < α) : DriftModelAssumptions (withOperatorRate p α) where
  η_pos := by simpa using model.η_pos
  η_le_one := by simpa using model.η_le_one
  lambda₀_pos := by simpa using model.lambda₀_pos
  lambda₀_lt_one := by simpa using model.lambda₀_lt_one
  I_pos := by simpa using model.I_pos
  v_pos := by simpa using model.v_pos
  c_pos := by simpa using model.c_pos
  c_lt_one := by simpa using model.c_lt_one
  α_pos := by simpa using hα
  no_content_gain := by simpa using model.no_content_gain

/-- The small-step inequality persists when only the adaptation rate is
decreased. -/
theorem SmallStepAssumption.withOperatorRate
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {α : ℝ} (_hα : 0 ≤ α) (hαle : α ≤ p.α) :
    SmallStepAssumption (withOperatorRate p α) := by
  constructor
  simp only [withOperatorRate_alpha, withOperatorRate_c, withOperatorRate_I,
    withOperatorRate_lambda₀]
  have hcoef : 0 < 2 * p.c ^ 2 * p.I :=
    mul_pos (mul_pos two_pos (sq_pos_of_pos model.c_pos)) model.I_pos
  nlinarith [ss.bound]

/-- The unweighted threshold catalogue is independent of the operator rate. -/
def ThresholdAssumption.withOperatorRate
    {p : LoopParams} (threshold : ThresholdAssumption p) (α : ℝ) :
    ThresholdAssumption (withOperatorRate p α) where
  βdagger := threshold.βdagger
  βdagger_mem := threshold.βdagger_mem
  G_zero := by simpa using threshold.G_zero
  G_zero_neg := by simpa using threshold.G_zero_neg
  G_one_pos := by simpa using threshold.G_one_pos
  G_neg_before := by
    intro β hβ hbefore
    simpa using threshold.G_neg_before β hβ hbefore
  G_pos_after := by
    intro β hβ hafter
    simpa using threshold.G_pos_after β hβ hafter
  GSlope_pos := by simpa using threshold.GSlope_pos

/-- The civic-weighted threshold catalogue is likewise independent of the
operator rate. -/
def WeightedThresholdAssumption.withOperatorRate
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (α : ℝ) : WeightedThresholdAssumption (withOperatorRate p α) ρ where
  βdagger := weighted.βdagger
  βdagger_mem := weighted.βdagger_mem
  gradient_zero := by simpa using weighted.gradient_zero
  gradient_zero_neg := by
    simpa using weighted.gradient_zero_neg
  gradient_one_pos := by
    simpa using weighted.gradient_one_pos
  gradient_neg_before := by
    intro β hβ hbefore
    simpa using
      weighted.gradient_neg_before β hβ hbefore
  gradient_pos_after := by
    intro β hβ hafter
    simpa using
      weighted.gradient_pos_after β hβ hafter
  gradientSlope_pos := by
    simpa using weighted.gradientSlope_pos

@[simp] theorem WeightedThresholdAssumption.withOperatorRate_βdagger
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (α : ℝ) :
    (weighted.withOperatorRate α).βdagger = weighted.βdagger := rfl

/-- The literal strategy infimum along the family which varies only `α`. -/
noncomputable def upwardStrategyCostAtRate
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (α : ℝ) : ℝ :=
  upwardStrategyCost (weighted.withOperatorRate α)

/-- A global Lipschitz constant for the zero-content-gain stationary
characteristic on the policy interval. -/
def driftStationaryStockLipschitzBound (p : LoopParams) : ℝ :=
  p.I * (2 * p.η * (1 - p.lambda₀)) / p.lambda₀ ^ 2

@[simp] theorem driftStationaryStockLipschitzBound_withOperatorRate
    (p : LoopParams) (α : ℝ) :
    driftStationaryStockLipschitzBound (withOperatorRate p α) =
      driftStationaryStockLipschitzBound p := rfl

theorem driftStationaryStockLipschitzBound_pos
    {p : LoopParams} (model : DriftModelAssumptions p) :
    0 < driftStationaryStockLipschitzBound p := by
  simp only [driftStationaryStockLipschitzBound]
  exact div_pos
    (mul_pos model.I_pos
      (mul_pos (mul_pos two_pos model.η_pos)
        (sub_pos.mpr model.lambda₀_lt_one)))
    (sq_pos_of_pos model.lambda₀_pos)

/-- The stationary characteristic obeys its explicit global Lipschitz bound
on `[0,1]`. -/
theorem stationaryStock_sub_le_driftLipschitz
    {p : LoopParams} (model : DriftModelAssumptions p)
    {β₁ β₂ : ℝ} (hβ₁ : β₁ ∈ Icc (0 : ℝ) 1)
    (hβ₂ : β₂ ∈ Icc (0 : ℝ) 1) (hβ : β₁ ≤ β₂) :
    p.stationaryStock β₂ - p.stationaryStock β₁ ≤
      driftStationaryStockLipschitzBound p * (β₂ - β₁) := by
  let d₁ := 1 - p.s β₁
  let d₂ := 1 - p.s β₂
  let k := 2 * p.η * (1 - p.lambda₀)
  have hd₁ : 0 < d₁ := thresholdDenominator_pos model hβ₁
  have hd₂ : 0 < d₂ := thresholdDenominator_pos model hβ₂
  have hsdiff := stockMultiplier_sub_le model hβ₁ hβ₂ hβ
  have hlambda_d₁ : p.lambda₀ ≤ d₁ := by
    dsimp only [d₁]
    linarith [(driftStockMultiplier_nonneg_le model hβ₁).2]
  have hlambda_d₂ : p.lambda₀ ≤ d₂ := by
    dsimp only [d₂]
    linarith [(driftStockMultiplier_nonneg_le model hβ₂).2]
  have hden : p.lambda₀ ^ 2 ≤ d₁ * d₂ := by
    nlinarith [mul_le_mul hlambda_d₁ hlambda_d₂ model.lambda₀_pos.le hd₁.le]
  have hk_nonneg : 0 ≤ k := by
    dsimp only [k]
    exact mul_nonneg (mul_nonneg (by norm_num) model.η_pos.le)
      (sub_nonneg.mpr model.lambda₀_lt_one.le)
  have hdelta : 0 ≤ β₂ - β₁ := sub_nonneg.mpr hβ
  have hnum : p.I * (p.s β₂ - p.s β₁) ≤
      p.I * (k * (β₂ - β₁)) :=
    mul_le_mul_of_nonneg_left (by simpa only [k] using hsdiff) model.I_pos.le
  have hupper_nonneg : 0 ≤ p.I * (k * (β₂ - β₁)) :=
    mul_nonneg model.I_pos.le (mul_nonneg hk_nonneg hdelta)
  have hfrac :
      p.I * (p.s β₂ - p.s β₁) / (d₁ * d₂) ≤
        p.I * (k * (β₂ - β₁)) / p.lambda₀ ^ 2 :=
    div_le_div₀ hupper_nonneg hnum (sq_pos_of_pos model.lambda₀_pos) hden
  have hid : p.stationaryStock β₂ - p.stationaryStock β₁ =
      p.I * (p.s β₂ - p.s β₁) / (d₁ * d₂) := by
    simp only [LoopParams.stationaryStock, model.no_content_gain, sub_zero]
    rw [div_sub_div p.I p.I hd₂.ne' hd₁.ne']
    dsimp only [d₁, d₂]
    ring
  rw [hid]
  calc
    _ ≤ p.I * (k * (β₂ - β₁)) / p.lambda₀ ^ 2 := hfrac
    _ = driftStationaryStockLipschitzBound p * (β₂ - β₁) := by
      simp only [driftStationaryStockLipschitzBound]
      dsimp only [k]
      ring

/-- The oriented stationary gradient is nonpositive through the weighted
saddle, including both endpoints. -/
theorem WeightedThresholdAssumption.gradient_nonpos_before
    {p : LoopParams} {ρ β : ℝ}
    (weighted : WeightedThresholdAssumption p ρ)
    (hβ : β ∈ Icc (0 : ℝ) 1) (hle : β ≤ weighted.βdagger) :
    weightedStationaryGradient p ρ β ≤ 0 := by
  by_cases hzero : β = 0
  · subst β
    exact weighted.gradient_zero_neg.le
  by_cases hroot : β = weighted.βdagger
  · subst β
    exact weighted.gradient_zero.le
  have hβIoo : β ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hβ.1 (Ne.symm hzero),
      hle.trans_lt weighted.βdagger_mem.2⟩
  exact (weighted.gradient_neg_before β hβIoo
    (lt_of_le_of_ne hle hroot)).le

/-- Before the first crossing, every climb policy remains at or below the
weighted saddle. -/
theorem marginClimbPath_le_saddle_before_stop
    {p : LoopParams} (model : DriftModelAssumptions p)
    {ρ ε : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (hε : 0 < ε) {n : ℕ} (hn : n < upperStrategyClimbStop weighted ε) :
    (marginClimbPath p ρ ε n).1 ≤ weighted.βdagger := by
  have hexists : ∃ k, 0 <
      (marginClimbPath p ρ ε k).1 - weighted.βdagger := by
    obtain ⟨k, hk⟩ := marginClimbPath_eventually_crosses model weighted hε
    exact ⟨k, sub_pos.mpr hk⟩
  have hbefore := firstPositiveIndex_nonpos_before hexists
    (by simpa only [upperStrategyClimbStop] using hn)
  linarith

/-- At every pre-crossing step whose worst-case increment stays below one,
the projection is inactive.  The policy increment is exactly
`α(-gρ+ε)`, with `-gρ` between zero and `v`. -/
theorem marginClimb_before_stop_step_data
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ ε : ℝ}
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε)
    (hroom : p.α * (p.v + ε) ≤ 1 - weighted.βdagger)
    {n : ℕ} (hn : n < upperStrategyClimbStop weighted ε) :
    let g := civicWeightedGradient p ρ
      (marginClimbPath p ρ ε n).1 (marginClimbPath p ρ ε n).2
    (marginClimbPath p ρ ε (n + 1)).1 -
          (marginClimbPath p ρ ε n).1 = p.α * (-g + ε) ∧
      0 ≤ -g ∧ -g ≤ p.v := by
  let x := marginClimbPath p ρ ε n
  let g := civicWeightedGradient p ρ x.1 x.2
  have path := marginClimbPath_isControlled p ρ ε
  have hxBox := path.mem_absorbingBox model n
  have hxPolicy : x.1 ∈ Icc (0 : ℝ) 1 := hxBox.1
  have hxStockNonneg : 0 ≤ x.2 := model.I_pos.le.trans hxBox.2.1
  have hβroot : x.1 ≤ weighted.βdagger :=
    marginClimbPath_le_saddle_before_stop model weighted hε hn
  have hmono := monotone_marginClimbPolicy model ρ ε hε.le
  have hmax : policyRunningMax (marginClimbPath p ρ ε) n = x.1 := by
    simp only [policyRunningMax, x]
    exact runningMax_eq_of_monotone hmono n
  have hgradientLe : g ≤ weightedStationaryGradient p ρ x.1 := by
    have h := path.gradient_le_runningMax model ss hcoop n
    simpa only [hmax, sub_self, mul_zero, add_zero, x, g] using h
  have hstationaryNonpos :=
    weighted.gradient_nonpos_before hxPolicy hβroot
  have hgNonpos : g ≤ 0 := hgradientLe.trans hstationaryNonpos
  have hcoef := weighted_stock_coefficient_nonnegative model hcoop hxPolicy
  have hgLower : -p.v ≤ g := by
    simp only [g, civicWeightedGradient, LoopParams.gradU]
    nlinarith [mul_nonneg hcoef hxStockNonneg]
  have hcontrol : marginClimbControl p ρ ε x = 2 * (-g) + ε := by
    simp only [marginClimbControl, doublingControl, g]
    rw [max_eq_left (neg_nonneg.mpr hgNonpos)]
  have hnet : civicWeightedGradient p ρ x.1 x.2 +
      marginClimbControl p ρ ε x = -g + ε := by
    rw [hcontrol]
    dsimp only [g]
    ring
  have hnetNonneg : 0 ≤ -g + ε := by linarith
  have hnetUpper : -g + ε ≤ p.v + ε := by linarith
  have hrawMem : x.1 + p.α * (-g + ε) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · nlinarith [model.α_pos, hxPolicy.1]
    · have hmul := mul_le_mul_of_nonneg_left hnetUpper model.α_pos.le
      nlinarith
  have hnext : (marginClimbPath p ρ ε (n + 1)).1 =
      x.1 + p.α * (-g + ε) := by
    rw [marginClimbPath_succ]
    simp only [controlledCivicWeightedStep, marginClimbControlSequence]
    rw [hnet, clipUnit_eq_self hrawMem]
  dsimp only [x] at hnext ⊢
  refine ⟨?_, by linarith, by linarith⟩
  linarith

/-- Consequent uniform increment bounds for every pre-crossing climb step. -/
theorem marginClimb_before_stop_increment_bounds
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ ε : ℝ}
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε)
    (hroom : p.α * (p.v + ε) ≤ 1 - weighted.βdagger)
    {n : ℕ} (hn : n < upperStrategyClimbStop weighted ε) :
    p.α * ε ≤
        (marginClimbPath p ρ ε (n + 1)).1 -
          (marginClimbPath p ρ ε n).1 ∧
      (marginClimbPath p ρ ε (n + 1)).1 -
          (marginClimbPath p ρ ε n).1 ≤ p.α * (p.v + ε) := by
  obtain ⟨hstep, hgNonneg, hgUpper⟩ :=
    marginClimb_before_stop_step_data model ss hcoop weighted hε hroom hn
  constructor <;> rw [hstep]
  · nlinarith [model.α_pos]
  · exact mul_le_mul_of_nonneg_left (by linarith) model.α_pos.le

/-- Lag of the exact stock below the stationary characteristic at the current
policy. -/
def stationaryStockLag (p : LoopParams) (x : LoopState) : ℝ :=
  p.stationaryStock x.1 - x.2

/-- The climb lag obeys the exact forced contraction recurrence: movement of
the characteristic is the forcing term and the stock multiplier contracts the
previous lag. -/
theorem marginClimb_stationaryStockLag_succ
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ρ ε : ℝ) (n : ℕ) :
    stationaryStockLag p (marginClimbPath p ρ ε (n + 1)) =
      (p.stationaryStock (marginClimbPath p ρ ε (n + 1)).1 -
        p.stationaryStock (marginClimbPath p ρ ε n).1) +
      p.s (marginClimbPath p ρ ε n).1 *
        stationaryStockLag p (marginClimbPath p ρ ε n) := by
  let x := marginClimbPath p ρ ε n
  have hxPolicy : x.1 ∈ Icc (0 : ℝ) 1 :=
    (marginClimbPath_isControlled p ρ ε).policy_mem n
  have hfixed := stationaryStock_fixed model hxPolicy
  rw [marginClimbPath_succ]
  simp only [stationaryStockLag, controlledCivicWeightedStep,
    marginClimbControlSequence, LoopParams.stockStep, model.no_content_gain,
    add_zero]
  simp only [LoopParams.stockStep, model.no_content_gain, add_zero] at hfixed
  dsimp only [x] at hfixed
  linarith [hfixed]

/-- Uniform `O(α)` stock lag through the first crossing. -/
theorem marginClimb_stationaryStockLag_le
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ ε : ℝ}
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε)
    (hroom : p.α * (p.v + ε) ≤ 1 - weighted.βdagger)
    {n : ℕ} (hn : n ≤ upperStrategyClimbStop weighted ε) :
    stationaryStockLag p (marginClimbPath p ρ ε n) ≤
      driftStationaryStockLipschitzBound p *
        (p.α * (p.v + ε)) / p.lambda₀ := by
  let K := driftStationaryStockLipschitzBound p
  let δ := p.α * (p.v + ε)
  let B := K * δ / p.lambda₀
  have hK : 0 < K := driftStationaryStockLipschitzBound_pos model
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact mul_pos model.α_pos (add_pos model.v_pos hε)
  have hB : 0 < B := div_pos (mul_pos hK hδ) model.lambda₀_pos
  change stationaryStockLag p (marginClimbPath p ρ ε n) ≤ B
  induction n with
  | zero =>
      simp only [stationaryStockLag, marginClimbPath_zero, calibratedPoint,
        sub_self]
      exact hB.le
  | succ n ih =>
      have hnlt : n < upperStrategyClimbStop weighted ε := by omega
      have hnle : n ≤ upperStrategyClimbStop weighted ε := hnlt.le
      have hinc := marginClimb_before_stop_increment_bounds
        model ss hcoop weighted hε hroom hnlt
      have hmono := monotone_marginClimbPolicy model ρ ε hε.le
      have hnPolicy : (marginClimbPath p ρ ε n).1 ∈ Icc (0 : ℝ) 1 :=
        (marginClimbPath_isControlled p ρ ε).policy_mem n
      have hnextPolicy : (marginClimbPath p ρ ε (n + 1)).1 ∈ Icc (0 : ℝ) 1 :=
        (marginClimbPath_isControlled p ρ ε).policy_mem (n + 1)
      have hchar := stationaryStock_sub_le_driftLipschitz model hnPolicy
        hnextPolicy (hmono n.le_succ)
      have hcharUpper :
          p.stationaryStock (marginClimbPath p ρ ε (n + 1)).1 -
              p.stationaryStock (marginClimbPath p ρ ε n).1 ≤ K * δ := by
        calc
          _ ≤ K * ((marginClimbPath p ρ ε (n + 1)).1 -
              (marginClimbPath p ρ ε n).1) := by simpa only [K] using hchar
          _ ≤ K * δ := mul_le_mul_of_nonneg_left
            (by simpa only [δ] using hinc.2) hK.le
      have hs := driftStockMultiplier_nonneg_le model hnPolicy
      have hlagNonneg : 0 ≤
          stationaryStockLag p (marginClimbPath p ρ ε n) := by
        simp only [stationaryStockLag]
        exact sub_nonneg.mpr
          (marginClimbPath_stock_le_stationaryStock model ss hε.le n)
      have hcontract :
          p.s (marginClimbPath p ρ ε n).1 *
              stationaryStockLag p (marginClimbPath p ρ ε n) ≤
            (1 - p.lambda₀) * B := by
        calc
          _ ≤ p.s (marginClimbPath p ρ ε n).1 * B :=
            mul_le_mul_of_nonneg_left (ih hnle) hs.1
          _ ≤ (1 - p.lambda₀) * B :=
            mul_le_mul_of_nonneg_right hs.2 hB.le
      have hidentity : K * δ + (1 - p.lambda₀) * B = B := by
        dsimp only [B]
        field_simp [model.lambda₀_pos.ne']
        ring
      rw [marginClimb_stationaryStockLag_succ model ρ ε n]
      linarith

/-! ## Quantitative action of the upper strategy -/

/-- The unscaled corrected barrier integral appearing in both bounds. -/
noncomputable def weightedBarrierArea
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ) : ℝ :=
  ∫ b in (0 : ℝ)..weighted.βdagger, weightedBarrierIntegrand p ρ b

/-- The square root which factors the Paper II persistence denominator. -/
noncomputable def driftPersistenceRoot (p : LoopParams) : ℝ :=
  Real.sqrt (1 - p.lambda₀)

/-- The affine evidence-retention factor whose square defines `s`. -/
def driftEvidenceFactor (p : LoopParams) (β : ℝ) : ℝ :=
  p.η * β + (1 - p.η)

/-- The constant term obtained when the weighted stock coefficient is
rewritten as an affine function of `driftEvidenceFactor`. -/
def weightedBarrierLogCoefficient (p : LoopParams) (ρ : ℝ) : ℝ :=
  2 * p.c - ρ + 2 * p.c ^ 2 * (1 - p.η) / p.η

/-- A logarithmic antiderivative of the corrected barrier integrand.  Its
endpoint difference is the closed form asserted in `prop:qpbounds`. -/
noncomputable def weightedBarrierClosedPrimitive
    (p : LoopParams) (ρ β : ℝ) : ℝ :=
  p.v * β - p.I *
    ((weightedBarrierLogCoefficient p ρ /
        (2 * p.η * driftPersistenceRoot p)) *
      (Real.log (1 + driftPersistenceRoot p * driftEvidenceFactor p β) -
        Real.log (1 - driftPersistenceRoot p * driftEvidenceFactor p β)) +
      (p.c ^ 2 / (p.η ^ 2 * (1 - p.lambda₀))) *
        Real.log
          (1 - (1 - p.lambda₀) * driftEvidenceFactor p β ^ 2))

/-- The displayed logarithmic primitive has derivative exactly equal to the
weighted barrier integrand throughout the policy interval. -/
theorem hasDerivAt_weightedBarrierClosedPrimitive
    {p : LoopParams} (model : DriftModelAssumptions p) (ρ : ℝ)
    {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (weightedBarrierClosedPrimitive p ρ)
      (weightedBarrierIntegrand p ρ β) β := by
  let k := driftPersistenceRoot p
  let u := driftEvidenceFactor p
  let B := weightedBarrierLogCoefficient p ρ
  have ha : 0 < 1 - p.lambda₀ := sub_pos.mpr model.lambda₀_lt_one
  have hk : 0 < k := by
    simpa only [k, driftPersistenceRoot] using Real.sqrt_pos.2 ha
  have hkSq : k ^ 2 = 1 - p.lambda₀ := by
    simpa only [k, driftPersistenceRoot] using Real.sq_sqrt ha.le
  have huNonneg : 0 ≤ u β := by
    have hηβ := mul_nonneg model.η_pos.le hβ.1
    dsimp only [u, driftEvidenceFactor]
    nlinarith [model.η_le_one]
  have huLeOne : u β ≤ 1 := by
    have hηres := mul_nonneg model.η_pos.le (sub_nonneg.mpr hβ.2)
    dsimp only [u, driftEvidenceFactor]
    nlinarith
  have hkLtOne : k < 1 := by
    nlinarith [model.lambda₀_pos]
  have hkuLtOne : k * u β < 1 := by
    have hle : k * u β ≤ k := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left huLeOne hk.le
    exact hle.trans_lt hkLtOne
  have hplusPos : 0 < 1 + k * u β := by
    nlinarith [mul_nonneg hk.le huNonneg]
  have hminusPos : 0 < 1 - k * u β := by
    linarith
  have hsEq : p.s β = (1 - p.lambda₀) * u β ^ 2 := by
    simp only [LoopParams.s, u, driftEvidenceFactor]
    congr 1
    ring
  have hdenPos : 0 < 1 - (1 - p.lambda₀) * u β ^ 2 := by
    have h := thresholdDenominator_pos model hβ
    rw [hsEq] at h
    exact h
  have huDeriv : HasDerivAt u p.η β := by
    convert! ((hasDerivAt_id β).const_mul p.η).const_add (1 - p.η) using 1
    · funext z
      change p.η * z + (1 - p.η) = 1 - p.η + p.η * z
      ring
    · ring
  have hplusDeriv : HasDerivAt (fun z ↦ 1 + k * u z) (k * p.η) β := by
    simpa only [add_comm] using (huDeriv.const_mul k).const_add 1
  have hminusDeriv : HasDerivAt (fun z ↦ 1 - k * u z) (-k * p.η) β := by
    simpa only [neg_mul] using (huDeriv.const_mul k).const_sub 1
  have hdenDeriv : HasDerivAt
      (fun z ↦ 1 - (1 - p.lambda₀) * u z ^ 2)
      (-2 * (1 - p.lambda₀) * u β * p.η) β := by
    have huSq : HasDerivAt (fun z ↦ u z ^ 2) (2 * u β * p.η) β := by
      convert! huDeriv.pow 2 using 1
      norm_num
    have hraw := (huSq.const_mul (1 - p.lambda₀)).const_sub 1
    simpa only [neg_mul] using hraw.congr_deriv (by ring)
  have hlogPlus := hplusDeriv.log hplusPos.ne'
  have hlogMinus := hminusDeriv.log hminusPos.ne'
  have hlogDen := hdenDeriv.log hdenPos.ne'
  have hlogDifference : HasDerivAt
      (fun z ↦ Real.log (1 + k * u z) - Real.log (1 - k * u z))
      (k * p.η / (1 + k * u β) -
        (-k * p.η) / (1 - k * u β)) β :=
    hlogPlus.sub hlogMinus
  have hinside : HasDerivAt
      (fun z ↦
        (B / (2 * p.η * k)) *
            (Real.log (1 + k * u z) - Real.log (1 - k * u z)) +
          (p.c ^ 2 / (p.η ^ 2 * (1 - p.lambda₀))) *
            Real.log (1 - (1 - p.lambda₀) * u z ^ 2))
      ((B / (2 * p.η * k)) *
          (k * p.η / (1 + k * u β) -
            (-k * p.η) / (1 - k * u β)) +
        (p.c ^ 2 / (p.η ^ 2 * (1 - p.lambda₀))) *
          (-2 * (1 - p.lambda₀) * u β * p.η /
            (1 - (1 - p.lambda₀) * u β ^ 2))) β := by
    exact (hlogDifference.const_mul (B / (2 * p.η * k))).add
      (hlogDen.const_mul (p.c ^ 2 / (p.η ^ 2 * (1 - p.lambda₀))))
  have hprimitive : HasDerivAt
      (fun z ↦ p.v * z - p.I *
        ((B / (2 * p.η * k)) *
            (Real.log (1 + k * u z) - Real.log (1 - k * u z)) +
          (p.c ^ 2 / (p.η ^ 2 * (1 - p.lambda₀))) *
            Real.log (1 - (1 - p.lambda₀) * u z ^ 2)))
      (p.v - p.I *
        ((B / (2 * p.η * k)) *
            (k * p.η / (1 + k * u β) -
              (-k * p.η) / (1 - k * u β)) +
          (p.c ^ 2 / (p.η ^ 2 * (1 - p.lambda₀))) *
            (-2 * (1 - p.lambda₀) * u β * p.η /
              (1 - (1 - p.lambda₀) * u β ^ 2)))) β := by
    have hraw := ((hasDerivAt_id β).const_mul p.v).sub (hinside.const_mul p.I)
    convert! hraw using 1
    all_goals simp only [mul_one]
  have hfactor :
      (1 + k * u β) * (1 - k * u β) =
        1 - (1 - p.lambda₀) * u β ^ 2 := by
    nlinarith [hkSq]
  have hfirstTerm :
      (B / (2 * p.η * k)) *
          (k * p.η / (1 + k * u β) -
            (-k * p.η) / (1 - k * u β)) =
        B / (1 - (1 - p.lambda₀) * u β ^ 2) := by
    rw [← hfactor]
    field_simp [model.η_pos.ne', hk.ne', hplusPos.ne', hminusPos.ne']
    ring
  have hsecondTerm :
      (p.c ^ 2 / (p.η ^ 2 * (1 - p.lambda₀))) *
          (-2 * (1 - p.lambda₀) * u β * p.η /
            (1 - (1 - p.lambda₀) * u β ^ 2)) =
        -(2 * p.c ^ 2 / p.η) * u β /
          (1 - (1 - p.lambda₀) * u β ^ 2) := by
    field_simp [model.η_pos.ne', ha.ne', hdenPos.ne']
  have hcoefficient :
      B - (2 * p.c ^ 2 / p.η) * u β =
        2 * p.c * (1 - p.c * β) - ρ := by
    dsimp only [B, u, weightedBarrierLogCoefficient, driftEvidenceFactor]
    field_simp [model.η_pos.ne']
    ring
  have hinsideEq :
      (B / (2 * p.η * k)) *
          (k * p.η / (1 + k * u β) -
            (-k * p.η) / (1 - k * u β)) +
        (p.c ^ 2 / (p.η ^ 2 * (1 - p.lambda₀))) *
          (-2 * (1 - p.lambda₀) * u β * p.η /
            (1 - (1 - p.lambda₀) * u β ^ 2)) =
      (2 * p.c * (1 - p.c * β) - ρ) /
        (1 - (1 - p.lambda₀) * u β ^ 2) := by
    rw [hfirstTerm, hsecondTerm]
    calc
      B / (1 - (1 - p.lambda₀) * u β ^ 2) +
          -(2 * p.c ^ 2 / p.η) * u β /
            (1 - (1 - p.lambda₀) * u β ^ 2) =
          (B - (2 * p.c ^ 2 / p.η) * u β) /
            (1 - (1 - p.lambda₀) * u β ^ 2) := by ring
      _ = (2 * p.c * (1 - p.c * β) - ρ) /
          (1 - (1 - p.lambda₀) * u β ^ 2) := by rw [hcoefficient]
  have hbarrierEq : weightedBarrierIntegrand p ρ β =
      p.v - p.I *
        ((2 * p.c * (1 - p.c * β) - ρ) /
          (1 - (1 - p.lambda₀) * u β ^ 2)) := by
    simp only [weightedBarrierIntegrand, weightedStationaryGradient,
      LoopParams.G, LoopParams.stationaryStock, model.no_content_gain, sub_zero]
    rw [hsEq]
    field_simp [hdenPos.ne']
    ring
  have hderivEq :
      p.v - p.I *
        ((B / (2 * p.η * k)) *
            (k * p.η / (1 + k * u β) -
              (-k * p.η) / (1 - k * u β)) +
          (p.c ^ 2 / (p.η ^ 2 * (1 - p.lambda₀))) *
            (-2 * (1 - p.lambda₀) * u β * p.η /
              (1 - (1 - p.lambda₀) * u β ^ 2))) =
        weightedBarrierIntegrand p ρ β := by
    rw [hinsideEq, hbarrierEq]
  have hfinal := hprimitive.congr_deriv hderivEq
  exact hfinal

/-- Paper II's lower-barrier integral equals an explicit difference of
logarithmic endpoint values. -/
theorem weightedBarrierArea_closedForm
    {p : LoopParams} (model : DriftModelAssumptions p) {ρ : ℝ}
    (weighted : WeightedThresholdAssumption p ρ) :
    weightedBarrierArea weighted =
      weightedBarrierClosedPrimitive p ρ weighted.βdagger -
        weightedBarrierClosedPrimitive p ρ 0 := by
  have hderiv : ∀ b ∈ uIcc (0 : ℝ) weighted.βdagger,
      HasDerivAt (weightedBarrierClosedPrimitive p ρ)
        (weightedBarrierIntegrand p ρ b) b := by
    intro b hb
    rw [uIcc_of_le weighted.βdagger_mem.1.le] at hb
    exact hasDerivAt_weightedBarrierClosedPrimitive model ρ
      ⟨hb.1, hb.2.trans weighted.βdagger_mem.2.le⟩
  have hint : IntervalIntegrable (weightedBarrierIntegrand p ρ)
      MeasureTheory.volume 0 weighted.βdagger :=
    (show ContinuousOn (weightedBarrierIntegrand p ρ)
        [[(0 : ℝ), weighted.βdagger]] by
      rw [uIcc_of_le weighted.βdagger_mem.1.le]
      exact continuousOn_weightedBarrierIntegrand model ρ weighted).intervalIntegrable
  simpa only [weightedBarrierArea] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- The corrected barrier area itself is independent of the operator rate. -/
theorem weightedBarrierArea_withOperatorRate
    {p : LoopParams} {ρ α : ℝ}
    (weighted : WeightedThresholdAssumption p ρ) :
    weightedBarrierArea (weighted.withOperatorRate α) =
      weightedBarrierArea weighted := by
  simp [weightedBarrierArea, WeightedThresholdAssumption.withOperatorRate]

/-- Off the stationary characteristic, the negative weighted gradient is the
barrier integrand plus the stock coefficient times the characteristic lag. -/
theorem neg_civicWeightedGradient_eq_barrier_add_lag
    (p : LoopParams) (ρ β D : ℝ) :
    -civicWeightedGradient p ρ β D =
      weightedBarrierIntegrand p ρ β +
        (2 * p.c * (1 - p.c * β) - ρ) *
          stationaryStockLag p (β, D) := by
  simp only [civicWeightedGradient, LoopParams.gradU,
    weightedBarrierIntegrand, weightedStationaryGradient, LoopParams.G,
    LoopParams.stationaryStock, stationaryStockLag]
  ring

/-- In the cooperative window the stock coefficient is also bounded above by
`2c` when the civic weight is nonnegative. -/
theorem weighted_stock_coefficient_le_two_c
    {p : LoopParams} (model : DriftModelAssumptions p)
    {ρ β : ℝ} (hρ : 0 ≤ ρ) (hβ : β ∈ Icc (0 : ℝ) 1) :
    2 * p.c * (1 - p.c * β) - ρ ≤ 2 * p.c := by
  have hcβ : 0 ≤ p.c * β := mul_nonneg model.c_pos.le hβ.1
  nlinarith [model.c_pos]

/-- During a fixed-policy hold, the gap to the stationary stock contracts by
the exact geometric factor `s(b)^n`. -/
theorem stationaryStock_sub_cancellingHoldStockPath
    {p : LoopParams} (model : DriftModelAssumptions p)
    {b D₀ : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    p.stationaryStock b - cancellingHoldStockPath p b D₀ n =
      (p.s b) ^ n * (p.stationaryStock b - D₀) := by
  have hs := driftStockMultiplier_nonneg_le model hb
  have hsne : p.s b ≠ 1 :=
    ne_of_lt (hs.2.trans_lt (sub_lt_self 1 model.lambda₀_pos))
  simp only [cancellingHoldStockPath]
  rw [arithGeom_eq hsne n]
  simp only [LoopParams.stationaryStock, model.no_content_gain, sub_zero]
  ring

/-- The finite sum of squared contraction factors is bounded by the inverse
uniform contraction gap. -/
theorem sum_sq_geometric_le_inv_gap
    {s lam : ℝ} (hs : 0 ≤ s) (hsle : s ≤ 1 - lam) (hlam : 0 < lam)
    (N : ℕ) :
    (∑ k ∈ Finset.range N, ((s ^ k) ^ 2)) ≤ 1 / lam := by
  let q : ℝ := s ^ 2
  have hsOne : s ≤ 1 := by linarith
  have hsqLe : s ^ 2 ≤ s := by
    have := mul_nonneg hs (sub_nonneg.mpr hsOne)
    nlinarith [sq_nonneg s]
  have hqNonneg : 0 ≤ q := by
    dsimp only [q]
    positivity
  have hqLe : q ≤ 1 - lam := hsqLe.trans hsle
  have hqOne : q ≤ 1 := by linarith
  let S : ℝ := ∑ k ∈ Finset.range N, q ^ k
  have hSNonneg : 0 ≤ S := by
    dsimp only [S]
    exact Finset.sum_nonneg fun k _hk ↦ pow_nonneg hqNonneg k
  have hgeom : S * (1 - q) = 1 - q ^ N := by
    simpa only [S] using geom_sum_mul_of_le_one hqOne N
  have hgeomLe : S * (1 - q) ≤ 1 := by
    rw [hgeom]
    exact sub_le_self 1 (pow_nonneg hqNonneg N)
  have hlamLe : lam ≤ 1 - q := by linarith
  have hlamS : S * lam ≤ 1 := by
    calc
      S * lam ≤ S * (1 - q) := mul_le_mul_of_nonneg_left hlamLe hSNonneg
      _ ≤ 1 := hgeomLe
  have hSLe : S ≤ 1 / lam := (le_div_iff₀ hlam).2 hlamS
  calc
    (∑ k ∈ Finset.range N, ((s ^ k) ^ 2)) = S := by
      dsimp only [S, q]
      apply Finset.sum_congr rfl
      intro k _hk
      simp only [← pow_mul, Nat.mul_comm]
    _ ≤ 1 / lam := hSLe

/-- Every pre-stop cancelling control is bounded by the geometrically
contracting initial stock gap. -/
theorem cancellingHoldControl_le_geometric
    {p : LoopParams} (model : DriftModelAssumptions p)
    {ρ b D₀ B : ℝ} (hρ : 0 ≤ ρ)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (hb : b ∈ Icc (0 : ℝ) 1)
    (hstationary : 0 < weightedStationaryGradient p ρ b)
    (hgapNonneg : 0 ≤ p.stationaryStock b - D₀)
    (hgapLe : p.stationaryStock b - D₀ ≤ B)
    {k : ℕ} (hk : k < cancellingHoldStop p ρ b D₀) :
    cancellingHoldControl p ρ b D₀ k ≤
      2 * p.c * (p.s b) ^ k * B := by
  let A : ℝ := 2 * p.c * (1 - p.c * b) - ρ
  let gap : ℝ := p.stationaryStock b - D₀
  have hBNonneg : 0 ≤ B := hgapNonneg.trans hgapLe
  have hs := driftStockMultiplier_nonneg_le model hb
  have hpowNonneg : 0 ≤ (p.s b) ^ k := pow_nonneg hs.1 k
  have hA_nonneg : 0 ≤ A := by
    simpa only [A] using weighted_stock_coefficient_nonnegative model hcoop hb
  have hA_le : A ≤ 2 * p.c := by
    simpa only [A] using weighted_stock_coefficient_le_two_c model hρ hb
  have hgapPowerLe : (p.s b) ^ k * gap ≤ (p.s b) ^ k * B :=
    mul_le_mul_of_nonneg_left (by simpa only [gap] using hgapLe) hpowNonneg
  have hAlagLe : A * ((p.s b) ^ k * gap) ≤
      2 * p.c * ((p.s b) ^ k * B) :=
    mul_le_mul hA_le hgapPowerLe
      (mul_nonneg hpowNonneg (by simpa only [gap] using hgapNonneg))
      (mul_nonneg (by norm_num) model.c_pos.le)
  have hgradient := cancellingHoldStop_gradient_nonpos_before
    model hb hstationary hk
  have hcontrol : cancellingHoldControl p ρ b D₀ k =
      -civicWeightedGradient p ρ b (cancellingHoldStockPath p b D₀ k) := by
    simp only [cancellingHoldControl, cancellingHoldGradient] at hgradient ⊢
    rw [max_eq_left (neg_nonneg.mpr hgradient)]
  have hgapEq := stationaryStock_sub_cancellingHoldStockPath
    model (D₀ := D₀) hb k
  have hgradientEq :
      -civicWeightedGradient p ρ b (cancellingHoldStockPath p b D₀ k) =
        A * (p.stationaryStock b - cancellingHoldStockPath p b D₀ k) -
          weightedStationaryGradient p ρ b := by
    have hid := neg_civicWeightedGradient_eq_barrier_add_lag
      p ρ b (cancellingHoldStockPath p b D₀ k)
    simp only [weightedBarrierIntegrand, stationaryStockLag] at hid
    dsimp only [A]
    linarith
  rw [hcontrol, hgradientEq, hgapEq]
  dsimp only [gap] at hAlagLe
  nlinarith

/-- Any finite prefix of the cancelling hold has action at most the squared
initial lag times the geometric-series constant. -/
theorem cancellingHoldAction_le
    {p : LoopParams} (model : DriftModelAssumptions p)
    {ρ b D₀ B : ℝ} (hρ : 0 ≤ ρ)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (hb : b ∈ Icc (0 : ℝ) 1)
    (hstationary : 0 < weightedStationaryGradient p ρ b)
    (hgapNonneg : 0 ≤ p.stationaryStock b - D₀)
    (hgapLe : p.stationaryStock b - D₀ ≤ B) :
    controlAction (cancellingHoldControl p ρ b D₀)
        (cancellingHoldStop p ρ b D₀) ≤
      2 * p.c ^ 2 * B ^ 2 / p.lambda₀ := by
  let T := cancellingHoldStop p ρ b D₀
  let C : ℝ := 2 * p.c * B
  have hBNonneg : 0 ≤ B := hgapNonneg.trans hgapLe
  have hCNonneg : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (mul_nonneg (by norm_num) model.c_pos.le) hBNonneg
  have hs := driftStockMultiplier_nonneg_le model hb
  have hsumControls :
      (∑ k ∈ Finset.range T,
          (cancellingHoldControl p ρ b D₀ k) ^ 2) ≤
        C ^ 2 * ∑ k ∈ Finset.range T, ((p.s b) ^ k) ^ 2 := by
    calc
      _ ≤ ∑ k ∈ Finset.range T,
          C ^ 2 * ((p.s b) ^ k) ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        have hcontrolNonneg : 0 ≤ cancellingHoldControl p ρ b D₀ k := by
          simp only [cancellingHoldControl]
          exact le_max_right _ _
        have hcontrolLe := cancellingHoldControl_le_geometric
          model hρ hcoop hb hstationary hgapNonneg hgapLe
          (by simpa only [T] using Finset.mem_range.mp hk)
        have hrightNonneg : 0 ≤ C * (p.s b) ^ k :=
          mul_nonneg hCNonneg (pow_nonneg hs.1 k)
        have hcontrolLe' : cancellingHoldControl p ρ b D₀ k ≤
            C * (p.s b) ^ k := by
          calc
            _ ≤ 2 * p.c * (p.s b) ^ k * B := hcontrolLe
            _ = C * (p.s b) ^ k := by
              dsimp only [C]
              ring
        have hsquare := (sq_le_sq₀ hcontrolNonneg hrightNonneg).2 hcontrolLe'
        nlinarith
      _ = C ^ 2 * ∑ k ∈ Finset.range T, ((p.s b) ^ k) ^ 2 := by
        rw [Finset.mul_sum]
  have hgeom := sum_sq_geometric_le_inv_gap hs.1 hs.2 model.lambda₀_pos T
  have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
  have htotal :
      (∑ k ∈ Finset.range T,
          (cancellingHoldControl p ρ b D₀ k) ^ 2) ≤ C ^ 2 / p.lambda₀ := by
    calc
      _ ≤ C ^ 2 * ∑ k ∈ Finset.range T, ((p.s b) ^ k) ^ 2 := hsumControls
      _ ≤ C ^ 2 * (1 / p.lambda₀) :=
        mul_le_mul_of_nonneg_left hgeom hC2
      _ = C ^ 2 / p.lambda₀ := by ring
  change (1 / 2 : ℝ) *
      ∑ k ∈ Finset.range T, (cancellingHoldControl p ρ b D₀ k) ^ 2 ≤ _
  have hhalf := mul_le_mul_of_nonneg_left htotal (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    _ ≤ (1 / 2 : ℝ) * ((2 * p.c * B) ^ 2 / p.lambda₀) := by
      simpa only [C] using hhalf
    _ = 2 * p.c ^ 2 * B ^ 2 / p.lambda₀ := by ring

/-- The action spent during the finite cancelling-hold phase of the upper
strategy. -/
noncomputable def upwardStrategyHoldAction
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (ε : ℝ) : ℝ :=
  controlAction
    (cancellingHoldControl p ρ (upperStrategyClimbState weighted ε).1
      (upperStrategyClimbState weighted ε).2)
    (upperStrategyHoldStop weighted ε)

/-- The hold action is quadratic in the crossing lag and hence `O(α²)` for
fixed positive margin. -/
theorem upwardStrategyHoldAction_le
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ ε : ℝ} (hρ : 0 ≤ ρ)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε)
    (hroom : p.α * (p.v + ε) ≤ 1 - weighted.βdagger) :
    upwardStrategyHoldAction weighted ε ≤
      2 * p.c ^ 2 *
        (driftStationaryStockLipschitzBound p *
          (p.α * (p.v + ε)) / p.lambda₀) ^ 2 / p.lambda₀ := by
  let y := upperStrategyClimbState weighted ε
  let B := driftStationaryStockLipschitzBound p *
    (p.α * (p.v + ε)) / p.lambda₀
  have hyPolicy : y.1 ∈ Icc (0 : ℝ) 1 := by
    dsimp only [y, upperStrategyClimbState]
    exact (marginClimbPath_isControlled p ρ ε).policy_mem
      (upperStrategyClimbStop weighted ε)
  have hyAbove : weighted.βdagger < y.1 := by
    simpa only [y, upperStrategyClimbState] using
      upperStrategyClimbStop_crosses model weighted hε
  have hstationary : 0 < weightedStationaryGradient p ρ y.1 :=
    weighted.gradient_pos_of_mem_Ioc ⟨hyAbove, hyPolicy.2⟩
  have hgapNonneg : 0 ≤ p.stationaryStock y.1 - y.2 := by
    dsimp only [y, upperStrategyClimbState]
    exact sub_nonneg.mpr
      (marginClimbPath_stock_le_stationaryStock model ss hε.le
        (upperStrategyClimbStop weighted ε))
  have hgapLe : p.stationaryStock y.1 - y.2 ≤ B := by
    simpa only [stationaryStockLag, y, upperStrategyClimbState, B] using
      marginClimb_stationaryStockLag_le model ss hcoop weighted hε hroom
        (n := upperStrategyClimbStop weighted ε) (le_refl _)
  have hhold := cancellingHoldAction_le model hρ hcoop hyPolicy hstationary
    hgapNonneg hgapLe
  simpa only [upwardStrategyHoldAction, upperStrategyHoldStop, y, B] using hhold

/-- The barrier integrand is nonnegative on the entire closed saddle
segment, with zero only needed explicitly at its right endpoint. -/
theorem WeightedThresholdAssumption.barrier_nonneg_before
    {p : LoopParams} {ρ β : ℝ}
    (weighted : WeightedThresholdAssumption p ρ)
    (hβ : β ∈ Icc (0 : ℝ) weighted.βdagger) :
    0 ≤ weightedBarrierIntegrand p ρ β := by
  rcases hβ.2.lt_or_eq with hlt | heq
  · exact (weighted.barrier_pos_before hβ hlt).le
  · subst β
    simp only [weightedBarrierIntegrand, weighted.gradient_zero, neg_zero]
    norm_num

/-- On the saddle segment the barrier height is at most the primitive loss
scale `v`. -/
theorem WeightedThresholdAssumption.barrier_le_v
    {p : LoopParams} (model : DriftModelAssumptions p)
    {ρ β : ℝ} (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (hβ : β ∈ Icc (0 : ℝ) weighted.βdagger) :
    weightedBarrierIntegrand p ρ β ≤ p.v := by
  have hβUnit : β ∈ Icc (0 : ℝ) 1 :=
    ⟨hβ.1, hβ.2.trans weighted.βdagger_mem.2.le⟩
  have hcoef := weighted_stock_coefficient_nonnegative model hcoop hβUnit
  have hstock : 0 ≤ p.stationaryStock β :=
    model.I_pos.le.trans (stationaryStock_mem_stockInterval model hβUnit).1
  have hprod : 0 ≤
      (2 * p.c * (1 - p.c * β) - ρ) * p.stationaryStock β :=
    mul_nonneg hcoef hstock
  have hgradientLower : -p.v ≤
      civicWeightedGradient p ρ β (p.stationaryStock β) := by
    simp only [civicWeightedGradient, LoopParams.gradU]
    nlinarith
  have hid := neg_civicWeightedGradient_eq_barrier_add_lag
    p ρ β (p.stationaryStock β)
  simp only [stationaryStockLag, sub_self, mul_zero, add_zero] at hid
  linarith

/-- Before crossing, the exact climb summand splits into the barrier-work
term and the square of the positive margin. -/
theorem marginClimb_action_summand_eq
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ ε : ℝ}
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε)
    (hroom : p.α * (p.v + ε) ≤ 1 - weighted.βdagger)
    {n : ℕ} (hn : n < upperStrategyClimbStop weighted ε) :
    let g := civicWeightedGradient p ρ
      (marginClimbPath p ρ ε n).1 (marginClimbPath p ρ ε n).2
    (marginClimbControlSequence p ρ ε n) ^ 2 / 2 =
      (2 / p.α) * (-g) *
        ((marginClimbPath p ρ ε (n + 1)).1 -
          (marginClimbPath p ρ ε n).1) + ε ^ 2 / 2 := by
  let g := civicWeightedGradient p ρ
    (marginClimbPath p ρ ε n).1 (marginClimbPath p ρ ε n).2
  obtain ⟨hstep, hgNonneg, _hgUpper⟩ :=
    marginClimb_before_stop_step_data model ss hcoop weighted hε hroom hn
  have hcontrol : marginClimbControlSequence p ρ ε n = 2 * (-g) + ε := by
    simp only [marginClimbControlSequence, marginClimbControl, doublingControl,
      g]
    rw [max_eq_left hgNonneg]
  rw [hcontrol, hstep]
  field_simp [model.α_pos.ne']
  ring

/-- The left barrier work accumulated by the climb through its first crossing
is the barrier area plus only the Lipschitz mesh error and the single final
overshoot rectangle. -/
theorem marginClimb_barrier_work_le
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ ε L : ℝ}
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε)
    (hroom : p.α * (p.v + ε) ≤ 1 - weighted.βdagger)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p ρ) L
      0 weighted.βdagger) :
    (∑ n ∈ Finset.range (upperStrategyClimbStop weighted ε),
        weightedBarrierIntegrand p ρ (marginClimbPath p ρ ε n).1 *
          ((marginClimbPath p ρ ε (n + 1)).1 -
            (marginClimbPath p ρ ε n).1)) ≤
      weightedBarrierArea weighted +
        (L / 2) * (p.α * (p.v + ε)) +
        p.v * (p.α * (p.v + ε)) := by
  let β : ℕ → ℝ := fun n ↦ (marginClimbPath p ρ ε n).1
  let f : ℝ → ℝ := weightedBarrierIntegrand p ρ
  let T : ℕ := upperStrategyClimbStop weighted ε
  let M : ℕ := T - 1
  let δ : ℝ := p.α * (p.v + ε)
  have hδpos : 0 < δ := by
    dsimp only [δ]
    exact mul_pos model.α_pos (add_pos model.v_pos hε)
  have hcross : weighted.βdagger < β T := by
    simpa only [β, T] using upperStrategyClimbStop_crosses model weighted hε
  have hTpos : 0 < T := by
    by_contra hnot
    have hTzero : T = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hTzero] at hcross
    simp only [β, marginClimbPath_zero, calibratedPoint] at hcross
    linarith [weighted.βdagger_mem.1]
  have hMsucc : M + 1 = T := by
    dsimp only [M]
    omega
  have hMlt : M < T := by omega
  have hmono : Monotone β := by
    simpa only [β] using monotone_marginClimbPolicy model ρ ε hε.le
  have hβmem : ∀ n ≤ M, β n ∈ Icc (0 : ℝ) weighted.βdagger := by
    intro n hn
    have hnT : n < T := by omega
    have hunit := (marginClimbPath_isControlled p ρ ε).policy_mem n
    exact ⟨hunit.1, by
      simpa only [β, T] using
        marginClimbPath_le_saddle_before_stop model weighted hε hnT⟩
  have hcont : ContinuousOn f (Icc (0 : ℝ) weighted.βdagger) := by
    simpa only [f] using continuousOn_weightedBarrierIntegrand model ρ weighted
  have hRiemann :
      (∑ n ∈ Finset.range M, f (β n) * (β (n + 1) - β n)) ≤
        (∫ z in β 0..β M, f z) +
          (L / 2) * ∑ n ∈ Finset.range M, (β (n + 1) - β n) ^ 2 :=
    leftRiemannSum_le_integral_add_lipschitz hcont hL hβmem
      (fun n _hn ↦ hmono n.le_succ)
  have hstart : β 0 = 0 := by
    simp only [β, marginClimbPath_zero, calibratedPoint]
  have hintegral : (∫ z in β 0..β M, f z) ≤ weightedBarrierArea weighted := by
    have htail : 0 ≤ ∫ z in β M..weighted.βdagger, f z := by
      apply intervalIntegral.integral_nonneg (hβmem M le_rfl).2
      intro z hz
      exact weighted.barrier_nonneg_before
        ⟨(hβmem M le_rfl).1.trans hz.1, hz.2⟩
    have hleftInt : IntervalIntegrable f MeasureTheory.volume (β 0) (β M) := by
      have hsubset : [[β 0, β M]] ⊆ Icc (0 : ℝ) weighted.βdagger := by
        rw [uIcc_of_le (hmono (Nat.zero_le M))]
        intro z hz
        exact ⟨(hβmem 0 (Nat.zero_le M)).1.trans hz.1,
          hz.2.trans (hβmem M le_rfl).2⟩
      exact (hcont.mono hsubset).intervalIntegrable
    have hrightInt : IntervalIntegrable f MeasureTheory.volume
        (β M) weighted.βdagger := by
      have hsubset : [[β M, weighted.βdagger]] ⊆
          Icc (0 : ℝ) weighted.βdagger := by
        rw [uIcc_of_le (hβmem M le_rfl).2]
        intro z hz
        exact ⟨(hβmem M le_rfl).1.trans hz.1, hz.2⟩
      exact (hcont.mono hsubset).intervalIntegrable
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      hleftInt hrightInt
    simp only [weightedBarrierArea, f, hstart]
    simpa only [f, hstart] using (show
      (∫ z in β 0..β M, f z) ≤
        ∫ z in β 0..weighted.βdagger, f z by linarith)
  have hsquares :
      (∑ n ∈ Finset.range M, (β (n + 1) - β n) ^ 2) ≤ δ := by
    have hsum :
        (∑ n ∈ Finset.range M, (β (n + 1) - β n) ^ 2) ≤
          ∑ n ∈ Finset.range M, δ * (β (n + 1) - β n) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnM : n < M := Finset.mem_range.mp hn
      have hnT : n < T := hnM.trans_le hMlt.le
      have hinc := marginClimb_before_stop_increment_bounds
        model ss hcoop weighted hε hroom
        (by simpa only [T] using hnT)
      have hincNonneg : 0 ≤ β (n + 1) - β n :=
        sub_nonneg.mpr (hmono n.le_succ)
      have hincUpper : β (n + 1) - β n ≤ δ := by
        simpa only [β, δ] using hinc.2
      nlinarith
    have htel :
        (∑ n ∈ Finset.range M, δ * (β (n + 1) - β n)) =
          δ * (β M - β 0) := by
      rw [← Finset.mul_sum, Finset.sum_range_sub]
    have hβMle : β M ≤ 1 :=
      (hβmem M le_rfl).2.trans weighted.βdagger_mem.2.le
    calc
      (∑ n ∈ Finset.range M, (β (n + 1) - β n) ^ 2) ≤
          ∑ n ∈ Finset.range M, δ * (β (n + 1) - β n) := hsum
      _ = δ * (β M - β 0) := htel
      _ ≤ δ := by
        rw [hstart]
        nlinarith
  have hpartial :
      (∑ n ∈ Finset.range M, f (β n) * (β (n + 1) - β n)) ≤
        weightedBarrierArea weighted + (L / 2) * δ := by
    have hLhalf : 0 ≤ L / 2 := div_nonneg hL.nonneg (by norm_num)
    have herr := mul_le_mul_of_nonneg_left hsquares hLhalf
    linarith
  have hfinalMem : β M ∈ Icc (0 : ℝ) weighted.βdagger := hβmem M le_rfl
  have hfinalNonneg : 0 ≤ f (β M) := by
    simpa only [f] using weighted.barrier_nonneg_before hfinalMem
  have hfinalLe : f (β M) ≤ p.v := by
    simpa only [f] using weighted.barrier_le_v model hcoop hfinalMem
  have hfinalInc := marginClimb_before_stop_increment_bounds
    model ss hcoop weighted hε hroom (by simpa only [T] using hMlt)
  have hfinalIncNonneg : 0 ≤ β (M + 1) - β M :=
    sub_nonneg.mpr (hmono M.le_succ)
  have hfinalIncLe : β (M + 1) - β M ≤ δ := by
    simpa only [β, δ] using hfinalInc.2
  have hfinal : f (β M) * (β (M + 1) - β M) ≤ p.v * δ :=
    mul_le_mul hfinalLe hfinalIncLe hfinalIncNonneg model.v_pos.le
  change (∑ n ∈ Finset.range T, f (β n) * (β (n + 1) - β n)) ≤ _
  rw [← hMsucc, Finset.sum_range_succ]
  linarith

/-- The work done against the exact off-characteristic gradient differs from
the stationary barrier work by at most the uniform `O(α)` stock-lag term. -/
theorem marginClimb_negative_gradient_work_le
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ ε L : ℝ} (hρ : 0 ≤ ρ)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε)
    (hroom : p.α * (p.v + ε) ≤ 1 - weighted.βdagger)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p ρ) L
      0 weighted.βdagger) :
    (∑ n ∈ Finset.range (upperStrategyClimbStop weighted ε),
        (-civicWeightedGradient p ρ
            (marginClimbPath p ρ ε n).1
            (marginClimbPath p ρ ε n).2) *
          ((marginClimbPath p ρ ε (n + 1)).1 -
            (marginClimbPath p ρ ε n).1)) ≤
      weightedBarrierArea weighted +
        (L / 2 + p.v +
          2 * p.c * driftStationaryStockLipschitzBound p / p.lambda₀) *
            (p.α * (p.v + ε)) := by
  let β : ℕ → ℝ := fun n ↦ (marginClimbPath p ρ ε n).1
  let x : ℕ → LoopState := marginClimbPath p ρ ε
  let f : ℝ → ℝ := weightedBarrierIntegrand p ρ
  let T : ℕ := upperStrategyClimbStop weighted ε
  let δ : ℝ := p.α * (p.v + ε)
  let B : ℝ := driftStationaryStockLipschitzBound p * δ / p.lambda₀
  let E : ℝ := 2 * p.c * B
  have hδpos : 0 < δ := by
    dsimp only [δ]
    exact mul_pos model.α_pos (add_pos model.v_pos hε)
  have hBpos : 0 < B := by
    dsimp only [B]
    exact div_pos
      (mul_pos (driftStationaryStockLipschitzBound_pos model) hδpos)
      model.lambda₀_pos
  have hEpos : 0 < E := by
    dsimp only [E]
    exact mul_pos (mul_pos two_pos model.c_pos) hBpos
  have hmono : Monotone β := by
    simpa only [β] using monotone_marginClimbPolicy model ρ ε hε.le
  have hterm : ∀ n < T,
      (-civicWeightedGradient p ρ (x n).1 (x n).2) *
          (β (n + 1) - β n) ≤
        f (β n) * (β (n + 1) - β n) +
          E * (β (n + 1) - β n) := by
    intro n hn
    have hnStop : n < upperStrategyClimbStop weighted ε := by
      simpa only [T] using hn
    have hpolicy := (marginClimbPath_isControlled p ρ ε).policy_mem n
    have hlagNonneg : 0 ≤ stationaryStockLag p (x n) := by
      simp only [stationaryStockLag, x]
      exact sub_nonneg.mpr
        (marginClimbPath_stock_le_stationaryStock model ss hε.le n)
    have hlagLe : stationaryStockLag p (x n) ≤ B := by
      simpa only [x, B, δ] using
        marginClimb_stationaryStockLag_le model ss hcoop weighted hε hroom
          hnStop.le
    have hcoefLe := weighted_stock_coefficient_le_two_c model hρ hpolicy
    have hcoefLag :
        (2 * p.c * (1 - p.c * (x n).1) - ρ) *
            stationaryStockLag p (x n) ≤ E := by
      have hmul := mul_le_mul hcoefLe hlagLe hlagNonneg
        (mul_nonneg (by norm_num) model.c_pos.le)
      simpa only [E] using hmul
    have hid := neg_civicWeightedGradient_eq_barrier_add_lag
      p ρ (x n).1 (x n).2
    have hinc : 0 ≤ β (n + 1) - β n :=
      sub_nonneg.mpr (hmono n.le_succ)
    have hbase : -civicWeightedGradient p ρ (x n).1 (x n).2 ≤
        f (β n) + E := by
      simpa only [f, β] using (show
        -civicWeightedGradient p ρ (x n).1 (x n).2 ≤
          weightedBarrierIntegrand p ρ (x n).1 + E by linarith)
    have := mul_le_mul_of_nonneg_right hbase hinc
    nlinarith
  have hsum :
      (∑ n ∈ Finset.range T,
          (-civicWeightedGradient p ρ (x n).1 (x n).2) *
            (β (n + 1) - β n)) ≤
        (∑ n ∈ Finset.range T,
          f (β n) * (β (n + 1) - β n)) + E := by
    have hpoint :
        (∑ n ∈ Finset.range T,
            (-civicWeightedGradient p ρ (x n).1 (x n).2) *
              (β (n + 1) - β n)) ≤
          ∑ n ∈ Finset.range T,
            (f (β n) * (β (n + 1) - β n) +
              E * (β (n + 1) - β n)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hterm n (Finset.mem_range.mp hn)
    have htel :
        ∑ n ∈ Finset.range T, (β (n + 1) - β n) = β T - β 0 :=
      Finset.sum_range_sub β T
    have hstart : β 0 = 0 := by
      simp only [β, marginClimbPath_zero, calibratedPoint]
    have hend : β T ≤ 1 :=
      (marginClimbPath_isControlled p ρ ε).policy_mem T |>.2
    have herror :
        E * ∑ n ∈ Finset.range T, (β (n + 1) - β n) ≤ E := by
      rw [htel, hstart]
      nlinarith
    calc
      _ ≤ ∑ n ∈ Finset.range T,
          (f (β n) * (β (n + 1) - β n) +
            E * (β (n + 1) - β n)) := hpoint
      _ = (∑ n ∈ Finset.range T,
          f (β n) * (β (n + 1) - β n)) +
          E * ∑ n ∈ Finset.range T, (β (n + 1) - β n) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ (∑ n ∈ Finset.range T,
          f (β n) * (β (n + 1) - β n)) + E :=
        by linarith
  have hbarrier := marginClimb_barrier_work_le
    model ss hcoop weighted hε hroom hL
  change (∑ n ∈ Finset.range T,
    (-civicWeightedGradient p ρ (x n).1 (x n).2) *
      (β (n + 1) - β n)) ≤ _
  have hbarrier' :
      (∑ n ∈ Finset.range T, f (β n) * (β (n + 1) - β n)) ≤
        weightedBarrierArea weighted + (L / 2) * δ + p.v * δ := by
    simpa only [T, f, β, δ] using hbarrier
  dsimp only [E, B] at hsum
  have hcombined :
      (∑ n ∈ Finset.range T,
          (-civicWeightedGradient p ρ (x n).1 (x n).2) *
            (β (n + 1) - β n)) ≤
        weightedBarrierArea weighted +
          (L / 2 + p.v +
            2 * p.c * driftStationaryStockLipschitzBound p / p.lambda₀) * δ := by
    calc
      _ ≤ (∑ n ∈ Finset.range T,
          f (β n) * (β (n + 1) - β n)) +
            2 * p.c *
              (driftStationaryStockLipschitzBound p * δ / p.lambda₀) := hsum
      _ ≤ (weightedBarrierArea weighted + (L / 2) * δ + p.v * δ) +
            2 * p.c *
              (driftStationaryStockLipschitzBound p * δ / p.lambda₀) :=
        by linarith
      _ = weightedBarrierArea weighted +
          (L / 2 + p.v +
            2 * p.c * driftStationaryStockLipschitzBound p / p.lambda₀) * δ := by
        ring
  simpa only [δ] using hcombined

/-- The action spent during the climb phase alone. -/
noncomputable def upwardStrategyClimbAction
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (ε : ℝ) : ℝ :=
  controlAction (marginClimbControlSequence p ρ ε)
    (upperStrategyClimbStop weighted ε)

/-- Exact summed climb-action ledger. -/
theorem upwardStrategyClimbAction_eq
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ ε : ℝ}
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε)
    (hroom : p.α * (p.v + ε) ≤ 1 - weighted.βdagger) :
    upwardStrategyClimbAction weighted ε =
      (2 / p.α) *
        (∑ n ∈ Finset.range (upperStrategyClimbStop weighted ε),
          (-civicWeightedGradient p ρ
              (marginClimbPath p ρ ε n).1
              (marginClimbPath p ρ ε n).2) *
            ((marginClimbPath p ρ ε (n + 1)).1 -
              (marginClimbPath p ρ ε n).1)) +
      (upperStrategyClimbStop weighted ε : ℝ) * (ε ^ 2 / 2) := by
  let T := upperStrategyClimbStop weighted ε
  calc
    upwardStrategyClimbAction weighted ε =
        ∑ n ∈ Finset.range T,
          (marginClimbControlSequence p ρ ε n) ^ 2 / 2 := by
      simp only [upwardStrategyClimbAction, controlAction, T,
        div_eq_mul_inv, Finset.mul_sum]
      ring_nf
    _ = ∑ n ∈ Finset.range T,
        ((2 / p.α) *
          (-civicWeightedGradient p ρ
              (marginClimbPath p ρ ε n).1
              (marginClimbPath p ρ ε n).2) *
            ((marginClimbPath p ρ ε (n + 1)).1 -
              (marginClimbPath p ρ ε n).1) + ε ^ 2 / 2) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact marginClimb_action_summand_eq model ss hcoop weighted hε hroom
        (by simpa only [T] using Finset.mem_range.mp hn)
    _ = (2 / p.α) *
        (∑ n ∈ Finset.range T,
          (-civicWeightedGradient p ρ
              (marginClimbPath p ρ ε n).1
              (marginClimbPath p ρ ε n).2) *
            ((marginClimbPath p ρ ε (n + 1)).1 -
              (marginClimbPath p ρ ε n).1)) +
        (T : ℝ) * (ε ^ 2 / 2) := by
      rw [Finset.sum_add_distrib]
      have hfactor :
          (∑ n ∈ Finset.range T,
            (2 / p.α) *
              (-civicWeightedGradient p ρ
                  (marginClimbPath p ρ ε n).1
                  (marginClimbPath p ρ ε n).2) *
                ((marginClimbPath p ρ ε (n + 1)).1 -
                  (marginClimbPath p ρ ε n).1)) =
            (2 / p.α) *
              ∑ n ∈ Finset.range T,
                (-civicWeightedGradient p ρ
                    (marginClimbPath p ρ ε n).1
                    (marginClimbPath p ρ ε n).2) *
                  ((marginClimbPath p ρ ε (n + 1)).1 -
                    (marginClimbPath p ρ ε n).1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _hn
        ring
      rw [hfactor]
      congr 1
      simp

/-- Quantitative climb-action upper bound. -/
theorem upwardStrategyClimbAction_le
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ ε L : ℝ} (hρ : 0 ≤ ρ)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε)
    (hroom : p.α * (p.v + ε) ≤ 1 - weighted.βdagger)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p ρ) L
      0 weighted.βdagger) :
    upwardStrategyClimbAction weighted ε ≤
      (2 / p.α) * weightedBarrierArea weighted +
      (2 / p.α) *
        ((L / 2 + p.v +
          2 * p.c * driftStationaryStockLipschitzBound p / p.lambda₀) *
            (p.α * (p.v + ε))) +
      (upperStrategyClimbStop weighted ε : ℝ) * (ε ^ 2 / 2) := by
  rw [upwardStrategyClimbAction_eq model ss hcoop weighted hε hroom]
  have hwork := marginClimb_negative_gradient_work_le
    model ss hρ hcoop weighted hε hroom hL
  have hscale : 0 ≤ 2 / p.α := div_nonneg (by norm_num) model.α_pos.le
  have hscaled := mul_le_mul_of_nonneg_left hwork hscale
  nlinarith

/-- Before the crossing stop, the spliced strategy's realized control is the
autonomous margin-climb control. -/
theorem twoPhaseUpperControl_eq_marginClimb_before
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (ε : ℝ) {n : ℕ} (hn : n < upperStrategyClimbStop weighted ε) :
    twoPhaseUpperControl weighted ε n =
      marginClimbControlSequence p ρ ε n := by
  simp only [twoPhaseUpperControl, twoPhaseUpperControlAt, if_pos hn,
    marginClimbControlSequence]
  rw [twoPhaseUpperPath_eq_marginClimb_of_le weighted ε hn.le]

/-- After crossing and before the total stop, the spliced control is exactly
the indexed cancelling-hold control. -/
theorem twoPhaseUpperControl_eq_cancellingHold
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (ε : ℝ) {k : ℕ} (hk : k < upperStrategyHoldStop weighted ε) :
    twoPhaseUpperControl weighted ε
        (upperStrategyClimbStop weighted ε + k) =
      cancellingHoldControl p ρ (upperStrategyClimbState weighted ε).1
        (upperStrategyClimbState weighted ε).2 k := by
  have hnot : ¬ upperStrategyClimbStop weighted ε + k <
      upperStrategyClimbStop weighted ε := by omega
  have hphase : upperStrategyClimbStop weighted ε + k <
      upperStrategyTotalStop weighted ε := by
    simp only [upperStrategyTotalStop]
    omega
  have hsub : upperStrategyClimbStop weighted ε + k -
      upperStrategyClimbStop weighted ε = k := by omega
  simp only [twoPhaseUpperControl, twoPhaseUpperControlAt, if_neg hnot,
    if_pos hphase, hsub]

/-- The complete finite action splits exactly into climb and hold actions. -/
theorem upwardStrategyCostEpsilon_eq_climb_add_hold
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (ε : ℝ) :
    upwardStrategyCostEpsilon weighted ε =
      upwardStrategyClimbAction weighted ε +
        upwardStrategyHoldAction weighted ε := by
  let T := upperStrategyClimbStop weighted ε
  let H := upperStrategyHoldStop weighted ε
  have hclimb :
      (∑ n ∈ Finset.range T, (twoPhaseUpperControl weighted ε n) ^ 2) =
        ∑ n ∈ Finset.range T,
          (marginClimbControlSequence p ρ ε n) ^ 2 := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [twoPhaseUpperControl_eq_marginClimb_before weighted ε
      (by simpa only [T] using Finset.mem_range.mp hn)]
  have hhold :
      (∑ k ∈ Finset.range H,
          (twoPhaseUpperControl weighted ε (T + k)) ^ 2) =
        ∑ k ∈ Finset.range H,
          (cancellingHoldControl p ρ (upperStrategyClimbState weighted ε).1
            (upperStrategyClimbState weighted ε).2 k) ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [twoPhaseUpperControl_eq_cancellingHold weighted ε
      (by simpa only [H] using Finset.mem_range.mp hk)]
  simp only [upwardStrategyCostEpsilon, upwardStrategyClimbAction,
    upwardStrategyHoldAction, controlAction, upperStrategyTotalStop]
  change (1 / 2 : ℝ) *
      ∑ n ∈ Finset.range (T + H), (twoPhaseUpperControl weighted ε n) ^ 2 = _
  rw [Finset.sum_range_add, hclimb, hhold]
  ring

/-- Every printed positive-margin cost lies above the infimum defining
`S↑`. -/
theorem upwardStrategyCost_le_upwardStrategyCostEpsilon
    {p : LoopParams} {ρ ε : ℝ}
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε) :
    upwardStrategyCost weighted ≤ upwardStrategyCostEpsilon weighted ε := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro a ⟨δ, hδ, rfl⟩
    exact controlAction_nonneg _ _
  · exact ⟨ε, hε, rfl⟩

/-- Explicit finite-strategy upper bound for `S↑_ε`, retaining the exact
crossing-count margin term and the quadratic hold remainder. -/
theorem upwardStrategyCostEpsilon_le
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ ε L : ℝ} (hρ : 0 ≤ ρ)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε)
    (hroom : p.α * (p.v + ε) ≤ 1 - weighted.βdagger)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p ρ) L
      0 weighted.βdagger) :
    upwardStrategyCostEpsilon weighted ε ≤
      (2 / p.α) * weightedBarrierArea weighted +
      (2 / p.α) *
        ((L / 2 + p.v +
          2 * p.c * driftStationaryStockLipschitzBound p / p.lambda₀) *
            (p.α * (p.v + ε))) +
      (upperStrategyClimbStop weighted ε : ℝ) * (ε ^ 2 / 2) +
      2 * p.c ^ 2 *
        (driftStationaryStockLipschitzBound p *
          (p.α * (p.v + ε)) / p.lambda₀) ^ 2 / p.lambda₀ := by
  rw [upwardStrategyCostEpsilon_eq_climb_add_hold]
  have hclimb := upwardStrategyClimbAction_le
    model ss hρ hcoop weighted hε hroom hL
  have hhold := upwardStrategyHoldAction_le
    model ss hρ hcoop weighted hε hroom
  linarith

/-- The ceiling bound also controls the product of the crossing count with
one guaranteed margin increment. -/
theorem upperStrategyClimbStop_mul_margin_le
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ ε : ℝ}
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε) :
    (upperStrategyClimbStop weighted ε : ℝ) * (p.α * ε) ≤
      weighted.βdagger + p.α * ε := by
  let step : ℝ := p.α * ε
  let C : ℕ := Nat.ceil (weighted.βdagger / step)
  have hstep : 0 < step := mul_pos model.α_pos hε
  have hstop := upperStrategyClimbStop_le_natCeil
    model ss hcoop weighted hε
  have hstopReal : (upperStrategyClimbStop weighted ε : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast hstop
  have hceil : (C : ℝ) < weighted.βdagger / step + 1 := by
    simpa only [C] using Nat.ceil_lt_add_one
      (div_nonneg weighted.βdagger_mem.1.le hstep.le)
  have hleft := mul_le_mul_of_nonneg_right hstopReal hstep.le
  have hright := mul_lt_mul_of_pos_right hceil hstep
  have hcancel : (weighted.βdagger / step + 1) * step =
      weighted.βdagger + step := by
    field_simp [hstep.ne']
  dsimp only [step] at hleft ⊢
  rw [hcancel] at hright
  exact hleft.trans hright.le

/-- A fixed, primitive-dependent bound for all nonleading terms of the
`ε=α` strategy when `0 < α ≤ 1`. -/
def smallRateStrategyRemainderBound (p : LoopParams) (L : ℝ) : ℝ :=
  2 * (L / 2 + p.v +
      2 * p.c * driftStationaryStockLipschitzBound p / p.lambda₀) *
      (p.v + 1) +
    1 +
    2 * p.c ^ 2 *
      (driftStationaryStockLipschitzBound p *
        (p.v + 1) / p.lambda₀) ^ 2 / p.lambda₀

theorem smallRateStrategyRemainderBound_nonneg
    {p : LoopParams} (model : DriftModelAssumptions p) {L : ℝ}
    (hL : 0 ≤ L) :
    0 ≤ smallRateStrategyRemainderBound p L := by
  have hK : 0 ≤ driftStationaryStockLipschitzBound p :=
    (driftStationaryStockLipschitzBound_pos model).le
  have hcoef : 0 ≤ L / 2 + p.v +
      2 * p.c * driftStationaryStockLipschitzBound p / p.lambda₀ := by
    have hterm : 0 ≤
        2 * p.c * driftStationaryStockLipschitzBound p / p.lambda₀ :=
      div_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) model.c_pos.le) hK)
        model.lambda₀_pos.le
    linarith [model.v_pos, div_nonneg hL (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [smallRateStrategyRemainderBound]
  have hvOne : 0 ≤ p.v + 1 := by linarith [model.v_pos]
  have hfirst : 0 ≤ 2 * (L / 2 + p.v +
      2 * p.c * driftStationaryStockLipschitzBound p / p.lambda₀) *
      (p.v + 1) := mul_nonneg (mul_nonneg (by norm_num) hcoef) hvOne
  have hthird : 0 ≤ 2 * p.c ^ 2 *
      (driftStationaryStockLipschitzBound p * (p.v + 1) /
        p.lambda₀) ^ 2 / p.lambda₀ :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg p.c))
      (sq_nonneg _)) model.lambda₀_pos.le
  linarith

/-- Pointwise lower half of the fixed-primitives family sandwich. -/
theorem upwardStrategyCostAtRate_lower_bound
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {ρ L α : ℝ} (hρ : 0 ≤ ρ) (hρcure : ρ < cureThreshold p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p ρ) L
      0 weighted.βdagger)
    (hα : 0 < α) (hαle : α ≤ p.α) :
    (2 / (α * (1 + 2 * α * L))) * weightedBarrierArea weighted ≤
      upwardStrategyCostAtRate weighted α := by
  let q := withOperatorRate p α
  let modelq : DriftModelAssumptions q := model.withOperatorRate hα
  let ssq : SmallStepAssumption q :=
    ss.withOperatorRate model hα.le hαle
  let thresholdq : ThresholdAssumption q := threshold.withOperatorRate α
  let weightedq : WeightedThresholdAssumption q ρ := weighted.withOperatorRate α
  have hLq : IsLipschitzConstantOn (weightedBarrierIntegrand q ρ) L
      0 weightedq.βdagger := by
    change IsLipschitzConstantOn
      (weightedBarrierIntegrand (withOperatorRate p α) ρ) L
        0 weighted.βdagger
    have hfun : weightedBarrierIntegrand (withOperatorRate p α) ρ =
        weightedBarrierIntegrand p ρ := by
      funext β
      exact withOperatorRate_weightedBarrierIntegrand p α ρ β
    rw [hfun]
    exact hL
  have hlower := civicQuasipotential_lower_bound
    modelq ssq thresholdq hρ (by simpa [q] using hρcure)
      (by simpa [q] using hcoop) weightedq hLq
  have hupper := civicQuasipotential_le_upwardStrategyCost
    modelq ssq (by simpa [q] using hρcure)
      (by simpa [q] using hcoop) weightedq
  have hsandwich := hlower.trans hupper
  change (2 / (α * (1 + 2 * α * L))) *
      weightedBarrierArea (weighted.withOperatorRate α) ≤
        upwardStrategyCost (weighted.withOperatorRate α) at hsandwich
  rw [weightedBarrierArea_withOperatorRate] at hsandwich
  exact hsandwich

/-- Pointwise upper half: for `ε=α`, all nonleading terms are bounded by one
constant independent of the replacement adaptation rate. -/
theorem upwardStrategyCostAtRate_upper_bound
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ L α : ℝ} (hρ : 0 ≤ ρ)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p ρ) L
      0 weighted.βdagger)
    (hα : 0 < α) (hαle : α ≤ p.α) (hαone : α ≤ 1)
    (hroom : α * (p.v + α) ≤ 1 - weighted.βdagger) :
    upwardStrategyCostAtRate weighted α ≤
      (2 / α) * weightedBarrierArea weighted +
        smallRateStrategyRemainderBound p L := by
  let q := withOperatorRate p α
  let modelq : DriftModelAssumptions q := model.withOperatorRate hα
  let ssq : SmallStepAssumption q :=
    ss.withOperatorRate model hα.le hαle
  let weightedq : WeightedThresholdAssumption q ρ := weighted.withOperatorRate α
  let K := driftStationaryStockLipschitzBound p
  let C := L / 2 + p.v + 2 * p.c * K / p.lambda₀
  have hLq : IsLipschitzConstantOn (weightedBarrierIntegrand q ρ) L
      0 weightedq.βdagger := by
    change IsLipschitzConstantOn
      (weightedBarrierIntegrand (withOperatorRate p α) ρ) L
        0 weighted.βdagger
    have hfun : weightedBarrierIntegrand (withOperatorRate p α) ρ =
        weightedBarrierIntegrand p ρ := by
      funext β
      exact withOperatorRate_weightedBarrierIntegrand p α ρ β
    rw [hfun]
    exact hL
  have hcostInf := upwardStrategyCost_le_upwardStrategyCostEpsilon weightedq hα
  have hcostFinite := upwardStrategyCostEpsilon_le
    modelq ssq hρ (by simpa [q] using hcoop) weightedq hα
      (by
        change α * (p.v + α) ≤ 1 - weighted.βdagger
        exact hroom) hLq
  have hcost := hcostInf.trans hcostFinite
  have hcountRaw := upperStrategyClimbStop_mul_margin_le
    modelq ssq (by simpa [q] using hcoop) weightedq hα
  have hcount :
      (upperStrategyClimbStop weightedq α : ℝ) * (α ^ 2 / 2) ≤ 1 := by
    have hraw :
        (upperStrategyClimbStop weightedq α : ℝ) * (α * α) ≤
          weighted.βdagger + α * α := by
      change (upperStrategyClimbStop weightedq α : ℝ) * (α * α) ≤
        weighted.βdagger + α * α at hcountRaw
      exact hcountRaw
    have halphaSq : α ^ 2 ≤ 1 := by nlinarith
    have hroot : weighted.βdagger ≤ 1 := weighted.βdagger_mem.2.le
    nlinarith
  have hK : 0 < K := by
    simpa only [K] using driftStationaryStockLipschitzBound_pos model
  have hC : 0 ≤ C := by
    dsimp only [C]
    have hterm : 0 ≤ 2 * p.c * K / p.lambda₀ :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) model.c_pos.le) hK.le)
        model.lambda₀_pos.le
    linarith [hL.nonneg, model.v_pos]
  have hvα : p.v + α ≤ p.v + 1 := by linarith
  have hscaledError :
      (2 / α) * (C * (α * (p.v + α))) ≤
        2 * C * (p.v + 1) := by
    have heq : (2 / α) * (C * (α * (p.v + α))) =
        2 * C * (p.v + α) := by
      field_simp [hα.ne']
    rw [heq]
    exact mul_le_mul_of_nonneg_left hvα (mul_nonneg (by norm_num) hC)
  have htransit : α * (p.v + α) ≤ p.v + 1 := by
    have hsumPos : 0 ≤ p.v + α := (add_pos model.v_pos hα).le
    calc
      α * (p.v + α) ≤ 1 * (p.v + α) :=
        mul_le_mul_of_nonneg_right hαone hsumPos
      _ ≤ p.v + 1 := by simpa only [one_mul] using hvα
  have hlagScale :
      K * (α * (p.v + α)) / p.lambda₀ ≤
        K * (p.v + 1) / p.lambda₀ := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left htransit hK.le) model.lambda₀_pos.le
  have hlagLeft : 0 ≤ K * (α * (p.v + α)) / p.lambda₀ := by
    exact div_nonneg
      (mul_nonneg hK.le (mul_nonneg hα.le (add_pos model.v_pos hα).le))
      model.lambda₀_pos.le
  have hlagRight : 0 ≤ K * (p.v + 1) / p.lambda₀ := by
    exact div_nonneg
      (mul_nonneg hK.le (by linarith [model.v_pos])) model.lambda₀_pos.le
  have hhold :
      2 * p.c ^ 2 * (K * (α * (p.v + α)) / p.lambda₀) ^ 2 /
          p.lambda₀ ≤
        2 * p.c ^ 2 * (K * (p.v + 1) / p.lambda₀) ^ 2 /
          p.lambda₀ := by
    have hsquare := (sq_le_sq₀ hlagLeft hlagRight).2 hlagScale
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsquare
        (mul_nonneg (by norm_num) (sq_nonneg p.c))) model.lambda₀_pos.le
  have hcost' : upwardStrategyCostAtRate weighted α ≤
      (2 / α) * weightedBarrierArea weighted +
        (2 / α) * (C * (α * (p.v + α))) +
        (upperStrategyClimbStop weightedq α : ℝ) * (α ^ 2 / 2) +
        2 * p.c ^ 2 * (K * (α * (p.v + α)) / p.lambda₀) ^ 2 /
          p.lambda₀ := by
    rw [weightedBarrierArea_withOperatorRate] at hcost
    simpa only [upwardStrategyCostAtRate, q, weightedq,
      withOperatorRate_alpha, withOperatorRate_v, withOperatorRate_c,
      withOperatorRate_lambda₀, withOperatorRate_eta, withOperatorRate_I,
      driftStationaryStockLipschitzBound_withOperatorRate, K, C,
      ] using hcost
  simp only [smallRateStrategyRemainderBound]
  dsimp only [C, K] at hscaledError hhold hcost' ⊢
  linarith

/-- The corrected barrier area is strictly positive. -/
theorem weightedBarrierArea_pos
    {p : LoopParams} (model : DriftModelAssumptions p) {ρ : ℝ}
    (weighted : WeightedThresholdAssumption p ρ) :
    0 < weightedBarrierArea weighted := by
  have hcont := continuousOn_weightedBarrierIntegrand model ρ weighted
  have hnonneg : ∀ b ∈ Ioc (0 : ℝ) weighted.βdagger,
      0 ≤ weightedBarrierIntegrand p ρ b := by
    intro b hb
    exact weighted.barrier_nonneg_before ⟨hb.1.le, hb.2⟩
  have hpositive : ∃ b ∈ Icc (0 : ℝ) weighted.βdagger,
      0 < weightedBarrierIntegrand p ρ b := by
    exact ⟨0, ⟨le_rfl, weighted.βdagger_mem.1.le⟩,
      weighted.barrier_pos_before
        ⟨le_rfl, weighted.βdagger_mem.1.le⟩ weighted.βdagger_mem.1⟩
  simpa only [weightedBarrierArea] using
    intervalIntegral.integral_pos weighted.βdagger_mem.1 hcont hnonneg hpositive

/-- Paper II, Proposition `prop:qpbounds`, `civic_drift.tex:354`:
holding every primitive except the adaptation rate fixed, the explicit upper
strategy has the printed relative `O(α)` expansion around the barrier area. -/
theorem upwardStrategyCostAtRate_relative_isBigO
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {ρ L : ℝ} (hρ : 0 ≤ ρ) (hρcure : ρ < cureThreshold p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p ρ) L
      0 weighted.βdagger) :
    Asymptotics.IsBigO (nhdsWithin 0 (Ioi (0 : ℝ)))
      (fun α ↦
        α * upwardStrategyCostAtRate weighted α /
            (2 * weightedBarrierArea weighted) - 1)
      (fun α ↦ α) := by
  let A := weightedBarrierArea weighted
  let C₀ := smallRateStrategyRemainderBound p L
  let C := 2 * L + C₀ / (2 * A)
  have hA : 0 < A := by
    simpa only [A] using weightedBarrierArea_pos model weighted
  have hC₀ : 0 ≤ C₀ := by
    simpa only [C₀] using
      smallRateStrategyRemainderBound_nonneg model hL.nonneg
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg (mul_nonneg (by norm_num) hL.nonneg)
      (div_nonneg hC₀ (mul_nonneg (by norm_num) hA.le))
  let d := (1 - weighted.βdagger) / (p.v + 1)
  have hd : 0 < d := by
    dsimp only [d]
    exact div_pos (sub_pos.mpr weighted.βdagger_mem.2)
      (by linarith [model.v_pos])
  have hbaseNhds : ∀ᶠ α : ℝ in 𝓝 0, α < p.α :=
    Iio_mem_nhds model.α_pos
  have honeNhds : ∀ᶠ α : ℝ in 𝓝 0, α < 1 :=
    Iio_mem_nhds zero_lt_one
  have hdNhds : ∀ᶠ α : ℝ in 𝓝 0, α < d :=
    Iio_mem_nhds hd
  have hbase : ∀ᶠ α : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)), α < p.α :=
    hbaseNhds.filter_mono inf_le_left
  have hone : ∀ᶠ α : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)), α < 1 :=
    honeNhds.filter_mono inf_le_left
  have hdsmall : ∀ᶠ α : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)), α < d :=
    hdNhds.filter_mono inf_le_left
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hbase, hone, hdsmall] with α hαmem
      hαbase hαone hαd
  have hα : 0 < α := hαmem
  have hroom : α * (p.v + α) ≤ 1 - weighted.βdagger := by
    have hvα : p.v + α ≤ p.v + 1 := by linarith
    have hfirst : α * (p.v + α) ≤ α * (p.v + 1) :=
      mul_le_mul_of_nonneg_left hvα hα.le
    have hvOne : 0 < p.v + 1 := by linarith [model.v_pos]
    have hsecond : α * (p.v + 1) ≤ 1 - weighted.βdagger := by
      have hαd' : α ≤ (1 - weighted.βdagger) / (p.v + 1) := by
        simpa only [d] using hαd.le
      exact (le_div_iff₀ hvOne).mp hαd'
    exact hfirst.trans hsecond
  have hlower := upwardStrategyCostAtRate_lower_bound
    model ss threshold hρ hρcure hcoop weighted hL hα hαbase.le
  have hupper := upwardStrategyCostAtRate_upper_bound
    model ss hρ hcoop weighted hL hα hαbase.le hαone.le hroom
  let S := upwardStrategyCostAtRate weighted α
  let R := α * S / (2 * A) - 1
  have hden : 0 < 2 * A := mul_pos two_pos hA
  have hcorrection : 0 < 1 + 2 * α * L := by
    have : 0 ≤ 2 * α * L :=
      mul_nonneg (mul_nonneg (by norm_num) hα.le) hL.nonneg
    linarith
  have hlowerRatio : 1 / (1 + 2 * α * L) ≤ α * S / (2 * A) := by
    have hscale : 0 ≤ α / (2 * A) := div_nonneg hα.le hden.le
    have hscaled := mul_le_mul_of_nonneg_left hlower hscale
    have hleft : (α / (2 * A)) *
        ((2 / (α * (1 + 2 * α * L))) * A) =
          1 / (1 + 2 * α * L) := by
      field_simp [hα.ne', hA.ne', hcorrection.ne']
    have hright : (α / (2 * A)) *
        upwardStrategyCostAtRate weighted α = α * S / (2 * A) := by
      dsimp only [S]
      ring
    rw [hleft, hright] at hscaled
    exact hscaled
  have hlowerR : -(2 * L) * α ≤ R := by
    let x : ℝ := 2 * α * L
    have hx : 0 ≤ x := by
      dsimp only [x]
      exact mul_nonneg (mul_nonneg (by norm_num) hα.le) hL.nonneg
    have hsqdiv : 0 ≤ x ^ 2 / (1 + x) :=
      div_nonneg (sq_nonneg x) (by dsimp only [x]; linarith)
    have hid : 1 / (1 + x) - 1 + x = x ^ 2 / (1 + x) := by
      field_simp [show 1 + x ≠ 0 by linarith]
      ring
    have hbase : -x ≤ 1 / (1 + x) - 1 := by linarith
    dsimp only [R, x] at hbase ⊢
    linarith
  have hupperRatio : α * S / (2 * A) ≤
      1 + α * C₀ / (2 * A) := by
    have hmul := mul_le_mul_of_nonneg_left hupper hα.le
    have hdiv := (div_le_div_iff_of_pos_right hden).2 hmul
    have hright : α * ((2 / α) * A + C₀) / (2 * A) =
        1 + α * C₀ / (2 * A) := by
      field_simp [hα.ne', hA.ne']
    dsimp only [S, C₀, A] at hdiv ⊢
    rw [hright] at hdiv
    exact hdiv
  have hupperR : R ≤ (C₀ / (2 * A)) * α := by
    dsimp only [R]
    calc
      α * S / (2 * A) - 1 ≤ α * C₀ / (2 * A) := by linarith
      _ = (C₀ / (2 * A)) * α := by ring
  have habs : |R| ≤ C * α := by
    apply abs_le.mpr
    constructor
    · have hcoef : 2 * L ≤ C := by
        dsimp only [C]
        exact le_add_of_nonneg_right
          (div_nonneg hC₀ (mul_nonneg (by norm_num) hA.le))
      have hmul := mul_le_mul_of_nonneg_right hcoef hα.le
      nlinarith
    · have hcoef : C₀ / (2 * A) ≤ C := by
        dsimp only [C]
        exact le_add_of_nonneg_left (mul_nonneg (by norm_num) hL.nonneg)
      exact hupperR.trans (mul_le_mul_of_nonneg_right hcoef hα.le)
  simpa only [Real.norm_eq_abs, abs_of_pos hα, R, S, A] using habs

/-! ## Weight comparative statics of the barrier integral -/

/-- The discriminant of the civic-weighted threshold quadratic. -/
def weightedThresholdDiscriminant (p : LoopParams) (ρ : ℝ) : ℝ :=
  thresholdLinearCoefficient p ^ 2 -
    4 * thresholdQuadraticCoefficient p *
      (thresholdConstantCoefficient p - ρ * p.I)

/-- The canonical larger root of the civic-weighted threshold quadratic. -/
noncomputable def weightedThresholdRoot (p : LoopParams) (ρ : ℝ) : ℝ :=
  (-thresholdLinearCoefficient p + Real.sqrt (weightedThresholdDiscriminant p ρ)) /
    (2 * thresholdQuadraticCoefficient p)

/-- At an oriented weighted threshold, the quadratic discriminant is the
square of the strictly positive numerator slope. -/
theorem weightedThresholdDiscriminant_eq_slope_sq
    {p : LoopParams} (model : DriftModelAssumptions p) {ρ : ℝ}
    (weighted : WeightedThresholdAssumption p ρ) :
    weightedThresholdDiscriminant p ρ =
      (2 * thresholdQuadraticCoefficient p * weighted.βdagger +
        thresholdLinearCoefficient p) ^ 2 := by
  have hr : weighted.βdagger ∈ Icc (0 : ℝ) 1 :=
    ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩
  have hden := thresholdDenominator_pos model hr
  have hnum : weightedThresholdNumerator p ρ weighted.βdagger = 0 := by
    have hgradient := weighted.gradient_zero
    rw [weightedStationaryGradient_eq_numerator_div model ρ hr] at hgradient
    exact (div_eq_zero_iff.mp hgradient).resolve_right hden.ne'
  have hpoly :
      thresholdQuadraticCoefficient p * weighted.βdagger ^ 2 +
          thresholdLinearCoefficient p * weighted.βdagger +
          (thresholdConstantCoefficient p - ρ * p.I) = 0 := by
    rw [weightedThresholdNumerator_eq_quadratic] at hnum
    simpa only [quadraticValue] using hnum
  simp only [weightedThresholdDiscriminant]
  linear_combination -4 * thresholdQuadraticCoefficient p * hpoly

/-- The canonical quadratic root agrees with every oriented weighted-threshold
bundle, so downstream calculus is independent of classical choice. -/
theorem weightedThresholdRoot_eq
    {p : LoopParams} (model : DriftModelAssumptions p) {ρ : ℝ}
    (weighted : WeightedThresholdAssumption p ρ) :
    weightedThresholdRoot p ρ = weighted.βdagger := by
  have hr : weighted.βdagger ∈ Icc (0 : ℝ) 1 :=
    ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩
  have hden := thresholdDenominator_pos model hr
  have hnum : weightedThresholdNumerator p ρ weighted.βdagger = 0 := by
    have hgradient := weighted.gradient_zero
    rw [weightedStationaryGradient_eq_numerator_div model ρ hr] at hgradient
    exact (div_eq_zero_iff.mp hgradient).resolve_right hden.ne'
  have hslope :
      0 < 2 * thresholdQuadraticCoefficient p * weighted.βdagger +
        thresholdLinearCoefficient p := by
    have hgradientSlope := weighted.gradientSlope_pos
    rw [weightedStationaryGradientSlope_eq_numeratorSlope_div_at_root
      model ρ hr hnum] at hgradientSlope
    have hnumerator : 0 < thresholdNumeratorSlope p weighted.βdagger :=
      (div_pos_iff_of_pos_right hden).mp hgradientSlope
    rwa [thresholdNumeratorSlope_eq_quadraticSlope] at hnumerator
  have hA := thresholdQuadraticCoefficient_pos model
  simp only [weightedThresholdRoot,
    weightedThresholdDiscriminant_eq_slope_sq model weighted,
    Real.sqrt_sq_eq_abs, abs_of_pos hslope]
  field_simp [hA.ne']
  ring

/-- The canonical weighted threshold varies differentiably with the standing
civic weight at every oriented transversal crossing. -/
theorem differentiableAt_weightedThresholdRoot
    {p : LoopParams} (model : DriftModelAssumptions p) {ρ : ℝ}
    (weighted : WeightedThresholdAssumption p ρ) :
    DifferentiableAt ℝ (weightedThresholdRoot p) ρ := by
  have hr : weighted.βdagger ∈ Icc (0 : ℝ) 1 :=
    ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩
  have hden := thresholdDenominator_pos model hr
  have hnum : weightedThresholdNumerator p ρ weighted.βdagger = 0 := by
    have hgradient := weighted.gradient_zero
    rw [weightedStationaryGradient_eq_numerator_div model ρ hr] at hgradient
    exact (div_eq_zero_iff.mp hgradient).resolve_right hden.ne'
  have hslope :
      0 < 2 * thresholdQuadraticCoefficient p * weighted.βdagger +
        thresholdLinearCoefficient p := by
    have hgradientSlope := weighted.gradientSlope_pos
    rw [weightedStationaryGradientSlope_eq_numeratorSlope_div_at_root
      model ρ hr hnum] at hgradientSlope
    have hnumerator : 0 < thresholdNumeratorSlope p weighted.βdagger :=
      (div_pos_iff_of_pos_right hden).mp hgradientSlope
    rwa [thresholdNumeratorSlope_eq_quadraticSlope] at hnumerator
  have hdiscPos : 0 < weightedThresholdDiscriminant p ρ := by
    rw [weightedThresholdDiscriminant_eq_slope_sq model weighted]
    exact sq_pos_of_pos hslope
  have hdiscDiff :
      DifferentiableAt ℝ (weightedThresholdDiscriminant p) ρ := by
    change DifferentiableAt ℝ (fun x : ℝ ↦
      thresholdLinearCoefficient p ^ 2 -
        4 * thresholdQuadraticCoefficient p *
          (thresholdConstantCoefficient p - x * p.I)) ρ
    fun_prop
  have hsqrtDiff : DifferentiableAt ℝ
      (fun x ↦ Real.sqrt (weightedThresholdDiscriminant p x)) ρ :=
    hdiscDiff.sqrt hdiscPos.ne'
  change DifferentiableAt ℝ (fun x : ℝ ↦
    (-thresholdLinearCoefficient p +
      Real.sqrt (weightedThresholdDiscriminant p x)) /
        (2 * thresholdQuadraticCoefficient p)) ρ
  exact ((differentiableAt_const (c := -thresholdLinearCoefficient p)).add
    hsqrtDiff).div_const (2 * thresholdQuadraticCoefficient p)

/-- A calculus-friendly extension of the corrected barrier area.  At every
valid civic weight it is exactly `weightedBarrierArea`; the decomposition
keeps the moving-root and affine-in-weight contributions explicit. -/
noncomputable def weightedBarrierAreaFamily (p : LoopParams) (ρ : ℝ) : ℝ :=
  (∫ b in (0 : ℝ)..weightedThresholdRoot p ρ,
      weightedBarrierIntegrand p 0 b) +
    ρ * ∫ b in (0 : ℝ)..weightedThresholdRoot p ρ, p.stationaryStock b

/-- The calculus-friendly barrier family agrees with the paper's integral at
every oriented weighted saddle. -/
theorem weightedBarrierAreaFamily_eq
    {p : LoopParams} (model : DriftModelAssumptions p) {ρ : ℝ}
    (weighted : WeightedThresholdAssumption p ρ) :
    weightedBarrierAreaFamily p ρ = weightedBarrierArea weighted := by
  let r := weighted.βdagger
  have hr : r ∈ Icc (0 : ℝ) 1 :=
    ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩
  have hbaseCont : ContinuousOn (weightedBarrierIntegrand p 0) (Icc (0 : ℝ) r) := by
    intro b hb
    have hbUnit : b ∈ Icc (0 : ℝ) 1 := ⟨hb.1, hb.2.trans hr.2⟩
    exact (hasDerivAt_weightedStationaryGradient model 0 hbUnit).neg.continuousAt.continuousWithinAt
  have hstockCont : ContinuousOn p.stationaryStock (Icc (0 : ℝ) r) := by
    intro b hb
    have hbUnit : b ∈ Icc (0 : ℝ) 1 := ⟨hb.1, hb.2.trans hr.2⟩
    exact (hasDerivAt_stationaryStock_zeroGain model hbUnit).continuousAt.continuousWithinAt
  have hbaseInt : IntervalIntegrable (weightedBarrierIntegrand p 0)
      MeasureTheory.volume 0 r :=
    (show ContinuousOn (weightedBarrierIntegrand p 0) [[(0 : ℝ), r]] by
      rw [uIcc_of_le weighted.βdagger_mem.1.le]
      exact hbaseCont).intervalIntegrable
  have hstockInt : IntervalIntegrable p.stationaryStock
      MeasureTheory.volume 0 r :=
    (show ContinuousOn p.stationaryStock [[(0 : ℝ), r]] by
      rw [uIcc_of_le weighted.βdagger_mem.1.le]
      exact hstockCont).intervalIntegrable
  simp only [weightedBarrierAreaFamily, weightedBarrierArea,
    weightedThresholdRoot_eq model weighted]
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add hbaseInt (hstockInt.const_mul ρ)]
  apply intervalIntegral.integral_congr
  intro b _hb
  simp only [weightedBarrierIntegrand, weightedStationaryGradient]
  ring

/-- Paper II, derivative clause of Proposition `prop:qpbounds`: the boundary
term from the moving saddle vanishes, leaving the integrated characteristic
stock as the exact marginal unscaled barrier. -/
theorem hasDerivAt_weightedBarrierAreaFamily
    {p : LoopParams} (model : DriftModelAssumptions p) {ρ : ℝ}
    (weighted : WeightedThresholdAssumption p ρ) :
    HasDerivAt (weightedBarrierAreaFamily p)
      (∫ b in (0 : ℝ)..weighted.βdagger, p.stationaryStock b) ρ := by
  let r := weighted.βdagger
  let r' := deriv (weightedThresholdRoot p) ρ
  have hr : r ∈ Ioo (0 : ℝ) 1 := weighted.βdagger_mem
  have hrClosed : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1.le, hr.2.le⟩
  have hrootDiff := differentiableAt_weightedThresholdRoot model weighted
  have hrootDeriv : HasDerivAt (weightedThresholdRoot p) r' ρ := by
    simpa only [r'] using hrootDiff.hasDerivAt
  have hbaseContClosed :
      ContinuousOn (weightedBarrierIntegrand p 0) (Icc (0 : ℝ) r) := by
    intro b hb
    have hbUnit : b ∈ Icc (0 : ℝ) 1 := ⟨hb.1, hb.2.trans hr.2.le⟩
    exact (hasDerivAt_weightedStationaryGradient model 0 hbUnit).neg.continuousAt.continuousWithinAt
  have hstockContClosed : ContinuousOn p.stationaryStock (Icc (0 : ℝ) r) := by
    intro b hb
    have hbUnit : b ∈ Icc (0 : ℝ) 1 := ⟨hb.1, hb.2.trans hr.2.le⟩
    exact (hasDerivAt_stationaryStock_zeroGain model hbUnit).continuousAt.continuousWithinAt
  have hbaseContOpen :
      ContinuousOn (weightedBarrierIntegrand p 0) (Ioo (0 : ℝ) 1) := by
    intro b hb
    exact (hasDerivAt_weightedStationaryGradient model 0
      ⟨hb.1.le, hb.2.le⟩).neg.continuousAt.continuousWithinAt
  have hstockContOpen : ContinuousOn p.stationaryStock (Ioo (0 : ℝ) 1) := by
    intro b hb
    exact (hasDerivAt_stationaryStock_zeroGain model
      ⟨hb.1.le, hb.2.le⟩).continuousAt.continuousWithinAt
  have hbaseAt : ContinuousAt (weightedBarrierIntegrand p 0) r :=
    (hasDerivAt_weightedStationaryGradient model 0 hrClosed).neg.continuousAt
  have hstockAt : ContinuousAt p.stationaryStock r :=
    (hasDerivAt_stationaryStock_zeroGain model hrClosed).continuousAt
  have hbaseInt : IntervalIntegrable (weightedBarrierIntegrand p 0)
      MeasureTheory.volume 0 r :=
    (show ContinuousOn (weightedBarrierIntegrand p 0) [[(0 : ℝ), r]] by
      rw [uIcc_of_le hr.1.le]
      exact hbaseContClosed).intervalIntegrable
  have hstockInt : IntervalIntegrable p.stationaryStock
      MeasureTheory.volume 0 r :=
    (show ContinuousOn p.stationaryStock [[(0 : ℝ), r]] by
      rw [uIcc_of_le hr.1.le]
      exact hstockContClosed).intervalIntegrable
  have hbaseMeas : StronglyMeasurableAtFilter (weightedBarrierIntegrand p 0)
      (𝓝 r) MeasureTheory.volume :=
    hbaseContOpen.stronglyMeasurableAtFilter isOpen_Ioo r hr
  have hstockMeas : StronglyMeasurableAtFilter p.stationaryStock
      (𝓝 r) MeasureTheory.volume :=
    hstockContOpen.stronglyMeasurableAtFilter isOpen_Ioo r hr
  have hbaseFTC : HasDerivAt
      (fun z ↦ ∫ b in (0 : ℝ)..z, weightedBarrierIntegrand p 0 b)
      (weightedBarrierIntegrand p 0 r) r :=
    intervalIntegral.integral_hasDerivAt_right hbaseInt hbaseMeas hbaseAt
  have hstockFTC : HasDerivAt
      (fun z ↦ ∫ b in (0 : ℝ)..z, p.stationaryStock b)
      (p.stationaryStock r) r :=
    intervalIntegral.integral_hasDerivAt_right hstockInt hstockMeas hstockAt
  have hrootEq : weightedThresholdRoot p ρ = r :=
    weightedThresholdRoot_eq model weighted
  have hbaseFTCroot : HasDerivAt
      (fun z ↦ ∫ b in (0 : ℝ)..z, weightedBarrierIntegrand p 0 b)
      (weightedBarrierIntegrand p 0 r) (weightedThresholdRoot p ρ) := by
    simpa only [hrootEq] using hbaseFTC
  have hstockFTCroot : HasDerivAt
      (fun z ↦ ∫ b in (0 : ℝ)..z, p.stationaryStock b)
      (p.stationaryStock r) (weightedThresholdRoot p ρ) := by
    simpa only [hrootEq] using hstockFTC
  have hbaseComp := hbaseFTCroot.comp ρ hrootDeriv
  have hstockComp := hstockFTCroot.comp ρ hrootDeriv
  have hbaseComp' : HasDerivAt
      (fun x ↦ ∫ b in (0 : ℝ)..weightedThresholdRoot p x,
        weightedBarrierIntegrand p 0 b)
      (weightedBarrierIntegrand p 0 r * r') ρ := by
    apply hbaseComp.congr_of_eventuallyEq
    filter_upwards with x
    rfl
  have hstockComp' : HasDerivAt
      (fun x ↦ ∫ b in (0 : ℝ)..weightedThresholdRoot p x,
        p.stationaryStock b)
      (p.stationaryStock r * r') ρ := by
    apply hstockComp.congr_of_eventuallyEq
    filter_upwards with x
    rfl
  have hproduct : HasDerivAt
      (fun x ↦ x * ∫ b in (0 : ℝ)..weightedThresholdRoot p x,
        p.stationaryStock b)
      (1 * (∫ b in (0 : ℝ)..r, p.stationaryStock b) +
        ρ * (p.stationaryStock r * r')) ρ := by
    have hraw := (hasDerivAt_id ρ).mul hstockComp'
    have hfunction : HasDerivAt
        (fun x ↦ x * ∫ b in (0 : ℝ)..weightedThresholdRoot p x,
          p.stationaryStock b)
        (1 * (∫ b in (0 : ℝ)..weightedThresholdRoot p ρ,
            p.stationaryStock b) +
          ρ * (p.stationaryStock r * r')) ρ := by
      apply hraw.congr_of_eventuallyEq
      filter_upwards with x
      rfl
    apply hfunction.congr_deriv
    rw [hrootEq]
  have hsum : HasDerivAt
      (fun x ↦
        (∫ b in (0 : ℝ)..weightedThresholdRoot p x,
          weightedBarrierIntegrand p 0 b) +
        x * ∫ b in (0 : ℝ)..weightedThresholdRoot p x,
          p.stationaryStock b)
      (weightedBarrierIntegrand p 0 r * r' +
        (1 * (∫ b in (0 : ℝ)..r, p.stationaryStock b) +
          ρ * (p.stationaryStock r * r'))) ρ :=
    hbaseComp'.add hproduct
  have hboundary :
      weightedBarrierIntegrand p 0 r + ρ * p.stationaryStock r = 0 := by
    have hrewrite : weightedBarrierIntegrand p ρ r =
        weightedBarrierIntegrand p 0 r + ρ * p.stationaryStock r := by
      simp only [weightedBarrierIntegrand, weightedStationaryGradient]
      ring
    rw [← hrewrite]
    change -weightedStationaryGradient p ρ weighted.βdagger = 0
    rw [weighted.gradient_zero]
    norm_num
  apply hsum.congr_deriv
  linear_combination r' * hboundary

/-- The `2/α`-scaled barrier family used in the displayed comparative static. -/
noncomputable def scaledWeightedBarrierFamily (p : LoopParams) (ρ : ℝ) : ℝ :=
  (2 / p.α) * weightedBarrierAreaFamily p ρ

/-- Paper II, displayed marginal-barrier identity in Proposition
`prop:qpbounds`. -/
theorem hasDerivAt_scaledWeightedBarrierFamily
    {p : LoopParams} (model : DriftModelAssumptions p) {ρ : ℝ}
    (weighted : WeightedThresholdAssumption p ρ) :
    HasDerivAt (scaledWeightedBarrierFamily p)
      ((2 / p.α) *
        ∫ b in (0 : ℝ)..weighted.βdagger, p.stationaryStock b) ρ := by
  change HasDerivAt
    (fun x ↦ (2 / p.α) * weightedBarrierAreaFamily p x)
    ((2 / p.α) *
      ∫ b in (0 : ℝ)..weighted.βdagger, p.stationaryStock b) ρ
  exact (hasDerivAt_weightedBarrierAreaFamily model weighted).const_mul (2 / p.α)

/-- Raising the civic weight adds exactly `(ρ'-ρ)D*` to the barrier
integrand. -/
theorem weightedBarrierIntegrand_weight_difference
    (p : LoopParams) (ρ ρ' β : ℝ) :
    weightedBarrierIntegrand p ρ' β =
      weightedBarrierIntegrand p ρ β +
        (ρ' - ρ) * p.stationaryStock β := by
  simp only [weightedBarrierIntegrand, weightedStationaryGradient]
  ring

/-- The unique weighted saddle moves strictly right when the standing civic
weight rises. -/
theorem weightedThreshold_strictMono_in_weight
    {p : LoopParams} (model : DriftModelAssumptions p)
    {ρ ρ' : ℝ} (hρρ' : ρ < ρ')
    (weighted : WeightedThresholdAssumption p ρ)
    (weighted' : WeightedThresholdAssumption p ρ') :
    weighted.βdagger < weighted'.βdagger := by
  have hrootUnit : weighted.βdagger ∈ Icc (0 : ℝ) 1 :=
    ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩
  have hstockPos : 0 < p.stationaryStock weighted.βdagger :=
    model.I_pos.trans_le (stationaryStock_mem_stockInterval model hrootUnit).1
  have hnegative :
      weightedStationaryGradient p ρ' weighted.βdagger < 0 := by
    have hid : weightedStationaryGradient p ρ' weighted.βdagger =
        weightedStationaryGradient p ρ weighted.βdagger -
          (ρ' - ρ) * p.stationaryStock weighted.βdagger := by
      simp only [weightedStationaryGradient]
      ring
    rw [hid, weighted.gradient_zero]
    have hprod := mul_pos (sub_pos.mpr hρρ') hstockPos
    linarith
  by_contra hnot
  have hle : weighted'.βdagger ≤ weighted.βdagger := le_of_not_gt hnot
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hpositive := weighted'.gradient_pos_after weighted.βdagger
      weighted.βdagger_mem hlt
    linarith
  · rw [← heq, weighted'.gradient_zero] at hnegative
    exact (lt_irrefl 0 hnegative).elim

/-- The corrected barrier integral is strictly increasing in the standing
civic weight.  This proof uses only the oriented root catalogue and positivity
of the characteristic stock; it does not differentiate a chosen root. -/
theorem weightedBarrierArea_strictMono
    {p : LoopParams} (model : DriftModelAssumptions p)
    {ρ ρ' : ℝ} (hρρ' : ρ < ρ')
    (weighted : WeightedThresholdAssumption p ρ)
    (weighted' : WeightedThresholdAssumption p ρ') :
    weightedBarrierArea weighted < weightedBarrierArea weighted' := by
  let r := weighted.βdagger
  let r' := weighted'.βdagger
  let f := weightedBarrierIntegrand p ρ
  let g := weightedBarrierIntegrand p ρ'
  have hrr' : r < r' :=
    weightedThreshold_strictMono_in_weight model hρρ' weighted weighted'
  have hrpos : 0 < r := weighted.βdagger_mem.1
  have hr'le : r' ≤ 1 := weighted'.βdagger_mem.2.le
  have hfcont : ContinuousOn f (Icc (0 : ℝ) r) := by
    simpa only [f, r] using continuousOn_weightedBarrierIntegrand model ρ weighted
  have hgcontFull : ContinuousOn g (Icc (0 : ℝ) r') := by
    simpa only [g, r'] using
      continuousOn_weightedBarrierIntegrand model ρ' weighted'
  have hsubset : Icc (0 : ℝ) r ⊆ Icc (0 : ℝ) r' := by
    intro x hx
    exact ⟨hx.1, hx.2.trans hrr'.le⟩
  have hgcont : ContinuousOn g (Icc (0 : ℝ) r) :=
    hgcontFull.mono hsubset
  have hpointStrict : ∀ x ∈ Icc (0 : ℝ) r, f x < g x := by
    intro x hx
    have hxUnit : x ∈ Icc (0 : ℝ) 1 :=
      ⟨hx.1, hx.2.trans (hrr'.le.trans hr'le)⟩
    have hstockPos : 0 < p.stationaryStock x :=
      model.I_pos.trans_le (stationaryStock_mem_stockInterval model hxUnit).1
    dsimp only [f, g]
    calc
      weightedBarrierIntegrand p ρ x <
          weightedBarrierIntegrand p ρ x +
            (ρ' - ρ) * p.stationaryStock x :=
        lt_add_of_pos_right _ (mul_pos (sub_pos.mpr hρρ') hstockPos)
      _ = weightedBarrierIntegrand p ρ' x :=
        (weightedBarrierIntegrand_weight_difference p ρ ρ' x).symm
  have hfirst : (∫ x in (0 : ℝ)..r, f x) < ∫ x in (0 : ℝ)..r, g x := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      hrpos hfcont hgcont
    · intro x hx
      exact (hpointStrict x ⟨hx.1.le, hx.2⟩).le
    · exact ⟨0, ⟨le_rfl, hrpos.le⟩, hpointStrict 0 ⟨le_rfl, hrpos.le⟩⟩
  have hextraNonneg : 0 ≤ ∫ x in r..r', g x := by
    apply intervalIntegral.integral_nonneg hrr'.le
    intro x hx
    by_cases hxroot : x = r'
    · subst x
      simp only [g, r', weightedBarrierIntegrand,
        weighted'.gradient_zero, neg_zero]
      norm_num
    · have hxlt : x < r' := lt_of_le_of_ne hx.2 hxroot
      have hxSegment : x ∈ Icc (0 : ℝ) weighted'.βdagger := by
        exact ⟨hrpos.le.trans hx.1, by simpa only [r'] using hx.2⟩
      exact (weighted'.barrier_pos_before hxSegment (by simpa only [r'] using hxlt)).le
  have hleftInt : IntervalIntegrable g MeasureTheory.volume 0 r :=
    (show ContinuousOn g [[(0 : ℝ), r]] by
      rw [uIcc_of_le hrpos.le]
      exact hgcont).intervalIntegrable
  have hextraSubset : [[r, r']] ⊆ Icc (0 : ℝ) r' := by
    rw [uIcc_of_le hrr'.le]
    intro x hx
    exact ⟨hrpos.le.trans hx.1, hx.2⟩
  have hextraInt : IntervalIntegrable g MeasureTheory.volume r r' :=
    (hgcontFull.mono hextraSubset).intervalIntegrable
  have hadd :
      (∫ x in (0 : ℝ)..r, g x) + (∫ x in r..r', g x) =
        ∫ x in (0 : ℝ)..r', g x :=
    intervalIntegral.integral_add_adjacent_intervals hleftInt hextraInt
  change (∫ x in (0 : ℝ)..r, f x) < ∫ x in (0 : ℝ)..r', g x
  exact hfirst.trans_le ((le_add_of_nonneg_right hextraNonneg).trans_eq hadd)

#print axioms controlAction_nonneg
#print axioms runningMax_zero
#print axioms runningMax_succ
#print axioms le_runningMax
#print axioms monotone_runningMax
#print axioms runningMax_le_of_forall_le
#print axioms le_runningMax_of_le_zero
#print axioms IsControlledCivicWeightedPath.policy_mem
#print axioms IsControlledCivicWeightedPath.runningMax_mem
#print axioms policy_le_runningMax
#print axioms IsControlledCivicWeightedPath.mem_absorbingBox
#print axioms IsControlledCivicWeightedPath.calibratedPoint_le
#print axioms IsControlledCivicWeightedPath.stock_le_stationary_runningMax
#print axioms civicWeightedGradient_stationary_eq_weightedStationaryGradient
#print axioms civicWeighted_characteristic_step_le_of_below
#print axioms civicWeighted_characteristic_below_tendsto_calibrated
#print axioms calibratedPoint_mem_civicWeightedCalibratedBasin
#print axioms mem_civicWeightedCalibratedBasin_of_le_characteristic_below
#print axioms IsControlledCivicWeightedPath.mem_calibratedBasin_of_runningMax_lt
#print axioms IsControlledCivicWeightedPath.exit_forces_runningMax_ge
#print axioms monotone_cappedPolicyRunningMax
#print axioms IsControlledCivicWeightedPath.cappedRunningMax_zero
#print axioms cappedRunningMax_eq_target
#print axioms cappedRunningMax_increment_nonneg
#print axioms cappedRunningMax_advance_structure
#print axioms clipUnit_le_input_of_pos
#print axioms IsControlledCivicWeightedPath.gradient_le_runningMax
#print axioms two_alpha_c_sq_stationaryStock_le_one
#print axioms IsControlledCivicWeightedPath.control_ge_barrier_add_advance
#print axioms IsControlledCivicWeightedPath.advance_barrier_le_half_control_sq
#print axioms IsControlledCivicWeightedPath.barrier_increment_le_half_control_sq
#print axioms IsControlledCivicWeightedPath.sum_barrier_increments_le_action
#print axioms continuousOn_weightedBarrierIntegrand
#print axioms IsControlledCivicWeightedPath.cappedRunningMax_mem
#print axioms integral_le_left_rectangle_add_lipschitz
#print axioms WeightedThresholdAssumption.barrier_pos_before
#print axioms IsControlledCivicWeightedPath.capped_increment_sq_le_control_sq
#print axioms IsControlledCivicWeightedPath.sum_capped_increment_sq_le_action
#print axioms IsControlledCivicWeightedPath.barrier_integral_le_partition
#print axioms IsControlledCivicWeightedPath.action_lower_bound
#print axioms forcedCapturedStockPath_succ
#print axioms forcedCapturedPath_isControlled
#print axioms forcedCapturedPath_tendsto
#print axioms quasipotentialActionSet_nonempty
#print axioms civicQuasipotential_lower_bound
#print axioms civicQuasipotential_le_controlAction
#print axioms quasipotential_strictMono_of_bracket_separation
#print axioms doublingControl_strictly_advances_of_gradient_neg
#print axioms marginClimbPath_zero
#print axioms marginClimbPath_succ
#print axioms marginClimbPath_isControlled
#print axioms marginClimb_net_gradient_ge
#print axioms monotone_marginClimbPolicy
#print axioms runningMax_eq_of_monotone
#print axioms marginClimbPath_eventually_crosses
#print axioms lt_clipUnit_of_mem_Ico_of_lt
#print axioms marginClimbPath_increment_gt_margin_of_not_crossed
#print axioms marginClimbPath_crosses_by_natCeil
#print axioms cancellingHoldStockPath_zero
#print axioms cancellingHoldPath_zero
#print axioms cancellingHoldStockPath_succ
#print axioms cancellingHoldPath_step_of_gradient_nonpos
#print axioms cancellingHoldStockPath_tendsto
#print axioms WeightedThresholdAssumption.gradient_pos_of_mem_Ioc
#print axioms cancellingHoldGradient_tendsto
#print axioms cancellingHoldGradient_eventually_positive
#print axioms firstPositiveIndex_spec
#print axioms firstPositiveIndex_nonpos_before
#print axioms cancellingHoldStop_gradient_pos
#print axioms cancellingHoldStop_gradient_nonpos_before
#print axioms cancellingHoldPath_step_before_stop
#print axioms cancellingHoldStop_dominates_characteristic
#print axioms cancellingHoldPath_mem_absorbingBox
#print axioms civicWeightedOrbit_tendsto_captured_of_dominates_characteristic
#print axioms marginClimbPath_stock_le_stationaryStock
#print axioms twoPhaseUpperPath_zero
#print axioms twoPhaseUpperPath_succ
#print axioms twoPhaseUpperPath_isControlled
#print axioms twoPhaseUpperPath_eq_marginClimb_of_le
#print axioms twoPhaseUpperPath_eq_cancellingHold
#print axioms twoPhaseUpperPath_at_totalStop
#print axioms twoPhaseUpperPath_totalStop_mem_absorbingBox
#print axioms twoPhaseUpperPath_totalStop_dominates_characteristic
#print axioms twoPhaseUpperPath_totalStop_tendsto_captured
#print axioms twoPhaseUpperPath_exits_calibratedBasin
#print axioms upwardStrategyCostEpsilon_mem_quasipotentialActionSet
#print axioms civicQuasipotential_le_upwardStrategyCostEpsilon
#print axioms civicQuasipotential_le_upwardStrategyCost
#print axioms exists_lipschitzConstantOn_weightedBarrierIntegrand
#print axioms left_rectangle_le_integral_add_lipschitz
#print axioms leftRiemannSum_le_integral_add_lipschitz
#print axioms upperStrategyClimbStop_crosses
#print axioms upperStrategyClimbStop_le_natCeil
#print axioms withOperatorRate_eta
#print axioms withOperatorRate_lambda₀
#print axioms withOperatorRate_I
#print axioms withOperatorRate_v
#print axioms withOperatorRate_c
#print axioms withOperatorRate_alpha
#print axioms withOperatorRate_g
#print axioms withOperatorRate_s
#print axioms withOperatorRate_sSlope
#print axioms withOperatorRate_gradU
#print axioms withOperatorRate_stationaryStock
#print axioms withOperatorRate_G
#print axioms withOperatorRate_GSlope
#print axioms withOperatorRate_civicWeightedGradient
#print axioms withOperatorRate_weightedStationaryGradient
#print axioms withOperatorRate_weightedStationaryGradientSlope
#print axioms withOperatorRate_weightedBarrierIntegrand
#print axioms withOperatorRate_cureThreshold
#print axioms DriftModelAssumptions.withOperatorRate
#print axioms SmallStepAssumption.withOperatorRate
#print axioms WeightedThresholdAssumption.withOperatorRate_βdagger
#print axioms driftStationaryStockLipschitzBound_withOperatorRate
#print axioms driftStationaryStockLipschitzBound_pos
#print axioms stationaryStock_sub_le_driftLipschitz
#print axioms WeightedThresholdAssumption.gradient_nonpos_before
#print axioms marginClimbPath_le_saddle_before_stop
#print axioms marginClimb_before_stop_step_data
#print axioms marginClimb_before_stop_increment_bounds
#print axioms marginClimb_stationaryStockLag_succ
#print axioms marginClimb_stationaryStockLag_le
#print axioms weightedBarrierArea_withOperatorRate
#print axioms neg_civicWeightedGradient_eq_barrier_add_lag
#print axioms weighted_stock_coefficient_le_two_c
#print axioms stationaryStock_sub_cancellingHoldStockPath
#print axioms sum_sq_geometric_le_inv_gap
#print axioms cancellingHoldControl_le_geometric
#print axioms cancellingHoldAction_le
#print axioms upwardStrategyHoldAction_le
#print axioms WeightedThresholdAssumption.barrier_nonneg_before
#print axioms WeightedThresholdAssumption.barrier_le_v
#print axioms marginClimb_action_summand_eq
#print axioms marginClimb_barrier_work_le
#print axioms marginClimb_negative_gradient_work_le
#print axioms upwardStrategyClimbAction_eq
#print axioms upwardStrategyClimbAction_le
#print axioms twoPhaseUpperControl_eq_marginClimb_before
#print axioms twoPhaseUpperControl_eq_cancellingHold
#print axioms upwardStrategyCostEpsilon_eq_climb_add_hold
#print axioms upwardStrategyCost_le_upwardStrategyCostEpsilon
#print axioms upwardStrategyCostEpsilon_le
#print axioms upperStrategyClimbStop_mul_margin_le
#print axioms smallRateStrategyRemainderBound_nonneg
#print axioms upwardStrategyCostAtRate_lower_bound
#print axioms upwardStrategyCostAtRate_upper_bound
#print axioms weightedBarrierArea_pos
#print axioms upwardStrategyCostAtRate_relative_isBigO
#print axioms weightedThresholdDiscriminant_eq_slope_sq
#print axioms weightedThresholdRoot_eq
#print axioms differentiableAt_weightedThresholdRoot
#print axioms weightedBarrierAreaFamily_eq
#print axioms hasDerivAt_weightedBarrierAreaFamily
#print axioms hasDerivAt_scaledWeightedBarrierFamily
#print axioms weightedBarrierIntegrand_weight_difference
#print axioms weightedThreshold_strictMono_in_weight
#print axioms weightedBarrierArea_strictMono
#print axioms hasDerivAt_weightedBarrierClosedPrimitive
#print axioms weightedBarrierArea_closedForm

end

end CivicAlignment.PaperII
