/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.LowActionRecurrence
import CivicAlignment.PaperII.BistabilityTopology
import CivicAlignment.PaperII.Quasipotential

/-!
# Paper II: basin recurrence from compact attraction

This file applies the general low-action recurrence theorem directly to the
controlled civic-weighted map.  It does not use the crossing, funnel, block,
or Arrhenius developments.

Every compact subset of the calibrated basin has a common finite horizon and
a positive action charge: a controlled path which stays outside a prescribed
neighborhood of the calibrated point throughout that horizon must pay at
least that charge.  Thus long basin excursions can be divided into
fixed-dimensional blocks without making a growing-horizon Big-O assertion.
-/

namespace CivicAlignment.PaperII

open Filter Function Set Topology

noncomputable section

/-- The controlled civic-weighted step is jointly continuous in its scalar
control and state variables. -/
theorem continuous_uncurry_controlledCivicWeightedStep
    (p : LoopParams) (rho : ℝ) :
    Continuous (Function.uncurry (controlledCivicWeightedStep p rho)) := by
  unfold controlledCivicWeightedStep civicWeightedGradient
    LoopParams.gradU LoopParams.stockStep LoopParams.s LoopParams.clipUnit
  fun_prop

/-- Zero control is exactly the deterministic civic-weighted map. -/
theorem controlledCivicWeightedStep_zero_eq_unforced
    (p : LoopParams) (rho : ℝ) :
    controlledCivicWeightedStep p rho 0 = civicWeightedLoopMap p rho := by
  funext x
  simp only [controlledCivicWeightedStep, civicWeightedLoopMap,
    civicWeightedDeferenceStep, civicWeightedInput, add_zero]

/-- The controlled step restricted to the invariant box. -/
def controlledCivicWeightedStepInBox
    {p : LoopParams} (model : DriftModelAssumptions p) (rho u : ℝ)
    (x : LoopBox p) : LoopBox p :=
  ⟨controlledCivicWeightedStep p rho u x.1, by
    constructor
    · exact LoopParams.clipUnit_mem _
    · have hnext := civicWeightedInvariantBox model rho x.2
      simpa only [controlledCivicWeightedStep, civicWeightedLoopMap,
        Prod.snd] using hnext.2⟩

/-- The restricted controlled step remains jointly continuous. -/
theorem continuous_uncurry_controlledCivicWeightedStepInBox
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ) :
    Continuous
      (Function.uncurry (controlledCivicWeightedStepInBox model rho)) := by
  have hpair : Continuous (fun z : ℝ × LoopBox p ↦
      ((z.1, z.2.1) : ℝ × LoopState)) := by
    fun_prop
  exact ((continuous_uncurry_controlledCivicWeightedStep p rho).comp
    hpair).subtype_mk _

/-- The calibrated point as a state of the invariant box. -/
def calibratedPointInBox
    (p : LoopParams) (model : DriftModelAssumptions p) : LoopBox p :=
  ⟨calibratedPoint p, ⟨by simp [calibratedPoint],
    stationaryStock_mem_stockInterval model (by norm_num)⟩⟩

/-- The calibrated basin in the relative topology of the invariant box,
defined here without the stochastic Arrhenius development. -/
def civicWeightedCalibratedBasinInBox (p : LoopParams) (rho : ℝ) :
    Set (LoopBox p) :=
  {x | Tendsto (civicWeightedOrbit p rho x.1) atTop
    (nhds (calibratedPoint p))}

@[simp]
theorem mem_civicWeightedCalibratedBasinInBox_iff
    {p : LoopParams} {rho : ℝ} {x : LoopBox p} :
    x ∈ civicWeightedCalibratedBasinInBox p rho ↔
      x.1 ∈ civicWeightedCalibratedBasin p rho :=
  Iff.rfl

/-- Restricting a weighted iterate to the invariant box preserves
continuity. -/
theorem continuous_civicWeightedIterateOnBox
    (p : LoopParams) (rho : ℝ) (n : ℕ) :
    Continuous (fun x : LoopBox p ↦ civicWeightedOrbit p rho x.1 n) := by
  exact ((continuous_civicWeightedLoopMap p rho).iterate n).comp
    continuous_subtype_val

/-- A weighted orbit restarted at time `n` is its `n`-shifted tail. -/
theorem civicWeightedOrbit_from_iterate (p : LoopParams) (rho : ℝ)
    (x₀ : LoopState) (n k : ℕ) :
    civicWeightedOrbit p rho (civicWeightedOrbit p rho x₀ n) k =
      civicWeightedOrbit p rho x₀ (k + n) := by
  simp only [civicWeightedOrbit, Function.iterate_add_apply]

/-- Deleting a finite prefix does not change convergence of a weighted
orbit. -/
theorem civicWeightedOrbit_tendsto_iff_tail (p : LoopParams) (rho : ℝ)
    (x₀ q : LoopState) (n : ℕ) :
    Tendsto (civicWeightedOrbit p rho
        (civicWeightedOrbit p rho x₀ n)) atTop (nhds q) ↔
      Tendsto (civicWeightedOrbit p rho x₀) atTop (nhds q) := by
  have hfun : civicWeightedOrbit p rho (civicWeightedOrbit p rho x₀ n) =
      fun k ↦ civicWeightedOrbit p rho x₀ (k + n) := by
    funext k
    exact civicWeightedOrbit_from_iterate p rho x₀ n k
  rw [hfun]
  exact tendsto_add_atTop_iff_nat n

/-- The calibrated basin is open in the relative topology of the invariant
box. -/
theorem civicWeightedCalibratedBasinInBox_isOpen
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) :
    IsOpen (civicWeightedCalibratedBasinInBox p rho) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  let N := calibratedPreventionNeighborhood p threshold
  have hN : N ∈ nhds (calibratedPoint p) :=
    calibratedPreventionNeighborhood_mem_nhds model threshold
  obtain ⟨U, hUN, hUopen, hcalibratedU⟩ := mem_nhds_iff.mp hN
  have hevent : ∀ᶠ n in atTop, civicWeightedOrbit p rho x.1 n ∈ U :=
    hx (hUopen.mem_nhds hcalibratedU)
  obtain ⟨n, hn⟩ := hevent.exists
  let W : Set (LoopBox p) :=
    {y | civicWeightedOrbit p rho y.1 n ∈ U}
  have hWopen : IsOpen W := by
    exact hUopen.preimage (continuous_civicWeightedIterateOnBox p rho n)
  have hxW : x ∈ W := hn
  refine mem_of_superset (hWopen.mem_nhds hxW) ?_
  intro y hy
  let tail := civicWeightedOrbit p rho
    (civicWeightedOrbit p rho y.1 n)
  have htailTrajectory : IsCivicWeightedScheduleTrajectory p
      (fun _ ↦ rho) tail := by
    intro k
    exact civicWeightedOrbit_isTrajectory p rho
      (civicWeightedOrbit p rho y.1 n) k
  have htailBox : tail 0 ∈ absorbingBox p := by
    exact civicWeightedTrajectory_mem_absorbingBox model
      (civicWeightedOrbit_isTrajectory p rho y.1) y.2 n
  have htail : Tendsto tail atTop (nhds (calibratedPoint p)) :=
    civicWeighted_prevention_uniform_attraction model ss threshold
      (fun _ ↦ hrho) htailTrajectory htailBox (hUN hy)
  exact (civicWeightedOrbit_tendsto_iff_tail p rho y.1
    (calibratedPoint p) n).mp htail

/-- Order of two starts in the invariant box propagates along their weighted
orbits whenever the weighted map is cooperative. -/
theorem civicWeightedOrbit_mono_on_box
    {p : LoopParams} {rho : ℝ}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    {x y : LoopBox p} (hxy : x ≤ y) (n : ℕ) :
    civicWeightedOrbit p rho x.1 n ≤
      civicWeightedOrbit p rho y.1 n := by
  have hxmem : ∀ k, civicWeightedOrbit p rho x.1 k ∈ absorbingBox p :=
    civicWeightedTrajectory_mem_absorbingBox model
      (civicWeightedOrbit_isTrajectory p rho x.1) x.2
  have hymem : ∀ k, civicWeightedOrbit p rho y.1 k ∈ absorbingBox p :=
    civicWeightedTrajectory_mem_absorbingBox model
      (civicWeightedOrbit_isTrajectory p rho y.1) y.2
  induction n with
  | zero =>
      simpa only [civicWeightedOrbit, Function.iterate_zero_apply] using
        (show x.1 ≤ y.1 from hxy)
  | succ n ih =>
      simpa only [civicWeightedOrbit, Function.iterate_succ_apply'] using
        civicWeightedLoopMap_monotoneOn_box model ss hcoop
          (hxmem n) (hymem n) ih

/-- In the cooperative regime the calibrated basin is a lower set in the
product order on the invariant box. -/
theorem civicWeightedCalibratedBasinInBox_lowerSet
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    {x y : LoopBox p} (hyx : y ≤ x)
    (hx : x ∈ civicWeightedCalibratedBasinInBox p rho) :
    y ∈ civicWeightedCalibratedBasinInBox p rho := by
  have hevent : ∀ᶠ n in atTop,
      civicWeightedOrbit p rho x.1 n ∈
        calibratedPreventionNeighborhood p threshold :=
    hx (calibratedPreventionNeighborhood_mem_nhds model threshold)
  obtain ⟨n, hxn⟩ := hevent.exists
  have hynOrder : civicWeightedOrbit p rho y.1 n ≤
      civicWeightedOrbit p rho x.1 n :=
    civicWeightedOrbit_mono_on_box model ss hcoop hyx n
  have hyn : civicWeightedOrbit p rho y.1 n ∈
      calibratedPreventionNeighborhood p threshold :=
    hynOrder.trans hxn
  let tail := civicWeightedOrbit p rho
    (civicWeightedOrbit p rho y.1 n)
  have htailTrajectory : IsCivicWeightedScheduleTrajectory p
      (fun _ ↦ rho) tail := by
    intro k
    exact civicWeightedOrbit_isTrajectory p rho
      (civicWeightedOrbit p rho y.1 n) k
  have htailBox : tail 0 ∈ absorbingBox p := by
    exact civicWeightedTrajectory_mem_absorbingBox model
      (civicWeightedOrbit_isTrajectory p rho y.1) y.2 n
  have htailNear : tail 0 ∈
      calibratedPreventionNeighborhood p threshold := by
    simpa only [tail, civicWeightedOrbit,
      Function.iterate_zero_apply] using hyn
  have htail : Tendsto tail atTop (nhds (calibratedPoint p)) :=
    civicWeighted_prevention_uniform_attraction model ss threshold
      (fun _ ↦ hrho) htailTrajectory htailBox htailNear
  exact (civicWeightedOrbit_tendsto_iff_tail p rho y.1
    (calibratedPoint p) n).mp htail

/-- Adding the same control to two ordered states preserves their order in
the cooperative regime. -/
theorem controlledCivicWeightedStep_monotoneOn_box_recurrence
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (hcoop : rho ≤ 2 * p.c * (1 - p.c)) (u : ℝ) :
    MonotoneOn (controlledCivicWeightedStep p rho u) (absorbingBox p) := by
  intro x hx y hy hxy
  have hpolicyFirst := civicWeightedInput_mono_policy (ρ := rho) model ss
    hx.1 hy.1 hxy.1 hx.2
  have hpolicySecond := civicWeightedInput_mono_stock model hcoop
    hy.1 hxy.2
  have hweightedInput :
      civicWeightedInput p rho x.1 x.2 ≤
        civicWeightedInput p rho y.1 y.2 :=
    hpolicyFirst.trans hpolicySecond
  have hcontrolledInput :
      x.1 + p.α * (civicWeightedGradient p rho x.1 x.2 + u) ≤
        y.1 + p.α * (civicWeightedGradient p rho y.1 y.2 + u) := by
    simp only [civicWeightedInput] at hweightedInput
    linarith
  have hpolicy := LoopParams.monotone_clipUnit hcontrolledInput
  have hstock :=
    (civicWeightedLoopMap_monotoneOn_box model ss hcoop hx hy hxy).2
  exact ⟨by
      simpa only [controlledCivicWeightedStep] using hpolicy,
    by simpa only [controlledCivicWeightedStep, civicWeightedLoopMap] using hstock⟩

/-- At a fixed state, increasing the scalar control increases the controlled
state in product order. -/
theorem controlledCivicWeightedStep_mono_control
    {p : LoopParams} (model : DriftModelAssumptions p) {rho u v : ℝ}
    (huv : u ≤ v) (x : LoopState) :
    controlledCivicWeightedStep p rho u x ≤
      controlledCivicWeightedStep p rho v x := by
  constructor
  · apply LoopParams.monotone_clipUnit
    have hinner : civicWeightedGradient p rho x.1 x.2 + u ≤
        civicWeightedGradient p rho x.1 x.2 + v :=
      by linarith
    have hmul := mul_le_mul_of_nonneg_left hinner model.α_pos.le
    linarith
  · exact le_rfl

/-- The restricted controlled step is jointly monotone in state and control
in the cooperative regime. -/
theorem controlledCivicWeightedStepInBox_mono
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho u v : ℝ}
    (hcoop : rho ≤ 2 * p.c * (1 - p.c)) (huv : u ≤ v)
    {x y : LoopBox p} (hxy : x ≤ y) :
    controlledCivicWeightedStepInBox model rho u x ≤
      controlledCivicWeightedStepInBox model rho v y := by
  exact (controlledCivicWeightedStep_monotoneOn_box_recurrence
      model ss hcoop u x.2 y.2 hxy).trans
    (controlledCivicWeightedStep_mono_control model huv y.1)

/-- Pointwise larger finite controls produce a componentwise larger state at
every time through their common horizon. -/
theorem finiteControlOrbitInBox_mono_controls
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    {T : ℕ} {u v : Fin T → ℝ} (huv : ∀ i, u i ≤ v i)
    (x₀ : LoopBox p) {n : ℕ} (hn : n ≤ T) :
    finiteControlOrbit (controlledCivicWeightedStepInBox model rho) x₀ u n ≤
      finiteControlOrbit (controlledCivicWeightedStepInBox model rho) x₀ v n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      have hnlt : n < T := by omega
      simp only [finiteControlOrbit]
      apply controlledCivicWeightedStepInBox_mono model ss hcoop
      · simp only [finiteControlValue, hnlt, dite_true]
        exact huv ⟨n, hnlt⟩
      · exact ih (by omega)

/-- Ordered initial states and pointwise ordered controls produce ordered
states throughout their common finite horizon. -/
theorem finiteControlOrbitInBox_mono
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    {T : ℕ} {u v : Fin T → ℝ} (huv : ∀ i, u i ≤ v i)
    {x₀ y₀ : LoopBox p} (hxy : x₀ ≤ y₀) {n : ℕ} (hn : n ≤ T) :
    finiteControlOrbit (controlledCivicWeightedStepInBox model rho) x₀ u n ≤
      finiteControlOrbit (controlledCivicWeightedStepInBox model rho) y₀ v n := by
  induction n with
  | zero => exact hxy
  | succ n ih =>
      have hnlt : n < T := by omega
      simp only [finiteControlOrbit]
      apply controlledCivicWeightedStepInBox_mono model ss hcoop
      · simp only [finiteControlValue, hnlt, dite_true]
        exact huv ⟨n, hnlt⟩
      · exact ih (by omega)

/-- A terminal basin exit is preserved by every pointwise larger finite
control vector.  This supplies a one-sided robust control box even when the
nominal endpoint lies exactly on the basin boundary. -/
theorem finiteControlOrbitInBox_not_mem_basin_of_mono_controls
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    {T : ℕ} {u v : Fin T → ℝ} (huv : ∀ i, u i ≤ v i)
    (x₀ : LoopBox p)
    (hexit : finiteControlOrbit
        (controlledCivicWeightedStepInBox model rho) x₀ u T ∉
      civicWeightedCalibratedBasinInBox p rho) :
    finiteControlOrbit
        (controlledCivicWeightedStepInBox model rho) x₀ v T ∉
      civicWeightedCalibratedBasinInBox p rho := by
  have horder := finiteControlOrbitInBox_mono_controls
    model ss hcoop huv x₀ (n := T) le_rfl
  intro hvBasin
  exact hexit (civicWeightedCalibratedBasinInBox_lowerSet
    model ss threshold hrho hcoop horder hvBasin)

/-- A terminal exit from the calibrated corner is inherited by every larger
initial state and every pointwise larger finite control.  Thus one nominal
exit control is a uniform restart certificate for every state reachable from
the calibrated corner. -/
theorem finiteControlOrbitInBox_not_mem_basin_of_ordered_start
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    {T : ℕ} {u v : Fin T → ℝ} (huv : ∀ i, u i ≤ v i)
    {y₀ : LoopBox p} (hcalibrated : calibratedPointInBox p model ≤ y₀)
    (hexit : finiteControlOrbit
        (controlledCivicWeightedStepInBox model rho)
        (calibratedPointInBox p model) u T ∉
      civicWeightedCalibratedBasinInBox p rho) :
    finiteControlOrbit
        (controlledCivicWeightedStepInBox model rho) y₀ v T ∉
      civicWeightedCalibratedBasinInBox p rho := by
  have horder := finiteControlOrbitInBox_mono model ss hcoop huv
    hcalibrated (n := T) le_rfl
  intro hvBasin
  exact hexit (civicWeightedCalibratedBasinInBox_lowerSet
    model ss threshold hrho hcoop horder hvBasin)

/-- States of the relative calibrated basin with prescribed clearance from
its complement inside the invariant box. -/
def calibratedBasinCoreInBox
    (p : LoopParams) (rho eta : ℝ) : Set (LoopBox p) :=
  {x | eta ≤ Metric.infDist x (civicWeightedCalibratedBasinInBox p rho)ᶜ}

/-- Every relative positive-clearance core is compact, without requiring a
separate description of the basin boundary. -/
theorem calibratedBasinCoreInBox_isCompact
    (p : LoopParams) (rho eta : ℝ) :
    IsCompact (calibratedBasinCoreInBox p rho eta) := by
  have hbox : IsCompact (absorbingBox p) := by
    simpa only [absorbingBox] using
      (isCompact_Icc.prod isCompact_Icc :
        IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc p.I (p.I / p.lambda₀)))
  letI : CompactSpace (LoopBox p) := isCompact_iff_compactSpace.mp hbox
  have hclearance : IsClosed
      {x : LoopBox p |
        eta ≤ Metric.infDist x (civicWeightedCalibratedBasinInBox p rho)ᶜ} :=
    isClosed_Ici.preimage
      (Metric.continuous_infDist_pt
        (civicWeightedCalibratedBasinInBox p rho)ᶜ)
  exact hclearance.isCompact

/-- Positive metric clearance places every core state strictly inside the
relative calibrated basin. -/
theorem calibratedBasinCoreInBox_subset_basin
    (p : LoopParams) (rho : ℝ) {eta : ℝ} (heta : 0 < eta) :
    calibratedBasinCoreInBox p rho eta ⊆
      civicWeightedCalibratedBasinInBox p rho := by
  intro x hx
  by_contra hxBasin
  have hzero : Metric.infDist x
      (civicWeightedCalibratedBasinInBox p rho)ᶜ = 0 :=
    Metric.infDist_zero_of_mem (show
      x ∈ (civicWeightedCalibratedBasinInBox p rho)ᶜ from hxBasin)
  have hclearance := hx
  change eta ≤ Metric.infDist x
    (civicWeightedCalibratedBasinInBox p rho)ᶜ at hclearance
  rw [hzero] at hclearance
  linarith

/-- The underlying state of a zero-control restricted iterate is the
deterministic civic-weighted orbit. -/
theorem controlledCivicWeightedStepInBox_zero_iterate_val
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    (x : LoopBox p) (n : ℕ) :
    (((controlledCivicWeightedStepInBox model rho 0)^[n]) x).1 =
      civicWeightedOrbit p rho x.1 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply', civicWeightedOrbit]
      change controlledCivicWeightedStep p rho 0
          ((((controlledCivicWeightedStepInBox model rho 0)^[n]) x).1) =
        civicWeightedLoopMap p rho
          (((civicWeightedLoopMap p rho)^[n]) x.1)
      rw [controlledCivicWeightedStep_zero_eq_unforced, ih]
      rfl

/-- Membership in the relative basin is exactly the attraction premise needed
by the standalone recurrence theorem on the box. -/
theorem controlledCivicWeightedStepInBox_zero_tendsto_calibrated
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    {x : LoopBox p} (hx : x ∈ civicWeightedCalibratedBasinInBox p rho) :
    Tendsto
      (fun n : ℕ ↦
        (((controlledCivicWeightedStepInBox model rho 0)^[n]) x))
      atTop (nhds (calibratedPointInBox p model)) := by
  apply tendsto_subtype_rng.mpr
  have hfun : (fun n : ℕ ↦
      ((((controlledCivicWeightedStepInBox model rho 0)^[n]) x).1)) =
      civicWeightedOrbit p rho x.1 := by
    funext n
    exact controlledCivicWeightedStepInBox_zero_iterate_val model rho x n
  rw [hfun]
  exact hx

/-- On each compact subset of the calibrated basin, avoiding the calibrated
neighborhood for one common block costs a uniformly positive amount of
quadratic control action. -/
theorem exists_uniform_action_cost_of_avoiding_calibrated
    (p : LoopParams) (rho : ℝ) {K : Set LoopState}
    (hK : IsCompact K)
    (hKbasin : K ⊆ civicWeightedCalibratedBasin p rho)
    {inner outer : ℝ} (hinner : 0 < inner) (hgap : inner < outer) :
    ∃ N : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ x₀ ∈ K, ∀ u : Fin (N + 1) → ℝ,
        (∀ n ≤ N,
          outer ≤ dist
            (finiteControlOrbit (controlledCivicWeightedStep p rho) x₀ u n)
            (calibratedPoint p)) →
          c ≤ finiteQuadraticAction u := by
  have hconv : ∀ x ∈ K,
      Tendsto
        (fun n : ℕ ↦
          (((controlledCivicWeightedStep p rho 0)^[n]) x))
        atTop (nhds (calibratedPoint p)) := by
    intro x hx
    have hxBasin := hKbasin hx
    rw [controlledCivicWeightedStep_zero_eq_unforced]
    change Tendsto (civicWeightedOrbit p rho x) atTop
      (nhds (calibratedPoint p))
    exact hxBasin
  exact exists_uniform_action_cost_of_avoiding_attractor
    (controlledCivicWeightedStep p rho)
    (continuous_uncurry_controlledCivicWeightedStep p rho)
    hK hinner hgap hconv

/-- The preceding action charge applies canonically to every relative
positive-clearance core of the calibrated basin. -/
theorem exists_uniform_action_cost_on_calibratedBasinCoreInBox
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    {eta inner outer : ℝ}
    (heta : 0 < eta) (hinner : 0 < inner) (hgap : inner < outer) :
    ∃ N : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ x₀ ∈ calibratedBasinCoreInBox p rho eta,
        ∀ u : Fin (N + 1) → ℝ,
          (∀ n ≤ N,
            outer ≤ dist
              (finiteControlOrbit
                (controlledCivicWeightedStepInBox model rho) x₀ u n)
              (calibratedPointInBox p model)) →
            c ≤ finiteQuadraticAction u := by
  have hconv : ∀ x ∈ calibratedBasinCoreInBox p rho eta,
      Tendsto
        (fun n : ℕ ↦
          (((controlledCivicWeightedStepInBox model rho 0)^[n]) x))
        atTop (nhds (calibratedPointInBox p model)) := by
    intro x hx
    exact controlledCivicWeightedStepInBox_zero_tendsto_calibrated
      model rho (calibratedBasinCoreInBox_subset_basin p rho heta hx)
  exact exists_uniform_action_cost_of_avoiding_attractor
    (controlledCivicWeightedStepInBox model rho)
    (continuous_uncurry_controlledCivicWeightedStepInBox model rho)
    (calibratedBasinCoreInBox_isCompact p rho eta)
    hinner hgap hconv

/-- Across any number of consecutive blocks whose starting states remain in
the positive-clearance core, avoiding the calibrated neighborhood costs at
least the block count times one fixed positive charge. -/
theorem exists_uniform_linear_action_cost_on_calibratedBasinCoreInBox
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    {eta inner outer : ℝ}
    (heta : 0 < eta) (hinner : 0 < inner) (hgap : inner < outer) :
    ∃ N : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) (x₀ : LoopBox p) (u : ℕ → ℝ),
        (∀ j < q,
          controlOrbit (controlledCivicWeightedStepInBox model rho) x₀ u
              (j * (N + 1)) ∈ calibratedBasinCoreInBox p rho eta) →
        (∀ n < q * (N + 1),
          outer ≤ dist
            (controlOrbit
              (controlledCivicWeightedStepInBox model rho) x₀ u n)
            (calibratedPointInBox p model)) →
        (q : ℝ) * c ≤ quadraticActionPrefix u (q * (N + 1)) := by
  have hconv : ∀ x ∈ calibratedBasinCoreInBox p rho eta,
      Tendsto
        (fun n : ℕ ↦
          (((controlledCivicWeightedStepInBox model rho 0)^[n]) x))
        atTop (nhds (calibratedPointInBox p model)) := by
    intro x hx
    exact controlledCivicWeightedStepInBox_zero_tendsto_calibrated
      model rho (calibratedBasinCoreInBox_subset_basin p rho heta hx)
  exact exists_uniform_linear_action_cost_of_avoiding_attractor
    (controlledCivicWeightedStepInBox model rho)
    (continuous_uncurry_controlledCivicWeightedStepInBox model rho)
    (calibratedBasinCoreInBox_isCompact p rho eta)
    hinner hgap hconv

#print axioms continuous_uncurry_controlledCivicWeightedStep
#print axioms controlledCivicWeightedStep_zero_eq_unforced
#print axioms controlledCivicWeightedStepInBox_zero_tendsto_calibrated
#print axioms calibratedBasinCoreInBox_isCompact
#print axioms calibratedBasinCoreInBox_subset_basin
#print axioms exists_uniform_action_cost_of_avoiding_calibrated
#print axioms exists_uniform_action_cost_on_calibratedBasinCoreInBox
#print axioms exists_uniform_linear_action_cost_on_calibratedBasinCoreInBox

end

end CivicAlignment.PaperII
