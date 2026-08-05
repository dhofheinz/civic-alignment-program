/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.ArrheniusLaw
import CivicAlignment.PaperII.BasinExitRecurrence
import CivicAlignment.PaperII.BistabilityTopology
import CivicAlignment.PaperII.Passage

/-!
# Paper II: the genuine calibrated-basin exit process

The Arrhenius process used elsewhere stops when the policy first reaches the
weighted saddle level.  This file defines the distinct stopping time at which
the noisy state actually leaves the calibrated basin.  The basin is treated
in the invariant box, where it is relatively open and hence measurable.

Every finite history that realizes this event pays the basin-exit
quasipotential `V` exactly in the variational sense.  Order monotonicity turns
any finite exit control from the calibrated corner into a uniform restart
certificate from every reachable state.  The resulting geometric survival
bound proves that the genuine mean-exit logarithmic limsup is at most `V`.
The complementary liminf available here is the first-crossing
quasipotential; `BasinExitLaw` records the unconditional bracket and the
conditional equality theorem.
-/

namespace CivicAlignment.PaperII

open Filter Function MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal

noncomputable section

/-! ## The weighted basin as a relatively open subset of the invariant box -/

/-! ## Finite and infinite noisy exit events -/

/-- The finite controlled state, regarded as an element of the invariant
box. -/
def finiteControlledOrbitInBox
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    {T : ℕ} (u : Fin T → ℝ) (n : ℕ) : LoopBox p :=
  ⟨finiteControlledOrbit p rho u n,
    (finiteControlledOrbit_isControlled p rho u).mem_absorbingBox model n⟩

/-- The finite controlled recursion from an arbitrary state of the invariant
box. -/
def finiteControlledOrbitFromInBox
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    (x₀ : LoopBox p) {T : ℕ} (u : Fin T → ℝ) (n : ℕ) : LoopBox p :=
  finiteControlOrbit (controlledCivicWeightedStepInBox model rho) x₀ u n

/-- The standalone recurrence on the box agrees exactly with the finite
controlled orbit used by the Gaussian process. -/
theorem finiteControlOrbitInBox_eq_finiteControlledOrbitInBox
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    {T : ℕ} (u : Fin T → ℝ) (n : ℕ) :
    finiteControlOrbit (controlledCivicWeightedStepInBox model rho)
        (calibratedPointInBox p model) u n =
      finiteControlledOrbitInBox model rho u n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      apply Subtype.ext
      change controlledCivicWeightedStep p rho (finiteControlValue u n)
          (finiteControlOrbit
            (controlledCivicWeightedStepInBox model rho)
            (calibratedPointInBox p model) u n).1 =
        controlledCivicWeightedStep p rho (extendFiniteControl u n)
          (finiteControlledOrbit p rho u n)
      rw [show (finiteControlOrbit
          (controlledCivicWeightedStepInBox model rho)
          (calibratedPointInBox p model) u n).1 =
          finiteControlledOrbit p rho u n from congrArg Subtype.val ih]
      congr 1

/-- Every finite controlled state reachable from the calibrated corner remains
above that corner in product order. -/
theorem calibratedPointInBox_le_finiteControlledOrbitFromInBox
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (rho : ℝ)
    {T : ℕ} (u : Fin T → ℝ) (n : ℕ) :
    calibratedPointInBox p model ≤
      finiteControlledOrbitFromInBox model rho
        (calibratedPointInBox p model) u n := by
  change calibratedPoint p ≤ finiteControlOrbit
    (controlledCivicWeightedStepInBox model rho)
      (calibratedPointInBox p model) u n
  rw [finiteControlOrbitInBox_eq_finiteControlledOrbitInBox]
  exact (finiteControlledOrbit_isControlled p rho u).calibratedPoint_le
    model ss n

/-- A finite Gaussian vector drives the state out of the calibrated basin by
time `T`. -/
def gaussianBasinExitEvent
    {p : LoopParams} (model : DriftModelAssumptions p)
    (_ss : SmallStepAssumption p) (_threshold : ThresholdAssumption p)
    {rho : ℝ} (_hrho : 0 ≤ rho) (T : ℕ) (sigma : ℝ) :
    Set (Fin T → ℝ) :=
  {xi | ∃ k ∈ Finset.range (T + 1),
    finiteControlledOrbitInBox model rho
        (scaledGaussianControl sigma xi) k ∉
      civicWeightedCalibratedBasinInBox p rho}

/-- Basin exit by a finite horizon from an arbitrary state of the invariant
box.  This is the restart event used after a surviving Gaussian prefix. -/
def gaussianBasinExitEventFromInBox
    {p : LoopParams} (model : DriftModelAssumptions p)
    (_ss : SmallStepAssumption p) (_threshold : ThresholdAssumption p)
    {rho : ℝ} (_hrho : 0 ≤ rho) (x₀ : LoopBox p)
    (T : ℕ) (sigma : ℝ) : Set (Fin T → ℝ) :=
  {xi | ∃ k ∈ Finset.range (T + 1),
    finiteControlledOrbitFromInBox model rho x₀
        (scaledGaussianControl sigma xi) k ∉
      civicWeightedCalibratedBasinInBox p rho}

/-- At each fixed time, the finite controlled state is continuous as a map
into the invariant-box subtype. -/
theorem continuous_finiteControlledOrbitInBox
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    {T : ℕ} (n : ℕ) :
    Continuous (fun u : Fin T → ℝ ↦
      finiteControlledOrbitInBox model rho u n) := by
  exact (continuous_finiteControlledOrbit p rho n).subtype_mk _

/-- At each fixed time the arbitrary-start restricted recursion is continuous
in its finite control vector. -/
theorem continuous_finiteControlledOrbitFromInBox
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    (x₀ : LoopBox p) {T : ℕ} (n : ℕ) :
    Continuous (fun u : Fin T → ℝ ↦
      finiteControlledOrbitFromInBox model rho x₀ u n) := by
  have hpair : Continuous (fun u : Fin T → ℝ ↦
      ((x₀, u) : LoopBox p × (Fin T → ℝ))) := by
    fun_prop
  exact (continuous_finiteControlOrbit
    (controlledCivicWeightedStepInBox model rho)
    (continuous_uncurry_controlledCivicWeightedStepInBox model rho) n).comp hpair

/-- The finite-vector genuine-exit event is Borel measurable. -/
theorem measurableSet_gaussianBasinExitEvent
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (T : ℕ) (sigma : ℝ) :
    MeasurableSet
      (gaussianBasinExitEvent model ss threshold hrho T sigma) := by
  let basin := civicWeightedCalibratedBasinInBox p rho
  have hclosed : IsClosed basinᶜ :=
    (civicWeightedCalibratedBasinInBox_isOpen
      model ss threshold hrho).isClosed_compl
  have hmeasurable (k : ℕ) : MeasurableSet
      {xi : Fin T → ℝ |
        finiteControlledOrbitInBox model rho
            (scaledGaussianControl sigma xi) k ∈ basinᶜ} := by
    exact hclosed.measurableSet.preimage
      ((continuous_finiteControlledOrbitInBox model rho k).measurable.comp
        (by unfold scaledGaussianControl; fun_prop))
  rw [show gaussianBasinExitEvent model ss threshold hrho T sigma =
      ⋃ k ∈ Finset.range (T + 1),
        {xi : Fin T → ℝ |
          finiteControlledOrbitInBox model rho
              (scaledGaussianControl sigma xi) k ∈ basinᶜ} by
    ext xi
    simp only [gaussianBasinExitEvent, mem_setOf_eq, mem_iUnion,
      mem_compl_iff]
    constructor
    · rintro ⟨k, hk, hexit⟩
      exact ⟨k, hk, hexit⟩
    · rintro ⟨k, hk, hexit⟩
      exact ⟨k, hk, hexit⟩]
  exact Finset.measurableSet_biUnion _ fun k _ ↦ hmeasurable k

/-- The arbitrary-start finite-vector basin-exit event is Borel measurable. -/
theorem measurableSet_gaussianBasinExitEventFromInBox
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (x₀ : LoopBox p)
    (T : ℕ) (sigma : ℝ) :
    MeasurableSet
      (gaussianBasinExitEventFromInBox
        model ss threshold hrho x₀ T sigma) := by
  let basin := civicWeightedCalibratedBasinInBox p rho
  have hclosed : IsClosed basinᶜ :=
    (civicWeightedCalibratedBasinInBox_isOpen
      model ss threshold hrho).isClosed_compl
  have hmeasurable (k : ℕ) : MeasurableSet
      {xi : Fin T → ℝ |
        finiteControlledOrbitFromInBox model rho x₀
            (scaledGaussianControl sigma xi) k ∈ basinᶜ} := by
    exact hclosed.measurableSet.preimage
      ((continuous_finiteControlledOrbitFromInBox
          model rho x₀ k).measurable.comp
        (by unfold scaledGaussianControl; fun_prop))
  rw [show gaussianBasinExitEventFromInBox
        model ss threshold hrho x₀ T sigma =
      ⋃ k ∈ Finset.range (T + 1),
        {xi : Fin T → ℝ |
          finiteControlledOrbitFromInBox model rho x₀
              (scaledGaussianControl sigma xi) k ∈ basinᶜ} by
    ext xi
    simp only [gaussianBasinExitEventFromInBox, mem_setOf_eq, mem_iUnion,
      mem_compl_iff, basin]
    constructor
    · rintro ⟨k, hk, hexit⟩
      exact ⟨k, hk, hexit⟩
    · rintro ⟨k, hk, hexit⟩
      exact ⟨k, hk, hexit⟩]
  exact Finset.measurableSet_biUnion _ fun k _ ↦ hmeasurable k

/-- Product-Gaussian probability of genuine basin exit by a fixed finite
horizon. -/
def gaussianBasinExitProbability
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (T : ℕ) (sigma : ℝ) : ℝ≥0∞ :=
  standardGaussianVector T
    (gaussianBasinExitEvent model ss threshold hrho T sigma)

/-- Product-Gaussian basin-exit probability from an arbitrary restart state
of the invariant box. -/
def gaussianBasinExitProbabilityFromInBox
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (x₀ : LoopBox p)
    (T : ℕ) (sigma : ℝ) : ℝ≥0∞ :=
  standardGaussianVector T
    (gaussianBasinExitEventFromInBox
      model ss threshold hrho x₀ T sigma)

/-- Failure to leave the calibrated basin during an arbitrary-start finite
window. -/
def gaussianBasinSurvivalEventFromInBox
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (x₀ : LoopBox p)
    (T : ℕ) (sigma : ℝ) : Set (Fin T → ℝ) :=
  (gaussianBasinExitEventFromInBox
    model ss threshold hrho x₀ T sigma)ᶜ

/-- The arbitrary-start finite-window basin-survival probability. -/
def gaussianBasinSurvivalProbabilityFromInBox
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (x₀ : LoopBox p)
    (T : ℕ) (sigma : ℝ) : ℝ≥0∞ :=
  standardGaussianVector T
    (gaussianBasinSurvivalEventFromInBox
      model ss threshold hrho x₀ T sigma)

/-- Starting from the calibrated corner, the arbitrary-start event is exactly
the canonical finite-vector basin-exit event. -/
theorem gaussianBasinExitEventFromInBox_calibratedPoint
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (T : ℕ) (sigma : ℝ) :
    gaussianBasinExitEventFromInBox model ss threshold hrho
        (calibratedPointInBox p model) T sigma =
      gaussianBasinExitEvent model ss threshold hrho T sigma := by
  ext xi
  simp only [gaussianBasinExitEventFromInBox, gaussianBasinExitEvent,
    mem_setOf_eq]
  apply exists_congr
  intro k
  apply and_congr_right
  intro _hk
  rw [finiteControlledOrbitFromInBox,
    finiteControlOrbitInBox_eq_finiteControlledOrbitInBox]

/-- Consequently the arbitrary-start probability at the calibrated corner is
the canonical finite-window basin-exit probability. -/
theorem gaussianBasinExitProbabilityFromInBox_calibratedPoint
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (T : ℕ) (sigma : ℝ) :
    gaussianBasinExitProbabilityFromInBox model ss threshold hrho
        (calibratedPointInBox p model) T sigma =
      gaussianBasinExitProbability model ss threshold hrho T sigma := by
  unfold gaussianBasinExitProbabilityFromInBox gaussianBasinExitProbability
  rw [gaussianBasinExitEventFromInBox_calibratedPoint]

/-- Finite basin survival means that every state through the horizon remains
in the relative basin. -/
theorem mem_gaussianBasinSurvivalEventFromInBox_iff
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (x₀ : LoopBox p)
    (T : ℕ) (sigma : ℝ) (xi : Fin T → ℝ) :
    xi ∈ gaussianBasinSurvivalEventFromInBox
        model ss threshold hrho x₀ T sigma ↔
      ∀ k ≤ T,
        finiteControlledOrbitFromInBox model rho x₀
            (scaledGaussianControl sigma xi) k ∈
          civicWeightedCalibratedBasinInBox p rho := by
  simp only [gaussianBasinSurvivalEventFromInBox, mem_compl_iff,
    gaussianBasinExitEventFromInBox, mem_setOf_eq, Finset.mem_range]
  constructor
  · intro h k hk
    by_contra hnot
    exact h ⟨k, by omega, hnot⟩
  · intro h hexit
    obtain ⟨k, hk, hnot⟩ := hexit
    exact hnot (h k (by omega))

/-- Basin survival is Borel measurable. -/
theorem measurableSet_gaussianBasinSurvivalEventFromInBox
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (x₀ : LoopBox p)
    (T : ℕ) (sigma : ℝ) :
    MeasurableSet (gaussianBasinSurvivalEventFromInBox
      model ss threshold hrho x₀ T sigma) :=
  (measurableSet_gaussianBasinExitEventFromInBox
    model ss threshold hrho x₀ T sigma).compl

/-- Survival probability is one minus exit probability. -/
theorem gaussianBasinSurvivalProbabilityFromInBox_eq_one_sub
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (x₀ : LoopBox p)
    (T : ℕ) (sigma : ℝ) :
    gaussianBasinSurvivalProbabilityFromInBox
        model ss threshold hrho x₀ T sigma =
      1 - gaussianBasinExitProbabilityFromInBox
        model ss threshold hrho x₀ T sigma := by
  letI : IsProbabilityMeasure (standardGaussianVector T) := by
    unfold standardGaussianVector
    infer_instance
  unfold gaussianBasinSurvivalProbabilityFromInBox
    gaussianBasinSurvivalEventFromInBox
    gaussianBasinExitProbabilityFromInBox
  rw [measure_compl
    (measurableSet_gaussianBasinExitEventFromInBox
      model ss threshold hrho x₀ T sigma)
    (measure_ne_top (standardGaussianVector T) _)]
  rw [measure_univ]

/-- Exact pathwise restart: a concatenated Gaussian vector survives precisely
when its prefix survives and its suffix survives from the prefix endpoint. -/
theorem mem_gaussianBasinSurvivalEventFromInBox_append_iff
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (x₀ : LoopBox p)
    {N T : ℕ} (sigma : ℝ) (u : Fin N → ℝ) (v : Fin T → ℝ) :
    Fin.append u v ∈ gaussianBasinSurvivalEventFromInBox
        model ss threshold hrho x₀ (N + T) sigma ↔
      u ∈ gaussianBasinSurvivalEventFromInBox
          model ss threshold hrho x₀ N sigma ∧
        v ∈ gaussianBasinSurvivalEventFromInBox
          model ss threshold hrho
          (finiteControlledOrbitFromInBox model rho x₀
            (scaledGaussianControl sigma u) N) T sigma := by
  rw [mem_gaussianBasinSurvivalEventFromInBox_iff,
    mem_gaussianBasinSurvivalEventFromInBox_iff,
    mem_gaussianBasinSurvivalEventFromInBox_iff]
  simp only [finiteControlledOrbitFromInBox]
  constructor
  · intro h
    constructor
    · intro n hn
      rw [← finiteControlOrbit_append_left
        (controlledCivicWeightedStepInBox model rho) x₀
        (scaledGaussianControl sigma u) (scaledGaussianControl sigma v) hn,
        ← scaledGaussianControl_append]
      exact h n (hn.trans (Nat.le_add_right N T))
    · intro k hk
      rw [← finiteControlOrbit_append_right
        (controlledCivicWeightedStepInBox model rho) x₀
        (scaledGaussianControl sigma u) (scaledGaussianControl sigma v) hk,
        ← scaledGaussianControl_append]
      exact h (N + k) (Nat.add_le_add_left hk N)
  · rintro ⟨hprefix, hsuffix⟩ n hn
    by_cases hnPrefix : n ≤ N
    · rw [scaledGaussianControl_append,
        finiteControlOrbit_append_left
          (controlledCivicWeightedStepInBox model rho) x₀
          (scaledGaussianControl sigma u) (scaledGaussianControl sigma v) hnPrefix]
      exact hprefix n hnPrefix
    · have hNn : N ≤ n := Nat.le_of_lt (lt_of_not_ge hnPrefix)
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNn
      have hk : k ≤ T := by omega
      rw [scaledGaussianControl_append,
        finiteControlOrbit_append_right
          (controlledCivicWeightedStepInBox model rho) x₀
          (scaledGaussianControl sigma u) (scaledGaussianControl sigma v) hk]
      exact hsuffix k hk

/-! ## Uniform finite-product restart for genuine basin exit -/

/-- The basin-survival event transported to independent prefix and suffix
coordinates. -/
def gaussianBasinRestartSurvivalSet
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (x₀ : LoopBox p)
    (N T : ℕ) (sigma : ℝ) :
    Set ((Fin N → ℝ) × (Fin T → ℝ)) :=
  (gaussianVectorSplitEquiv N T).symm ⁻¹'
    gaussianBasinSurvivalEventFromInBox
      model ss threshold hrho x₀ (N + T) sigma

/-- The transported basin-survival restart event is measurable. -/
theorem measurableSet_gaussianBasinRestartSurvivalSet
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (x₀ : LoopBox p)
    (N T : ℕ) (sigma : ℝ) :
    MeasurableSet (gaussianBasinRestartSurvivalSet
      model ss threshold hrho x₀ N T sigma) := by
  exact (measurableSet_gaussianBasinSurvivalEventFromInBox
    model ss threshold hrho x₀ (N + T) sigma).preimage
      (gaussianVectorSplitEquiv N T).symm.measurable

/-- After a surviving prefix, the restart fiber is exactly the suffix
survival event from the prefix endpoint. -/
theorem gaussianBasinRestartSurvivalSet_fiber_of_mem
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (x₀ : LoopBox p)
    {N T : ℕ} (sigma : ℝ) (u : Fin N → ℝ)
    (hu : u ∈ gaussianBasinSurvivalEventFromInBox
      model ss threshold hrho x₀ N sigma) :
    Prod.mk u ⁻¹' gaussianBasinRestartSurvivalSet
        model ss threshold hrho x₀ N T sigma =
      gaussianBasinSurvivalEventFromInBox
        model ss threshold hrho
        (finiteControlledOrbitFromInBox model rho x₀
          (scaledGaussianControl sigma u) N) T sigma := by
  ext v
  simp only [mem_preimage]
  rw [show ((u, v) ∈ gaussianBasinRestartSurvivalSet
      model ss threshold hrho x₀ N T sigma) ↔
      Fin.append u v ∈ gaussianBasinSurvivalEventFromInBox
        model ss threshold hrho x₀ (N + T) sigma by
    simp only [gaussianBasinRestartSurvivalSet, mem_preimage,
      gaussianVectorSplitEquiv_symm_pair]]
  rw [mem_gaussianBasinSurvivalEventFromInBox_append_iff]
  simp only [hu, true_and]

/-- After a failed prefix, the basin-survival restart fiber is empty. -/
theorem gaussianBasinRestartSurvivalSet_fiber_of_notMem
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (x₀ : LoopBox p)
    {N T : ℕ} (sigma : ℝ) (u : Fin N → ℝ)
    (hu : u ∉ gaussianBasinSurvivalEventFromInBox
      model ss threshold hrho x₀ N sigma) :
    Prod.mk u ⁻¹' gaussianBasinRestartSurvivalSet
        model ss threshold hrho x₀ N T sigma = ∅ := by
  ext v
  simp only [mem_preimage]
  rw [show ((u, v) ∈ gaussianBasinRestartSurvivalSet
      model ss threshold hrho x₀ N T sigma) ↔
      Fin.append u v ∈ gaussianBasinSurvivalEventFromInBox
        model ss threshold hrho x₀ (N + T) sigma by
    simp only [gaussianBasinRestartSurvivalSet, mem_preimage,
      gaussianVectorSplitEquiv_symm_pair]]
  rw [mem_gaussianBasinSurvivalEventFromInBox_append_iff]
  simp only [hu, false_and, mem_empty_iff_false]

/-- Under the product decomposition, full basin survival is the measure of
the restart set. -/
theorem gaussianBasinSurvivalProbabilityFromInBox_eq_restartMeasure
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (x₀ : LoopBox p)
    (N T : ℕ) (sigma : ℝ) :
    gaussianBasinSurvivalProbabilityFromInBox
        model ss threshold hrho x₀ (N + T) sigma =
      (standardGaussianVector N).prod (standardGaussianVector T)
        (gaussianBasinRestartSurvivalSet
          model ss threshold hrho x₀ N T sigma) := by
  unfold gaussianBasinSurvivalProbabilityFromInBox
  have hpreimage :
      gaussianVectorSplitEquiv N T ⁻¹'
          gaussianBasinRestartSurvivalSet
            model ss threshold hrho x₀ N T sigma =
        gaussianBasinSurvivalEventFromInBox
          model ss threshold hrho x₀ (N + T) sigma := by
    ext xi
    simp only [gaussianBasinRestartSurvivalSet, mem_preimage,
      MeasurableEquiv.symm_apply_apply]
  rw [← hpreimage]
  exact standardGaussianVector_split_preimage
    (measurableSet_gaussianBasinRestartSurvivalSet
      model ss threshold hrho x₀ N T sigma)

/-- A uniform one-block exit lower bound contracts survival from the
calibrated corner by its complementary factor after every block. -/
theorem gaussianBasinSurvivalProbabilityFromInBox_add_le
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (N T : ℕ) (sigma : ℝ) (q : ℝ≥0∞)
    (hq : ∀ x : LoopBox p, calibratedPointInBox p model ≤ x →
      q ≤ gaussianBasinExitProbabilityFromInBox
        model ss threshold hrho x T sigma) :
    gaussianBasinSurvivalProbabilityFromInBox
        model ss threshold hrho (calibratedPointInBox p model)
          (N + T) sigma ≤
      gaussianBasinSurvivalProbabilityFromInBox
          model ss threshold hrho (calibratedPointInBox p model) N sigma *
        (1 - q) := by
  let μN := standardGaussianVector N
  let μT := standardGaussianVector T
  let xcal := calibratedPointInBox p model
  let S := gaussianBasinRestartSurvivalSet
    model ss threshold hrho xcal N T sigma
  let A := gaussianBasinSurvivalEventFromInBox
    model ss threshold hrho xcal N sigma
  letI : IsProbabilityMeasure μN := by
    dsimp only [μN, standardGaussianVector]
    infer_instance
  letI : IsProbabilityMeasure μT := by
    dsimp only [μT, standardGaussianVector]
    infer_instance
  have hS : MeasurableSet S :=
    measurableSet_gaussianBasinRestartSurvivalSet
      model ss threshold hrho xcal N T sigma
  have hA : MeasurableSet A :=
    measurableSet_gaussianBasinSurvivalEventFromInBox
      model ss threshold hrho xcal N sigma
  have hfiber : ∀ u : Fin N → ℝ,
      μT (Prod.mk u ⁻¹' S) ≤ A.indicator (fun _ ↦ 1 - q) u := by
    intro u
    by_cases hu : u ∈ A
    · rw [indicator_of_mem hu]
      let x := finiteControlledOrbitFromInBox model rho xcal
        (scaledGaussianControl sigma u) N
      have hx : calibratedPointInBox p model ≤ x := by
        dsimp only [x, xcal]
        exact calibratedPointInBox_le_finiteControlledOrbitFromInBox
          model ss rho (scaledGaussianControl sigma u) N
      dsimp only [S]
      rw [gaussianBasinRestartSurvivalSet_fiber_of_mem
        model ss threshold hrho xcal sigma u hu]
      exact prob_compl_le_one_sub_of_le_prob
        (hq x hx)
        (measurableSet_gaussianBasinExitEventFromInBox
          model ss threshold hrho x T sigma)
    · rw [indicator_of_notMem hu]
      dsimp only [S]
      rw [gaussianBasinRestartSurvivalSet_fiber_of_notMem
        model ss threshold hrho xcal sigma u hu]
      simp only [measure_empty]
      exact le_rfl
  calc
    gaussianBasinSurvivalProbabilityFromInBox
        model ss threshold hrho xcal (N + T) sigma = μN.prod μT S := by
      exact gaussianBasinSurvivalProbabilityFromInBox_eq_restartMeasure
        model ss threshold hrho xcal N T sigma
    _ = ∫⁻ u, μT (Prod.mk u ⁻¹' S) ∂μN := Measure.prod_apply hS
    _ ≤ ∫⁻ u, A.indicator (fun _ ↦ 1 - q) u ∂μN :=
      lintegral_mono hfiber
    _ = (1 - q) * μN A := lintegral_indicator_const hA (1 - q)
    _ = gaussianBasinSurvivalProbabilityFromInBox
          model ss threshold hrho xcal N sigma * (1 - q) := by
      rw [mul_comm]
      rfl

/-- A common one-block exit floor gives geometric genuine-basin survival on
integer multiples of the block horizon. -/
theorem gaussianBasinSurvivalProbabilityFromInBox_mul_le_pow
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (T : ℕ) (sigma : ℝ) (q : ℝ≥0∞)
    (hq : ∀ x : LoopBox p, calibratedPointInBox p model ≤ x →
      q ≤ gaussianBasinExitProbabilityFromInBox
        model ss threshold hrho x T sigma) :
    ∀ k : ℕ,
      gaussianBasinSurvivalProbabilityFromInBox
          model ss threshold hrho (calibratedPointInBox p model)
            (k * T) sigma ≤
        (1 - q) ^ k := by
  intro k
  induction k with
  | zero =>
      letI : IsProbabilityMeasure (standardGaussianVector 0) := by
        unfold standardGaussianVector
        infer_instance
      simp only [zero_mul, pow_zero]
      unfold gaussianBasinSurvivalProbabilityFromInBox
      exact prob_le_one
  | succ k ih =>
      calc
        gaussianBasinSurvivalProbabilityFromInBox
            model ss threshold hrho (calibratedPointInBox p model)
              ((k + 1) * T) sigma =
            gaussianBasinSurvivalProbabilityFromInBox
              model ss threshold hrho (calibratedPointInBox p model)
                (k * T + T) sigma := by
                  rw [Nat.add_mul, one_mul]
        _ ≤ gaussianBasinSurvivalProbabilityFromInBox
              model ss threshold hrho (calibratedPointInBox p model)
                (k * T) sigma * (1 - q) :=
          gaussianBasinSurvivalProbabilityFromInBox_add_le
            model ss threshold hrho (k * T) T sigma q hq
        _ ≤ (1 - q) ^ k * (1 - q) :=
          mul_le_mul_of_nonneg_right ih bot_le
        _ = (1 - q) ^ (k + 1) := (pow_succ (1 - q) k).symm

/-- The geometric estimate in terms of the canonical finite-window exit
probability. -/
theorem one_sub_gaussianBasinExitProbability_mul_le_pow
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (T : ℕ) (sigma : ℝ) (q : ℝ≥0∞)
    (hq : ∀ x : LoopBox p, calibratedPointInBox p model ≤ x →
      q ≤ gaussianBasinExitProbabilityFromInBox
        model ss threshold hrho x T sigma)
    (k : ℕ) :
    1 - gaussianBasinExitProbability
        model ss threshold hrho (k * T) sigma ≤
      (1 - q) ^ k := by
  rw [← gaussianBasinExitProbabilityFromInBox_calibratedPoint,
    ← gaussianBasinSurvivalProbabilityFromInBox_eq_one_sub]
  exact gaussianBasinSurvivalProbabilityFromInBox_mul_le_pow
    model ss threshold hrho T sigma q hq k

/-- The extended-real fixed-horizon logarithmic rate of genuine basin exit. -/
def gaussianBasinExitLogRate
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (T : ℕ) (sigma : ℝ) : EReal :=
  (sigma ^ 2 : ℝ) * ENNReal.log
    (gaussianBasinExitProbability model ss threshold hrho T sigma)

/-- If one finite control exits at its terminal horizon, then the one-sided
Gaussian control box above it consists entirely of genuine basin exits.  No
open exterior endpoint or overshoot margin is required. -/
theorem gaussianControlBox_subset_basinExitEvent_of_terminal_exit
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    {T : ℕ} (u : Fin T → ℝ)
    (hexit : finiteControlledOrbit p rho u T ∉
      civicWeightedCalibratedBasin p rho)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    gaussianControlBox u sigma ⊆
      gaussianBasinExitEvent model ss threshold hrho T sigma := by
  have hnominal : finiteControlOrbit
        (controlledCivicWeightedStepInBox model rho)
        (calibratedPointInBox p model) u T ∉
      civicWeightedCalibratedBasinInBox p rho := by
    rw [finiteControlOrbitInBox_eq_finiteControlledOrbitInBox]
    simpa only [mem_civicWeightedCalibratedBasinInBox_iff,
      finiteControlledOrbitInBox] using hexit
  intro xi hxi
  have huv : ∀ i, u i ≤ scaledGaussianControl sigma xi i := by
    intro i
    have hi := hxi i (mem_univ i)
    have hscaled := (div_le_iff₀ hsigma).mp hi.1
    simpa only [scaledGaussianControl, mul_comm] using hscaled
  have hcontrolledExit :=
    finiteControlOrbitInBox_not_mem_basin_of_mono_controls
      model ss threshold hrho hcoop huv (calibratedPointInBox p model)
      hnominal
  refine ⟨T, by simp, ?_⟩
  rw [← finiteControlOrbitInBox_eq_finiteControlledOrbitInBox]
  exact hcontrolledExit

/-- The same one-sided Gaussian box forces exit uniformly from every ordered
restart state above the calibrated corner. -/
theorem gaussianControlBox_subset_basinExitEventFromInBox
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    {T : ℕ} (u : Fin T → ℝ)
    (hexit : finiteControlledOrbit p rho u T ∉
      civicWeightedCalibratedBasin p rho)
    {x₀ : LoopBox p} (hcalibrated : calibratedPointInBox p model ≤ x₀)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    gaussianControlBox u sigma ⊆
      gaussianBasinExitEventFromInBox
        model ss threshold hrho x₀ T sigma := by
  have hnominal : finiteControlOrbit
        (controlledCivicWeightedStepInBox model rho)
        (calibratedPointInBox p model) u T ∉
      civicWeightedCalibratedBasinInBox p rho := by
    rw [finiteControlOrbitInBox_eq_finiteControlledOrbitInBox]
    simpa only [mem_civicWeightedCalibratedBasinInBox_iff,
      finiteControlledOrbitInBox] using hexit
  intro xi hxi
  have huv : ∀ i, u i ≤ scaledGaussianControl sigma xi i := by
    intro i
    have hi := hxi i (mem_univ i)
    have hscaled := (div_le_iff₀ hsigma).mp hi.1
    simpa only [scaledGaussianControl, mul_comm] using hscaled
  have hcontrolledExit :=
    finiteControlOrbitInBox_not_mem_basin_of_ordered_start
      model ss threshold hrho hcoop huv hcalibrated hnominal
  exact ⟨T, by simp, hcontrolledExit⟩

/-- One finite terminal-exit control supplies a common positive block-success
floor at every ordered restart state. -/
theorem gaussianControlBox_probability_le_basinExitProbabilityFromInBox
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    {T : ℕ} (u : Fin T → ℝ)
    (hexit : finiteControlledOrbit p rho u T ∉
      civicWeightedCalibratedBasin p rho)
    {x₀ : LoopBox p} (hcalibrated : calibratedPointInBox p model ≤ x₀)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    standardGaussianVector T (gaussianControlBox u sigma) ≤
      gaussianBasinExitProbabilityFromInBox
        model ss threshold hrho x₀ T sigma := by
  exact measure_mono
    (gaussianControlBox_subset_basinExitEventFromInBox
      model ss threshold hrho hcoop u hexit hcalibrated hsigma)

/-- The product-Gaussian probability of the one-sided control box is a lower
bound for the fixed-horizon genuine-exit probability. -/
theorem gaussianControlBox_probability_le_basinExitProbability
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    {T : ℕ} (u : Fin T → ℝ)
    (hexit : finiteControlledOrbit p rho u T ∉
      civicWeightedCalibratedBasin p rho)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    standardGaussianVector T (gaussianControlBox u sigma) ≤
      gaussianBasinExitProbability model ss threshold hrho T sigma := by
  exact measure_mono
    (gaussianControlBox_subset_basinExitEvent_of_terminal_exit
      model ss threshold hrho hcoop u hexit hsigma)

/-- Every exhibited terminal exit gives the matching fixed-horizon Gaussian
large-deviation lower bound at exactly its action, even when its endpoint is
on the basin boundary. -/
theorem gaussianBasinExitLogRate_liminf_of_terminal_control
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    {T : ℕ} (u : Fin T → ℝ)
    (hexit : finiteControlledOrbit p rho u T ∉
      civicWeightedCalibratedBasin p rho) :
    ((-gaussianVectorAction u : ℝ) : EReal) ≤
      liminf
        (fun sigma : ℝ ↦
          gaussianBasinExitLogRate model ss threshold hrho T sigma)
        (nhdsWithin 0 (Ioi (0 : ℝ))) := by
  have hpointwise : ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      (sigma ^ 2 : ℝ) *
          ENNReal.log
            (standardGaussianVector T (gaussianControlBox u sigma)) ≤
        gaussianBasinExitLogRate model ss threshold hrho T sigma := by
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    have hprob := gaussianControlBox_probability_le_basinExitProbability
      model ss threshold hrho hcoop u hexit hsigma
    have hlog := ENNReal.logOrderIso.monotone hprob
    change ENNReal.log
        (standardGaussianVector T (gaussianControlBox u sigma)) ≤
      ENNReal.log
        (gaussianBasinExitProbability model ss threshold hrho T sigma) at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog
      (show (0 : EReal) ≤ (sigma ^ 2 : ℝ) by
        exact_mod_cast sq_nonneg sigma)
    simpa only [gaussianBasinExitLogRate] using hmul
  exact (gaussianControlBox_logRate_liminf u).trans
    (liminf_le_liminf hpointwise)

/-- For every positive tolerance, one fixed horizon realizes the genuine
basin-exit lower probability rate within that tolerance of the basin
quasipotential.  The horizon depends on the tolerance, never on the noise
scale. -/
theorem exists_horizon_gaussianBasinExitLogRate_liminf
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ T : ℕ,
      (((-civicQuasipotential p rho - delta : ℝ) : EReal) ≤
        liminf
          (fun sigma : ℝ ↦
            gaussianBasinExitLogRate model ss threshold hrho T sigma)
          (nhdsWithin 0 (Ioi (0 : ℝ)))) := by
  have hnonempty := quasipotentialActionSet_nonempty
    model ss hrho hrhoCure
  have hinfLt : sInf (quasipotentialActionSet p rho) <
      civicQuasipotential p rho + delta := by
    rw [← civicQuasipotential]
    linarith
  obtain ⟨a, ha, haLt⟩ := exists_lt_of_csInf_lt hnonempty hinfLt
  rcases ha with ⟨T, u, x, path, hexit, rfl⟩
  let v : Fin T → ℝ := fun i ↦ u i
  have horbit : finiteControlledOrbit p rho v T = x T :=
    finiteControlledOrbit_restrict_eq path le_rfl
  have hexitFinite : finiteControlledOrbit p rho v T ∉
      civicWeightedCalibratedBasin p rho := by
    rwa [horbit]
  have hrate := gaussianBasinExitLogRate_liminf_of_terminal_control
    model ss threshold hrho hcoop v hexitFinite
  have haction : gaussianVectorAction v = controlAction u T :=
    gaussianVectorAction_restrict u T
  refine ⟨T, ?_⟩
  have hcost : -civicQuasipotential p rho - delta ≤
      -gaussianVectorAction v := by
    rw [haction]
    linarith
  exact (show
      (((-civicQuasipotential p rho - delta : ℝ) : EReal) ≤
        ((-gaussianVectorAction v : ℝ) : EReal)) by
      exact_mod_cast hcost).trans hrate

/-- The infinite noisy state, regarded as a state in the invariant box. -/
def gaussianNoisyOrbitInBox
    {p : LoopParams} (model : DriftModelAssumptions p)
    (rho sigma : ℝ) (xi : GaussianNoisePath) (n : ℕ) : LoopBox p :=
  ⟨gaussianNoisyOrbit p rho sigma xi n,
    (gaussianNoisyOrbit_isControlled p rho sigma xi).mem_absorbingBox model n⟩

/-- At every fixed time the noisy state is continuous as an invariant-box
valued random variable. -/
theorem continuous_gaussianNoisyOrbitInBox
    {p : LoopParams} (model : DriftModelAssumptions p)
    (rho sigma : ℝ) (n : ℕ) :
    Continuous (fun xi : GaussianNoisePath ↦
      gaussianNoisyOrbitInBox model rho sigma xi n) := by
  exact (continuous_gaussianNoisyOrbit p rho sigma n).subtype_mk _

/-- The event that the infinite noisy recursion has genuinely left the
calibrated basin by time `T`. -/
def gaussianBasinExitByEvent
    {p : LoopParams} (model : DriftModelAssumptions p)
    (_ss : SmallStepAssumption p) (_threshold : ThresholdAssumption p)
    {rho : ℝ} (_hrho : 0 ≤ rho) (T : ℕ) (sigma : ℝ) :
    Set GaussianNoisePath :=
  {xi | ∃ k ∈ Finset.range (T + 1),
    gaussianNoisyOrbitInBox model rho sigma xi k ∉
      civicWeightedCalibratedBasinInBox p rho}

/-- The infinite-history genuine-exit event is Borel measurable. -/
theorem measurableSet_gaussianBasinExitByEvent
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (T : ℕ) (sigma : ℝ) :
    MeasurableSet
      (gaussianBasinExitByEvent model ss threshold hrho T sigma) := by
  let basin := civicWeightedCalibratedBasinInBox p rho
  have hclosed : IsClosed basinᶜ :=
    (civicWeightedCalibratedBasinInBox_isOpen
      model ss threshold hrho).isClosed_compl
  have hmeasurable (k : ℕ) : MeasurableSet
      {xi : GaussianNoisePath |
        gaussianNoisyOrbitInBox model rho sigma xi k ∈ basinᶜ} := by
    exact hclosed.measurableSet.preimage
      (continuous_gaussianNoisyOrbitInBox model rho sigma k).measurable
  rw [show gaussianBasinExitByEvent model ss threshold hrho T sigma =
      ⋃ k ∈ Finset.range (T + 1),
        {xi : GaussianNoisePath |
          gaussianNoisyOrbitInBox model rho sigma xi k ∈ basinᶜ} by
    ext xi
    simp only [gaussianBasinExitByEvent, mem_setOf_eq, mem_iUnion,
      mem_compl_iff]
    constructor
    · rintro ⟨k, hk, hexit⟩
      exact ⟨k, hk, hexit⟩
    · rintro ⟨k, hk, hexit⟩
      exact ⟨k, hk, hexit⟩]
  exact Finset.measurableSet_biUnion _ fun k _ ↦ hmeasurable k

/-- Pulling the finite-vector basin-exit event back along prefix restriction
gives the genuine exit event for the infinite recursion. -/
theorem gaussianPrefix_preimage_basinExitEvent
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (T : ℕ) (sigma : ℝ) :
    gaussianPrefix T ⁻¹'
        gaussianBasinExitEvent model ss threshold hrho T sigma =
      gaussianBasinExitByEvent model ss threshold hrho T sigma := by
  ext xi
  simp only [mem_preimage, gaussianBasinExitEvent,
    gaussianBasinExitByEvent, mem_setOf_eq]
  constructor
  · rintro ⟨k, hk, hexit⟩
    have hkT : k ≤ T := by
      simp only [Finset.mem_range] at hk
      omega
    refine ⟨k, hk, ?_⟩
    have horbit :
        finiteControlledOrbitInBox model rho
            (scaledGaussianControl sigma (gaussianPrefix T xi)) k =
          gaussianNoisyOrbitInBox model rho sigma xi k := by
      apply Subtype.ext
      exact (gaussianNoisyOrbit_eq_finiteControlledOrbit
        p rho sigma xi hkT).symm
    rwa [horbit] at hexit
  · rintro ⟨k, hk, hexit⟩
    have hkT : k ≤ T := by
      simp only [Finset.mem_range] at hk
      omega
    refine ⟨k, hk, ?_⟩
    have horbit :
        finiteControlledOrbitInBox model rho
            (scaledGaussianControl sigma (gaussianPrefix T xi)) k =
          gaussianNoisyOrbitInBox model rho sigma xi k := by
      apply Subtype.ext
      exact (gaussianNoisyOrbit_eq_finiteControlledOrbit
        p rho sigma xi hkT).symm
    rwa [horbit]

/-- Infinite-history exit by `T` has exactly the canonical finite-vector
probability. -/
theorem standardGaussianSequence_basinExitByEvent
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (T : ℕ) (sigma : ℝ) :
    standardGaussianSequence
        (gaussianBasinExitByEvent model ss threshold hrho T sigma) =
      gaussianBasinExitProbability model ss threshold hrho T sigma := by
  rw [← gaussianPrefix_preimage_basinExitEvent
    model ss threshold hrho T sigma]
  rw [← Measure.map_apply (measurable_gaussianPrefix T)
    (measurableSet_gaussianBasinExitEvent
      model ss threshold hrho T sigma)]
  rw [standardGaussianSequence_map_prefix]
  rfl

/-- Genuine basin-exit probability is monotone in the finite horizon. -/
theorem monotone_gaussianBasinExitProbability
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (sigma : ℝ) :
    Monotone
      (fun T ↦ gaussianBasinExitProbability
        model ss threshold hrho T sigma) := by
  intro N T hNT
  change gaussianBasinExitProbability model ss threshold hrho N sigma ≤
    gaussianBasinExitProbability model ss threshold hrho T sigma
  rw [← standardGaussianSequence_basinExitByEvent
      model ss threshold hrho N sigma,
    ← standardGaussianSequence_basinExitByEvent
      model ss threshold hrho T sigma]
  apply measure_mono
  rintro xi ⟨k, hk, hexit⟩
  refine ⟨k, ?_, hexit⟩
  simp only [Finset.mem_range] at hk ⊢
  omega

/-! ## The genuine basin-exit stopping time -/

/-- The natural filtration of the invariant-box-valued noisy process. -/
def gaussianBasinOrbitFiltration
    {p : LoopParams} (model : DriftModelAssumptions p)
    (rho sigma : ℝ) :
    Filtration ℕ (inferInstance : MeasurableSpace GaussianNoisePath) :=
  Filtration.natural
    (fun n xi ↦ gaussianNoisyOrbitInBox model rho sigma xi n)
    (fun n ↦ (continuous_gaussianNoisyOrbitInBox
      model rho sigma n).stronglyMeasurable)

/-- The invariant-box-valued noisy recursion is adapted to its natural
filtration. -/
theorem gaussianNoisyOrbitInBox_adapted
    {p : LoopParams} (model : DriftModelAssumptions p)
    (rho sigma : ℝ) :
    Adapted (gaussianBasinOrbitFiltration model rho sigma)
      (fun n xi ↦ gaussianNoisyOrbitInBox model rho sigma xi n) := by
  unfold gaussianBasinOrbitFiltration
  exact (Filtration.stronglyAdapted_natural
    (fun n ↦ (continuous_gaussianNoisyOrbitInBox
      model rho sigma n).stronglyMeasurable)).adapted

/-- The first time the noisy state leaves the calibrated basin, with `top`
if it never leaves. -/
def gaussianBasinExitTime
    {p : LoopParams} (model : DriftModelAssumptions p)
    (_ss : SmallStepAssumption p) (_threshold : ThresholdAssumption p)
    {rho : ℝ} (_hrho : 0 ≤ rho) (sigma : ℝ) :
    GaussianNoisePath → WithTop ℕ :=
  hittingAfter
    (fun n xi ↦ gaussianNoisyOrbitInBox model rho sigma xi n)
    (civicWeightedCalibratedBasinInBox p rho)ᶜ 0

/-- Genuine basin exit is a stopping time. -/
theorem gaussianBasinExitTime_isStoppingTime
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (sigma : ℝ) :
    IsStoppingTime (gaussianBasinOrbitFiltration model rho sigma)
      (gaussianBasinExitTime model ss threshold hrho sigma) := by
  unfold gaussianBasinExitTime
  exact (gaussianNoisyOrbitInBox_adapted model rho sigma).isStoppingTime_hittingAfter
    ((civicWeightedCalibratedBasinInBox_isOpen
      model ss threshold hrho).isClosed_compl.measurableSet)

/-- Exit by a finite horizon is exactly the corresponding stopping-time
sublevel event. -/
theorem gaussianBasinExitTime_le_iff
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (sigma : ℝ)
    (xi : GaussianNoisePath) (T : ℕ) :
    gaussianBasinExitTime model ss threshold hrho sigma xi ≤
        (T : WithTop ℕ) ↔
      xi ∈ gaussianBasinExitByEvent model ss threshold hrho T sigma := by
  have hhit :
      hittingAfter
          (fun n xi ↦ gaussianNoisyOrbitInBox model rho sigma xi n)
          (civicWeightedCalibratedBasinInBox p rho)ᶜ 0 xi ≤
          (T : WithTop ℕ) ↔
        ∃ j ∈ Icc 0 T,
          gaussianNoisyOrbitInBox model rho sigma xi j ∈
            (civicWeightedCalibratedBasinInBox p rho)ᶜ :=
    hittingAfter_le_iff
  rw [gaussianBasinExitTime, hhit]
  simp only [mem_Icc, zero_le, true_and, gaussianBasinExitByEvent,
    mem_setOf_eq, mem_compl_iff, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, hexit⟩
    exact ⟨j, by omega, hexit⟩
  · rintro ⟨j, hj, hexit⟩
    exact ⟨j, by omega, hexit⟩

/-- Finite-horizon survival for the genuine basin-exit stopping time is
measurable. -/
theorem measurableSet_gaussianBasinExitTime_gt
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (T : ℕ) (sigma : ℝ) :
    MeasurableSet
      {xi | (T : WithTop ℕ) <
        gaussianBasinExitTime model ss threshold hrho sigma xi} := by
  rw [show {xi | (T : WithTop ℕ) <
        gaussianBasinExitTime model ss threshold hrho sigma xi} =
      (gaussianBasinExitByEvent model ss threshold hrho T sigma)ᶜ by
    ext xi
    simp only [mem_setOf_eq, mem_compl_iff]
    rw [← gaussianBasinExitTime_le_iff
      model ss threshold hrho sigma xi T]
    exact (not_le :
      ¬gaussianBasinExitTime model ss threshold hrho sigma xi ≤
          (T : WithTop ℕ) ↔
        (T : WithTop ℕ) <
          gaussianBasinExitTime model ss threshold hrho sigma xi).symm]
  exact (measurableSet_gaussianBasinExitByEvent
    model ss threshold hrho T sigma).compl

/-- The genuine basin-survival probability is one minus the canonical
finite-window exit probability. -/
theorem standardGaussianSequence_basinExitTime_gt
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (T : ℕ) (sigma : ℝ) :
    standardGaussianSequence
        {xi | (T : WithTop ℕ) <
          gaussianBasinExitTime model ss threshold hrho sigma xi} =
      1 - gaussianBasinExitProbability
        model ss threshold hrho T sigma := by
  rw [show {xi | (T : WithTop ℕ) <
        gaussianBasinExitTime model ss threshold hrho sigma xi} =
      (gaussianBasinExitByEvent model ss threshold hrho T sigma)ᶜ by
    ext xi
    simp only [mem_setOf_eq, mem_compl_iff]
    rw [← gaussianBasinExitTime_le_iff
      model ss threshold hrho sigma xi T]
    exact (not_le :
      ¬gaussianBasinExitTime model ss threshold hrho sigma xi ≤
          (T : WithTop ℕ) ↔
        (T : WithTop ℕ) <
          gaussianBasinExitTime model ss threshold hrho sigma xi).symm]
  rw [measure_compl
    (measurableSet_gaussianBasinExitByEvent
      model ss threshold hrho T sigma)
    (measure_ne_top standardGaussianSequence _)]
  rw [measure_univ,
    standardGaussianSequence_basinExitByEvent]

/-! ## Comparison with first saddle-policy crossing -/

/-- If genuine basin exit has occurred by `T`, saddle-policy crossing has
already occurred by `T`. -/
theorem gaussianEscapeTime_le_of_basinExitTime_le
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (sigma : ℝ) (xi : GaussianNoisePath) (T : ℕ)
    (hexit : gaussianBasinExitTime model ss threshold hrho sigma xi ≤
      (T : WithTop ℕ)) :
    gaussianEscapeTime weighted sigma xi ≤ (T : WithTop ℕ) := by
  have hexitBy := (gaussianBasinExitTime_le_iff
    model ss threshold hrho sigma xi T).mp hexit
  obtain ⟨k, hk, hexitBox⟩ := hexitBy
  have hkT : k ≤ T := by
    simp only [Finset.mem_range] at hk
    omega
  have hexitAmbient : gaussianNoisyOrbit p rho sigma xi k ∉
      civicWeightedCalibratedBasin p rho := by
    simpa only [gaussianNoisyOrbitInBox,
      mem_civicWeightedCalibratedBasinInBox_iff] using hexitBox
  have hcrossK : weighted.βdagger ≤
      policyRunningMax (gaussianNoisyOrbit p rho sigma xi) k :=
    (gaussianNoisyOrbit_isControlled p rho sigma xi).exit_forces_runningMax_ge
      model ss threshold hrho hcoop weighted hexitAmbient
  have hcrossT : weighted.βdagger ≤
      policyRunningMax (gaussianNoisyOrbit p rho sigma xi) T :=
    hcrossK.trans ((monotone_runningMax
      (fun n ↦ (gaussianNoisyOrbit p rho sigma xi n).1)) hkT)
  exact (gaussianEscapeTime_le_iff weighted sigma xi T).2 hcrossT

/-- First saddle-policy crossing occurs no later than genuine basin exit on
every noise history. -/
theorem gaussianEscapeTime_le_gaussianBasinExitTime
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (sigma : ℝ) (xi : GaussianNoisePath) :
    gaussianEscapeTime weighted sigma xi ≤
      gaussianBasinExitTime model ss threshold hrho sigma xi := by
  by_cases htop :
      gaussianBasinExitTime model ss threshold hrho sigma xi = ⊤
  · rw [htop]
    exact le_top
  · obtain ⟨T, hT⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hT]
    exact gaussianEscapeTime_le_of_basinExitTime_le
      model ss threshold hrho hcoop weighted sigma xi T (by
        rw [← hT]
        exact le_rfl)

/-! ## Exact finite-action barrier -/

/-- Every finite history which genuinely exits by its terminal horizon pays
at least the basin-exit quasipotential `V`. -/
theorem civicQuasipotential_le_gaussianVectorAction_of_terminal_basinExit
    {p : LoopParams} (_model : DriftModelAssumptions p)
    {rho : ℝ} {T : ℕ} {u : Fin T → ℝ}
    (hexit : finiteControlledOrbit p rho u T ∉
      civicWeightedCalibratedBasin p rho) :
    civicQuasipotential p rho ≤ gaussianVectorAction u := by
  let path := finiteControlledOrbit_isControlled p rho u
  have hbarrier := civicQuasipotential_le_controlAction path hexit
  simpa only [controlAction_extendFiniteControl] using hbarrier

/-- The same exact barrier holds when exit occurs at any time up to the
finite horizon. -/
theorem civicQuasipotential_le_gaussianVectorAction_of_basinExit
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho : ℝ} {T : ℕ} {u : Fin T → ℝ}
    (hexit : ∃ k ∈ Finset.range (T + 1),
      finiteControlledOrbitInBox model rho u k ∉
        civicWeightedCalibratedBasinInBox p rho) :
    civicQuasipotential p rho ≤ gaussianVectorAction u := by
  obtain ⟨k, hk, hexit⟩ := hexit
  have hkT : k ≤ T := by
    simp only [Finset.mem_range] at hk
    omega
  let w := extendFiniteControl u
  let x := finiteControlledOrbit p rho u
  have hpath : IsControlledCivicWeightedPath p rho w x :=
    finiteControlledOrbit_isControlled p rho u
  have hexitAmbient : x k ∉ civicWeightedCalibratedBasin p rho := by
    simpa only [x, finiteControlledOrbitInBox,
      mem_civicWeightedCalibratedBasinInBox_iff] using hexit
  have hprefix : civicQuasipotential p rho ≤ controlAction w k :=
    civicQuasipotential_le_controlAction hpath hexitAmbient
  calc
    civicQuasipotential p rho ≤ controlAction w k := hprefix
    _ ≤ controlAction w T := controlAction_mono hkT
    _ = gaussianVectorAction u := by
      simpa only [w] using controlAction_extendFiniteControl u

/-- On the finite Gaussian exit event, scaled noise action is at least `V`.
This is an exact pathwise statement, with no asymptotic notation. -/
theorem civicQuasipotential_le_scaledGaussianAction_of_mem_basinExitEvent
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) {T : ℕ} {sigma : ℝ}
    {xi : Fin T → ℝ}
    (hxi : xi ∈ gaussianBasinExitEvent
      model ss threshold hrho T sigma) :
    civicQuasipotential p rho ≤
      sigma ^ 2 * gaussianVectorAction xi := by
  have hbarrier := civicQuasipotential_le_gaussianVectorAction_of_basinExit
    model hxi
  rw [gaussianVectorAction_scaledGaussianControl] at hbarrier
  exact hbarrier

/-- A fixed-horizon basin-exit event is contained in the radial Gaussian
action tail at threshold `V / sigma^2`. -/
theorem gaussianBasinExitEvent_subset_actionTail
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (T : ℕ) {sigma : ℝ}
    (hsigma : sigma ≠ 0) :
    gaussianBasinExitEvent model ss threshold hrho T sigma ⊆
      gaussianActionTailEvent T
        (civicQuasipotential p rho / sigma ^ 2) := by
  intro xi hxi
  have hbarrier :=
    civicQuasipotential_le_scaledGaussianAction_of_mem_basinExitEvent
      model ss threshold hrho hxi
  change civicQuasipotential p rho / sigma ^ 2 ≤ gaussianVectorAction xi
  rw [div_le_iff₀ (sq_pos_of_ne_zero hsigma)]
  nlinarith

/-- The fixed-horizon genuine-exit probability is bounded by the
corresponding action-tail probability. -/
theorem gaussianBasinExitProbability_le_actionTail
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (T : ℕ) {sigma : ℝ}
    (hsigma : sigma ≠ 0) :
    gaussianBasinExitProbability model ss threshold hrho T sigma ≤
      gaussianActionTailProbability T
        (civicQuasipotential p rho / sigma ^ 2) := by
  exact measure_mono
    (gaussianBasinExitEvent_subset_actionTail
      model ss threshold hrho T hsigma)

/-- An explicit fixed-horizon Chernoff bound with the exact basin-exit
barrier in its exponential term. -/
theorem gaussianBasinExitProbability_le_chernoff
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (T : ℕ) {sigma t : ℝ}
    (hsigma : sigma ≠ 0) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    gaussianBasinExitProbability model ss threshold hrho T sigma ≤
      ENNReal.ofReal
        (Real.exp (-t * (civicQuasipotential p rho / sigma ^ 2)) *
          gaussianHalfSquareMgf t ^ T) := by
  exact (gaussianBasinExitProbability_le_actionTail
    model ss threshold hrho T hsigma).trans
      (gaussianActionTailProbability_le_chernoff T ht0 ht1)

/-- At a fixed Chernoff parameter, the finite-horizon logarithmic exit rate
has exact barrier term `-t V`; the dimension enters only through the displayed
finite Gaussian moment. -/
theorem gaussianBasinExitLogRate_le_chernoff
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) {T : ℕ} {sigma t : ℝ}
    (hsigma : sigma ≠ 0) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    gaussianBasinExitLogRate model ss threshold hrho T sigma ≤
      ((-t * civicQuasipotential p rho +
        sigma ^ 2 * Real.log (gaussianHalfSquareMgf t ^ T) : ℝ) : EReal) := by
  let B : ℝ := civicQuasipotential p rho
  let C : ℝ := gaussianHalfSquareMgf t ^ T
  have hCpos : 0 < C := by
    exact pow_pos (gaussianHalfSquareMgf_pos ht1) T
  have hprob := gaussianBasinExitProbability_le_chernoff
    model ss threshold hrho T hsigma ht0 ht1
  change gaussianBasinExitProbability model ss threshold hrho T sigma ≤
      ENNReal.ofReal (Real.exp (-t * (B / sigma ^ 2)) * C) at hprob
  have hlog :
      ENNReal.log
          (gaussianBasinExitProbability model ss threshold hrho T sigma) ≤
        ENNReal.log
          (ENNReal.ofReal (Real.exp (-t * (B / sigma ^ 2)) * C)) :=
    ENNReal.logOrderIso.monotone hprob
  have hrhs : ENNReal.log
      (ENNReal.ofReal (Real.exp (-t * (B / sigma ^ 2)) * C)) =
      ((-t * (B / sigma ^ 2) + Real.log C : ℝ) : EReal) := by
    rw [ENNReal.log_ofReal_of_pos (mul_pos (Real.exp_pos _) hCpos)]
    norm_cast
    rw [Real.log_mul (Real.exp_pos _).ne' hCpos.ne', Real.log_exp]
  have hmul := mul_le_mul_of_nonneg_left hlog
    (show (0 : EReal) ≤ (sigma ^ 2 : ℝ) by
      exact_mod_cast sq_nonneg sigma)
  rw [hrhs] at hmul
  change gaussianBasinExitLogRate model ss threshold hrho T sigma ≤
    ((sigma ^ 2 : ℝ) : EReal) *
      ((-t * (B / sigma ^ 2) + Real.log C : ℝ) : EReal) at hmul
  have heq : ((sigma ^ 2 : ℝ) : EReal) *
        ((-t * (B / sigma ^ 2) + Real.log C : ℝ) : EReal) =
      ((-t * B + sigma ^ 2 * Real.log C : ℝ) : EReal) := by
    norm_cast
    field_simp [hsigma]
  simpa only [B, C] using hmul.trans_eq heq

/-- At every fixed horizon, the finite Gaussian moment vanishes on the
small-noise logarithmic scale at a fixed Chernoff parameter. -/
theorem limsup_gaussianBasinExitLogRate_le_chernoffParameter
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (T : ℕ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    limsup (fun sigma : ℝ ↦
        gaussianBasinExitLogRate model ss threshold hrho T sigma)
        (nhdsWithin 0 (Ioi (0 : ℝ))) ≤
      ((-t * civicQuasipotential p rho : ℝ) : EReal) := by
  let C : ℝ := Real.log (gaussianHalfSquareMgf t ^ T)
  let B : ℝ := civicQuasipotential p rho
  have hpointwise : ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      gaussianBasinExitLogRate model ss threshold hrho T sigma ≤
        ((-t * B + sigma ^ 2 * C : ℝ) : EReal) := by
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    simpa only [B, C] using gaussianBasinExitLogRate_le_chernoff
      (T := T) model ss threshold hrho hsigma.ne' ht0 ht1
  have hreal : Tendsto (fun sigma : ℝ ↦ -t * B + sigma ^ 2 * C)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds (-t * B)) := by
    have hcont : ContinuousAt
        (fun sigma : ℝ ↦ -t * B + sigma ^ 2 * C) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hereal : Tendsto
      (fun sigma : ℝ ↦ ((-t * B + sigma ^ 2 * C : ℝ) : EReal))
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds (((-t * B : ℝ) : EReal))) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hreal
  exact (limsup_le_limsup hpointwise).trans_eq (by
    simpa only [B] using hereal.limsup_eq)

/-- The fixed-horizon logarithmic upper rate for genuine basin exit is at
most the negative basin quasipotential. -/
theorem gaussianBasinExitLogRate_limsup_le_quasipotential
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (T : ℕ) :
    limsup (fun sigma : ℝ ↦
        gaussianBasinExitLogRate model ss threshold hrho T sigma)
        (nhdsWithin 0 (Ioi (0 : ℝ))) ≤
      ((-civicQuasipotential p rho : ℝ) : EReal) := by
  let B : ℝ := civicQuasipotential p rho
  let R : EReal := limsup (fun sigma : ℝ ↦
    gaussianBasinExitLogRate model ss threshold hrho T sigma)
    (nhdsWithin 0 (Ioi (0 : ℝ)))
  let t : ℕ → ℝ := fun n ↦ 1 - 1 / (n + 1 : ℝ)
  have hparameter : ∀ n, R ≤ ((-t n * B : ℝ) : EReal) := by
    intro n
    have hdenPos : 0 < (n + 1 : ℝ) := by positivity
    have hdenOne : (1 : ℝ) ≤ n + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have ht0 : 0 ≤ t n := by
      dsimp only [t]
      have := (div_le_one hdenPos).2 hdenOne
      linarith
    have ht1 : t n < 1 := by
      dsimp only [t]
      have : 0 < 1 / (n + 1 : ℝ) := div_pos one_pos hdenPos
      linarith
    simpa only [R, B] using
      limsup_gaussianBasinExitLogRate_le_chernoffParameter
        model ss threshold hrho T ht0 ht1
  have htendsto : Tendsto t atTop (nhds (1 : ℝ)) := by
    have hinv : Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) atTop
        (nhds (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [t, sub_zero] using tendsto_const_nhds.sub hinv
  have hreal : Tendsto (fun n ↦ -t n * B) atTop (nhds (-B)) := by
    simpa using htendsto.neg.mul_const B
  have hereal : Tendsto (fun n ↦ ((-t n * B : ℝ) : EReal)) atTop
      (nhds (((-B : ℝ) : EReal))) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hreal
  have hclosed : ((-B : ℝ) : EReal) ∈ Ici R :=
    isClosed_Ici.mem_of_tendsto hereal (Eventually.of_forall hparameter)
  simpa only [R, B, mem_Ici] using hclosed

/-- The extended mean of the genuine basin-exit stopping time. -/
def meanGaussianBasinExitTime
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (sigma : ℝ) : ℝ≥0∞ :=
  ∫⁻ xi, ENat.toENNReal
    (show ℕ∞ from gaussianBasinExitTime
      model ss threshold hrho sigma xi)
    ∂standardGaussianSequence

/-- Exact tail-sum representation of the genuine mean basin-exit time. -/
theorem meanGaussianBasinExitTime_eq_tsum_survival
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (sigma : ℝ) :
    meanGaussianBasinExitTime model ss threshold hrho sigma =
      ∑' T : ℕ,
        (1 - gaussianBasinExitProbability
          model ss threshold hrho T sigma) := by
  have hindicator : ∀ T : ℕ,
      (fun xi : GaussianNoisePath ↦
        if (T : ℕ∞) <
            (show ℕ∞ from gaussianBasinExitTime
              model ss threshold hrho sigma xi)
          then (1 : ℝ≥0∞) else 0) =
        {xi | (T : WithTop ℕ) <
          gaussianBasinExitTime model ss threshold hrho sigma xi}.indicator
            (fun _ ↦ 1) := by
    intro T
    funext xi
    by_cases hxi : (T : WithTop ℕ) <
        gaussianBasinExitTime model ss threshold hrho sigma xi
    · have hxi' : (T : ℕ∞) <
          (show ℕ∞ from gaussianBasinExitTime
            model ss threshold hrho sigma xi) := hxi
      rw [if_pos hxi']
      have hmem : xi ∈ {xi : GaussianNoisePath |
          (T : WithTop ℕ) <
            gaussianBasinExitTime model ss threshold hrho sigma xi} := hxi
      exact (indicator_of_mem hmem (fun _ ↦ (1 : ℝ≥0∞))).symm
    · have hxi' : ¬(T : ℕ∞) <
          (show ℕ∞ from gaussianBasinExitTime
            model ss threshold hrho sigma xi) := hxi
      rw [if_neg hxi']
      have hmem : xi ∉ {xi : GaussianNoisePath |
          (T : WithTop ℕ) <
            gaussianBasinExitTime model ss threshold hrho sigma xi} := hxi
      exact (indicator_of_notMem hmem
        (fun _ ↦ (1 : ℝ≥0∞))).symm
  rw [meanGaussianBasinExitTime]
  conv_lhs =>
    enter [2, xi]
    rw [enatToENNReal_eq_tsum_lt]
  rw [lintegral_tsum]
  · congr 1
    funext T
    rw [hindicator T]
    rw [lintegral_indicator_const
      (measurableSet_gaussianBasinExitTime_gt
        model ss threshold hrho T sigma)]
    rw [one_mul,
      standardGaussianSequence_basinExitTime_gt]
  · intro T
    rw [hindicator T]
    exact (measurable_const.indicator
      (measurableSet_gaussianBasinExitTime_gt
        model ss threshold hrho T sigma)).aemeasurable

/-- A pointwise majorant of genuine basin-survival probabilities bounds the
mean basin-exit time. -/
theorem meanGaussianBasinExitTime_le_tsum_of_survival_le
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (sigma : ℝ)
    (majorant : ℕ → ℝ≥0∞)
    (hmajorant : ∀ T,
      1 - gaussianBasinExitProbability
          model ss threshold hrho T sigma ≤ majorant T) :
    meanGaussianBasinExitTime model ss threshold hrho sigma ≤
      ∑' T, majorant T := by
  rw [meanGaussianBasinExitTime_eq_tsum_survival]
  exact ENNReal.tsum_le_tsum hmajorant

/-- A uniform one-block genuine-exit floor bounds the full mean exit time by
the block length times the inverse floor. -/
theorem meanGaussianBasinExitTime_le_block_mul_inv
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (T : ℕ) (hT : 0 < T) (sigma : ℝ) (q : ℝ≥0∞)
    (hq : ∀ x : LoopBox p, calibratedPointInBox p model ≤ x →
      q ≤ gaussianBasinExitProbabilityFromInBox
        model ss threshold hrho x T sigma) :
    meanGaussianBasinExitTime model ss threshold hrho sigma ≤
      (T : ℝ≥0∞) * q⁻¹ := by
  have hsurvival : ∀ n : ℕ,
      1 - gaussianBasinExitProbability
          model ss threshold hrho n sigma ≤
        (1 - q) ^ (n / T) := by
    intro n
    have hblock : n / T * T ≤ n := Nat.div_mul_le_self n T
    have hanti :
        1 - gaussianBasinExitProbability
            model ss threshold hrho n sigma ≤
          1 - gaussianBasinExitProbability
            model ss threshold hrho (n / T * T) sigma :=
      tsub_le_tsub_left
        (monotone_gaussianBasinExitProbability
          model ss threshold hrho sigma hblock) 1
    exact hanti.trans
      (one_sub_gaussianBasinExitProbability_mul_le_pow
        model ss threshold hrho T sigma q hq (n / T))
  have hqOne : q ≤ 1 := by
    have hprob := hq (calibratedPointInBox p model) le_rfl
    letI : IsProbabilityMeasure (standardGaussianVector T) := by
      unfold standardGaussianVector
      infer_instance
    exact hprob.trans prob_le_one
  calc
    meanGaussianBasinExitTime model ss threshold hrho sigma ≤
        ∑' n : ℕ, (1 - q) ^ (n / T) :=
      meanGaussianBasinExitTime_le_tsum_of_survival_le
        model ss threshold hrho sigma
          (fun n ↦ (1 - q) ^ (n / T)) hsurvival
    _ = (T : ℝ≥0∞) * (1 - (1 - q))⁻¹ :=
      tsum_pow_nat_div T hT (1 - q)
    _ = (T : ℝ≥0∞) * q⁻¹ := by
      rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top hqOne]

/-- A single finite terminal-exit control gives an explicit independent
upper bound for the genuine mean basin-exit time. -/
theorem meanGaussianBasinExitTime_le_terminal_control
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    {T : ℕ} (hT : 0 < T) (u : Fin T → ℝ)
    (hexit : finiteControlledOrbit p rho u T ∉
      civicWeightedCalibratedBasin p rho)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    meanGaussianBasinExitTime model ss threshold hrho sigma ≤
      (T : ℝ≥0∞) *
        (ENNReal.ofReal
          (∏ i, gaussianCoordinateLowerBound (u i) sigma))⁻¹ := by
  apply meanGaussianBasinExitTime_le_block_mul_inv
    model ss threshold hrho T hT sigma
  intro x hx
  exact (gaussianControlBox_probability_lower u hsigma).trans
    (gaussianControlBox_probability_le_basinExitProbabilityFromInBox
      model ss threshold hrho hcoop u hexit hx hsigma)

/-- The logarithmic small-noise scale of the genuine mean basin-exit time. -/
def meanGaussianBasinExitLogRate
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (sigma : ℝ) : EReal :=
  (sigma ^ 2 : ℝ) * ENNReal.log
    (meanGaussianBasinExitTime model ss threshold hrho sigma)

/-- The genuine mean-exit logarithmic rate is bounded above by the action of
any single finite terminal-exit control. -/
theorem meanGaussianBasinExitLogRate_limsup_le_terminal_control
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    {T : ℕ} (hT : 0 < T) (u : Fin T → ℝ)
    (hexit : finiteControlledOrbit p rho u T ∉
      civicWeightedCalibratedBasin p rho) :
    limsup
        (meanGaussianBasinExitLogRate model ss threshold hrho)
        (nhdsWithin 0 (Ioi (0 : ℝ))) ≤
      ((gaussianVectorAction u : ℝ) : EReal) := by
  have hTReal : 0 < (T : ℝ) := by
    exact_mod_cast hT
  have hlogT : ENNReal.log (T : ℝ≥0∞) =
      ((Real.log (T : ℝ) : ℝ) : EReal) := by
    rw [← ENNReal.ofReal_natCast T,
      ENNReal.log_ofReal_of_pos hTReal]
  have hpointwise : ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      meanGaussianBasinExitLogRate model ss threshold hrho sigma ≤
        ((sigma ^ 2 * Real.log (T : ℝ) -
          gaussianControlBoxExplicitRate u sigma : ℝ) : EReal) := by
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    have hmean := meanGaussianBasinExitTime_le_terminal_control
      model ss threshold hrho hcoop hT u hexit hsigma
    have hlog := ENNReal.logOrderIso.monotone hmean
    have hmul := mul_le_mul_of_nonneg_left hlog
      (show (0 : EReal) ≤ (sigma ^ 2 : ℝ) by
        exact_mod_cast sq_nonneg sigma)
    have hprodPos : 0 < ∏ i, gaussianCoordinateLowerBound (u i) sigma :=
      Finset.prod_pos fun i _ ↦
        gaussianCoordinateLowerBound_pos (u i)
    calc
      meanGaussianBasinExitLogRate model ss threshold hrho sigma ≤
          (sigma ^ 2 : ℝ) * ENNReal.log
            ((T : ℝ≥0∞) *
              (ENNReal.ofReal
                (∏ i, gaussianCoordinateLowerBound (u i) sigma))⁻¹) := hmul
      _ = (sigma ^ 2 : ℝ) * ENNReal.log (T : ℝ≥0∞) -
            ((gaussianControlBoxExplicitRate u sigma : ℝ) : EReal) := by
        rw [ENNReal.log_mul_add, ENNReal.log_inv,
          ENNReal.log_ofReal_of_pos hprodPos, hlogT]
        unfold gaussianControlBoxExplicitRate
        norm_cast
        ring
      _ = ((sigma ^ 2 * Real.log (T : ℝ) -
          gaussianControlBoxExplicitRate u sigma : ℝ) : EReal) := by
        rw [hlogT]
        norm_cast
  have hzero : Tendsto
      (fun sigma : ℝ ↦ sigma ^ 2 * Real.log (T : ℝ))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
    have hcont : ContinuousAt
        (fun sigma : ℝ ↦ sigma ^ 2 * Real.log (T : ℝ)) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hreal : Tendsto
      (fun sigma : ℝ ↦ sigma ^ 2 * Real.log (T : ℝ) -
        gaussianControlBoxExplicitRate u sigma)
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds (gaussianVectorAction u)) := by
    have hsub := hzero.sub (gaussianControlBoxExplicitRate_tendsto u)
    simpa only [zero_sub, neg_neg] using hsub
  have hmajor : Tendsto
      (fun sigma : ℝ ↦
        ((sigma ^ 2 * Real.log (T : ℝ) -
          gaussianControlBoxExplicitRate u sigma : ℝ) : EReal))
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds ((gaussianVectorAction u : ℝ) : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hreal
  exact (limsup_le_limsup hpointwise).trans_eq hmajor.limsup_eq

/-- For every positive tolerance, the genuine mean basin-exit exponent is at
most `V + delta`. -/
theorem meanGaussianBasinExitLogRate_limsup_le_add
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    {delta : ℝ} (hdelta : 0 < delta) :
    limsup
        (meanGaussianBasinExitLogRate model ss threshold hrho)
        (nhdsWithin 0 (Ioi (0 : ℝ))) ≤
      ((civicQuasipotential p rho + delta : ℝ) : EReal) := by
  have hnonempty := quasipotentialActionSet_nonempty
    model ss hrho hrhoCure
  have hinfLt : sInf (quasipotentialActionSet p rho) <
      civicQuasipotential p rho + delta := by
    rw [← civicQuasipotential]
    linarith
  obtain ⟨a, ha, haLt⟩ := exists_lt_of_csInf_lt hnonempty hinfLt
  rcases ha with ⟨T, u, x, path, hexit, rfl⟩
  let v : Fin T → ℝ := fun i ↦ u i
  have horbit : finiteControlledOrbit p rho v T = x T :=
    finiteControlledOrbit_restrict_eq path le_rfl
  have hexitFinite : finiteControlledOrbit p rho v T ∉
      civicWeightedCalibratedBasin p rho := by
    rwa [horbit]
  have hT : 0 < T := by
    by_contra hnot
    have hzero : T = 0 := Nat.eq_zero_of_not_pos hnot
    subst T
    apply hexitFinite
    simpa only [finiteControlledOrbit] using
      (calibratedPoint_mem_civicWeightedCalibratedBasin
        model threshold hrho)
  have hrate := meanGaussianBasinExitLogRate_limsup_le_terminal_control
    model ss threshold hrho hcoop hT v hexitFinite
  have haction : gaussianVectorAction v = controlAction u T :=
    gaussianVectorAction_restrict u T
  apply hrate.trans
  exact_mod_cast (show gaussianVectorAction v ≤
      civicQuasipotential p rho + delta by
    rw [haction]
    exact haLt.le)

/-- The independent restart construction proves the full genuine mean-exit
upper Arrhenius bound at the literal finite-exit quasipotential `V`. -/
theorem meanGaussianBasinExitLogRate_limsup_le_quasipotential
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c)) :
    limsup
        (meanGaussianBasinExitLogRate model ss threshold hrho)
        (nhdsWithin 0 (Ioi (0 : ℝ))) ≤
      ((civicQuasipotential p rho : ℝ) : EReal) := by
  let R : EReal := limsup
    (meanGaussianBasinExitLogRate model ss threshold hrho)
    (nhdsWithin 0 (Ioi (0 : ℝ)))
  let b : ℕ → ℝ := fun n ↦
    civicQuasipotential p rho + 1 / (n + 1 : ℝ)
  have hparameter : ∀ n, R ≤ ((b n : ℝ) : EReal) := by
    intro n
    have hdenPos : 0 < (n + 1 : ℝ) := by positivity
    simpa only [R, b] using
      meanGaussianBasinExitLogRate_limsup_le_add
        model ss threshold hrho hrhoCure hcoop
          (delta := 1 / (n + 1 : ℝ)) (div_pos one_pos hdenPos)
  have hinv : Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) atTop
      (nhds (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hreal : Tendsto b atTop
      (nhds (civicQuasipotential p rho)) := by
    simpa only [b, add_zero] using
      tendsto_const_nhds.add hinv
  have hereal : Tendsto (fun n ↦ ((b n : ℝ) : EReal)) atTop
      (nhds ((civicQuasipotential p rho : ℝ) : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hreal
  have hclosed : ((civicQuasipotential p rho : ℝ) : EReal) ∈ Ici R :=
    isClosed_Ici.mem_of_tendsto hereal
      (Eventually.of_forall hparameter)
  simpa only [R, mem_Ici] using hclosed

/-- The genuine mean basin-exit time is at least the mean first-crossing
time. -/
theorem meanGaussianEscapeTime_le_meanGaussianBasinExitTime
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho) (sigma : ℝ) :
    meanGaussianEscapeTime weighted sigma ≤
      meanGaussianBasinExitTime model ss threshold hrho sigma := by
  unfold meanGaussianEscapeTime gaussianEscapeTimeENNReal
    meanGaussianBasinExitTime
  apply lintegral_mono
  intro xi
  exact ENat.toENNReal_mono
    (gaussianEscapeTime_le_gaussianBasinExitTime
      model ss threshold hrho hcoop weighted sigma xi)

/-- Pointwise, the logarithmic genuine mean-exit scale dominates the
logarithmic mean first-crossing scale. -/
theorem meanGaussianEscapeLogRate_le_meanGaussianBasinExitLogRate
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho) (sigma : ℝ) :
    meanGaussianEscapeLogRate weighted sigma ≤
      meanGaussianBasinExitLogRate model ss threshold hrho sigma := by
  have hmean := meanGaussianEscapeTime_le_meanGaussianBasinExitTime
    model ss threshold hrho hcoop weighted sigma
  have hlog := ENNReal.logOrderIso.monotone hmean
  change ENNReal.log (meanGaussianEscapeTime weighted sigma) ≤
    ENNReal.log
      (meanGaussianBasinExitTime model ss threshold hrho sigma) at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog
    (show (0 : EReal) ≤ (sigma ^ 2 : ℝ) by
      exact_mod_cast sq_nonneg sigma)
  simpa only [meanGaussianEscapeLogRate,
    meanGaussianBasinExitLogRate] using hmul

/-- The genuine mean basin-exit logarithmic rate has liminf at least the
crossing quasipotential.  This is the strongest mean-rate consequence of the
current comparison theorem; it does not replace the right-hand side by `V`. -/
theorem crossingQuasipotential_le_liminf_meanGaussianBasinExitLogRate
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho L : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    ((civicCrossingQuasipotential weighted : ℝ) : EReal) ≤
      liminf
        (meanGaussianBasinExitLogRate model ss threshold hrho)
        (nhdsWithin 0 (Ioi (0 : ℝ))) := by
  exact (crossingLowerMeanRate model ss threshold hrho hcoop weighted hL).trans
    (liminf_le_liminf (Eventually.of_forall fun sigma ↦
      meanGaussianEscapeLogRate_le_meanGaussianBasinExitLogRate
        model ss threshold hrho hcoop weighted sigma))

#print axioms civicWeightedCalibratedBasinInBox_isOpen
#print axioms measurableSet_gaussianBasinExitEvent
#print axioms measurableSet_gaussianBasinExitByEvent
#print axioms gaussianBasinExitTime_isStoppingTime
#print axioms gaussianBasinExitTime_le_iff
#print axioms gaussianEscapeTime_le_gaussianBasinExitTime
#print axioms civicQuasipotential_le_gaussianVectorAction_of_terminal_basinExit
#print axioms civicQuasipotential_le_gaussianVectorAction_of_basinExit
#print axioms civicQuasipotential_le_scaledGaussianAction_of_mem_basinExitEvent
#print axioms gaussianBasinExitProbability_le_chernoff
#print axioms gaussianBasinExitLogRate_limsup_le_quasipotential
#print axioms gaussianBasinSurvivalProbabilityFromInBox_add_le
#print axioms gaussianBasinSurvivalProbabilityFromInBox_mul_le_pow
#print axioms gaussianPrefix_preimage_basinExitEvent
#print axioms standardGaussianSequence_basinExitByEvent
#print axioms meanGaussianBasinExitTime_eq_tsum_survival
#print axioms meanGaussianBasinExitTime_le_terminal_control
#print axioms meanGaussianBasinExitLogRate_limsup_le_terminal_control
#print axioms meanGaussianBasinExitLogRate_limsup_le_quasipotential
#print axioms meanGaussianEscapeTime_le_meanGaussianBasinExitTime
#print axioms meanGaussianEscapeLogRate_le_meanGaussianBasinExitLogRate
#print axioms crossingQuasipotential_le_liminf_meanGaussianBasinExitLogRate

end

end CivicAlignment.PaperII
