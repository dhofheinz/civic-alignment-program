/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.Quasipotential
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic

/-!
# Paper II: fixed-horizon Gaussian saddle-crossing windows

This file formalizes `prop:arrwindow`.  Finite noise histories are distributed
under a product of standard real Gaussians.  Logarithmic probability rates use
`ENNReal.log : ℝ≥0∞ → EReal`, whose value at zero is `⊥`; this is the correct
extended-real convention for large-deviation bounds.

The legacy `Escape` declaration names in this module denote first passage of
the policy running maximum through the weighted saddle. They do not denote
exit from the calibrated basin.
-/

namespace CivicAlignment.PaperII

open Filter Function MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal Interval

noncomputable section

/-! ## Finite Gaussian noise histories -/

/-- The law of `T` independent standard real Gaussian coordinates. -/
def standardGaussianVector (T : ℕ) : Measure (Fin T → ℝ) :=
  Measure.pi fun _ : Fin T ↦ gaussianReal 0 1

/-- Half the squared Euclidean norm, matching the finite control action. -/
def gaussianVectorAction {T : ℕ} (ξ : Fin T → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, (ξ i) ^ 2

/-- Extend a finite control history by zero after its horizon. -/
def extendFiniteControl {T : ℕ} (u : Fin T → ℝ) (n : ℕ) : ℝ :=
  if h : n < T then u ⟨n, h⟩ else 0

/-- The exact controlled civic-weighted orbit driven by a finite history,
continued with zero control after the horizon. -/
def finiteControlledOrbit (p : LoopParams) (ρ : ℝ) {T : ℕ}
    (u : Fin T → ℝ) : ℕ → LoopState
  | 0 => calibratedPoint p
  | n + 1 => controlledCivicWeightedStep p ρ (extendFiniteControl u n)
      (finiteControlledOrbit p ρ u n)

/-- Scale a standard Gaussian history into the gradient controls `σξ_t`. -/
def scaledGaussianControl {T : ℕ} (σ : ℝ) (ξ : Fin T → ℝ) : Fin T → ℝ :=
  fun i ↦ σ * ξ i

/-- The finite-horizon crossing event in `prop:arrwindow`: by time `T`, the
policy running maximum has reached the civic-weighted saddle. -/
def gaussianEscapeEvent {p : LoopParams} {ρ : ℝ}
    (weighted : WeightedThresholdAssumption p ρ) (T : ℕ) (σ : ℝ) :
    Set (Fin T → ℝ) :=
  {ξ | weighted.βdagger ≤
    policyRunningMax (finiteControlledOrbit p ρ (scaledGaussianControl σ ξ)) T}

/-- The saddle-crossing probability under `T` independent standard Gaussian draws. -/
def gaussianEscapeProbability {p : LoopParams} {ρ : ℝ}
    (weighted : WeightedThresholdAssumption p ρ) (T : ℕ) (σ : ℝ) : ℝ≥0∞ :=
  standardGaussianVector T (gaussianEscapeEvent weighted T σ)

/-- The extended-real logarithmic rate `σ² log P`, with `log 0 = -∞`. -/
def gaussianEscapeLogRate {p : LoopParams} {ρ : ℝ}
    (weighted : WeightedThresholdAssumption p ρ) (T : ℕ) (σ : ℝ) : EReal :=
  (σ ^ 2 : ℝ) * ENNReal.log (gaussianEscapeProbability weighted T σ)

/-- The robust subset of the crossing event whose unforced continuation from
the finite horizon converges to the captured corner. -/
def gaussianCapturingEscapeEvent {p : LoopParams} {ρ : ℝ}
    (weighted : WeightedThresholdAssumption p ρ) (T : ℕ) (σ : ℝ) :
    Set (Fin T → ℝ) :=
  {ξ | ξ ∈ gaussianEscapeEvent weighted T σ ∧
    Tendsto
      (fun k ↦ finiteControlledOrbit p ρ (scaledGaussianControl σ ξ) (T + k))
      atTop (nhds (capturedPoint p))}

/-- Probability of a saddle crossing whose unforced continuation captures. -/
def gaussianCapturingEscapeProbability {p : LoopParams} {ρ : ℝ}
    (weighted : WeightedThresholdAssumption p ρ) (T : ℕ) (σ : ℝ) : ℝ≥0∞ :=
  standardGaussianVector T (gaussianCapturingEscapeEvent weighted T σ)

/-- Extended-real logarithmic rate of robust capturing crossings. -/
def gaussianCapturingEscapeLogRate {p : LoopParams} {ρ : ℝ}
    (weighted : WeightedThresholdAssumption p ρ) (T : ℕ) (σ : ℝ) : EReal :=
  (σ ^ 2 : ℝ) * ENNReal.log
    (gaussianCapturingEscapeProbability weighted T σ)

/-! ## Deterministic pathwise bridge -/

@[simp]
theorem extendFiniteControl_apply {T : ℕ} (u : Fin T → ℝ)
    (n : Fin T) : extendFiniteControl u n = u n := by
  simp only [extendFiniteControl, n.isLt, dite_true]

/-- The recursively defined finite-history orbit is an exact controlled path. -/
theorem finiteControlledOrbit_isControlled
    (p : LoopParams) (ρ : ℝ) {T : ℕ} (u : Fin T → ℝ) :
    IsControlledCivicWeightedPath p ρ (extendFiniteControl u)
      (finiteControlledOrbit p ρ u) where
  initial := rfl
  step _ := rfl

/-- The sequence action through the finite horizon is the vector action. -/
theorem controlAction_extendFiniteControl {T : ℕ} (u : Fin T → ℝ) :
    controlAction (extendFiniteControl u) T = gaussianVectorAction u := by
  simp only [controlAction, gaussianVectorAction]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [extendFiniteControl_apply]

/-- Scaling a finite Gaussian vector by `σ` scales its action by `σ²`. -/
theorem controlAction_scaledGaussianControl {T : ℕ} (σ : ℝ)
    (ξ : Fin T → ℝ) :
    controlAction (extendFiniteControl (scaledGaussianControl σ ξ)) T =
      σ ^ 2 * gaussianVectorAction ξ := by
  rw [controlAction_extendFiniteControl]
  simp only [gaussianVectorAction, scaledGaussianControl, mul_pow,
    ← Finset.mul_sum]
  ring

/-- A crossing path's capped running maxima partition the complete barrier
interval.  This is the crossing-event form of the Riemann comparison used in
`prop:qpbounds`; it does not assume that the terminal point has already left
the basin. -/
theorem IsControlledCivicWeightedPath.barrier_integral_le_partition_of_crossing
    {p : LoopParams} {ρ L : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p)
    (weighted : WeightedThresholdAssumption p ρ)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p ρ) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPath p ρ u x) {N : ℕ}
    (hcross : weighted.βdagger ≤ policyRunningMax x N) :
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
    cappedRunningMax_eq_target hcross
  have hcells :
      ∑ n ∈ Finset.range N, ∫ z in b n..b (n + 1), f z ≤
        ∑ n ∈ Finset.range N,
          (f (b n) * (b (n + 1) - b n) +
            (L / 2) * (b (n + 1) - b n) ^ 2) := by
    apply Finset.sum_le_sum
    intro n hn
    exact integral_le_left_rectangle_add_lipschitz hcont hL
      (hbmem n) (hbmem (n + 1)) (hbmono n)
  change (∫ z in (0 : ℝ)..weighted.βdagger, f z) ≤ _
  calc
    (∫ z in (0 : ℝ)..weighted.βdagger, f z) =
        ∑ n ∈ Finset.range N, ∫ z in b n..b (n + 1), f z := by
      rw [hadjacent, hstart, hend]
    _ ≤ ∑ n ∈ Finset.range N,
        (f (b n) * (b (n + 1) - b n) +
          (L / 2) * (b (n + 1) - b n) ^ 2) := hcells
    _ = (∑ n ∈ Finset.range N,
          f (b n) * (b (n + 1) - b n)) +
        (L / 2) * ∑ n ∈ Finset.range N,
          (b (n + 1) - b n) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Every finite path whose running maximum reaches the weighted saddle pays
the corrected barrier.  This is the deterministic necessity statement used
by `prop:arrwindow`(ii). -/
theorem IsControlledCivicWeightedPath.action_lower_bound_of_crossing
    {p : LoopParams} {ρ L : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p ρ) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPath p ρ u x) {N : ℕ}
    (hcross : weighted.βdagger ≤ policyRunningMax x N) :
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
    path.barrier_integral_le_partition_of_crossing model weighted hL hcross
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

/-- Membership in the Gaussian saddle-crossing event forces the realized
scaled noise vector to pay the corrected deterministic action. -/
theorem gaussianEscapeEvent_action_lower_bound
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ L : ℝ}
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p ρ) L
      0 weighted.βdagger)
    {T : ℕ} {σ : ℝ} {ξ : Fin T → ℝ}
    (hξ : ξ ∈ gaussianEscapeEvent weighted T σ) :
    (2 / (p.α * (1 + 2 * p.α * L))) *
        (∫ b in (0 : ℝ)..weighted.βdagger,
          weightedBarrierIntegrand p ρ b) ≤
      σ ^ 2 * gaussianVectorAction ξ := by
  have hpath := finiteControlledOrbit_isControlled p ρ
    (scaledGaussianControl σ ξ)
  have haction := hpath.action_lower_bound_of_crossing model ss hcoop
    weighted hL hξ
  rwa [controlAction_scaledGaussianControl] at haction

/-! ## Robust finite control tubes -/

/-- At every fixed time, the controlled endpoint depends continuously on the
finite control vector. -/
theorem continuous_finiteControlledOrbit (p : LoopParams) (ρ : ℝ)
    {T : ℕ} (n : ℕ) :
    Continuous (fun u : Fin T → ℝ ↦ finiteControlledOrbit p ρ u n) := by
  induction n with
  | zero =>
      simp only [finiteControlledOrbit]
      fun_prop
  | succ n ih =>
      simp only [finiteControlledOrbit]
      unfold controlledCivicWeightedStep civicWeightedGradient
        LoopParams.gradU LoopParams.stockStep LoopParams.s LoopParams.clipUnit
        extendFiniteControl
      split <;> fun_prop

/-- Restricting the controls of an exact controlled path reproduces that path
through the restriction horizon. -/
theorem finiteControlledOrbit_restrict_eq
    {p : LoopParams} {ρ : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (path : IsControlledCivicWeightedPath p ρ u x) {T n : ℕ}
    (hn : n ≤ T) :
    finiteControlledOrbit p ρ (fun i : Fin T ↦ u i) n = x n := by
  induction n with
  | zero => simpa only [finiteControlledOrbit] using path.initial.symm
  | succ n ih =>
      have hnlt : n < T := by omega
      rw [finiteControlledOrbit, path.step n, ih (by omega)]
      simp only [extendFiniteControl, hnlt, dite_true]

/-- Once a finite history is exhausted, its continuation is exactly the
unforced civic-weighted orbit from the terminal state. -/
theorem finiteControlledOrbit_tail
    (p : LoopParams) (ρ : ℝ) {T : ℕ} (u : Fin T → ℝ) (k : ℕ) :
    finiteControlledOrbit p ρ u (T + k) =
      civicWeightedOrbit p ρ (finiteControlledOrbit p ρ u T) k := by
  induction k with
  | zero => simp only [Nat.add_zero, civicWeightedOrbit, Function.iterate_zero_apply]
  | succ k ih =>
      rw [Nat.add_succ, finiteControlledOrbit, ih]
      have hnot : ¬T + k < T := by omega
      simp only [extendFiniteControl, hnot, dite_false,
        controlledCivicWeightedStep, civicWeightedOrbit,
        Function.iterate_succ_apply', civicWeightedLoopMap,
        civicWeightedDeferenceStep, civicWeightedInput, add_zero]

/-- The vector action of a restricted sequence is its sequence action through
the same horizon. -/
theorem gaussianVectorAction_restrict (u : ℕ → ℝ) (T : ℕ) :
    gaussianVectorAction (fun i : Fin T ↦ u i) = controlAction u T := by
  simp only [gaussianVectorAction, controlAction]
  rw [← Fin.sum_univ_eq_sum_range]

/-- The two-phase control is identically zero after its canonical
stopping horizon. -/
theorem twoPhaseUpperControl_eq_zero_of_totalStop_le
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (ε : ℝ) {n : ℕ} (hn : upperStrategyTotalStop weighted ε ≤ n) :
    twoPhaseUpperControl weighted ε n = 0 := by
  have hclimb : ¬n < upperStrategyClimbStop weighted ε := by
    exact not_lt_of_ge ((Nat.le_add_right _ _).trans hn)
  have htotal : ¬n < upperStrategyTotalStop weighted ε := not_lt_of_ge hn
  simp only [twoPhaseUpperControl, twoPhaseUpperControlAt,
    if_neg hclimb, if_neg htotal]

/-- Adding an unforced tail does not change the two-phase strategy's action. -/
theorem controlAction_twoPhaseUpperControl_add_totalStop
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (ε : ℝ) (k : ℕ) :
    controlAction (twoPhaseUpperControl weighted ε)
        (upperStrategyTotalStop weighted ε + k) =
      upwardStrategyCostEpsilon weighted ε := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [Nat.add_succ, controlAction, Finset.sum_range_succ]
      rw [twoPhaseUpperControl_eq_zero_of_totalStop_le weighted ε
        (Nat.le_add_right _ _)]
      rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero]
      simpa only [controlAction] using ih

/-- After its stopping horizon, the two-phase path is the unforced
orbit from its stopping state. -/
theorem twoPhaseUpperPath_add_totalStop
    {p : LoopParams} {ρ : ℝ} (weighted : WeightedThresholdAssumption p ρ)
    (ε : ℝ) (k : ℕ) :
    twoPhaseUpperPath weighted ε (upperStrategyTotalStop weighted ε + k) =
      civicWeightedOrbit p ρ
        (twoPhaseUpperPath weighted ε (upperStrategyTotalStop weighted ε)) k := by
  induction k with
  | zero => simp only [Nat.add_zero, civicWeightedOrbit, Function.iterate_zero_apply]
  | succ k ih =>
      rw [Nat.add_succ, twoPhaseUpperPath_succ, ih,
        twoPhaseUpperControl_eq_zero_of_totalStop_le weighted ε
          (Nat.le_add_right _ _)]
      simp only [controlledCivicWeightedStep, civicWeightedOrbit,
        Function.iterate_succ_apply', civicWeightedLoopMap,
        civicWeightedDeferenceStep, civicWeightedInput, add_zero]

/-- A positive-margin two-phase strategy admits a finite open ball of control
histories which both crosses the saddle and then converges, unforced, to the
captured corner.  This is the robust deterministic tube used in
`prop:arrwindow`(i). -/
theorem exists_twoPhaseCapturingControlBall
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ ε : ℝ}
    (hρ : 0 ≤ ρ) (hρcure : ρ < cureThreshold p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hε : 0 < ε) :
    ∃ (T : ℕ) (u : Fin T → ℝ) (r : ℝ),
      0 < r ∧
      gaussianVectorAction u = upwardStrategyCostEpsilon weighted ε ∧
      ∀ v ∈ Metric.ball u r,
        weighted.βdagger ≤
            policyRunningMax (finiteControlledOrbit p ρ v) T ∧
          Tendsto (fun k ↦ finiteControlledOrbit p ρ v (T + k)) atTop
            (nhds (capturedPoint p)) := by
  obtain ⟨N, hN, hattract⟩ :=
    civicWeighted_captured_local_attraction model ss hρ hρcure
  obtain ⟨U, hUN, hUopen, hcapturedU⟩ := mem_nhds_iff.mp hN
  let W : Set LoopState := U ∩ Prod.fst ⁻¹' Ioi weighted.βdagger
  have hWopen : IsOpen W :=
    hUopen.inter (isOpen_Ioi.preimage continuous_fst)
  have hcapturedW : capturedPoint p ∈ W := by
    refine ⟨hcapturedU, ?_⟩
    simpa only [capturedPoint, mem_preimage, mem_Ioi] using
      weighted.βdagger_mem.2
  let T₀ := upperStrategyTotalStop weighted ε
  let y := twoPhaseUpperPath weighted ε T₀
  have hycaptured : Tendsto (civicWeightedOrbit p ρ y) atTop
      (nhds (capturedPoint p)) := by
    simpa only [y, T₀] using
      twoPhaseUpperPath_totalStop_tendsto_captured
        model ss hρcure hcoop weighted hε
  have heventually : ∀ᶠ k in atTop, civicWeightedOrbit p ρ y k ∈ W :=
    hycaptured.eventually (hWopen.mem_nhds hcapturedW)
  obtain ⟨k, hk⟩ := heventually.exists
  let T := T₀ + k
  let u : Fin T → ℝ := fun i ↦ twoPhaseUpperControl weighted ε i
  have hcenterPath : finiteControlledOrbit p ρ u T =
      twoPhaseUpperPath weighted ε T := by
    exact finiteControlledOrbit_restrict_eq
      (twoPhaseUpperPath_isControlled weighted ε) le_rfl
  have hcenterW : finiteControlledOrbit p ρ u T ∈ W := by
    rw [hcenterPath]
    have htail := twoPhaseUpperPath_add_totalStop weighted ε k
    change twoPhaseUpperPath weighted ε (T₀ + k) ∈ W
    rw [htail]
    simpa only [y, T₀] using hk
  let V : Set (Fin T → ℝ) :=
    {v | finiteControlledOrbit p ρ v T ∈ W}
  have hVopen : IsOpen V := by
    exact hWopen.preimage (continuous_finiteControlledOrbit p ρ T)
  have huV : u ∈ V := hcenterW
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hVopen.mem_nhds huV)
  refine ⟨T, u, r, hr, ?_, ?_⟩
  · rw [gaussianVectorAction_restrict,
      controlAction_twoPhaseUpperControl_add_totalStop]
  · intro v hv
    have hvW : finiteControlledOrbit p ρ v T ∈ W := hball hv
    constructor
    · exact hvW.2.le.trans
        (policy_le_runningMax (finiteControlledOrbit p ρ v) T)
    · have hvN : finiteControlledOrbit p ρ v T ∈ N := hUN hvW.1
      have hvBox : finiteControlledOrbit p ρ v T ∈ absorbingBox p :=
        (finiteControlledOrbit_isControlled p ρ v).mem_absorbingBox model T
      have hlim := hattract
        (civicWeightedOrbit_isTrajectory p ρ
          (finiteControlledOrbit p ρ v T)) hvBox hvN
      simpa only [finiteControlledOrbit_tail] using hlim

/-! ## Finite-dimensional Gaussian estimates -/

/-- A coordinate rectangle of standard-Gaussian histories whose scaled
controls lie one noise increment above a prescribed control vector. -/
def gaussianControlBox {T : ℕ} (u : Fin T → ℝ) (σ : ℝ) :
    Set (Fin T → ℝ) :=
  Set.pi univ fun i ↦ Icc (u i / σ) (u i / σ + 1)

/-- The explicit density floor on the unit interval used in
`gaussianControlBox`. -/
noncomputable def gaussianCoordinateLowerBound (u σ : ℝ) : ℝ :=
  (√(2 * Real.pi))⁻¹ *
    Real.exp (-((|u| / σ + 1) ^ 2) / 2)

theorem gaussianCoordinateLowerBound_pos (u : ℝ) {σ : ℝ} :
    0 < gaussianCoordinateLowerBound u σ := by
  unfold gaussianCoordinateLowerBound
  positivity

/-- On the shifted unit interval, the standard-Gaussian density is bounded
below by the displayed explicit floor. -/
theorem gaussianCoordinateLowerBound_le_pdf
    {u σ x : ℝ} (hσ : 0 < σ) (hx : x ∈ Icc (u / σ) (u / σ + 1)) :
    gaussianCoordinateLowerBound u σ ≤ gaussianPDFReal 0 1 x := by
  have hdiff : 0 ≤ x - u / σ ∧ x - u / σ ≤ 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have habsDiff : |x - u / σ| ≤ 1 := by
    rw [abs_of_nonneg hdiff.1]
    exact hdiff.2
  have habsCenter : |u / σ| = |u| / σ := by
    rw [abs_div, abs_of_pos hσ]
  have habs : |x| ≤ |u| / σ + 1 := by
    calc
      |x| = |u / σ + (x - u / σ)| := by ring_nf
      _ ≤ |u / σ| + |x - u / σ| := abs_add_le _ _
      _ ≤ |u| / σ + 1 := by rw [habsCenter]; gcongr
  have hright : 0 ≤ |u| / σ + 1 := by positivity
  have hsquare : x ^ 2 ≤ (|u| / σ + 1) ^ 2 := by
    calc
      x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      _ ≤ (|u| / σ + 1) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg x) hright).2 habs
  unfold gaussianCoordinateLowerBound gaussianPDFReal
  norm_num
  gcongr

/-- A standard Gaussian assigns at least the explicit density floor to the
corresponding unit interval. -/
theorem gaussianReal_unitInterval_lower
    {u σ : ℝ} (hσ : 0 < σ) :
    ENNReal.ofReal (gaussianCoordinateLowerBound u σ) ≤
      gaussianReal 0 1 (Icc (u / σ) (u / σ + 1)) := by
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero]
  apply ENNReal.ofReal_le_ofReal
  let q := gaussianCoordinateLowerBound u σ
  have hconst : IntegrableOn (fun _ : ℝ ↦ q) (Icc (u / σ) (u / σ + 1)) :=
    integrableOn_const (by simp [Real.volume_Icc])
  have hpdf : IntegrableOn (gaussianPDFReal 0 1)
      (Icc (u / σ) (u / σ + 1)) :=
    (integrable_gaussianPDFReal 0 1).integrableOn
  have hmono := setIntegral_mono_on hconst hpdf measurableSet_Icc
    (fun x hx ↦ gaussianCoordinateLowerBound_le_pdf hσ hx)
  calc
    q = ∫ _x in Icc (u / σ) (u / σ + 1), q := by
      rw [setIntegral_const]
      simp [Measure.real, Real.volume_Icc]
    _ ≤ ∫ x in Icc (u / σ) (u / σ + 1), gaussianPDFReal 0 1 x := hmono

/-- The product Gaussian measure of the control box has the product of the
coordinate density floors as a lower bound. -/
theorem gaussianControlBox_probability_lower {T : ℕ}
    (u : Fin T → ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ENNReal.ofReal (∏ i, gaussianCoordinateLowerBound (u i) σ) ≤
      standardGaussianVector T (gaussianControlBox u σ) := by
  rw [standardGaussianVector, gaussianControlBox, Measure.pi_pi]
  rw [ENNReal.ofReal_prod_of_nonneg
    (fun i _ ↦ (gaussianCoordinateLowerBound_pos (u i)).le)]
  exact Finset.prod_le_prod (fun _ _ ↦ bot_le)
    (fun i _ ↦ gaussianReal_unitInterval_lower hσ)

/-- For `0 < σ < r`, every scaled history in the control box lies in the
radius-`r` control tube. -/
theorem scaledGaussianControl_mem_ball_of_mem_controlBox
    {T : ℕ} {u : Fin T → ℝ} {σ r : ℝ}
    (hσ : 0 < σ) (hσr : σ < r) {ξ : Fin T → ℝ}
    (hξ : ξ ∈ gaussianControlBox u σ) :
    scaledGaussianControl σ ξ ∈ Metric.ball u r := by
  rw [Metric.mem_ball, dist_pi_lt_iff (hσ.trans hσr)]
  intro i
  have hi := hξ i (mem_univ i)
  have hlower : u i ≤ σ * ξ i := by
    have := (div_le_iff₀ hσ).mp hi.1
    simpa only [mul_comm] using this
  have hupper : σ * ξ i ≤ u i + σ := by
    calc
      σ * ξ i ≤ σ * (u i / σ + 1) :=
        mul_le_mul_of_nonneg_left hi.2 hσ.le
      _ = u i + σ := by field_simp [hσ.ne']
  simp only [scaledGaussianControl]
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlower)]
  linarith

/-- The explicit real logarithmic rate of the product density floor. -/
noncomputable def gaussianControlBoxExplicitRate {T : ℕ}
    (u : Fin T → ℝ) (σ : ℝ) : ℝ :=
  σ ^ 2 * Real.log (∏ i, gaussianCoordinateLowerBound (u i) σ)

/-- Coordinatewise algebra behind the lower Gaussian tube rate. -/
theorem scaled_log_gaussianCoordinateLowerBound
    (u : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    σ ^ 2 * Real.log (gaussianCoordinateLowerBound u σ) =
      -(1 / 2 : ℝ) * u ^ 2 - σ * |u| +
        σ ^ 2 * (Real.log (√(2 * Real.pi))⁻¹ - 1 / 2) := by
  unfold gaussianCoordinateLowerBound
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  rw [← sq_abs u]
  field_simp [hσ.ne']
  ring_nf

/-- The finite product floor has the action as its exact leading logarithmic
rate, with explicit linear and quadratic remainders. -/
theorem gaussianControlBoxExplicitRate_eq {T : ℕ}
    (u : Fin T → ℝ) {σ : ℝ} (hσ : 0 < σ) :
    gaussianControlBoxExplicitRate u σ =
      -gaussianVectorAction u - σ * ∑ i, |u i| +
        σ ^ 2 * (T : ℝ) *
          (Real.log (√(2 * Real.pi))⁻¹ - 1 / 2) := by
  unfold gaussianControlBoxExplicitRate
  rw [Real.log_prod (fun i _ ↦
    (gaussianCoordinateLowerBound_pos (u i)).ne')]
  rw [Finset.mul_sum]
  simp_rw [scaled_log_gaussianCoordinateLowerBound _ hσ]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const]
  rw [Finset.card_univ, Fintype.card_fin]
  unfold gaussianVectorAction
  have habs : (∑ i : Fin T, σ * |u i|) = σ * ∑ i, |u i| := by
    rw [Finset.mul_sum]
  have hsquare : (∑ i : Fin T, (-(1 / 2 : ℝ)) * u i ^ 2) =
      (-(1 / 2 : ℝ)) * ∑ i, u i ^ 2 := by
    rw [Finset.mul_sum]
  rw [habs, hsquare]
  simp only [nsmul_eq_mul]
  ring

/-- The explicit product density floor converges to minus the finite control
action at the small-noise scale. -/
theorem gaussianControlBoxExplicitRate_tendsto {T : ℕ} (u : Fin T → ℝ) :
    Tendsto (gaussianControlBoxExplicitRate u)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds (-gaussianVectorAction u)) := by
  let P : ℝ → ℝ := fun σ ↦
    -gaussianVectorAction u - σ * ∑ i, |u i| +
      σ ^ 2 * (T : ℝ) *
        (Real.log (√(2 * Real.pi))⁻¹ - 1 / 2)
  have hP : Tendsto P (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds (-gaussianVectorAction u)) := by
    have hcont : ContinuousAt P 0 := by
      dsimp only [P]
      fun_prop
    have ht := hcont.tendsto.mono_left
      (nhdsWithin_le_nhds :
        nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)) ≤ nhds 0)
    simpa [P] using ht
  apply hP.congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  exact (gaussianControlBoxExplicitRate_eq u hσ).symm

/-- The product-Gaussian probability of the control box has logarithmic
liminf at least minus the prescribed control action. -/
theorem gaussianControlBox_logRate_liminf {T : ℕ} (u : Fin T → ℝ) :
    ((-gaussianVectorAction u : ℝ) : EReal) ≤
      liminf
        (fun σ : ℝ ↦ (σ ^ 2 : ℝ) *
          ENNReal.log (standardGaussianVector T (gaussianControlBox u σ)))
        (nhdsWithin 0 (Ioi (0 : ℝ))) := by
  have hpointwise : ∀ᶠ σ : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      ((gaussianControlBoxExplicitRate u σ : ℝ) : EReal) ≤
        (σ ^ 2 : ℝ) *
          ENNReal.log (standardGaussianVector T (gaussianControlBox u σ)) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hprob := gaussianControlBox_probability_lower u hσ
    have hlog := ENNReal.logOrderIso.monotone hprob
    change ENNReal.log
        (ENNReal.ofReal (∏ i, gaussianCoordinateLowerBound (u i) σ)) ≤
      ENNReal.log (standardGaussianVector T (gaussianControlBox u σ)) at hlog
    have hprodPos : 0 < ∏ i, gaussianCoordinateLowerBound (u i) σ :=
      Finset.prod_pos fun i _ ↦ gaussianCoordinateLowerBound_pos (u i)
    rw [ENNReal.log_ofReal_of_pos hprodPos] at hlog
    have hσsq : 0 ≤ (σ ^ 2 : ℝ) := sq_nonneg σ
    have hmul := mul_le_mul_of_nonneg_left hlog
      (show (0 : EReal) ≤ (σ ^ 2 : ℝ) by exact_mod_cast hσsq)
    simpa only [gaussianControlBoxExplicitRate, EReal.coe_mul] using hmul
  have hreal := gaussianControlBoxExplicitRate_tendsto u
  have hereal : Tendsto
      (fun σ ↦ ((gaussianControlBoxExplicitRate u σ : ℝ) : EReal))
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds (((-gaussianVectorAction u : ℝ) : EReal))) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hreal
  exact le_trans hereal.liminf_eq.symm.le (liminf_le_liminf hpointwise)

/-- Any robust capturing control ball yields a matching finite-horizon
Gaussian lower rate at the action of its center. -/
theorem gaussianCapturingEscapeLogRate_liminf_of_controlBall
    {p : LoopParams} {ρ : ℝ}
    (weighted : WeightedThresholdAssumption p ρ)
    {T : ℕ} (u : Fin T → ℝ) {r : ℝ} (hr : 0 < r)
    (htub : ∀ v ∈ Metric.ball u r,
      weighted.βdagger ≤
          policyRunningMax (finiteControlledOrbit p ρ v) T ∧
        Tendsto (fun k ↦ finiteControlledOrbit p ρ v (T + k)) atTop
          (nhds (capturedPoint p))) :
    ((-gaussianVectorAction u : ℝ) : EReal) ≤
      liminf (fun σ : ℝ ↦ gaussianCapturingEscapeLogRate weighted T σ)
        (nhdsWithin 0 (Ioi (0 : ℝ))) := by
  have hrNhds : ∀ᶠ σ : ℝ in nhds 0, σ < r := Iio_mem_nhds hr
  have hrEventually : ∀ᶠ σ : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)), σ < r :=
    hrNhds.filter_mono inf_le_left
  have hpointwise : ∀ᶠ σ : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      (σ ^ 2 : ℝ) *
          ENNReal.log (standardGaussianVector T (gaussianControlBox u σ)) ≤
        gaussianCapturingEscapeLogRate weighted T σ := by
    filter_upwards [self_mem_nhdsWithin, hrEventually] with σ hσ hσr
    have hsubset : gaussianControlBox u σ ⊆
        gaussianCapturingEscapeEvent weighted T σ := by
      intro ξ hξ
      have hball := scaledGaussianControl_mem_ball_of_mem_controlBox
        hσ hσr hξ
      exact htub (scaledGaussianControl σ ξ) hball
    have hmeasure :
        standardGaussianVector T (gaussianControlBox u σ) ≤
          standardGaussianVector T
            (gaussianCapturingEscapeEvent weighted T σ) :=
      measure_mono hsubset
    have hlog := ENNReal.logOrderIso.monotone hmeasure
    change ENNReal.log
        (standardGaussianVector T (gaussianControlBox u σ)) ≤
      ENNReal.log (gaussianCapturingEscapeProbability weighted T σ) at hlog
    have hσsq : 0 ≤ (σ ^ 2 : ℝ) := sq_nonneg σ
    have hmul := mul_le_mul_of_nonneg_left hlog
      (show (0 : EReal) ≤ (σ ^ 2 : ℝ) by exact_mod_cast hσsq)
    simpa only [gaussianCapturingEscapeLogRate] using hmul
  exact (gaussianControlBox_logRate_liminf u).trans
    (liminf_le_liminf hpointwise)

/-- Capturing crossings form a subset of all saddle crossings. -/
theorem gaussianCapturingEscapeLogRate_liminf_le_escapeLogRate_liminf
    {p : LoopParams} {ρ : ℝ}
    (weighted : WeightedThresholdAssumption p ρ) (T : ℕ) :
    liminf (fun σ : ℝ ↦ gaussianCapturingEscapeLogRate weighted T σ)
        (nhdsWithin 0 (Ioi (0 : ℝ))) ≤
      liminf (fun σ : ℝ ↦ gaussianEscapeLogRate weighted T σ)
        (nhdsWithin 0 (Ioi (0 : ℝ))) := by
  apply liminf_le_liminf (hu := Filter.isBounded_ge_of_bot)
    (hv := Filter.isCobounded_ge_of_top)
  filter_upwards with σ
  have hsubset : gaussianCapturingEscapeEvent weighted T σ ⊆
      gaussianEscapeEvent weighted T σ := fun _ h ↦ h.1
  have hmeasure :
      standardGaussianVector T
          (gaussianCapturingEscapeEvent weighted T σ) ≤
        standardGaussianVector T (gaussianEscapeEvent weighted T σ) :=
    measure_mono hsubset
  have hlog := ENNReal.logOrderIso.monotone hmeasure
  change ENNReal.log (gaussianCapturingEscapeProbability weighted T σ) ≤
    ENNReal.log (gaussianEscapeProbability weighted T σ) at hlog
  have hσsq : 0 ≤ (σ ^ 2 : ℝ) := sq_nonneg σ
  exact mul_le_mul_of_nonneg_left hlog
    (show (0 : EReal) ≤ (σ ^ 2 : ℝ) by exact_mod_cast hσsq)

/-- A positive tolerance selects one finite two-phase strategy whose robust
capturing tube has logarithmic rate within that tolerance of `S↑`. -/
theorem exists_horizon_gaussianCapturingEscapeLogRate_liminf
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hρcure : ρ < cureThreshold p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) (hδ : 0 < δ) :
    ∃ T : ℕ,
      (((-upwardStrategyCost weighted - δ : ℝ) : EReal) ≤
        liminf
          (fun σ : ℝ ↦ gaussianCapturingEscapeLogRate weighted T σ)
          (nhdsWithin 0 (Ioi (0 : ℝ)))) := by
  have hcostSetNonempty : (upwardStrategyCostSet weighted).Nonempty :=
    ⟨upwardStrategyCostEpsilon weighted 1, 1, by norm_num, rfl⟩
  have hinfLt : sInf (upwardStrategyCostSet weighted) <
      upwardStrategyCost weighted + δ / 2 := by
    rw [← upwardStrategyCost]
    linarith
  obtain ⟨a, haSet, haLt⟩ :=
    exists_lt_of_csInf_lt hcostSetNonempty hinfLt
  rcases haSet with ⟨ε, hε, rfl⟩
  obtain ⟨T, u, r, hr, haction, htube⟩ :=
    exists_twoPhaseCapturingControlBall
      model ss hρ hρcure hcoop weighted hε
  refine ⟨T, ?_⟩
  have htubeRate := gaussianCapturingEscapeLogRate_liminf_of_controlBall
    weighted u hr htube
  rw [haction] at htubeRate
  have hcost : -upwardStrategyCost weighted - δ ≤
      -upwardStrategyCostEpsilon weighted ε := by
    linarith
  exact (show
      (((-upwardStrategyCost weighted - δ : ℝ) : EReal) ≤
        ((-upwardStrategyCostEpsilon weighted ε : ℝ) : EReal)) by
      exact_mod_cast hcost).trans htubeRate

/-- A standard Gaussian has a finite exponential moment of half its square
at every parameter strictly below one. -/
theorem integrable_exp_half_sq_standardGaussian {t : ℝ} (ht : t < 1) :
    Integrable (fun x : ℝ ↦ Real.exp (t * ((1 / 2 : ℝ) * x ^ 2)))
      (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1)
    (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)]
  have hcoefficient : 0 < (1 - t) / 2 := by linarith
  have hbase : Integrable (fun x : ℝ ↦
      Real.exp (-((1 - t) / 2) * x ^ 2)) (volume : Measure ℝ) :=
    integrable_exp_neg_mul_sq hcoefficient
  have hconst := hbase.const_mul (√(2 * Real.pi))⁻¹
  refine hconst.congr (ae_of_all _ fun x ↦ ?_)
  simp only [toReal_gaussianPDF, smul_eq_mul, gaussianPDFReal,
    NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  ring_nf

/-- The action of a finite independent standard-Gaussian vector has a finite
exponential moment at every parameter strictly below one. -/
theorem integrable_exp_gaussianVectorAction {T : ℕ} {t : ℝ} (ht : t < 1) :
    Integrable (fun ξ : Fin T → ℝ ↦ Real.exp (t * gaussianVectorAction ξ))
      (standardGaussianVector T) := by
  have hprod : Integrable
      (fun ξ : Fin T → ℝ ↦
        ∏ i, Real.exp (t * ((1 / 2 : ℝ) * (ξ i) ^ 2)))
      (standardGaussianVector T) :=
    Integrable.fintype_prod fun _ ↦
      integrable_exp_half_sq_standardGaussian ht
  convert hprod using 1
  funext ξ
  simp only [gaussianVectorAction]
  have hsum : t * ((1 / 2 : ℝ) * ∑ i, (ξ i) ^ 2) =
      ∑ i, t * ((1 / 2 : ℝ) * (ξ i) ^ 2) := by
    simp only [Finset.mul_sum]
  rw [hsum]
  simpa using (Real.exp_sum Finset.univ
    (fun i : Fin T ↦ t * ((1 / 2 : ℝ) * (ξ i) ^ 2)))

/-- Finite-dimensional Chernoff estimate for the saddle-crossing event.  The
parameter is normalized for the action `½∑ξ²`, hence its critical value is one. -/
theorem gaussianEscapeProbability_le_chernoff
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ L : ℝ}
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p ρ) L
      0 weighted.βdagger)
    {T : ℕ} {σ t : ℝ} (hσ : σ ≠ 0) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    gaussianEscapeProbability weighted T σ ≤
      ENNReal.ofReal
        (Real.exp (-t *
            (((2 / (p.α * (1 + 2 * p.α * L))) *
              (∫ b in (0 : ℝ)..weighted.βdagger,
                weightedBarrierIntegrand p ρ b)) / σ ^ 2)) *
          mgf gaussianVectorAction (standardGaussianVector T) t) := by
  letI : IsProbabilityMeasure (standardGaussianVector T) := by
    unfold standardGaussianVector
    infer_instance
  let B : ℝ := (2 / (p.α * (1 + 2 * p.α * L))) *
    (∫ b in (0 : ℝ)..weighted.βdagger,
      weightedBarrierIntegrand p ρ b)
  have hσsq : 0 < σ ^ 2 := sq_pos_of_ne_zero hσ
  have hsubset : gaussianEscapeEvent weighted T σ ⊆
      {ξ : Fin T → ℝ | B / σ ^ 2 ≤ gaussianVectorAction ξ} := by
    intro ξ hξ
    have hpay := gaussianEscapeEvent_action_lower_bound
      model ss hcoop weighted hL hξ
    change B ≤ σ ^ 2 * gaussianVectorAction ξ at hpay
    exact (div_le_iff₀ hσsq).2 (by simpa only [mul_comm] using hpay)
  have hmono :
      (standardGaussianVector T).real (gaussianEscapeEvent weighted T σ) ≤
        (standardGaussianVector T).real
          {ξ : Fin T → ℝ | B / σ ^ 2 ≤ gaussianVectorAction ξ} :=
    measureReal_mono hsubset
  have hchernoff :
      (standardGaussianVector T).real
          {ξ : Fin T → ℝ | B / σ ^ 2 ≤ gaussianVectorAction ξ} ≤
        Real.exp (-t * (B / σ ^ 2)) *
          mgf gaussianVectorAction (standardGaussianVector T) t :=
    measure_ge_le_exp_mul_mgf (B / σ ^ 2) ht0
      (integrable_exp_gaussianVectorAction ht1)
  have hnonneg : 0 ≤ Real.exp (-t * (B / σ ^ 2)) *
      mgf gaussianVectorAction (standardGaussianVector T) t :=
    mul_nonneg (Real.exp_pos _).le mgf_nonneg
  have hprob_ne_top : gaussianEscapeProbability weighted T σ ≠ ∞ := by
    exact measure_ne_top _ _
  apply (ENNReal.toReal_le_toReal hprob_ne_top (by simp)).1
  change (standardGaussianVector T).real
      (gaussianEscapeEvent weighted T σ) ≤ _
  rw [ENNReal.toReal_ofReal hnonneg]
  exact hmono.trans hchernoff

/-- After taking the extended logarithm, the Chernoff prefactor is an
ordinary finite constant multiplied by `σ²`. -/
theorem gaussianEscapeLogRate_le_chernoff
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ L : ℝ}
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p ρ) L
      0 weighted.βdagger)
    {T : ℕ} {σ t : ℝ} (hσ : σ ≠ 0) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    gaussianEscapeLogRate weighted T σ ≤
      ((-t * ((2 / (p.α * (1 + 2 * p.α * L))) *
          (∫ b in (0 : ℝ)..weighted.βdagger,
            weightedBarrierIntegrand p ρ b)) +
        σ ^ 2 * Real.log
          (mgf gaussianVectorAction (standardGaussianVector T) t) : ℝ) : EReal) := by
  letI : IsProbabilityMeasure (standardGaussianVector T) := by
    unfold standardGaussianVector
    infer_instance
  let B : ℝ := (2 / (p.α * (1 + 2 * p.α * L))) *
    (∫ b in (0 : ℝ)..weighted.βdagger,
      weightedBarrierIntegrand p ρ b)
  let C : ℝ := mgf gaussianVectorAction (standardGaussianVector T) t
  have hInt : Integrable
      (fun ξ : Fin T → ℝ ↦ Real.exp (t * gaussianVectorAction ξ))
      (standardGaussianVector T) :=
    integrable_exp_gaussianVectorAction ht1
  have hCpos : 0 < C := by
    simpa only [C] using mgf_pos hInt
  have hprob := gaussianEscapeProbability_le_chernoff
    (T := T) model ss hcoop weighted hL hσ ht0 ht1
  change gaussianEscapeProbability weighted T σ ≤
      ENNReal.ofReal (Real.exp (-t * (B / σ ^ 2)) * C) at hprob
  have hlog : ENNReal.log (gaussianEscapeProbability weighted T σ) ≤
      ENNReal.log (ENNReal.ofReal (Real.exp (-t * (B / σ ^ 2)) * C)) :=
    ENNReal.logOrderIso.monotone hprob
  have hrhs : ENNReal.log
      (ENNReal.ofReal (Real.exp (-t * (B / σ ^ 2)) * C)) =
      ((-t * (B / σ ^ 2) + Real.log C : ℝ) : EReal) := by
    rw [ENNReal.log_ofReal_of_pos (mul_pos (Real.exp_pos _) hCpos)]
    norm_cast
    rw [Real.log_mul (Real.exp_pos _).ne' hCpos.ne', Real.log_exp]
  have hσsq : 0 ≤ (σ ^ 2 : ℝ) := sq_nonneg σ
  have hmul := mul_le_mul_of_nonneg_left hlog
    (show (0 : EReal) ≤ (σ ^ 2 : ℝ) by exact_mod_cast hσsq)
  rw [hrhs] at hmul
  change gaussianEscapeLogRate weighted T σ ≤
    ((σ ^ 2 : ℝ) : EReal) *
      ((-t * (B / σ ^ 2) + Real.log C : ℝ) : EReal) at hmul
  have heq : ((σ ^ 2 : ℝ) : EReal) *
        ((-t * (B / σ ^ 2) + Real.log C : ℝ) : EReal) =
      ((-t * B + σ ^ 2 * Real.log C : ℝ) : EReal) := by
    norm_cast
    field_simp [hσ]
  simpa only [B, C] using hmul.trans_eq heq

/-- At fixed Chernoff parameter, the finite moment contributes zero to the
small-noise logarithmic rate. -/
theorem limsup_gaussianEscapeLogRate_le_chernoffParameter
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ L : ℝ}
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p ρ) L
      0 weighted.βdagger)
    (T : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    limsup (fun σ : ℝ ↦ gaussianEscapeLogRate weighted T σ)
        (nhdsWithin 0 (Ioi (0 : ℝ))) ≤
      ((-t * ((2 / (p.α * (1 + 2 * p.α * L))) *
        (∫ b in (0 : ℝ)..weighted.βdagger,
          weightedBarrierIntegrand p ρ b)) : ℝ) : EReal) := by
  let C : ℝ := Real.log
    (mgf gaussianVectorAction (standardGaussianVector T) t)
  let B : ℝ := (2 / (p.α * (1 + 2 * p.α * L))) *
    (∫ b in (0 : ℝ)..weighted.βdagger,
      weightedBarrierIntegrand p ρ b)
  have hpointwise : ∀ᶠ σ : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      gaussianEscapeLogRate weighted T σ ≤
        ((-t * B + σ ^ 2 * C : ℝ) : EReal) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    simpa only [B, C] using gaussianEscapeLogRate_le_chernoff
      (T := T) model ss hcoop weighted hL hσ.ne' ht0 ht1
  have hreal : Tendsto (fun σ : ℝ ↦ -t * B + σ ^ 2 * C)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (𝓝 (-t * B)) := by
    have hcont : ContinuousAt (fun σ : ℝ ↦ -t * B + σ ^ 2 * C) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hereal : Tendsto
      (fun σ : ℝ ↦ ((-t * B + σ ^ 2 * C : ℝ) : EReal))
      (nhdsWithin 0 (Ioi (0 : ℝ)))
        (nhds (((-t * B : ℝ) : EReal))) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hreal
  exact (limsup_le_limsup hpointwise).trans_eq (by
    simpa only [B] using hereal.limsup_eq)

/-- Paper II, Proposition `prop:arrwindow`(ii) in `civic_drift.tex`:
at every fixed horizon, the small-noise upper logarithmic rate is at most the
corrected deterministic barrier. -/
theorem gaussianEscapeLogRate_limsup_le_correctedBarrier
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ L : ℝ}
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p ρ) L
      0 weighted.βdagger)
    (T : ℕ) :
    limsup (fun σ : ℝ ↦ gaussianEscapeLogRate weighted T σ)
        (nhdsWithin 0 (Ioi (0 : ℝ))) ≤
      ((-((2 / (p.α * (1 + 2 * p.α * L))) *
        (∫ b in (0 : ℝ)..weighted.βdagger,
          weightedBarrierIntegrand p ρ b)) : ℝ) : EReal) := by
  let B : ℝ := (2 / (p.α * (1 + 2 * p.α * L))) *
    (∫ b in (0 : ℝ)..weighted.βdagger,
      weightedBarrierIntegrand p ρ b)
  let R : EReal := limsup
    (fun σ : ℝ ↦ gaussianEscapeLogRate weighted T σ)
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
      limsup_gaussianEscapeLogRate_le_chernoffParameter
        model ss hcoop weighted hL T ht0 ht1
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

/-- Paper II, Proposition `prop:arrwindow` in `civic_drift.tex`.
For every positive tolerance, one finite horizon has the lower logarithmic
rate promised by the explicit two-phase strategy; the bound already holds
for the subset of crossing histories whose unforced continuation captures.
At every fixed horizon, all crossing histories obey the corrected-barrier
upper logarithmic rate. -/
theorem escapeProbabilityWindow
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (_threshold : ThresholdAssumption p)
    {ρ L : ℝ} (hρ : 0 ≤ ρ) (hρcure : ρ < cureThreshold p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p ρ) L
      0 weighted.βdagger) :
    (∀ δ : ℝ, 0 < δ → ∃ T : ℕ,
      (((-upwardStrategyCost weighted - δ : ℝ) : EReal) ≤
        liminf
          (fun σ : ℝ ↦ gaussianCapturingEscapeLogRate weighted T σ)
          (nhdsWithin 0 (Ioi (0 : ℝ)))) ∧
      (((-upwardStrategyCost weighted - δ : ℝ) : EReal) ≤
        liminf (fun σ : ℝ ↦ gaussianEscapeLogRate weighted T σ)
          (nhdsWithin 0 (Ioi (0 : ℝ))))) ∧
    (∀ T : ℕ,
      limsup (fun σ : ℝ ↦ gaussianEscapeLogRate weighted T σ)
          (nhdsWithin 0 (Ioi (0 : ℝ))) ≤
        ((-((2 / (p.α * (1 + 2 * p.α * L))) *
          (∫ b in (0 : ℝ)..weighted.βdagger,
            weightedBarrierIntegrand p ρ b)) : ℝ) : EReal)) := by
  constructor
  · intro δ hδ
    obtain ⟨T, hcapturing⟩ :=
      exists_horizon_gaussianCapturingEscapeLogRate_liminf
        model ss hρ hρcure hcoop weighted hδ
    refine ⟨T, hcapturing, ?_⟩
    exact hcapturing.trans
      (gaussianCapturingEscapeLogRate_liminf_le_escapeLogRate_liminf
        weighted T)
  · intro T
    exact gaussianEscapeLogRate_limsup_le_correctedBarrier
      model ss hcoop weighted hL T

#print axioms extendFiniteControl_apply
#print axioms finiteControlledOrbit_isControlled
#print axioms controlAction_extendFiniteControl
#print axioms controlAction_scaledGaussianControl
#print axioms IsControlledCivicWeightedPath.barrier_integral_le_partition_of_crossing
#print axioms IsControlledCivicWeightedPath.action_lower_bound_of_crossing
#print axioms gaussianEscapeEvent_action_lower_bound
#print axioms continuous_finiteControlledOrbit
#print axioms finiteControlledOrbit_restrict_eq
#print axioms finiteControlledOrbit_tail
#print axioms gaussianVectorAction_restrict
#print axioms twoPhaseUpperControl_eq_zero_of_totalStop_le
#print axioms controlAction_twoPhaseUpperControl_add_totalStop
#print axioms twoPhaseUpperPath_add_totalStop
#print axioms exists_twoPhaseCapturingControlBall
#print axioms gaussianCoordinateLowerBound_pos
#print axioms gaussianCoordinateLowerBound_le_pdf
#print axioms gaussianReal_unitInterval_lower
#print axioms gaussianControlBox_probability_lower
#print axioms scaledGaussianControl_mem_ball_of_mem_controlBox
#print axioms scaled_log_gaussianCoordinateLowerBound
#print axioms gaussianControlBoxExplicitRate_eq
#print axioms gaussianControlBoxExplicitRate_tendsto
#print axioms gaussianControlBox_logRate_liminf
#print axioms gaussianCapturingEscapeLogRate_liminf_of_controlBall
#print axioms gaussianCapturingEscapeLogRate_liminf_le_escapeLogRate_liminf
#print axioms exists_horizon_gaussianCapturingEscapeLogRate_liminf
#print axioms integrable_exp_half_sq_standardGaussian
#print axioms integrable_exp_gaussianVectorAction
#print axioms gaussianEscapeProbability_le_chernoff
#print axioms gaussianEscapeLogRate_le_chernoff
#print axioms limsup_gaussianEscapeLogRate_le_chernoffParameter
#print axioms gaussianEscapeLogRate_limsup_le_correctedBarrier
#print axioms escapeProbabilityWindow

end

end CivicAlignment.PaperII
