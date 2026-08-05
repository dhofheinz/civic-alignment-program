/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.BasinBoundaryAccessibility
import CivicAlignment.PaperII.ArrheniusLower

/-!
# Paper II: the sharp lower rate for genuine basin exit

Under the weighted convergent-step condition, a thin inner layer of the
calibrated-basin boundary has approach cost arbitrarily close to the
quasipotential.  Policy matching transfers this charge uniformly to starts
near the calibrated corner.  Before an excursion reaches that layer, every
block stays in a positive-clearance basin core, where avoidance of the corner
has a fixed positive action charge.

The resulting first-entrance decomposition places every complete excursion
in one fixed-dimensional Gaussian action tail, independently of its duration.
A last-visit decomposition then proves persistence up to every exponential
horizon below the quasipotential and hence the sharp mean basin-exit rate.
-/

namespace CivicAlignment.PaperII

open Filter Function MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## Nearby-start transport of the boundary-layer charge -/

/-- The basin quasipotential is nonnegative whenever its defining action set
is nonempty under the printed below-release assumptions. -/
theorem civicQuasipotential_nonneg
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (hrho : 0 ≤ rho) (hrhoCure : rho < cureThreshold p) :
    0 ≤ civicQuasipotential p rho := by
  rw [civicQuasipotential]
  apply le_csInf (quasipotentialActionSet_nonempty model ss hrho hrhoCure)
  rintro a ⟨N, u, _x, _path, _hexit, rfl⟩
  exact controlAction_nonneg u N

/-- The arbitrary-start restricted finite recursion has the same underlying
state as the ambient arbitrary-start recursion. -/
theorem finiteControlledOrbitFromInBox_val
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    (x₀ : LoopBox p) {T : ℕ} (u : Fin T → ℝ) (n : ℕ) :
    (finiteControlledOrbitFromInBox model rho x₀ u n).1 =
      finiteControlledOrbitFrom p rho x₀.1 u n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change controlledCivicWeightedStep p rho (finiteControlValue u n)
          (finiteControlledOrbitFromInBox model rho x₀ u n).1 =
        controlledCivicWeightedStep p rho (extendFiniteControl u n)
          (finiteControlledOrbitFrom p rho x₀.1 u n)
      rw [ih]
      congr 1

/-- Policy matching keeps the terminal state uniformly close to the original
terminal state.  The bound is independent of the control horizon. -/
theorem finiteControlledOrbitFromInBox_dist_policyMatched_le
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    (z : LoopBox p) {T : ℕ} (u : Fin T → ℝ) (hT : 1 ≤ T) :
    dist
        (finiteControlledOrbitFromInBox model rho z u T)
        (finiteControlledOrbitInBox model rho
          (policyMatchedControl p rho z.1 u) T) ≤
      policyMatchingInitialStockConstant p *
        dist z (calibratedPointInBox p model) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T ≠ 0)
  let uSeq : ℕ → ℝ := extendFiniteControl u
  have horiginal :
      finiteControlledOrbitFrom p rho z.1 u (n + 1) =
        controlledCivicWeightedOrbitFrom p rho z.1 uSeq (n + 1) := by
    simpa only [uSeq, extendFiniteControl_apply] using
      (finiteControlledOrbitFrom_restrict_eq
        (controlledCivicWeightedOrbitFrom_isControlled p rho z.1 uSeq)
        (T := n + 1) le_rfl)
  have hmatched :
      finiteControlledOrbit p rho (policyMatchedControl p rho z.1 u) (n + 1) =
        policyMatchedOrbit p rho z.1 uSeq (n + 1) := by
    rw [← finiteControlledOrbitFrom_calibratedPoint]
    exact finiteControlledOrbitFrom_policyMatchedControl
      model rho z.1 u le_rfl
  have hstock := policyMatchedOrbit_stock_geometric_bound
    model rho z.2 uSeq n
  have hfactor0 : 0 ≤ 1 - p.lambda₀ :=
    sub_nonneg.mpr model.lambda₀_lt_one.le
  have hfactor1 : 1 - p.lambda₀ ≤ 1 := by linarith [model.lambda₀_pos]
  have hpow : (1 - p.lambda₀) ^ n ≤ 1 :=
    pow_le_one₀ hfactor0 hfactor1
  have hconstant : 0 ≤ policyMatchingInitialStockConstant p :=
    (policyMatchingInitialStockConstant_pos model).le
  have hdistance : 0 ≤ dist z (calibratedPointInBox p model) := dist_nonneg
  change dist
      (finiteControlledOrbitFromInBox model rho z u (n + 1)).1
      (finiteControlledOrbitInBox model rho
        (policyMatchedControl p rho z.1 u) (n + 1)).1 ≤ _
  rw [finiteControlledOrbitFromInBox_val]
  change dist
    (finiteControlledOrbitFrom p rho z.1 u (n + 1))
    (finiteControlledOrbit p rho
      (policyMatchedControl p rho z.1 u) (n + 1)) ≤ _
  rw [horiginal, hmatched, Prod.dist_eq,
    policyMatchedOrbit_policy_succ]
  simp only [dist_self, Real.dist_eq]
  rw [max_eq_right (abs_nonneg _)]
  calc
    |(controlledCivicWeightedOrbitFrom p rho z.1 uSeq (n + 1)).2 -
        (policyMatchedOrbit p rho z.1 uSeq (n + 1)).2| ≤
        (1 - p.lambda₀) ^ n * policyMatchingInitialStockConstant p *
          dist z.1 (calibratedPoint p) := hstock
    _ ≤ policyMatchingInitialStockConstant p *
          dist z (calibratedPointInBox p model) := by
      have hsubtype : dist z.1 (calibratedPoint p) =
          dist z (calibratedPointInBox p model) := rfl
      rw [hsubtype]
      nlinarith [mul_nonneg hconstant hdistance]

/-- A boundary target consists of the complement together with the closed
inner layer whose distance to the complement is at most `eta`. -/
def calibratedBasinBoundaryTarget
    (p : LoopParams) (rho eta : ℝ) : Set (LoopBox p) :=
  {x | Metric.infDist x
    (civicWeightedCalibratedBasinInBox p rho)ᶜ ≤ eta}

/-- The boundary target is relatively closed in the invariant box. -/
theorem calibratedBasinBoundaryTarget_isClosed
    (p : LoopParams) (rho eta : ℝ) :
    IsClosed (calibratedBasinBoundaryTarget p rho eta) := by
  exact isClosed_Iic.preimage
    (Metric.continuous_infDist_pt
      (civicWeightedCalibratedBasinInBox p rho)ᶜ)

/-- For every positive loss, one can choose a closed inner target and a home
radius such that the home ball is disjoint from the target and every finite
target-reaching path from any home-ball start pays at least `V - delta`.
Both radii and the action statement are uniform in the path horizon. -/
theorem exists_uniform_nearby_boundaryTarget_action_lower
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho delta : ℝ} (hrho : 0 ≤ rho)
    (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (ssplus : WeightedConvergentStepAssumption p rho)
    (weighted : WeightedThresholdAssumption p rho)
    (hdelta : 0 < delta) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ home : ℝ, 0 < home ∧ home ≤ 1 ∧
      (∀ z : LoopBox p,
        dist z (calibratedPointInBox p model) ≤ home →
          eta < Metric.infDist z
            (civicWeightedCalibratedBasinInBox p rho)ᶜ) ∧
      ∀ (z : LoopBox p),
        dist z (calibratedPointInBox p model) ≤ home →
        ∀ {T : ℕ} (u : Fin T → ℝ), 1 ≤ T →
          finiteControlledOrbitFromInBox model rho z u T ∈
              calibratedBasinBoundaryTarget p rho eta →
            civicQuasipotential p rho - delta ≤ finiteQuadraticAction u := by
  have hquarter : 0 < delta / 4 := div_pos hdelta (by norm_num)
  obtain ⟨boundaryWidth, hboundaryWidth, hboundary⟩ :=
    quasipotential_le_action_add_of_terminal_in_boundaryLayer
      model threshold hrho hrhoCure hcoop ssplus weighted hquarter
  have hbasinOpen : IsOpen (civicWeightedCalibratedBasinInBox p rho) :=
    civicWeightedCalibratedBasinInBox_isOpen model ss threshold hrho
  have hcalibrated : calibratedPointInBox p model ∈
      civicWeightedCalibratedBasinInBox p rho := by
    exact calibratedPoint_mem_civicWeightedCalibratedBasin
      model threshold hrho
  have hcompl :
      (civicWeightedCalibratedBasinInBox p rho)ᶜ.Nonempty :=
    ⟨weightedSaddlePointInBox model weighted,
      weightedSaddlePoint_not_mem_calibratedBasinInBox model weighted⟩
  let clearance : ℝ := Metric.infDist (calibratedPointInBox p model)
    (civicWeightedCalibratedBasinInBox p rho)ᶜ
  have hclearance : 0 < clearance := by
    exact (hbasinOpen.isClosed_compl.notMem_iff_infDist_pos hcompl).mp
      (by simpa only [mem_compl_iff, not_not] using hcalibrated)
  let V : ℝ := civicQuasipotential p rho
  have hV0 : 0 ≤ V := by
    simpa only [V] using civicQuasipotential_nonneg
      model ss hrho hrhoCure
  let B : ℝ := V + 1
  obtain ⟨matchingRadius, hmatchingRadius, hmatchingOne,
      _hmatchingSaddle, hmatchingError⟩ :=
    exists_policyMatching_radius model weighted B hquarter
  let C : ℝ := policyMatchingInitialStockConstant p
  have hC : 0 < C := policyMatchingInitialStockConstant_pos model
  let eta : ℝ := min (boundaryWidth / 4) (clearance / 4)
  have heta : 0 < eta := by
    dsimp only [eta]
    exact lt_min (div_pos hboundaryWidth (by norm_num))
      (div_pos hclearance (by norm_num))
  have hetaBoundary : eta ≤ boundaryWidth / 4 := min_le_left _ _
  have hetaClearance : eta ≤ clearance / 4 := min_le_right _ _
  let transportRadius : ℝ := boundaryWidth / (4 * C)
  have htransportRadius : 0 < transportRadius := by
    dsimp only [transportRadius]
    exact div_pos hboundaryWidth (mul_pos (by norm_num) hC)
  let home : ℝ := min matchingRadius
    (min (clearance / 4) transportRadius)
  have hhome : 0 < home := by
    dsimp only [home]
    rw [lt_min_iff, lt_min_iff]
    exact ⟨hmatchingRadius, div_pos hclearance (by norm_num),
      htransportRadius⟩
  have hhomeMatching : home ≤ matchingRadius := min_le_left _ _
  have hhomeClearance : home ≤ clearance / 4 :=
    (min_le_right matchingRadius _).trans (min_le_left _ _)
  have hhomeTransport : home ≤ transportRadius :=
    (min_le_right matchingRadius _).trans (min_le_right _ _)
  have hhomeOne : home ≤ 1 := hhomeMatching.trans hmatchingOne
  refine ⟨eta, heta, home, hhome, hhomeOne, ?_, ?_⟩
  · intro z hz
    have hinf := Metric.infDist_le_infDist_add_dist
      (x := calibratedPointInBox p model) (y := z)
      (s := (civicWeightedCalibratedBasinInBox p rho)ᶜ)
    have hdist : dist (calibratedPointInBox p model) z ≤ clearance / 4 := by
      rw [dist_comm]
      exact hz.trans hhomeClearance
    linarith
  · intro z hz T u hT huTarget
    let matched : Fin T → ℝ := policyMatchedControl p rho z.1 u
    let originalEndpoint : LoopBox p :=
      finiteControlledOrbitFromInBox model rho z u T
    let matchedEndpoint : LoopBox p :=
      finiteControlledOrbitInBox model rho matched T
    have hendpointDistance :
        dist originalEndpoint matchedEndpoint ≤ C * home := by
      dsimp only [originalEndpoint, matchedEndpoint, matched, C]
      exact (finiteControlledOrbitFromInBox_dist_policyMatched_le
        model rho z u hT).trans
          (mul_le_mul_of_nonneg_left hz hC.le)
    have htransport : C * home ≤ boundaryWidth / 4 := by
      have hscaled := mul_le_mul_of_nonneg_left hhomeTransport hC.le
      dsimp only [transportRadius] at hscaled
      have hcancel : C * (boundaryWidth / (4 * C)) =
          boundaryWidth / 4 := by field_simp [hC.ne']
      rwa [hcancel] at hscaled
    have horiginalTarget : Metric.infDist originalEndpoint
        (civicWeightedCalibratedBasinInBox p rho)ᶜ ≤ eta := huTarget
    have hmatchedNear : Metric.infDist matchedEndpoint
        (civicWeightedCalibratedBasinInBox p rho)ᶜ < boundaryWidth := by
      have hinf := Metric.infDist_le_infDist_add_dist
        (x := matchedEndpoint) (y := originalEndpoint)
        (s := (civicWeightedCalibratedBasinInBox p rho)ᶜ)
      have hdistComm : dist matchedEndpoint originalEndpoint ≤
          boundaryWidth / 4 := by
        rw [dist_comm]
        exact hendpointDistance.trans htransport
      linarith
    by_cases hlarge : B ≤ finiteQuadraticAction u
    · dsimp only [B, V] at hlarge ⊢
      linarith
    · have huB : finiteQuadraticAction u ≤ B :=
        (lt_of_not_ge hlarge).le
      have hmatchedAction' :
          finiteQuadraticAction matched ≤
            finiteQuadraticAction u +
              policyMatchingActionConstant p rho * home *
                (1 + √(2 * B)) := by
        simpa only [matched, finiteQuadraticAction, gaussianVectorAction] using
          gaussianVectorAction_policyMatchedControl_le_of_le
            model rho z.2 hz hhomeOne u huB
      have herror : policyMatchingActionConstant p rho * home *
          (1 + √(2 * B)) < delta / 4 := by
        have hconstant : 0 ≤ policyMatchingActionConstant p rho :=
          policyMatchingActionConstant_nonneg model rho
        have hroot : 0 ≤ 1 + √(2 * B) :=
          add_nonneg zero_le_one (Real.sqrt_nonneg _)
        have hmono : policyMatchingActionConstant p rho * home *
            (1 + √(2 * B)) ≤
          policyMatchingActionConstant p rho * matchingRadius *
            (1 + √(2 * B)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hhomeMatching hconstant) hroot
        exact hmono.trans_lt hmatchingError
      have hVmatched : civicQuasipotential p rho ≤
          finiteQuadraticAction matched + delta / 4 := by
        by_cases hyBasin : matchedEndpoint ∈
            civicWeightedCalibratedBasinInBox p rho
        · have hlocal := hboundary matched
          rw [finiteControlOrbitInBox_eq_finiteControlledOrbitInBox] at hlocal
          have hlocal' := hlocal hyBasin hmatchedNear
          simpa only [matched, finiteQuadraticAction] using hlocal'
        · have hyExit : finiteControlledOrbit p rho matched T ∉
              civicWeightedCalibratedBasin p rho := by
            simpa only [matchedEndpoint, finiteControlledOrbitInBox,
              mem_civicWeightedCalibratedBasinInBox_iff] using hyBasin
          have hbarrier :=
            civicQuasipotential_le_gaussianVectorAction_of_terminal_basinExit
              model hyExit
          simpa only [finiteQuadraticAction, gaussianVectorAction] using
            hbarrier.trans (le_add_of_nonneg_right hquarter.le)
      linarith

/-! ## Boundary-target excursions -/

/-- The restricted noisy recursion from an arbitrary state of the invariant
box. -/
def gaussianNoisyOrbitFromInBox
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    (x₀ : LoopBox p) (sigma : ℝ) (xi : GaussianNoisePath) :
    ℕ → LoopBox p :=
  controlOrbit (controlledCivicWeightedStepInBox model rho) x₀
    (fun n ↦ sigma * xi n)

/-- The canonical invariant-box noisy orbit is the restricted controlled
recursion from the calibrated corner. -/
theorem gaussianNoisyOrbitInBox_eq_controlOrbit
    {p : LoopParams} (model : DriftModelAssumptions p)
    (rho sigma : ℝ) (xi : GaussianNoisePath) (n : ℕ) :
    gaussianNoisyOrbitInBox model rho sigma xi n =
      controlOrbit (controlledCivicWeightedStepInBox model rho)
        (calibratedPointInBox p model) (fun k ↦ sigma * xi k) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      apply Subtype.ext
      change controlledCivicWeightedStep p rho (sigma * xi n)
          (gaussianNoisyOrbitInBox model rho sigma xi n).1 =
        controlledCivicWeightedStep p rho (sigma * xi n)
          (controlOrbit (controlledCivicWeightedStepInBox model rho)
            (calibratedPointInBox p model) (fun k ↦ sigma * xi k) n).1
      rw [ih]

/-- Restarting the restricted noisy recursion at a deterministic time and
feeding it the shifted noise history reproduces the canonical orbit. -/
theorem gaussianNoisyOrbitFromInBox_tail_eq
    {p : LoopParams} (model : DriftModelAssumptions p)
    (rho sigma : ℝ) (xi : GaussianNoisePath) (M n : ℕ) :
    gaussianNoisyOrbitFromInBox model rho
        (gaussianNoisyOrbitInBox model rho sigma xi M)
        sigma (gaussianTail M xi) n =
      gaussianNoisyOrbitInBox model rho sigma xi (M + n) := by
  rw [gaussianNoisyOrbitInBox_eq_controlOrbit]
  rw [gaussianNoisyOrbitInBox_eq_controlOrbit]
  rw [controlOrbit_add]
  rfl

/-- A finite Gaussian prefix reproduces the arbitrary-start restricted noisy
recursion through its horizon. -/
theorem finiteControlOrbit_scaledPrefix_eq_gaussianNoisyOrbitFromInBox
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    (x₀ : LoopBox p) (sigma : ℝ) (xi : GaussianNoisePath)
    {T n : ℕ} (hn : n ≤ T) :
    finiteControlOrbit (controlledCivicWeightedStepInBox model rho) x₀
        (scaledGaussianControl sigma (gaussianPrefix T xi)) n =
      gaussianNoisyOrbitFromInBox model rho x₀ sigma xi n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hnlt : n < T := by omega
      rw [finiteControlOrbit, gaussianNoisyOrbitFromInBox, controlOrbit,
        ih (by omega)]
      simp only [finiteControlValue, hnlt, dite_true,
        scaledGaussianControl, gaussianPrefix]
      rfl

/-- At every fixed time, the arbitrary-start restricted noisy recursion is a
continuous function of the infinite noise history. -/
theorem continuous_gaussianNoisyOrbitFromInBox
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    (x₀ : LoopBox p) (sigma : ℝ) (n : ℕ) :
    Continuous (fun xi : GaussianNoisePath ↦
      gaussianNoisyOrbitFromInBox model rho x₀ sigma xi n) := by
  induction n with
  | zero =>
      simp only [gaussianNoisyOrbitFromInBox, controlOrbit]
      fun_prop
  | succ n ih =>
      change Continuous (fun xi : GaussianNoisePath ↦
        controlledCivicWeightedStepInBox model rho (sigma * xi n)
          (gaussianNoisyOrbitFromInBox model rho x₀ sigma xi n))
      have hpair : Continuous (fun xi : GaussianNoisePath ↦
          ((sigma * xi n,
            gaussianNoisyOrbitFromInBox model rho x₀ sigma xi n) :
            ℝ × LoopBox p)) := by
        fun_prop
      exact (continuous_uncurry_controlledCivicWeightedStepInBox
        model rho).comp hpair

/-- A home-to-boundary excursion completes at time `n`: it reaches the
closed boundary target then, while every positive-time state through `n`
lies outside the closed home ball. -/
def basinBoundaryExcursionAtTimeEvent
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    (z : LoopBox p) (sigma home eta : ℝ) (n : ℕ) :
    Set GaussianNoisePath :=
  {xi | 1 ≤ n ∧
    gaussianNoisyOrbitFromInBox model rho z sigma xi n ∈
      calibratedBasinBoundaryTarget p rho eta ∧
    ∀ k ∈ Finset.Icc 1 n,
      home < dist
        (gaussianNoisyOrbitFromInBox model rho z sigma xi k)
        (calibratedPointInBox p model)}

/-- A complete home-to-boundary excursion has some finite positive
completion time. -/
def basinBoundaryExcursionEvent
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    (z : LoopBox p) (sigma home eta : ℝ) : Set GaussianNoisePath :=
  ⋃ n : ℕ,
    basinBoundaryExcursionAtTimeEvent model rho z sigma home eta n

/-- Literal membership semantics for a complete boundary-target excursion. -/
theorem mem_basinBoundaryExcursionEvent_iff
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    (z : LoopBox p) (sigma home eta : ℝ) (xi : GaussianNoisePath) :
    xi ∈ basinBoundaryExcursionEvent model rho z sigma home eta ↔
      ∃ n : ℕ, 1 ≤ n ∧
        gaussianNoisyOrbitFromInBox model rho z sigma xi n ∈
          calibratedBasinBoundaryTarget p rho eta ∧
        ∀ k ∈ Finset.Icc 1 n,
          home < dist
            (gaussianNoisyOrbitFromInBox model rho z sigma xi k)
            (calibratedPointInBox p model) := by
  simp only [basinBoundaryExcursionEvent, mem_iUnion,
    basinBoundaryExcursionAtTimeEvent, mem_setOf_eq]

/-- The exact-time boundary-target excursion event is Borel measurable. -/
theorem measurableSet_basinBoundaryExcursionAtTimeEvent
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    (z : LoopBox p) (sigma home eta : ℝ) (n : ℕ) :
    MeasurableSet
      (basinBoundaryExcursionAtTimeEvent
        model rho z sigma home eta n) := by
  by_cases hn : 1 ≤ n
  · have htarget : MeasurableSet
        {xi : GaussianNoisePath |
          gaussianNoisyOrbitFromInBox model rho z sigma xi n ∈
            calibratedBasinBoundaryTarget p rho eta} :=
      (calibratedBasinBoundaryTarget_isClosed p rho eta).measurableSet.preimage
        (continuous_gaussianNoisyOrbitFromInBox
          model rho z sigma n).measurable
    have hout : ∀ k : ℕ, MeasurableSet
        {xi : GaussianNoisePath | home < dist
          (gaussianNoisyOrbitFromInBox model rho z sigma xi k)
          (calibratedPointInBox p model)} := by
      intro k
      exact measurableSet_Ioi.preimage
        ((continuous_gaussianNoisyOrbitFromInBox
          model rho z sigma k).dist continuous_const).measurable
    rw [show basinBoundaryExcursionAtTimeEvent
          model rho z sigma home eta n =
        {xi : GaussianNoisePath |
          gaussianNoisyOrbitFromInBox model rho z sigma xi n ∈
            calibratedBasinBoundaryTarget p rho eta} ∩
          ⋂ k ∈ Finset.Icc 1 n,
            {xi : GaussianNoisePath | home < dist
              (gaussianNoisyOrbitFromInBox model rho z sigma xi k)
              (calibratedPointInBox p model)} by
      ext xi
      simp only [basinBoundaryExcursionAtTimeEvent, mem_setOf_eq,
        mem_inter_iff, mem_iInter, hn, true_and]]
    exact htarget.inter
      (Finset.measurableSet_biInter (Finset.Icc 1 n) fun k _hk ↦ hout k)
  · have hempty : basinBoundaryExcursionAtTimeEvent
        model rho z sigma home eta n = ∅ := by
      ext xi
      simp only [basinBoundaryExcursionAtTimeEvent, mem_setOf_eq,
        mem_empty_iff_false, iff_false]
      exact fun h ↦ hn h.1
    rw [hempty]
    exact MeasurableSet.empty

/-- The unrestricted boundary-target excursion event is measurable. -/
theorem measurableSet_basinBoundaryExcursionEvent
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    (z : LoopBox p) (sigma home eta : ℝ) :
    MeasurableSet
      (basinBoundaryExcursionEvent model rho z sigma home eta) :=
  MeasurableSet.iUnion fun n ↦
    measurableSet_basinBoundaryExcursionAtTimeEvent
      model rho z sigma home eta n

set_option maxHeartbeats 800000 in
-- The excursion dichotomy combines compact-core block accounting with the
-- transported boundary charge and exceeds the default elaboration budget.
/-- Every positive rate loss admits a home ball, a closed boundary target,
and one fixed Gaussian dimension which contain every complete excursion in
the corresponding action tail.  Long excursions pay through core blocks;
short excursions pay through the transported boundary charge. -/
theorem exists_basinBoundaryExcursionEvent_subset_actionTail
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho delta : ℝ} (hrho : 0 ≤ rho)
    (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (ssplus : WeightedConvergentStepAssumption p rho)
    (weighted : WeightedThresholdAssumption p rho)
    (hdelta : 0 < delta) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ home : ℝ, 0 < home ∧
      ∃ H : ℕ,
        (∀ z : LoopBox p,
          dist z (calibratedPointInBox p model) ≤ home →
            eta < Metric.infDist z
              (civicWeightedCalibratedBasinInBox p rho)ᶜ) ∧
        ∀ (z : LoopBox p),
          dist z (calibratedPointInBox p model) ≤ home →
          ∀ {sigma : ℝ}, sigma ≠ 0 →
            basinBoundaryExcursionEvent model rho z sigma home eta ⊆
              gaussianPrefixActionTailEvent H
                ((civicQuasipotential p rho - delta) / sigma ^ 2) := by
  classical
  obtain ⟨eta, heta, home, hhome, _hhomeOne,
      hhomeTargetFree, hnearAction⟩ :=
    exists_uniform_nearby_boundaryTarget_action_lower
      model ss threshold hrho hrhoCure hcoop ssplus weighted hdelta
  obtain ⟨N, c, hc, hlinear⟩ :=
    exists_uniform_linear_action_cost_on_calibratedBasinCoreInBox
      model rho heta (half_pos hhome) (half_lt_self hhome)
  let stride : ℕ := N + 1
  let base : ℝ := civicQuasipotential p rho - delta
  let K : ℕ := ⌈max 0 base / c⌉₊
  let H : ℕ := (K + 1) * stride
  have hbaseK : base ≤ (K : ℝ) * c := by
    have hceil : max 0 base / c ≤ (K : ℝ) := Nat.le_ceil _
    have hmul : max 0 base ≤ (K : ℝ) * c := by
      have hscaled := mul_le_mul_of_nonneg_right hceil hc.le
      calc
        max 0 base = (max 0 base / c) * c := by
          field_simp [hc.ne']
        _ ≤ (K : ℝ) * c := hscaled
    exact (le_max_right 0 base).trans hmul
  refine ⟨eta, heta, home, hhome, H, hhomeTargetFree, ?_⟩
  intro z hz sigma hsigma xi hxi
  obtain ⟨n, hn1, hnTarget, hnHome⟩ :=
    (mem_basinBoundaryExcursionEvent_iff
      model rho z sigma home eta xi).1 hxi
  let target : ℕ → Prop := fun m ↦
    gaussianNoisyOrbitFromInBox model rho z sigma xi m ∈
      calibratedBasinBoundaryTarget p rho eta
  have hex : ∃ m, target m := ⟨n, hnTarget⟩
  let first : ℕ := Nat.find hex
  have hfirstTarget : target first := Nat.find_spec hex
  have hfirstLe : first ≤ n := Nat.find_min' hex hnTarget
  have hfirst1 : 1 ≤ first := by
    by_contra hnot
    have hzero : first = 0 := Nat.eq_zero_of_not_pos hnot
    have htarget0 : Metric.infDist z
        (civicWeightedCalibratedBasinInBox p rho)ᶜ ≤ eta := by
      have hmem : target 0 := hzero ▸ hfirstTarget
      simpa only [target, calibratedBasinBoundaryTarget,
        gaussianNoisyOrbitFromInBox, controlOrbit, mem_setOf_eq] using hmem
    exact (not_lt_of_ge htarget0) (hhomeTargetFree z hz)
  let uSeq : ℕ → ℝ := fun k ↦ sigma * xi k
  let x : ℕ → LoopBox p :=
    gaussianNoisyOrbitFromInBox model rho z sigma xi
  have hxControl : x = controlOrbit
      (controlledCivicWeightedStepInBox model rho) z uSeq := rfl
  have hscaled : quadraticActionPrefix uSeq H =
      sigma ^ 2 * gaussianVectorAction (gaussianPrefix H xi) := by
    change controlAction uSeq H = _
    rw [← gaussianVectorAction_restrict uSeq H]
    change gaussianVectorAction
      (scaledGaussianControl sigma (gaussianPrefix H xi)) = _
    exact gaussianVectorAction_scaledGaussianControl
      sigma (gaussianPrefix H xi)
  have htailMembership : base ≤ quadraticActionPrefix uSeq H →
      xi ∈ gaussianPrefixActionTailEvent H (base / sigma ^ 2) := by
    intro hpay
    apply (div_le_iff₀ (sq_pos_of_ne_zero hsigma)).2
    rw [hscaled] at hpay
    simpa only [mul_comm] using hpay
  by_cases hfirstShort : first ≤ H
  · let uFirst : Fin first → ℝ := fun i ↦ uSeq i
    have hendpoint : finiteControlOrbit
        (controlledCivicWeightedStepInBox model rho) z uFirst first =
          x first := by
      have hu : uFirst =
          scaledGaussianControl sigma (gaussianPrefix first xi) := by
        funext i
        rfl
      rw [hu]
      simpa only [x] using
        (finiteControlOrbit_scaledPrefix_eq_gaussianNoisyOrbitFromInBox
          model rho z sigma xi (T := first) le_rfl)
    have htargetFinite : finiteControlledOrbitFromInBox
        model rho z uFirst first ∈
          calibratedBasinBoundaryTarget p rho eta := by
      simpa only [finiteControlledOrbitFromInBox, hendpoint] using
        hfirstTarget
    have hpay := hnearAction z hz uFirst hfirst1 htargetFinite
    apply htailMembership
    calc
      base ≤ finiteQuadraticAction uFirst := by simpa only [base] using hpay
      _ = quadraticActionPrefix uSeq first := by
        simpa only [uFirst, Nat.zero_add] using
          finiteQuadraticAction_slice_eq uSeq 0 first
      _ ≤ quadraticActionPrefix uSeq H := by
        change controlAction uSeq first ≤ controlAction uSeq H
        exact controlAction_mono hfirstShort
  · have hHfirst : H < first := lt_of_not_ge hfirstShort
    let shifted : ℕ → ℝ := fun k ↦ uSeq (stride + k)
    let z₁ : LoopBox p := x stride
    have hrestart : ∀ m,
        controlOrbit (controlledCivicWeightedStepInBox model rho)
            z₁ shifted m = x (stride + m) := by
      intro m
      dsimp only [z₁, shifted]
      rw [hxControl, ← controlOrbit_add]
    have hstarts : ∀ j < K,
        controlOrbit (controlledCivicWeightedStepInBox model rho)
            z₁ shifted (j * stride) ∈
          calibratedBasinCoreInBox p rho eta := by
      intro j hj
      rw [hrestart]
      have htime : stride + j * stride < first := by
        have hle : stride + j * stride ≤ K * stride := by
          have hj1 : j + 1 ≤ K := Nat.succ_le_of_lt hj
          calc
            stride + j * stride = (j + 1) * stride := by ring
            _ ≤ K * stride := Nat.mul_le_mul_right stride hj1
        have hKH : K * stride < H := by
          dsimp only [H]
          have hstride : 0 < stride := by dsimp only [stride]; omega
          nlinarith
        exact hle.trans_lt (hKH.trans hHfirst)
      have hnot := Nat.find_min hex htime
      change ¬target (stride + j * stride) at hnot
      change eta ≤ Metric.infDist (x (stride + j * stride))
        (civicWeightedCalibratedBasinInBox p rho)ᶜ
      exact (lt_of_not_ge hnot).le
    have havoid : ∀ m < K * stride,
        home ≤ dist
          (controlOrbit (controlledCivicWeightedStepInBox model rho)
            z₁ shifted m) (calibratedPointInBox p model) := by
      intro m hm
      rw [hrestart]
      have htime1 : 1 ≤ stride + m := by
        dsimp only [stride]
        omega
      have htimeFirst : stride + m < first := by
        have htimeH : stride + m < H := by
          calc
            stride + m < stride + K * stride :=
              Nat.add_lt_add_left hm stride
            _ = (K + 1) * stride := by ring
            _ = H := rfl
        exact htimeH.trans hHfirst
      have htimeN : stride + m ≤ n :=
        htimeFirst.le.trans hfirstLe
      exact (hnHome (stride + m)
        (Finset.mem_Icc.mpr ⟨htime1, htimeN⟩)).le
    have hcharged := hlinear K z₁ shifted hstarts havoid
    have hcharged' : (K : ℝ) * c ≤
        controlIntervalAction uSeq stride (K * stride) := by
      change (K : ℝ) * c ≤ controlAction shifted (K * stride) at hcharged
      rw [controlAction_shift_eq_controlIntervalAction] at hcharged
      exact hcharged
    have hinterval : controlIntervalAction uSeq stride (K * stride) ≤
        controlAction uSeq H := by
      apply controlIntervalAction_le_controlAction
      dsimp only [H]
      ring_nf
      exact le_rfl
    apply htailMembership
    change base ≤ controlAction uSeq H
    exact hbaseK.trans (hcharged'.trans hinterval)

/-! ## Last-visit decomposition on the canonical process -/

/-- At deterministic time `M`, the process is in the closed home ball and
its shifted future completes a boundary-target excursion. -/
def lastExitBasinBoundaryEvent
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    (sigma home eta : ℝ) (M : ℕ) : Set GaussianNoisePath :=
  {xi |
    let z := gaussianNoisyOrbitInBox model rho sigma xi M
    dist z (calibratedPointInBox p model) ≤ home ∧
      gaussianTail M xi ∈
        basinBoundaryExcursionEvent model rho z sigma home eta}

/-- A uniform arbitrary-start excursion inclusion transfers pathwise to every
deterministic last-home time. -/
theorem lastExitBasinBoundaryEvent_subset_tail_actionTail
    {p : LoopParams} (model : DriftModelAssumptions p) {rho : ℝ}
    {sigma home eta base : ℝ} {H : ℕ}
    (hset : ∀ z : LoopBox p,
      dist z (calibratedPointInBox p model) ≤ home →
        basinBoundaryExcursionEvent model rho z sigma home eta ⊆
          gaussianPrefixActionTailEvent H (base / sigma ^ 2))
    (M : ℕ) :
    lastExitBasinBoundaryEvent model rho sigma home eta M ⊆
      gaussianTail M ⁻¹'
        gaussianPrefixActionTailEvent H (base / sigma ^ 2) := by
  intro xi hxi
  exact hset _ hxi.1 hxi.2

/-- Every deterministic last-home event obeys the same fixed-dimensional
Chernoff bound, independently of its location in the global history. -/
theorem lastExitBasinBoundaryEvent_probability_le_chernoff
    {p : LoopParams} (model : DriftModelAssumptions p) {rho : ℝ}
    {sigma home eta base t : ℝ} {H : ℕ}
    (hset : ∀ z : LoopBox p,
      dist z (calibratedPointInBox p model) ≤ home →
        basinBoundaryExcursionEvent model rho z sigma home eta ⊆
          gaussianPrefixActionTailEvent H (base / sigma ^ 2))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (M : ℕ) :
    standardGaussianSequence
        (lastExitBasinBoundaryEvent model rho sigma home eta M) ≤
      ENNReal.ofReal
        (Real.exp (-t * (base / sigma ^ 2)) *
          mgf gaussianVectorAction (standardGaussianVector H) t) := by
  calc
    standardGaussianSequence
        (lastExitBasinBoundaryEvent model rho sigma home eta M) ≤
        standardGaussianSequence
          (gaussianTail M ⁻¹'
            gaussianPrefixActionTailEvent H (base / sigma ^ 2)) :=
      measure_mono
        (lastExitBasinBoundaryEvent_subset_tail_actionTail model hset M)
    _ = standardGaussianSequence
          (gaussianPrefixActionTailEvent H (base / sigma ^ 2)) :=
      standardGaussianSequence_tail_preimage M
        (measurableSet_gaussianPrefixActionTailEvent H (base / sigma ^ 2))
    _ = gaussianActionTailProbability H (base / sigma ^ 2) :=
      standardGaussianSequence_gaussianPrefixActionTailEvent _ _
    _ ≤ ENNReal.ofReal
          (Real.exp (-t * (base / sigma ^ 2)) *
            mgf gaussianVectorAction (standardGaussianVector H) t) := by
      simpa only [mgf_gaussianVectorAction_eq_pow] using
        (gaussianActionTailProbability_le_chernoff
          H (B := base / sigma ^ 2) ht0 ht1)

/-- Any genuine basin exit by time `N` has a first boundary-target entrance.
The last visit to the home ball before that entrance starts one of the
deterministic-time excursion events above. -/
theorem gaussianBasinExitByEvent_subset_lastExitBasinBoundary
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho sigma home eta : ℝ} (hrho : 0 ≤ rho)
    (hhome : 0 ≤ home) (heta : 0 ≤ eta)
    (hhomeTargetFree : ∀ z : LoopBox p,
      dist z (calibratedPointInBox p model) ≤ home →
        eta < Metric.infDist z
          (civicWeightedCalibratedBasinInBox p rho)ᶜ)
    (N : ℕ) :
    gaussianBasinExitByEvent model ss threshold hrho N sigma ⊆
      ⋃ M ∈ Finset.range (N + 1),
        lastExitBasinBoundaryEvent model rho sigma home eta M := by
  classical
  intro xi hescape
  let x : ℕ → LoopBox p := gaussianNoisyOrbitInBox model rho sigma xi
  have hx0 : x 0 = calibratedPointInBox p model := by
    apply Subtype.ext
    rfl
  obtain ⟨n, hnN, hnExit⟩ := hescape
  have hnTarget : x n ∈ calibratedBasinBoundaryTarget p rho eta := by
    change Metric.infDist (x n)
      (civicWeightedCalibratedBasinInBox p rho)ᶜ ≤ eta
    have hzero : Metric.infDist (x n)
        (civicWeightedCalibratedBasinInBox p rho)ᶜ = 0 :=
      Metric.infDist_zero_of_mem (show x n ∈
        (civicWeightedCalibratedBasinInBox p rho)ᶜ from hnExit)
    rw [hzero]
    exact heta
  let target : ℕ → Prop := fun k ↦
    x k ∈ calibratedBasinBoundaryTarget p rho eta
  have hex : ∃ k, target k := ⟨n, hnTarget⟩
  let first : ℕ := Nat.find hex
  have hfirstTarget : target first := Nat.find_spec hex
  have hfirstN : first ≤ N :=
    (Nat.find_min' hex hnTarget).trans (by
      simp only [Finset.mem_range] at hnN
      omega)
  have hfirst1 : 1 ≤ first := by
    by_contra hnot
    have hzero : first = 0 := Nat.eq_zero_of_not_pos hnot
    have htarget0 : Metric.infDist (calibratedPointInBox p model)
        (civicWeightedCalibratedBasinInBox p rho)ᶜ ≤ eta := by
      have hmem : target 0 := hzero ▸ hfirstTarget
      have hmem' : Metric.infDist (x 0)
          (civicWeightedCalibratedBasinInBox p rho)ᶜ ≤ eta := by
        simpa only [target, calibratedBasinBoundaryTarget,
          mem_setOf_eq] using hmem
      rwa [hx0] at hmem'
    exact (not_lt_of_ge htarget0)
      (hhomeTargetFree (calibratedPointInBox p model) (by
        rw [dist_self]
        exact hhome))
  let homeAt : ℕ → Prop := fun k ↦
    dist (x k) (calibratedPointInBox p model) ≤ home
  have hhome0 : homeAt 0 := by
    dsimp only [homeAt]
    rw [hx0, dist_self]
    exact hhome
  let last : ℕ := Nat.findGreatest homeAt first
  have hlastHome : homeAt last :=
    Nat.findGreatest_spec (Nat.zero_le first) hhome0
  have hlastLe : last ≤ first := Nat.findGreatest_le _
  have hfirstNotHome : ¬homeAt first := by
    intro hfirstHome
    have hfar := hhomeTargetFree (x first) hfirstHome
    have hnear : Metric.infDist (x first)
        (civicWeightedCalibratedBasinInBox p rho)ᶜ ≤ eta := by
      simpa only [target, calibratedBasinBoundaryTarget, mem_setOf_eq] using
        hfirstTarget
    exact (not_lt_of_ge hnear) hfar
  have hlastFirst : last < first :=
    hlastLe.lt_of_ne (fun h ↦ hfirstNotHome (h ▸ hlastHome))
  have hlastN : last ∈ Finset.range (N + 1) := by
    simp only [Finset.mem_range]
    omega
  apply mem_iUnion.2
  refine ⟨last, mem_iUnion.2 ⟨hlastN, ?_⟩⟩
  have hduration : 1 ≤ first - last := by omega
  have hrestart : gaussianTail last xi ∈
      basinBoundaryExcursionEvent model rho (x last)
        sigma home eta := by
    rw [mem_basinBoundaryExcursionEvent_iff]
    refine ⟨first - last, hduration, ?_, ?_⟩
    · have heq := gaussianNoisyOrbitFromInBox_tail_eq
        model rho sigma xi last (first - last)
      rw [Nat.add_sub_of_le hlastLe] at heq
      rw [heq]
      exact hfirstTarget
    · intro r hr
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
      have hrLe : r ≤ first - last := (Finset.mem_Icc.mp hr).2
      have hlastLt : last < last + r := by omega
      have haddLe : last + r ≤ first := by omega
      have hnotHome : ¬homeAt (last + r) :=
        Nat.findGreatest_is_greatest hlastLt haddLe
      have heq := gaussianNoisyOrbitFromInBox_tail_eq
        model rho sigma xi last r
      rw [heq]
      exact lt_of_not_ge hnotHome
  exact ⟨hlastHome, hrestart⟩

/-- The fixed-dimensional excursion tail and the last-home union bound price
genuine basin exit by every deterministic horizon. -/
theorem gaussianBasinExitProbability_le_lastExit_chernoff
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho sigma home eta base t : ℝ} (hrho : 0 ≤ rho) {H : ℕ}
    (hhome : 0 ≤ home) (heta : 0 ≤ eta)
    (hhomeTargetFree : ∀ z : LoopBox p,
      dist z (calibratedPointInBox p model) ≤ home →
        eta < Metric.infDist z
          (civicWeightedCalibratedBasinInBox p rho)ᶜ)
    (hset : ∀ z : LoopBox p,
      dist z (calibratedPointInBox p model) ≤ home →
        basinBoundaryExcursionEvent model rho z sigma home eta ⊆
          gaussianPrefixActionTailEvent H (base / sigma ^ 2))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (N : ℕ) :
    gaussianBasinExitProbability model ss threshold hrho N sigma ≤
      (N + 1 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-t * (base / sigma ^ 2)) *
            mgf gaussianVectorAction (standardGaussianVector H) t) := by
  rw [← standardGaussianSequence_basinExitByEvent
    model ss threshold hrho N sigma]
  calc
    standardGaussianSequence
        (gaussianBasinExitByEvent model ss threshold hrho N sigma) ≤
        standardGaussianSequence
          (⋃ M ∈ Finset.range (N + 1),
            lastExitBasinBoundaryEvent model rho sigma home eta M) :=
      measure_mono
        (gaussianBasinExitByEvent_subset_lastExitBasinBoundary
          model ss threshold hrho hhome heta hhomeTargetFree N)
    _ ≤ ∑ M ∈ Finset.range (N + 1),
          standardGaussianSequence
            (lastExitBasinBoundaryEvent
              model rho sigma home eta M) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _M ∈ Finset.range (N + 1),
          ENNReal.ofReal
            (Real.exp (-t * (base / sigma ^ 2)) *
              mgf gaussianVectorAction (standardGaussianVector H) t) := by
      exact Finset.sum_le_sum fun M _ ↦
        lastExitBasinBoundaryEvent_probability_le_chernoff
          model hset ht0 ht1 M
    _ = (N + 1 : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp (-t * (base / sigma ^ 2)) *
              mgf gaussianVectorAction (standardGaussianVector H) t) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      norm_cast

/-! ## Exponential persistence -/

/-- Whenever the requested exponential horizon rate is strictly below a
Chernoff fraction of `V - delta`, genuine basin exit by that horizon has
probability tending to zero. -/
theorem exponentialBasinExitProbability_tendsto_zero_of_rate_lt
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho delta rate t : ℝ} (hrho : 0 ≤ rho)
    (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (ssplus : WeightedConvergentStepAssumption p rho)
    (weighted : WeightedThresholdAssumption p rho)
    (hdelta : 0 < delta) (hrate : 0 < rate)
    (ht0 : 0 < t) (ht1 : t < 1)
    (hgap : rate < t * (civicQuasipotential p rho - delta)) :
    Tendsto
      (fun sigma : ℝ ↦ gaussianBasinExitProbability
        model ss threshold hrho
        (exponentialEscapeHorizon rate sigma) sigma)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
  obtain ⟨eta, heta, home, hhome, H, hhomeTargetFree, hset⟩ :=
    exists_basinBoundaryExcursionEvent_subset_actionTail
      model ss threshold hrho hrhoCure hcoop ssplus weighted hdelta
  let base : ℝ := civicQuasipotential p rho - delta
  let gap : ℝ := t * base - rate
  have hgapPos : 0 < gap := by
    dsimp only [gap, base]
    linarith
  have hmgf : 0 ≤
      mgf gaussianVectorAction (standardGaussianVector H) t := by
    rw [mgf_gaussianVectorAction_eq_pow]
    exact pow_nonneg (gaussianHalfSquareMgf_pos ht1).le H
  let majorant : ℝ → ℝ≥0∞ := fun sigma ↦
    ENNReal.ofReal
      (2 * mgf gaussianVectorAction (standardGaussianVector H) t *
        Real.exp (-gap / sigma ^ 2))
  have hbound : ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      gaussianBasinExitProbability model ss threshold hrho
          (exponentialEscapeHorizon rate sigma) sigma ≤ majorant sigma := by
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    have hsigmaNe : sigma ≠ 0 := ne_of_gt hsigma
    have hlocal : ∀ z : LoopBox p,
        dist z (calibratedPointInBox p model) ≤ home →
          basinBoundaryExcursionEvent model rho z sigma home eta ⊆
            gaussianPrefixActionTailEvent H (base / sigma ^ 2) := by
      intro z hz
      simpa only [base] using hset z hz hsigmaNe
    have hglobal := gaussianBasinExitProbability_le_lastExit_chernoff
      model ss threshold hrho hhome.le heta.le hhomeTargetFree hlocal
        ht0.le ht1 (exponentialEscapeHorizon rate sigma)
    have hhorizon := exponentialEscapeHorizon_add_one_le
      (sigma := sigma) hrate.le
    calc
      gaussianBasinExitProbability model ss threshold hrho
          (exponentialEscapeHorizon rate sigma) sigma ≤
          (exponentialEscapeHorizon rate sigma + 1 : ℝ≥0∞) *
            ENNReal.ofReal
              (Real.exp (-t * (base / sigma ^ 2)) *
                mgf gaussianVectorAction
                  (standardGaussianVector H) t) := by
        simpa only [base] using hglobal
      _ ≤ ENNReal.ofReal (2 * Real.exp (rate / sigma ^ 2)) *
            ENNReal.ofReal
              (Real.exp (-t * (base / sigma ^ 2)) *
                mgf gaussianVectorAction
                  (standardGaussianVector H) t) :=
        mul_le_mul' hhorizon le_rfl
      _ = majorant sigma := by
        dsimp only [majorant]
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have hexp :
          Real.exp (rate / sigma ^ 2) *
              Real.exp (-t * (base / sigma ^ 2)) =
            Real.exp (-gap / sigma ^ 2) := by
          rw [← Real.exp_add]
          congr 1
          dsimp only [gap]
          ring
        calc
          2 * Real.exp (rate / sigma ^ 2) *
              (Real.exp (-t * (base / sigma ^ 2)) *
                mgf gaussianVectorAction (standardGaussianVector H) t) =
            2 * mgf gaussianVectorAction (standardGaussianVector H) t *
              (Real.exp (rate / sigma ^ 2) *
                Real.exp (-t * (base / sigma ^ 2))) := by ring
          _ = 2 * mgf gaussianVectorAction
                (standardGaussianVector H) t *
              Real.exp (-gap / sigma ^ 2) := by rw [hexp]
  have hactivated := tendsto_exp_neg_const_div_sq_nhdsGT_zero hgapPos
  have hreal : Tendsto
      (fun sigma : ℝ ↦
        2 * mgf gaussianVectorAction (standardGaussianVector H) t *
          Real.exp (-gap / sigma ^ 2))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
    simpa using tendsto_const_nhds.mul hactivated
  have hmajorant : Tendsto majorant
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
    simpa only [majorant, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal hreal
  exact (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (0 : ℝ≥0∞))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0)).squeeze'
    hmajorant (Eventually.of_forall fun _ ↦ bot_le) hbound

/-- The basin quasipotential is strictly positive under the same Lipschitz
hypothesis used for the paper's crossing lower bound. -/
theorem civicQuasipotential_pos_of_lipschitz
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho L : ℝ} (hrho : 0 ≤ rho)
    (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    0 < civicQuasipotential p rho := by
  exact (civicCrossingQuasipotential_pos_of_lipschitz
    model ss hcoop weighted hL).trans_le
      (civicCrossingQuasipotential_le_civicQuasipotential
        model ss threshold hrho hrhoCure hcoop weighted)

/-- For every positive tolerance, genuine basin exit by
`exp((V - delta) / sigma²)` has probability tending to zero under weighted
`(SS+)`. -/
theorem basinExitLowerProbability_of_convergentStep
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho L delta : ℝ} (hrho : 0 ≤ rho)
    (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (ssplus : WeightedConvergentStepAssumption p rho)
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (hdelta : 0 < delta) :
    Tendsto
      (fun sigma : ℝ ↦ gaussianBasinExitProbability
        model ss threshold hrho
        (exponentialEscapeHorizon
          (civicQuasipotential p rho - delta) sigma) sigma)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
  let V : ℝ := civicQuasipotential p rho
  have hV : 0 < V := by
    simpa only [V] using civicQuasipotential_pos_of_lipschitz
      model ss threshold hrho hrhoCure hcoop weighted hL
  let d : ℝ := min (delta / 4) (V / 8)
  have hd : 0 < d := by
    dsimp only [d]
    exact lt_min (div_pos hdelta (by norm_num))
      (div_pos hV (by norm_num))
  have hdDelta : d ≤ delta / 4 := min_le_left _ _
  have hdV : d ≤ V / 8 := min_le_right _ _
  let base : ℝ := V - d
  let rate : ℝ := V - 2 * d
  have hrate : 0 < rate := by
    dsimp only [rate]
    linarith
  have hbase : 0 < base := by
    dsimp only [base]
    linarith
  have hrateBase : rate < base := by
    dsimp only [rate, base]
    linarith
  let t : ℝ := (rate / base + 1) / 2
  have ht0 : 0 < t := by
    dsimp only [t]
    have : 0 < rate / base := div_pos hrate hbase
    linarith
  have ht1 : t < 1 := by
    dsimp only [t]
    have : rate / base < 1 := (div_lt_one hbase).2 hrateBase
    linarith
  have hgap : rate < t * (V - d) := by
    have hbaseEq : V - d = base := rfl
    rw [hbaseEq]
    dsimp only [t]
    field_simp [hbase.ne']
    linarith
  have haux := exponentialBasinExitProbability_tendsto_zero_of_rate_lt
    model ss threshold hrho hrhoCure hcoop ssplus weighted
      hd hrate ht0 ht1 (by simpa only [V] using hgap)
  have htargetRate : V - delta ≤ rate := by
    dsimp only [rate]
    linarith
  have hpointwise : ∀ sigma : ℝ,
      gaussianBasinExitProbability model ss threshold hrho
          (exponentialEscapeHorizon (V - delta) sigma) sigma ≤
        gaussianBasinExitProbability model ss threshold hrho
          (exponentialEscapeHorizon rate sigma) sigma := by
    intro sigma
    exact monotone_gaussianBasinExitProbability
      model ss threshold hrho sigma
        (monotone_exponentialEscapeHorizon sigma htargetRate)
  have hzero : Tendsto (fun _ : ℝ ↦ (0 : ℝ≥0∞))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := tendsto_const_nhds
  apply hzero.squeeze' haux (Eventually.of_forall fun _ ↦ bot_le)
  filter_upwards with sigma
  simpa only [V] using hpointwise sigma

/-! ## Mean-time lower bound -/

/-- Finite-horizon survival gives the elementary expectation bound
`T * P(tau > T) ≤ E[tau]` for the genuine basin-exit stopping time. -/
theorem horizon_mul_survival_le_meanGaussianBasinExitTime
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (T : ℕ) (sigma : ℝ) :
    (T : ℝ≥0∞) *
        (1 - gaussianBasinExitProbability
          model ss threshold hrho T sigma) ≤
      meanGaussianBasinExitTime model ss threshold hrho sigma := by
  let survival : Set GaussianNoisePath :=
    {xi | (T : WithTop ℕ) <
      gaussianBasinExitTime model ss threshold hrho sigma xi}
  have hsurvivalMeasurable : MeasurableSet survival := by
    simpa only [survival] using
      measurableSet_gaussianBasinExitTime_gt
        model ss threshold hrho T sigma
  have hsurvivalMeasure : standardGaussianSequence survival =
      1 - gaussianBasinExitProbability
        model ss threshold hrho T sigma := by
    simpa only [survival] using
      standardGaussianSequence_basinExitTime_gt
        model ss threshold hrho T sigma
  have hpointwise :
      survival.indicator (fun _ ↦ (T : ℝ≥0∞)) ≤
        fun xi ↦ ENat.toENNReal
          (show ℕ∞ from gaussianBasinExitTime
            model ss threshold hrho sigma xi) := by
    intro xi
    by_cases hxi : xi ∈ survival
    · rw [indicator_of_mem hxi]
      have htime : (T : ℕ∞) ≤
          (show ℕ∞ from gaussianBasinExitTime
            model ss threshold hrho sigma xi) := by
        change (T : WithTop ℕ) ≤
          gaussianBasinExitTime model ss threshold hrho sigma xi
        exact hxi.le
      exact ENat.toENNReal_mono htime
    · rw [indicator_of_notMem hxi]
      exact bot_le
  calc
    (T : ℝ≥0∞) *
        (1 - gaussianBasinExitProbability
          model ss threshold hrho T sigma) =
        (T : ℝ≥0∞) * standardGaussianSequence survival := by
      rw [hsurvivalMeasure]
    _ = ∫⁻ xi, survival.indicator (fun _ ↦ (T : ℝ≥0∞)) xi
          ∂standardGaussianSequence := by
      rw [lintegral_indicator_const hsurvivalMeasurable]
    _ ≤ ∫⁻ xi, ENat.toENNReal
          (show ℕ∞ from gaussianBasinExitTime
            model ss threshold hrho sigma xi)
          ∂standardGaussianSequence := lintegral_mono hpointwise
    _ = meanGaussianBasinExitTime model ss threshold hrho sigma := rfl

/-- Persistence at a positive exponential horizon forces the logarithmic
mean genuine basin-exit time to have liminf at least that horizon rate. -/
theorem meanGaussianBasinExitLogRate_liminf_ge_of_persistence
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho rate : ℝ} (hrho : 0 ≤ rho)
    (hrate : 0 < rate)
    (hpersistence : Tendsto
      (fun sigma : ℝ ↦ gaussianBasinExitProbability
        model ss threshold hrho
        (exponentialEscapeHorizon rate sigma) sigma)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0)) :
    ((rate : ℝ) : EReal) ≤
      liminf (meanGaussianBasinExitLogRate
        model ss threshold hrho)
        (nhdsWithin 0 (Ioi (0 : ℝ))) := by
  have hprobHalf : ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      gaussianBasinExitProbability model ss threshold hrho
          (exponentialEscapeHorizon rate sigma) sigma <
        (1 / 2 : ℝ≥0∞) :=
    (tendsto_order.1 hpersistence).2 _ (by norm_num)
  have hhorizon := eventually_half_exp_le_exponentialEscapeHorizon hrate
  have hpointwise : ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      ((rate - sigma ^ 2 * Real.log 4 : ℝ) : EReal) ≤
        meanGaussianBasinExitLogRate
          model ss threshold hrho sigma := by
    filter_upwards [self_mem_nhdsWithin, hprobHalf, hhorizon] with
        sigma hsigma hprob hhorizonSigma
    let H : ℕ := exponentialEscapeHorizon rate sigma
    let probability : ℝ≥0∞ :=
      gaussianBasinExitProbability model ss threshold hrho H sigma
    letI : IsProbabilityMeasure (standardGaussianVector H) := by
      unfold standardGaussianVector
      infer_instance
    have hprobTop : probability ≠ ∞ := by
      dsimp only [probability, gaussianBasinExitProbability]
      exact measure_ne_top _ _
    have hprob' : probability < (1 / 2 : ℝ≥0∞) := by
      simpa only [probability, H] using hprob
    have hsurvival : (1 / 2 : ℝ≥0∞) ≤ 1 - probability := by
      apply ENNReal.le_sub_of_add_le_left hprobTop
      calc
        probability + (1 / 2 : ℝ≥0∞) ≤
            (1 / 2 : ℝ≥0∞) + (1 / 2 : ℝ≥0∞) := by
          simpa only [add_comm] using
            add_le_add_right hprob'.le (1 / 2 : ℝ≥0∞)
        _ = 1 := by
          simpa only [one_div] using ENNReal.add_halves (1 : ℝ≥0∞)
    have hbridge := horizon_mul_survival_le_meanGaussianBasinExitTime
      model ss threshold hrho H sigma
    have hproduct :
        ENNReal.ofReal (Real.exp (rate / sigma ^ 2) / 2) *
            (1 / 2 : ℝ≥0∞) ≤
          meanGaussianBasinExitTime model ss threshold hrho sigma := by
      exact (mul_le_mul' hhorizonSigma hsurvival).trans hbridge
    have hquarter :
        ENNReal.ofReal (Real.exp (rate / sigma ^ 2) / 4) =
          ENNReal.ofReal (Real.exp (rate / sigma ^ 2) / 2) *
            (1 / 2 : ℝ≥0∞) := by
      rw [show (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
          norm_num,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    have hmeanLower :
        ENNReal.ofReal (Real.exp (rate / sigma ^ 2) / 4) ≤
          meanGaussianBasinExitTime model ss threshold hrho sigma := by
      rw [hquarter]
      exact hproduct
    have hlog := ENNReal.logOrderIso.monotone hmeanLower
    change ENNReal.log
        (ENNReal.ofReal (Real.exp (rate / sigma ^ 2) / 4)) ≤
      ENNReal.log
        (meanGaussianBasinExitTime
          model ss threshold hrho sigma) at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog
      (show (0 : EReal) ≤ (sigma ^ 2 : ℝ) by
        exact_mod_cast sq_nonneg sigma)
    have hsigmaSq : sigma ^ 2 ≠ 0 := (sq_pos_of_pos hsigma).ne'
    have hlogLower :
        ENNReal.log
            (ENNReal.ofReal (Real.exp (rate / sigma ^ 2) / 4)) =
          ((rate / sigma ^ 2 - Real.log 4 : ℝ) : EReal) := by
      rw [ENNReal.log_ofReal_of_pos
        (div_pos (Real.exp_pos _) (by norm_num))]
      norm_cast
      rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp]
    rw [hlogLower] at hmul
    have hexplicit :
        ((rate - sigma ^ 2 * Real.log 4 : ℝ) : EReal) =
          (sigma ^ 2 : ℝ) *
            ((rate / sigma ^ 2 - Real.log 4 : ℝ) : EReal) := by
      norm_cast
      calc
        rate - sigma ^ 2 * Real.log 4 =
            (rate / sigma ^ 2) * sigma ^ 2 -
              sigma ^ 2 * Real.log 4 := by
          rw [div_mul_cancel₀ rate hsigmaSq]
        _ = sigma ^ 2 * (rate / sigma ^ 2 - Real.log 4) := by ring
    rw [hexplicit]
    simpa only [meanGaussianBasinExitLogRate] using hmul
  have hreal : Tendsto
      (fun sigma : ℝ ↦ rate - sigma ^ 2 * Real.log 4)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds rate) := by
    have hcont : ContinuousAt
        (fun sigma : ℝ ↦ rate - sigma ^ 2 * Real.log 4) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hereal : Tendsto
      (fun sigma : ℝ ↦
        ((rate - sigma ^ 2 * Real.log 4 : ℝ) : EReal))
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds ((rate : ℝ) : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hreal
  exact hereal.liminf_eq.symm.le.trans (liminf_le_liminf hpointwise)

/-- Under weighted `(SS+)`, the mean genuine basin-exit logarithmic rate has
liminf at least the basin quasipotential. -/
theorem basinExitLowerMeanRate_of_convergentStep
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho L : ℝ} (hrho : 0 ≤ rho)
    (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (ssplus : WeightedConvergentStepAssumption p rho)
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    ((civicQuasipotential p rho : ℝ) : EReal) ≤
      liminf (meanGaussianBasinExitLogRate
        model ss threshold hrho)
        (nhdsWithin 0 (Ioi (0 : ℝ))) := by
  let V : ℝ := civicQuasipotential p rho
  let R : EReal := liminf
    (meanGaussianBasinExitLogRate model ss threshold hrho)
    (nhdsWithin 0 (Ioi (0 : ℝ)))
  have hV : 0 < V := by
    simpa only [V] using civicQuasipotential_pos_of_lipschitz
      model ss threshold hrho hrhoCure hcoop weighted hL
  let delta : ℕ → ℝ := fun n ↦ V / (n + 1 : ℝ)
  let rate : ℕ → ℝ := fun n ↦ V - delta n
  have hdelta : ∀ n, 0 < delta n := by
    intro n
    dsimp only [delta]
    positivity
  have hrate : ∀ n, 1 ≤ n → 0 < rate n := by
    intro n hn
    have hden : 2 ≤ (n + 1 : ℝ) := by
      exact_mod_cast (show 2 ≤ n + 1 by omega)
    have hfrac : delta n ≤ V / 2 := by
      dsimp only [delta]
      exact div_le_div_of_nonneg_left hV.le (by norm_num) hden
    dsimp only [rate]
    linarith
  have hparameter : ∀ᶠ n : ℕ in atTop,
      ((rate n : ℝ) : EReal) ≤ R := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hpersistence := basinExitLowerProbability_of_convergentStep
      model ss threshold hrho hrhoCure hcoop ssplus weighted hL (hdelta n)
    have hlower := meanGaussianBasinExitLogRate_liminf_ge_of_persistence
      model ss threshold hrho (hrate n hn) hpersistence
    simpa only [R] using hlower
  have hinv : Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ))
      atTop (nhds (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hdeltaLimit : Tendsto delta atTop (nhds (0 : ℝ)) := by
    have hmul : Tendsto (fun n : ℕ ↦ V * (1 / (n + 1 : ℝ)))
        atTop (nhds (0 : ℝ)) := by
      simpa using tendsto_const_nhds.mul hinv
    apply hmul.congr'
    filter_upwards with n
    dsimp only [delta]
    ring
  have hrateLimit : Tendsto rate atTop (nhds V) := by
    simpa only [rate, sub_zero] using tendsto_const_nhds.sub hdeltaLimit
  have hereal : Tendsto (fun n ↦ ((rate n : ℝ) : EReal))
      atTop (nhds ((V : ℝ) : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hrateLimit
  have hclosed : ((V : ℝ) : EReal) ∈ Iic R :=
    isClosed_Iic.mem_of_tendsto hereal hparameter
  simpa only [V, R, mem_Iic] using hclosed

/-- The sharp genuine mean basin-exit Arrhenius law under weighted `(SS+)`.
The lower bound is the excursion theorem above; the upper bound is the
independent finite-exit restart construction. -/
theorem meanGaussianBasinExitLogRate_tendsto_of_convergentStep
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho L : ℝ} (hrho : 0 ≤ rho)
    (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (ssplus : WeightedConvergentStepAssumption p rho)
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    Tendsto (meanGaussianBasinExitLogRate
      model ss threshold hrho)
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds ((civicQuasipotential p rho : ℝ) : EReal)) := by
  exact tendsto_of_le_liminf_of_limsup_le
    (basinExitLowerMeanRate_of_convergentStep
      model ss threshold hrho hrhoCure hcoop ssplus weighted hL)
    (meanGaussianBasinExitLogRate_limsup_le_quasipotential
      model ss threshold hrho hrhoCure hcoop)

#print axioms exists_uniform_nearby_boundaryTarget_action_lower
#print axioms exists_basinBoundaryExcursionEvent_subset_actionTail
#print axioms basinExitLowerProbability_of_convergentStep
#print axioms basinExitLowerMeanRate_of_convergentStep
#print axioms meanGaussianBasinExitLogRate_tendsto_of_convergentStep

end

end CivicAlignment.PaperII
