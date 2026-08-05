/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.ArrheniusFunnel
import CivicAlignment.PaperII.BasinExitProcess

/-!
# Paper II: quantitative accessibility of the calibrated-basin boundary

Under the weighted convergent-step condition, every point on the relative
boundary of the calibrated basin converges to the weighted saddle.  A
two-step control of arbitrarily small quadratic action moves a whole
neighborhood of that saddle outside the calibrated basin.  Compactness then
gives a common finite horizon and a positive boundary-layer width.

The final theorem quantifies the state, the controlled orbit, the horizon,
and the action.  It therefore supplies the boundary-accessibility input
needed by a genuine basin-exit lower-bound argument without an asymptotic
shorthand or an unproved continuation premise.
-/

namespace CivicAlignment.PaperII

open Filter Function Set Topology
open scoped BigOperators Interval

noncomputable section

/-! ## Weighted basin topology and the boundary limit -/

/-- The basin in the invariant box of an arbitrary limit for the
constant-weight dynamics. -/
def civicWeightedBasinInBox (p : LoopParams) (rho : ℝ)
    (q : LoopState) : Set (LoopBox p) :=
  {x | Tendsto (civicWeightedOrbit p rho x.1) atTop (nhds q)}

@[simp]
theorem civicWeightedBasinInBox_calibrated
    (p : LoopParams) (rho : ℝ) :
    civicWeightedBasinInBox p rho (calibratedPoint p) =
      civicWeightedCalibratedBasinInBox p rho :=
  rfl

/-- A weighted basin is open whenever its limit has an attracting
neighborhood for all starts in the invariant box. -/
theorem civicWeightedBasinInBox_isOpen_of_attractingNeighborhood
    {p : LoopParams} (model : DriftModelAssumptions p) {rho : ℝ}
    {q : LoopState} {N : Set LoopState}
    (hN : N ∈ nhds q)
    (hattract : ∀ {x : ℕ → LoopState}, IsCivicWeightedTrajectory p rho x →
      x 0 ∈ absorbingBox p → x 0 ∈ N → Tendsto x atTop (nhds q)) :
    IsOpen (civicWeightedBasinInBox p rho q) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨U, hUN, hUopen, hqU⟩ := mem_nhds_iff.mp hN
  have hevent : ∀ᶠ n in atTop, civicWeightedOrbit p rho x.1 n ∈ U :=
    hx (hUopen.mem_nhds hqU)
  obtain ⟨n, hn⟩ := hevent.exists
  let V : Set (LoopBox p) :=
    {y | civicWeightedOrbit p rho y.1 n ∈ U}
  have hVopen : IsOpen V :=
    hUopen.preimage (continuous_civicWeightedIterateOnBox p rho n)
  refine mem_of_superset (hVopen.mem_nhds hn) ?_
  intro y hy
  have htail := hattract
    (civicWeightedOrbit_isTrajectory p rho
      (civicWeightedOrbit p rho y.1 n))
    (civicWeightedTrajectory_mem_absorbingBox model
      (civicWeightedOrbit_isTrajectory p rho y.1) y.2 n)
    (hUN hy)
  exact (civicWeightedOrbit_tendsto_iff_tail p rho y.1 q n).mp htail

/-- Below release, the captured weighted basin is relatively open. -/
theorem civicWeightedCapturedBasinInBox_isOpen
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (hrho : 0 ≤ rho) (hrhoCure : rho < cureThreshold p) :
    IsOpen (civicWeightedBasinInBox p rho (capturedPoint p)) := by
  obtain ⟨N, hN, hattract⟩ :=
    civicWeighted_captured_local_attraction model ss hrho hrhoCure
  exact civicWeightedBasinInBox_isOpen_of_attractingNeighborhood
    model hN hattract

/-- Basins of distinct weighted limits are disjoint. -/
theorem civicWeightedBasinInBox_disjoint_of_ne
    {p : LoopParams} {rho : ℝ} {q₁ q₂ : LoopState}
    (hne : q₁ ≠ q₂) :
    Disjoint (civicWeightedBasinInBox p rho q₁)
      (civicWeightedBasinInBox p rho q₂) := by
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  exact hne (tendsto_nhds_unique hx₁ hx₂)

/-- Every weighted fixed point in the invariant box is one of the calibrated
corner, the unique weighted saddle, or the captured corner. -/
theorem civicWeightedEquilibrium_eq_calibrated_or_saddle_or_captured
    {p : LoopParams} (model : DriftModelAssumptions p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    {q : LoopState} (hqmem : q ∈ absorbingBox p)
    (heq : IsCivicWeightedEquilibrium p rho q.1 q.2) :
    q = calibratedPoint p ∨ q = weightedSaddlePoint weighted ∨
      q = capturedPoint p := by
  have hqbeta : q.1 ∈ Icc (0 : ℝ) 1 := hqmem.1
  have hqstock :=
    civicWeightedEquilibrium_stock_eq_stationary model hqbeta heq
  by_cases hzero : q.1 = 0
  · left
    apply Prod.ext
    · simpa only [calibratedPoint] using hzero
    · simpa only [calibratedPoint, hzero] using hqstock
  by_cases hone : q.1 = 1
  · right; right
    apply Prod.ext
    · simpa only [capturedPoint] using hone
    · simpa only [capturedPoint, hone] using hqstock
  right; left
  have hinterior : q.1 ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hqbeta.1 (Ne.symm hzero),
      lt_of_le_of_ne hqbeta.2 hone⟩
  have hpolicy := congrArg Prod.fst heq
  simp only [civicWeightedLoopMap, civicWeightedDeferenceStep] at hpolicy
  have hinput := (clipUnit_eq_interior_iff hinterior).mp hpolicy
  have hgradient : civicWeightedGradient p rho q.1 q.2 = 0 := by
    simp only [civicWeightedInput] at hinput
    nlinarith [model.α_pos]
  have hstationary : weightedStationaryGradient p rho q.1 = 0 := by
    rw [← civicWeightedGradient_stationary_eq_weightedStationaryGradient
      rho ⟨hinterior.1.le, hinterior.2.le⟩]
    rwa [← hqstock]
  have hbeta : q.1 = weighted.βdagger := by
    rcases lt_trichotomy q.1 weighted.βdagger with hlt | heqbeta | hgt
    · exact (ne_of_lt (weighted.gradient_neg_before q.1 hinterior hlt)
        hstationary).elim
    · exact heqbeta
    · exact (ne_of_gt (weighted.gradient_pos_after q.1 hinterior hgt)
        hstationary).elim
  apply Prod.ext
  · simpa only [weightedSaddlePoint] using hbeta
  · simpa only [weightedSaddlePoint, hbeta] using hqstock

/-- The weighted saddle does not lie in the calibrated basin. -/
theorem weightedSaddlePoint_not_mem_calibratedBasinInBox
    {p : LoopParams} (model : DriftModelAssumptions p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) :
    (⟨weightedSaddlePoint weighted,
        weightedSaddlePoint_mem_absorbingBox model weighted⟩ : LoopBox p) ∉
      civicWeightedCalibratedBasinInBox p rho := by
  intro hbasin
  let q : LoopState := weightedSaddlePoint weighted
  have hfixed : civicWeightedLoopMap p rho q = q :=
    civicWeightedLoopMap_weightedSaddlePoint model weighted
  have horbit : ∀ n, civicWeightedOrbit p rho q n = q := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [(civicWeightedOrbit_isTrajectory p rho q) n, ih, hfixed]
  have hsaddle : Tendsto (civicWeightedOrbit p rho q) atTop (nhds q) := by
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall fun n ↦ (horbit n).symm
  have heqpoint : calibratedPoint p = q :=
    tendsto_nhds_unique hbasin hsaddle
  have hpolicy := congrArg Prod.fst heqpoint
  simp only [calibratedPoint, q, weightedSaddlePoint] at hpolicy
  linarith [weighted.βdagger_mem.1]

/-- Under weighted `(SS⁺)`, the unforced orbit of every relative calibrated-
basin boundary point converges to the weighted saddle. -/
theorem frontier_calibratedBasinInBox_tendsto_weightedSaddle
    {p : LoopParams} (model : DriftModelAssumptions p)
    (threshold : ThresholdAssumption p) {rho : ℝ}
    (hrho : 0 ≤ rho) (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (ssplus : WeightedConvergentStepAssumption p rho)
    (weighted : WeightedThresholdAssumption p rho)
    {x : LoopBox p}
    (hx : x ∈ frontier (civicWeightedCalibratedBasinInBox p rho)) :
    Tendsto (civicWeightedOrbit p rho x.1) atTop
      (nhds (weightedSaddlePoint weighted)) := by
  let ss : SmallStepAssumption p :=
    (ssplus.toStrictSmallStep model hcoop).toSmallStep
  obtain ⟨q, hqmem, hlim, hcatalogue⟩ :=
    civicWeighted_globalConvergence_of_convergentStep
      model hcoop ssplus (civicWeightedOrbit_isTrajectory p rho x.1) x.2
  have hcalOpen : IsOpen (civicWeightedCalibratedBasinInBox p rho) :=
    civicWeightedCalibratedBasinInBox_isOpen model ss threshold hrho
  have hxNotCal : x ∉ civicWeightedCalibratedBasinInBox p rho := by
    intro hxCal
    have hxInterior : x ∈ interior
        (civicWeightedCalibratedBasinInBox p rho) := by
      rw [IsOpen.interior_eq hcalOpen]
      exact hxCal
    exact ((mem_frontier_iff_notMem_interior hxCal).mp hx) hxInterior
  have hcapturedOpen : IsOpen
      (civicWeightedBasinInBox p rho (capturedPoint p)) :=
    civicWeightedCapturedBasinInBox_isOpen model ss hrho hrhoCure
  have hpointsNe : calibratedPoint p ≠ capturedPoint p := by
    intro heq
    have hpolicy := congrArg Prod.fst heq
    norm_num [calibratedPoint, capturedPoint] at hpolicy
  have hdisjoint : Disjoint (civicWeightedCalibratedBasinInBox p rho)
      (civicWeightedBasinInBox p rho (capturedPoint p)) := by
    rw [← civicWeightedBasinInBox_calibrated]
    exact civicWeightedBasinInBox_disjoint_of_ne hpointsNe
  have hxNotCaptured :
      x ∉ civicWeightedBasinInBox p rho (capturedPoint p) := by
    exact Set.disjoint_left.mp
      (hdisjoint.frontier_left hcapturedOpen) hx
  rcases civicWeightedEquilibrium_eq_calibrated_or_saddle_or_captured
      model weighted hqmem hcatalogue with hq | hq | hq
  · exfalso
    apply hxNotCal
    change Tendsto (civicWeightedOrbit p rho x.1) atTop
      (nhds (calibratedPoint p))
    rwa [← hq]
  · rwa [hq] at hlim
  · exfalso
    apply hxNotCaptured
    change Tendsto (civicWeightedOrbit p rho x.1) atTop
      (nhds (capturedPoint p))
    rwa [← hq]

/-! ## A vanishing-action two-step saddle exit -/

/-- The weighted saddle regarded as a point of the invariant box. -/
def weightedSaddlePointInBox
    {p : LoopParams} (model : DriftModelAssumptions p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) : LoopBox p :=
  ⟨weightedSaddlePoint weighted,
    weightedSaddlePoint_mem_absorbingBox model weighted⟩

/-- Raise the saddle policy by `delta`, then cancel the gradient so that the
second policy step holds the raised level. -/
def weightedSaddlePushControl
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (delta : ℝ) :
    Fin 2 → ℝ :=
  ![delta / p.α,
    -civicWeightedGradient p rho (weighted.βdagger + delta)
      (p.stationaryStock weighted.βdagger)]

/-- The actual weighted gradient vanishes at the weighted saddle. -/
theorem civicWeightedGradient_weightedSaddle_eq_zero
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) :
    civicWeightedGradient p rho weighted.βdagger
      (p.stationaryStock weighted.βdagger) = 0 := by
  rw [civicWeightedGradient_stationary_eq_weightedStationaryGradient rho
    ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩]
  exact weighted.gradient_zero

/-- The first push step raises policy by exactly `delta` while the stock stays
at its saddle value. -/
theorem weightedSaddlePush_firstStep
    {p : LoopParams} (model : DriftModelAssumptions p) {rho delta : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    (htarget : weighted.βdagger + delta ∈ Icc (0 : ℝ) 1) :
    (finiteControlOrbit (controlledCivicWeightedStepInBox model rho)
      (weightedSaddlePointInBox model weighted)
      (weightedSaddlePushControl weighted delta) 1).1 =
        (weighted.βdagger + delta,
          p.stationaryStock weighted.βdagger) := by
  have hgradient := civicWeightedGradient_weightedSaddle_eq_zero weighted
  have hstock := stationaryStock_fixed model
    ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩
  have hscale : p.α * (delta / p.α) = delta := by
    field_simp [model.α_pos.ne']
  apply Prod.ext
  · change LoopParams.clipUnit
      (weighted.βdagger + p.α *
        (civicWeightedGradient p rho weighted.βdagger
          (p.stationaryStock weighted.βdagger) + delta / p.α)) =
        weighted.βdagger + delta
    rw [hgradient, zero_add, hscale]
    exact clipUnit_eq_self htarget
  · change p.stockStep weighted.βdagger
      (p.stationaryStock weighted.βdagger) =
        p.stationaryStock weighted.βdagger
    exact hstock

/-- The two-step endpoint holds the raised policy exactly. -/
theorem weightedSaddlePush_secondStep_policy
    {p : LoopParams} (model : DriftModelAssumptions p) {rho delta : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    (htarget : weighted.βdagger + delta ∈ Icc (0 : ℝ) 1) :
    ((finiteControlOrbit (controlledCivicWeightedStepInBox model rho)
      (weightedSaddlePointInBox model weighted)
      (weightedSaddlePushControl weighted delta) 2).1).1 =
        weighted.βdagger + delta := by
  rw [finiteControlOrbit]
  have hfirst := weightedSaddlePush_firstStep model weighted htarget
  have huOne : finiteControlValue
      (weightedSaddlePushControl weighted delta) 1 =
        -civicWeightedGradient p rho (weighted.βdagger + delta)
          (p.stationaryStock weighted.βdagger) := by
    simp [finiteControlValue, weightedSaddlePushControl]
  rw [huOne]
  change (controlledCivicWeightedStep p rho
    (-civicWeightedGradient p rho (weighted.βdagger + delta)
      (p.stationaryStock weighted.βdagger))
    (finiteControlOrbit (controlledCivicWeightedStepInBox model rho)
      (weightedSaddlePointInBox model weighted)
      (weightedSaddlePushControl weighted delta) 1).1).1 =
        weighted.βdagger + delta
  rw [hfirst]
  simp only [controlledCivicWeightedStep, add_neg_cancel, mul_zero, add_zero]
  exact clipUnit_eq_self htarget

/-- A positive saddle push makes the second-step stock strictly larger than
the saddle stock. -/
theorem weightedSaddlePush_secondStep_stock_gt
    {p : LoopParams} (model : DriftModelAssumptions p) {rho delta : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    (hdelta : 0 < delta)
    (htarget : weighted.βdagger + delta ∈ Icc (0 : ℝ) 1) :
    p.stationaryStock weighted.βdagger <
      ((finiteControlOrbit (controlledCivicWeightedStepInBox model rho)
        (weightedSaddlePointInBox model weighted)
        (weightedSaddlePushControl weighted delta) 2).1).2 := by
  rw [finiteControlOrbit]
  have hfirst := weightedSaddlePush_firstStep model weighted htarget
  change p.stockStep
    ((finiteControlOrbit (controlledCivicWeightedStepInBox model rho)
      (weightedSaddlePointInBox model weighted)
      (weightedSaddlePushControl weighted delta) 1).1).1
    ((finiteControlOrbit (controlledCivicWeightedStepInBox model rho)
      (weightedSaddlePointInBox model weighted)
      (weightedSaddlePushControl weighted delta) 1).1).2 >
        p.stationaryStock weighted.βdagger
  rw [hfirst]
  have hb : weighted.βdagger ∈ Icc (0 : ℝ) 1 :=
    ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩
  have hslt : p.s weighted.βdagger <
      p.s (weighted.βdagger + delta) :=
    driftStockMultiplier_strictMonoOn model hb htarget (by linarith)
  have hstockPos : 0 < p.stationaryStock weighted.βdagger :=
    model.I_pos.trans_le (stationaryStock_mem_stockInterval model hb).1
  have hfixed := stationaryStock_fixed model hb
  simp only [LoopParams.stockStep, model.no_content_gain, add_zero] at hfixed ⊢
  nlinarith [mul_lt_mul_of_pos_right hslt hstockPos]

/-- The explicit two-step saddle-push action tends to zero with its policy
increment. -/
theorem weightedSaddlePush_action_tendsto_zero
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) :
    Tendsto
      (fun delta ↦ finiteQuadraticAction
        (weightedSaddlePushControl weighted delta))
      (nhds 0) (nhds 0) := by
  have hcontinuous : Continuous
      (fun delta ↦ finiteQuadraticAction
        (weightedSaddlePushControl weighted delta)) := by
    simp only [finiteQuadraticAction, weightedSaddlePushControl,
      Fin.sum_univ_two, civicWeightedGradient, LoopParams.gradU]
    fun_prop
  have hzero : finiteQuadraticAction
      (weightedSaddlePushControl weighted 0) = 0 := by
    simp [finiteQuadraticAction, weightedSaddlePushControl,
      civicWeightedGradient_weightedSaddle_eq_zero weighted]
  simpa only [hzero] using hcontinuous.tendsto 0

/-- For every positive action tolerance, one fixed two-step control exits the
calibrated basin from every state in an open saddle neighborhood. -/
theorem exists_uniform_twoStep_exit_near_weightedSaddle
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho epsilon : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hepsilon : 0 < epsilon) :
    ∃ u : Fin 2 → ℝ, finiteQuadraticAction u < epsilon ∧
      ∃ H : Set (LoopBox p), IsOpen H ∧
        weightedSaddlePointInBox model weighted ∈ H ∧
        ∀ x ∈ H,
          finiteControlOrbit (controlledCivicWeightedStepInBox model rho)
            x u 2 ∉ civicWeightedCalibratedBasinInBox p rho := by
  let action : ℝ → ℝ := fun delta ↦
    finiteQuadraticAction (weightedSaddlePushControl weighted delta)
  have hactionMap : {a : ℝ | a < epsilon} ∈
      map action (nhds 0) :=
    weightedSaddlePush_action_tendsto_zero weighted
      (isOpen_Iio.mem_nhds hepsilon)
  have hactionNhds : action ⁻¹' {a : ℝ | a < epsilon} ∈ nhds 0 :=
    Filter.mem_map.mp hactionMap
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hactionNhds
  let gap : ℝ := 1 - weighted.βdagger
  have hgap : 0 < gap := sub_pos.mpr weighted.βdagger_mem.2
  let delta : ℝ := min (r / 2) (gap / 2)
  have hdelta : 0 < delta := by
    exact lt_min (half_pos hr) (half_pos hgap)
  have hdeltar : delta < r :=
    (min_le_left (r / 2) (gap / 2)).trans_lt (half_lt_self hr)
  have hdeltagap : delta < gap :=
    (min_le_right (r / 2) (gap / 2)).trans_lt (half_lt_self hgap)
  have htarget : weighted.βdagger + delta ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith [weighted.βdagger_mem.1]
    · change weighted.βdagger + delta ≤ 1
      dsimp only [gap] at hdeltagap
      linarith
  let u : Fin 2 → ℝ := weightedSaddlePushControl weighted delta
  have huAction : finiteQuadraticAction u < epsilon := by
    apply hball
    change dist delta 0 < r
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hdelta] using hdeltar
  let endpoint : LoopBox p → LoopBox p := fun x ↦
    finiteControlOrbit (controlledCivicWeightedStepInBox model rho) x u 2
  have hendpoint : Continuous endpoint := by
    have hstep (a : ℝ) : Continuous
        (controlledCivicWeightedStepInBox model rho a) := by
      have hpair : Continuous (fun x : LoopBox p ↦ ((a, x) : ℝ × LoopBox p)) := by
        fun_prop
      exact (continuous_uncurry_controlledCivicWeightedStepInBox model rho).comp
        hpair
    change Continuous
      ((controlledCivicWeightedStepInBox model rho (finiteControlValue u 1)) ∘
        controlledCivicWeightedStepInBox model rho (finiteControlValue u 0))
    exact (hstep (finiteControlValue u 1)).comp
      (hstep (finiteControlValue u 0))
  let H : Set (LoopBox p) :=
    {x | weighted.βdagger < (endpoint x).1.1} ∩
      {x | p.stationaryStock weighted.βdagger < (endpoint x).1.2}
  have hHopen : IsOpen H := by
    apply IsOpen.inter
    · exact isOpen_lt continuous_const
        ((continuous_fst.comp continuous_subtype_val).comp hendpoint)
    · exact isOpen_lt continuous_const
        ((continuous_snd.comp continuous_subtype_val).comp hendpoint)
  have hqH : weightedSaddlePointInBox model weighted ∈ H := by
    constructor
    · change weighted.βdagger <
        ((finiteControlOrbit
          (controlledCivicWeightedStepInBox model rho)
          (weightedSaddlePointInBox model weighted) u 2).1).1
      rw [weightedSaddlePush_secondStep_policy model weighted htarget]
      exact lt_add_of_pos_right weighted.βdagger hdelta
    · exact weightedSaddlePush_secondStep_stock_gt
        model weighted hdelta htarget
  refine ⟨u, huAction, H, hHopen, hqH, ?_⟩
  intro x hxH hxBasin
  have horder : weightedSaddlePointInBox model weighted ≤ endpoint x :=
    ⟨hxH.1.le, hxH.2.le⟩
  exact weightedSaddlePoint_not_mem_calibratedBasinInBox model weighted
    (civicWeightedCalibratedBasinInBox_lowerSet
      model ss threshold hrho hcoop horder hxBasin)

/-! ## Compact boundary layers -/

/-- In a compact metric space, an open neighborhood of the frontier of an
open set contains a positive inner boundary layer. -/
theorem exists_innerBoundaryLayer_subset
    {X : Type*} [MetricSpace X] [CompactSpace X]
    {A W : Set X} (hAopen : IsOpen A) (hWopen : IsOpen W)
    (hfrontier : frontier A ⊆ W) (hcompl : Aᶜ.Nonempty) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ x ∈ A, Metric.infDist x Aᶜ < eta → x ∈ W := by
  let C : Set X := Wᶜ ∩ closure A
  have hCclosed : IsClosed C := hWopen.isClosed_compl.inter isClosed_closure
  have hCcompact : IsCompact C := hCclosed.isCompact
  have hCsubset : C ⊆ A := by
    intro x hx
    rcases hx with ⟨hxW, hxClosure⟩
    rw [closure_eq_self_union_frontier A] at hxClosure
    rcases hxClosure with hxA | hxFrontier
    · exact hxA
    · exact (hxW (hfrontier hxFrontier)).elim
  by_cases hCempty : C = ∅
  · refine ⟨1, by norm_num, ?_⟩
    intro x hxA _hdist
    by_contra hxW
    have hxC : x ∈ C := ⟨hxW, subset_closure hxA⟩
    rw [hCempty] at hxC
    exact hxC
  · have hCnonempty : C.Nonempty := nonempty_iff_ne_empty.mpr hCempty
    obtain ⟨z, hzC, hzmin⟩ := hCcompact.exists_isMinOn hCnonempty
      (Metric.continuous_infDist_pt Aᶜ).continuousOn
    let eta : ℝ := Metric.infDist z Aᶜ
    have hzA : z ∈ A := hCsubset hzC
    have heta : 0 < eta := by
      have hzNot : z ∉ Aᶜ := by
        simpa only [mem_compl_iff, not_not] using hzA
      exact (hAopen.isClosed_compl.notMem_iff_infDist_pos hcompl).mp hzNot
    refine ⟨eta, heta, ?_⟩
    intro x hxA hxdist
    by_contra hxW
    have hxC : x ∈ C := ⟨hxW, subset_closure hxA⟩
    have hmin : eta ≤ Metric.infDist x Aᶜ := hzmin hxC
    exact (not_lt_of_ge hmin) hxdist

/-- Fully quantified vanishing-cost accessibility of the inner calibrated-
basin boundary layer.  The horizon bound is uniform over the layer, while
the realized path length and control vector may depend on the initial state. -/
def HasUniformVanishingBasinBoundaryAccessibility
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ eta : ℝ, 0 < eta ∧ ∃ T : ℕ,
      ∀ x ∈ civicWeightedCalibratedBasinInBox p rho,
        Metric.infDist x
          (civicWeightedCalibratedBasinInBox p rho)ᶜ < eta →
        ∃ n : ℕ, n ≤ T ∧ ∃ u : Fin n → ℝ,
          finiteQuadraticAction u < epsilon ∧
          finiteControlOrbit
              (controlledCivicWeightedStepInBox model rho) x u n ∉
            civicWeightedCalibratedBasinInBox p rho

/-- Weighted `(SS⁺)` proves the genuine uniform boundary-accessibility
property.  No variational continuation premise is assumed. -/
theorem hasUniformVanishingBasinBoundaryAccessibility_of_convergentStep
    {p : LoopParams} (model : DriftModelAssumptions p)
    (threshold : ThresholdAssumption p) {rho : ℝ}
    (hrho : 0 ≤ rho) (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (ssplus : WeightedConvergentStepAssumption p rho)
    (weighted : WeightedThresholdAssumption p rho) :
    HasUniformVanishingBasinBoundaryAccessibility model rho := by
  intro epsilon hepsilon
  let ss : SmallStepAssumption p :=
    (ssplus.toStrictSmallStep model hcoop).toSmallStep
  obtain ⟨u, huAction, H, hHopen, hqH, hHexit⟩ :=
    exists_uniform_twoStep_exit_near_weightedSaddle
      model ss threshold hrho hcoop weighted hepsilon
  have hbox : IsCompact (absorbingBox p) := by
    simpa only [absorbingBox] using
      (isCompact_Icc.prod isCompact_Icc :
        IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc p.I (p.I / p.lambda₀)))
  letI : CompactSpace (LoopBox p) := isCompact_iff_compactSpace.mp hbox
  let step : ℝ → LoopBox p → LoopBox p :=
    controlledCivicWeightedStepInBox model rho
  let f : LoopBox p → LoopBox p := step 0
  have hf : Continuous f := by
    have hpair : Continuous (fun x : LoopBox p ↦ ((0, x) : ℝ × LoopBox p)) := by
      fun_prop
    exact (continuous_uncurry_controlledCivicWeightedStepInBox model rho).comp
      hpair
  let K : Set (LoopBox p) :=
    frontier (civicWeightedCalibratedBasinInBox p rho)
  have hKcompact : IsCompact K := isClosed_frontier.isCompact
  have hKconverges : ∀ x ∈ K,
      Tendsto (fun n : ℕ ↦ (f^[n]) x) atTop
        (nhds (weightedSaddlePointInBox model weighted)) := by
    intro x hxK
    apply tendsto_subtype_rng.mpr
    simpa only [f, step, weightedSaddlePointInBox,
      controlledCivicWeightedStepInBox_zero_iterate_val] using
      frontier_calibratedBasinInBox_tendsto_weightedSaddle
        model threshold hrho hrhoCure hcoop ssplus weighted hxK
  obtain ⟨N, hN⟩ := exists_uniform_iterate_entrance_time
    hf hKcompact hHopen hqH hKconverges
  let W : Set (LoopBox p) :=
    ⋃ i : Fin (N + 1), (f^[i.1]) ⁻¹' H
  have hWopen : IsOpen W := by
    apply isOpen_iUnion
    intro i
    exact hHopen.preimage (hf.iterate i.1)
  have hfrontierW :
      frontier (civicWeightedCalibratedBasinInBox p rho) ⊆ W := by
    intro x hxK
    obtain ⟨n, hn, hnenters⟩ := hN x hxK
    have hnlt : n < N + 1 := by omega
    exact mem_iUnion_of_mem (⟨n, hnlt⟩ : Fin (N + 1)) hnenters
  have hbasinOpen : IsOpen
      (civicWeightedCalibratedBasinInBox p rho) :=
    civicWeightedCalibratedBasinInBox_isOpen model ss threshold hrho
  have hcomplNonempty :
      (civicWeightedCalibratedBasinInBox p rho)ᶜ.Nonempty :=
    ⟨weightedSaddlePointInBox model weighted,
      weightedSaddlePoint_not_mem_calibratedBasinInBox model weighted⟩
  obtain ⟨eta, heta, hlayer⟩ := exists_innerBoundaryLayer_subset
    hbasinOpen hWopen hfrontierW hcomplNonempty
  refine ⟨eta, heta, N + 2, ?_⟩
  intro x hxBasin hxdist
  have hxW : x ∈ W := hlayer x hxBasin hxdist
  rcases mem_iUnion.mp hxW with ⟨i, hi⟩
  let v : Fin (i.1 + 2) → ℝ :=
    Fin.append (0 : Fin i.1 → ℝ) u
  have hvAction : finiteQuadraticAction v = finiteQuadraticAction u := by
    simp [v, finiteQuadraticAction, Fin.sum_univ_add]
  have hvExit : finiteControlOrbit step x v (i.1 + 2) ∉
      civicWeightedCalibratedBasinInBox p rho := by
    rw [finiteControlOrbit_append_right step x
      (0 : Fin i.1 → ℝ) u le_rfl]
    rw [finiteControlOrbit_zero_eq_iterate]
    exact hHexit ((f^[i.1]) x) hi
  refine ⟨i.1 + 2, by omega, v, ?_, hvExit⟩
  rwa [hvAction]

/-- Variational consequence of boundary accessibility: reaching a sufficiently
thin inner boundary layer from the calibrated corner already costs at least
`V - epsilon`.  This is the exact boundary-approach estimate needed by a
direct basin-exit lower proof. -/
theorem quasipotential_le_action_add_of_terminal_in_boundaryLayer
    {p : LoopParams} (model : DriftModelAssumptions p)
    (threshold : ThresholdAssumption p) {rho : ℝ}
    (hrho : 0 ≤ rho) (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (ssplus : WeightedConvergentStepAssumption p rho)
    (weighted : WeightedThresholdAssumption p rho)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {N : ℕ} (u : Fin N → ℝ),
        let x := finiteControlOrbit
          (controlledCivicWeightedStepInBox model rho)
          (calibratedPointInBox p model) u N
        x ∈ civicWeightedCalibratedBasinInBox p rho →
        Metric.infDist x
          (civicWeightedCalibratedBasinInBox p rho)ᶜ < eta →
        civicQuasipotential p rho ≤ finiteQuadraticAction u + epsilon := by
  obtain ⟨eta, heta, T, haccess⟩ :=
    hasUniformVanishingBasinBoundaryAccessibility_of_convergentStep
      model threshold hrho hrhoCure hcoop ssplus weighted epsilon hepsilon
  refine ⟨eta, heta, ?_⟩
  intro N u x hxBasin hxDistance
  obtain ⟨n, _hnT, v, hvAction, hvExit⟩ :=
    haccess x hxBasin hxDistance
  let w : Fin (N + n) → ℝ := Fin.append u v
  have hwExit : finiteControlOrbit
      (controlledCivicWeightedStepInBox model rho)
      (calibratedPointInBox p model) w (N + n) ∉
        civicWeightedCalibratedBasinInBox p rho := by
    rw [finiteControlOrbit_append_right
      (controlledCivicWeightedStepInBox model rho)
      (calibratedPointInBox p model) u v le_rfl]
    exact hvExit
  have hwExitProcess : finiteControlledOrbit p rho w (N + n) ∉
      civicWeightedCalibratedBasin p rho := by
    have hwExitBox : finiteControlledOrbitInBox model rho w (N + n) ∉
        civicWeightedCalibratedBasinInBox p rho := by
      rwa [← finiteControlOrbitInBox_eq_finiteControlledOrbitInBox]
    simpa only [finiteControlledOrbitInBox,
      mem_civicWeightedCalibratedBasinInBox_iff] using hwExitBox
  have hbarrier : civicQuasipotential p rho ≤ gaussianVectorAction w :=
    civicQuasipotential_le_gaussianVectorAction_of_terminal_basinExit
      model hwExitProcess
  have hwAction : gaussianVectorAction w =
      finiteQuadraticAction u + finiteQuadraticAction v := by
    simp only [w, gaussianVectorAction, finiteQuadraticAction,
      Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    ring
  calc
    civicQuasipotential p rho ≤ gaussianVectorAction w := hbarrier
    _ = finiteQuadraticAction u + finiteQuadraticAction v := hwAction
    _ ≤ finiteQuadraticAction u + epsilon :=
      (add_lt_add_right hvAction (finiteQuadraticAction u)).le

#print axioms frontier_calibratedBasinInBox_tendsto_weightedSaddle
#print axioms weightedSaddlePush_action_tendsto_zero
#print axioms exists_uniform_twoStep_exit_near_weightedSaddle
#print axioms hasUniformVanishingBasinBoundaryAccessibility_of_convergentStep
#print axioms quasipotential_le_action_add_of_terminal_in_boundaryLayer

end

end CivicAlignment.PaperII
