/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.ArrheniusRestart
import CivicAlignment.PaperII.ArrheniusPersistence

/-!
# Paper II: uniform upper Arrhenius blocks

This file constructs the model-specific uniform crossing block consumed by
`ArrheniusRestart`.  It implements a full-state dichotomy: a small-action
tube covers a ball about the weighted saddle, while
the compact complement first shadows its unforced funnel into a calibrated
home neighborhood and then follows a robust crossing tube.
-/

namespace CivicAlignment.PaperII

open Filter Function MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal

noncomputable section

/-! ## Extending robust tubes -/

/-- Quadratic action is additive under concatenation. -/
theorem gaussianVectorAction_append
    {N T : ℕ} (u : Fin N → ℝ) (v : Fin T → ℝ) :
    gaussianVectorAction (Fin.append u v) =
      gaussianVectorAction u + gaussianVectorAction v := by
  simp only [gaussianVectorAction]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  ring

/-- A robust crossing tube remains robust after appending unused control
coordinates.  This lets tubes from the two branches share one block horizon. -/
def RobustCrossingTube.padRight
    {p : LoopParams} {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (tube : RobustCrossingTube weighted) (extra : ℕ) :
    RobustCrossingTube weighted where
  starts := tube.starts
  horizon := tube.horizon + extra
  center := Fin.append tube.center 0
  radius := tube.radius
  radius_pos := tube.radius_pos
  actionBound := tube.actionBound
  center_action_le := by
    rw [gaussianVectorAction_append]
    have hzero : gaussianVectorAction (0 : Fin extra → ℝ) = 0 := by
      simp [gaussianVectorAction]
    rw [hzero, add_zero]
    exact tube.center_action_le
  crosses := by
    intro x₀ hx₀ u hu
    let uPrefix : Fin tube.horizon → ℝ :=
      fun i ↦ u (Fin.castAdd extra i)
    let uSuffix : Fin extra → ℝ :=
      fun i ↦ u (Fin.natAdd tube.horizon i)
    have hprefix : uPrefix ∈ Metric.ball tube.center tube.radius := by
      rw [Metric.mem_ball, dist_pi_lt_iff tube.radius_pos]
      intro i
      have hall := (dist_pi_lt_iff tube.radius_pos).1 hu
        (Fin.castAdd extra i)
      simpa only [uPrefix, Fin.append_left] using hall
    have huAppend : Fin.append uPrefix uSuffix = u := by
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp only [Fin.append_left, uPrefix]
      · intro j
        simp only [Fin.append_right, uSuffix]
    have hcross := tube.crosses x₀ hx₀ uPrefix hprefix
    obtain ⟨k, hk, hβ⟩ := (le_runningMax_iff (a := fun n ↦
      (finiteControlledOrbitFrom p rho x₀ uPrefix n).1)).1 hcross
    apply (le_runningMax_iff (a := fun n ↦
      (finiteControlledOrbitFrom p rho x₀ u n).1)).2
    refine ⟨k, hk.trans (Nat.le_add_right tube.horizon extra), ?_⟩
    rw [← huAppend,
      finiteControlledOrbitFrom_append_left p rho x₀ uPrefix uSuffix hk]
    exact hβ

/-! ## Funnelling into a home tube -/

/-- If every unforced orbit from a compact set reaches an inner calibrated
ball, then small prefix controls followed by a home crossing tube form one
robust tube over the whole compact start set. -/
theorem exists_funnelledRobustCrossingTube
    {p : LoopParams} {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (homeTube : RobustCrossingTube weighted)
    {homeRadius : ℝ}
    (hhomeStarts : homeTube.starts =
      Metric.closedBall (calibratedPoint p) homeRadius)
    {K : Set LoopState} (hK : IsCompact K)
    (N : ℕ) {inner : ℝ} (_hinner : 0 ≤ inner)
    (hgap : inner < homeRadius)
    (hhome : ∀ x₀ ∈ K,
      finiteControlledOrbitFrom p rho x₀ (0 : Fin N → ℝ) N ∈
        Metric.closedBall (calibratedPoint p) inner) :
    ∃ tube : RobustCrossingTube weighted,
      tube.starts = K ∧
      tube.horizon = N + homeTube.horizon ∧
      tube.actionBound = homeTube.actionBound := by
  have hgapPos : 0 < homeRadius - inner := sub_pos.mpr hgap
  obtain ⟨prefixRadius, hprefixRadius, hprefixClose⟩ :=
    exists_uniform_finiteControl_radius p rho (T := N) hK N hgapPos
  let radius : ℝ := min prefixRadius homeTube.radius
  have hradius : 0 < radius :=
    lt_min hprefixRadius homeTube.radius_pos
  let center : Fin (N + homeTube.horizon) → ℝ :=
    Fin.append (0 : Fin N → ℝ) homeTube.center
  let tube : RobustCrossingTube weighted :=
    { starts := K
      horizon := N + homeTube.horizon
      center := center
      radius := radius
      radius_pos := hradius
      actionBound := homeTube.actionBound
      center_action_le := by
        dsimp only [center]
        rw [gaussianVectorAction_append]
        have hzero : gaussianVectorAction (0 : Fin N → ℝ) = 0 := by
          simp [gaussianVectorAction]
        rw [hzero, zero_add]
        exact homeTube.center_action_le
      crosses := by
        intro x₀ hx₀ u hu
        let uPrefix : Fin N → ℝ := fun i ↦ u (Fin.castAdd homeTube.horizon i)
        let uSuffix : Fin homeTube.horizon → ℝ :=
          fun i ↦ u (Fin.natAdd N i)
        have hall := (dist_pi_lt_iff hradius).1 hu
        have hprefixBall : dist uPrefix 0 < prefixRadius := by
          rw [dist_pi_lt_iff hprefixRadius]
          intro i
          have hi := hall (Fin.castAdd homeTube.horizon i)
          have hrle : radius ≤ prefixRadius := min_le_left _ _
          have hcoord : dist (uPrefix i) 0 < radius := by
            simpa only [uPrefix, center, Fin.append_left, Pi.zero_apply] using hi
          exact hcoord.trans_le hrle
        have hsuffixBall : uSuffix ∈
            Metric.ball homeTube.center homeTube.radius := by
          rw [Metric.mem_ball, dist_pi_lt_iff homeTube.radius_pos]
          intro i
          have hi := hall (Fin.natAdd N i)
          have hrle : radius ≤ homeTube.radius := min_le_right _ _
          have hcoord : dist (uSuffix i) (homeTube.center i) < radius := by
            simpa only [uSuffix, center, Fin.append_right] using hi
          exact hcoord.trans_le hrle
        have hcontrolledClose := hprefixClose x₀ hx₀ uPrefix hprefixBall
        have hunforced := hhome x₀ hx₀
        have hcontrolledHome :
            finiteControlledOrbitFrom p rho x₀ uPrefix N ∈
              Metric.closedBall (calibratedPoint p) homeRadius := by
          rw [Metric.mem_closedBall]
          have hunforcedDist :
              dist (finiteControlledOrbitFrom p rho x₀
                (0 : Fin N → ℝ) N) (calibratedPoint p) ≤ inner := hunforced
          have hdistLt :
              dist (finiteControlledOrbitFrom p rho x₀ uPrefix N)
                (calibratedPoint p) < homeRadius := by
            calc
            dist (finiteControlledOrbitFrom p rho x₀ uPrefix N)
                (calibratedPoint p) ≤
                dist (finiteControlledOrbitFrom p rho x₀ uPrefix N)
                    (finiteControlledOrbitFrom p rho x₀
                      (0 : Fin N → ℝ) N) +
                  dist (finiteControlledOrbitFrom p rho x₀
                      (0 : Fin N → ℝ) N) (calibratedPoint p) :=
              dist_triangle _ _ _
            _ < (homeRadius - inner) + inner := by
              exact add_lt_add_of_lt_of_le
                (by simpa only [dist_comm] using hcontrolledClose)
                hunforcedDist
            _ = homeRadius := by ring
          exact hdistLt.le
        have hstart : finiteControlledOrbitFrom p rho x₀ uPrefix N ∈
            homeTube.starts := by
          rw [hhomeStarts]
          exact hcontrolledHome
        have hcross := homeTube.crosses
          (finiteControlledOrbitFrom p rho x₀ uPrefix N)
          hstart uSuffix hsuffixBall
        obtain ⟨k, hk, hβ⟩ := (le_runningMax_iff (a := fun n ↦
          (finiteControlledOrbitFrom p rho
            (finiteControlledOrbitFrom p rho x₀ uPrefix N) uSuffix n).1)).1 hcross
        have huAppend : Fin.append uPrefix uSuffix = u := by
          funext i
          refine Fin.addCases ?_ ?_ i
          · intro j
            simp only [Fin.append_left, uPrefix]
          · intro j
            simp only [Fin.append_right, uSuffix]
        apply (le_runningMax_iff (a := fun n ↦
          (finiteControlledOrbitFrom p rho x₀ u n).1)).2
        refine ⟨N + k, Nat.add_le_add_left hk N, ?_⟩
        rw [← huAppend,
          finiteControlledOrbitFrom_append_right p rho x₀ uPrefix uSuffix hk]
        exact hβ }
  exact ⟨tube, rfl, rfl, rfl⟩

/-! ## A common uniform block -/

/-- A robust tube containing the calibrated state cannot have zero horizon:
the calibrated policy is strictly below the weighted saddle. -/
theorem RobustCrossingTube.horizon_pos_of_calibrated_mem
    {p : LoopParams} {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (tube : RobustCrossingTube weighted)
    (hcalibrated : calibratedPoint p ∈ tube.starts) :
    0 < tube.horizon := by
  by_contra hpos
  have hzero : tube.horizon = 0 := Nat.eq_zero_of_not_pos hpos
  have hcross := tube.crosses (calibratedPoint p) hcalibrated tube.center
    (Metric.mem_ball_self tube.radius_pos)
  have hmaxZero : weighted.βdagger ≤
      policyRunningMax
        (finiteControlledOrbitFrom p rho (calibratedPoint p) tube.center) 0 :=
    hcross.trans_eq (congrArg
      (policyRunningMax
        (finiteControlledOrbitFrom p rho (calibratedPoint p) tube.center))
      hzero)
  simp only [policyRunningMax, runningMax_zero, finiteControlledOrbitFrom,
    calibratedPoint] at hmaxZero
  exact (not_le_of_gt weighted.βdagger_mem.1) hmaxZero

/-- The fixed-horizon crossing block used by the geometric restart.  Its two
tubes implement the exhaustive full-state split: a closed saddle ball and
the compact pre-crossing order interval outside the corresponding open ball.
Both tubes have the same horizon, but retain separate centers so their
Gaussian costs can be tracked independently. -/
structure UniformRobustCrossingBlock {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) where
  horizon : ℕ
  horizon_pos : 0 < horizon
  saddleRadius : ℝ
  saddleRadius_pos : 0 < saddleRadius
  nearTube : RobustCrossingTube weighted
  awayTube : RobustCrossingTube weighted
  near_starts : nearTube.starts =
    Metric.closedBall (weightedSaddlePoint weighted) saddleRadius
  away_starts : awayTube.starts =
    weightedPreCrossingAwaySet weighted saddleRadius
  near_horizon : nearTube.horizon = horizon
  away_horizon : awayTube.horizon = horizon

/-- Every state in the compact pre-crossing order interval is covered by one
of the two tubes of a uniform block. -/
theorem UniformRobustCrossingBlock.mem_near_or_away
    {p : LoopParams} {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (block : UniformRobustCrossingBlock weighted)
    {x : LoopState}
    (hx : x ∈ absorbingBox p ∩
      Icc (calibratedPoint p) (weightedSaddlePoint weighted)) :
    x ∈ block.nearTube.starts ∨ x ∈ block.awayTube.starts := by
  by_cases hnear : dist x (weightedSaddlePoint weighted) ≤ block.saddleRadius
  · left
    rw [block.near_starts]
    exact hnear
  · right
    rw [block.away_starts]
    exact ⟨hx, fun hball ↦ hnear hball.le⟩

/-- For every positive action tolerance there is one fixed block horizon
covering the entire pre-crossing order interval.  The saddle branch costs at
most `delta`; the away branch first funnels home at zero control and then
uses a `V^x + delta` robust crossing tube. -/
theorem exists_uniformRobustCrossingBlock
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho delta : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hdelta : 0 < delta) :
    ∃ block : UniformRobustCrossingBlock weighted,
      gaussianVectorAction block.nearTube.center ≤ delta ∧
      gaussianVectorAction block.awayTube.center ≤
        civicCrossingQuasipotential weighted + delta := by
  obtain ⟨homeRadius, hhomeRadius, homeTube,
      hhomeStarts, hhomeAction⟩ :=
    exists_quasipotential_robustCrossingTube model weighted hdelta
  obtain ⟨saddleRadius, hsaddleRadius, nearTube,
      hnearStarts, hnearAction⟩ :=
    exists_weightedSaddle_robustCrossingTube_small_action
      model weighted hdelta
  let inner : ℝ := homeRadius / 2
  have hinner : 0 ≤ inner := (half_pos hhomeRadius).le
  have hinnerLt : inner < homeRadius := half_lt_self hhomeRadius
  obtain ⟨N, hN⟩ := exists_uniform_away_saddle_funnel_time
    model ss threshold hrho hcoop weighted hsaddleRadius
      (half_pos hhomeRadius)
  let K : Set LoopState := weightedPreCrossingAwaySet weighted saddleRadius
  have hK : IsCompact K :=
    isCompact_weightedPreCrossingAwaySet weighted saddleRadius
  have hhome : ∀ x₀ ∈ K,
      finiteControlledOrbitFrom p rho x₀ (0 : Fin N → ℝ) N ∈
        Metric.closedBall (calibratedPoint p) inner := by
    intro x₀ hx₀
    rw [finiteControlledOrbitFrom_zero_eq_civicWeightedOrbit]
    exact calibratedHomeRectangle_subset_closedBall p inner (hN x₀ hx₀)
  obtain ⟨awayTube, hawayStarts, hawayHorizon, hawayAction⟩ :=
    exists_funnelledRobustCrossingTube homeTube hhomeStarts hK N hinner
      hinnerLt hhome
  have hcalibrated : calibratedPoint p ∈ homeTube.starts := by
    rw [hhomeStarts]
    rw [Metric.mem_closedBall]
    simpa only [dist_self] using hhomeRadius.le
  have hhomeHorizon : 0 < homeTube.horizon :=
    homeTube.horizon_pos_of_calibrated_mem hcalibrated
  have hawayHorizonPos : 0 < awayTube.horizon := by
    rw [hawayHorizon]
    omega
  let nearPadded : RobustCrossingTube weighted :=
    nearTube.padRight awayTube.horizon
  let awayPadded : RobustCrossingTube weighted :=
    awayTube.padRight nearTube.horizon
  let W : ℕ := nearTube.horizon + awayTube.horizon
  have hW : 0 < W := by
    dsimp only [W]
    omega
  have hnearPaddedStarts : nearPadded.starts =
      Metric.closedBall (weightedSaddlePoint weighted) saddleRadius := by
    simpa only [nearPadded, RobustCrossingTube.padRight] using hnearStarts
  have hawayPaddedStarts : awayPadded.starts =
      weightedPreCrossingAwaySet weighted saddleRadius := by
    simpa only [awayPadded, RobustCrossingTube.padRight] using hawayStarts
  have hnearPaddedHorizon : nearPadded.horizon = W := by
    rfl
  have hawayPaddedHorizon : awayPadded.horizon = W := by
    dsimp only [awayPadded, RobustCrossingTube.padRight, W]
    omega
  let block : UniformRobustCrossingBlock weighted :=
    { horizon := W
      horizon_pos := hW
      saddleRadius := saddleRadius
      saddleRadius_pos := hsaddleRadius
      nearTube := nearPadded
      awayTube := awayPadded
      near_starts := hnearPaddedStarts
      away_starts := hawayPaddedStarts
      near_horizon := hnearPaddedHorizon
      away_horizon := hawayPaddedHorizon }
  have hnearCost : gaussianVectorAction nearPadded.center ≤ delta := by
    have hbound := nearPadded.center_action_le
    change gaussianVectorAction nearPadded.center ≤ nearTube.actionBound at hbound
    rwa [hnearAction] at hbound
  have hawayCost : gaussianVectorAction awayPadded.center ≤
      civicCrossingQuasipotential weighted + delta := by
    have hbound := awayPadded.center_action_le
    change gaussianVectorAction awayPadded.center ≤ awayTube.actionBound at hbound
    rw [hawayAction, hhomeAction] at hbound
    exact hbound
  exact ⟨block, hnearCost, hawayCost⟩

/-- The concatenation of the two branch centers.  It is used only to expose
one scalar Gaussian lower bound whose logarithmic action is the sum of the
two branch actions. -/
def UniformRobustCrossingBlock.combinedCenter
    {p : LoopParams} {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (block : UniformRobustCrossingBlock weighted) :
    Fin (block.nearTube.horizon + block.awayTube.horizon) → ℝ :=
  Fin.append block.nearTube.center block.awayTube.center

/-- A start-independent one-block success lower bound.  The product form is
deliberate: it lies below either branch probability, while its logarithmic
cost is just the sum of the two finite control actions. -/
noncomputable def UniformRobustCrossingBlock.successLower
    {p : LoopParams} {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (block : UniformRobustCrossingBlock weighted) (sigma : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (∏ i, gaussianCoordinateLowerBound (block.combinedCenter i) sigma)

/-- The scalar block lower bound factors into the two coordinate-box density
floors. -/
theorem UniformRobustCrossingBlock.successLower_eq_mul
    {p : LoopParams} {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (block : UniformRobustCrossingBlock weighted) (sigma : ℝ) :
    block.successLower sigma =
      ENNReal.ofReal
          (∏ i, gaussianCoordinateLowerBound
            (block.nearTube.center i) sigma) *
        ENNReal.ofReal
          (∏ i, gaussianCoordinateLowerBound
            (block.awayTube.center i) sigma) := by
  rw [UniformRobustCrossingBlock.successLower]
  change ENNReal.ofReal
      (∏ i, gaussianCoordinateLowerBound
        ((Fin.append block.nearTube.center block.awayTube.center) i) sigma) = _
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [ENNReal.ofReal_mul]
  exact Finset.prod_nonneg fun i _ ↦
    (gaussianCoordinateLowerBound_pos (block.nearTube.center i)).le

/-- The success lower bound is valid uniformly over the entire compact
pre-crossing order interval. -/
theorem UniformRobustCrossingBlock.successLower_le_crossingProbability
    {p : LoopParams} {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (block : UniformRobustCrossingBlock weighted)
    {x : LoopState}
    (hx : x ∈ absorbingBox p ∩
      Icc (calibratedPoint p) (weightedSaddlePoint weighted))
    {sigma : ℝ} (hsigma : 0 < sigma)
    (hsigmaNear : sigma < block.nearTube.radius)
    (hsigmaAway : sigma < block.awayTube.radius) :
    block.successLower sigma ≤
      gaussianCrossingProbabilityFrom weighted x block.horizon sigma := by
  let nearFloor : ℝ≥0∞ := ENNReal.ofReal
    (∏ i, gaussianCoordinateLowerBound
      (block.nearTube.center i) sigma)
  let awayFloor : ℝ≥0∞ := ENNReal.ofReal
    (∏ i, gaussianCoordinateLowerBound
      (block.awayTube.center i) sigma)
  letI : IsProbabilityMeasure
      (standardGaussianVector block.nearTube.horizon) := by
    unfold standardGaussianVector
    infer_instance
  have hnearOne : nearFloor ≤ 1 := by
    exact (gaussianControlBox_probability_lower
      block.nearTube.center hsigma).trans prob_le_one
  letI : IsProbabilityMeasure
      (standardGaussianVector block.awayTube.horizon) := by
    unfold standardGaussianVector
    infer_instance
  have hawayOne : awayFloor ≤ 1 := by
    exact (gaussianControlBox_probability_lower
      block.awayTube.center hsigma).trans prob_le_one
  have hsplit : block.successLower sigma = nearFloor * awayFloor := by
    simpa only [nearFloor, awayFloor] using block.successLower_eq_mul sigma
  rcases block.mem_near_or_away hx with hnear | haway
  · have hlower := robustCrossingTube_probability_lower
      block.nearTube hnear hsigma hsigmaNear
    have hhorizon :
        gaussianCrossingProbabilityFrom weighted x
            block.nearTube.horizon sigma =
          gaussianCrossingProbabilityFrom weighted x block.horizon sigma :=
      congrArg
        (fun T ↦ gaussianCrossingProbabilityFrom weighted x T sigma)
        block.near_horizon
    rw [hsplit]
    exact (mul_le_mul_of_nonneg_left hawayOne bot_le).trans_eq (mul_one nearFloor)
      |>.trans (hlower.trans_eq hhorizon)
  · have hlower := robustCrossingTube_probability_lower
      block.awayTube haway hsigma hsigmaAway
    have hhorizon :
        gaussianCrossingProbabilityFrom weighted x
            block.awayTube.horizon sigma =
          gaussianCrossingProbabilityFrom weighted x block.horizon sigma :=
      congrArg
        (fun T ↦ gaussianCrossingProbabilityFrom weighted x T sigma)
        block.away_horizon
    rw [hsplit]
    exact (mul_le_mul_of_nonneg_right hnearOne bot_le).trans_eq (one_mul awayFloor)
      |>.trans (hlower.trans_eq hhorizon)

/-- The concatenated center has exactly the sum of the branch actions. -/
theorem UniformRobustCrossingBlock.combinedCenter_action
    {p : LoopParams} {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (block : UniformRobustCrossingBlock weighted) :
    gaussianVectorAction block.combinedCenter =
      gaussianVectorAction block.nearTube.center +
        gaussianVectorAction block.awayTube.center := by
  exact gaussianVectorAction_append _ _

/-- The explicit block success lower bound is strictly positive. -/
theorem UniformRobustCrossingBlock.successLower_pos
    {p : LoopParams} {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (block : UniformRobustCrossingBlock weighted) (sigma : ℝ) :
    0 < block.successLower sigma := by
  rw [UniformRobustCrossingBlock.successLower, ENNReal.ofReal_pos]
  exact Finset.prod_pos fun i _ ↦
    gaussianCoordinateLowerBound_pos (block.combinedCenter i)

/-- Restarting the uniform block gives the exact geometric survival bound at
integer multiples of its horizon. -/
theorem UniformRobustCrossingBlock.survival_mul_le_pow
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (block : UniformRobustCrossingBlock weighted)
    {sigma : ℝ} (hsigma : 0 < sigma)
    (hsigmaNear : sigma < block.nearTube.radius)
    (hsigmaAway : sigma < block.awayTube.radius)
    (k : ℕ) :
    1 - gaussianEscapeProbability weighted (k * block.horizon) sigma ≤
      (1 - block.successLower sigma) ^ k := by
  exact one_sub_gaussianEscapeProbability_mul_le_pow
    model ss weighted block.horizon sigma (block.successLower sigma)
      (fun _x hx ↦ block.successLower_le_crossingProbability
        hx hsigma hsigmaNear hsigmaAway) k

/-- The block-geometric restart bounds the mean first-crossing time by the common
block length times the inverse explicit success floor. -/
theorem UniformRobustCrossingBlock.meanGaussianEscapeTime_le
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (block : UniformRobustCrossingBlock weighted)
    {sigma : ℝ} (hsigma : 0 < sigma)
    (hsigmaNear : sigma < block.nearTube.radius)
    (hsigmaAway : sigma < block.awayTube.radius) :
    meanGaussianEscapeTime weighted sigma ≤
      (block.horizon : ℝ≥0∞) * (block.successLower sigma)⁻¹ := by
  exact meanGaussianEscapeTime_le_block_mul_inv
    model ss weighted block.horizon block.horizon_pos sigma
      (block.successLower sigma)
      (fun _x hx ↦ block.successLower_le_crossingProbability
        hx hsigma hsigmaNear hsigmaAway)

/-! ## Small-noise logarithmic cost of a block -/

/-- The logarithmic rate of the explicit uniform one-block success floor. -/
noncomputable def UniformRobustCrossingBlock.successLowerLogRate
    {p : LoopParams} {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (block : UniformRobustCrossingBlock weighted) (sigma : ℝ) : EReal :=
  (sigma ^ 2 : ℝ) * ENNReal.log (block.successLower sigma)

/-- On positive noise scales the block success log-rate is exactly the
explicit finite-dimensional Gaussian control-box rate. -/
theorem UniformRobustCrossingBlock.successLowerLogRate_eq
    {p : LoopParams} {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (block : UniformRobustCrossingBlock weighted)
    {sigma : ℝ} (_hsigma : 0 < sigma) :
    block.successLowerLogRate sigma =
      ((gaussianControlBoxExplicitRate block.combinedCenter sigma : ℝ) : EReal) := by
  have hprodPos : 0 < ∏ i, gaussianCoordinateLowerBound
      (block.combinedCenter i) sigma :=
    Finset.prod_pos fun i _ ↦
      gaussianCoordinateLowerBound_pos (block.combinedCenter i)
  rw [UniformRobustCrossingBlock.successLowerLogRate,
    UniformRobustCrossingBlock.successLower,
    ENNReal.log_ofReal_of_pos hprodPos]
  rfl

/-- The success floor has the negative sum of the two branch actions as its
exact small-noise logarithmic rate. -/
theorem UniformRobustCrossingBlock.successLowerLogRate_tendsto
    {p : LoopParams} {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (block : UniformRobustCrossingBlock weighted) :
    Tendsto block.successLowerLogRate
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds (((-(gaussianVectorAction block.nearTube.center +
        gaussianVectorAction block.awayTube.center) : ℝ) : EReal))) := by
  have hexplicit := gaussianControlBoxExplicitRate_tendsto block.combinedCenter
  have hcoe : Tendsto
      (fun sigma ↦
        ((gaussianControlBoxExplicitRate block.combinedCenter sigma : ℝ) : EReal))
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds (((-gaussianVectorAction block.combinedCenter : ℝ) : EReal))) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hexplicit
  have hcongr : block.successLowerLogRate =ᶠ[nhdsWithin 0 (Ioi (0 : ℝ))]
      fun sigma ↦
        ((gaussianControlBoxExplicitRate block.combinedCenter sigma : ℝ) : EReal) := by
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    exact block.successLowerLogRate_eq hsigma
  rw [block.combinedCenter_action] at hcoe
  exact hcoe.congr' hcongr.symm

/-- The logarithmic small-noise scale of the mean Gaussian first-crossing time. -/
noncomputable def meanGaussianEscapeLogRate
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (sigma : ℝ) : EReal :=
  (sigma ^ 2 : ℝ) * ENNReal.log (meanGaussianEscapeTime weighted sigma)

/-- A fixed uniform block bounds the logarithmic mean first-crossing rate by the sum
of its two branch actions. -/
theorem UniformRobustCrossingBlock.meanGaussianEscapeLogRate_limsup_le
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (block : UniformRobustCrossingBlock weighted) :
    limsup (meanGaussianEscapeLogRate weighted)
        (nhdsWithin 0 (Ioi (0 : ℝ))) ≤
      ((gaussianVectorAction block.nearTube.center +
        gaussianVectorAction block.awayTube.center : ℝ) : EReal) := by
  have hnearEventually : ∀ᶠ sigma : ℝ in nhds 0,
      sigma < block.nearTube.radius :=
    Iio_mem_nhds block.nearTube.radius_pos
  have hawayEventually : ∀ᶠ sigma : ℝ in nhds 0,
      sigma < block.awayTube.radius :=
    Iio_mem_nhds block.awayTube.radius_pos
  have hHReal : 0 < (block.horizon : ℝ) := by
    exact_mod_cast block.horizon_pos
  have hlogH : ENNReal.log (block.horizon : ℝ≥0∞) =
      ((Real.log (block.horizon : ℝ) : ℝ) : EReal) := by
    rw [← ENNReal.ofReal_natCast block.horizon,
      ENNReal.log_ofReal_of_pos hHReal]
  have hpointwise : ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      meanGaussianEscapeLogRate weighted sigma ≤
        ((sigma ^ 2 * Real.log (block.horizon : ℝ) -
          gaussianControlBoxExplicitRate block.combinedCenter sigma : ℝ) : EReal) := by
    filter_upwards [self_mem_nhdsWithin,
      hnearEventually.filter_mono inf_le_left,
      hawayEventually.filter_mono inf_le_left] with
        sigma hsigma hsigmaNear hsigmaAway
    have hmean := block.meanGaussianEscapeTime_le
      model ss hsigma hsigmaNear hsigmaAway
    have hlog := ENNReal.logOrderIso.monotone hmean
    have hmul := mul_le_mul_of_nonneg_left hlog
      (show (0 : EReal) ≤ (sigma ^ 2 : ℝ) by
        exact_mod_cast sq_nonneg sigma)
    calc
      meanGaussianEscapeLogRate weighted sigma ≤
          (sigma ^ 2 : ℝ) *
            ENNReal.log
              ((block.horizon : ℝ≥0∞) *
                (block.successLower sigma)⁻¹) := hmul
      _ = (sigma ^ 2 : ℝ) * ENNReal.log (block.horizon : ℝ≥0∞) -
            block.successLowerLogRate sigma := by
        have hprodPos : 0 < ∏ i, gaussianCoordinateLowerBound
            (block.combinedCenter i) sigma :=
          Finset.prod_pos fun i _ ↦
            gaussianCoordinateLowerBound_pos (block.combinedCenter i)
        rw [ENNReal.log_mul_add, ENNReal.log_inv,
          UniformRobustCrossingBlock.successLowerLogRate,
          UniformRobustCrossingBlock.successLower,
          ENNReal.log_ofReal_of_pos hprodPos, hlogH]
        norm_cast
        ring
      _ = ((sigma ^ 2 * Real.log (block.horizon : ℝ) -
          gaussianControlBoxExplicitRate block.combinedCenter sigma : ℝ) : EReal) := by
        rw [hlogH, block.successLowerLogRate_eq hsigma]
        norm_cast
  have hzero : Tendsto
      (fun sigma : ℝ ↦ sigma ^ 2 * Real.log (block.horizon : ℝ))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
    have hcont : ContinuousAt
        (fun sigma : ℝ ↦ sigma ^ 2 * Real.log (block.horizon : ℝ)) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hexplicit :=
    gaussianControlBoxExplicitRate_tendsto block.combinedCenter
  have hreal : Tendsto
      (fun sigma : ℝ ↦ sigma ^ 2 * Real.log (block.horizon : ℝ) -
        gaussianControlBoxExplicitRate block.combinedCenter sigma)
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds (gaussianVectorAction block.nearTube.center +
        gaussianVectorAction block.awayTube.center)) := by
    have hsub := hzero.sub hexplicit
    rw [block.combinedCenter_action] at hsub
    simpa only [zero_sub, neg_neg] using hsub
  have hmajor : Tendsto
      (fun sigma : ℝ ↦
        ((sigma ^ 2 * Real.log (block.horizon : ℝ) -
          gaussianControlBoxExplicitRate block.combinedCenter sigma : ℝ) : EReal))
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds ((gaussianVectorAction block.nearTube.center +
        gaussianVectorAction block.awayTube.center : ℝ) : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hreal
  exact (limsup_le_limsup hpointwise).trans_eq hmajor.limsup_eq

/-- At every positive tolerance, the corrected two-branch construction
bounds the mean escape exponent within twice that tolerance of the crossing
quasipotential. -/
theorem meanGaussianEscapeLogRate_limsup_le_add
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho delta : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hdelta : 0 < delta) :
    limsup (meanGaussianEscapeLogRate weighted)
        (nhdsWithin 0 (Ioi (0 : ℝ))) ≤
      ((civicCrossingQuasipotential weighted + 2 * delta : ℝ) : EReal) := by
  obtain ⟨block, hnear, haway⟩ :=
    exists_uniformRobustCrossingBlock
      model ss threshold hrho hcoop weighted hdelta
  refine (block.meanGaussianEscapeLogRate_limsup_le model ss).trans ?_
  exact_mod_cast (show
    gaussianVectorAction block.nearTube.center +
        gaussianVectorAction block.awayTube.center ≤
      civicCrossingQuasipotential weighted + 2 * delta by
    linarith)

/-- Paper II, Theorem `thm:rate`, mean-time upper clause: the logarithmic
mean crossing time has limsup at most the crossing quasipotential. -/
theorem crossingUpperMeanRate
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho) :
    limsup (meanGaussianEscapeLogRate weighted)
        (nhdsWithin 0 (Ioi (0 : ℝ))) ≤
      ((civicCrossingQuasipotential weighted : ℝ) : EReal) := by
  let R : EReal := limsup (meanGaussianEscapeLogRate weighted)
    (nhdsWithin 0 (Ioi (0 : ℝ)))
  let delta : ℕ → ℝ := fun n ↦ 1 / (n + 1 : ℝ)
  have hparameter : ∀ n,
      R ≤ ((civicCrossingQuasipotential weighted + 2 * delta n : ℝ) : EReal) := by
    intro n
    have hdelta : 0 < delta n := by
      dsimp only [delta]
      positivity
    have hbound := meanGaussianEscapeLogRate_limsup_le_add
      model ss threshold hrho hcoop weighted hdelta
    simpa only [R] using hbound
  have hinv : Tendsto delta atTop (nhds (0 : ℝ)) := by
    simpa only [delta] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hreal : Tendsto
      (fun n ↦ civicCrossingQuasipotential weighted + 2 * delta n)
      atTop (nhds (civicCrossingQuasipotential weighted)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
  have hereal : Tendsto
      (fun n ↦
        ((civicCrossingQuasipotential weighted + 2 * delta n : ℝ) : EReal))
      atTop (nhds ((civicCrossingQuasipotential weighted : ℝ) : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hreal
  have hclosed : ((civicCrossingQuasipotential weighted : ℝ) : EReal) ∈ Ici R :=
    isClosed_Ici.mem_of_tendsto hereal (Eventually.of_forall hparameter)
  simpa only [R, mem_Ici] using hclosed

/-! ## Escape by an exponential horizon -/

/-- The natural horizon corresponding exactly to the real inequality
`T ≤ exp(rate / sigma²)`. -/
noncomputable def exponentialEscapeHorizon (rate sigma : ℝ) : ℕ :=
  ⌊Real.exp (rate / sigma ^ 2)⌋₊

/-- Above two, the natural floor retains at least half of a positive real
number. -/
theorem half_le_natFloor_of_two_le {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ (Nat.floor x : ℝ) := by
  have hfloor : x - 1 < (Nat.floor x : ℝ) := Nat.sub_one_lt_floor x
  linarith

/-- A positive activated exponential diverges as positive noise vanishes. -/
theorem tendsto_exp_const_div_sq_atTop_nhdsGT_zero
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun sigma : ℝ ↦ Real.exp (a / sigma ^ 2))
      (nhdsWithin 0 (Ioi (0 : ℝ))) atTop := by
  have hsquare : Tendsto (fun sigma : ℝ ↦ sigma ^ 2)
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhdsWithin 0 (Ioi (0 : ℝ))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hcont : ContinuousAt (fun sigma : ℝ ↦ sigma ^ 2) 0 := by
        fun_prop
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with sigma hsigma
      exact sq_pos_of_pos (by simpa only [mem_Ioi] using hsigma)
  have hinv : Tendsto (fun sigma : ℝ ↦ (sigma ^ 2)⁻¹)
      (nhdsWithin 0 (Ioi (0 : ℝ))) atTop :=
    tendsto_inv_nhdsGT_zero.comp hsquare
  have hscaled : Tendsto (fun sigma : ℝ ↦ a * (sigma ^ 2)⁻¹)
      (nhdsWithin 0 (Ioi (0 : ℝ))) atTop := by
    simpa only [mul_comm] using hinv.atTop_mul_const ha
  have hexp := Real.tendsto_exp_atTop.comp hscaled
  apply hexp.congr'
  filter_upwards with sigma
  simp only [Function.comp_apply, div_eq_mul_inv]

/-- Eventually, the inverse discrete exponential horizon is no larger than
twice the reciprocal real exponential. -/
theorem eventually_exponentialEscapeHorizon_inv_le
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      (exponentialEscapeHorizon rate sigma : ℝ≥0∞)⁻¹ ≤
        ENNReal.ofReal (2 * Real.exp (-rate / sigma ^ 2)) := by
  have hdiverge := tendsto_exp_const_div_sq_atTop_nhdsGT_zero hrate
  have htwo : ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      2 ≤ Real.exp (rate / sigma ^ 2) :=
    (tendsto_atTop.1 hdiverge) 2
  filter_upwards [htwo] with sigma hsigma
  let x : ℝ := Real.exp (rate / sigma ^ 2)
  have hxpos : 0 < x := Real.exp_pos _
  have hfloorReal : x / 2 ≤ (exponentialEscapeHorizon rate sigma : ℝ) := by
    simpa only [x, exponentialEscapeHorizon] using
      half_le_natFloor_of_two_le hsigma
  have hfloorENN : ENNReal.ofReal (x / 2) ≤
      (exponentialEscapeHorizon rate sigma : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hfloorReal
  have hinv := ENNReal.inv_le_inv' hfloorENN
  rw [← ENNReal.ofReal_inv_of_pos (div_pos hxpos zero_lt_two)] at hinv
  have hreal : (x / 2)⁻¹ = 2 * Real.exp (-rate / sigma ^ 2) := by
    dsimp only [x]
    rw [inv_div, div_eq_mul_inv]
    rw [show -rate / sigma ^ 2 = -(rate / sigma ^ 2) by ring,
      Real.exp_neg]
  rwa [hreal] at hinv

/-- The inverse explicit block-success floor grows at most at the exponential
rate of the concatenated center action, with any prescribed positive
tolerance. -/
theorem UniformRobustCrossingBlock.eventually_successLower_inv_le_exp
    {p : LoopParams} {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (block : UniformRobustCrossingBlock weighted)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      (block.successLower sigma)⁻¹ ≤
        ENNReal.ofReal (Real.exp
          ((gaussianVectorAction block.combinedCenter + epsilon) /
            sigma ^ 2)) := by
  have hrate := gaussianControlBoxExplicitRate_tendsto block.combinedCenter
  have hlower : ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      -gaussianVectorAction block.combinedCenter - epsilon <
        gaussianControlBoxExplicitRate block.combinedCenter sigma :=
    (tendsto_order.1 hrate).1 _ (by linarith)
  filter_upwards [self_mem_nhdsWithin, hlower] with sigma hsigma hlowerSigma
  let q : ℝ := ∏ i, gaussianCoordinateLowerBound
    (block.combinedCenter i) sigma
  have hq : 0 < q :=
    Finset.prod_pos fun i _ ↦
      gaussianCoordinateLowerBound_pos (block.combinedCenter i)
  have hsigmaSq : 0 < sigma ^ 2 := sq_pos_of_pos hsigma
  have hscaled : -gaussianVectorAction block.combinedCenter - epsilon <
      sigma ^ 2 * Real.log q := by
    simpa only [gaussianControlBoxExplicitRate, q] using hlowerSigma
  have hneg : -(sigma ^ 2 * Real.log q) <
      gaussianVectorAction block.combinedCenter + epsilon := by
    linarith [neg_lt_neg hscaled]
  have hlogInv : -Real.log q <
      (gaussianVectorAction block.combinedCenter + epsilon) /
        sigma ^ 2 := by
    apply (lt_div_iff₀ hsigmaSq).2
    calc
      -Real.log q * sigma ^ 2 = -(sigma ^ 2 * Real.log q) := by ring
      _ < gaussianVectorAction block.combinedCenter + epsilon := hneg
  have hinv : q⁻¹ ≤ Real.exp
      ((gaussianVectorAction block.combinedCenter + epsilon) /
        sigma ^ 2) := by
    calc
      q⁻¹ = Real.exp (-Real.log q) := by
        rw [Real.exp_neg, Real.exp_log hq]
      _ ≤ Real.exp
          ((gaussianVectorAction block.combinedCenter + epsilon) /
            sigma ^ 2) := Real.exp_le_exp.mpr hlogInv.le
  rw [UniformRobustCrossingBlock.successLower]
  rw [← ENNReal.ofReal_inv_of_pos hq]
  exact ENNReal.ofReal_le_ofReal hinv

/-- If a uniform block's concatenated center action is strictly below a
chosen rate, survival up to the corresponding real exponential horizon tends
to zero. -/
theorem UniformRobustCrossingBlock.exponentialSurvival_tendsto_zero
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho rate : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (block : UniformRobustCrossingBlock weighted)
    (haction : gaussianVectorAction block.combinedCenter < rate) :
    Tendsto
      (fun sigma : ℝ ↦ 1 - gaussianEscapeProbability weighted
        (exponentialEscapeHorizon rate sigma) sigma)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
  let gap : ℝ := rate - gaussianVectorAction block.combinedCenter
  have hgap : 0 < gap := sub_pos.mpr haction
  let epsilon : ℝ := gap / 2
  have hepsilon : 0 < epsilon := half_pos hgap
  have hqInv := block.eventually_successLower_inv_le_exp hepsilon
  have hactionNonneg : 0 ≤ gaussianVectorAction block.combinedCenter := by
    unfold gaussianVectorAction
    positivity
  have hHInv := eventually_exponentialEscapeHorizon_inv_le
    (hactionNonneg.trans_lt haction)
  have hnearEventually : ∀ᶠ sigma : ℝ in nhds 0,
      sigma < block.nearTube.radius :=
    Iio_mem_nhds block.nearTube.radius_pos
  have hawayEventually : ∀ᶠ sigma : ℝ in nhds 0,
      sigma < block.awayTube.radius :=
    Iio_mem_nhds block.awayTube.radius_pos
  let majorant : ℝ → ℝ≥0∞ := fun sigma ↦
    (block.horizon : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp
        ((gaussianVectorAction block.combinedCenter + epsilon) /
          sigma ^ 2)) *
      ENNReal.ofReal (2 * Real.exp (-rate / sigma ^ 2))
  have hsurvival : ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      1 - gaussianEscapeProbability weighted
          (exponentialEscapeHorizon rate sigma) sigma ≤ majorant sigma := by
    filter_upwards [self_mem_nhdsWithin, hqInv, hHInv,
      hnearEventually.filter_mono inf_le_left,
      hawayEventually.filter_mono inf_le_left] with
        sigma hsigma hqSigma hHSigma hsigmaNear hsigmaAway
    let H : ℕ := exponentialEscapeHorizon rate sigma
    let survival : ℝ≥0∞ :=
      1 - gaussianEscapeProbability weighted H sigma
    have hmean := block.meanGaussianEscapeTime_le
      model ss hsigma hsigmaNear hsigmaAway
    have hbridge := horizon_mul_survival_le_meanGaussianEscapeTime
      weighted H sigma
    have htotal : (H : ℝ≥0∞) * survival ≤
        (block.horizon : ℝ≥0∞) * (block.successLower sigma)⁻¹ :=
      hbridge.trans hmean
    have hHne : (H : ℝ≥0∞) ≠ 0 := by
      intro hzero
      have hinfinite : (⊤ : ℝ≥0∞) ≤
          ENNReal.ofReal (2 * Real.exp (-rate / sigma ^ 2)) := by
        simpa only [H, hzero, ENNReal.inv_zero] using hHSigma
      exact (not_le_of_gt ENNReal.ofReal_lt_top) hinfinite
    have hHtop : (H : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top H
    have hdivide : survival ≤
        ((block.horizon : ℝ≥0∞) * (block.successLower sigma)⁻¹) /
          (H : ℝ≥0∞) := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl hHne) (Or.inl hHtop)).2
      simpa only [mul_comm] using htotal
    calc
      1 - gaussianEscapeProbability weighted
          (exponentialEscapeHorizon rate sigma) sigma = survival := rfl
      _ ≤ ((block.horizon : ℝ≥0∞) * (block.successLower sigma)⁻¹) /
          (H : ℝ≥0∞) := hdivide
      _ = (block.horizon : ℝ≥0∞) * (block.successLower sigma)⁻¹ *
          (H : ℝ≥0∞)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ majorant sigma := by
        exact mul_le_mul' (mul_le_mul' le_rfl hqSigma) hHSigma
  have hmajorantEq : majorant = fun sigma ↦
      ENNReal.ofReal
        ((block.horizon : ℝ) * 2 *
          Real.exp (-(gap / 2) / sigma ^ 2)) := by
    funext sigma
    have hexp :
        Real.exp
            ((gaussianVectorAction block.combinedCenter + epsilon) /
              sigma ^ 2) *
          Real.exp (-rate / sigma ^ 2) =
        Real.exp (-(gap / 2) / sigma ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [epsilon, gap]
      ring
    dsimp only [majorant]
    rw [← ENNReal.ofReal_natCast block.horizon]
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    calc
      (block.horizon : ℝ) *
          Real.exp
            ((gaussianVectorAction block.combinedCenter + epsilon) /
              sigma ^ 2) *
          (2 * Real.exp (-rate / sigma ^ 2)) =
        (block.horizon : ℝ) * 2 *
          (Real.exp
              ((gaussianVectorAction block.combinedCenter + epsilon) /
                sigma ^ 2) *
            Real.exp (-rate / sigma ^ 2)) := by ring
      _ = (block.horizon : ℝ) * 2 *
          Real.exp (-(gap / 2) / sigma ^ 2) := by rw [hexp]
  have hactivated :=
    tendsto_exp_neg_const_div_sq_nhdsGT_zero (half_pos hgap)
  have hreal : Tendsto
      (fun sigma : ℝ ↦ (block.horizon : ℝ) * 2 *
        Real.exp (-(gap / 2) / sigma ^ 2))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hactivated)
  have hmajorant : Tendsto majorant
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
    rw [hmajorantEq]
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hreal
  exact (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (0 : ℝ≥0∞))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0)).squeeze'
    hmajorant (Eventually.of_forall fun _ ↦ bot_le) hsurvival

/-- Equivalently, the crossing probability at that exponential horizon tends
to one. -/
theorem UniformRobustCrossingBlock.exponentialEscapeProbability_tendsto_one
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho rate : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (block : UniformRobustCrossingBlock weighted)
    (haction : gaussianVectorAction block.combinedCenter < rate) :
    Tendsto
      (fun sigma : ℝ ↦ gaussianEscapeProbability weighted
        (exponentialEscapeHorizon rate sigma) sigma)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 1) := by
  have hsurvival := block.exponentialSurvival_tendsto_zero
    model ss haction
  have hdouble : Tendsto
      (fun sigma : ℝ ↦ 1 -
        (1 - gaussianEscapeProbability weighted
          (exponentialEscapeHorizon rate sigma) sigma))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 1) := by
    simpa only [Function.comp_def, tsub_zero] using
      (ENNReal.continuous_sub_left ENNReal.one_ne_top).continuousAt.tendsto.comp
        hsurvival
  apply hdouble.congr'
  filter_upwards with sigma
  letI : IsProbabilityMeasure
      (standardGaussianVector (exponentialEscapeHorizon rate sigma)) := by
    unfold standardGaussianVector
    infer_instance
  exact ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one

/-- Paper II, Theorem `thm:rate`, escape-probability upper clause: for every
positive tolerance, crossing occurs by the real horizon
`exp((V^x + delta) / sigma²)` with probability tending to one. -/
theorem crossingUpperEscapeProbability
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho delta : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hdelta : 0 < delta) :
    Tendsto
      (fun sigma : ℝ ↦ gaussianEscapeProbability weighted
        (exponentialEscapeHorizon
          (civicCrossingQuasipotential weighted + delta) sigma) sigma)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 1) := by
  let epsilon : ℝ := delta / 4
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    linarith
  obtain ⟨block, hnear, haway⟩ :=
    exists_uniformRobustCrossingBlock
      model ss threshold hrho hcoop weighted hepsilon
  have hactionLe : gaussianVectorAction block.combinedCenter ≤
      civicCrossingQuasipotential weighted + 2 * epsilon := by
    rw [block.combinedCenter_action]
    linarith
  have haction : gaussianVectorAction block.combinedCenter <
      civicCrossingQuasipotential weighted + delta := by
    apply hactionLe.trans_lt
    dsimp only [epsilon]
    linarith
  exact block.exponentialEscapeProbability_tendsto_one
    model ss haction

/-! ## Paper theorem assembly -/

/-- Paper II, Theorem `thm:rate` in `civic_drift.tex`, upper-rate half.
The crossing quasipotential lies between the printed barriers and the
basin-exit quasipotential; crossing by every slightly larger
exponential horizon has probability tending to one; the mean-time limsup is
at most `V^x`; and the fixed-primitives small-adaptation-rate pinch is exact.
-/
theorem crossingUpperRate
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho L : ℝ} (hrho : 0 ≤ rho) (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    ((2 / (p.α * (1 + 2 * p.α * L))) *
          (∫ b in (0 : ℝ)..weighted.βdagger,
            weightedBarrierIntegrand p rho b) ≤
        civicCrossingQuasipotential weighted ∧
      civicCrossingQuasipotential weighted ≤ civicQuasipotential p rho ∧
      civicQuasipotential p rho ≤ upwardStrategyCost weighted) ∧
    (∀ delta : ℝ, 0 < delta →
      Tendsto
        (fun sigma : ℝ ↦ gaussianEscapeProbability weighted
          (exponentialEscapeHorizon
            (civicCrossingQuasipotential weighted + delta) sigma) sigma)
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 1)) ∧
    limsup (meanGaussianEscapeLogRate weighted)
        (nhdsWithin 0 (Ioi (0 : ℝ))) ≤
      ((civicCrossingQuasipotential weighted : ℝ) : EReal) ∧
    Tendsto
      (fun alpha : ℝ ↦
        alpha * civicCrossingQuasipotentialAtRate weighted alpha)
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds (2 * weightedBarrierArea weighted)) := by
  exact ⟨crossingQuasipotential_bracket
      model ss threshold hrho hrhoCure hcoop weighted hL,
    fun delta hdelta ↦ crossingUpperEscapeProbability
      model ss threshold hrho hcoop weighted hdelta,
    crossingUpperMeanRate model ss threshold hrho hcoop weighted,
    civicCrossingQuasipotentialAtRate_tendsto_barrier
      model ss threshold hrho hrhoCure hcoop weighted⟩

#print axioms gaussianVectorAction_append
#print axioms RobustCrossingTube.padRight
#print axioms exists_funnelledRobustCrossingTube
#print axioms RobustCrossingTube.horizon_pos_of_calibrated_mem
#print axioms UniformRobustCrossingBlock.mem_near_or_away
#print axioms exists_uniformRobustCrossingBlock
#print axioms UniformRobustCrossingBlock.successLower_eq_mul
#print axioms UniformRobustCrossingBlock.successLower_le_crossingProbability
#print axioms UniformRobustCrossingBlock.combinedCenter_action
#print axioms UniformRobustCrossingBlock.successLower_pos
#print axioms UniformRobustCrossingBlock.survival_mul_le_pow
#print axioms UniformRobustCrossingBlock.meanGaussianEscapeTime_le
#print axioms UniformRobustCrossingBlock.successLowerLogRate_eq
#print axioms UniformRobustCrossingBlock.successLowerLogRate_tendsto
#print axioms UniformRobustCrossingBlock.meanGaussianEscapeLogRate_limsup_le
#print axioms meanGaussianEscapeLogRate_limsup_le_add
#print axioms crossingUpperMeanRate
#print axioms half_le_natFloor_of_two_le
#print axioms tendsto_exp_const_div_sq_atTop_nhdsGT_zero
#print axioms eventually_exponentialEscapeHorizon_inv_le
#print axioms UniformRobustCrossingBlock.eventually_successLower_inv_le_exp
#print axioms UniformRobustCrossingBlock.exponentialSurvival_tendsto_zero
#print axioms UniformRobustCrossingBlock.exponentialEscapeProbability_tendsto_one
#print axioms crossingUpperEscapeProbability
#print axioms crossingUpperRate

end

end CivicAlignment.PaperII
