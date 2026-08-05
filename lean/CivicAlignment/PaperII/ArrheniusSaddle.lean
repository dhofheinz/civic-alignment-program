/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.ArrheniusPersistence
import CivicAlignment.PaperII.ArrheniusRestart
import CivicAlignment.PaperII.BistabilityTopology
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Paper II: weighted-saddle expansion for Arrhenius persistence

The persistence half of `thm:arr` must control residence near the civic-weighted
saddle without strengthening the paper's weak small-step assumption to
`(SS⁺)`.  This file isolates the local deterministic geometry used by that
argument.  The weighted Jacobian has a real expanding root under exactly
`(SS)`, the cooperativity window, and the ascending weighted threshold.
-/

namespace CivicAlignment.PaperII

open Filter Function MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal

noncomputable section

/-! ## The weighted interior Jacobian -/

/-- The stationary-gradient root in `WeightedThresholdAssumption` is the same
interior crossing as the price equation used by `Hysteresis.lean`. -/
theorem WeightedThresholdAssumption.weightedCureThreshold_eq
    {p : LoopParams} (model : DriftModelAssumptions p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) :
    weightedCureThreshold p weighted.βdagger = rho := by
  have hbeta : weighted.βdagger ∈ Icc (0 : ℝ) 1 :=
    ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩
  have hgradient :
      civicWeightedGradient p rho weighted.βdagger
          (p.stationaryStock weighted.βdagger) = 0 := by
    rw [civicWeightedGradient_stationary_eq_weightedStationaryGradient
      rho hbeta]
    exact weighted.gradient_zero
  rw [civicWeightedGradient_stationary_eq model hbeta] at hgradient
  have hstock : 0 < p.stationaryStock weighted.βdagger :=
    model.I_pos.trans_le (stationaryStock_mem_stockInterval model hbeta).1
  nlinarith

/-- Under the Arrhenius hypotheses, the weighted saddle Jacobian has
nonnegative diagonal entries, strictly positive off-diagonal entries, and its
stock diagonal is strictly below one. -/
theorem weightedSaddleJacobian_entry_bounds
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) :
    let J := weightedInteriorLoopJacobian p rho weighted.βdagger
      (p.stationaryStock weighted.βdagger)
    0 ≤ J.a ∧ J.a ≤ 1 ∧ 0 < J.b ∧ 0 < J.cJ ∧
      0 ≤ J.d ∧ J.d < 1 := by
  exact weightedCrossingJacobian_entry_bounds model ss
    weighted.βdagger_mem (weighted.weightedCureThreshold_eq model)

/-- At the stationary weighted saddle, the characteristic polynomial at one
is the negative weighted stationary-gradient slope times a positive scale.
This is the weighted form of the shared `eq:p1` identity. -/
theorem weightedSaddleJacobian_charPoly_one_eq
    {p : LoopParams} (model : DriftModelAssumptions p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) :
    let beta := weighted.βdagger
    let J := weightedInteriorLoopJacobian p rho beta
      (p.stationaryStock beta)
    J.charPoly 1 =
      -p.α * (1 - p.s beta) *
        weightedStationaryGradientSlope p rho beta := by
  let beta := weighted.βdagger
  have hbeta : beta ∈ Icc (0 : ℝ) 1 :=
    ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩
  have hden : 1 - p.s beta ≠ 0 := (one_sub_s_pos model hbeta).ne'
  simp only [LoopJacobian.charPoly, LoopJacobian.trace, LoopJacobian.det,
    weightedInteriorLoopJacobian, weightedStationaryGradientSlope,
    LoopParams.GSlope, LoopParams.stationaryStock, model.no_content_gain,
    sub_zero]
  field_simp [hden]
  ring

/-- The weighted saddle has a real expanding multiplier under the weak
small-step assumption used by `thm:arr`; no global-convergence or `(SS⁺)`
hypothesis is required. -/
theorem weightedSaddle_largerEigenvalue_gt_one
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) :
    let J := weightedInteriorLoopJacobian p rho weighted.βdagger
      (p.stationaryStock weighted.βdagger)
    1 < J.largerEigenvalue := by
  let beta := weighted.βdagger
  let J := weightedInteriorLoopJacobian p rho beta
    (p.stationaryStock beta)
  have hentries := weightedSaddleJacobian_entry_bounds
    model ss weighted
  have hdisc : 0 ≤ J.discriminant :=
    J.discriminant_nonneg hentries.2.2.1.le hentries.2.2.2.1.le
  have hsmall : J.smallerEigenvalue < 1 :=
    J.smallerEigenvalue_lt_one hentries.2.2.2.2.2
      (mul_nonneg hentries.2.2.1.le hentries.2.2.2.1.le)
  have hbeta : beta ∈ Icc (0 : ℝ) 1 :=
    ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩
  have hden : 0 < 1 - p.s beta := one_sub_s_pos model hbeta
  have hpoly : J.charPoly 1 < 0 := by
    rw [show J.charPoly 1 =
        -p.α * (1 - p.s beta) *
          weightedStationaryGradientSlope p rho beta by
      simpa only [J, beta] using
        weightedSaddleJacobian_charPoly_one_eq model weighted]
    have hnegative : -p.α * (1 - p.s beta) < 0 := by
      nlinarith [model.α_pos, hden]
    exact mul_neg_of_neg_of_pos hnegative weighted.gradientSlope_pos
  exact (J.largerEigenvalue_gt_one_iff_charPoly_one_neg hdisc hsmall).2 hpoly

/-! ## Exact ordered differences -/

/-- Exact coefficients for the difference of two civic-weighted steps with
the same control. -/
def weightedOrderedDifferenceCoefficients (p : LoopParams) (rho : ℝ)
    (x y : LoopState) : LoopJacobian where
  a := 1 - 2 * p.α * p.c ^ 2 * y.2
  b := p.α * (2 * p.c * (1 - p.c * x.1) - rho)
  cJ := (1 - p.lambda₀) * p.η *
    (2 * (1 - p.η) + p.η * (x.1 + y.1)) * y.2
  d := p.s x.1

/-- At coincident states, the weighted ordered-difference coefficients are
the ordinary weighted interior Jacobian. -/
theorem weightedOrderedDifferenceCoefficients_self
    (p : LoopParams) (rho : ℝ) (x : LoopState) :
    weightedOrderedDifferenceCoefficients p rho x x =
      weightedInteriorLoopJacobian p rho x.1 x.2 := by
  rcases x with ⟨beta, D⟩
  simp only [weightedOrderedDifferenceCoefficients,
    weightedInteriorLoopJacobian, LoopParams.sSlope]
  congr 1
  ring

/-- The policy-diagonal weighted difference coefficient is continuous. -/
theorem continuous_weightedOrderedDifferenceCoefficients_a
    (p : LoopParams) (rho : ℝ) :
    Continuous (fun z : LoopState × LoopState ↦
      (weightedOrderedDifferenceCoefficients p rho z.1 z.2).a) := by
  simp only [weightedOrderedDifferenceCoefficients]
  fun_prop

/-- The stock-to-policy weighted difference coefficient is continuous. -/
theorem continuous_weightedOrderedDifferenceCoefficients_b
    (p : LoopParams) (rho : ℝ) :
    Continuous (fun z : LoopState × LoopState ↦
      (weightedOrderedDifferenceCoefficients p rho z.1 z.2).b) := by
  simp only [weightedOrderedDifferenceCoefficients]
  fun_prop

/-- The policy-to-stock weighted difference coefficient is continuous. -/
theorem continuous_weightedOrderedDifferenceCoefficients_cJ
    (p : LoopParams) (rho : ℝ) :
    Continuous (fun z : LoopState × LoopState ↦
      (weightedOrderedDifferenceCoefficients p rho z.1 z.2).cJ) := by
  simp only [weightedOrderedDifferenceCoefficients]
  fun_prop

/-- The stock-diagonal weighted difference coefficient is continuous. -/
theorem continuous_weightedOrderedDifferenceCoefficients_d
    (p : LoopParams) (rho : ℝ) :
    Continuous (fun z : LoopState × LoopState ↦
      (weightedOrderedDifferenceCoefficients p rho z.1 z.2).d) := by
  simp only [weightedOrderedDifferenceCoefficients, LoopParams.s]
  fun_prop

/-- When both projected outputs are interior, equal controls cancel from the
ordered difference and the two coordinate gaps obey the exact weighted linear
identities. -/
theorem controlledCivicWeightedStep_orderedDifference_eq
    {p : LoopParams} (model : DriftModelAssumptions p) (rho u : ℝ)
    (x y : LoopState)
    (hxout : (controlledCivicWeightedStep p rho u x).1 ∈ Ioo (0 : ℝ) 1)
    (hyout : (controlledCivicWeightedStep p rho u y).1 ∈ Ioo (0 : ℝ) 1) :
    let C := weightedOrderedDifferenceCoefficients p rho x y
    (controlledCivicWeightedStep p rho u y).1 -
          (controlledCivicWeightedStep p rho u x).1 =
        C.a * (y.1 - x.1) + C.b * (y.2 - x.2) ∧
      (controlledCivicWeightedStep p rho u y).2 -
          (controlledCivicWeightedStep p rho u x).2 =
        C.cJ * (y.1 - x.1) + C.d * (y.2 - x.2) := by
  let C := weightedOrderedDifferenceCoefficients p rho x y
  have hxclip :
      LoopParams.clipUnit
          (x.1 + p.α * (civicWeightedGradient p rho x.1 x.2 + u)) =
        (controlledCivicWeightedStep p rho u x).1 := rfl
  have hyclip :
      LoopParams.clipUnit
          (y.1 + p.α * (civicWeightedGradient p rho y.1 y.2 + u)) =
        (controlledCivicWeightedStep p rho u y).1 := rfl
  have hxinput := (clipUnit_eq_interior_iff hxout).mp hxclip
  have hyinput := (clipUnit_eq_interior_iff hyout).mp hyclip
  constructor
  · simp only [weightedOrderedDifferenceCoefficients]
    simp only [civicWeightedGradient, LoopParams.gradU] at hxinput hyinput
    rw [← hxinput, ← hyinput]
    ring
  · simp only [weightedOrderedDifferenceCoefficients,
      controlledCivicWeightedStep, LoopParams.stockStep,
      model.no_content_gain, add_zero, LoopParams.s]
    ring

/-! ## A robust expanding functional -/

/-- Coefficient on the policy gap after evaluating the next gap with the
larger-root left eigenfunctional of `J`. -/
def unstablePolicyGain (J C : LoopJacobian) : ℝ :=
  J.cJ * C.a + (J.largerEigenvalue - J.a) * C.cJ

/-- Coefficient on the stock gap after evaluating the next gap with the
larger-root left eigenfunctional of `J`. -/
def unstableStockGain (J C : LoopJacobian) : ℝ :=
  J.cJ * C.b + (J.largerEigenvalue - J.a) * C.d

/-- At the linearization itself, the policy-gap gain is exactly the larger
eigenvalue times the policy weight. -/
theorem unstablePolicyGain_self (J : LoopJacobian)
    (hdisc : 0 ≤ J.discriminant) :
    unstablePolicyGain J J = J.largerEigenvalue * J.cJ := by
  simpa only [unstablePolicyGain, unstableFunctional, mul_one, mul_zero,
    add_zero] using unstableFunctional_jacobian J hdisc 1 0

/-- At the linearization itself, the stock-gap gain is exactly the larger
eigenvalue times the stock weight. -/
theorem unstableStockGain_self (J : LoopJacobian)
    (hdisc : 0 ≤ J.discriminant) :
    unstableStockGain J J =
      J.largerEigenvalue * (J.largerEigenvalue - J.a) := by
  simpa only [unstableStockGain, unstableFunctional, mul_zero, mul_one,
    zero_add] using unstableFunctional_jacobian J hdisc 0 1

/-- Near the weighted saddle, the positive-cone gap between two equally
controlled steps expands in the larger-root left eigenfunctional by a fixed
factor `mu > 1`.  The statement is local in the pair of input states; output
interiority records exactly where projection is inactive. -/
theorem exists_weightedSaddle_eventually_coneExpansion
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) :
    let q := weightedSaddlePoint weighted
    let J := weightedInteriorLoopJacobian p rho weighted.βdagger
      (p.stationaryStock weighted.βdagger)
    ∃ mu : ℝ, 1 < mu ∧
      ∀ᶠ z : LoopState × LoopState in 𝓝 (q, q),
        ∀ u : ℝ,
          z.1 ≤ z.2 →
          (controlledCivicWeightedStep p rho u z.1).1 ∈ Ioo (0 : ℝ) 1 →
          (controlledCivicWeightedStep p rho u z.2).1 ∈ Ioo (0 : ℝ) 1 →
          mu * unstableFunctional J
              (z.2.1 - z.1.1) (z.2.2 - z.1.2) ≤
            unstableFunctional J
              ((controlledCivicWeightedStep p rho u z.2).1 -
                (controlledCivicWeightedStep p rho u z.1).1)
              ((controlledCivicWeightedStep p rho u z.2).2 -
                (controlledCivicWeightedStep p rho u z.1).2) := by
  let q := weightedSaddlePoint weighted
  let J := weightedInteriorLoopJacobian p rho weighted.βdagger
    (p.stationaryStock weighted.βdagger)
  let scale := saddleExpansionScale J
  let mu := scale * J.largerEigenvalue
  let C := fun z : LoopState × LoopState ↦
    weightedOrderedDifferenceCoefficients p rho z.1 z.2
  have hentries := weightedSaddleJacobian_entry_bounds model ss weighted
  have hlarge := weightedSaddle_largerEigenvalue_gt_one model ss weighted
  have hdisc : 0 ≤ J.discriminant :=
    J.discriminant_nonneg hentries.2.2.1.le hentries.2.2.2.1.le
  have hscale := saddleExpansionScale_spec J hlarge
  have hmu : 1 < mu := by simpa only [mu, scale] using hscale.2.2
  have hpolicyWeight : 0 < J.cJ := hentries.2.2.2.1
  have hstockWeight : 0 < J.largerEigenvalue - J.a := by
    linarith [hentries.2.1, hlarge]
  have hCself : C (q, q) = J := by
    simp only [C, weightedOrderedDifferenceCoefficients_self, q,
      weightedSaddlePoint, J]
  have hpolicyValue :
      unstablePolicyGain J (C (q, q)) =
        J.largerEigenvalue * J.cJ := by
    rw [hCself]
    exact unstablePolicyGain_self J hdisc
  have hstockValue :
      unstableStockGain J (C (q, q)) =
        J.largerEigenvalue * (J.largerEigenvalue - J.a) := by
    rw [hCself]
    exact unstableStockGain_self J hdisc
  have hpolicyContinuous :
      Continuous (fun z : LoopState × LoopState ↦
        unstablePolicyGain J (C z)) := by
    simp only [unstablePolicyGain, C,
      weightedOrderedDifferenceCoefficients]
    fun_prop
  have hstockContinuous :
      Continuous (fun z : LoopState × LoopState ↦
        unstableStockGain J (C z)) := by
    simp only [unstableStockGain, C,
      weightedOrderedDifferenceCoefficients, LoopParams.s]
    fun_prop
  have hpolicyTendsto := hpolicyContinuous.tendsto (q, q)
  have hstockTendsto := hstockContinuous.tendsto (q, q)
  rw [hpolicyValue] at hpolicyTendsto
  rw [hstockValue] at hstockTendsto
  have hpolicyTarget :
      mu * J.cJ < J.largerEigenvalue * J.cJ := by
    have hfactor : 0 < J.largerEigenvalue * J.cJ :=
      mul_pos (zero_lt_one.trans hlarge) hpolicyWeight
    have h := mul_lt_mul_of_pos_right hscale.2.1 hfactor
    simpa only [mu, scale, mul_assoc, one_mul] using h
  have hstockTarget :
      mu * (J.largerEigenvalue - J.a) <
        J.largerEigenvalue * (J.largerEigenvalue - J.a) := by
    have hfactor :
        0 < J.largerEigenvalue * (J.largerEigenvalue - J.a) :=
      mul_pos (zero_lt_one.trans hlarge) hstockWeight
    have h := mul_lt_mul_of_pos_right hscale.2.1 hfactor
    simpa only [mu, scale, mul_assoc, one_mul] using h
  refine ⟨mu, hmu, ?_⟩
  filter_upwards
    [hpolicyTendsto.eventually_const_lt hpolicyTarget,
      hstockTendsto.eventually_const_lt hstockTarget]
      with z hpolicy hstock
  intro u hxy hxout hyout
  have hbetaGap : 0 ≤ z.2.1 - z.1.1 := sub_nonneg.mpr hxy.1
  have hstockGap : 0 ≤ z.2.2 - z.1.2 := sub_nonneg.mpr hxy.2
  have hdiff := controlledCivicWeightedStep_orderedDifference_eq
    model rho u z.1 z.2 hxout hyout
  have hpolicyScaled :=
    mul_le_mul_of_nonneg_right hpolicy.le hbetaGap
  have hstockScaled :=
    mul_le_mul_of_nonneg_right hstock.le hstockGap
  calc
    mu * unstableFunctional J
        (z.2.1 - z.1.1) (z.2.2 - z.1.2) =
        (mu * J.cJ) * (z.2.1 - z.1.1) +
          (mu * (J.largerEigenvalue - J.a)) *
            (z.2.2 - z.1.2) := by
      simp only [unstableFunctional]
      ring
    _ ≤ unstablePolicyGain J (C z) * (z.2.1 - z.1.1) +
          unstableStockGain J (C z) * (z.2.2 - z.1.2) :=
      add_le_add hpolicyScaled hstockScaled
    _ = unstableFunctional J
          ((controlledCivicWeightedStep p rho u z.2).1 -
            (controlledCivicWeightedStep p rho u z.1).1)
          ((controlledCivicWeightedStep p rho u z.2).2 -
            (controlledCivicWeightedStep p rho u z.1).2) := by
      rw [hdiff.1, hdiff.2]
      simp only [unstablePolicyGain, unstableStockGain,
        unstableFunctional, C]
      ring

/-- Metric-ball form of the local cone expansion, ready for a saddle-sojourn
argument. -/
theorem exists_weightedSaddle_ball_coneExpansion
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) :
    let q := weightedSaddlePoint weighted
    let J := weightedInteriorLoopJacobian p rho weighted.βdagger
      (p.stationaryStock weighted.βdagger)
    ∃ mu : ℝ, 1 < mu ∧ ∃ radius : ℝ, 0 < radius ∧
      ∀ (x y : LoopState) (u : ℝ),
        dist (x, y) (q, q) < radius →
        x ≤ y →
        (controlledCivicWeightedStep p rho u x).1 ∈ Ioo (0 : ℝ) 1 →
        (controlledCivicWeightedStep p rho u y).1 ∈ Ioo (0 : ℝ) 1 →
        mu * unstableFunctional J (y.1 - x.1) (y.2 - x.2) ≤
          unstableFunctional J
            ((controlledCivicWeightedStep p rho u y).1 -
              (controlledCivicWeightedStep p rho u x).1)
            ((controlledCivicWeightedStep p rho u y).2 -
              (controlledCivicWeightedStep p rho u x).2) := by
  obtain ⟨mu, hmu, hexpand⟩ :=
    exists_weightedSaddle_eventually_coneExpansion model ss weighted
  obtain ⟨radius, hradius, hball⟩ :=
    Metric.eventually_nhds_iff.mp hexpand
  exact ⟨mu, hmu, radius, hradius,
    fun x y u hnear hxy hxout hyout ↦
      hball hnear u hxy hxout hyout⟩

/-- A state sufficiently close to the interior weighted saddle has interior
policy coordinate. -/
theorem policy_mem_Ioo_of_dist_weightedSaddle_lt
    {p : LoopParams} {rho radius : ℝ}
    (weighted : WeightedThresholdAssumption p rho) {x : LoopState}
    (hradiusLeft : radius ≤ weighted.βdagger)
    (hradiusRight : radius ≤ 1 - weighted.βdagger)
    (hx : dist x (weightedSaddlePoint weighted) < radius) :
    x.1 ∈ Ioo (0 : ℝ) 1 := by
  have hxPolicy : dist x.1 weighted.βdagger < radius := by
    rw [Prod.dist_eq, max_lt_iff] at hx
    exact hx.1
  rw [Real.dist_eq] at hxPolicy
  have habs := abs_lt.mp hxPolicy
  constructor <;> nlinarith

/-- A saddle chart that packages both cone expansion and projection
inactivity: if two ordered trajectories remain in this ball for one more
step, their unstable functional expands by `mu > 1`. -/
theorem exists_weightedSaddle_sojournChart
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) :
    let q := weightedSaddlePoint weighted
    let J := weightedInteriorLoopJacobian p rho weighted.βdagger
      (p.stationaryStock weighted.βdagger)
    ∃ mu : ℝ, 1 < mu ∧ ∃ radius : ℝ, 0 < radius ∧
      ∀ (x y : LoopState) (u : ℝ),
        dist x q < radius →
        dist y q < radius →
        dist (controlledCivicWeightedStep p rho u x) q < radius →
        dist (controlledCivicWeightedStep p rho u y) q < radius →
        x ≤ y →
        mu * unstableFunctional J (y.1 - x.1) (y.2 - x.2) ≤
          unstableFunctional J
            ((controlledCivicWeightedStep p rho u y).1 -
              (controlledCivicWeightedStep p rho u x).1)
            ((controlledCivicWeightedStep p rho u y).2 -
              (controlledCivicWeightedStep p rho u x).2) := by
  obtain ⟨mu, hmu, pairRadius, hpairRadius, hexpand⟩ :=
    exists_weightedSaddle_ball_coneExpansion model ss weighted
  let radius := min (pairRadius / 2)
    (min (weighted.βdagger / 2) ((1 - weighted.βdagger) / 2))
  have hradius : 0 < radius := by
    dsimp only [radius]
    rw [lt_min_iff, lt_min_iff]
    exact ⟨div_pos hpairRadius (by norm_num),
      div_pos weighted.βdagger_mem.1 (by norm_num),
      div_pos (sub_pos.mpr weighted.βdagger_mem.2) (by norm_num)⟩
  have hradiusPair : radius < pairRadius := by
    calc
      radius ≤ pairRadius / 2 := min_le_left _ _
      _ < pairRadius := by linarith
  have hradiusLeft : radius ≤ weighted.βdagger := by
    calc
      radius ≤ weighted.βdagger / 2 :=
        (min_le_right _ _).trans (min_le_left _ _)
      _ ≤ weighted.βdagger := by linarith [weighted.βdagger_mem.1]
  have hradiusRight : radius ≤ 1 - weighted.βdagger := by
    calc
      radius ≤ (1 - weighted.βdagger) / 2 :=
        (min_le_right _ _).trans (min_le_right _ _)
      _ ≤ 1 - weighted.βdagger := by
        linarith [weighted.βdagger_mem.2]
  refine ⟨mu, hmu, radius, hradius,
    fun x y u hx hy hxnext hynext hxy ↦ ?_⟩
  have hpair :
      dist (x, y)
          (weightedSaddlePoint weighted, weightedSaddlePoint weighted) <
        pairRadius := by
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨hx.trans hradiusPair, hy.trans hradiusPair⟩
  exact hexpand x y u hpair hxy
    (policy_mem_Ioo_of_dist_weightedSaddle_lt weighted
      hradiusLeft hradiusRight hxnext)
    (policy_mem_Ioo_of_dist_weightedSaddle_lt weighted
      hradiusLeft hradiusRight hynext)

/-- The larger-root functional of an ordered pair inside a state ball has an
explicit terminal width. -/
theorem unstableFunctional_ordered_gap_le_of_dist_lt
    (J : LoopJacobian) {q x y : LoopState} {radius : ℝ}
    (hJc : 0 ≤ J.cJ)
    (hstockWeight : 0 ≤ J.largerEigenvalue - J.a)
    (hx : dist x q < radius) (hy : dist y q < radius) :
    unstableFunctional J (y.1 - x.1) (y.2 - x.2) ≤
      2 * radius * (J.cJ + (J.largerEigenvalue - J.a)) := by
  rw [Prod.dist_eq, max_lt_iff] at hx hy
  have hxPolicy := hx.1
  have hyPolicy := hy.1
  have hxStock := hx.2
  have hyStock := hy.2
  rw [Real.dist_eq] at hxPolicy hyPolicy hxStock hyStock
  have hpolicyGap : y.1 - x.1 ≤ 2 * radius := by
    have hxl := (abs_lt.mp hxPolicy).1
    have hyr := (abs_lt.mp hyPolicy).2
    nlinarith
  have hstockGap : y.2 - x.2 ≤ 2 * radius := by
    have hxl := (abs_lt.mp hxStock).1
    have hyr := (abs_lt.mp hyStock).2
    nlinarith
  have hpolicyScaled :=
    mul_le_mul_of_nonneg_left hpolicyGap hJc
  have hstockScaled :=
    mul_le_mul_of_nonneg_left hstockGap hstockWeight
  simp only [unstableFunctional]
  nlinarith

/-! ## Iterating the cone expansion -/

/-- Adding the same policy-gradient control to both states preserves the
weighted map's order on the absorbing box. -/
theorem controlledCivicWeightedStep_monotoneOn_box
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

/-- A one-step local expansion iterates geometrically along two ordered paths
with the same control history, as long as both remain in the local saddle
chart and projection stays inactive. -/
theorem unstableFunctional_gap_pow_le_of_localExpansion
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    {q : LoopState} {J : LoopJacobian} {mu radius : ℝ}
    (hmu : 0 ≤ mu)
    (hlocal : ∀ (x y : LoopState) (u : ℝ),
      dist (x, y) (q, q) < radius →
      x ≤ y →
      (controlledCivicWeightedStep p rho u x).1 ∈ Ioo (0 : ℝ) 1 →
      (controlledCivicWeightedStep p rho u y).1 ∈ Ioo (0 : ℝ) 1 →
      mu * unstableFunctional J (y.1 - x.1) (y.2 - x.2) ≤
        unstableFunctional J
          ((controlledCivicWeightedStep p rho u y).1 -
            (controlledCivicWeightedStep p rho u x).1)
          ((controlledCivicWeightedStep p rho u y).2 -
            (controlledCivicWeightedStep p rho u x).2))
    (x y : ℕ → LoopState) (u : ℕ → ℝ)
    (hxstep : ∀ n,
      x (n + 1) = controlledCivicWeightedStep p rho (u n) (x n))
    (hystep : ∀ n,
      y (n + 1) = controlledCivicWeightedStep p rho (u n) (y n))
    (hboxx : ∀ n, x n ∈ absorbingBox p)
    (hboxy : ∀ n, y n ∈ absorbingBox p)
    (hxy : x 0 ≤ y 0) {N : ℕ}
    (hnear : ∀ n < N, dist (x n, y n) (q, q) < radius)
    (hxinterior : ∀ n < N, (x (n + 1)).1 ∈ Ioo (0 : ℝ) 1)
    (hyinterior : ∀ n < N, (y (n + 1)).1 ∈ Ioo (0 : ℝ) 1) :
    mu ^ N * unstableFunctional J
        ((y 0).1 - (x 0).1) ((y 0).2 - (x 0).2) ≤
      unstableFunctional J
        ((y N).1 - (x N).1) ((y N).2 - (x N).2) := by
  have horder : ∀ n, x n ≤ y n := by
    intro n
    induction n with
    | zero => exact hxy
    | succ n ih =>
        rw [show n + 1 = Nat.succ n by omega, hxstep n, hystep n]
        exact controlledCivicWeightedStep_monotoneOn_box
          model ss hcoop (u n) (hboxx n) (hboxy n) ih
  have honeStep : ∀ n < N,
      mu * unstableFunctional J
          ((y n).1 - (x n).1) ((y n).2 - (x n).2) ≤
        unstableFunctional J
          ((y (n + 1)).1 - (x (n + 1)).1)
          ((y (n + 1)).2 - (x (n + 1)).2) := by
    intro n hn
    rw [hxstep n, hystep n]
    exact hlocal (x n) (y n) (u n) (hnear n hn) (horder n)
      (by simpa only [hxstep n] using hxinterior n hn)
      (by simpa only [hystep n] using hyinterior n hn)
  have hpow : ∀ n ≤ N,
      mu ^ n * unstableFunctional J
          ((y 0).1 - (x 0).1) ((y 0).2 - (x 0).2) ≤
        unstableFunctional J
          ((y n).1 - (x n).1) ((y n).2 - (x n).2) := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
        have hnlt : n < N := by omega
        have hscaled := mul_le_mul_of_nonneg_left (ih (by omega)) hmu
        calc
          mu ^ (n + 1) * unstableFunctional J
              ((y 0).1 - (x 0).1) ((y 0).2 - (x 0).2) =
              mu * (mu ^ n * unstableFunctional J
                ((y 0).1 - (x 0).1) ((y 0).2 - (x 0).2)) := by
            rw [pow_succ]
            ring
          _ ≤ mu * unstableFunctional J
              ((y n).1 - (x n).1) ((y n).2 - (x n).2) := hscaled
          _ ≤ unstableFunctional J
              ((y (n + 1)).1 - (x (n + 1)).1)
              ((y (n + 1)).2 - (x (n + 1)).2) := honeStep n hnlt
  exact hpow N le_rfl

/-! ## One-coordinate lookback fibers -/

/-- The future orbit after a distinguished one-step control at the lookback
time.  Varying `first` while fixing `future` is the fiber used for Gaussian
anti-concentration. -/
def saddleLookbackOrbit (p : LoopParams) (rho : ℝ) (z : LoopState)
    (first : ℝ) (future : ℕ → ℝ) : ℕ → LoopState :=
  controlledCivicWeightedOrbitFrom p rho
    (controlledCivicWeightedStep p rho first z) future

/-- Once both outputs are interior, changing only the control changes the
next policy by exactly `α` times the control change. -/
theorem controlledCivicWeightedStep_policy_sub_eq_alpha_mul
    {p : LoopParams} (rho : ℝ) (z : LoopState) {first second : ℝ}
    (hfirst : (controlledCivicWeightedStep p rho first z).1 ∈ Ioo (0 : ℝ) 1)
    (hsecond : (controlledCivicWeightedStep p rho second z).1 ∈ Ioo (0 : ℝ) 1) :
    (controlledCivicWeightedStep p rho second z).1 -
        (controlledCivicWeightedStep p rho first z).1 =
      p.α * (second - first) := by
  have hfirstClip :
      LoopParams.clipUnit
          (z.1 + p.α * (civicWeightedGradient p rho z.1 z.2 + first)) =
        (controlledCivicWeightedStep p rho first z).1 := rfl
  have hsecondClip :
      LoopParams.clipUnit
          (z.1 + p.α * (civicWeightedGradient p rho z.1 z.2 + second)) =
        (controlledCivicWeightedStep p rho second z).1 := rfl
  have hfirstInput := (clipUnit_eq_interior_iff hfirst).mp hfirstClip
  have hsecondInput := (clipUnit_eq_interior_iff hsecond).mp hsecondClip
  rw [← hfirstInput, ← hsecondInput]
  ring

/-- Ordered lookback controls produce ordered first states. -/
theorem saddleLookbackOrbit_zero_mono
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    (z : LoopState) (future : ℕ → ℝ) {first second : ℝ}
    (hcontrols : first ≤ second) :
    saddleLookbackOrbit p rho z first future 0 ≤
      saddleLookbackOrbit p rho z second future 0 := by
  have hinput :
      z.1 + p.α * (civicWeightedGradient p rho z.1 z.2 + first) ≤
        z.1 + p.α * (civicWeightedGradient p rho z.1 z.2 + second) := by
    nlinarith [model.α_pos]
  exact ⟨by
      simpa only [saddleLookbackOrbit, controlledCivicWeightedOrbitFrom,
        controlledCivicWeightedStep] using LoopParams.monotone_clipUnit hinput,
    le_rfl⟩

/-- The geometric cone expansion makes every admissible lookback fiber thin:
if two first controls with the same future both realize an `N`-step local
sojourn, their separation is bounded by the terminal functional width divided
by `mu^N`. -/
theorem saddleLookback_control_sub_le_of_functional_bound
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    {q : LoopState} {J : LoopJacobian} {mu radius M : ℝ}
    (hmu : 1 < mu) (hJc : 0 < J.cJ)
    (hlocal : ∀ (x y : LoopState) (u : ℝ),
      dist (x, y) (q, q) < radius →
      x ≤ y →
      (controlledCivicWeightedStep p rho u x).1 ∈ Ioo (0 : ℝ) 1 →
      (controlledCivicWeightedStep p rho u y).1 ∈ Ioo (0 : ℝ) 1 →
      mu * unstableFunctional J (y.1 - x.1) (y.2 - x.2) ≤
        unstableFunctional J
          ((controlledCivicWeightedStep p rho u y).1 -
            (controlledCivicWeightedStep p rho u x).1)
          ((controlledCivicWeightedStep p rho u y).2 -
            (controlledCivicWeightedStep p rho u x).2))
    (z : LoopState) (future : ℕ → ℝ) {first second : ℝ}
    (hcontrols : first ≤ second)
    (hfirstInterior :
      (controlledCivicWeightedStep p rho first z).1 ∈ Ioo (0 : ℝ) 1)
    (hsecondInterior :
      (controlledCivicWeightedStep p rho second z).1 ∈ Ioo (0 : ℝ) 1)
    {N : ℕ}
    (hboxFirst : ∀ n, saddleLookbackOrbit p rho z first future n ∈
      absorbingBox p)
    (hboxSecond : ∀ n, saddleLookbackOrbit p rho z second future n ∈
      absorbingBox p)
    (hnear : ∀ n < N,
      dist
        (saddleLookbackOrbit p rho z first future n,
          saddleLookbackOrbit p rho z second future n)
        (q, q) < radius)
    (hfirstFutureInterior : ∀ n < N,
      (saddleLookbackOrbit p rho z first future (n + 1)).1 ∈
        Ioo (0 : ℝ) 1)
    (hsecondFutureInterior : ∀ n < N,
      (saddleLookbackOrbit p rho z second future (n + 1)).1 ∈
        Ioo (0 : ℝ) 1)
    (hterminal :
      unstableFunctional J
          ((saddleLookbackOrbit p rho z second future N).1 -
            (saddleLookbackOrbit p rho z first future N).1)
          ((saddleLookbackOrbit p rho z second future N).2 -
            (saddleLookbackOrbit p rho z first future N).2) ≤ M) :
    second - first ≤ M / (mu ^ N * J.cJ * p.α) := by
  let x := saddleLookbackOrbit p rho z first future
  let y := saddleLookbackOrbit p rho z second future
  have hxy : x 0 ≤ y 0 :=
    saddleLookbackOrbit_zero_mono model rho z future hcontrols
  have hamp := unstableFunctional_gap_pow_le_of_localExpansion
    model ss hcoop (zero_le_one.trans hmu.le) hlocal x y future
    (fun _ ↦ rfl) (fun _ ↦ rfl) hboxFirst hboxSecond hxy
    hnear hfirstFutureInterior hsecondFutureInterior
  have hinitialPolicy : (y 0).1 - (x 0).1 =
      p.α * (second - first) := by
    exact controlledCivicWeightedStep_policy_sub_eq_alpha_mul
      rho z hfirstInterior hsecondInterior
  have hinitialStock : (y 0).2 - (x 0).2 = 0 := by
    simp only [x, y, saddleLookbackOrbit,
      controlledCivicWeightedOrbitFrom, controlledCivicWeightedStep,
      sub_self]
  have haction :
      mu ^ N * (J.cJ * p.α * (second - first)) ≤ M := by
    calc
      mu ^ N * (J.cJ * p.α * (second - first)) =
          mu ^ N * unstableFunctional J
            ((y 0).1 - (x 0).1) ((y 0).2 - (x 0).2) := by
        rw [hinitialPolicy, hinitialStock]
        simp only [unstableFunctional, mul_zero, add_zero]
        ring
      _ ≤ unstableFunctional J
          ((y N).1 - (x N).1) ((y N).2 - (x N).2) := hamp
      _ ≤ M := hterminal
  have hden : 0 < mu ^ N * J.cJ * p.α := by
    exact mul_pos (mul_pos (pow_pos (zero_lt_one.trans hmu) N) hJc)
      model.α_pos
  apply (le_div_iff₀ hden).2
  nlinarith

/-- Complete deterministic lookback-width theorem for the weighted saddle.
There is a fixed saddle ball and `mu > 1` such that, after conditioning on all
future controls, any ordered pair of first controls whose paths both remain in
the ball for `N` steps differs by at most `C / mu^N`. -/
theorem exists_weightedSaddle_sojourn_control_width
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho) :
    let q := weightedSaddlePoint weighted
    ∃ mu : ℝ, 1 < mu ∧ ∃ radius : ℝ, 0 < radius ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (z : LoopState) (future : ℕ → ℝ) {first second : ℝ} (N : ℕ),
          first ≤ second →
          (∀ n ≤ N,
            dist (saddleLookbackOrbit p rho z first future n) q < radius) →
          (∀ n ≤ N,
            dist (saddleLookbackOrbit p rho z second future n) q < radius) →
          (∀ n, saddleLookbackOrbit p rho z first future n ∈
            absorbingBox p) →
          (∀ n, saddleLookbackOrbit p rho z second future n ∈
            absorbingBox p) →
          second - first ≤ C / mu ^ N := by
  let q := weightedSaddlePoint weighted
  let J := weightedInteriorLoopJacobian p rho weighted.βdagger
    (p.stationaryStock weighted.βdagger)
  obtain ⟨mu, hmu, pairRadius, hpairRadius, hlocal⟩ :=
    exists_weightedSaddle_ball_coneExpansion model ss weighted
  let radius := min (pairRadius / 2)
    (min (weighted.βdagger / 2) ((1 - weighted.βdagger) / 2))
  have hradius : 0 < radius := by
    dsimp only [radius]
    rw [lt_min_iff, lt_min_iff]
    exact ⟨div_pos hpairRadius (by norm_num),
      div_pos weighted.βdagger_mem.1 (by norm_num),
      div_pos (sub_pos.mpr weighted.βdagger_mem.2) (by norm_num)⟩
  have hradiusPair : radius < pairRadius := by
    calc
      radius ≤ pairRadius / 2 := min_le_left _ _
      _ < pairRadius := by linarith
  have hradiusLeft : radius ≤ weighted.βdagger := by
    calc
      radius ≤ weighted.βdagger / 2 :=
        (min_le_right _ _).trans (min_le_left _ _)
      _ ≤ weighted.βdagger := by linarith [weighted.βdagger_mem.1]
  have hradiusRight : radius ≤ 1 - weighted.βdagger := by
    calc
      radius ≤ (1 - weighted.βdagger) / 2 :=
        (min_le_right _ _).trans (min_le_right _ _)
      _ ≤ 1 - weighted.βdagger := by
        linarith [weighted.βdagger_mem.2]
  have hentries := weightedSaddleJacobian_entry_bounds model ss weighted
  have hlarge := weightedSaddle_largerEigenvalue_gt_one model ss weighted
  have hJc : 0 < J.cJ := hentries.2.2.2.1
  have hstockWeight : 0 < J.largerEigenvalue - J.a := by
    linarith [hentries.2.1, hlarge]
  let C :=
    (2 * radius * (J.cJ + (J.largerEigenvalue - J.a))) /
      (J.cJ * p.α)
  have hC : 0 < C := by
    dsimp only [C]
    exact div_pos
      (mul_pos (mul_pos two_pos hradius)
        (add_pos hJc hstockWeight))
      (mul_pos hJc model.α_pos)
  refine ⟨mu, hmu, radius, hradius, C, hC,
    fun z future first second N hcontrols hstayFirst hstaySecond
      hboxFirst hboxSecond ↦ ?_⟩
  have hfirstInterior :
      (controlledCivicWeightedStep p rho first z).1 ∈ Ioo (0 : ℝ) 1 := by
    apply policy_mem_Ioo_of_dist_weightedSaddle_lt weighted
      hradiusLeft hradiusRight
    simpa only [saddleLookbackOrbit, controlledCivicWeightedOrbitFrom] using
      hstayFirst 0 (Nat.zero_le N)
  have hsecondInterior :
      (controlledCivicWeightedStep p rho second z).1 ∈ Ioo (0 : ℝ) 1 := by
    apply policy_mem_Ioo_of_dist_weightedSaddle_lt weighted
      hradiusLeft hradiusRight
    simpa only [saddleLookbackOrbit, controlledCivicWeightedOrbitFrom] using
      hstaySecond 0 (Nat.zero_le N)
  have hnear : ∀ n < N,
      dist
        (saddleLookbackOrbit p rho z first future n,
          saddleLookbackOrbit p rho z second future n)
        (q, q) < pairRadius := by
    intro n hn
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨(hstayFirst n hn.le).trans hradiusPair,
      (hstaySecond n hn.le).trans hradiusPair⟩
  have hfirstFutureInterior : ∀ n < N,
      (saddleLookbackOrbit p rho z first future (n + 1)).1 ∈
        Ioo (0 : ℝ) 1 := by
    intro n hn
    exact policy_mem_Ioo_of_dist_weightedSaddle_lt weighted
      hradiusLeft hradiusRight (hstayFirst (n + 1) (by omega))
  have hsecondFutureInterior : ∀ n < N,
      (saddleLookbackOrbit p rho z second future (n + 1)).1 ∈
        Ioo (0 : ℝ) 1 := by
    intro n hn
    exact policy_mem_Ioo_of_dist_weightedSaddle_lt weighted
      hradiusLeft hradiusRight (hstaySecond (n + 1) (by omega))
  have hterminal :
      unstableFunctional J
          ((saddleLookbackOrbit p rho z second future N).1 -
            (saddleLookbackOrbit p rho z first future N).1)
          ((saddleLookbackOrbit p rho z second future N).2 -
            (saddleLookbackOrbit p rho z first future N).2) ≤
        2 * radius * (J.cJ + (J.largerEigenvalue - J.a)) :=
    unstableFunctional_ordered_gap_le_of_dist_lt J hJc.le
      hstockWeight.le (hstayFirst N le_rfl) (hstaySecond N le_rfl)
  have hwidth := saddleLookback_control_sub_le_of_functional_bound
    model ss hcoop hmu hJc hlocal z future hcontrols
    hfirstInterior hsecondInterior hboxFirst hboxSecond hnear
    hfirstFutureInterior hsecondFutureInterior hterminal
  calc
    second - first ≤
        (2 * radius * (J.cJ + (J.largerEigenvalue - J.a))) /
          (mu ^ N * J.cJ * p.α) := hwidth
    _ = C / mu ^ N := by
      dsimp only [C]
      field_simp [hJc.ne', model.α_pos.ne',
        (pow_pos (zero_lt_one.trans hmu) N).ne']

/-! ## Gaussian anti-concentration -/

/-- The standard real Gaussian density is bounded above by one.  The sharp
constant is unnecessary for the sojourn tail. -/
theorem standardGaussianPDFReal_le_one (x : ℝ) :
    gaussianPDFReal 0 1 x ≤ 1 := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.one_le_sqrt]
    nlinarith [Real.pi_gt_three]
  have hsqrtPos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hinv : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 :=
    (inv_le_one₀ hsqrtPos).2 hsqrt
  have hexponent : -(x ^ 2) / 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) (by norm_num)
  have hexp : Real.exp (-(x ^ 2) / 2) ≤ 1 :=
    (Real.exp_le_one_iff).2 hexponent
  exact (mul_le_mul hinv hexp (Real.exp_pos _).le zero_le_one).trans_eq
    (mul_one 1)

/-- Consequently the standard Gaussian measure is dominated by Lebesgue
volume. -/
theorem standardGaussianReal_le_volume :
    gaussianReal 0 1 ≤ (volume : Measure ℝ) := by
  have hone : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  rw [gaussianReal_of_var_ne_zero 0 hone]
  calc
    volume.withDensity (gaussianPDF 0 1) ≤ volume.withDensity 1 := by
      exact withDensity_mono (ae_of_all _ fun x ↦ by
        change ENNReal.ofReal (gaussianPDFReal 0 1 x) ≤ (1 : ℝ≥0∞)
        rw [ENNReal.ofReal_le_one]
        exact standardGaussianPDFReal_le_one x)
    _ = volume := withDensity_one

/-- Any subset of the line with pairwise diameter at most `D` receives at
most `2D` standard-Gaussian mass. -/
theorem standardGaussianReal_apply_le_two_mul_of_pairwise_dist_le
    {s : Set ℝ} {D : ℝ}
    (hdiameter : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ D) :
    gaussianReal 0 1 s ≤ ENNReal.ofReal (2 * D) := by
  by_cases hs : s.Nonempty
  · obtain ⟨a, ha⟩ := hs
    have hsubset : s ⊆ Icc (a - D) (a + D) := by
      intro x hx
      have hdist := hdiameter x hx a ha
      rw [Real.dist_eq] at hdist
      have habs := abs_le.mp hdist
      constructor <;> linarith
    calc
      gaussianReal 0 1 s ≤ volume s := standardGaussianReal_le_volume s
      _ ≤ volume (Icc (a - D) (a + D)) := measure_mono hsubset
      _ = ENNReal.ofReal (2 * D) := by
        rw [Real.volume_Icc]
        congr 1
        ring
  · rw [Set.not_nonempty_iff_eq_empty.mp hs]
    simp only [measure_empty]
    exact (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * D))

/-- Fiberwise diameter control under a product with one standard Gaussian
coordinate gives the same anti-concentration bound after integrating out all
other coordinates. -/
theorem standardGaussianReal_prod_apply_le_of_fiber_diameter
    {Omega : Type*} [MeasurableSpace Omega] (nu : Measure Omega)
    [IsProbabilityMeasure nu] {s : Set (ℝ × Omega)} (hs : MeasurableSet s)
    {D : ℝ}
    (hdiameter : ∀ omega, ∀ x ∈ (fun y ↦ (y, omega)) ⁻¹' s,
      ∀ y ∈ (fun y ↦ (y, omega)) ⁻¹' s, dist x y ≤ D) :
    (gaussianReal 0 1).prod nu s ≤ ENNReal.ofReal (2 * D) := by
  rw [Measure.prod_apply_symm hs]
  calc
    (∫⁻ omega, gaussianReal 0 1 ((fun x ↦ (x, omega)) ⁻¹' s) ∂nu) ≤
        ∫⁻ _omega, ENNReal.ofReal (2 * D) ∂nu := by
      apply lintegral_mono
      intro omega
      exact standardGaussianReal_apply_le_two_mul_of_pairwise_dist_le
        (hdiameter omega)
    _ = ENNReal.ofReal (2 * D) := by simp

/-! ## Finite-product saddle-sojourn event -/

/-- Split a finite Gaussian history into its scalar first coordinate and the
remaining `N` coordinates. -/
def gaussianHeadTailSplitEquiv (N : ℕ) :
    (Fin (1 + N) → ℝ) ≃ᵐ ℝ × (Fin N → ℝ) :=
  (gaussianVectorSplitEquiv 1 N).trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.funUnique (Fin 1) ℝ)
      (MeasurableEquiv.refl (Fin N → ℝ)))

/-- The scalar head/tail split evaluates an explicitly appended singleton
prefix as expected. -/
@[simp]
theorem gaussianHeadTailSplitEquiv_append
    {N : ℕ} (x : ℝ) (tail : Fin N → ℝ) :
    gaussianHeadTailSplitEquiv N (Fin.append (fun _ : Fin 1 ↦ x) tail) =
      (x, tail) := by
  rw [gaussianHeadTailSplitEquiv, MeasurableEquiv.trans_apply,
    gaussianVectorSplitEquiv_append]
  rfl

/-- Every finite history is reconstructed by appending the scalar head and
tail returned by `gaussianHeadTailSplitEquiv`. -/
theorem gaussianHeadTailSplitEquiv_reconstruct
    {N : ℕ} (xi : Fin (1 + N) → ℝ) :
    xi = Fin.append
      (fun _ : Fin 1 ↦ (gaussianHeadTailSplitEquiv N xi).1)
      (gaussianHeadTailSplitEquiv N xi).2 := by
  apply (gaussianHeadTailSplitEquiv N).injective
  rw [gaussianHeadTailSplitEquiv_append]

/-- The scalar head/tail split sends the finite standard-Gaussian law to one
standard Gaussian coordinate times an independent `N`-vector. -/
theorem measurePreserving_gaussianHeadTailSplitEquiv (N : ℕ) :
    MeasurePreserving (gaussianHeadTailSplitEquiv N)
      (standardGaussianVector (1 + N))
      ((gaussianReal 0 1).prod (standardGaussianVector N)) := by
  letI : IsProbabilityMeasure (standardGaussianVector 1) := by
    unfold standardGaussianVector
    infer_instance
  letI : IsProbabilityMeasure (standardGaussianVector N) := by
    unfold standardGaussianVector
    infer_instance
  have hhead : MeasurePreserving
      (MeasurableEquiv.funUnique (Fin 1) ℝ)
      (standardGaussianVector 1) (gaussianReal 0 1) := by
    unfold standardGaussianVector
    exact measurePreserving_piUnique
      (fun _ : Fin 1 ↦ gaussianReal 0 1)
  have htail : MeasurePreserving
      (MeasurableEquiv.refl (Fin N → ℝ))
      (standardGaussianVector N) (standardGaussianVector N) := by
    exact MeasurePreserving.id _
  have hprod := hhead.prod htail
  have hprod' : MeasurePreserving
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.funUnique (Fin 1) ℝ)
        (MeasurableEquiv.refl (Fin N → ℝ)))
      ((standardGaussianVector 1).prod (standardGaussianVector N))
      ((gaussianReal 0 1).prod (standardGaussianVector N)) := by
    convert hprod using 1
    funext w
    rfl
  exact hprod'.comp (measurePreserving_gaussianVectorSplitEquiv 1 N)

/-- In split coordinates, the first scalar Gaussian draw is the lookback
coordinate and the `N`-vector supplies all subsequent draws.  This event says
that the resulting post-lookback path stays inside the saddle ball through
time `N`. -/
def saddleSojournProductEvent
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (z : LoopState) (sigma radius : ℝ) (N : ℕ) :
    Set (ℝ × (Fin N → ℝ)) :=
  ⋂ n ∈ Finset.range (N + 1),
    {w | dist
      (saddleLookbackOrbit p rho z (sigma * w.1)
        (extendFiniteControl (scaledGaussianControl sigma w.2)) n)
      (weightedSaddlePoint weighted) < radius}

/-- Fixed-time saddle-lookback states depend continuously on the split finite
noise history. -/
theorem continuous_saddleLookbackOrbit_product
    (p : LoopParams) (rho sigma : ℝ) (z : LoopState) (N n : ℕ) :
    Continuous (fun w : ℝ × (Fin N → ℝ) ↦
      saddleLookbackOrbit p rho z (sigma * w.1)
        (extendFiniteControl (scaledGaussianControl sigma w.2)) n) := by
  have hstep : Continuous (fun w : ℝ × LoopState ↦
      controlledCivicWeightedStep p rho w.1 w.2) := by
    unfold controlledCivicWeightedStep civicWeightedGradient
      LoopParams.gradU LoopParams.stockStep LoopParams.s LoopParams.clipUnit
    fun_prop
  induction n with
  | zero =>
      have hfirst : Continuous (fun w : ℝ × (Fin N → ℝ) ↦ sigma * w.1) := by
        fun_prop
      have hpair : Continuous (fun w : ℝ × (Fin N → ℝ) ↦
          (sigma * w.1, z)) := hfirst.prodMk continuous_const
      change Continuous (fun w : ℝ × (Fin N → ℝ) ↦
        controlledCivicWeightedStep p rho (sigma * w.1) z)
      convert hstep.comp hpair using 1
      funext w
      rfl
  | succ n ih =>
      have hcontrol : Continuous (fun w : ℝ × (Fin N → ℝ) ↦
          extendFiniteControl (scaledGaussianControl sigma w.2) n) := by
        unfold extendFiniteControl scaledGaussianControl
        split <;> fun_prop
      have hpair : Continuous (fun w : ℝ × (Fin N → ℝ) ↦
          (extendFiniteControl (scaledGaussianControl sigma w.2) n,
            saddleLookbackOrbit p rho z (sigma * w.1)
              (extendFiniteControl (scaledGaussianControl sigma w.2)) n)) :=
        hcontrol.prodMk ih
      change Continuous (fun w : ℝ × (Fin N → ℝ) ↦
        controlledCivicWeightedStep p rho
          (extendFiniteControl (scaledGaussianControl sigma w.2) n)
          (saddleLookbackOrbit p rho z (sigma * w.1)
            (extendFiniteControl (scaledGaussianControl sigma w.2)) n))
      convert hstep.comp hpair using 1
      funext w
      rfl

/-- The split finite-product saddle-sojourn event is Borel measurable. -/
theorem measurableSet_saddleSojournProductEvent
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (z : LoopState) (sigma radius : ℝ) (N : ℕ) :
    MeasurableSet (saddleSojournProductEvent weighted z sigma radius N) := by
  unfold saddleSojournProductEvent
  refine Finset.measurableSet_biInter (Finset.range (N + 1)) fun n _hn ↦ ?_
  change MeasurableSet
    ((fun w : ℝ × (Fin N → ℝ) ↦
      saddleLookbackOrbit p rho z (sigma * w.1)
        (extendFiniteControl (scaledGaussianControl sigma w.2)) n) ⁻¹'
      Metric.ball (weightedSaddlePoint weighted) radius)
  exact Metric.isOpen_ball.measurableSet.preimage
    (continuous_saddleLookbackOrbit_product p rho sigma z N n).measurable

/-- The same saddle-sojourn event expressed in the ordinary `(N+1)`-vector
coordinates used by finite Gaussian prefixes. -/
def saddleSojournFiniteEvent
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (z : LoopState) (sigma radius : ℝ) (N : ℕ) :
    Set (Fin (1 + N) → ℝ) :=
  gaussianHeadTailSplitEquiv N ⁻¹'
    saddleSojournProductEvent weighted z sigma radius N

/-- The ordinary finite-vector saddle-sojourn event is Borel measurable. -/
theorem measurableSet_saddleSojournFiniteEvent
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (z : LoopState) (sigma radius : ℝ) (N : ℕ) :
    MeasurableSet (saddleSojournFiniteEvent weighted z sigma radius N) := by
  exact (measurableSet_saddleSojournProductEvent
    weighted z sigma radius N).preimage (gaussianHeadTailSplitEquiv N).measurable

/-- Evaluation of a finite saddle-sojourn event agrees exactly with its
scalar-head product representation. -/
theorem standardGaussianVector_saddleSojournFiniteEvent
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (z : LoopState) (sigma radius : ℝ) (N : ℕ) :
    standardGaussianVector (1 + N)
        (saddleSojournFiniteEvent weighted z sigma radius N) =
      (gaussianReal 0 1).prod (standardGaussianVector N)
        (saddleSojournProductEvent weighted z sigma radius N) := by
  unfold saddleSojournFiniteEvent
  rw [← Measure.map_apply (gaussianHeadTailSplitEquiv N).measurable
      (measurableSet_saddleSojournProductEvent weighted z sigma radius N),
    (measurePreserving_gaussianHeadTailSplitEquiv N).map_eq]

/-- Membership in the finite intersection is exactly residence through every
time `n ≤ N`. -/
theorem mem_saddleSojournProductEvent_iff
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (z : LoopState) (sigma radius : ℝ) (N : ℕ)
    (w : ℝ × (Fin N → ℝ)) :
    w ∈ saddleSojournProductEvent weighted z sigma radius N ↔
      ∀ n ≤ N,
        dist
          (saddleLookbackOrbit p rho z (sigma * w.1)
            (extendFiniteControl (scaledGaussianControl sigma w.2)) n)
          (weightedSaddlePoint weighted) < radius := by
  simp only [saddleSojournProductEvent, Set.mem_iInter,
    Set.mem_setOf_eq, Finset.mem_range]
  constructor
  · intro h n hn
    exact h n (by omega)
  · intro h n hn
    exact h n (by omega)

/-- A finite controlled orbit is definitionally the arbitrary-start
controlled recursion driven by the finite control extended by zero. -/
theorem finiteControlledOrbitFrom_eq_controlledCivicWeightedOrbitFrom
    (p : LoopParams) (rho : ℝ) (z : LoopState) {N : ℕ}
    (u : Fin N → ℝ) (n : ℕ) :
    finiteControlledOrbitFrom p rho z u n =
      controlledCivicWeightedOrbitFrom p rho z (extendFiniteControl u) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [finiteControlledOrbitFrom, controlledCivicWeightedOrbitFrom, ih]

/-- Appending a singleton first control and a future vector is exactly the
lookback recursion used in the saddle argument. -/
theorem finiteControlledOrbitFrom_append_singleton
    (p : LoopParams) (rho : ℝ) (z : LoopState) {N : ℕ}
    (first : ℝ) (future : Fin N → ℝ) {n : ℕ} (hn : n ≤ N) :
    finiteControlledOrbitFrom p rho z
        (Fin.append (fun _ : Fin 1 ↦ first) future) (1 + n) =
      saddleLookbackOrbit p rho z first (extendFiniteControl future) n := by
  rw [finiteControlledOrbitFrom_append_right p rho z
    (fun _ : Fin 1 ↦ first) future hn]
  have hfirst : finiteControlledOrbitFrom p rho z
      (fun _ : Fin 1 ↦ first) 1 =
        controlledCivicWeightedStep p rho first z := by
    rw [finiteControlledOrbitFrom]
    simp only [extendFiniteControl, Nat.zero_lt_one, dite_true]
    rfl
  rw [hfirst,
    finiteControlledOrbitFrom_eq_controlledCivicWeightedOrbitFrom]
  rfl

/-- Membership in the finite-vector event is exactly residence of the actual
finite noisy recursion after its first (lookback) step. -/
theorem mem_saddleSojournFiniteEvent_iff
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (z : LoopState) (sigma radius : ℝ) (N : ℕ)
    (xi : Fin (1 + N) → ℝ) :
    xi ∈ saddleSojournFiniteEvent weighted z sigma radius N ↔
      ∀ n ≤ N,
        dist
          (finiteControlledOrbitFrom p rho z
            (scaledGaussianControl sigma xi) (1 + n))
          (weightedSaddlePoint weighted) < radius := by
  rw [gaussianHeadTailSplitEquiv_reconstruct xi]
  simp only [saddleSojournFiniteEvent, Set.mem_preimage,
    gaussianHeadTailSplitEquiv_append]
  rw [mem_saddleSojournProductEvent_iff]
  apply forall_congr'
  intro n
  apply forall_congr'
  intro hn
  rw [scaledGaussianControl_append]
  change
    dist
        (saddleLookbackOrbit p rho z
          (sigma * (gaussianHeadTailSplitEquiv N xi).1)
          (extendFiniteControl
            (scaledGaussianControl sigma (gaussianHeadTailSplitEquiv N xi).2)) n)
        (weightedSaddlePoint weighted) < radius ↔
      dist
        (finiteControlledOrbitFrom p rho z
          (Fin.append
            (fun _ : Fin 1 ↦ sigma * (gaussianHeadTailSplitEquiv N xi).1)
            (scaledGaussianControl sigma (gaussianHeadTailSplitEquiv N xi).2))
          (1 + n))
        (weightedSaddlePoint weighted) < radius
  rw [finiteControlledOrbitFrom_append_singleton p rho z
    (sigma * (gaussianHeadTailSplitEquiv N xi).1)
    (scaledGaussianControl sigma (gaussianHeadTailSplitEquiv N xi).2) hn]

/-- The Gaussian noisy recursion from an arbitrary deterministic state. -/
def gaussianNoisyOrbitFrom (p : LoopParams) (rho : ℝ) (z : LoopState)
    (sigma : ℝ) (xi : GaussianNoisePath) : ℕ → LoopState :=
  controlledCivicWeightedOrbitFrom p rho z (fun n ↦ sigma * xi n)

/-- A finite Gaussian prefix reproduces the arbitrary-start noisy recursion
through every time within the prefix. -/
theorem finiteControlledOrbitFrom_gaussianPrefix_eq_gaussianNoisyOrbitFrom
    (p : LoopParams) (rho : ℝ) (z : LoopState) (sigma : ℝ)
    (xi : GaussianNoisePath) {T n : ℕ} (hn : n ≤ T) :
    finiteControlledOrbitFrom p rho z
        (scaledGaussianControl sigma (gaussianPrefix T xi)) n =
      gaussianNoisyOrbitFrom p rho z sigma xi n := by
  have hpath := controlledCivicWeightedOrbitFrom_isControlled p rho z
    (fun k ↦ sigma * xi k)
  change finiteControlledOrbitFrom p rho z
      (fun i : Fin T ↦ sigma * xi i) n =
    controlledCivicWeightedOrbitFrom p rho z (fun k ↦ sigma * xi k) n
  exact finiteControlledOrbitFrom_restrict_eq hpath hn

/-- Infinite histories whose arbitrary-start noisy orbit remains inside the
weighted saddle ball after the lookback step through time `N`. -/
def saddleSojournPathEvent
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (z : LoopState) (sigma radius : ℝ) (N : ℕ) : Set GaussianNoisePath :=
  gaussianPrefix (1 + N) ⁻¹'
    saddleSojournFiniteEvent weighted z sigma radius N

/-- The path-space event has the literal residence interpretation. -/
theorem mem_saddleSojournPathEvent_iff
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (z : LoopState) (sigma radius : ℝ) (N : ℕ)
    (xi : GaussianNoisePath) :
    xi ∈ saddleSojournPathEvent weighted z sigma radius N ↔
      ∀ n ≤ N,
        dist (gaussianNoisyOrbitFrom p rho z sigma xi (1 + n))
          (weightedSaddlePoint weighted) < radius := by
  simp only [saddleSojournPathEvent, Set.mem_preimage]
  rw [mem_saddleSojournFiniteEvent_iff]
  apply forall_congr'
  intro n
  apply forall_congr'
  intro hn
  rw [finiteControlledOrbitFrom_gaussianPrefix_eq_gaussianNoisyOrbitFrom
    p rho z sigma xi (by omega : 1 + n ≤ 1 + N)]

/-- The infinite-history saddle-sojourn event is measurable. -/
theorem measurableSet_saddleSojournPathEvent
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (z : LoopState) (sigma radius : ℝ) (N : ℕ) :
    MeasurableSet (saddleSojournPathEvent weighted z sigma radius N) := by
  exact (measurableSet_saddleSojournFiniteEvent
    weighted z sigma radius N).preimage (measurable_gaussianPrefix (1 + N))

/-- The infinite product evaluates a saddle-sojourn event by the corresponding
finite Gaussian prefix. -/
theorem standardGaussianSequence_saddleSojournPathEvent
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (z : LoopState) (sigma radius : ℝ) (N : ℕ) :
    standardGaussianSequence
        (saddleSojournPathEvent weighted z sigma radius N) =
      standardGaussianVector (1 + N)
        (saddleSojournFiniteEvent weighted z sigma radius N) := by
  unfold saddleSojournPathEvent
  rw [← Measure.map_apply (measurable_gaussianPrefix (1 + N))
      (measurableSet_saddleSojournFiniteEvent weighted z sigma radius N),
    standardGaussianSequence_map_prefix]

/-- A lookback orbit stays in the absorbing box for every control history when
the pre-lookback state starts there. -/
theorem saddleLookbackOrbit_mem_absorbingBox
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    {z : LoopState} (hz : z ∈ absorbingBox p) (first : ℝ)
    (future : ℕ → ℝ) (n : ℕ) :
    saddleLookbackOrbit p rho z first future n ∈ absorbingBox p := by
  let zfirst := controlledCivicWeightedStep p rho first z
  have hzfirst : zfirst ∈ absorbingBox p := by
    have hstock := (civicWeightedInvariantBox model rho hz).2
    exact ⟨LoopParams.clipUnit_mem _, by
      simpa only [zfirst, controlledCivicWeightedStep,
        civicWeightedLoopMap] using hstock⟩
  exact (controlledCivicWeightedOrbitFrom_isControlled
    p rho zfirst future).mem_absorbingBox model hzfirst n

/-- Under the split finite-product Gaussian law, residence in the weighted
saddle ball through time `N` has probability at most `2 C / (sigma mu^N)`.
The estimate conditions on every future Gaussian coordinate and uses only the
one-dimensional density bound for the lookback coordinate. -/
theorem exists_weightedSaddle_sojourn_product_probability_bound
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho) :
    ∃ mu : ℝ, 1 < mu ∧ ∃ radius : ℝ, 0 < radius ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (z : LoopState), z ∈ absorbingBox p →
          ∀ sigma : ℝ, 0 < sigma → ∀ N : ℕ,
            (gaussianReal 0 1).prod (standardGaussianVector N)
                (saddleSojournProductEvent weighted z sigma radius N) ≤
              ENNReal.ofReal (2 * (C / (sigma * mu ^ N))) := by
  obtain ⟨mu, hmu, radius, hradius, C, hC, hwidth⟩ :=
    exists_weightedSaddle_sojourn_control_width model ss hcoop weighted
  refine ⟨mu, hmu, radius, hradius, C, hC, ?_⟩
  intro z hz sigma hsigma N
  letI : IsProbabilityMeasure (standardGaussianVector N) := by
    unfold standardGaussianVector
    infer_instance
  apply standardGaussianReal_prod_apply_le_of_fiber_diameter
    (nu := standardGaussianVector N)
    (measurableSet_saddleSojournProductEvent weighted z sigma radius N)
  intro futureGaussian x hx y hy
  have hxstay : ∀ n ≤ N,
      dist
        (saddleLookbackOrbit p rho z (sigma * x)
          (extendFiniteControl
            (scaledGaussianControl sigma futureGaussian)) n)
        (weightedSaddlePoint weighted) < radius :=
    (mem_saddleSojournProductEvent_iff weighted z sigma radius N
      (x, futureGaussian)).1 hx
  have hystay : ∀ n ≤ N,
      dist
        (saddleLookbackOrbit p rho z (sigma * y)
          (extendFiniteControl
            (scaledGaussianControl sigma futureGaussian)) n)
        (weightedSaddlePoint weighted) < radius :=
    (mem_saddleSojournProductEvent_iff weighted z sigma radius N
      (y, futureGaussian)).1 hy
  let future := extendFiniteControl
    (scaledGaussianControl sigma futureGaussian)
  have hboxX : ∀ n,
      saddleLookbackOrbit p rho z (sigma * x) future n ∈
        absorbingBox p := by
    intro n
    exact saddleLookbackOrbit_mem_absorbingBox model rho hz
      (sigma * x) future n
  have hboxY : ∀ n,
      saddleLookbackOrbit p rho z (sigma * y) future n ∈
        absorbingBox p := by
    intro n
    exact saddleLookbackOrbit_mem_absorbingBox model rho hz
      (sigma * y) future n
  have hpow : 0 < mu ^ N := pow_pos (zero_lt_one.trans hmu) N
  rcases le_total x y with hxy | hyx
  · have hcontrol : sigma * x ≤ sigma * y :=
      mul_le_mul_of_nonneg_left hxy hsigma.le
    have hraw := hwidth z future N hcontrol
      (by simpa only [future] using hxstay)
      (by simpa only [future] using hystay) hboxX hboxY
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)]
    apply (le_div_iff₀ (mul_pos hsigma hpow)).2
    have hraw' : (sigma * y - sigma * x) * mu ^ N ≤ C :=
      (le_div_iff₀ hpow).1 hraw
    calc
      (-(x - y)) * (sigma * mu ^ N) =
          (sigma * y - sigma * x) * mu ^ N := by ring
      _ ≤ C := hraw'
  · have hcontrol : sigma * y ≤ sigma * x :=
      mul_le_mul_of_nonneg_left hyx hsigma.le
    have hraw := hwidth z future N hcontrol
      (by simpa only [future] using hystay)
      (by simpa only [future] using hxstay) hboxY hboxX
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx)]
    apply (le_div_iff₀ (mul_pos hsigma hpow)).2
    have hraw' : (sigma * x - sigma * y) * mu ^ N ≤ C :=
      (le_div_iff₀ hpow).1 hraw
    calc
      (x - y) * (sigma * mu ^ N) =
          (sigma * x - sigma * y) * mu ^ N := by ring
      _ ≤ C := hraw'

/-- The product-coordinate estimate transferred to the ordinary finite
Gaussian prefix law. -/
theorem exists_weightedSaddle_sojourn_finite_probability_bound
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho) :
    ∃ mu : ℝ, 1 < mu ∧ ∃ radius : ℝ, 0 < radius ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (z : LoopState), z ∈ absorbingBox p →
          ∀ sigma : ℝ, 0 < sigma → ∀ N : ℕ,
            standardGaussianVector (1 + N)
                (saddleSojournFiniteEvent weighted z sigma radius N) ≤
              ENNReal.ofReal (2 * (C / (sigma * mu ^ N))) := by
  obtain ⟨mu, hmu, radius, hradius, C, hC, hprob⟩ :=
    exists_weightedSaddle_sojourn_product_probability_bound
      model ss hcoop weighted
  refine ⟨mu, hmu, radius, hradius, C, hC, ?_⟩
  intro z hz sigma hsigma N
  rw [standardGaussianVector_saddleSojournFiniteEvent]
  exact hprob z hz sigma hsigma N

/-- The saddle-sojourn probability bound on the canonical infinite Gaussian
history space. -/
theorem exists_weightedSaddle_sojourn_path_probability_bound
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho) :
    ∃ mu : ℝ, 1 < mu ∧ ∃ radius : ℝ, 0 < radius ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (z : LoopState), z ∈ absorbingBox p →
          ∀ sigma : ℝ, 0 < sigma → ∀ N : ℕ,
            standardGaussianSequence
                (saddleSojournPathEvent weighted z sigma radius N) ≤
              ENNReal.ofReal (2 * (C / (sigma * mu ^ N))) := by
  obtain ⟨mu, hmu, radius, hradius, C, hC, hprob⟩ :=
    exists_weightedSaddle_sojourn_finite_probability_bound
      model ss hcoop weighted
  refine ⟨mu, hmu, radius, hradius, C, hC, ?_⟩
  intro z hz sigma hsigma N
  rw [standardGaussianSequence_saddleSojournPathEvent]
  exact hprob z hz sigma hsigma N

/-- The logarithmic number of saddle steps needed for noise scale `sigma` to
be amplified to unit order by a multiplier `mu > 1`. -/
def saddleSojournBurnIn (mu sigma : ℝ) : ℕ :=
  ⌈Real.log (1 / sigma) / Real.log mu⌉₊

/-- The ceiling defining `saddleSojournBurnIn` really reaches unit amplified
scale for every positive `sigma`. -/
theorem one_le_sigma_mul_pow_saddleSojournBurnIn
    {mu sigma : ℝ} (hmu : 1 < mu) (hsigma : 0 < sigma) :
    1 ≤ sigma * mu ^ saddleSojournBurnIn mu sigma := by
  have hlogMu : 0 < Real.log mu := Real.log_pos hmu
  have hceil : Real.log (1 / sigma) / Real.log mu ≤
      (saddleSojournBurnIn mu sigma : ℝ) := by
    exact Nat.le_ceil _
  have hlog : Real.log (1 / sigma) ≤
      (saddleSojournBurnIn mu sigma : ℝ) * Real.log mu :=
    (div_le_iff₀ hlogMu).1 hceil
  have hinvLe : 1 / sigma ≤ mu ^ saddleSojournBurnIn mu sigma := by
    apply (Real.log_le_log_iff (by positivity)
      (pow_pos (zero_lt_one.trans hmu) _)).1
    rw [Real.log_pow]
    exact hlog
  have hscale : 1 ≤ mu ^ saddleSojournBurnIn mu sigma * sigma :=
    (div_le_iff₀ hsigma).1 hinvLe
  simpa only [mul_comm] using hscale

/-- On the small-noise range, the burn-in is strictly below the real
logarithmic threshold plus one. -/
theorem saddleSojournBurnIn_cast_lt
    {mu sigma : ℝ} (hmu : 1 < mu) (hsigma : 0 < sigma)
    (hsigmaOne : sigma ≤ 1) :
    (saddleSojournBurnIn mu sigma : ℝ) <
      Real.log (1 / sigma) / Real.log mu + 1 := by
  exact Nat.ceil_lt_add_one
    (div_nonneg
      (Real.log_nonneg (one_le_one_div hsigma hsigmaOne))
      (Real.log_pos hmu).le)

/-- The logarithmic saddle burn-in is negligible on the Arrhenius
`sigma^2` scale. -/
theorem tendsto_sigma_sq_mul_saddleSojournBurnIn
    {mu : ℝ} (hmu : 1 < mu) :
    Tendsto (fun sigma : ℝ ↦
        sigma ^ 2 * (saddleSojournBurnIn mu sigma : ℝ))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
  have hlogSquare : Tendsto
      (fun sigma : ℝ ↦ Real.log sigma * sigma ^ 2)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
    simpa only [Real.rpow_two] using
      (tendsto_log_mul_rpow_nhdsGT_zero
        (r := (2 : ℝ)) (by norm_num))
  have hsquare : Tendsto (fun sigma : ℝ ↦ sigma ^ 2)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
    have hcont : ContinuousAt (fun sigma : ℝ ↦ sigma ^ 2) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hupperLimit : Tendsto (fun sigma : ℝ ↦
      sigma ^ 2 *
        (Real.log (1 / sigma) / Real.log mu + 1))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
    have hcombined :=
      (hlogSquare.const_mul (-(Real.log mu)⁻¹)).add hsquare
    convert hcombined using 1
    · funext sigma
      rw [one_div, Real.log_inv]
      ring
    · ring
  have hleOne : ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)), sigma ≤ 1 :=
    Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_le_nhds (by norm_num))
  have hupper : ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      sigma ^ 2 * (saddleSojournBurnIn mu sigma : ℝ) ≤
        sigma ^ 2 *
          (Real.log (1 / sigma) / Real.log mu + 1) := by
    filter_upwards [self_mem_nhdsWithin, hleOne] with sigma hsigma hsigmaOne
    exact mul_le_mul_of_nonneg_left
      (saddleSojournBurnIn_cast_lt hmu hsigma hsigmaOne |>.le)
      (sq_nonneg sigma)
  exact squeeze_zero'
    (Eventually.of_forall fun sigma ↦
      mul_nonneg (sq_nonneg sigma) (Nat.cast_nonneg _))
    hupper hupperLimit

/-- Once the expanding scale has reached unit size, every additional saddle
step costs a geometric factor `mu⁻¹`, uniformly in the noise scale.  This is
the shifted form consumed by the long-excursion accounting. -/
theorem exists_weightedSaddle_sojourn_geometric_tail
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho) :
    ∃ mu : ℝ, 1 < mu ∧ ∃ radius : ℝ, 0 < radius ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (z : LoopState), z ∈ absorbingBox p →
          ∀ sigma : ℝ, 0 < sigma → ∀ t : ℕ,
            1 ≤ sigma * mu ^ t → ∀ s : ℕ,
              (gaussianReal 0 1).prod (standardGaussianVector (t + s))
                  (saddleSojournProductEvent weighted z sigma radius (t + s)) ≤
                ENNReal.ofReal (2 * (C / mu ^ s)) := by
  obtain ⟨mu, hmu, radius, hradius, C, hC, hprob⟩ :=
    exists_weightedSaddle_sojourn_product_probability_bound
      model ss hcoop weighted
  refine ⟨mu, hmu, radius, hradius, C, hC, ?_⟩
  intro z hz sigma hsigma t hscale s
  calc
    (gaussianReal 0 1).prod (standardGaussianVector (t + s))
          (saddleSojournProductEvent weighted z sigma radius (t + s)) ≤
        ENNReal.ofReal (2 * (C / (sigma * mu ^ (t + s)))) :=
      hprob z hz sigma hsigma (t + s)
    _ ≤ ENNReal.ofReal (2 * (C / mu ^ s)) := by
      apply ENNReal.ofReal_le_ofReal
      have hpowS : 0 < mu ^ s := pow_pos (zero_lt_one.trans hmu) s
      have hden : mu ^ s ≤ sigma * mu ^ (t + s) := by
        rw [pow_add]
        calc
          mu ^ s = 1 * mu ^ s := by ring
          _ ≤ (sigma * mu ^ t) * mu ^ s :=
            mul_le_mul_of_nonneg_right hscale hpowS.le
          _ = sigma * (mu ^ t * mu ^ s) := by ring
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hC.le hpowS hden) (by norm_num)

/-- The weighted-saddle residence tail with its canonical logarithmic burn-in
inserted. -/
theorem exists_weightedSaddle_sojourn_logarithmic_tail
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho) :
    ∃ mu : ℝ, 1 < mu ∧ ∃ radius : ℝ, 0 < radius ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (z : LoopState), z ∈ absorbingBox p →
          ∀ sigma : ℝ, 0 < sigma → ∀ s : ℕ,
            (gaussianReal 0 1).prod
                (standardGaussianVector (saddleSojournBurnIn mu sigma + s))
                (saddleSojournProductEvent weighted z sigma radius
                  (saddleSojournBurnIn mu sigma + s)) ≤
              ENNReal.ofReal (2 * (C / mu ^ s)) := by
  obtain ⟨mu, hmu, radius, hradius, C, hC, htail⟩ :=
    exists_weightedSaddle_sojourn_geometric_tail model ss hcoop weighted
  refine ⟨mu, hmu, radius, hradius, C, hC, ?_⟩
  intro z hz sigma hsigma s
  exact htail z hz sigma hsigma (saddleSojournBurnIn mu sigma)
    (one_le_sigma_mul_pow_saddleSojournBurnIn hmu hsigma) s

/-- Canonical-path form of the weighted-saddle residence estimate: after the
logarithmic burn-in, every additional `s` steps cost `mu⁻ˢ`. -/
theorem exists_weightedSaddle_sojourn_path_logarithmic_tail
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho) :
    ∃ mu : ℝ, 1 < mu ∧ ∃ radius : ℝ, 0 < radius ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (z : LoopState), z ∈ absorbingBox p →
          ∀ sigma : ℝ, 0 < sigma → ∀ s : ℕ,
            standardGaussianSequence
                (saddleSojournPathEvent weighted z sigma radius
                  (saddleSojournBurnIn mu sigma + s)) ≤
              ENNReal.ofReal (2 * (C / mu ^ s)) := by
  obtain ⟨mu, hmu, radius, hradius, C, hC, hprob⟩ :=
    exists_weightedSaddle_sojourn_path_probability_bound
      model ss hcoop weighted
  refine ⟨mu, hmu, radius, hradius, C, hC, ?_⟩
  intro z hz sigma hsigma s
  let t := saddleSojournBurnIn mu sigma
  have hscale : 1 ≤ sigma * mu ^ t :=
    one_le_sigma_mul_pow_saddleSojournBurnIn hmu hsigma
  calc
    standardGaussianSequence
          (saddleSojournPathEvent weighted z sigma radius (t + s)) ≤
        ENNReal.ofReal (2 * (C / (sigma * mu ^ (t + s)))) :=
      hprob z hz sigma hsigma (t + s)
    _ ≤ ENNReal.ofReal (2 * (C / mu ^ s)) := by
      apply ENNReal.ofReal_le_ofReal
      have hpowS : 0 < mu ^ s := pow_pos (zero_lt_one.trans hmu) s
      have hden : mu ^ s ≤ sigma * mu ^ (t + s) := by
        rw [pow_add]
        calc
          mu ^ s = 1 * mu ^ s := by ring
          _ ≤ (sigma * mu ^ t) * mu ^ s :=
            mul_le_mul_of_nonneg_right hscale hpowS.le
          _ = sigma * (mu ^ t * mu ^ s) := by ring
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hC.le hpowS hden) (by norm_num)

#print axioms weightedSaddleJacobian_entry_bounds
#print axioms WeightedThresholdAssumption.weightedCureThreshold_eq
#print axioms weightedSaddleJacobian_charPoly_one_eq
#print axioms weightedSaddle_largerEigenvalue_gt_one
#print axioms weightedOrderedDifferenceCoefficients_self
#print axioms continuous_weightedOrderedDifferenceCoefficients_a
#print axioms continuous_weightedOrderedDifferenceCoefficients_b
#print axioms continuous_weightedOrderedDifferenceCoefficients_cJ
#print axioms continuous_weightedOrderedDifferenceCoefficients_d
#print axioms controlledCivicWeightedStep_orderedDifference_eq
#print axioms unstablePolicyGain_self
#print axioms unstableStockGain_self
#print axioms exists_weightedSaddle_eventually_coneExpansion
#print axioms exists_weightedSaddle_ball_coneExpansion
#print axioms controlledCivicWeightedStep_monotoneOn_box
#print axioms unstableFunctional_gap_pow_le_of_localExpansion
#print axioms controlledCivicWeightedStep_policy_sub_eq_alpha_mul
#print axioms saddleLookbackOrbit_zero_mono
#print axioms saddleLookback_control_sub_le_of_functional_bound
#print axioms policy_mem_Ioo_of_dist_weightedSaddle_lt
#print axioms exists_weightedSaddle_sojournChart
#print axioms unstableFunctional_ordered_gap_le_of_dist_lt
#print axioms exists_weightedSaddle_sojourn_control_width
#print axioms standardGaussianPDFReal_le_one
#print axioms standardGaussianReal_le_volume
#print axioms standardGaussianReal_apply_le_two_mul_of_pairwise_dist_le
#print axioms standardGaussianReal_prod_apply_le_of_fiber_diameter
#print axioms continuous_saddleLookbackOrbit_product
#print axioms measurableSet_saddleSojournProductEvent
#print axioms measurePreserving_gaussianHeadTailSplitEquiv
#print axioms measurableSet_saddleSojournFiniteEvent
#print axioms standardGaussianVector_saddleSojournFiniteEvent
#print axioms mem_saddleSojournProductEvent_iff
#print axioms finiteControlledOrbitFrom_eq_controlledCivicWeightedOrbitFrom
#print axioms finiteControlledOrbitFrom_append_singleton
#print axioms mem_saddleSojournFiniteEvent_iff
#print axioms finiteControlledOrbitFrom_gaussianPrefix_eq_gaussianNoisyOrbitFrom
#print axioms mem_saddleSojournPathEvent_iff
#print axioms measurableSet_saddleSojournPathEvent
#print axioms standardGaussianSequence_saddleSojournPathEvent
#print axioms saddleLookbackOrbit_mem_absorbingBox
#print axioms exists_weightedSaddle_sojourn_product_probability_bound
#print axioms exists_weightedSaddle_sojourn_finite_probability_bound
#print axioms exists_weightedSaddle_sojourn_path_probability_bound
#print axioms one_le_sigma_mul_pow_saddleSojournBurnIn
#print axioms saddleSojournBurnIn_cast_lt
#print axioms tendsto_sigma_sq_mul_saddleSojournBurnIn
#print axioms exists_weightedSaddle_sojourn_geometric_tail
#print axioms exists_weightedSaddle_sojourn_logarithmic_tail
#print axioms exists_weightedSaddle_sojourn_path_logarithmic_tail

end

end CivicAlignment.PaperII
