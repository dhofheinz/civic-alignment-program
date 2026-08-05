/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.ArrheniusUpper
import Mathlib.Analysis.Real.Sqrt

/-!
# Paper II: policy matching near the calibrated state

The lower half of the sharp Arrhenius rate compares a crossing path started
near the calibrated corner with one started exactly at that corner.  Direct
trajectory transport is unstable near the saddle.  Instead, this file changes
the controls so that the two policy coordinates agree after one step.  The
remaining stock discrepancy then contracts at the retirement rate.
-/

namespace CivicAlignment.PaperII

open Filter Function Set Topology
open scoped BigOperators Interval

noncomputable section

/-! ## The matched path and its controls -/

/-- The comparison path starts at the calibrated corner, copies the original
path's next policy coordinate, and evolves its own stock without forcing. -/
def policyMatchedOrbit (p : LoopParams) (rho : ℝ) (z : LoopState)
    (u : ℕ → ℝ) : ℕ → LoopState
  | 0 => calibratedPoint p
  | n + 1 =>
      let x := controlledCivicWeightedOrbitFrom p rho z u (n + 1)
      let y := policyMatchedOrbit p rho z u n
      (x.1, p.stockStep y.1 y.2)

/-- The control correction which realizes `policyMatchedOrbit`.  At time zero
the policy displacement is paid once; after that displacement vanishes and
only the gradient difference remains. -/
def policyMatchedControlSequence (p : LoopParams) (rho : ℝ)
    (z : LoopState) (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  let x := controlledCivicWeightedOrbitFrom p rho z u n
  let y := policyMatchedOrbit p rho z u n
  u n + (x.1 - y.1) / p.α +
    civicWeightedGradient p rho x.1 x.2 -
      civicWeightedGradient p rho y.1 y.2

/-- The matched recursion is exactly a controlled path from the calibrated
corner. -/
theorem policyMatchedOrbit_isControlled
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    (z : LoopState) (u : ℕ → ℝ) :
    IsControlledCivicWeightedPathFrom p rho (calibratedPoint p)
      (policyMatchedControlSequence p rho z u)
      (policyMatchedOrbit p rho z u) := by
  constructor
  · rfl
  · intro n
    apply Prod.ext
    · simp only [policyMatchedOrbit, controlledCivicWeightedOrbitFrom,
        controlledCivicWeightedStep, policyMatchedControlSequence]
      congr 1
      field_simp [model.α_pos.ne']
      ring
    · simp only [policyMatchedOrbit, controlledCivicWeightedStep]

/-- Policies agree exactly from time one onward, irrespective of projection. -/
@[simp]
theorem policyMatchedOrbit_policy_succ
    (p : LoopParams) (rho : ℝ) (z : LoopState) (u : ℕ → ℝ) (n : ℕ) :
    (policyMatchedOrbit p rho z u (n + 1)).1 =
      (controlledCivicWeightedOrbitFrom p rho z u (n + 1)).1 := by
  rfl

/-- The initial correction is the one-shot policy displacement plus the
initial gradient displacement. -/
theorem policyMatchedControlSequence_zero
    (p : LoopParams) (rho : ℝ) (z : LoopState) (u : ℕ → ℝ) :
    policyMatchedControlSequence p rho z u 0 =
      u 0 + z.1 / p.α + civicWeightedGradient p rho z.1 z.2 -
        civicWeightedGradient p rho 0 (p.stationaryStock 0) := by
  simp only [policyMatchedControlSequence, controlledCivicWeightedOrbitFrom,
    policyMatchedOrbit, calibratedPoint, sub_zero]

/-- After time zero, matching only pays the difference between the two
gradients at their common policy. -/
theorem policyMatchedControlSequence_succ
    (p : LoopParams) (rho : ℝ) (z : LoopState) (u : ℕ → ℝ) (n : ℕ) :
    policyMatchedControlSequence p rho z u (n + 1) =
      u (n + 1) +
        civicWeightedGradient p rho
          (controlledCivicWeightedOrbitFrom p rho z u (n + 1)).1
          (controlledCivicWeightedOrbitFrom p rho z u (n + 1)).2 -
        civicWeightedGradient p rho
          (policyMatchedOrbit p rho z u (n + 1)).1
          (policyMatchedOrbit p rho z u (n + 1)).2 := by
  simp only [policyMatchedControlSequence, policyMatchedOrbit_policy_succ,
    sub_self, zero_div, add_zero]

/-- At a common policy, the gradient correction is exactly linear in the
stock discrepancy. -/
theorem civicWeightedGradient_sub_at_common_policy
    (p : LoopParams) (rho beta Dx Dy : ℝ) :
    civicWeightedGradient p rho beta Dx -
        civicWeightedGradient p rho beta Dy =
      (2 * p.c * (1 - p.c * beta) - rho) * (Dx - Dy) := by
  simp only [civicWeightedGradient, LoopParams.gradU]
  ring

/-- Thus every maintaining correction has the coefficient printed in the
policy-matching argument. -/
theorem policyMatchedControlSequence_succ_eq
    (p : LoopParams) (rho : ℝ) (z : LoopState) (u : ℕ → ℝ) (n : ℕ) :
    policyMatchedControlSequence p rho z u (n + 1) =
      u (n + 1) +
        (2 * p.c *
            (1 - p.c *
              (controlledCivicWeightedOrbitFrom p rho z u (n + 1)).1) - rho) *
          ((controlledCivicWeightedOrbitFrom p rho z u (n + 1)).2 -
            (policyMatchedOrbit p rho z u (n + 1)).2) := by
  rw [policyMatchedControlSequence_succ]
  rw [policyMatchedOrbit_policy_succ]
  rw [add_sub_assoc]
  rw [civicWeightedGradient_sub_at_common_policy]

/-! ## Exact stock contraction -/

/-- Once policies have matched, the stock discrepancy follows the exact
scalar retirement recursion. -/
theorem policyMatchedOrbit_stock_sub_succ_succ
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    (z : LoopState) (u : ℕ → ℝ) (n : ℕ) :
    (controlledCivicWeightedOrbitFrom p rho z u (n + 2)).2 -
        (policyMatchedOrbit p rho z u (n + 2)).2 =
      p.s (controlledCivicWeightedOrbitFrom p rho z u (n + 1)).1 *
        ((controlledCivicWeightedOrbitFrom p rho z u (n + 1)).2 -
          (policyMatchedOrbit p rho z u (n + 1)).2) := by
  change
    p.stockStep
          (controlledCivicWeightedOrbitFrom p rho z u (n + 1)).1
          (controlledCivicWeightedOrbitFrom p rho z u (n + 1)).2 -
        p.stockStep
          (policyMatchedOrbit p rho z u (n + 1)).1
          (policyMatchedOrbit p rho z u (n + 1)).2 = _
  rw [policyMatchedOrbit_policy_succ]
  simp only [LoopParams.stockStep, model.no_content_gain, add_zero]
  ring

/-- On the unit interval, displacement of the stock multiplier from its
calibrated value is at most twice the policy displacement. -/
theorem abs_stockMultiplier_sub_zero_le
    {p : LoopParams} (model : DriftModelAssumptions p)
    {beta : ℝ} (hbeta : beta ∈ Icc (0 : ℝ) 1) :
    |p.s beta - p.s 0| ≤ 2 * beta := by
  have hzero : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hsub := stockMultiplier_sub_le model hzero hbeta hbeta.1
  have hr0 : 0 ≤ 1 - p.η := sub_nonneg.mpr model.η_le_one
  have hrbeta : 0 ≤ 1 - p.η * (1 - beta) := by
    have hresidual : 1 - beta ≤ 1 := by linarith [hbeta.1]
    have hproduct := mul_le_mul_of_nonneg_left hresidual model.η_pos.le
    linarith [model.η_le_one]
  have hrorder : 1 - p.η ≤ 1 - p.η * (1 - beta) := by
    have hmul : p.η * (1 - beta) ≤ p.η := by
      nlinarith [model.η_pos.le, hbeta.1]
    linarith
  have hsmono : p.s 0 ≤ p.s beta := by
    have hsquare : (1 - p.η) ^ 2 ≤
        (1 - p.η * (1 - beta)) ^ 2 :=
      (sq_le_sq₀ hr0 hrbeta).2 hrorder
    simpa only [LoopParams.s, sub_zero, mul_one] using
      mul_le_mul_of_nonneg_left hsquare
        (sub_nonneg.mpr model.lambda₀_lt_one.le)
  have hcoef : 2 * p.η * (1 - p.lambda₀) ≤ 2 := by
    have hground : 1 - p.lambda₀ ≤ 1 := by linarith [model.lambda₀_pos]
    have hproduct : p.η * (1 - p.lambda₀) ≤ 1 := calc
      p.η * (1 - p.lambda₀) ≤ p.η * 1 :=
        mul_le_mul_of_nonneg_left hground model.η_pos.le
      _ = p.η := mul_one _
      _ ≤ 1 := model.η_le_one
    nlinarith
  rw [abs_of_nonneg (sub_nonneg.mpr hsmono)]
  exact hsub.trans (by
    have := mul_le_mul_of_nonneg_right hcoef hbeta.1
    nlinarith)

/-- A convenient explicit Lipschitz constant for the first unmatched stock
update. -/
def policyMatchingInitialStockConstant (p : LoopParams) : ℝ :=
  1 + 2 * (p.I / p.lambda₀)

/-- The only unmatched stock update is Lipschitz in the full initial state. -/
theorem policyMatchedOrbit_initial_stock_bound
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    {z : LoopState} (hz : z ∈ absorbingBox p) (u : ℕ → ℝ) :
    |(controlledCivicWeightedOrbitFrom p rho z u 1).2 -
        (policyMatchedOrbit p rho z u 1).2| ≤
      policyMatchingInitialStockConstant p * dist z (calibratedPoint p) := by
  have hzero : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hD0mem := stationaryStock_mem_stockInterval model hzero
  have hD0pos : 0 < p.stationaryStock 0 := model.I_pos.trans_le hD0mem.1
  have hdistBeta : |z.1| ≤ dist z (calibratedPoint p) := by
    rw [Prod.dist_eq]
    have h := le_max_left (dist z.1 (calibratedPoint p).1)
      (dist z.2 (calibratedPoint p).2)
    simpa only [calibratedPoint, Real.dist_eq, sub_zero] using h
  have hdistStock : |z.2 - p.stationaryStock 0| ≤
      dist z (calibratedPoint p) := by
    rw [Prod.dist_eq]
    have h := le_max_right (dist z.1 (calibratedPoint p).1)
      (dist z.2 (calibratedPoint p).2)
    simpa only [calibratedPoint, Real.dist_eq] using h
  have hs := driftStockMultiplier_nonneg_le model hz.1
  have hsabs : |p.s z.1| ≤ 1 := by
    rw [abs_of_nonneg hs.1]
    linarith [hs.2, model.lambda₀_pos]
  have hsdiff : |p.s z.1 - p.s 0| ≤
      2 * dist z (calibratedPoint p) := by
    have hzbetaDist : z.1 ≤ dist z (calibratedPoint p) :=
      (le_abs_self z.1).trans hdistBeta
    exact (abs_stockMultiplier_sub_zero_le model hz.1).trans
      (mul_le_mul_of_nonneg_left hzbetaDist (by norm_num))
  have hfirst : |p.s z.1| * |z.2 - p.stationaryStock 0| ≤
      dist z (calibratedPoint p) := by
    calc
      |p.s z.1| * |z.2 - p.stationaryStock 0| ≤
          1 * dist z (calibratedPoint p) :=
        mul_le_mul hsabs hdistStock (abs_nonneg _)
          (by positivity)
      _ = dist z (calibratedPoint p) := one_mul _
  have hsecond : |p.s z.1 - p.s 0| * |p.stationaryStock 0| ≤
      2 * dist z (calibratedPoint p) * (p.I / p.lambda₀) := by
    rw [abs_of_pos hD0pos]
    exact mul_le_mul hsdiff hD0mem.2 hD0pos.le (by positivity)
  have hidentity :
      (controlledCivicWeightedOrbitFrom p rho z u 1).2 -
          (policyMatchedOrbit p rho z u 1).2 =
        p.s z.1 * (z.2 - p.stationaryStock 0) +
          (p.s z.1 - p.s 0) * p.stationaryStock 0 := by
    simp only [controlledCivicWeightedOrbitFrom, policyMatchedOrbit,
      controlledCivicWeightedStep, calibratedPoint, LoopParams.stockStep,
      model.no_content_gain, add_zero]
    ring
  rw [hidentity]
  calc
    |p.s z.1 * (z.2 - p.stationaryStock 0) +
        (p.s z.1 - p.s 0) * p.stationaryStock 0| ≤
        |p.s z.1| * |z.2 - p.stationaryStock 0| +
          |p.s z.1 - p.s 0| * |p.stationaryStock 0| := by
      simpa only [abs_mul] using abs_add_le
        (p.s z.1 * (z.2 - p.stationaryStock 0))
        ((p.s z.1 - p.s 0) * p.stationaryStock 0)
    _ ≤ dist z (calibratedPoint p) +
        2 * dist z (calibratedPoint p) * (p.I / p.lambda₀) :=
      add_le_add hfirst hsecond
    _ = policyMatchingInitialStockConstant p *
        dist z (calibratedPoint p) := by
      simp only [policyMatchingInitialStockConstant]
      ring

/-- The residual stock discrepancy decays geometrically, uniformly in the
control horizon and in the route taken by the common policy. -/
theorem policyMatchedOrbit_stock_geometric_bound
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    {z : LoopState} (hz : z ∈ absorbingBox p) (u : ℕ → ℝ) (n : ℕ) :
    |(controlledCivicWeightedOrbitFrom p rho z u (n + 1)).2 -
        (policyMatchedOrbit p rho z u (n + 1)).2| ≤
      (1 - p.lambda₀) ^ n * policyMatchingInitialStockConstant p *
        dist z (calibratedPoint p) := by
  induction n with
  | zero =>
      simpa only [pow_zero, one_mul] using
        policyMatchedOrbit_initial_stock_bound model rho hz u
  | succ n ih =>
      have hpath := controlledCivicWeightedOrbitFrom_isControlled p rho z u
      have hbeta := hpath.policy_mem hz.1 (n + 1)
      have hs := driftStockMultiplier_nonneg_le model hbeta
      rw [policyMatchedOrbit_stock_sub_succ_succ model rho z u n, abs_mul,
        abs_of_nonneg hs.1]
      calc
        p.s (controlledCivicWeightedOrbitFrom p rho z u (n + 1)).1 *
            |(controlledCivicWeightedOrbitFrom p rho z u (n + 1)).2 -
              (policyMatchedOrbit p rho z u (n + 1)).2| ≤
            (1 - p.lambda₀) *
              |(controlledCivicWeightedOrbitFrom p rho z u (n + 1)).2 -
                (policyMatchedOrbit p rho z u (n + 1)).2| :=
          mul_le_mul_of_nonneg_right hs.2 (abs_nonneg _)
        _ ≤ (1 - p.lambda₀) *
            ((1 - p.lambda₀) ^ n * policyMatchingInitialStockConstant p *
              dist z (calibratedPoint p)) :=
          mul_le_mul_of_nonneg_left ih
            (sub_nonneg.mpr model.lambda₀_lt_one.le)
        _ = (1 - p.lambda₀) ^ (n + 1) *
            policyMatchingInitialStockConstant p *
              dist z (calibratedPoint p) := by
          rw [pow_succ]
          ring

/-! ## Control-correction bounds -/

/-- A uniform bound for the coefficient multiplying the residual stock
discrepancy in every maintaining correction. -/
def policyMatchingGradientCoefficientConstant (rho : ℝ) : ℝ :=
  2 + |rho|

/-- The common-policy gradient coefficient is uniformly bounded on the policy
interval. -/
theorem abs_matchingGradientCoefficient_le
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    {beta : ℝ} (hbeta : beta ∈ Icc (0 : ℝ) 1) :
    |2 * p.c * (1 - p.c * beta) - rho| ≤
      policyMatchingGradientCoefficientConstant rho := by
  have hcbetaNonneg : 0 ≤ p.c * beta :=
    mul_nonneg model.c_pos.le hbeta.1
  have hcbetaLeOne : p.c * beta ≤ 1 := calc
    p.c * beta ≤ p.c * 1 :=
      mul_le_mul_of_nonneg_left hbeta.2 model.c_pos.le
    _ = p.c := mul_one _
    _ ≤ 1 := model.c_lt_one.le
  have hinnerNonneg : 0 ≤ 1 - p.c * beta :=
    sub_nonneg.mpr hcbetaLeOne
  have hinnerLeOne : 1 - p.c * beta ≤ 1 := by linarith
  have hproductLeOne : p.c * (1 - p.c * beta) ≤ 1 := calc
    p.c * (1 - p.c * beta) ≤ 1 * (1 - p.c * beta) :=
      mul_le_mul_of_nonneg_right model.c_lt_one.le hinnerNonneg
    _ = 1 - p.c * beta := one_mul _
    _ ≤ 1 := hinnerLeOne
  have hcoefficientNonneg : 0 ≤ 2 * p.c * (1 - p.c * beta) := by
    exact mul_nonneg (mul_nonneg (by norm_num) model.c_pos.le) hinnerNonneg
  have hcoefficientLe : 2 * p.c * (1 - p.c * beta) ≤ 2 := by
    nlinarith
  calc
    |2 * p.c * (1 - p.c * beta) - rho| ≤
        |2 * p.c * (1 - p.c * beta)| + |rho| := abs_sub _ _
    _ = 2 * p.c * (1 - p.c * beta) + |rho| := by
      rw [abs_of_nonneg hcoefficientNonneg]
    _ ≤ 2 + |rho| := add_le_add hcoefficientLe le_rfl
    _ = policyMatchingGradientCoefficientConstant rho := rfl

/-- Every post-initial correction inherits the uniform geometric stock
bound. -/
theorem policyMatchedControlSequence_succ_sub_bound
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    {z : LoopState} (hz : z ∈ absorbingBox p) (u : ℕ → ℝ) (n : ℕ) :
    |policyMatchedControlSequence p rho z u (n + 1) - u (n + 1)| ≤
      policyMatchingGradientCoefficientConstant rho *
        ((1 - p.lambda₀) ^ n * policyMatchingInitialStockConstant p *
          dist z (calibratedPoint p)) := by
  have hpath := controlledCivicWeightedOrbitFrom_isControlled p rho z u
  have hbeta := hpath.policy_mem hz.1 (n + 1)
  have hcoefficient := abs_matchingGradientCoefficient_le model rho hbeta
  have hstock := policyMatchedOrbit_stock_geometric_bound model rho hz u n
  rw [policyMatchedControlSequence_succ_eq]
  have hrewrite :
      u (n + 1) +
          (2 * p.c *
              (1 - p.c *
                (controlledCivicWeightedOrbitFrom p rho z u (n + 1)).1) - rho) *
            ((controlledCivicWeightedOrbitFrom p rho z u (n + 1)).2 -
              (policyMatchedOrbit p rho z u (n + 1)).2) -
          u (n + 1) =
        (2 * p.c *
              (1 - p.c *
                (controlledCivicWeightedOrbitFrom p rho z u (n + 1)).1) - rho) *
            ((controlledCivicWeightedOrbitFrom p rho z u (n + 1)).2 -
              (policyMatchedOrbit p rho z u (n + 1)).2) := by ring
  rw [hrewrite, abs_mul]
  exact mul_le_mul hcoefficient hstock (abs_nonneg _)
    (by simp only [policyMatchingGradientCoefficientConstant]; positivity)

/-- A convenient explicit Lipschitz constant for the one-shot control
correction at time zero. -/
def policyMatchingInitialControlConstant (p : LoopParams) (rho : ℝ) : ℝ :=
  1 / p.α +
    2 * p.c * (1 + p.c * (p.I / p.lambda₀)) + |rho|

/-- The initial weighted-gradient discrepancy is Lipschitz on the absorbing
box at the calibrated corner. -/
theorem civicWeightedGradient_initial_sub_bound
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    {z : LoopState} (hz : z ∈ absorbingBox p) :
    |civicWeightedGradient p rho z.1 z.2 -
        civicWeightedGradient p rho 0 (p.stationaryStock 0)| ≤
      (2 * p.c * (1 + p.c * (p.I / p.lambda₀)) + |rho|) *
        dist z (calibratedPoint p) := by
  have hzero : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hD0mem := stationaryStock_mem_stockInterval model hzero
  have hzDnonneg : 0 ≤ z.2 := model.I_pos.le.trans hz.2.1
  have hdistBeta : z.1 ≤ dist z (calibratedPoint p) := by
    have h := le_max_left (dist z.1 (calibratedPoint p).1)
      (dist z.2 (calibratedPoint p).2)
    rw [← Prod.dist_eq] at h
    have habs : |z.1| ≤ dist z (calibratedPoint p) := by
      simpa only [calibratedPoint, Real.dist_eq, sub_zero] using h
    exact (le_abs_self z.1).trans habs
  have hdistStock : |z.2 - p.stationaryStock 0| ≤
      dist z (calibratedPoint p) := by
    rw [Prod.dist_eq]
    have h := le_max_right (dist z.1 (calibratedPoint p).1)
      (dist z.2 (calibratedPoint p).2)
    simpa only [calibratedPoint, Real.dist_eq] using h
  have hpolicyStock : p.c * z.1 * z.2 ≤
      p.c * dist z (calibratedPoint p) * (p.I / p.lambda₀) := by
    have hfirst : p.c * z.1 ≤ p.c * dist z (calibratedPoint p) :=
      mul_le_mul_of_nonneg_left hdistBeta model.c_pos.le
    exact mul_le_mul hfirst hz.2.2 hzDnonneg
      (mul_nonneg model.c_pos.le (dist_nonneg : 0 ≤ dist z (calibratedPoint p)))
  have hcore :
      |(1 - p.c * z.1) * z.2 - p.stationaryStock 0| ≤
        (1 + p.c * (p.I / p.lambda₀)) *
          dist z (calibratedPoint p) := by
    have hidentity :
        (1 - p.c * z.1) * z.2 - p.stationaryStock 0 =
          (z.2 - p.stationaryStock 0) - p.c * z.1 * z.2 := by ring
    rw [hidentity]
    calc
      |z.2 - p.stationaryStock 0 - p.c * z.1 * z.2| ≤
          |z.2 - p.stationaryStock 0| + |p.c * z.1 * z.2| := abs_sub _ _
      _ = |z.2 - p.stationaryStock 0| + p.c * z.1 * z.2 := by
        rw [abs_of_nonneg
          (mul_nonneg (mul_nonneg model.c_pos.le hz.1.1) hzDnonneg)]
      _ ≤ dist z (calibratedPoint p) +
          p.c * dist z (calibratedPoint p) * (p.I / p.lambda₀) :=
        add_le_add hdistStock hpolicyStock
      _ = (1 + p.c * (p.I / p.lambda₀)) *
          dist z (calibratedPoint p) := by ring
  have hidentity :
      civicWeightedGradient p rho z.1 z.2 -
          civicWeightedGradient p rho 0 (p.stationaryStock 0) =
        2 * p.c *
            ((1 - p.c * z.1) * z.2 - p.stationaryStock 0) -
          rho * (z.2 - p.stationaryStock 0) := by
    simp only [civicWeightedGradient, LoopParams.gradU, mul_zero, sub_zero]
    ring
  rw [hidentity]
  calc
    |2 * p.c * ((1 - p.c * z.1) * z.2 - p.stationaryStock 0) -
        rho * (z.2 - p.stationaryStock 0)| ≤
        |2 * p.c * ((1 - p.c * z.1) * z.2 - p.stationaryStock 0)| +
          |rho * (z.2 - p.stationaryStock 0)| := abs_sub _ _
    _ = 2 * p.c *
          |(1 - p.c * z.1) * z.2 - p.stationaryStock 0| +
        |rho| * |z.2 - p.stationaryStock 0| := by
      simp only [abs_mul, abs_of_nonneg model.c_pos.le,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * p.c *
          ((1 + p.c * (p.I / p.lambda₀)) *
            dist z (calibratedPoint p)) +
        |rho| * dist z (calibratedPoint p) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hcore
          (mul_nonneg (by norm_num) model.c_pos.le))
        (mul_le_mul_of_nonneg_left hdistStock (abs_nonneg rho))
    _ = (2 * p.c * (1 + p.c * (p.I / p.lambda₀)) + |rho|) *
        dist z (calibratedPoint p) := by ring

/-- The one-shot policy-and-gradient correction is linear in the distance
from the calibrated corner. -/
theorem policyMatchedControlSequence_zero_sub_bound
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    {z : LoopState} (hz : z ∈ absorbingBox p) (u : ℕ → ℝ) :
    |policyMatchedControlSequence p rho z u 0 - u 0| ≤
      policyMatchingInitialControlConstant p rho *
        dist z (calibratedPoint p) := by
  have hdistBeta : z.1 ≤ dist z (calibratedPoint p) := by
    have h := le_max_left (dist z.1 (calibratedPoint p).1)
      (dist z.2 (calibratedPoint p).2)
    rw [← Prod.dist_eq] at h
    have habs : |z.1| ≤ dist z (calibratedPoint p) := by
      simpa only [calibratedPoint, Real.dist_eq, sub_zero] using h
    exact (le_abs_self z.1).trans habs
  have hpolicy : |z.1 / p.α| ≤
      (1 / p.α) * dist z (calibratedPoint p) := by
    rw [abs_div, abs_of_nonneg hz.1.1, abs_of_pos model.α_pos]
    have hdiv := (div_le_div_iff_of_pos_right model.α_pos).2 hdistBeta
    calc
      z.1 / p.α ≤ dist z (calibratedPoint p) / p.α := hdiv
      _ = (1 / p.α) * dist z (calibratedPoint p) := by ring
  have hgradient := civicWeightedGradient_initial_sub_bound model rho hz
  rw [policyMatchedControlSequence_zero]
  have hrewrite :
      u 0 + z.1 / p.α + civicWeightedGradient p rho z.1 z.2 -
          civicWeightedGradient p rho 0 (p.stationaryStock 0) - u 0 =
        z.1 / p.α +
          (civicWeightedGradient p rho z.1 z.2 -
            civicWeightedGradient p rho 0 (p.stationaryStock 0)) := by ring
  rw [hrewrite]
  calc
    |z.1 / p.α +
        (civicWeightedGradient p rho z.1 z.2 -
          civicWeightedGradient p rho 0 (p.stationaryStock 0))| ≤
        |z.1 / p.α| +
          |civicWeightedGradient p rho z.1 z.2 -
            civicWeightedGradient p rho 0 (p.stationaryStock 0)| :=
      abs_add_le _ _
    _ ≤ (1 / p.α) * dist z (calibratedPoint p) +
        (2 * p.c * (1 + p.c * (p.I / p.lambda₀)) + |rho|) *
          dist z (calibratedPoint p) := add_le_add hpolicy hgradient
    _ = policyMatchingInitialControlConstant p rho *
        dist z (calibratedPoint p) := by
      simp only [policyMatchingInitialControlConstant]
      ring

/-- The squared-energy coefficient for all policy-matching corrections.  The
tail uses the uniform geometric bound `1 / lambda₀`. -/
def policyMatchingCorrectionEnergy (p : LoopParams) (rho : ℝ) : ℝ :=
  (policyMatchingInitialControlConstant p rho) ^ 2 +
    (policyMatchingGradientCoefficientConstant rho) ^ 2 *
      (policyMatchingInitialStockConstant p) ^ 2 / p.lambda₀

/-- The initial-stock comparison constant is positive. -/
theorem policyMatchingInitialStockConstant_pos
    {p : LoopParams} (model : DriftModelAssumptions p) :
    0 < policyMatchingInitialStockConstant p := by
  simp only [policyMatchingInitialStockConstant]
  have : 0 < p.I / p.lambda₀ := div_pos model.I_pos model.lambda₀_pos
  positivity

/-- The initial-control comparison constant is positive. -/
theorem policyMatchingInitialControlConstant_pos
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ) :
    0 < policyMatchingInitialControlConstant p rho := by
  simp only [policyMatchingInitialControlConstant]
  have hratio : 0 < p.I / p.lambda₀ :=
    div_pos model.I_pos model.lambda₀_pos
  have hinv : 0 < 1 / p.α := one_div_pos.mpr model.α_pos
  have hmiddle : 0 ≤
      2 * p.c * (1 + p.c * (p.I / p.lambda₀)) := by
    have hinside : 0 ≤ 1 + p.c * (p.I / p.lambda₀) :=
      add_nonneg zero_le_one (mul_nonneg model.c_pos.le hratio.le)
    exact mul_nonneg (mul_nonneg (by norm_num) model.c_pos.le) hinside
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg hinv hmiddle) (abs_nonneg rho)

/-- The full correction-energy coefficient is nonnegative. -/
theorem policyMatchingCorrectionEnergy_nonneg
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ) :
    0 ≤ policyMatchingCorrectionEnergy p rho := by
  simp only [policyMatchingCorrectionEnergy]
  exact add_nonneg (sq_nonneg _)
    (div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) model.lambda₀_pos.le)

/-- The finite control vector obtained by restricting the matched control
sequence corresponding to `u`. -/
def policyMatchedControl {T : ℕ} (p : LoopParams) (rho : ℝ)
    (z : LoopState) (u : Fin T → ℝ) : Fin T → ℝ :=
  fun i ↦ policyMatchedControlSequence p rho z (extendFiniteControl u) i

/-- The finite correction vector added to an original finite control. -/
def policyMatchedCorrection {T : ℕ} (p : LoopParams) (rho : ℝ)
    (z : LoopState) (u : Fin T → ℝ) : Fin T → ℝ :=
  fun i ↦ policyMatchedControl p rho z u i - u i

/-- Policy matching costs uniformly bounded squared control energy, independent
of the horizon and of the route followed by the common policy. -/
theorem sum_sq_policyMatchedCorrection_le
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    {z : LoopState} (hz : z ∈ absorbingBox p) {T : ℕ} (u : Fin T → ℝ) :
    (∑ i, (policyMatchedCorrection p rho z u i) ^ 2) ≤
      policyMatchingCorrectionEnergy p rho *
        (dist z (calibratedPoint p)) ^ 2 := by
  cases T with
  | zero =>
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact mul_nonneg (policyMatchingCorrectionEnergy_nonneg model rho) (sq_nonneg _)
  | succ T =>
      let uSeq : ℕ → ℝ := extendFiniteControl u
      let d : ℝ := dist z (calibratedPoint p)
      let C0 : ℝ := policyMatchingInitialControlConstant p rho
      let K : ℝ := policyMatchingGradientCoefficientConstant rho
      let C1 : ℝ := policyMatchingInitialStockConstant p
      let r : ℝ := 1 - p.lambda₀
      have hd : 0 ≤ d := by simp only [d]; positivity
      have hC0 : 0 ≤ C0 := by
        exact (policyMatchingInitialControlConstant_pos model rho).le
      have hK : 0 ≤ K := by
        simp only [K, policyMatchingGradientCoefficientConstant]
        positivity
      have hC1 : 0 ≤ C1 :=
        (policyMatchingInitialStockConstant_pos model).le
      have hr : 0 ≤ r := sub_nonneg.mpr model.lambda₀_lt_one.le
      have hzeroRaw :=
        policyMatchedControlSequence_zero_sub_bound model rho hz uSeq
      have hextZero : extendFiniteControl u 0 = u 0 := by
        simpa using extendFiniteControl_apply u (0 : Fin (T + 1))
      have hzero :
          |policyMatchedCorrection p rho z u 0| ≤ C0 * d := by
        simpa only [policyMatchedCorrection, policyMatchedControl,
          uSeq, Fin.val_zero, hextZero, C0, d] using hzeroRaw
      have hzeroSq :
          (policyMatchedCorrection p rho z u 0) ^ 2 ≤ (C0 * d) ^ 2 := by
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC0 hd)).2 hzero
      have htail : ∀ i : Fin T,
          |policyMatchedCorrection p rho z u i.succ| ≤
            K * (r ^ (i : ℕ) * C1 * d) := by
        intro i
        have hraw := policyMatchedControlSequence_succ_sub_bound
          model rho hz uSeq (i : ℕ)
        have hextSucc : extendFiniteControl u ((i : ℕ) + 1) = u i.succ := by
          simpa only [Fin.val_succ] using extendFiniteControl_apply u i.succ
        simpa only [policyMatchedCorrection, policyMatchedControl,
          uSeq, hextSucc, Fin.val_succ, K, r, C1, d] using hraw
      have htailSq : ∀ i : Fin T,
          (policyMatchedCorrection p rho z u i.succ) ^ 2 ≤
            (K * (r ^ (i : ℕ) * C1 * d)) ^ 2 := by
        intro i
        have hright : 0 ≤ K * (r ^ (i : ℕ) * C1 * d) := by positivity
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) hright).2 (htail i)
      have hgeom : (∑ i : Fin T, ((r ^ (i : ℕ)) ^ 2)) ≤
          1 / p.lambda₀ := by
        rw [Fin.sum_univ_eq_sum_range (fun n ↦ (r ^ n) ^ 2) T]
        exact sum_sq_geometric_le_inv_gap hr le_rfl model.lambda₀_pos T
      have htailSum :
          (∑ i : Fin T, (policyMatchedCorrection p rho z u i.succ) ^ 2) ≤
            K ^ 2 * C1 ^ 2 * d ^ 2 / p.lambda₀ := by
        calc
          (∑ i : Fin T, (policyMatchedCorrection p rho z u i.succ) ^ 2) ≤
              ∑ i : Fin T, (K * (r ^ (i : ℕ) * C1 * d)) ^ 2 := by
            exact Finset.sum_le_sum fun i _hi ↦ htailSq i
          _ = (K ^ 2 * C1 ^ 2 * d ^ 2) *
              ∑ i : Fin T, ((r ^ (i : ℕ)) ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _hi
            ring
          _ ≤ (K ^ 2 * C1 ^ 2 * d ^ 2) * (1 / p.lambda₀) := by
            exact mul_le_mul_of_nonneg_left hgeom (by positivity)
          _ = K ^ 2 * C1 ^ 2 * d ^ 2 / p.lambda₀ := by ring
      rw [Fin.sum_univ_succ]
      calc
        (policyMatchedCorrection p rho z u 0) ^ 2 +
            ∑ i : Fin T, (policyMatchedCorrection p rho z u i.succ) ^ 2 ≤
            (C0 * d) ^ 2 + K ^ 2 * C1 ^ 2 * d ^ 2 / p.lambda₀ :=
          add_le_add hzeroSq htailSum
        _ = policyMatchingCorrectionEnergy p rho *
            (dist z (calibratedPoint p)) ^ 2 := by
          simp only [policyMatchingCorrectionEnergy, C0, K, C1, d]
          ring

/-! ## Finite histories -/

/-- Restricting the matched sequence reproduces the matched path through the
finite horizon. -/
theorem finiteControlledOrbitFrom_policyMatchedControl
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    (z : LoopState) {T n : ℕ} (u : Fin T → ℝ) (hn : n ≤ T) :
    finiteControlledOrbitFrom p rho (calibratedPoint p)
        (policyMatchedControl p rho z u) n =
      policyMatchedOrbit p rho z (extendFiniteControl u) n := by
  exact finiteControlledOrbitFrom_restrict_eq
    (policyMatchedOrbit_isControlled model rho z (extendFiniteControl u)) hn

/-- A crossing path whose initial policy is strictly below the saddle remains
a crossing path after policy matching, and crosses at the same positive time. -/
theorem policyMatchedControl_crosses
    {p : LoopParams} (model : DriftModelAssumptions p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    {z : LoopState} (hzbelow : z.1 < weighted.βdagger)
    {T : ℕ} {u : Fin T → ℝ}
    (hcross : weighted.βdagger ≤
      policyRunningMax (finiteControlledOrbitFrom p rho z u) T) :
    weighted.βdagger ≤
      policyRunningMax
        (finiteControlledOrbit p rho (policyMatchedControl p rho z u)) T := by
  obtain ⟨k, hk, hbeta⟩ :=
    (le_runningMax_iff (a := fun n ↦
      (finiteControlledOrbitFrom p rho z u n).1)).1 hcross
  cases k with
  | zero =>
      simp only [finiteControlledOrbitFrom] at hbeta
      exact False.elim ((not_le_of_gt hzbelow) hbeta)
  | succ k =>
      apply (le_runningMax_iff (a := fun n ↦
        (finiteControlledOrbit p rho (policyMatchedControl p rho z u) n).1)).2
      refine ⟨k + 1, hk, ?_⟩
      rw [← finiteControlledOrbitFrom_calibratedPoint]
      rw [finiteControlledOrbitFrom_policyMatchedControl model rho z u hk]
      rw [policyMatchedOrbit_policy_succ]
      have horiginal :
          controlledCivicWeightedOrbitFrom p rho z (extendFiniteControl u) (k + 1) =
            finiteControlledOrbitFrom p rho z u (k + 1) := by
        have hrestrict := finiteControlledOrbitFrom_restrict_eq
          (controlledCivicWeightedOrbitFrom_isControlled
            p rho z (extendFiniteControl u)) hk
        simpa only [extendFiniteControl_apply] using hrestrict.symm
      rw [horiginal]
      exact hbeta

/-! ## Action comparison -/

/-- The matched action expands into the original action, its cross term with
the correction, and the correction action. -/
theorem gaussianVectorAction_policyMatchedControl
    (p : LoopParams) (rho : ℝ) (z : LoopState)
    {T : ℕ} (u : Fin T → ℝ) :
    gaussianVectorAction (policyMatchedControl p rho z u) =
      gaussianVectorAction u +
        ∑ i, u i * policyMatchedCorrection p rho z u i +
          gaussianVectorAction (policyMatchedCorrection p rho z u) := by
  have hpoint : ∀ i : Fin T,
      policyMatchedControl p rho z u i =
        u i + policyMatchedCorrection p rho z u i := by
    intro i
    simp only [policyMatchedCorrection]
    ring
  simp only [gaussianVectorAction]
  calc
    (1 / 2 : ℝ) * ∑ i, (policyMatchedControl p rho z u i) ^ 2 =
        (1 / 2 : ℝ) * ∑ i,
          ((u i) ^ 2 + 2 * u i * policyMatchedCorrection p rho z u i +
            (policyMatchedCorrection p rho z u i) ^ 2) := by
      apply congrArg ((1 / 2 : ℝ) * ·)
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hpoint]
      ring
    _ = (1 / 2 : ℝ) * ∑ i, (u i) ^ 2 +
        ∑ i, u i * policyMatchedCorrection p rho z u i +
          (1 / 2 : ℝ) *
            ∑ i, (policyMatchedCorrection p rho z u i) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      have hmiddle :
          (∑ i, 2 * u i * policyMatchedCorrection p rho z u i) =
            2 * ∑ i, u i * policyMatchedCorrection p rho z u i := by
        calc
          (∑ i, 2 * u i * policyMatchedCorrection p rho z u i) =
              ∑ i, 2 * (u i * policyMatchedCorrection p rho z u i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
          _ = 2 * ∑ i, u i * policyMatchedCorrection p rho z u i := by
            rw [Finset.mul_sum]
      rw [hmiddle]
      ring

/-- The horizon-independent constant in the policy-matching action bound. -/
def policyMatchingActionConstant (p : LoopParams) (rho : ℝ) : ℝ :=
  √(policyMatchingCorrectionEnergy p rho) +
    policyMatchingCorrectionEnergy p rho / 2

/-- The action-comparison constant is nonnegative. -/
theorem policyMatchingActionConstant_nonneg
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ) :
    0 ≤ policyMatchingActionConstant p rho := by
  simp only [policyMatchingActionConstant]
  exact add_nonneg (Real.sqrt_nonneg _)
    (div_nonneg (policyMatchingCorrectionEnergy_nonneg model rho) (by norm_num))

/-- Policy matching changes action by only `O(dist(z,p₁))`, uniformly in
the control horizon.  The factor involving the original action is the exact
Cauchy--Schwarz dependence used by the paper. -/
theorem gaussianVectorAction_policyMatchedControl_le
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    {z : LoopState} (hz : z ∈ absorbingBox p)
    (hzdistance : dist z (calibratedPoint p) ≤ 1)
    {T : ℕ} (u : Fin T → ℝ) :
    gaussianVectorAction (policyMatchedControl p rho z u) ≤
      gaussianVectorAction u +
        policyMatchingActionConstant p rho * dist z (calibratedPoint p) *
          (1 + √(2 * gaussianVectorAction u)) := by
  let correction : Fin T → ℝ := policyMatchedCorrection p rho z u
  let energy : ℝ := policyMatchingCorrectionEnergy p rho
  let d : ℝ := dist z (calibratedPoint p)
  have hd : 0 ≤ d := by simp only [d]; positivity
  have henergy : 0 ≤ energy := by
    exact policyMatchingCorrectionEnergy_nonneg model rho
  have hsumCorrection : (∑ i, (correction i) ^ 2) ≤ energy * d ^ 2 := by
    simpa only [correction, energy, d] using
      sum_sq_policyMatchedCorrection_le model rho hz u
  have hsqrtCorrection : √(∑ i, (correction i) ^ 2) ≤ √energy * d := by
    have hsqrt := Real.sqrt_le_sqrt hsumCorrection
    calc
      √(∑ i, (correction i) ^ 2) ≤ √(energy * d ^ 2) := hsqrt
      _ = √energy * √(d ^ 2) := Real.sqrt_mul henergy _
      _ = √energy * d := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hd]
  have horiginalSquares : (∑ i, (u i) ^ 2) =
      2 * gaussianVectorAction u := by
    simp only [gaussianVectorAction]
    ring
  have hcross :
      (∑ i, u i * correction i) ≤
        √(2 * gaussianVectorAction u) * (√energy * d) := by
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ u correction
    rw [horiginalSquares] at hcs
    exact hcs.trans (mul_le_mul_of_nonneg_left hsqrtCorrection
      (Real.sqrt_nonneg _))
  have hcorrectionAction : gaussianVectorAction correction ≤
      energy / 2 * d := by
    have hhalf := mul_le_mul_of_nonneg_left hsumCorrection
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hdsq : d ^ 2 ≤ d := by nlinarith [hd, hzdistance]
    have hreduce : (1 / 2 : ℝ) * (energy * d ^ 2) ≤
        energy / 2 * d := by
      have := mul_le_mul_of_nonneg_left hdsq henergy
      nlinarith
    simp only [gaussianVectorAction]
    exact hhalf.trans hreduce
  rw [gaussianVectorAction_policyMatchedControl]
  change gaussianVectorAction u + (∑ i, u i * correction i) +
      gaussianVectorAction correction ≤ _
  have hsum :
      (∑ i, u i * correction i) + gaussianVectorAction correction ≤
        √(2 * gaussianVectorAction u) * (√energy * d) +
          energy / 2 * d := add_le_add hcross hcorrectionAction
  have hfactor :
      √(2 * gaussianVectorAction u) * (√energy * d) +
          energy / 2 * d ≤
        policyMatchingActionConstant p rho * d *
          (1 + √(2 * gaussianVectorAction u)) := by
    have hsqrtAction : 0 ≤ √(2 * gaussianVectorAction u) :=
      Real.sqrt_nonneg _
    have hsqrtEnergy : 0 ≤ √energy := Real.sqrt_nonneg _
    have hhalfEnergy : 0 ≤ energy / 2 := div_nonneg henergy (by norm_num)
    simp only [policyMatchingActionConstant, energy, d]
    nlinarith [mul_nonneg hsqrtEnergy hd,
      mul_nonneg hhalfEnergy hd,
      mul_nonneg (mul_nonneg hhalfEnergy hd) hsqrtAction,
      mul_nonneg (mul_nonneg hsqrtEnergy hd) hsqrtAction]
  linarith

/-! ## Crossing values from nearby starts -/

/-- Crossing actions when the controlled path starts at an arbitrary state. -/
def crossingActionSetFrom {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (z : LoopState) : Set ℝ :=
  {a | ∃ (T : ℕ) (u : Fin T → ℝ),
    weighted.βdagger ≤
        policyRunningMax (finiteControlledOrbitFrom p rho z u) T ∧
      a = gaussianVectorAction u}

/-- The least crossing action from an arbitrary initial state. -/
def civicCrossingQuasipotentialFrom {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (z : LoopState) : ℝ :=
  sInf (crossingActionSetFrom weighted z)

/-- Crossing actions from every start are nonempty: one control can force the
next projected policy to one. -/
theorem crossingActionSetFrom_nonempty
    {p : LoopParams} (model : DriftModelAssumptions p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (z : LoopState) :
    (crossingActionSetFrom weighted z).Nonempty := by
  let u : Fin 1 → ℝ := fun _ ↦
    (1 - z.1) / p.α - civicWeightedGradient p rho z.1 z.2
  have hext : extendFiniteControl u 0 = u 0 := by
    simpa using extendFiniteControl_apply u (0 : Fin 1)
  have hinput :
      z.1 + p.α *
          (civicWeightedGradient p rho z.1 z.2 + u 0) = 1 := by
    simp only [u]
    field_simp [model.α_pos.ne']
    ring
  have horbit : (finiteControlledOrbitFrom p rho z u 1).1 = 1 := by
    rw [finiteControlledOrbitFrom, hext]
    change LoopParams.clipUnit
      (z.1 + p.α * (civicWeightedGradient p rho z.1 z.2 + u 0)) = 1
    rw [hinput]
    exact clipUnit_eq_self (by norm_num)
  have hcross : weighted.βdagger ≤
      policyRunningMax (finiteControlledOrbitFrom p rho z u) 1 := by
    calc
      weighted.βdagger ≤ 1 := weighted.βdagger_mem.2.le
      _ = (finiteControlledOrbitFrom p rho z u 1).1 := horbit.symm
      _ ≤ policyRunningMax (finiteControlledOrbitFrom p rho z u) 1 :=
        policy_le_runningMax _ _
  exact ⟨gaussianVectorAction u, 1, u, hcross, rfl⟩

/-- Arbitrary-start crossing actions are bounded below by zero. -/
theorem crossingActionSetFrom_bddBelow
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (z : LoopState) :
    BddBelow (crossingActionSetFrom weighted z) := by
  refine ⟨0, ?_⟩
  rintro a ⟨T, u, _hcross, rfl⟩
  simp only [gaussianVectorAction]
  positivity

/-- Under an a priori action cap, the explicit matching estimate may use the
same cap inside the Cauchy--Schwarz factor and any larger distance radius. -/
theorem gaussianVectorAction_policyMatchedControl_le_of_le
    {p : LoopParams} (model : DriftModelAssumptions p) (rho : ℝ)
    {z : LoopState} (hz : z ∈ absorbingBox p)
    {epsilon B : ℝ} (hdist : dist z (calibratedPoint p) ≤ epsilon)
    (hepsilon : epsilon ≤ 1) {T : ℕ} (u : Fin T → ℝ)
    (haction : gaussianVectorAction u ≤ B) :
    gaussianVectorAction (policyMatchedControl p rho z u) ≤
      gaussianVectorAction u +
        policyMatchingActionConstant p rho * epsilon *
          (1 + √(2 * B)) := by
  have hbase := gaussianVectorAction_policyMatchedControl_le
    model rho hz (hdist.trans hepsilon) u
  have hconstant := policyMatchingActionConstant_nonneg model rho
  have hepsilonNonneg : 0 ≤ epsilon := (dist_nonneg :
    0 ≤ dist z (calibratedPoint p)).trans hdist
  have hsqrt : √(2 * gaussianVectorAction u) ≤ √(2 * B) := by
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hdistanceFactor :
      policyMatchingActionConstant p rho * dist z (calibratedPoint p) ≤
        policyMatchingActionConstant p rho * epsilon :=
    mul_le_mul_of_nonneg_left hdist hconstant
  have hrootFactor :
      1 + √(2 * gaussianVectorAction u) ≤ 1 + √(2 * B) :=
    add_le_add le_rfl hsqrt
  have herror :
      policyMatchingActionConstant p rho * dist z (calibratedPoint p) *
          (1 + √(2 * gaussianVectorAction u)) ≤
        policyMatchingActionConstant p rho * epsilon * (1 + √(2 * B)) := by
    exact mul_le_mul hdistanceFactor hrootFactor
      (by positivity)
      (mul_nonneg hconstant hepsilonNonneg)
  exact hbase.trans (add_le_add le_rfl herror)

/-- Every nearby-start crossing control costs at least the calibrated crossing
value minus the policy-matching error.  Controls above `B` satisfy the claim
directly; controls below `B` are transported by matching. -/
theorem civicCrossingQuasipotential_sub_matchingError_le_action
    {p : LoopParams} (model : DriftModelAssumptions p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    {z : LoopState} (hz : z ∈ absorbingBox p)
    (hzbelow : z.1 < weighted.βdagger)
    {epsilon B : ℝ} (hdist : dist z (calibratedPoint p) ≤ epsilon)
    (hepsilon : epsilon ≤ 1)
    (hvalue : civicCrossingQuasipotential weighted ≤ B)
    {T : ℕ} {u : Fin T → ℝ}
    (hcross : weighted.βdagger ≤
      policyRunningMax (finiteControlledOrbitFrom p rho z u) T) :
    civicCrossingQuasipotential weighted -
        policyMatchingActionConstant p rho * epsilon * (1 + √(2 * B)) ≤
      gaussianVectorAction u := by
  rcases le_total (gaussianVectorAction u) B with haction | hlarge
  · have hmatchedCross :=
      policyMatchedControl_crosses model weighted hzbelow hcross
    have hvalueMatched :=
      civicCrossingQuasipotential_le_gaussianVectorAction
        weighted hmatchedCross
    have hmatchedAction :=
      gaussianVectorAction_policyMatchedControl_le_of_le
        model rho hz hdist hepsilon u haction
    linarith
  · have herrorNonneg : 0 ≤
        policyMatchingActionConstant p rho * epsilon * (1 + √(2 * B)) := by
      have hepsilonNonneg : 0 ≤ epsilon :=
        (dist_nonneg : 0 ≤ dist z (calibratedPoint p)).trans hdist
      exact mul_nonneg
        (mul_nonneg (policyMatchingActionConstant_nonneg model rho)
          hepsilonNonneg)
        (add_nonneg zero_le_one (Real.sqrt_nonneg _))
    linarith

/-- The from-start crossing value is bounded below by the calibrated value
minus a linear matching error.  This is the `csInf` form consumed by the
last-exit persistence argument. -/
theorem crossingQuasipotential_lipschitz_at_calibrated
    {p : LoopParams} (model : DriftModelAssumptions p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    {z : LoopState} (hz : z ∈ absorbingBox p)
    {epsilon B : ℝ} (hdist : dist z (calibratedPoint p) ≤ epsilon)
    (hepsilon : epsilon ≤ 1) (hepsilonSaddle : epsilon < weighted.βdagger)
    (hvalue : civicCrossingQuasipotential weighted ≤ B) :
    civicCrossingQuasipotential weighted -
        policyMatchingActionConstant p rho * epsilon * (1 + √(2 * B)) ≤
      civicCrossingQuasipotentialFrom weighted z := by
  have hzPolicyDist : z.1 ≤ dist z (calibratedPoint p) := by
    have h := le_max_left (dist z.1 (calibratedPoint p).1)
      (dist z.2 (calibratedPoint p).2)
    rw [← Prod.dist_eq] at h
    have habs : |z.1| ≤ dist z (calibratedPoint p) := by
      simpa only [calibratedPoint, Real.dist_eq, sub_zero] using h
    exact (le_abs_self z.1).trans habs
  have hzbelow : z.1 < weighted.βdagger :=
    lt_of_le_of_lt (hzPolicyDist.trans hdist) hepsilonSaddle
  change _ ≤ sInf (crossingActionSetFrom weighted z)
  apply le_csInf (crossingActionSetFrom_nonempty model weighted z)
  rintro a ⟨T, u, hcross, rfl⟩
  exact civicCrossingQuasipotential_sub_matchingError_le_action
    model weighted hz hzbelow hdist hepsilon hvalue hcross

/-- The policy-matching lemma packaged in the abstract no-cheap-crossing
interface, uniformly over every horizon. -/
def policyMatchingNoCheapCrossingRate
    {p : LoopParams} (model : DriftModelAssumptions p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    (epsilon B : ℝ) (hepsilonNonneg : 0 ≤ epsilon)
    (hepsilon : epsilon ≤ 1)
    (hepsilonSaddle : epsilon < weighted.βdagger)
    (hvalue : civicCrossingQuasipotential weighted ≤ B) (T : ℕ) :
    NoCheapCrossingRate weighted where
  starts := absorbingBox p ∩ Metric.closedBall (calibratedPoint p) epsilon
  horizon := T
  rate := civicCrossingQuasipotential weighted
  error := policyMatchingActionConstant p rho * epsilon * (1 + √(2 * B))
  error_nonneg := by
    exact mul_nonneg
      (mul_nonneg (policyMatchingActionConstant_nonneg model rho)
        hepsilonNonneg)
      (add_nonneg zero_le_one (Real.sqrt_nonneg _))
  action_lower z hz u hcross := by
    have hzPolicyDist : z.1 ≤ dist z (calibratedPoint p) := by
      have h := le_max_left (dist z.1 (calibratedPoint p).1)
        (dist z.2 (calibratedPoint p).2)
      rw [← Prod.dist_eq] at h
      have habs : |z.1| ≤ dist z (calibratedPoint p) := by
        simpa only [calibratedPoint, Real.dist_eq, sub_zero] using h
      exact (le_abs_self z.1).trans habs
    have hzbelow : z.1 < weighted.βdagger :=
      lt_of_le_of_lt (hzPolicyDist.trans hz.2) hepsilonSaddle
    exact civicCrossingQuasipotential_sub_matchingError_le_action
      model weighted hz.1 hzbelow hz.2 hepsilon hvalue hcross

/-- Every positive tolerance admits a positive home radius whose matching
error is strictly below that tolerance. -/
theorem exists_policyMatching_radius
    {p : LoopParams} (model : DriftModelAssumptions p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (B : ℝ)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧
      epsilon < weighted.βdagger ∧
      policyMatchingActionConstant p rho * epsilon * (1 + √(2 * B)) < delta := by
  let F : ℝ := policyMatchingActionConstant p rho * (1 + √(2 * B))
  have hF : 0 ≤ F := by
    dsimp only [F]
    exact mul_nonneg (policyMatchingActionConstant_nonneg model rho)
      (add_nonneg zero_le_one (Real.sqrt_nonneg _))
  let epsilon : ℝ := min (1 / 2 : ℝ)
    (min (weighted.βdagger / 2) (delta / (2 * (F + 1))))
  have hdenom : 0 < 2 * (F + 1) := by positivity
  have hepsilonPos : 0 < epsilon := by
    dsimp only [epsilon]
    rw [lt_min_iff, lt_min_iff]
    exact ⟨by norm_num,
      div_pos weighted.βdagger_mem.1 (by norm_num),
      div_pos hdelta hdenom⟩
  have hepsilonOne : epsilon ≤ 1 :=
    (min_le_left _ _).trans (by norm_num)
  have hepsilonSaddle : epsilon < weighted.βdagger := by
    have hhalf : epsilon ≤ weighted.βdagger / 2 := by
      dsimp only [epsilon]
      exact (min_le_right (1 / 2 : ℝ)
        (min (weighted.βdagger / 2) (delta / (2 * (F + 1))))).trans
          (min_le_left (weighted.βdagger / 2) (delta / (2 * (F + 1))))
    linarith [weighted.βdagger_mem.1]
  have hepsilonFraction : epsilon ≤ delta / (2 * (F + 1)) :=
    (min_le_right (1 / 2 : ℝ) _).trans (min_le_right _ _)
  have hscaled : (F + 1) * epsilon ≤ delta / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hepsilonFraction (by linarith : 0 ≤ F + 1)
    calc
      (F + 1) * epsilon ≤
          (F + 1) * (delta / (2 * (F + 1))) := hmul
      _ = delta / 2 := by field_simp [ne_of_gt (by linarith : 0 < F + 1)]
  have herror : F * epsilon < delta := by
    have hcompare : F * epsilon ≤ (F + 1) * epsilon := by
      exact mul_le_mul_of_nonneg_right (by linarith) hepsilonPos.le
    linarith
  refine ⟨epsilon, hepsilonPos, hepsilonOne, hepsilonSaddle, ?_⟩
  calc
    policyMatchingActionConstant p rho * epsilon * (1 + √(2 * B)) =
        F * epsilon := by
      simp only [F]
      ring
    _ < delta := herror

#print axioms policyMatchedOrbit_isControlled
#print axioms policyMatchedOrbit_policy_succ
#print axioms policyMatchedControlSequence_zero
#print axioms policyMatchedControlSequence_succ
#print axioms civicWeightedGradient_sub_at_common_policy
#print axioms policyMatchedControlSequence_succ_eq
#print axioms policyMatchedOrbit_stock_sub_succ_succ
#print axioms abs_stockMultiplier_sub_zero_le
#print axioms policyMatchedOrbit_initial_stock_bound
#print axioms policyMatchedOrbit_stock_geometric_bound
#print axioms abs_matchingGradientCoefficient_le
#print axioms policyMatchedControlSequence_succ_sub_bound
#print axioms civicWeightedGradient_initial_sub_bound
#print axioms policyMatchedControlSequence_zero_sub_bound
#print axioms policyMatchingInitialStockConstant_pos
#print axioms policyMatchingInitialControlConstant_pos
#print axioms policyMatchingCorrectionEnergy_nonneg
#print axioms sum_sq_policyMatchedCorrection_le
#print axioms finiteControlledOrbitFrom_policyMatchedControl
#print axioms policyMatchedControl_crosses
#print axioms gaussianVectorAction_policyMatchedControl
#print axioms policyMatchingActionConstant_nonneg
#print axioms gaussianVectorAction_policyMatchedControl_le
#print axioms crossingActionSetFrom_nonempty
#print axioms crossingActionSetFrom_bddBelow
#print axioms gaussianVectorAction_policyMatchedControl_le_of_le
#print axioms civicCrossingQuasipotential_sub_matchingError_le_action
#print axioms crossingQuasipotential_lipschitz_at_calibrated
#print axioms policyMatchingNoCheapCrossingRate
#print axioms exists_policyMatching_radius

end

end CivicAlignment.PaperII
