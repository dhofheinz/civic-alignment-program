/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.FiveParameterMargin

/-!
# Paper III / IV: finite-sample coverage-probability transfer

The safe-side rule is deterministically sound on its coverage event.  This
file adds a genuinely finite-sample probability statement under explicit
assumptions: a square-integrable unbiased scalar margin estimator and a radius
calibrated with its *true* variance.  Chebyshev's inequality then bounds both
coverage failure and false certification.

This result does **not** justify substituting an estimated standard error, does
not assert asymptotic normality, and does not supply the population bridge from
a positive structural margin to an audit verdict.
-/

namespace CivicAlignment.PaperIII

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

variable {Ω : Type*}

/-- The pointwise event that a scalar estimator misses its registered error
radius.  Its complement is the corresponding coverage event. -/
def MarginCoverageFailureEvent
    (estimate : Ω → ℝ) (truth radius : ℝ) : Set Ω :=
  {ω | radius < |estimate ω - truth|}

/-- The pointwise event on which the one-sided safe-side rule certifies. -/
def MarginCertificationEvent
    (estimate : Ω → ℝ) (radius : ℝ) : Set Ω :=
  {ω | radius < estimate ω}

/-- If the true margin is nonpositive, every positive safe-side certification
lies inside the registered coverage-failure event. -/
theorem marginCertificationEvent_subset_coverageFailure
    {estimate : Ω → ℝ} {truth radius : ℝ} (htruth : truth ≤ 0) :
    MarginCertificationEvent estimate radius ⊆
      MarginCoverageFailureEvent estimate truth radius := by
  intro ω hω
  rw [MarginCertificationEvent, Set.mem_setOf_eq] at hω
  rw [MarginCoverageFailureEvent, Set.mem_setOf_eq]
  have hcontrast : radius < estimate ω - truth := by
    linarith
  exact hcontrast.trans_le (le_abs_self (estimate ω - truth))

variable [MeasurableSpace Ω] {μ : Measure Ω}

/-- Chebyshev gives an exact finite-sample failure-probability bound for an
unbiased square-integrable margin estimator at any positive fixed radius. -/
theorem marginCoverageFailureProbability_le_variance
    [IsFiniteMeasure μ] {estimate : Ω → ℝ} (hEstimate : MemLp estimate 2 μ)
    {truth radius : ℝ} (hunbiased : μ[estimate] = truth)
    (hradius : 0 < radius) :
    μ (MarginCoverageFailureEvent estimate truth radius) ≤
      ENNReal.ofReal (Var[estimate; μ] / radius ^ 2) := by
  have hsubset :
      MarginCoverageFailureEvent estimate truth radius ⊆
        {ω | radius ≤ |estimate ω - μ[estimate]|} := by
    intro ω hω
    rw [MarginCoverageFailureEvent, Set.mem_setOf_eq] at hω
    rw [Set.mem_setOf_eq, hunbiased]
    exact hω.le
  exact (measure_mono hsubset).trans
    (meas_ge_le_variance_div_sq hEstimate hradius)

/-- Consequently, the finite-sample false-certification probability is no
larger than the Chebyshev coverage-failure bound. -/
theorem falseCertificationProbability_le_variance
    [IsFiniteMeasure μ] {estimate : Ω → ℝ} (hEstimate : MemLp estimate 2 μ)
    {truth radius : ℝ} (hunbiased : μ[estimate] = truth)
    (htruth : truth ≤ 0) (hradius : 0 < radius) :
    μ (MarginCertificationEvent estimate radius) ≤
      ENNReal.ofReal (Var[estimate; μ] / radius ^ 2) := by
  exact (measure_mono
      (marginCertificationEvent_subset_coverageFailure htruth)).trans
    (marginCoverageFailureProbability_le_variance
      hEstimate hunbiased hradius)

/-! ## Finite families and registered joint coverage -/

/-- Bonferroni transfer for a finite registered family: the probability that
at least one coverage event fails is at most the sum of the supplied marginal
failure bounds.  No independence assumption is used. -/
theorem finiteFamilyCoverageFailureProbability_le_sum
    {ι : Type*} [Fintype ι] (failure : ι → Set Ω) (budget : ι → ENNReal)
    (hmarginal : ∀ i, μ (failure i) ≤ budget i) :
    μ (⋃ i, failure i) ≤ ∑ i, budget i := by
  exact (measure_iUnion_fintype_le μ failure).trans
    (Finset.sum_le_sum fun i _ ↦ hmarginal i)

/-- Applying the scalar Chebyshev theorem componentwise gives a joint
finite-sample coverage-failure bound for any finite family of unbiased,
square-integrable estimators with positive fixed radii. -/
theorem finiteFamilyMarginCoverageFailureProbability_le_sumVariance
    [IsFiniteMeasure μ] {ι : Type*} [Fintype ι]
    (estimate : ι → Ω → ℝ) (truth radius : ι → ℝ)
    (hEstimate : ∀ i, MemLp (estimate i) 2 μ)
    (hunbiased : ∀ i, μ[estimate i] = truth i)
    (hradius : ∀ i, 0 < radius i) :
    μ (⋃ i, MarginCoverageFailureEvent (estimate i) (truth i) (radius i)) ≤
      ∑ i, ENNReal.ofReal (Var[estimate i; μ] / (radius i) ^ 2) := by
  apply finiteFamilyCoverageFailureProbability_le_sum
  intro i
  exact marginCoverageFailureProbability_le_variance
    (hEstimate i) (hunbiased i) (hradius i)

/-- Any false registered verdict that can occur only when at least one
primitive coverage event fails inherits the same finite-family error budget. -/
theorem falseVerdictProbability_le_sum_of_subset_failures
    {ι : Type*} [Fintype ι] {falseVerdict : Set Ω}
    (failure : ι → Set Ω) (budget : ι → ENNReal)
    (hfalse : falseVerdict ⊆ ⋃ i, failure i)
    (hmarginal : ∀ i, μ (failure i) ≤ budget i) :
    μ falseVerdict ≤ ∑ i, budget i := by
  exact (measure_mono hfalse).trans
    (finiteFamilyCoverageFailureProbability_le_sum failure budget hmarginal)

/-- With positive true variance, a radius of two *true* standard deviations
has coverage-failure probability at most `1/4`.  This is distribution-free;
the sharper normal value requires an additional Gaussian assumption. -/
theorem twoTrueSigmaCoverageFailureProbability_le_quarter
    [IsFiniteMeasure μ] {estimate : Ω → ℝ} (hEstimate : MemLp estimate 2 μ)
    {truth : ℝ} (hunbiased : μ[estimate] = truth)
    (hvariance : 0 < Var[estimate; μ]) :
    μ (MarginCoverageFailureEvent estimate truth
        (2 * Real.sqrt Var[estimate; μ])) ≤
      ENNReal.ofReal ((1 : ℝ) / 4) := by
  have hsqrt : 0 < Real.sqrt Var[estimate; μ] :=
    Real.sqrt_pos.2 hvariance
  calc
    μ (MarginCoverageFailureEvent estimate truth
        (2 * Real.sqrt Var[estimate; μ])) ≤
        ENNReal.ofReal
          (Var[estimate; μ] / (2 * Real.sqrt Var[estimate; μ]) ^ 2) :=
      marginCoverageFailureProbability_le_variance hEstimate hunbiased
        (mul_pos (by norm_num) hsqrt)
    _ = ENNReal.ofReal ((1 : ℝ) / 4) := by
      congr 1
      rw [mul_pow, Real.sq_sqrt (variance_nonneg estimate μ)]
      field_simp [hvariance.ne']
      norm_num

/-- Under the same explicit finite-sample assumptions, a two-true-sigma
safe-side rule has false-certification probability at most `1/4` whenever the
true margin is nonpositive. -/
theorem twoTrueSigmaFalseCertificationProbability_le_quarter
    [IsFiniteMeasure μ] {estimate : Ω → ℝ} (hEstimate : MemLp estimate 2 μ)
    {truth : ℝ} (hunbiased : μ[estimate] = truth)
    (htruth : truth ≤ 0) (hvariance : 0 < Var[estimate; μ]) :
    μ (MarginCertificationEvent estimate
        (2 * Real.sqrt Var[estimate; μ])) ≤
      ENNReal.ofReal ((1 : ℝ) / 4) := by
  exact (measure_mono
      (marginCertificationEvent_subset_coverageFailure htruth)).trans
    (twoTrueSigmaCoverageFailureProbability_le_quarter
      hEstimate hunbiased hvariance)

#print axioms marginCoverageFailureProbability_le_variance
#print axioms marginCertificationEvent_subset_coverageFailure
#print axioms falseCertificationProbability_le_variance
#print axioms finiteFamilyCoverageFailureProbability_le_sum
#print axioms finiteFamilyMarginCoverageFailureProbability_le_sumVariance
#print axioms falseVerdictProbability_le_sum_of_subset_failures
#print axioms twoTrueSigmaCoverageFailureProbability_le_quarter
#print axioms twoTrueSigmaFalseCertificationProbability_le_quarter

end

end CivicAlignment.PaperIII
