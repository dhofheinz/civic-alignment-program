/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.ArrheniusLower

/-!
# Paper II: the two-sided and variational Arrhenius laws

This file packages the first-entrance persistence estimate and the uniform
restart upper estimate into the paper's two theorems `thm:arr` and
`thm:rate`.
-/

namespace CivicAlignment.PaperII

open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

/-- Paper II, Theorem `thm:rate` in `civic_drift.tex`: the crossing
quasipotential lies between the printed barriers, both exponential-horizon
probability clauses have this same sharp constant, the logarithmic mean
first-crossing time converges to it, and its fixed-primitives
small-adaptation-rate limit is the printed integrated barrier. -/
theorem escapeRateVariational
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
            (civicCrossingQuasipotential weighted - delta) sigma) sigma)
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0)) ∧
    (∀ delta : ℝ, 0 < delta →
      Tendsto
        (fun sigma : ℝ ↦ gaussianEscapeProbability weighted
          (exponentialEscapeHorizon
            (civicCrossingQuasipotential weighted + delta) sigma) sigma)
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 1)) ∧
    Tendsto (meanGaussianEscapeLogRate weighted)
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds ((civicCrossingQuasipotential weighted : ℝ) : EReal)) ∧
    Tendsto
      (fun alpha : ℝ ↦
        alpha * civicCrossingQuasipotentialAtRate weighted alpha)
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds (2 * weightedBarrierArea weighted)) := by
  exact ⟨crossingQuasipotential_bracket
      model ss threshold hrho hrhoCure hcoop weighted hL,
    fun delta hdelta ↦ crossingLowerEscapeProbability
      model ss threshold hrho hcoop weighted hL hdelta,
    fun delta hdelta ↦ crossingUpperEscapeProbability
      model ss threshold hrho hcoop weighted hdelta,
    crossingMeanRate model ss threshold hrho hcoop weighted hL,
    civicCrossingQuasipotentialAtRate_tendsto_barrier
      model ss threshold hrho hrhoCure hcoop weighted⟩

/-- Paper II, Theorem `thm:arr` in `civic_drift.tex`: the saddle-crossing
time obeys the printed two-sided Arrhenius law.  The probability horizons
use the corrected integral and the two-phase cost, the logarithmic mean is
pinched between the same constants, and the intervening sharp rate has the
printed leading small-adaptation-rate limit. -/
theorem arrheniusLaw
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho L : ℝ} (hrho : 0 ≤ rho) (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    (∀ delta : ℝ, 0 < delta →
      Tendsto
        (fun sigma : ℝ ↦ gaussianEscapeProbability weighted
          (exponentialEscapeHorizon
            ((2 / (p.α * (1 + 2 * p.α * L))) *
              (∫ b in (0 : ℝ)..weighted.βdagger,
                weightedBarrierIntegrand p rho b) - delta) sigma) sigma)
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0)) ∧
    (∀ delta : ℝ, 0 < delta →
      Tendsto
        (fun sigma : ℝ ↦ gaussianEscapeProbability weighted
          (exponentialEscapeHorizon
            (upwardStrategyCost weighted + delta) sigma) sigma)
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 1)) ∧
    (((2 / (p.α * (1 + 2 * p.α * L))) *
          (∫ b in (0 : ℝ)..weighted.βdagger,
            weightedBarrierIntegrand p rho b) : ℝ) : EReal) ≤
      liminf (meanGaussianEscapeLogRate weighted)
        (nhdsWithin 0 (Ioi (0 : ℝ))) ∧
    liminf (meanGaussianEscapeLogRate weighted)
        (nhdsWithin 0 (Ioi (0 : ℝ))) ≤
      limsup (meanGaussianEscapeLogRate weighted)
        (nhdsWithin 0 (Ioi (0 : ℝ))) ∧
    limsup (meanGaussianEscapeLogRate weighted)
        (nhdsWithin 0 (Ioi (0 : ℝ))) ≤
      ((upwardStrategyCost weighted : ℝ) : EReal) ∧
    Tendsto
      (fun alpha : ℝ ↦
        alpha * civicCrossingQuasipotentialAtRate weighted alpha)
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds (2 * weightedBarrierArea weighted)) := by
  let Vminus : ℝ :=
    (2 / (p.α * (1 + 2 * p.α * L))) *
      (∫ b in (0 : ℝ)..weighted.βdagger,
        weightedBarrierIntegrand p rho b)
  let Vcross : ℝ := civicCrossingQuasipotential weighted
  let Vplus : ℝ := upwardStrategyCost weighted
  have hchain := crossingQuasipotential_bracket
    model ss threshold hrho hrhoCure hcoop weighted hL
  have hminusCross : Vminus ≤ Vcross := by
    simpa only [Vminus, Vcross] using hchain.1
  have hcrossPlus : Vcross ≤ Vplus := by
    simpa only [Vcross, Vplus] using hchain.2.1.trans hchain.2.2
  have hmean := crossingMeanRate
    model ss threshold hrho hcoop weighted hL
  refine ⟨?_, ?_, ?_, ?_, ?_,
    civicCrossingQuasipotentialAtRate_tendsto_barrier
      model ss threshold hrho hrhoCure hcoop weighted⟩
  · intro delta hdelta
    have hsharp := crossingLowerEscapeProbability
      model ss threshold hrho hcoop weighted hL hdelta
    have hpointwise : ∀ sigma : ℝ,
        gaussianEscapeProbability weighted
            (exponentialEscapeHorizon (Vminus - delta) sigma) sigma ≤
          gaussianEscapeProbability weighted
            (exponentialEscapeHorizon (Vcross - delta) sigma) sigma := by
      intro sigma
      apply monotone_gaussianEscapeProbability weighted sigma
      apply monotone_exponentialEscapeHorizon sigma
      linarith
    have hzero : Tendsto (fun _ : ℝ ↦ (0 : ℝ≥0∞))
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := tendsto_const_nhds
    have hsqueezed := hzero.squeeze' hsharp
      (Eventually.of_forall fun _ ↦ bot_le)
      (Eventually.of_forall hpointwise)
    simpa only [Vminus, Vcross] using hsqueezed
  · intro delta hdelta
    have hsharp := crossingUpperEscapeProbability
      model ss threshold hrho hcoop weighted hdelta
    have hpointwise : ∀ sigma : ℝ,
        gaussianEscapeProbability weighted
            (exponentialEscapeHorizon (Vcross + delta) sigma) sigma ≤
          gaussianEscapeProbability weighted
            (exponentialEscapeHorizon (Vplus + delta) sigma) sigma := by
      intro sigma
      apply monotone_gaussianEscapeProbability weighted sigma
      apply monotone_exponentialEscapeHorizon sigma
      linarith
    have hprobability : ∀ sigma : ℝ,
        gaussianEscapeProbability weighted
            (exponentialEscapeHorizon (Vplus + delta) sigma) sigma ≤ 1 := by
      intro sigma
      letI : IsProbabilityMeasure
          (standardGaussianVector
            (exponentialEscapeHorizon (Vplus + delta) sigma)) := by
        unfold standardGaussianVector
        infer_instance
      exact prob_le_one
    have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ≥0∞))
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 1) := tendsto_const_nhds
    have hsqueezed := hsharp.squeeze' hone
      (Eventually.of_forall hpointwise)
      (Eventually.of_forall hprobability)
    simpa only [Vcross, Vplus] using hsqueezed
  · rw [hmean.liminf_eq]
    exact_mod_cast hminusCross
  · rw [hmean.liminf_eq, hmean.limsup_eq]
  · rw [hmean.limsup_eq]
    exact_mod_cast hcrossPlus

#print axioms escapeRateVariational
#print axioms arrheniusLaw

end

end CivicAlignment.PaperII
