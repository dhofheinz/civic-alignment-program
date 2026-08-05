/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.BasinExitLower
import CivicAlignment.PaperII.SaddlePassageContinuity

/-!
# Paper II: the mean basin-exit rate bracket and its sharp closures

Under the base small-step condition, the mean genuine basin-exit logarithmic
rate lies between the crossing and basin quasipotentials.  Under weighted
`(SS+)`, the boundary-excursion theorem proves directly that the rate equals
the basin quasipotential.  Independently, the vanishing-continuation property
closes the base-condition bracket by identifying its two endpoints.  No
declaration asserts the vanishing-continuation property itself.
-/

namespace CivicAlignment.PaperII

open Filter Set
open scoped Topology

/-- The unconditional two-sided bracket: the mean genuine basin-exit
logarithmic rate lies between the crossing and basin quasipotentials. -/
theorem meanGaussianBasinExitLogRate_bracket
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho L : ℝ} (hrho : 0 ≤ rho) (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    ((civicCrossingQuasipotential weighted : ℝ) : EReal) ≤
        liminf (meanGaussianBasinExitLogRate model ss threshold hrho)
          (nhdsWithin 0 (Ioi (0 : ℝ))) ∧
      limsup (meanGaussianBasinExitLogRate model ss threshold hrho)
          (nhdsWithin 0 (Ioi (0 : ℝ))) ≤
        ((civicQuasipotential p rho : ℝ) : EReal) :=
  ⟨crossingQuasipotential_le_liminf_meanGaussianBasinExitLogRate
      model ss threshold hrho hcoop weighted hL,
    meanGaussianBasinExitLogRate_limsup_le_quasipotential
      model ss threshold hrho hrhoCure hcoop⟩

/-- Under weighted `(SS+)`, the difference between the genuine mean basin-exit
logarithmic rate and the mean first-crossing logarithmic rate converges to the
quasipotential gap.  Both limiting quasipotentials are finite real points of
`EReal`, so the subtraction avoids its two indeterminate endpoint cases. -/
theorem meanGaussianBasinExitCrossingLogRateGap_tendsto_of_convergentStep
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho L : ℝ} (hrho : 0 ≤ rho) (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (ssplus : WeightedConvergentStepAssumption p rho)
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    Tendsto
      (fun sigma : ℝ ↦
        meanGaussianBasinExitLogRate model ss threshold hrho sigma -
          meanGaussianEscapeLogRate weighted sigma)
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds (((civicQuasipotential p rho -
        civicCrossingQuasipotential weighted : ℝ) : EReal))) := by
  have hexit := meanGaussianBasinExitLogRate_tendsto_of_convergentStep
    model ss threshold hrho hrhoCure hcoop ssplus weighted hL
  have hcross := crossingMeanRate
    model ss threshold hrho hcoop weighted hL
  have hcrossNeg : Tendsto
      (fun sigma : ℝ ↦ -meanGaussianEscapeLogRate weighted sigma)
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds (-((civicCrossingQuasipotential weighted : ℝ) : EReal))) :=
    continuous_neg.continuousAt.tendsto.comp hcross
  have hV_ne_top :
      ((civicQuasipotential p rho : ℝ) : EReal) ≠ ⊤ :=
    EReal.coe_ne_top _
  have hV_ne_bot :
      ((civicQuasipotential p rho : ℝ) : EReal) ≠ ⊥ :=
    EReal.coe_ne_bot _
  have hgap : Tendsto
      (fun sigma : ℝ ↦
        meanGaussianBasinExitLogRate model ss threshold hrho sigma +
          -meanGaussianEscapeLogRate weighted sigma)
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds (((civicQuasipotential p rho : ℝ) : EReal) +
        -((civicCrossingQuasipotential weighted : ℝ) : EReal))) := by
    exact (EReal.continuousAt_add
      (Or.inl hV_ne_top) (Or.inl hV_ne_bot)).tendsto.comp
        (hexit.prodMk_nhds hcrossNeg)
  simpa only [sub_eq_add_neg, EReal.coe_add, EReal.coe_neg] using hgap

/-- Conditional genuine basin-exit Arrhenius law: the vanishing-continuation
property closes the bracket, and the mean-exit logarithmic rate converges to
the common value of the two quasipotentials. -/
theorem meanGaussianBasinExitLogRate_tendsto_of_vanishingContinuation
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho L : ℝ} (hrho : 0 ≤ rho) (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (continuity : HasVanishingSaddlePassageContinuation weighted) :
    Tendsto (meanGaussianBasinExitLogRate model ss threshold hrho)
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds ((civicQuasipotential p rho : ℝ) : EReal)) := by
  have hbracket := meanGaussianBasinExitLogRate_bracket
    model ss threshold hrho hrhoCure hcoop weighted hL
  have hequal : civicCrossingQuasipotential weighted =
      civicQuasipotential p rho :=
    saddlePassageConjecture_of_vanishingContinuation
      model ss threshold hrho hrhoCure hcoop weighted continuity
  refine tendsto_of_le_liminf_of_limsup_le ?_ hbracket.2
  rw [← hequal]
  exact hbracket.1

#print axioms meanGaussianBasinExitLogRate_bracket
#print axioms meanGaussianBasinExitCrossingLogRateGap_tendsto_of_convergentStep
#print axioms meanGaussianBasinExitLogRate_tendsto_of_vanishingContinuation

end CivicAlignment.PaperII
