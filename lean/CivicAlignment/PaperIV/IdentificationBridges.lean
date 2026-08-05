/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIV.RegisteredProtocol

/-!
# Paper IV: scoped population-identification obligations

This file refines the abstract `AuditIdentification` interface into the
primitive registered instruments.  It deliberately separates:

1. coverage events connecting seven one-sided estimates to supplied true
   estimands;
2. positive-side classification events connecting the four non-scalar
   registered outputs to four separately named latent truths; and
3. six construct/population bridges connecting those truths to the scoped
   population premises.

The theorem at the end composes those obligations with the decision algebra.
It does not discharge any layer from data: scalar coverage calibration,
non-scalar classification validity, and every population bridge remain
empirical obligations of a registered audit.
-/

namespace CivicAlignment.PaperIV

noncomputable section

/-- The true scalar estimands corresponding to the seven primitive one-sided
tests in C1--C5.  Basin position is already represented by its own registered
three-valued decision and is therefore not duplicated as a scalar here. -/
structure RegisteredConditionTruths where
  c1Dilution : ℝ
  c2Selection : ℝ
  c3CapacityLoss : ℝ
  c4Manufacture : ℝ
  c4Ratchet : ℝ
  c5Decoupling : ℝ
  c5TelemetryBelow : ℝ

/-- The four non-scalar truths hidden by the original Boolean/decision
components.  These are propositions about the registered scope, not values
created by the corresponding recorded outputs. -/
structure RegisteredNonScalarTruths where
  exposureBelowThreshold : Prop
  covarianceRegime : Prop
  capturedBasinClassification : Prop
  retentionDesignValid : Prop

/-- All primitive finite-sample coverage events needed to transfer positive
one-sided decisions to positivity of their supplied true estimands. -/
structure RegisteredPrimitiveCoverageEvents
    (tests : RegisteredConditionTests)
    (truths : RegisteredConditionTruths) : Prop where
  c1_dilution :
    |tests.c1Dilution.estimate - truths.c1Dilution| ≤ tests.c1Dilution.radius
  c2_selection :
    |tests.c2Selection.estimate - truths.c2Selection| ≤ tests.c2Selection.radius
  c3_capacity :
    |tests.c3CapacityLoss.estimate - truths.c3CapacityLoss| ≤
      tests.c3CapacityLoss.radius
  c4_manufacture :
    |tests.c4Manufacture.estimate - truths.c4Manufacture| ≤
      tests.c4Manufacture.radius
  c4_ratchet :
    |tests.c4Ratchet.estimate - truths.c4Ratchet| ≤ tests.c4Ratchet.radius
  c5_decoupling :
    |tests.c5Decoupling.estimate - truths.c5Decoupling| ≤
      tests.c5Decoupling.radius
  c5_telemetry :
    |tests.c5TelemetryBelow.estimate - truths.c5TelemetryBelow| ≤
      tests.c5TelemetryBelow.radius

/-- Positive-side classification events for the four non-scalar registered
components.  Each field is a separate empirical obligation: a positive
recorded output transfers to its latent truth only on the corresponding
event.  No claim is made here about negative-side error or event probability. -/
structure RegisteredNonScalarCoverageEvents
    (tests : RegisteredConditionTests)
    (truths : RegisteredNonScalarTruths) : Prop where
  c1_exposure :
    tests.c1ExposureBelowThreshold = true → truths.exposureBelowThreshold
  c1_covariance :
    tests.c1CovarianceRegime = true → truths.covarianceRegime
  c4_basin :
    tests.c4Basin = .positive → truths.capturedBasinClassification
  c5_retention :
    tests.c5RetentionIdentified = true → truths.retentionDesignValid

/-- Exact transfer from a positive registered decision to a positive true
estimand on that test's supplied coverage event. -/
theorem RegisteredOneSidedTest.positiveTruth_of_coverage
    {test : RegisteredOneSidedTest} {truth : ℝ}
    (hcoverage : |test.estimate - truth| ≤ test.radius)
    (hpositive : test.decision = .positive) :
    0 < truth := by
  have hdecision :=
    (RegisteredOneSidedTest.decision_eq_positive_iff test).mp hpositive
  have herror : test.estimate - truth ≤ test.radius :=
    (le_abs_self (test.estimate - truth)).trans hcoverage
  linarith

/-! ## Supplementary C4-prime identification -/

/-- Coverage event for the true gain-minus-grounding contrast underlying the
supplementary C4-prime decision. -/
def C4PrimeCoverageEvent
    (record : C4PrimeRecord) (trueGainMinusGrounding : ℝ) : Prop :=
  |record.gainMinusGrounding.estimate - trueGainMinusGrounding| ≤
    record.gainMinusGrounding.radius

/-- Model bridge from a positive true gain-minus-grounding contrast to the
scoped capturability proposition reported by C4-prime.  This bridge is an
empirical/modeling obligation, not a consequence of the test statistic. -/
structure C4PrimeIdentification
    (trueGainMinusGrounding : ℝ)
    (capturableOnVisitedEnvelope : Prop) : Prop where
  positiveContrast_capturable :
    0 < trueGainMinusGrounding → capturableOnVisitedEnvelope

/-- A positive C4-prime decision supports capturability only on its contrast
coverage event and through its explicit model bridge. -/
theorem registeredC4Prime_sound
    {record : C4PrimeRecord} {trueGainMinusGrounding : ℝ}
    {capturableOnVisitedEnvelope : Prop}
    (hcoverage : C4PrimeCoverageEvent record trueGainMinusGrounding)
    (identified :
      C4PrimeIdentification trueGainMinusGrounding
        capturableOnVisitedEnvelope)
    (hpositive : record.decision = .positive) :
    capturableOnVisitedEnvelope := by
  change record.gainMinusGrounding.decision = .positive at hpositive
  apply identified.positiveContrast_capturable
  exact record.gainMinusGrounding.positiveTruth_of_coverage
    hcoverage hpositive

/-- The six scoped construct/population bridges at primitive-instrument grain.

These fields are assumptions to be supported by the audit design and external
validity evidence.  In particular, Lean does not infer them from positive
statistics, guards, or the names of the conditions. -/
structure RegisteredPopulationIdentificationBridges
    {Deployment Domain Claim State : Type*}
    {scope : AuditScope Deployment Domain Claim State}
    (truths : RegisteredConditionTruths)
    (nonScalar : RegisteredNonScalarTruths)
    (population : ScopedPopulationPremises scope) : Prop where
  c1_dilution :
    0 < truths.c1Dilution →
      nonScalar.exposureBelowThreshold →
      nonScalar.covarianceRegime →
      population.evidenceDilution
  c2_selection :
    0 < truths.c2Selection → population.satisfactionSelection
  c3_capacity :
    0 < truths.c3CapacityLoss → population.capacityLoss
  c4_feedback :
    0 < truths.c4Manufacture →
      0 < truths.c4Ratchet →
      population.harmfulFeedback
  c4_basin :
    nonScalar.capturedBasinClassification → population.capturedBasin
  c5_laundering :
    0 < truths.c5Decoupling →
      0 < truths.c5TelemetryBelow →
      nonScalar.retentionDesignValid →
      population.laundering

@[simp] theorem RegisteredDecision.ofBool_eq_positive_iff (b : Bool) :
    RegisteredDecision.ofBool b = .positive ↔ b = true := by
  cases b <;> simp [RegisteredDecision.ofBool]

/-- C1 is positive exactly when its one-sided test and both hard predicates
are positive. -/
theorem registeredCondition_C1_eq_positive_iff
    (tests : RegisteredConditionTests) :
    tests.decisions.C1 = .positive ↔
      tests.c1Dilution.decision = .positive ∧
        tests.c1ExposureBelowThreshold = true ∧
        tests.c1CovarianceRegime = true := by
  simp [RegisteredConditionTests.decisions, and_assoc]

/-- C4 is positive exactly when manufacture, ratchet, and basin components
are all positive. -/
theorem registeredCondition_C4_eq_positive_iff
    (tests : RegisteredConditionTests) :
    tests.decisions.C4 = .positive ↔
      tests.c4Manufacture.decision = .positive ∧
        tests.c4Ratchet.decision = .positive ∧
        tests.c4Basin = .positive := by
  simp [RegisteredConditionTests.decisions, and_assoc]

/-- C5 is positive exactly when both one-sided tests and the retention design
predicate are positive. -/
theorem registeredCondition_C5_eq_positive_iff
    (tests : RegisteredConditionTests) :
    tests.decisions.C5 = .positive ↔
      tests.c5Decoupling.decision = .positive ∧
        tests.c5TelemetryBelow.decision = .positive ∧
        tests.c5RetentionIdentified = true := by
  simp [RegisteredConditionTests.decisions, and_assoc]

/-- Scalar coverage, non-scalar positive-side validity, and the six empirical
population bridges discharge the abstract `AuditIdentification` interface for
this scoped registered audit. -/
theorem registeredAuditIdentification_of_coverage_and_bridges
    {Deployment Domain Claim State : Type*}
    {scope : AuditScope Deployment Domain Claim State}
    {tests : RegisteredConditionTests}
    {truths : RegisteredConditionTruths}
    {nonScalar : RegisteredNonScalarTruths}
    {population : ScopedPopulationPremises scope}
    (coverage : RegisteredPrimitiveCoverageEvents tests truths)
    (nonScalarCoverage :
      RegisteredNonScalarCoverageEvents tests nonScalar)
    (bridges :
      RegisteredPopulationIdentificationBridges truths nonScalar population) :
    AuditIdentification tests.decisions.toAuditConditions
      population.toPopulationPremises := by
  constructor
  · intro hC1
    change tests.decisions.C1 = .positive at hC1
    have hcomponents := (registeredCondition_C1_eq_positive_iff tests).mp hC1
    exact bridges.c1_dilution
      (tests.c1Dilution.positiveTruth_of_coverage
        coverage.c1_dilution hcomponents.1)
      (nonScalarCoverage.c1_exposure hcomponents.2.1)
      (nonScalarCoverage.c1_covariance hcomponents.2.2)
  · intro hC2
    change tests.c2Selection.decision = .positive at hC2
    exact bridges.c2_selection
      (tests.c2Selection.positiveTruth_of_coverage coverage.c2_selection hC2)
  · intro hC3
    change tests.c3CapacityLoss.decision = .positive at hC3
    exact bridges.c3_capacity
      (tests.c3CapacityLoss.positiveTruth_of_coverage coverage.c3_capacity hC3)
  · intro hC4
    change tests.decisions.C4 = .positive at hC4
    have hcomponents := (registeredCondition_C4_eq_positive_iff tests).mp hC4
    exact bridges.c4_feedback
      (tests.c4Manufacture.positiveTruth_of_coverage
        coverage.c4_manufacture hcomponents.1)
      (tests.c4Ratchet.positiveTruth_of_coverage
        coverage.c4_ratchet hcomponents.2.1)
  · intro hC4
    change tests.decisions.C4 = .positive at hC4
    exact bridges.c4_basin
      (nonScalarCoverage.c4_basin
        ((registeredCondition_C4_eq_positive_iff tests).mp hC4).2.2)
  · intro hC5
    change tests.decisions.C5 = .positive at hC5
    have hcomponents := (registeredCondition_C5_eq_positive_iff tests).mp hC5
    exact bridges.c5_laundering
      (tests.c5Decoupling.positiveTruth_of_coverage
        coverage.c5_decoupling hcomponents.1)
      (tests.c5TelemetryBelow.positiveTruth_of_coverage
        coverage.c5_telemetry hcomponents.2.1)
      (nonScalarCoverage.c5_retention hcomponents.2.2)

/-- A scoped registered pressure verdict is sound only after all empirical
obligation layers have been supplied. -/
theorem registeredLicensedPressure_scoped_sound
    {Deployment Domain Claim State : Type*}
    {scope : AuditScope Deployment Domain Claim State}
    {tests : RegisteredConditionTests}
    {truths : RegisteredConditionTruths}
    {nonScalar : RegisteredNonScalarTruths}
    {population : ScopedPopulationPremises scope}
    (coverage : RegisteredPrimitiveCoverageEvents tests truths)
    (nonScalarCoverage :
      RegisteredNonScalarCoverageEvents tests nonScalar)
    (bridges :
      RegisteredPopulationIdentificationBridges truths nonScalar population)
    (htier : tests.decisions.licensedTier = .pressure) :
    CivicPressure population.toPopulationPremises := by
  exact licensedPressure_sound
    (registeredAuditIdentification_of_coverage_and_bridges
      coverage nonScalarCoverage bridges)
    htier

/-- A scoped registered drift verdict is sound only after all empirical
obligation layers have been supplied. -/
theorem registeredLicensedDrift_scoped_sound
    {Deployment Domain Claim State : Type*}
    {scope : AuditScope Deployment Domain Claim State}
    {tests : RegisteredConditionTests}
    {truths : RegisteredConditionTruths}
    {nonScalar : RegisteredNonScalarTruths}
    {population : ScopedPopulationPremises scope}
    (coverage : RegisteredPrimitiveCoverageEvents tests truths)
    (nonScalarCoverage :
      RegisteredNonScalarCoverageEvents tests nonScalar)
    (bridges :
      RegisteredPopulationIdentificationBridges truths nonScalar population)
    (htier : tests.decisions.licensedTier = .drift) :
    CivicDrift population.toPopulationPremises := by
  exact licensedDrift_sound
    (registeredAuditIdentification_of_coverage_and_bridges
      coverage nonScalarCoverage bridges)
    htier

/-- A scoped registered capture verdict is sound only after all empirical
obligation layers have been supplied. -/
theorem registeredLicensedCapture_scoped_sound
    {Deployment Domain Claim State : Type*}
    {scope : AuditScope Deployment Domain Claim State}
    {tests : RegisteredConditionTests}
    {truths : RegisteredConditionTruths}
    {nonScalar : RegisteredNonScalarTruths}
    {population : ScopedPopulationPremises scope}
    (coverage : RegisteredPrimitiveCoverageEvents tests truths)
    (nonScalarCoverage :
      RegisteredNonScalarCoverageEvents tests nonScalar)
    (bridges :
      RegisteredPopulationIdentificationBridges truths nonScalar population)
    (htier : tests.decisions.licensedTier = .capture) :
    CivicCapture population.toPopulationPremises := by
  exact licensedCapture_sound
    (registeredAuditIdentification_of_coverage_and_bridges
      coverage nonScalarCoverage bridges)
    htier

#print axioms RegisteredOneSidedTest.positiveTruth_of_coverage
#print axioms registeredC4Prime_sound
#print axioms registeredCondition_C1_eq_positive_iff
#print axioms registeredCondition_C4_eq_positive_iff
#print axioms registeredCondition_C5_eq_positive_iff
#print axioms registeredAuditIdentification_of_coverage_and_bridges
#print axioms registeredLicensedPressure_scoped_sound
#print axioms registeredLicensedDrift_scoped_sound
#print axioms registeredLicensedCapture_scoped_sound

end


end CivicAlignment.PaperIV
