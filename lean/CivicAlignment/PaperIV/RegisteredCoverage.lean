/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.CoverageProbability
import CivicAlignment.PaperIV.IdentificationBridges

/-!
# Paper IV: registered familywise coverage interface

The audit has eleven primitive positive-side error opportunities: seven scalar
coverage events and four non-scalar classification events.  This file gives
that family a fixed index, requires the protocol to supply a marginal budget
for every member, and transfers those supplied bounds to a registered
familywise cap by Bonferroni.

A transparent equal allocation at a five-percent familywise cap is instantiated
below.  No marginal probability is derived; those remain sampling-law
obligations.
-/

namespace CivicAlignment.PaperIV

open MeasureTheory
open scoped BigOperators

/-- The eleven primitive coverage/classification components entering C1--C5. -/
inductive RegisteredCoverageComponent where
  | c1Dilution
  | c1Exposure
  | c1Covariance
  | c2Selection
  | c3Capacity
  | c4Manufacture
  | c4Ratchet
  | c4Basin
  | c5Decoupling
  | c5Telemetry
  | c5Retention
  deriving DecidableEq, Repr

instance : Fintype RegisteredCoverageComponent where
  elems := {
    .c1Dilution, .c1Exposure, .c1Covariance, .c2Selection, .c3Capacity,
    .c4Manufacture, .c4Ratchet, .c4Basin, .c5Decoupling, .c5Telemetry,
    .c5Retention }
  complete x := by cases x <;> simp

/-- There are exactly seven scalar and four non-scalar primitive components. -/
theorem registeredCoverageComponent_card :
    Fintype.card RegisteredCoverageComponent = 11 := by
  decide

/-- A protocol-level error allocation.  The marginal bounds must sum to no
more than the announced familywise cap, which itself is a probability bound. -/
structure RegisteredFamilywiseBudget where
  marginalFailureBudget : RegisteredCoverageComponent → ENNReal
  familywiseCap : ENNReal
  sum_marginal_le_cap :
    (∑ i, marginalFailureBudget i) ≤ familywiseCap
  cap_le_one : familywiseCap ≤ 1

/-- The registered default familywise cap is exactly five percent. -/
noncomputable def defaultRegisteredFamilywiseCap : ENNReal :=
  1 / 20

/-- Equal Bonferroni allocation of the five-percent cap across eleven
primitive components. -/
noncomputable def defaultRegisteredMarginalFailureBudget
    (_ : RegisteredCoverageComponent) : ENNReal :=
  1 / 220

/-- The eleven equal marginal budgets sum exactly to the five-percent cap. -/
theorem sum_defaultRegisteredMarginalFailureBudget :
    (∑ i, defaultRegisteredMarginalFailureBudget i) =
      defaultRegisteredFamilywiseCap := by
  simp only [defaultRegisteredMarginalFailureBudget]
  rw [Finset.sum_const, Finset.card_univ,
    registeredCoverageComponent_card, nsmul_eq_mul]
  simp only [defaultRegisteredFamilywiseCap, div_eq_mul_inv, one_mul]
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.mul_ne_top (by simp) (by simp)) (by simp)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv]

/-- The concrete default registered familywise budget. -/
noncomputable def defaultRegisteredFamilywiseBudget : RegisteredFamilywiseBudget where
  marginalFailureBudget := defaultRegisteredMarginalFailureBudget
  familywiseCap := defaultRegisteredFamilywiseCap
  sum_marginal_le_cap := sum_defaultRegisteredMarginalFailureBudget.le
  cap_le_one := by norm_num [defaultRegisteredFamilywiseCap]

/-- The joint registered coverage event is the complement of every primitive
failure event. -/
def RegisteredJointCoverageEvent {Ω : Type*}
    (failure : RegisteredCoverageComponent → Set Ω) : Set Ω :=
  (⋃ i, failure i)ᶜ

/-- Supplied marginal bounds imply the announced familywise cap, without an
independence assumption. -/
theorem registeredFamilywiseFailureProbability_le_cap
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (failure : RegisteredCoverageComponent → Set Ω)
    (budget : RegisteredFamilywiseBudget)
    (hmarginal : ∀ i, μ (failure i) ≤ budget.marginalFailureBudget i) :
    μ (⋃ i, failure i) ≤ budget.familywiseCap := by
  exact
    (CivicAlignment.PaperIII.finiteFamilyCoverageFailureProbability_le_sum
      failure budget.marginalFailureBudget hmarginal).trans
      budget.sum_marginal_le_cap

/-- Any false tier verdict that is possible only after at least one primitive
coverage/classification failure inherits the same registered cap. -/
theorem registeredFalseVerdictProbability_le_cap
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (failure : RegisteredCoverageComponent → Set Ω)
    (budget : RegisteredFamilywiseBudget) (falseVerdict : Set Ω)
    (hfalse : falseVerdict ⊆ ⋃ i, failure i)
    (hmarginal : ∀ i, μ (failure i) ≤ budget.marginalFailureBudget i) :
    μ falseVerdict ≤ budget.familywiseCap := by
  exact (measure_mono hfalse).trans
    (registeredFamilywiseFailureProbability_le_cap
      μ failure budget hmarginal)

/-! ## Instantiation for the registered audit rule -/

/-- A random audit record before its realized sample point is known.  The true
estimands, non-scalar truths, scope, and population premises remain fixed. -/
structure RandomRegisteredAudit (Ω : Type*) where
  tests : Ω → RegisteredConditionTests

/-- The seven scalar coverage failures and four non-scalar false-positive
classification failures, indexed by the registered eleven-component family. -/
def RegisteredAuditFailureEvent {Ω : Type*}
    (audit : RandomRegisteredAudit Ω) (truths : RegisteredConditionTruths)
    (nonScalar : RegisteredNonScalarTruths) :
    RegisteredCoverageComponent → Set Ω
  | .c1Dilution => {ω |
      ¬|(audit.tests ω).c1Dilution.estimate - truths.c1Dilution| ≤
        (audit.tests ω).c1Dilution.radius}
  | .c1Exposure => {ω |
      (audit.tests ω).c1ExposureBelowThreshold = true ∧
        ¬nonScalar.exposureBelowThreshold}
  | .c1Covariance => {ω |
      (audit.tests ω).c1CovarianceRegime = true ∧
        ¬nonScalar.covarianceRegime}
  | .c2Selection => {ω |
      ¬|(audit.tests ω).c2Selection.estimate - truths.c2Selection| ≤
        (audit.tests ω).c2Selection.radius}
  | .c3Capacity => {ω |
      ¬|(audit.tests ω).c3CapacityLoss.estimate - truths.c3CapacityLoss| ≤
        (audit.tests ω).c3CapacityLoss.radius}
  | .c4Manufacture => {ω |
      ¬|(audit.tests ω).c4Manufacture.estimate - truths.c4Manufacture| ≤
        (audit.tests ω).c4Manufacture.radius}
  | .c4Ratchet => {ω |
      ¬|(audit.tests ω).c4Ratchet.estimate - truths.c4Ratchet| ≤
        (audit.tests ω).c4Ratchet.radius}
  | .c4Basin => {ω |
      (audit.tests ω).c4Basin = .positive ∧
        ¬nonScalar.capturedBasinClassification}
  | .c5Decoupling => {ω |
      ¬|(audit.tests ω).c5Decoupling.estimate - truths.c5Decoupling| ≤
        (audit.tests ω).c5Decoupling.radius}
  | .c5Telemetry => {ω |
      ¬|(audit.tests ω).c5TelemetryBelow.estimate -
          truths.c5TelemetryBelow| ≤
        (audit.tests ω).c5TelemetryBelow.radius}
  | .c5Retention => {ω |
      (audit.tests ω).c5RetentionIdentified = true ∧
        ¬nonScalar.retentionDesignValid}

/-- Outside the union of the eleven primitive failures, both the scalar and
non-scalar coverage records are constructible for the realized audit. -/
theorem registeredCoverageEvents_of_not_mem_failureUnion
    {Ω : Type*} {audit : RandomRegisteredAudit Ω}
    {truths : RegisteredConditionTruths}
    {nonScalar : RegisteredNonScalarTruths} {ω : Ω}
    (hno : ω ∉ ⋃ i, RegisteredAuditFailureEvent audit truths nonScalar i) :
    RegisteredPrimitiveCoverageEvents (audit.tests ω) truths ∧
      RegisteredNonScalarCoverageEvents (audit.tests ω) nonScalar := by
  classical
  have hcomponent (i : RegisteredCoverageComponent) :
      ω ∉ RegisteredAuditFailureEvent audit truths nonScalar i := by
    intro hi
    exact hno (Set.mem_iUnion.2 ⟨i, hi⟩)
  constructor
  · constructor
    · simpa [RegisteredAuditFailureEvent] using hcomponent .c1Dilution
    · simpa [RegisteredAuditFailureEvent] using hcomponent .c2Selection
    · simpa [RegisteredAuditFailureEvent] using hcomponent .c3Capacity
    · simpa [RegisteredAuditFailureEvent] using hcomponent .c4Manufacture
    · simpa [RegisteredAuditFailureEvent] using hcomponent .c4Ratchet
    · simpa [RegisteredAuditFailureEvent] using hcomponent .c5Decoupling
    · simpa [RegisteredAuditFailureEvent] using hcomponent .c5Telemetry
  · constructor
    · intro hpositive
      by_contra htruth
      apply hcomponent .c1Exposure
      exact ⟨hpositive, htruth⟩
    · intro hpositive
      by_contra htruth
      apply hcomponent .c1Covariance
      exact ⟨hpositive, htruth⟩
    · intro hpositive
      by_contra htruth
      apply hcomponent .c4Basin
      exact ⟨hpositive, htruth⟩
    · intro hpositive
      by_contra htruth
      apply hcomponent .c5Retention
      exact ⟨hpositive, htruth⟩

/-- Event that the strongest returned tier overstates the corresponding fixed
population truth.  Returning `none` is never a false positive here. -/
def RegisteredFalseReturnedTierEvent
    {Ω Deployment Domain Claim State : Type*}
    (audit : RandomRegisteredAudit Ω)
    {scope : AuditScope Deployment Domain Claim State}
    (population : ScopedPopulationPremises scope) : Set Ω :=
  {ω | match (audit.tests ω).decisions.licensedTier with
    | .none => False
    | .pressure => ¬CivicPressure population.toPopulationPremises
    | .drift => ¬CivicDrift population.toPopulationPremises
    | .capture => ¬CivicCapture population.toPopulationPremises}

/-- Conditional construct validity makes every false returned tier a subset
of the eleven primitive coverage/classification failures. -/
theorem registeredFalseReturnedTier_subset_failureUnion
    {Ω Deployment Domain Claim State : Type*}
    {audit : RandomRegisteredAudit Ω}
    {scope : AuditScope Deployment Domain Claim State}
    {truths : RegisteredConditionTruths}
    {nonScalar : RegisteredNonScalarTruths}
    {population : ScopedPopulationPremises scope}
    (bridges :
      RegisteredPopulationIdentificationBridges truths nonScalar population) :
    RegisteredFalseReturnedTierEvent audit population ⊆
      ⋃ i, RegisteredAuditFailureEvent audit truths nonScalar i := by
  intro ω hfalse
  by_contra hno
  have coverage := registeredCoverageEvents_of_not_mem_failureUnion hno
  cases htier : (audit.tests ω).decisions.licensedTier with
  | none =>
      simp [RegisteredFalseReturnedTierEvent, htier] at hfalse
  | pressure =>
      have hnot : ¬CivicPressure population.toPopulationPremises := by
        simpa [RegisteredFalseReturnedTierEvent, htier] using hfalse
      exact hnot (registeredLicensedPressure_scoped_sound
        coverage.1 coverage.2 bridges htier)
  | drift =>
      have hnot : ¬CivicDrift population.toPopulationPremises := by
        simpa [RegisteredFalseReturnedTierEvent, htier] using hfalse
      exact hnot (registeredLicensedDrift_scoped_sound
        coverage.1 coverage.2 bridges htier)
  | capture =>
      have hnot : ¬CivicCapture population.toPopulationPremises := by
        simpa [RegisteredFalseReturnedTierEvent, htier] using hfalse
      exact hnot (registeredLicensedCapture_scoped_sound
        coverage.1 coverage.2 bridges htier)

/-- Supplied marginal bounds on the concrete eleven failure events imply the
registered familywise cap for an overstated returned tier. -/
theorem registeredFalseReturnedTierProbability_le_cap
    {Ω Deployment Domain Claim State : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {audit : RandomRegisteredAudit Ω}
    {scope : AuditScope Deployment Domain Claim State}
    {truths : RegisteredConditionTruths}
    {nonScalar : RegisteredNonScalarTruths}
    {population : ScopedPopulationPremises scope}
    (bridges :
      RegisteredPopulationIdentificationBridges truths nonScalar population)
    (budget : RegisteredFamilywiseBudget)
    (hmarginal : ∀ i,
      μ (RegisteredAuditFailureEvent audit truths nonScalar i) ≤
        budget.marginalFailureBudget i) :
    μ (RegisteredFalseReturnedTierEvent audit population) ≤
      budget.familywiseCap := by
  exact registeredFalseVerdictProbability_le_cap μ
    (RegisteredAuditFailureEvent audit truths nonScalar) budget
    (RegisteredFalseReturnedTierEvent audit population)
    (registeredFalseReturnedTier_subset_failureUnion bridges) hmarginal

/-- Under the concrete equal allocation, supplied one-over-220 marginal
bounds give a one-over-20 familywise bound for an overstated returned tier. -/
theorem registeredFalseReturnedTierProbability_le_fivePercent
    {Ω Deployment Domain Claim State : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {audit : RandomRegisteredAudit Ω}
    {scope : AuditScope Deployment Domain Claim State}
    {truths : RegisteredConditionTruths}
    {nonScalar : RegisteredNonScalarTruths}
    {population : ScopedPopulationPremises scope}
    (bridges :
      RegisteredPopulationIdentificationBridges truths nonScalar population)
    (hmarginal : ∀ i,
      μ (RegisteredAuditFailureEvent audit truths nonScalar i) ≤ 1 / 220) :
    μ (RegisteredFalseReturnedTierEvent audit population) ≤ 1 / 20 := by
  simpa [defaultRegisteredFamilywiseBudget,
    defaultRegisteredMarginalFailureBudget,
    defaultRegisteredFamilywiseCap] using
    registeredFalseReturnedTierProbability_le_cap μ bridges
      defaultRegisteredFamilywiseBudget hmarginal

#print axioms registeredCoverageComponent_card
#print axioms sum_defaultRegisteredMarginalFailureBudget
#print axioms registeredFamilywiseFailureProbability_le_cap
#print axioms registeredFalseVerdictProbability_le_cap
#print axioms registeredCoverageEvents_of_not_mem_failureUnion
#print axioms registeredFalseReturnedTier_subset_failureUnion
#print axioms registeredFalseReturnedTierProbability_le_cap
#print axioms registeredFalseReturnedTierProbability_le_fivePercent

end CivicAlignment.PaperIV
