/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIV.RegisteredCoverage

/-!
# Paper IV: fitted-basin classification risk interface

A fitted basin classifier needs error accounting for the fitted map, the
visited-envelope approximation, and state estimation.  This file gives a
signed-score certificate whose registered radius is the sum of those three
component radii.  Supplied component failure probabilities transfer to the
classifier's false-positive probability by a three-way union bound.

The file does not estimate any radius or validate any sampling law.
-/

namespace CivicAlignment.PaperIV

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Registered signed-score basin classifier with three separately reported
error radii.  Positive true score is the latent captured-side classification. -/
structure BasinClassificationRecord where
  estimatedScore : ℝ
  mapFitRadius : ℝ
  envelopeRadius : ℝ
  stateRadius : ℝ
  mapFitRadius_nonnegative : 0 ≤ mapFitRadius
  envelopeRadius_nonnegative : 0 ≤ envelopeRadius
  stateRadius_nonnegative : 0 ≤ stateRadius
  specificationGuardPassed : Bool

/-- Total registered positive-side error radius. -/
def BasinClassificationRecord.totalRadius
    (record : BasinClassificationRecord) : ℝ :=
  record.mapFitRadius + record.envelopeRadius + record.stateRadius

/-- The basin score uses the same three-valued safe-side decision rule as the
scalar audit tests. -/
def BasinClassificationRecord.test
    (record : BasinClassificationRecord) : RegisteredOneSidedTest where
  estimate := record.estimatedScore
  radius := record.totalRadius
  radius_nonneg := by
    exact add_nonneg
      (add_nonneg record.mapFitRadius_nonnegative
        record.envelopeRadius_nonnegative)
      record.stateRadius_nonnegative
  guardPassed := record.specificationGuardPassed

def BasinClassificationRecord.decision
    (record : BasinClassificationRecord) : RegisteredDecision :=
  record.test.decision

/-- Exact additive decomposition of signed-score error into the three named
sources. -/
def BasinScoreErrorDecomposition
    (record : BasinClassificationRecord) (trueScore : ℝ)
    (mapFitError envelopeError stateError : ℝ) : Prop :=
  record.estimatedScore - trueScore =
    mapFitError + envelopeError + stateError

/-- Componentwise error bounds imply coverage by the summed radius. -/
theorem basinScore_coverage_of_component_bounds
    {record : BasinClassificationRecord} {trueScore : ℝ}
    {mapFitError envelopeError stateError : ℝ}
    (hdecomposition : BasinScoreErrorDecomposition record trueScore
      mapFitError envelopeError stateError)
    (hmap : |mapFitError| ≤ record.mapFitRadius)
    (henvelope : |envelopeError| ≤ record.envelopeRadius)
    (hstate : |stateError| ≤ record.stateRadius) :
    |record.estimatedScore - trueScore| ≤ record.totalRadius := by
  rw [hdecomposition]
  have hfirst : |mapFitError + envelopeError| ≤
      |mapFitError| + |envelopeError| :=
    abs_add_le mapFitError envelopeError
  have hall : |mapFitError + envelopeError + stateError| ≤
      |mapFitError + envelopeError| + |stateError| :=
    abs_add_le (mapFitError + envelopeError) stateError
  simp only [BasinClassificationRecord.totalRadius]
  linarith

/-- A positive fitted-basin decision implies positive true basin score on the
three-source coverage event. -/
theorem basinClassification_positiveTruth
    {record : BasinClassificationRecord} {trueScore : ℝ}
    (hcoverage :
      |record.estimatedScore - trueScore| ≤ record.totalRadius)
    (hpositive : record.decision = .positive) :
    0 < trueScore := by
  exact record.test.positiveTruth_of_coverage hcoverage hpositive

/-- The three primitive error sources for fitted-basin classification. -/
inductive BasinErrorComponent where
  | mapFit
  | envelope
  | state
  deriving DecidableEq, Repr

instance : Fintype BasinErrorComponent where
  elems := {.mapFit, .envelope, .state}
  complete x := by cases x <;> simp

/-- Component failure events for a random fitted-basin record. -/
def BasinComponentFailureEvent {Ω : Type*}
    (record : Ω → BasinClassificationRecord)
    (mapFitError envelopeError stateError : Ω → ℝ) :
    BasinErrorComponent → Set Ω
  | .mapFit => {ω | (record ω).mapFitRadius < |mapFitError ω|}
  | .envelope => {ω | (record ω).envelopeRadius < |envelopeError ω|}
  | .state => {ω | (record ω).stateRadius < |stateError ω|}

/-- False positive for the latent captured-side score. -/
def BasinClassificationFalsePositiveEvent {Ω : Type*}
    (record : Ω → BasinClassificationRecord) (trueScore : ℝ) : Set Ω :=
  {ω | (record ω).decision = .positive ∧ trueScore ≤ 0}

/-- Under the pointwise error decomposition, every false positive requires at
least one of the three registered component bounds to fail. -/
theorem basinClassificationFalsePositive_subset_failureUnion
    {Ω : Type*} {record : Ω → BasinClassificationRecord}
    {trueScore : ℝ} {mapFitError envelopeError stateError : Ω → ℝ}
    (hdecomposition : ∀ ω,
      BasinScoreErrorDecomposition (record ω) trueScore
        (mapFitError ω) (envelopeError ω) (stateError ω)) :
    BasinClassificationFalsePositiveEvent record trueScore ⊆
      ⋃ i, BasinComponentFailureEvent record mapFitError envelopeError
        stateError i := by
  intro ω hfalse
  by_contra hno
  have hcomponent (i : BasinErrorComponent) :
      ω ∉ BasinComponentFailureEvent record mapFitError envelopeError
        stateError i := by
    intro hi
    exact hno (Set.mem_iUnion.2 ⟨i, hi⟩)
  have hmap : |mapFitError ω| ≤ (record ω).mapFitRadius := by
    exact le_of_not_gt (hcomponent .mapFit)
  have henvelope : |envelopeError ω| ≤ (record ω).envelopeRadius := by
    exact le_of_not_gt (hcomponent .envelope)
  have hstate : |stateError ω| ≤ (record ω).stateRadius := by
    exact le_of_not_gt (hcomponent .state)
  have hcoverage := basinScore_coverage_of_component_bounds
    (hdecomposition ω) hmap henvelope hstate
  have hpositive := basinClassification_positiveTruth hcoverage hfalse.1
  linarith [hfalse.2]

/-- Supplied component risk bounds give a finite-sample false-positive bound
for the fitted-basin classifier, with no independence assumption. -/
theorem basinClassificationFalsePositiveProbability_le_sum
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {record : Ω → BasinClassificationRecord}
    {trueScore : ℝ} {mapFitError envelopeError stateError : Ω → ℝ}
    (hdecomposition : ∀ ω,
      BasinScoreErrorDecomposition (record ω) trueScore
        (mapFitError ω) (envelopeError ω) (stateError ω))
    (budget : BasinErrorComponent → ENNReal)
    (hmarginal : ∀ i,
      μ (BasinComponentFailureEvent record mapFitError envelopeError
        stateError i) ≤ budget i) :
    μ (BasinClassificationFalsePositiveEvent record trueScore) ≤
      ∑ i, budget i := by
  exact CivicAlignment.PaperIII.falseVerdictProbability_le_sum_of_subset_failures
    (BasinComponentFailureEvent record mapFitError envelopeError stateError)
    budget
    (basinClassificationFalsePositive_subset_failureUnion hdecomposition)
    hmarginal

#print axioms basinScore_coverage_of_component_bounds
#print axioms basinClassification_positiveTruth
#print axioms basinClassificationFalsePositive_subset_failureUnion
#print axioms basinClassificationFalsePositiveProbability_le_sum

end

end CivicAlignment.PaperIV
