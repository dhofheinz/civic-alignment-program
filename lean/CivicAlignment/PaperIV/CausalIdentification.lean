/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIV.IdentificationBridges

/-!
# Paper IV: causal-identification obligation interfaces

This file does not prove that a deployment satisfies causal assumptions.  It
types the assumptions that the pulse and survivorship modules must report and
checks only their logical composition into the corresponding non-scalar
positive-side truths.
-/

namespace CivicAlignment.PaperIV

/-! ## Pulse-based basin identification -/

/-- The registered pulse, delivered pulse, observed trajectory, and resulting
three-valued basin classification. -/
structure PulseBasinExperiment (Pulse Trajectory : Type*) where
  assignedPulse : Pulse
  deliveredPulse : Pulse
  observedTrajectory : Trajectory
  basinDecision : RegisteredDecision

/-- Explicit causal assumptions for reading a positive pulse response as
captured-side basin membership.

`potentialResponse` describes the audited system, while `stableResponse`
describes the response in the registered target period.  The final field is
the exclusion/construct bridge: the registered response signature must be
specific to captured-side basin membership on the stated scope. -/
structure PulseBasinIdentification
    {Pulse Trajectory : Type*}
    (experiment : PulseBasinExperiment Pulse Trajectory)
    (potentialResponse stableResponse : Pulse → Trajectory)
    (responseSignature : Trajectory → Prop)
    (capturedBasinTruth : Prop) : Prop where
  interventionFidelity :
    experiment.deliveredPulse = experiment.assignedPulse
  consistency :
    experiment.observedTrajectory =
      potentialResponse experiment.deliveredPulse
  temporalStability :
    potentialResponse experiment.assignedPulse =
      stableResponse experiment.assignedPulse
  outcomeObservable :
    experiment.basinDecision = .positive →
      responseSignature experiment.observedTrajectory
  noRelevantDirectPathway :
    responseSignature (stableResponse experiment.assignedPulse) →
      capturedBasinTruth

/-- A positive pulse classification implies the latent basin truth only after
intervention fidelity, consistency, temporal stability, observability, and the
exclusion/construct bridge have all been supplied. -/
theorem pulseBasin_positive_implies_truth
    {Pulse Trajectory : Type*}
    {experiment : PulseBasinExperiment Pulse Trajectory}
    {potentialResponse stableResponse : Pulse → Trajectory}
    {responseSignature : Trajectory → Prop}
    {capturedBasinTruth : Prop}
    (identified : PulseBasinIdentification experiment potentialResponse
      stableResponse responseSignature capturedBasinTruth)
    (hpositive : experiment.basinDecision = .positive) :
    capturedBasinTruth := by
  apply identified.noRelevantDirectPathway
  rw [← identified.temporalStability, ← identified.interventionFidelity,
    ← identified.consistency]
  exact identified.outcomeObservable hpositive

/-- The pulse assumptions produce exactly the positive-side classification
event required by the non-scalar Paper IV coverage interface. -/
theorem pulseBasin_nonScalarCoverage
    {Pulse Trajectory : Type*}
    {tests : RegisteredConditionTests}
    {experiment : PulseBasinExperiment Pulse Trajectory}
    {potentialResponse stableResponse : Pulse → Trajectory}
    {responseSignature : Trajectory → Prop}
    {capturedBasinTruth : Prop}
    (hregistered : experiment.basinDecision = tests.c4Basin)
    (identified : PulseBasinIdentification experiment potentialResponse
      stableResponse responseSignature capturedBasinTruth) :
    tests.c4Basin = .positive → capturedBasinTruth := by
  intro hpositive
  apply pulseBasin_positive_implies_truth identified
  rw [hregistered]
  exact hpositive

/-! ## Survivorship and IPW identification -/

/-- The causal and measurement premises that a survivorship analysis may need
to validate.  They are propositions so their deployment-specific content can
be supplied by the registered protocol rather than hidden in a Boolean. -/
structure SurvivorshipPremises where
  consistency : Prop
  conditionalExchangeability : Prop
  positivity : Prop
  outcomeModelCorrect : Prop
  censoringModelCorrect : Prop
  censoringTimeRegistered : Prop
  retainedMeasurementSucceeded : Prop
  uncertaintyPropagated : Prop

/-- Evidence that all required survivorship premises hold, allowing either a
correct outcome model or a correct censoring model for a registered
double-robust analysis. -/
structure SurvivorshipPremisesValidated
    (p : SurvivorshipPremises) : Prop where
  consistency : p.consistency
  conditionalExchangeability : p.conditionalExchangeability
  positivity : p.positivity
  nuisanceValidity : p.outcomeModelCorrect ∨ p.censoringModelCorrect
  censoringTimeRegistered : p.censoringTimeRegistered
  retainedMeasurementSucceeded : p.retainedMeasurementSucceeded
  uncertaintyPropagated : p.uncertaintyPropagated

/-- The remaining statistical/causal bridge from validated premises to the
latent statement that the retention design identifies its target contrast. -/
structure SurvivorshipIdentification
    (p : SurvivorshipPremises) (retentionDesignValid : Prop) : Prop where
  validatedPremises_identify :
    SurvivorshipPremisesValidated p → retentionDesignValid

/-- Validated premises and the explicit identification bridge imply the
latent retention-design truth. -/
theorem retentionDesignValid_of_survivorshipAssumptions
    {p : SurvivorshipPremises} {retentionDesignValid : Prop}
    (validated : SurvivorshipPremisesValidated p)
    (identified : SurvivorshipIdentification p retentionDesignValid) :
    retentionDesignValid :=
  identified.validatedPremises_identify validated

/-- A registered positive retention Boolean has positive-side validity only
when its validation record and causal identification bridge are supplied. -/
theorem retention_nonScalarCoverage
    {tests : RegisteredConditionTests}
    {p : SurvivorshipPremises} {retentionDesignValid : Prop}
    (validationOnPositive :
      tests.c5RetentionIdentified = true →
        SurvivorshipPremisesValidated p)
    (identified : SurvivorshipIdentification p retentionDesignValid) :
    tests.c5RetentionIdentified = true → retentionDesignValid := by
  intro hpositive
  exact retentionDesignValid_of_survivorshipAssumptions
    (validationOnPositive hpositive) identified

#print axioms pulseBasin_positive_implies_truth
#print axioms pulseBasin_nonScalarCoverage
#print axioms retentionDesignValid_of_survivorshipAssumptions
#print axioms retention_nonScalarCoverage

end CivicAlignment.PaperIV
