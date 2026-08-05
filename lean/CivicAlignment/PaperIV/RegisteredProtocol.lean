/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIV.DecisionRule
import CivicAlignment.PaperIII.FiveParameterMargin

/-!
# Paper IV: registered decisions, tier licensing, and clearance

`DecisionRule.lean` states the population-level conjunctions and their
conditional identification bridge.  This file adds the operational layer:
scoped audits, guarded one-sided tests, positive/negative/abstain decisions,
the strongest licensed tier, and supplementary C4-prime / clearance findings.

The tier function deliberately ignores the supplementary findings.  In
particular, capturability corroboration cannot substitute for the C4 basin
decision, and clearance is a separate positive finding rather than a tier.
-/

namespace CivicAlignment.PaperIV

open CivicAlignment.PaperIII

noncomputable section

/-- The deployment, domain, registered contested stream, and visited state
envelope to which an audit statement is scoped. -/
structure AuditScope
    (Deployment Domain Claim State : Type*) where
  deployment : Deployment
  domain : Domain
  contestedStream : Set Claim
  visitedEnvelope : Set State
  streamNonempty : contestedStream.Nonempty
  envelopeNonempty : visitedEnvelope.Nonempty

/-- Population premises attached to one explicit audit scope. -/
structure ScopedPopulationPremises
    {Deployment Domain Claim State : Type*}
    (scope : AuditScope Deployment Domain Claim State) where
  evidenceDilution : Prop
  satisfactionSelection : Prop
  capacityLoss : Prop
  harmfulFeedback : Prop
  capturedBasin : Prop
  laundering : Prop

/-- Forgetting the scope recovers the canonical six population premises. -/
def ScopedPopulationPremises.toPopulationPremises
    {Deployment Domain Claim State : Type*}
    {scope : AuditScope Deployment Domain Claim State}
    (p : ScopedPopulationPremises scope) : PopulationPremises where
  evidenceDilution := p.evidenceDilution
  satisfactionSelection := p.satisfactionSelection
  capacityLoss := p.capacityLoss
  harmfulFeedback := p.harmfulFeedback
  capturedBasin := p.capturedBasin
  laundering := p.laundering

/-- A registered test may establish, disconfirm, or fail to resolve a claim. -/
inductive RegisteredDecision where
  | positive
  | negative
  | abstain
  deriving DecidableEq, Repr

/-- Conjunction at the decision layer.  One disconfirmed component
disconfirms the conjunction; otherwise any unresolved component forces
abstention; only all-positive inputs establish it. -/
def RegisteredDecision.andDecision :
    RegisteredDecision → RegisteredDecision → RegisteredDecision
  | .negative, _ => .negative
  | _, .negative => .negative
  | .positive, .positive => .positive
  | _, _ => .abstain

@[simp] theorem RegisteredDecision.andDecision_eq_positive_iff
    (a b : RegisteredDecision) :
    a.andDecision b = .positive ↔ a = .positive ∧ b = .positive := by
  cases a <;> cases b <;> simp [RegisteredDecision.andDecision]

@[simp] theorem RegisteredDecision.andDecision_eq_negative_iff
    (a b : RegisteredDecision) :
    a.andDecision b = .negative ↔ a = .negative ∨ b = .negative := by
  cases a <;> cases b <;> simp [RegisteredDecision.andDecision]

/-- A deterministic registered prerequisite has no gray zone. -/
def RegisteredDecision.ofBool (b : Bool) : RegisteredDecision :=
  if b = true then .positive else .negative

/-- One registered one-sided statistic with an explicit radius and
specification/design guard. -/
structure RegisteredOneSidedTest where
  estimate : ℝ
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  guardPassed : Bool

/-- Positive above the radius, negative below its reflection, and abstaining
inside the gray zone or whenever the guard fails. -/
def RegisteredOneSidedTest.decision
    (t : RegisteredOneSidedTest) : RegisteredDecision :=
  if t.guardPassed = true then
    if t.radius < t.estimate then .positive
    else if t.estimate < -t.radius then .negative
    else .abstain
  else .abstain

@[simp] theorem RegisteredOneSidedTest.decision_eq_positive_iff
    (t : RegisteredOneSidedTest) :
    t.decision = .positive ↔
      t.guardPassed = true ∧ t.radius < t.estimate := by
  by_cases hg : t.guardPassed = true
  · by_cases hp : t.radius < t.estimate
    · simp [RegisteredOneSidedTest.decision, hg, hp]
    · by_cases hn : t.estimate < -t.radius <;>
        simp [RegisteredOneSidedTest.decision, hg, hp, hn]
  · simp [RegisteredOneSidedTest.decision, hg]

@[simp] theorem RegisteredOneSidedTest.decision_eq_negative_iff
    (t : RegisteredOneSidedTest) :
    t.decision = .negative ↔
      t.guardPassed = true ∧ t.estimate < -t.radius := by
  by_cases hg : t.guardPassed = true
  · by_cases hp : t.radius < t.estimate
    · have hn : ¬t.estimate < -t.radius := by
        linarith [t.radius_nonneg]
      simp [RegisteredOneSidedTest.decision, hg, hp, hn]
    · simp [RegisteredOneSidedTest.decision, hg, hp]
  · simp [RegisteredOneSidedTest.decision, hg]

/-- Construct the registered radius as a multiplier times a nonnegative
standard error. -/
def RegisteredOneSidedTest.ofStandardError
    (estimate standardError multiplier : ℝ)
    (hse : 0 ≤ standardError) (hmultiplier : 0 ≤ multiplier)
    (guardPassed : Bool) : RegisteredOneSidedTest where
  estimate := estimate
  radius := multiplier * standardError
  radius_nonneg := mul_nonneg hmultiplier hse
  guardPassed := guardPassed

/-- The audit statistics and hard design predicates from which C1--C5 are
assembled.  For `c5TelemetryBelow`, the registered estimate is
`threshold - telemetryWeight`, so a positive decision establishes that the
weight is below threshold. -/
structure RegisteredConditionTests where
  c1Dilution : RegisteredOneSidedTest
  c1ExposureBelowThreshold : Bool
  c1CovarianceRegime : Bool
  c2Selection : RegisteredOneSidedTest
  c3CapacityLoss : RegisteredOneSidedTest
  c4Manufacture : RegisteredOneSidedTest
  c4Ratchet : RegisteredOneSidedTest
  c4Basin : RegisteredDecision
  c5Decoupling : RegisteredOneSidedTest
  c5TelemetryBelow : RegisteredOneSidedTest
  c5RetentionIdentified : Bool

/-- The five condition-level decisions after registered component
conjunctions are applied. -/
structure RegisteredConditionDecisions where
  C1 : RegisteredDecision
  C2 : RegisteredDecision
  C3 : RegisteredDecision
  C4 : RegisteredDecision
  C5 : RegisteredDecision

/-- Assemble condition decisions exactly from the registered component tests. -/
def RegisteredConditionTests.decisions
    (t : RegisteredConditionTests) : RegisteredConditionDecisions where
  C1 := (t.c1Dilution.decision.andDecision
      (.ofBool t.c1ExposureBelowThreshold)).andDecision
        (.ofBool t.c1CovarianceRegime)
  C2 := t.c2Selection.decision
  C3 := t.c3CapacityLoss.decision
  C4 := (t.c4Manufacture.decision.andDecision
      t.c4Ratchet.decision).andDecision t.c4Basin
  C5 := (t.c5Decoupling.decision.andDecision
      t.c5TelemetryBelow.decision).andDecision
        (.ofBool t.c5RetentionIdentified)

/-- Interpret positive registered decisions as the five propositions used by
the population identification bridge. -/
def RegisteredConditionDecisions.toAuditConditions
    (c : RegisteredConditionDecisions) : AuditConditions where
  C1 := c.C1 = .positive
  C2 := c.C2 = .positive
  C3 := c.C3 = .positive
  C4 := c.C4 = .positive
  C5 := c.C5 = .positive

/-- Exact registered gate for the pressure tier. -/
def RegisteredConditionDecisions.pressureGate
    (c : RegisteredConditionDecisions) : Prop :=
  c.C1 = .positive ∧ c.C2 = .positive ∧ c.C3 = .positive

/-- Exact registered gate for the drift tier. -/
def RegisteredConditionDecisions.driftGate
    (c : RegisteredConditionDecisions) : Prop :=
  c.pressureGate ∧ c.C4 = .positive

/-- Exact registered gate for the capture tier. -/
def RegisteredConditionDecisions.captureGate
    (c : RegisteredConditionDecisions) : Prop :=
  c.driftGate ∧ c.C5 = .positive

/-- The strongest population tier licensed by the five registered decisions. -/
inductive LicensedTier where
  | none
  | pressure
  | drift
  | capture
  deriving DecidableEq, Repr

/-- Abstention or disconfirmation at a higher gate preserves any lower tier
whose own gate is fully positive. -/
def RegisteredConditionDecisions.licensedTier
    (c : RegisteredConditionDecisions) : LicensedTier :=
  match c.C1, c.C2, c.C3, c.C4, c.C5 with
  | .positive, .positive, .positive, .positive, .positive => .capture
  | .positive, .positive, .positive, .positive, _ => .drift
  | .positive, .positive, .positive, _, _ => .pressure
  | _, _, _, _, _ => .none

@[simp] theorem licensedTier_eq_capture_iff
    (c : RegisteredConditionDecisions) :
    c.licensedTier = .capture ↔ c.captureGate := by
  rcases c with ⟨c1, c2, c3, c4, c5⟩
  cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> cases c5 <;>
    simp [RegisteredConditionDecisions.licensedTier,
      RegisteredConditionDecisions.captureGate,
      RegisteredConditionDecisions.driftGate,
      RegisteredConditionDecisions.pressureGate]

@[simp] theorem licensedTier_eq_drift_iff
    (c : RegisteredConditionDecisions) :
    c.licensedTier = .drift ↔
      c.driftGate ∧ c.C5 ≠ .positive := by
  rcases c with ⟨c1, c2, c3, c4, c5⟩
  cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> cases c5 <;>
    simp [RegisteredConditionDecisions.licensedTier,
      RegisteredConditionDecisions.driftGate,
      RegisteredConditionDecisions.pressureGate]

@[simp] theorem licensedTier_eq_pressure_iff
    (c : RegisteredConditionDecisions) :
    c.licensedTier = .pressure ↔
      c.pressureGate ∧ c.C4 ≠ .positive := by
  rcases c with ⟨c1, c2, c3, c4, c5⟩
  cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> cases c5 <;>
    simp [RegisteredConditionDecisions.licensedTier,
      RegisteredConditionDecisions.pressureGate]

/-- No partial condition set can license capture. -/
theorem no_capture_without_full_gate
    (c : RegisteredConditionDecisions) (h : ¬c.captureGate) :
    c.licensedTier ≠ .capture := by
  intro htier
  exact h ((licensedTier_eq_capture_iff c).mp htier)

/-- Without the full C1--C4 gate, neither drift nor capture is licensed. -/
theorem no_drift_or_capture_without_drift_gate
    (c : RegisteredConditionDecisions) (h : ¬c.driftGate) :
    c.licensedTier ≠ .drift ∧ c.licensedTier ≠ .capture := by
  constructor
  · intro htier
    exact h ((licensedTier_eq_drift_iff c).mp htier).1
  · intro htier
    exact h ((licensedTier_eq_capture_iff c).mp htier).1

/-- Without the static C1--C3 gate, no population tier is licensed. -/
theorem licensedTier_eq_none_of_not_pressureGate
    (c : RegisteredConditionDecisions) (h : ¬c.pressureGate) :
    c.licensedTier = .none := by
  rcases c with ⟨c1, c2, c3, c4, c5⟩
  cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> cases c5 <;>
    simp_all [RegisteredConditionDecisions.licensedTier,
      RegisteredConditionDecisions.pressureGate]

/-- A registered pressure tier is sound under the population identification
bridges. -/
theorem licensedPressure_sound
    {c : RegisteredConditionDecisions} {p : PopulationPremises}
    (identified : AuditIdentification c.toAuditConditions p)
    (htier : c.licensedTier = .pressure) :
    CivicPressure p := by
  have hgate := (licensedTier_eq_pressure_iff c).mp htier
  exact pressureVerdict_sound identified hgate.1

/-- A registered drift tier is sound under the population identification
bridges. -/
theorem licensedDrift_sound
    {c : RegisteredConditionDecisions} {p : PopulationPremises}
    (identified : AuditIdentification c.toAuditConditions p)
    (htier : c.licensedTier = .drift) :
    CivicDrift p := by
  have hgate := (licensedTier_eq_drift_iff c).mp htier
  exact driftVerdict_sound identified hgate.1

/-- A registered capture tier is sound whenever the six population
identification bridges hold. -/
theorem licensedCapture_sound
    {c : RegisteredConditionDecisions} {p : PopulationPremises}
    (identified : AuditIdentification c.toAuditConditions p)
    (htier : c.licensedTier = .capture) :
    CivicCapture p := by
  have hgate := (licensedTier_eq_capture_iff c).mp htier
  exact captureVerdict_sound identified hgate

/-- Registered C4-prime capturability corroboration. -/
structure C4PrimeRecord where
  gainMinusGrounding : RegisteredOneSidedTest

def C4PrimeRecord.decision (r : C4PrimeRecord) : RegisteredDecision :=
  r.gainMinusGrounding.decision

/-- Registered clearance uses the five-parameter plug-in margin, an explicit
radius, and the specification guard. -/
structure ClearanceRecord where
  estimate : FiveParameterMarginPoint
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  specificationGuardPassed : Bool

def ClearanceRecord.test (r : ClearanceRecord) : RegisteredOneSidedTest where
  estimate := fiveParameterMargin r.estimate
  radius := r.radius
  radius_nonneg := r.radius_nonneg
  guardPassed := r.specificationGuardPassed

def ClearanceRecord.decision (r : ClearanceRecord) : RegisteredDecision :=
  r.test.decision

/-- The model bridge from a positive true margin to absence of capture on the
visited operating envelope. -/
structure ClearanceIdentification
    (truth : FiveParameterMarginPoint)
    (noCaptureOnVisitedEnvelope : Prop) : Prop where
  positiveMargin_noCapture :
    0 < fiveParameterMargin truth → noCaptureOnVisitedEnvelope

/-- A positive registered clearance is exactly sound on its coverage event
and under the certificate model bridge. -/
theorem registeredClearance_sound
    {truth : FiveParameterMarginPoint} {record : ClearanceRecord}
    {noCaptureOnVisitedEnvelope : Prop}
    (hcoverage :
      FiveParameterCoverageEvent truth record.estimate record.radius)
    (identified :
      ClearanceIdentification truth noCaptureOnVisitedEnvelope)
    (hpositive : record.decision = .positive) :
    noCaptureOnVisitedEnvelope := by
  have htest :=
    (RegisteredOneSidedTest.decision_eq_positive_iff record.test).mp hpositive
  apply identified.positiveMargin_noCapture
  exact fiveParameterSafeSideCertificate_sound hcoverage htest.2

/-- Complete registered output.  C4-prime and clearance are reported beside,
not inside, the pressure--drift--capture tier. -/
structure RegisteredAuditRecord where
  conditions : RegisteredConditionDecisions
  c4Prime : C4PrimeRecord
  clearance : ClearanceRecord

def RegisteredAuditRecord.tier (r : RegisteredAuditRecord) : LicensedTier :=
  r.conditions.licensedTier

/-- Supplementary findings cannot substitute for a missing tier condition. -/
theorem tier_independent_of_supplementary
    (conditions : RegisteredConditionDecisions)
    (c4Prime₁ c4Prime₂ : C4PrimeRecord)
    (clearance₁ clearance₂ : ClearanceRecord) :
    (RegisteredAuditRecord.mk conditions c4Prime₁ clearance₁).tier =
      (RegisteredAuditRecord.mk conditions c4Prime₂ clearance₂).tier := rfl

#print axioms no_capture_without_full_gate
#print axioms no_drift_or_capture_without_drift_gate
#print axioms licensedTier_eq_none_of_not_pressureGate
#print axioms licensedPressure_sound
#print axioms licensedDrift_sound
#print axioms licensedCapture_sound
#print axioms registeredClearance_sound
#print axioms tier_independent_of_supplementary

end

end CivicAlignment.PaperIV
