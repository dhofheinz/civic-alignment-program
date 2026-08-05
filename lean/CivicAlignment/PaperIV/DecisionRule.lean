/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.SafeSide

/-!
# Paper IV: canonical tier predicates and conditional verdict soundness

The audit conditions are statistical decisions; the tier definitions are
population-level claims.  This file keeps those layers distinct.  A verdict is
sound only through an explicit identification bridge mapping each accepted
condition to the corresponding population premise.
-/

namespace CivicAlignment.PaperIV

/-- Population-level premises used by the pressure--drift--capture ladder.
`capturedBasin` is deliberately separate from the full capture predicate. -/
structure PopulationPremises where
  evidenceDilution : Prop
  satisfactionSelection : Prop
  capacityLoss : Prop
  harmfulFeedback : Prop
  capturedBasin : Prop
  laundering : Prop

/-- Civic misalignment pressure is the static three-premise conjunction. -/
def CivicPressure (p : PopulationPremises) : Prop :=
  p.evidenceDilution ∧ p.satisfactionSelection ∧ p.capacityLoss

/-- Civic drift adds harmful operator--population feedback to pressure. -/
def CivicDrift (p : PopulationPremises) : Prop :=
  CivicPressure p ∧ p.harmfulFeedback

/-- Civic capture adds captured-side basin membership and laundering to drift.
Basin membership alone is therefore not the full capture verdict. -/
def CivicCapture (p : PopulationPremises) : Prop :=
  CivicDrift p ∧ p.capturedBasin ∧ p.laundering

/-- The five registered audit conditions, kept at the decision layer. -/
structure AuditConditions where
  C1 : Prop
  C2 : Prop
  C3 : Prop
  C4 : Prop
  C5 : Prop

/-- C1--C3 are the pressure verdict gate. -/
def PressureVerdict (c : AuditConditions) : Prop :=
  c.C1 ∧ c.C2 ∧ c.C3

/-- C1--C4 are the drift verdict gate. -/
def DriftVerdict (c : AuditConditions) : Prop :=
  PressureVerdict c ∧ c.C4

/-- C1--C5 are the capture verdict gate. -/
def CaptureVerdict (c : AuditConditions) : Prop :=
  DriftVerdict c ∧ c.C5

/-- Identification assumptions connecting accepted statistical conditions to
the population-level premises they purport to establish.  C4 has two distinct
obligations: harmful feedback and captured-side basin membership. -/
structure AuditIdentification
    (c : AuditConditions) (p : PopulationPremises) : Prop where
  c1_dilution : c.C1 → p.evidenceDilution
  c2_selection : c.C2 → p.satisfactionSelection
  c3_capacity : c.C3 → p.capacityLoss
  c4_feedback : c.C4 → p.harmfulFeedback
  c4_basin : c.C4 → p.capturedBasin
  c5_laundering : c.C5 → p.laundering

/-- Conditional soundness of the pressure verdict. -/
theorem pressureVerdict_sound
    {c : AuditConditions} {p : PopulationPremises}
    (identified : AuditIdentification c p) (h : PressureVerdict c) :
    CivicPressure p := by
  exact ⟨identified.c1_dilution h.1,
    identified.c2_selection h.2.1,
    identified.c3_capacity h.2.2⟩

/-- Conditional soundness of the drift verdict. -/
theorem driftVerdict_sound
    {c : AuditConditions} {p : PopulationPremises}
    (identified : AuditIdentification c p) (h : DriftVerdict c) :
    CivicDrift p := by
  exact ⟨pressureVerdict_sound identified h.1,
    identified.c4_feedback h.2⟩

/-- Conditional soundness of the full capture verdict. -/
theorem captureVerdict_sound
    {c : AuditConditions} {p : PopulationPremises}
    (identified : AuditIdentification c p) (h : CaptureVerdict c) :
    CivicCapture p := by
  exact ⟨driftVerdict_sound identified h.1,
    identified.c4_basin h.1.2,
    identified.c5_laundering h.2⟩

/-- Capture contains drift as a logical prerequisite. -/
theorem civicCapture_implies_civicDrift
    {p : PopulationPremises} (h : CivicCapture p) : CivicDrift p :=
  h.1

/-- Drift contains pressure as a logical prerequisite. -/
theorem civicDrift_implies_civicPressure
    {p : PopulationPremises} (h : CivicDrift p) : CivicPressure p :=
  h.1

#print axioms pressureVerdict_sound
#print axioms driftVerdict_sound
#print axioms captureVerdict_sound

end CivicAlignment.PaperIV
