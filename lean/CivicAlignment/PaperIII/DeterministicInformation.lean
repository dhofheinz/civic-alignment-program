/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.Observability
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Paper III: zero information for the deterministic captured-face channel

For a finite hidden-state distribution and a finite quantization of a
deterministic sensor, mutual information equals the Shannon entropy of the
sensor output.  This file defines that quantity and proves it is zero when the
sensor is constant.  The captured-face invariance theorem supplies exactly
that constancy for every finite quantization of satisfaction telemetry.

This is not a noisy-channel or continuous differential-entropy theorem.
-/

namespace CivicAlignment.PaperIII

open scoped BigOperators

noncomputable section

/-- A finite probability mass function. -/
structure FiniteProbabilityMass (X : Type*) [Fintype X] where
  mass : X → ℝ
  nonnegative : ∀ x, 0 ≤ mass x
  normalized : ∑ x, mass x = 1

/-- Probability mass induced on a finite deterministic sensor output. -/
def deterministicOutputMass
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (p : FiniteProbabilityMass X) (sensor : X → Y) (y : Y) : ℝ :=
  ∑ x with sensor x = y, p.mass x

/-- Shannon entropy summand, with the standard `0 log 0 = 0` convention. -/
def shannonEntropySummand (q : ℝ) : ℝ :=
  if q = 0 then 0 else -q * (Real.log q / Real.log 2)

/-- For a deterministic finite channel, mutual information between hidden
state and output is the Shannon entropy of the induced output mass. -/
def deterministicSensorInformation
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (p : FiniteProbabilityMass X) (sensor : X → Y) : ℝ :=
  ∑ y, shannonEntropySummand (deterministicOutputMass p sensor y)

/-- A constant deterministic sensor induces a point mass. -/
theorem deterministicOutputMass_of_constant
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (p : FiniteProbabilityMass X) {sensor : X → Y} {y₀ y : Y}
    (hconstant : ∀ x, sensor x = y₀) :
    deterministicOutputMass p sensor y = if y₀ = y then 1 else 0 := by
  classical
  by_cases hy : y₀ = y
  · subst y
    simp [deterministicOutputMass, hconstant, p.normalized]
  · simp [deterministicOutputMass, hconstant, hy]

/-- A constant finite deterministic channel carries exactly zero bits. -/
theorem deterministicSensorInformation_eq_zero_of_constant
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (p : FiniteProbabilityMass X) {sensor : X → Y} {y₀ : Y}
    (hconstant : ∀ x, sensor x = y₀) :
    deterministicSensorInformation p sensor = 0 := by
  classical
  rw [deterministicSensorInformation]
  apply Finset.sum_eq_zero
  intro y _hy
  rw [deterministicOutputMass_of_constant p hconstant]
  by_cases houtput : y₀ = y
  · simp [houtput, shannonEntropySummand]
  · simp [houtput, shannonEntropySummand]

/-- Any finite quantization of satisfaction telemetry has zero deterministic
information about a finite hidden low-coordinate state at every captured-face
horizon. -/
theorem capturedSatisfaction_zero_deterministic_information
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (p : FiniteProbabilityMass X) (lowCoordinate : X → ℝ)
    (quantize : ℝ → Y)
    (piH kappa aH injectionH aL injectionL xH : ℝ) (t : ℕ) :
    deterministicSensorInformation p
      (fun x ↦ quantize
        (capturedSatisfaction piH kappa
          ((capturedFaceMap aH injectionH aL injectionL)^[t]
            (xH, lowCoordinate x)))) = 0 := by
  apply deterministicSensorInformation_eq_zero_of_constant p
    (y₀ := quantize
      (healthySatisfaction piH kappa
        ((affineCoordinateStep aH injectionH)^[t] xH)))
  intro x
  rw [capturedSatisfaction_iterate_eq_healthy]

#print axioms deterministicOutputMass_of_constant
#print axioms deterministicSensorInformation_eq_zero_of_constant
#print axioms capturedSatisfaction_zero_deterministic_information

end


end CivicAlignment.PaperIII
