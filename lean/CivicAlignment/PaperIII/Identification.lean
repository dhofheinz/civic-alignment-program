/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.RateSeparation
import Mathlib.Analysis.Real.Sqrt

/-!
# Paper III: exact identification algebra

`prop:id` reports outcomes of a seed-pinned simulated panel, so the ledger
classifies the proposition itself as `NOT-A-THEOREM`.  This file formalizes the
deterministic algebra beneath that experiment: each noiseless moment relation
recovers its parameter, and exact parameter recovery preserves the certificate
margin.
-/

namespace CivicAlignment.PaperIII

noncomputable section

/-! ## Retirement and within-claim contraction -/

/-- The observed retirement rate from a count and its claim-period exposure. -/
def retirementRate (retirements exposure : ℝ) : ℝ :=
  retirements / exposure

/-- Exact expected retirements recover the grounding rate when exposure is nonzero. -/
theorem retirementRate_expected
    {lambda₀ exposure : ℝ} (hexposure : exposure ≠ 0) :
    retirementRate (lambda₀ * exposure) exposure = lambda₀ := by
  simp only [retirementRate]
  field_simp [hexposure]

/-- The unsquared within-claim contraction factor at a known policy. -/
def withinClaimContraction (η β : ℝ) : ℝ :=
  1 - η * (1 - β)

/-- One within-claim squared-deviation update. -/
def withinClaimSquaredStep (η β xSquared : ℝ) : ℝ :=
  withinClaimContraction η β ^ 2 * xSquared

/-- The noiseless contraction observation as a function of residual independence. -/
def contractionObservation (η residual : ℝ) : ℝ :=
  1 - η * residual

/-- The within-claim response is affine with slope `-η`. -/
theorem withinClaimContraction_eq_observation (η β : ℝ) :
    withinClaimContraction η β = contractionObservation η (1 - β) := by
  rfl

/-- Taking the square root of a positive squared-deviation ratio recovers the contraction. -/
theorem sqrt_withinClaimSquaredStep_ratio
    {η β xSquared : ℝ} (hxSquared : 0 < xSquared)
    (hcontraction : 0 ≤ withinClaimContraction η β) :
    Real.sqrt (withinClaimSquaredStep η β xSquared / xSquared) =
      withinClaimContraction η β := by
  have hratio : withinClaimSquaredStep η β xSquared / xSquared =
      withinClaimContraction η β ^ 2 := by
    simp only [withinClaimSquaredStep]
    field_simp [hxSquared.ne']
  rw [hratio, Real.sqrt_sq hcontraction]

/-- Negative two-point slope, the exact responsiveness estimator used by the panel. -/
def identifiedResponsiveness
    (residual₁ residual₂ ratio₁ ratio₂ : ℝ) : ℝ :=
  -(ratio₂ - ratio₁) / (residual₂ - residual₁)

/-- Two distinct noiseless contraction observations recover `η` exactly. -/
theorem identifiedResponsiveness_eq
    {η residual₁ residual₂ : ℝ} (hresidual : residual₁ ≠ residual₂) :
    identifiedResponsiveness residual₁ residual₂
        (contractionObservation η residual₁)
        (contractionObservation η residual₂) = η := by
  have hdenominator : residual₂ - residual₁ ≠ 0 := sub_ne_zero.mpr hresidual.symm
  simp only [identifiedResponsiveness, contractionObservation]
  field_simp [hdenominator]
  ring

/-! ## Affine arrival-channel recovery -/

/-- Conditional expected arrival mass from the scalar content channel. -/
def expectedArrivalMass (I₀ g laggedStock : ℝ) : ℝ :=
  I₀ + g * laggedStock

/-- Two-point slope estimator for the content gain. -/
def identifiedContentGain
    (stock₁ stock₂ mass₁ mass₂ : ℝ) : ℝ :=
  (mass₂ - mass₁) / (stock₂ - stock₁)

/-- Intercept estimator after recovering the content gain. -/
def identifiedBaselineArrival
    (stock₁ stock₂ mass₁ mass₂ : ℝ) : ℝ :=
  mass₁ - identifiedContentGain stock₁ stock₂ mass₁ mass₂ * stock₁

/-- Two distinct lagged stocks identify the affine content gain exactly. -/
theorem identifiedContentGain_eq
    {I₀ g stock₁ stock₂ : ℝ} (hstock : stock₁ ≠ stock₂) :
    identifiedContentGain stock₁ stock₂
        (expectedArrivalMass I₀ g stock₁)
        (expectedArrivalMass I₀ g stock₂) = g := by
  have hdenominator : stock₂ - stock₁ ≠ 0 := sub_ne_zero.mpr hstock.symm
  simp only [identifiedContentGain, expectedArrivalMass]
  field_simp [hdenominator]
  ring

/-- The matching intercept estimator recovers baseline arrivals exactly. -/
theorem identifiedBaselineArrival_eq
    {I₀ g stock₁ stock₂ : ℝ} (hstock : stock₁ ≠ stock₂) :
    identifiedBaselineArrival stock₁ stock₂
        (expectedArrivalMass I₀ g stock₁)
        (expectedArrivalMass I₀ g stock₂) = I₀ := by
  rw [identifiedBaselineArrival, identifiedContentGain_eq hstock]
  simp only [expectedArrivalMass]
  ring

/-- Values of an affine arrival channel at two distinct stocks identify both parameters. -/
theorem expectedArrivalMass_parameters_injective
    {I₀ g I₀' g' stock₁ stock₂ : ℝ} (hstock : stock₁ ≠ stock₂)
    (h₁ : expectedArrivalMass I₀ g stock₁ = expectedArrivalMass I₀' g' stock₁)
    (h₂ : expectedArrivalMass I₀ g stock₂ = expectedArrivalMass I₀' g' stock₂) :
    I₀ = I₀' ∧ g = g' := by
  have hgain : g = g' := by
    have hproduct : (g - g') * (stock₂ - stock₁) = 0 := by
      simp only [expectedArrivalMass] at h₁ h₂
      nlinarith
    rcases mul_eq_zero.mp hproduct with hgain | hstocks
    · exact sub_eq_zero.mp hgain
    · exact False.elim (hstock (sub_eq_zero.mp hstocks).symm)
  constructor
  · simp only [expectedArrivalMass, hgain] at h₁
    linarith
  · exact hgain

/-! ## Plug-in certificate margin -/

/-- The scalar certificate margin evaluated at a parameter tuple. -/
def estimatedCertificateMargin (v c lambda₀ g I₀ : ℝ) : ℝ :=
  v * (lambda₀ - g) - 2 * c * I₀

/-- Exact parameter recovery gives the exact certificate margin. -/
theorem estimatedCertificateMargin_eq
    {v c lambda₀ g I₀ lambdaHat gHat IHat : ℝ}
    (hlambda : lambdaHat = lambda₀) (hg : gHat = g) (hI : IHat = I₀) :
    estimatedCertificateMargin v c lambdaHat gHat IHat =
      estimatedCertificateMargin v c lambda₀ g I₀ := by
  subst lambdaHat
  subst gHat
  subst IHat
  rfl

/-- The exact, non-empirical content underlying `prop:id`. -/
structure IdentificationAlgebraConclusions
    (η lambda₀ I₀ g v c exposure residual₁ residual₂ stock₁ stock₂ : ℝ) : Prop where
  grounding_recovered : retirementRate (lambda₀ * exposure) exposure = lambda₀
  responsiveness_recovered :
    identifiedResponsiveness residual₁ residual₂
        (contractionObservation η residual₁)
        (contractionObservation η residual₂) = η
  gain_recovered :
    identifiedContentGain stock₁ stock₂
        (expectedArrivalMass I₀ g stock₁)
        (expectedArrivalMass I₀ g stock₂) = g
  baseline_recovered :
    identifiedBaselineArrival stock₁ stock₂
        (expectedArrivalMass I₀ g stock₁)
        (expectedArrivalMass I₀ g stock₂) = I₀
  margin_recovered :
    estimatedCertificateMargin v c lambda₀ g I₀ =
      v * (lambda₀ - g) - 2 * c * I₀

/--
Paper III, Numerical Result 8.1 (`prop:id`), `civic_loops.tex:668`: exact algebraic
core only.

Nonzero exposure, two distinct residual-independence values, and two distinct
lagged stocks identify `lambda₀`, `η`, `g`, and `I₀` from their noiseless
moment relations, and substitution recovers the certificate margin exactly.

The proposition itself reports finite-simulation errors, fitted RMSE slopes,
and `40/40` fate predictions. Those measurements are not propositions in Lean
and are documented as `NOT-A-THEOREM` in the ledgers.
-/
theorem identificationAlgebra
    {η lambda₀ I₀ g v c exposure residual₁ residual₂ stock₁ stock₂ : ℝ}
    (hexposure : exposure ≠ 0) (hresidual : residual₁ ≠ residual₂)
    (hstock : stock₁ ≠ stock₂) :
    IdentificationAlgebraConclusions
      η lambda₀ I₀ g v c exposure residual₁ residual₂ stock₁ stock₂ := by
  constructor
  · exact retirementRate_expected hexposure
  · exact identifiedResponsiveness_eq hresidual
  · exact identifiedContentGain_eq hstock
  · exact identifiedBaselineArrival_eq hstock
  · rfl

#print axioms retirementRate_expected
#print axioms withinClaimContraction_eq_observation
#print axioms sqrt_withinClaimSquaredStep_ratio
#print axioms identifiedResponsiveness_eq
#print axioms identifiedContentGain_eq
#print axioms identifiedBaselineArrival_eq
#print axioms expectedArrivalMass_parameters_injective
#print axioms estimatedCertificateMargin_eq
#print axioms identificationAlgebra

end

end CivicAlignment.PaperIII
