/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.Identification

/-!
# Paper III: exact finite-sample identification sensitivity

The simulation statements in `prop:id` remain empirical.  This file proves a
different, deterministic claim: for arbitrary finite-sample moment errors, the
identification errors are exactly the displayed error contrasts divided by the
registered design spreads.  No distribution, independence, unbiasedness, or
large-sample approximation is assumed.
-/

namespace CivicAlignment.PaperIII

noncomputable section

/-! ## Exact error identities -/

/-- An additive retirement-count error is divided by total exposure exactly. -/
theorem retirementRate_add_error_sub
    {lambda₀ exposure retirementError : ℝ} (hexposure : exposure ≠ 0) :
    retirementRate (lambda₀ * exposure + retirementError) exposure - lambda₀ =
      retirementError / exposure := by
  simp only [retirementRate]
  field_simp [hexposure]
  ring

/-- Two noisy contraction moments identify `η` up to their error contrast over
the residual-independence spread. -/
theorem identifiedResponsiveness_add_errors_sub
    {η residual₁ residual₂ error₁ error₂ : ℝ}
    (hresidual : residual₁ ≠ residual₂) :
    identifiedResponsiveness residual₁ residual₂
        (contractionObservation η residual₁ + error₁)
        (contractionObservation η residual₂ + error₂) - η =
      -(error₂ - error₁) / (residual₂ - residual₁) := by
  have hdenominator : residual₂ - residual₁ ≠ 0 :=
    sub_ne_zero.mpr hresidual.symm
  simp only [identifiedResponsiveness, contractionObservation]
  field_simp [hdenominator]
  ring

/-- Two noisy arrival moments identify `g` up to their error contrast over the
lagged-stock spread. -/
theorem identifiedContentGain_add_errors_sub
    {I₀ g stock₁ stock₂ error₁ error₂ : ℝ} (hstock : stock₁ ≠ stock₂) :
    identifiedContentGain stock₁ stock₂
        (expectedArrivalMass I₀ g stock₁ + error₁)
        (expectedArrivalMass I₀ g stock₂ + error₂) - g =
      (error₂ - error₁) / (stock₂ - stock₁) := by
  have hdenominator : stock₂ - stock₁ ≠ 0 := sub_ne_zero.mpr hstock.symm
  simp only [identifiedContentGain, expectedArrivalMass]
  field_simp [hdenominator]
  ring

/-- The matching noisy intercept error is the first moment error minus the
stock leverage times the slope error. -/
theorem identifiedBaselineArrival_add_errors_sub
    {I₀ g stock₁ stock₂ error₁ error₂ : ℝ} (hstock : stock₁ ≠ stock₂) :
    identifiedBaselineArrival stock₁ stock₂
        (expectedArrivalMass I₀ g stock₁ + error₁)
        (expectedArrivalMass I₀ g stock₂ + error₂) - I₀ =
      error₁ - stock₁ * ((error₂ - error₁) / (stock₂ - stock₁)) := by
  have hdenominator : stock₂ - stock₁ ≠ 0 := sub_ne_zero.mpr hstock.symm
  simp only [identifiedBaselineArrival, identifiedContentGain,
    expectedArrivalMass]
  field_simp [hdenominator]
  ring

/-! ## Design-conditioned deterministic bounds -/

/-- A two-moment error contrast is bounded by the sum of the two absolute
errors, divided by the absolute design spread. -/
theorem abs_errorContrast_div_le
    (error₁ error₂ spread : ℝ) :
    |(error₂ - error₁) / spread| ≤
      (|error₁| + |error₂|) / |spread| := by
  by_cases hspread : spread = 0
  · simp [hspread]
  · rw [abs_div]
    have hspreadPos : 0 < |spread| := abs_pos.mpr hspread
    apply (div_le_div_iff_of_pos_right hspreadPos).2
    simpa [add_comm] using abs_sub error₂ error₁

/-- Finite-sample responsiveness sensitivity is inversely proportional to the
registered residual-independence spread. -/
theorem identifiedResponsiveness_error_le
    {η residual₁ residual₂ error₁ error₂ : ℝ}
    (hresidual : residual₁ ≠ residual₂) :
    |identifiedResponsiveness residual₁ residual₂
        (contractionObservation η residual₁ + error₁)
        (contractionObservation η residual₂ + error₂) - η| ≤
      (|error₁| + |error₂|) / |residual₂ - residual₁| := by
  rw [identifiedResponsiveness_add_errors_sub hresidual]
  simpa only [abs_div, abs_neg] using
    abs_errorContrast_div_le error₁ error₂ (residual₂ - residual₁)

/-- Finite-sample content-gain sensitivity is inversely proportional to the
registered lagged-stock spread. -/
theorem identifiedContentGain_error_le
    {I₀ g stock₁ stock₂ error₁ error₂ : ℝ} (hstock : stock₁ ≠ stock₂) :
    |identifiedContentGain stock₁ stock₂
        (expectedArrivalMass I₀ g stock₁ + error₁)
        (expectedArrivalMass I₀ g stock₂ + error₂) - g| ≤
      (|error₁| + |error₂|) / |stock₂ - stock₁| := by
  rw [identifiedContentGain_add_errors_sub hstock]
  exact abs_errorContrast_div_le error₁ error₂ (stock₂ - stock₁)

/-- For fixed `v,c`, arbitrary errors in the three loop parameters perturb the
plug-in margin by exactly one linear contrast. -/
theorem estimatedCertificateMargin_add_errors_sub
    (v c lambda₀ g I₀ lambdaError gainError arrivalError : ℝ) :
    estimatedCertificateMargin v c
        (lambda₀ + lambdaError) (g + gainError) (I₀ + arrivalError) -
      estimatedCertificateMargin v c lambda₀ g I₀ =
        v * (lambdaError - gainError) - 2 * c * arrivalError := by
  simp only [estimatedCertificateMargin]
  ring

/-- A deterministic finite-sample envelope for the fixed-`v,c` plug-in margin.
It assumes only coordinatewise error magnitudes. -/
theorem estimatedCertificateMargin_error_le
    (v c lambda₀ g I₀ lambdaError gainError arrivalError : ℝ) :
    |estimatedCertificateMargin v c
        (lambda₀ + lambdaError) (g + gainError) (I₀ + arrivalError) -
      estimatedCertificateMargin v c lambda₀ g I₀| ≤
        |v| * (|lambdaError| + |gainError|) +
          2 * |c| * |arrivalError| := by
  rw [estimatedCertificateMargin_add_errors_sub]
  calc
    |v * (lambdaError - gainError) - 2 * c * arrivalError| ≤
        |v * (lambdaError - gainError)| + |2 * c * arrivalError| :=
      abs_sub _ _
    _ = |v| * |lambdaError - gainError| +
        2 * |c| * |arrivalError| := by
      simp only [abs_mul]
      norm_num
    _ ≤ |v| * (|lambdaError| + |gainError|) +
        2 * |c| * |arrivalError| := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (abs_sub lambdaError gainError)
          (abs_nonneg v)) le_rfl

/-- The exact deterministic finite-sample layer beneath `prop:id`. -/
structure FiniteSampleIdentificationConclusions
    (η lambda₀ I₀ g v c exposure residual₁ residual₂ stock₁ stock₂
      retirementError responseError₁ responseError₂
      arrivalError₁ arrivalError₂ : ℝ) : Prop where
  retirement_error :
    retirementRate (lambda₀ * exposure + retirementError) exposure - lambda₀ =
      retirementError / exposure
  responsiveness_error :
    identifiedResponsiveness residual₁ residual₂
        (contractionObservation η residual₁ + responseError₁)
        (contractionObservation η residual₂ + responseError₂) - η =
      -(responseError₂ - responseError₁) / (residual₂ - residual₁)
  gain_error :
    identifiedContentGain stock₁ stock₂
        (expectedArrivalMass I₀ g stock₁ + arrivalError₁)
        (expectedArrivalMass I₀ g stock₂ + arrivalError₂) - g =
      (arrivalError₂ - arrivalError₁) / (stock₂ - stock₁)
  baseline_error :
    identifiedBaselineArrival stock₁ stock₂
        (expectedArrivalMass I₀ g stock₁ + arrivalError₁)
        (expectedArrivalMass I₀ g stock₂ + arrivalError₂) - I₀ =
      arrivalError₁ - stock₁ *
        ((arrivalError₂ - arrivalError₁) / (stock₂ - stock₁))

/-- Exact finite-sample identification sensitivity under nondegenerate design. -/
theorem finiteSampleIdentification
    {η lambda₀ I₀ g v c exposure residual₁ residual₂ stock₁ stock₂
      retirementError responseError₁ responseError₂
      arrivalError₁ arrivalError₂ : ℝ}
    (hexposure : exposure ≠ 0) (hresidual : residual₁ ≠ residual₂)
    (hstock : stock₁ ≠ stock₂) :
    FiniteSampleIdentificationConclusions
      η lambda₀ I₀ g v c exposure residual₁ residual₂ stock₁ stock₂
      retirementError responseError₁ responseError₂
      arrivalError₁ arrivalError₂ := by
  constructor
  · exact retirementRate_add_error_sub hexposure
  · exact identifiedResponsiveness_add_errors_sub hresidual
  · exact identifiedContentGain_add_errors_sub hstock
  · exact identifiedBaselineArrival_add_errors_sub hstock

#print axioms retirementRate_add_error_sub
#print axioms identifiedResponsiveness_add_errors_sub
#print axioms identifiedContentGain_add_errors_sub
#print axioms identifiedBaselineArrival_add_errors_sub
#print axioms abs_errorContrast_div_le
#print axioms identifiedResponsiveness_error_le
#print axioms identifiedContentGain_error_le
#print axioms estimatedCertificateMargin_add_errors_sub
#print axioms estimatedCertificateMargin_error_le
#print axioms finiteSampleIdentification

end

end CivicAlignment.PaperIII
