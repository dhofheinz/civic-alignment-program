/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.Identification
import Mathlib.Probability.Moments.Variance

/-!
# Paper III: exact margin variance and safe-side algebra

This file formalizes the exact half of `prop:safe`.  Independence of the
retirement-rate estimate from the *joint* OLS pair is preserved by the linear
margin map, while covariance within that pair remains.  The resulting variance
identity is exact for square-integrable random variables.

Delta-method asymptotics, the normal-tail approximation, and finite battery
counts are documented separately and are not promoted to Lean theorems.
-/

namespace CivicAlignment.PaperIII

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*}

/-- The random plug-in certificate margin. -/
def randomCertificateMargin
    (v c : ℝ) (lambdaHat gHat IHat : Ω → ℝ) (ω : Ω) : ℝ :=
  v * (lambdaHat ω - gHat ω) - 2 * c * IHat ω

/-- The part of the random margin determined by the joint OLS pair. -/
def olsMarginContribution
    (v c : ℝ) (gHat IHat : Ω → ℝ) (ω : Ω) : ℝ :=
  (-v) * gHat ω + (-2 * c) * IHat ω

/-- The random margin splits into the independent retirement and OLS slices. -/
theorem randomCertificateMargin_eq_add
    (v c : ℝ) (lambdaHat gHat IHat : Ω → ℝ) :
    randomCertificateMargin v c lambdaHat gHat IHat =
      fun ω ↦ v * lambdaHat ω + olsMarginContribution v c gHat IHat ω := by
  funext ω
  simp only [randomCertificateMargin, olsMarginContribution]
  ring

variable [MeasurableSpace Ω] {μ : Measure Ω}

/-- The exact variance of the correlated two-coordinate OLS contribution. -/
theorem olsMarginContribution_variance
    [IsFiniteMeasure μ] (v c : ℝ) {gHat IHat : Ω → ℝ}
    (hg : MemLp gHat 2 μ) (hI : MemLp IHat 2 μ) :
    Var[olsMarginContribution v c gHat IHat; μ] =
      v ^ 2 * Var[gHat; μ] + 4 * c ^ 2 * Var[IHat; μ] +
        4 * v * c * cov[gHat, IHat; μ] := by
  have hgScaled : MemLp (fun ω ↦ (-v) * gHat ω) 2 μ := hg.const_mul (-v)
  have hIScaled : MemLp (fun ω ↦ (-2 * c) * IHat ω) 2 μ := hI.const_mul (-2 * c)
  rw [show olsMarginContribution v c gHat IHat =
      fun ω ↦ (-v) * gHat ω + (-2 * c) * IHat ω by rfl]
  rw [variance_fun_add hgScaled hIScaled, variance_const_mul,
    variance_const_mul, covariance_const_mul_left, covariance_const_mul_right]
  ring

/-- Independence from the joint OLS pair implies independence from its linear contribution. -/
theorem indepFun_scaledRetirement_olsContribution
    (v c : ℝ) {lambdaHat gHat IHat : Ω → ℝ}
    (hindep : lambdaHat ⟂ᵢ[μ] fun ω ↦ (gHat ω, IHat ω)) :
    (fun ω ↦ v * lambdaHat ω) ⟂ᵢ[μ] olsMarginContribution v c gHat IHat := by
  have hcomp := hindep.comp
    (show Measurable (fun x : ℝ ↦ v * x) by fun_prop)
    (show Measurable (fun p : ℝ × ℝ ↦ (-v) * p.1 + (-2 * c) * p.2) by fun_prop)
  convert hcomp using 1 <;> ext ω <;>
    simp only [Function.comp_apply, olsMarginContribution]

/--
Paper III, Proposition 8.2 (`prop:safe`), `civic_loops.tex:696`: exact variance
identity.

If the retirement-rate estimate is independent of the joint OLS pair and all
three estimators are square-integrable, then the plug-in margin has exactly the
variance displayed in the paper.  The covariance between the OLS slope and
intercept remains with its positive `4vc` coefficient.
-/
theorem safeSideMarginVariance
    [IsProbabilityMeasure μ] (v c : ℝ) {lambdaHat gHat IHat : Ω → ℝ}
    (hlambda : MemLp lambdaHat 2 μ) (hg : MemLp gHat 2 μ)
    (hI : MemLp IHat 2 μ)
    (hindep : lambdaHat ⟂ᵢ[μ] fun ω ↦ (gHat ω, IHat ω)) :
    Var[randomCertificateMargin v c lambdaHat gHat IHat; μ] =
      v ^ 2 * (Var[lambdaHat; μ] + Var[gHat; μ]) +
        4 * c ^ 2 * Var[IHat; μ] + 4 * v * c * cov[gHat, IHat; μ] := by
  have hlambdaScaled : MemLp (fun ω ↦ v * lambdaHat ω) 2 μ :=
    hlambda.const_mul v
  have hOls : MemLp (olsMarginContribution v c gHat IHat) 2 μ := by
    exact (hg.const_mul (-v)).add (hI.const_mul (-2 * c))
  have hscaledIndep :=
    indepFun_scaledRetirement_olsContribution v c hindep
  rw [randomCertificateMargin_eq_add]
  rw [hscaledIndep.variance_fun_add hlambdaScaled hOls,
    variance_const_mul, olsMarginContribution_variance v c hg hI]
  ring

/-! ## Deterministic meaning of the safe-side threshold -/

/-- A positive two-standard-error lower bound implies a positive point estimate. -/
theorem safeSideRule_estimatedMargin_pos
    {marginEstimate standardError : ℝ} (hse : 0 ≤ standardError)
    (hcertify : 0 < marginEstimate - 2 * standardError) :
    0 < marginEstimate := by
  linarith

/-- If the true error lies inside the two-SE band, certification implies a positive true margin. -/
theorem safeSideRule_sound_of_error_bound
    {trueMargin marginEstimate standardError : ℝ}
    (herror : |marginEstimate - trueMargin| ≤ 2 * standardError)
    (hcertify : 0 < marginEstimate - 2 * standardError) :
    0 < trueMargin := by
  have hupper : marginEstimate - trueMargin ≤ 2 * standardError :=
    (abs_le.mp herror).2
  linarith

/-- The exact, machine-checked portion of `prop:safe`. -/
structure SafeSideExactConclusions
    (v c : ℝ) (lambdaHat gHat IHat : Ω → ℝ) (μ : Measure Ω) : Prop where
  variance_identity :
    Var[randomCertificateMargin v c lambdaHat gHat IHat; μ] =
      v ^ 2 * (Var[lambdaHat; μ] + Var[gHat; μ]) +
        4 * c ^ 2 * Var[IHat; μ] + 4 * v * c * cov[gHat, IHat; μ]
  deterministic_rule : ∀ {trueMargin marginEstimate standardError : ℝ},
    |marginEstimate - trueMargin| ≤ 2 * standardError →
      0 < marginEstimate - 2 * standardError → 0 < trueMargin

/-- The variance identity and deterministic safe-side implication packaged together. -/
theorem safeSideExact
    [IsProbabilityMeasure μ] (v c : ℝ) {lambdaHat gHat IHat : Ω → ℝ}
    (hlambda : MemLp lambdaHat 2 μ) (hg : MemLp gHat 2 μ)
    (hI : MemLp IHat 2 μ)
    (hindep : lambdaHat ⟂ᵢ[μ] fun ω ↦ (gHat ω, IHat ω)) :
    SafeSideExactConclusions v c lambdaHat gHat IHat μ := by
  constructor
  · exact safeSideMarginVariance v c hlambda hg hI hindep
  · intro trueMargin marginEstimate standardError herror hcertify
    exact safeSideRule_sound_of_error_bound herror hcertify

#print axioms randomCertificateMargin_eq_add
#print axioms olsMarginContribution_variance
#print axioms indepFun_scaledRetirement_olsContribution
#print axioms safeSideMarginVariance
#print axioms safeSideRule_estimatedMargin_pos
#print axioms safeSideRule_sound_of_error_bound
#print axioms safeSideExact

end


end CivicAlignment.PaperIII
