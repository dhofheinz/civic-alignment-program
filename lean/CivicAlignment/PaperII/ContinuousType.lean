/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperI.Manipulability
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.Variance

/-!
# Continuous literacy types

This file begins Paper II's continuous-type extension. The first result is the
pointwise affine decomposition of each type's updated mean; the later covariance
results use its intercept and slope as random variables over the type space.
-/

namespace CivicAlignment.PaperII

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

/-- Effective deference for a continuous type with extraction rate `e`. -/
def continuousEffectiveDeference (e β : ℝ) : ℝ :=
  (1 - e) * β

/-- Evidence weight for a continuous type. -/
def continuousEvidenceWeight (η e β : ℝ) : ℝ :=
  η * (1 - continuousEffectiveDeference e β)

/-- The de-anchoring rate `r(τ)=η(τ)(1-e(τ))`. -/
def deanchoringRate (η e : ℝ) : ℝ :=
  η * (1 - e)

/-- Updated type mean after weighting the prior mean against the common signal. -/
def continuousUpdatedMean (η e μ m β : ℝ) : ℝ :=
  (1 - continuousEvidenceWeight η e β) * μ +
    continuousEvidenceWeight η e β * m

/-- The affine intercept `Aτ=(1-ητ)(μτ-m)`. -/
def meanAffineIntercept (η μ m : ℝ) : ℝ :=
  (1 - η) * (μ - m)

/-- The affine slope `Bτ=rτ(μτ-m)`. -/
def meanAffineSlope (η e μ m : ℝ) : ℝ :=
  deanchoringRate η e * (μ - m)

/-- The residual prior weight is affine in deference. -/
theorem one_sub_continuousEvidenceWeight (η e β : ℝ) :
    1 - continuousEvidenceWeight η e β =
      (1 - η) + deanchoringRate η e * β := by
  simp only [continuousEvidenceWeight, continuousEffectiveDeference, deanchoringRate]
  ring

/--
Paper II, Lemma 4.1 (`lem:affine`), `civic_drift.tex:741`.

For every literacy type, the displacement of its updated mean from the common
signal is affine in deference, with the paper's exact intercept `Aτ` and slope
`Bτ`.
-/
theorem affineMeanDynamics (η e μ m β : ℝ) :
    continuousUpdatedMean η e μ m β - m =
      meanAffineIntercept η μ m + meanAffineSlope η e μ m * β := by
  rw [continuousUpdatedMean, one_sub_continuousEvidenceWeight]
  simp only [continuousEvidenceWeight, continuousEffectiveDeference,
    meanAffineIntercept, meanAffineSlope, deanchoringRate]
  ring

/-! ## Between-type dispersion -/

/-- The affine displacement path `Aτ+Bτβ` from `lem:affine`. -/
def affineMeanPath {T : Type*} (A B : T → ℝ) (β : ℝ) (τ : T) : ℝ :=
  A τ + B τ * β

/-- Between-type dispersion of the affine mean path. -/
def affineDispersion {T : Type*} [MeasurableSpace T]
    (π : Measure T) (A B : T → ℝ) (β : ℝ) : ℝ :=
  Var[affineMeanPath A B β; π]

/-- The explicit quadratic appearing on the right of `eq:Squad`. -/
def dispersionQuadratic {T : Type*} [MeasurableSpace T]
    (π : Measure T) (A B : T → ℝ) (β : ℝ) : ℝ :=
  Var[A; π] + 2 * cov[A, B; π] * β + Var[B; π] * β ^ 2

/-- Bilinearity of covariance gives the exact variance expansion. -/
theorem affineDispersion_eq_quadratic {T : Type*} [MeasurableSpace T]
    (π : Measure T) [IsProbabilityMeasure π] {A B : T → ℝ}
    (hA : MemLp A 2 π) (hB : MemLp B 2 π) (β : ℝ) :
    affineDispersion π A B β = dispersionQuadratic π A B β := by
  have hBβ : MemLp (fun τ ↦ B τ * β) 2 π := hB.mul_const β
  change Var[(fun τ ↦ A τ + B τ * β); π] =
    Var[A; π] + 2 * cov[A, B; π] * β + Var[B; π] * β ^ 2
  rw [variance_fun_add hA hBβ, covariance_mul_const_right,
    variance_mul_const]
  ring

/-- The dispersion polynomial is convex because its leading coefficient is a variance. -/
theorem dispersionQuadratic_convex {T : Type*} [MeasurableSpace T]
    (π : Measure T) (A B : T → ℝ) :
    ConvexOn ℝ univ (dispersionQuadratic π A B) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hb_eq : b = 1 - a := by linarith
  subst b
  simp only [dispersionQuadratic, smul_eq_mul]
  have hvariance : 0 ≤ Var[B; π] := variance_nonneg B π
  have hgap : 0 ≤ a * (1 - a) * Var[B; π] * (x - y) ^ 2 := by positivity
  nlinarith [hgap]

/-- The covariance sign is the exact frontier for monotonicity on the policy interval. -/
theorem dispersionQuadratic_monotoneOn_iff {T : Type*} [MeasurableSpace T]
    (π : Measure T) (A B : T → ℝ) :
    MonotoneOn (dispersionQuadratic π A B) (Icc (0 : ℝ) 1) ↔
      0 ≤ cov[A, B; π] := by
  let cAB : ℝ := cov[A, B; π]
  let vB : ℝ := Var[B; π]
  change MonotoneOn
      (fun β ↦ Var[A; π] + 2 * cAB * β + vB * β ^ 2) (Icc (0 : ℝ) 1) ↔
    0 ≤ cAB
  have hvB : 0 ≤ vB := by
    dsimp only [vB]
    exact variance_nonneg B π
  constructor
  · intro hmono
    by_contra hcov
    have hcAB : cAB < 0 := lt_of_not_ge hcov
    by_cases hvBzero : vB = 0
    · have h01 := hmono (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
        (show (1 : ℝ) ∈ Icc 0 1 by norm_num) zero_le_one
      simp only [hvBzero, mul_zero, zero_mul, pow_two] at h01
      linarith
    · have hvBpos : 0 < vB := lt_of_le_of_ne hvB (Ne.symm hvBzero)
      let z : ℝ := min 1 ((-cAB) / vB)
      have hzpos : 0 < z := by
        dsimp only [z]
        exact lt_min zero_lt_one (div_pos (neg_pos.mpr hcAB) hvBpos)
      have hzleone : z ≤ 1 := min_le_left _ _
      have hzlediv : z ≤ (-cAB) / vB := min_le_right _ _
      have hvBz : vB * z ≤ -cAB := by
        have := (le_div_iff₀ hvBpos).mp hzlediv
        simpa only [mul_comm] using this
      have hfactor : 2 * cAB + vB * z < 0 := by linarith
      have hproduct : z * (2 * cAB + vB * z) < 0 :=
        mul_neg_of_pos_of_neg hzpos hfactor
      have h0z := hmono (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
        ⟨hzpos.le, hzleone⟩ hzpos.le
      norm_num at h0z
      nlinarith [hproduct]
  · intro hcov x hx y hy hxy
    have hgap : 0 ≤ y - x := sub_nonneg.mpr hxy
    have hsum : 0 ≤ x + y := by linarith [hx.1, hy.1]
    have hlinear : 0 ≤ 2 * cAB * (y - x) := by positivity
    have hquadratic : 0 ≤ vB * (y - x) * (x + y) := by positivity
    nlinarith [hlinear, hquadratic]

/-- Negative covariance forces strict dispersion reversal on a nontrivial initial interval. -/
theorem dispersionQuadratic_strictAntiOn_initial_of_covariance_neg
    {T : Type*} [MeasurableSpace T] (π : Measure T) (A B : T → ℝ)
    (hcov : cov[A, B; π] < 0) :
    ∃ ε : ℝ, 0 < ε ∧
      StrictAntiOn (dispersionQuadratic π A B) (Icc (0 : ℝ) ε) := by
  let cAB : ℝ := cov[A, B; π]
  let vB : ℝ := Var[B; π]
  have hcAB : cAB < 0 := by simpa only [cAB] using hcov
  have hvB : 0 ≤ vB := by
    dsimp only [vB]
    exact variance_nonneg B π
  by_cases hvBzero : vB = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx y hy hxy
    change Var[A; π] + 2 * cAB * y + vB * y ^ 2 <
      Var[A; π] + 2 * cAB * x + vB * x ^ 2
    rw [hvBzero]
    simp only [zero_mul, add_zero]
    nlinarith
  · have hvBpos : 0 < vB := lt_of_le_of_ne hvB (Ne.symm hvBzero)
    let ε : ℝ := min 1 ((-cAB) / (2 * vB))
    have hratio : 0 < (-cAB) / (2 * vB) :=
      div_pos (neg_pos.mpr hcAB) (mul_pos two_pos hvBpos)
    have hεpos : 0 < ε := by
      dsimp only [ε]
      exact lt_min zero_lt_one hratio
    refine ⟨ε, hεpos, ?_⟩
    intro x hx y hy hxy
    have hεle : ε ≤ (-cAB) / (2 * vB) := min_le_right _ _
    have hscaledε : 2 * vB * ε ≤ -cAB := by
      have := (le_div_iff₀ (mul_pos two_pos hvBpos)).mp hεle
      simpa only [mul_comm] using this
    have hsum : x + y ≤ 2 * ε := by linarith [hx.2, hy.2]
    have hscaledSum : vB * (x + y) ≤ 2 * vB * ε := by
      nlinarith [mul_nonneg hvB (sub_nonneg.mpr hsum)]
    have hfactor : 2 * cAB + vB * (x + y) < 0 := by linarith
    have hproduct : (y - x) * (2 * cAB + vB * (x + y)) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr hxy) hfactor
    change Var[A; π] + 2 * cAB * y + vB * y ^ 2 <
      Var[A; π] + 2 * cAB * x + vB * x ^ 2
    nlinarith [hproduct]

/-- The actual updated mean is the common signal plus its affine displacement. -/
theorem continuousUpdatedMean_eq_signal_add_affine (η e μ m β : ℝ) :
    continuousUpdatedMean η e μ m β =
      m + meanAffineIntercept η μ m + meanAffineSlope η e μ m * β := by
  linarith [affineMeanDynamics η e μ m β]

/-- The exact quadratic also computes the variance of the paper's updated mean path. -/
theorem continuousUpdatedMean_variance_eq_quadratic
    {T : Type*} [MeasurableSpace T] (π : Measure T) [IsProbabilityMeasure π]
    (η e μ : T → ℝ) (m β : ℝ)
    (hA : MemLp (fun τ ↦ meanAffineIntercept (η τ) (μ τ) m) 2 π)
    (hB : MemLp (fun τ ↦ meanAffineSlope (η τ) (e τ) (μ τ) m) 2 π) :
    Var[(fun τ ↦ continuousUpdatedMean (η τ) (e τ) (μ τ) m β); π] =
      dispersionQuadratic π
        (fun τ ↦ meanAffineIntercept (η τ) (μ τ) m)
        (fun τ ↦ meanAffineSlope (η τ) (e τ) (μ τ) m) β := by
  let A : T → ℝ := fun τ ↦ meanAffineIntercept (η τ) (μ τ) m
  let B : T → ℝ := fun τ ↦ meanAffineSlope (η τ) (e τ) (μ τ) m
  have hpath :
      (fun τ ↦ continuousUpdatedMean (η τ) (e τ) (μ τ) m β) =
        fun τ ↦ m + (A τ + B τ * β) := by
    funext τ
    simp only [A, B]
    rw [continuousUpdatedMean_eq_signal_add_affine]
    ring
  have hA' : MemLp A 2 π := by simpa only [A] using hA
  have hB' : MemLp B 2 π := by simpa only [B] using hB
  rw [hpath]
  have hshift : Var[(fun τ ↦ m + (A τ + B τ * β)); π] =
      Var[(fun τ ↦ A τ + B τ * β); π] := by
    simpa only using variance_const_add
      (X := fun τ ↦ A τ + B τ * β)
      (hA'.add (hB'.mul_const β)).aestronglyMeasurable m
  rw [hshift]
  change affineDispersion π A B β = dispersionQuadratic π A B β
  exact affineDispersion_eq_quadratic π hA' hB' β

/-- The four claims packaged by Paper II's explicit-quadratic proposition. -/
structure StratificationQuadraticConclusions
    {T : Type*} [MeasurableSpace T] (π : Measure T) (A B : T → ℝ) : Prop where
  exact_formula : ∀ β, affineDispersion π A B β = dispersionQuadratic π A B β
  convex : ConvexOn ℝ univ (affineDispersion π A B)
  monotone_iff_covariance_nonnegative :
    MonotoneOn (affineDispersion π A B) (Icc (0 : ℝ) 1) ↔ 0 ≤ cov[A, B; π]
  strictly_decreases_initially_of_covariance_neg : cov[A, B; π] < 0 →
    ∃ ε : ℝ, 0 < ε ∧ StrictAntiOn (affineDispersion π A B) (Icc (0 : ℝ) ε)

/--
Paper II, Proposition 4.2 (`prop:quad`), `civic_drift.tex:748`.

Between-type dispersion is the stated convex quadratic. Its restriction to the
policy interval is nondecreasing exactly when `Covπ(A,B)≥0`; negative covariance
forces strict decrease on a nontrivial initial interval.
-/
theorem stratificationExplicitQuadratic
    {T : Type*} [MeasurableSpace T] (π : Measure T) [IsProbabilityMeasure π]
    {A B : T → ℝ} (hA : MemLp A 2 π) (hB : MemLp B 2 π) :
    StratificationQuadraticConclusions π A B := by
  have hexact : ∀ β, affineDispersion π A B β = dispersionQuadratic π A B β :=
    affineDispersion_eq_quadratic π hA hB
  refine
    { exact_formula := hexact
      convex := (dispersionQuadratic_convex π A B).congr
        (fun β _ ↦ (hexact β).symm)
      monotone_iff_covariance_nonnegative := ?_
      strictly_decreases_initially_of_covariance_neg := ?_ }
  · constructor
    · intro hmono
      apply (dispersionQuadratic_monotoneOn_iff π A B).mp
      intro x hx y hy hxy
      rw [← hexact x, ← hexact y]
      exact hmono hx hy hxy
    · intro hcov
      have hmono := (dispersionQuadratic_monotoneOn_iff π A B).mpr hcov
      intro x hx y hy hxy
      rw [hexact x, hexact y]
      exact hmono hx hy hxy
  · intro hcov
    obtain ⟨ε, hε, hanti⟩ :=
      dispersionQuadratic_strictAntiOn_initial_of_covariance_neg π A B hcov
    refine ⟨ε, hε, ?_⟩
    intro x hx y hy hxy
    rw [hexact x, hexact y]
    exact hanti hx hy hxy

/-! ## Sufficient conditions for the covariance frontier -/

/-- Two functions are comonotone when every pair of their increments has the same weak sign. -/
def Comonotone {T : Type*} (A B : T → ℝ) : Prop :=
  ∀ x y, 0 ≤ (A x - A y) * (B x - B y)

/-- Assumption 4.3 (`ass:cov`): the affine intercept and slope have nonnegative covariance. -/
structure GeneralizedContestedClaimCondition
    {T : Type*} [MeasurableSpace T] (π : Measure T) (A B : T → ℝ) : Prop where
  covariance_nonnegative : 0 ≤ cov[A, B; π]

/-- The independent-copy identity underlying Chebyshev's association inequality. -/
theorem integral_pairwiseDifference_eq_two_mul_covariance
    {T : Type*} [MeasurableSpace T] (π : Measure T) [IsProbabilityMeasure π]
    {A B : T → ℝ} (hA : MemLp A 2 π) (hB : MemLp B 2 π) :
    (∫ z : T × T, (A z.1 - A z.2) * (B z.1 - B z.2) ∂π.prod π) =
      2 * cov[A, B; π] := by
  have hAint : Integrable A π := hA.integrable (by norm_num)
  have hBint : Integrable B π := hB.integrable (by norm_num)
  have hAB : Integrable (fun τ ↦ A τ * B τ) π := hA.integrable_mul hB
  have h11 : Integrable (fun z : T × T ↦ A z.1 * B z.1) (π.prod π) :=
    hAB.comp_fst π
  have h12 : Integrable (fun z : T × T ↦ A z.1 * B z.2) (π.prod π) :=
    hAint.mul_prod hBint
  have h21 : Integrable (fun z : T × T ↦ B z.1 * A z.2) (π.prod π) :=
    hBint.mul_prod hAint
  have h22 : Integrable (fun z : T × T ↦ A z.2 * B z.2) (π.prod π) :=
    hAB.comp_snd π
  have hsub12 :
      (∫ z : T × T, A z.1 * B z.1 - A z.1 * B z.2 ∂π.prod π) =
        (∫ z : T × T, A z.1 * B z.1 ∂π.prod π) -
          ∫ z : T × T, A z.1 * B z.2 ∂π.prod π := by
    simpa only [Pi.sub_apply] using integral_sub h11 h12
  have hsub123 :
      (∫ z : T × T, A z.1 * B z.1 - A z.1 * B z.2 - B z.1 * A z.2 ∂π.prod π) =
        (∫ z : T × T, A z.1 * B z.1 - A z.1 * B z.2 ∂π.prod π) -
          ∫ z : T × T, B z.1 * A z.2 ∂π.prod π := by
    simpa only [Pi.sub_apply] using integral_sub (h11.sub h12) h21
  have hInt11 :
      (∫ z : T × T, A z.1 * B z.1 ∂π.prod π) = ∫ τ, A τ * B τ ∂π := by
    simpa only [probReal_univ, one_smul] using
      integral_fun_fst (μ := π) (ν := π) (fun τ ↦ A τ * B τ)
  have hInt12 :
      (∫ z : T × T, A z.1 * B z.2 ∂π.prod π) = π[A] * π[B] := by
    exact integral_prod_mul A B
  have hInt21 :
      (∫ z : T × T, B z.1 * A z.2 ∂π.prod π) = π[B] * π[A] := by
    exact integral_prod_mul B A
  have hInt22 :
      (∫ z : T × T, A z.2 * B z.2 ∂π.prod π) = ∫ τ, A τ * B τ ∂π := by
    simpa only [probReal_univ, one_smul] using
      integral_fun_snd (μ := π) (ν := π) (fun τ ↦ A τ * B τ)
  rw [show (fun z : T × T ↦ (A z.1 - A z.2) * (B z.1 - B z.2)) =
      fun z ↦ A z.1 * B z.1 - A z.1 * B z.2 - B z.1 * A z.2 +
        A z.2 * B z.2 by
    funext z
    ring]
  calc
    (∫ z : T × T, A z.1 * B z.1 - A z.1 * B z.2 - B z.1 * A z.2 +
        A z.2 * B z.2 ∂π.prod π) =
        (∫ z : T × T, A z.1 * B z.1 - A z.1 * B z.2 - B z.1 * A z.2 ∂π.prod π) +
          ∫ z : T × T, A z.2 * B z.2 ∂π.prod π := by
      simpa only [Pi.add_apply, Pi.sub_apply] using
        integral_add ((h11.sub h12).sub h21) h22
    _ = ((∫ z : T × T, A z.1 * B z.1 ∂π.prod π) -
          (∫ z : T × T, A z.1 * B z.2 ∂π.prod π) -
          (∫ z : T × T, B z.1 * A z.2 ∂π.prod π)) +
          ∫ z : T × T, A z.2 * B z.2 ∂π.prod π := by
      rw [hsub123, hsub12]
    _ = 2 * cov[A, B; π] := by
      rw [hInt11, hInt12, hInt21, hInt22]
      rw [covariance_eq_sub hA hB]
      simp only [Pi.mul_apply]
      ring

/-- Chebyshev's association inequality for square-integrable comonotone functions. -/
theorem covariance_nonneg_of_comonotone
    {T : Type*} [MeasurableSpace T] (π : Measure T) [IsProbabilityMeasure π]
    {A B : T → ℝ} (hA : MemLp A 2 π) (hB : MemLp B 2 π)
    (hcomonotone : Comonotone A B) :
    0 ≤ cov[A, B; π] := by
  have hpair :
      0 ≤ ∫ z : T × T, (A z.1 - A z.2) * (B z.1 - B z.2) ∂π.prod π :=
    integral_nonneg fun z ↦ hcomonotone z.1 z.2
  rw [integral_pairwiseDifference_eq_two_mul_covariance π hA hB] at hpair
  linarith

/-- Comonotonicity implies the generalized contested-claim condition. -/
theorem generalizedContestedClaimCondition_of_comonotone
    {T : Type*} [MeasurableSpace T] (π : Measure T) [IsProbabilityMeasure π]
    {A B : T → ℝ} (hA : MemLp A 2 π) (hB : MemLp B 2 π)
    (hcomonotone : Comonotone A B) :
    GeneralizedContestedClaimCondition π A B :=
  ⟨covariance_nonneg_of_comonotone π hA hB hcomonotone⟩

/--
On a two-point straddle, the affine intercepts are weakly ordered and the
slopes are strictly ordered.
-/
theorem twoPointStraddle_affine_order
    (η e μ : Fin 2 → ℝ) (m : ℝ)
    (hη : ∀ i, η i ∈ Ioc (0 : ℝ) 1)
    (he : ∀ i, e i ∈ Ico (0 : ℝ) 1)
    (hμ₀ : μ 0 < m) (hμ₁ : m < μ 1) :
    meanAffineIntercept (η 0) (μ 0) m ≤ meanAffineIntercept (η 1) (μ 1) m ∧
      meanAffineSlope (η 0) (e 0) (μ 0) m <
        meanAffineSlope (η 1) (e 1) (μ 1) m := by
  have hA₀ : meanAffineIntercept (η 0) (μ 0) m ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos
    · exact sub_nonneg.mpr (hη 0).2
    · exact sub_nonpos.mpr hμ₀.le
  have hA₁ : 0 ≤ meanAffineIntercept (η 1) (μ 1) m := by
    apply mul_nonneg
    · exact sub_nonneg.mpr (hη 1).2
    · exact sub_nonneg.mpr hμ₁.le
  have hr₀ : 0 < deanchoringRate (η 0) (e 0) :=
    mul_pos (hη 0).1 (sub_pos.mpr (he 0).2)
  have hr₁ : 0 < deanchoringRate (η 1) (e 1) :=
    mul_pos (hη 1).1 (sub_pos.mpr (he 1).2)
  have hB₀ : meanAffineSlope (η 0) (e 0) (μ 0) m < 0 :=
    mul_neg_of_pos_of_neg hr₀ (sub_neg.mpr hμ₀)
  have hB₁ : 0 < meanAffineSlope (η 1) (e 1) (μ 1) m :=
    mul_pos hr₁ (sub_pos.mpr hμ₁)
  exact ⟨hA₀.trans hA₁, hB₀.trans hB₁⟩

/-- The affine intercept and slope are comonotone on every two-point straddle. -/
theorem twoPointStraddle_comonotone
    (η e μ : Fin 2 → ℝ) (m : ℝ)
    (hη : ∀ i, η i ∈ Ioc (0 : ℝ) 1)
    (he : ∀ i, e i ∈ Ico (0 : ℝ) 1)
    (hμ₀ : μ 0 < m) (hμ₁ : m < μ 1) :
    Comonotone
      (fun i ↦ meanAffineIntercept (η i) (μ i) m)
      (fun i ↦ meanAffineSlope (η i) (e i) (μ i) m) := by
  obtain ⟨hA, hB⟩ := twoPointStraddle_affine_order η e μ m hη he hμ₀ hμ₁
  intro i j
  fin_cases i <;> fin_cases j
  · simp
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hA) (sub_nonpos.mpr hB.le)
  · exact mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB.le)
  · simp

/-- A two-point straddle satisfies the generalized covariance condition. -/
theorem generalizedContestedClaimCondition_of_twoPointStraddle
    (π : Measure (Fin 2)) [IsProbabilityMeasure π]
    (η e μ : Fin 2 → ℝ) (m : ℝ)
    (hη : ∀ i, η i ∈ Ioc (0 : ℝ) 1)
    (he : ∀ i, e i ∈ Ico (0 : ℝ) 1)
    (hμ₀ : μ 0 < m) (hμ₁ : m < μ 1) :
    GeneralizedContestedClaimCondition π
      (fun i ↦ meanAffineIntercept (η i) (μ i) m)
      (fun i ↦ meanAffineSlope (η i) (e i) (μ i) m) := by
  apply generalizedContestedClaimCondition_of_comonotone π MemLp.of_discrete MemLp.of_discrete
  exact twoPointStraddle_comonotone η e μ m hη he hμ₀ hμ₁

universe u

/-- The two alternative sufficient conditions asserted by Paper II, Proposition 4. -/
structure ContestedClaimSufficientConditions : Prop where
  two_point_straddle :
    ∀ (π : Measure (Fin 2)) [IsProbabilityMeasure π]
      (η e μ : Fin 2 → ℝ) (m : ℝ),
      (∀ i, η i ∈ Ioc (0 : ℝ) 1) →
      (∀ i, e i ∈ Ico (0 : ℝ) 1) →
      μ 0 < m → m < μ 1 →
      GeneralizedContestedClaimCondition π
        (fun i ↦ meanAffineIntercept (η i) (μ i) m)
        (fun i ↦ meanAffineSlope (η i) (e i) (μ i) m)
  comonotonicity :
    ∀ {T : Type u} [MeasurableSpace T] (π : Measure T) [IsProbabilityMeasure π]
      {A B : T → ℝ}, MemLp A 2 π → MemLp B 2 π → Comonotone A B →
      GeneralizedContestedClaimCondition π A B

/--
Paper II, Proposition 4.4 (`prop:suff`), `civic_drift.tex:763`.

The generalized contested-claim covariance condition follows either from the
paper's two-point straddle or from comonotonicity. The background primitive
bounds `η∈(0,1]` and `e∈[0,1)` make the two-point de-anchoring rate positive at
both points, hence imply the proposition's weaker “positive somewhere” clause.
-/
theorem contestedClaimSufficientConditions : ContestedClaimSufficientConditions := by
  constructor
  · exact generalizedContestedClaimCondition_of_twoPointStraddle
  · exact generalizedContestedClaimCondition_of_comonotone

/-! ## Continuous-type harm -/

/-- A type's one-step MSE along its continuous-type evidence-weight path. -/
def continuousTypeMSE {T : Type*} (δm : ℝ) (δ γ η e : T → ℝ)
    (β : ℝ) (τ : T) : ℝ :=
  PaperI.typeMSE (δ τ) δm (γ τ) (η τ) (1 - e τ) β

/-- Population accuracy loss in Paper II, Theorem `thm:contA`. -/
noncomputable def continuousAccuracyLoss {T : Type*} [MeasurableSpace T]
    (π : Measure T) (δm : ℝ) (δ γ η e : T → ℝ) (β : ℝ) : ℝ :=
  ∫ τ, continuousTypeMSE δm δ γ η e β τ ∂π

/-- Continuous-type version of Paper I's within-type fragmentation term. -/
noncomputable def continuousWithinTypeDispersion {T : Type*} [MeasurableSpace T]
    (π : Measure T) (η e σ2 : T → ℝ) (β : ℝ) : ℝ :=
  ∫ τ, PaperI.residualVarianceFactor (η τ) (1 - e τ) β * σ2 τ ∂π

/-- Between-type dispersion of the updated type means. -/
noncomputable def continuousStratification {T : Type*} [MeasurableSpace T]
    (π : Measure T) (η e μ : T → ℝ) (m β : ℝ) : ℝ :=
  affineDispersion π
    (fun τ ↦ meanAffineIntercept (η τ) (μ τ) m)
    (fun τ ↦ meanAffineSlope (η τ) (e τ) (μ τ) m) β

/-- Paper II's continuous-type collective epistemic capacity. -/
noncomputable def continuousCollectiveCapacity {T : Type*} [MeasurableSpace T]
    (π : Measure T) (δm : ℝ) (δ γ η e μ σ2 : T → ℝ)
    (m lambda nu β : ℝ) : ℝ :=
  -continuousAccuracyLoss π δm δ γ η e β -
    lambda * continuousWithinTypeDispersion π η e σ2 β -
    nu * continuousStratification π η e μ m β

/-- The typewise MSE derivative `mg(τ;β)` from `def:hic`. -/
def continuousMarginalHarm {T : Type*} (δm : ℝ) (δ γ η e : T → ℝ)
    (β : ℝ) (τ : T) : ℝ :=
  2 * deanchoringRate (η τ) (e τ) *
    PaperI.marginalHarmBracket (δ τ) δm (γ τ) (η τ) (1 - e τ) β

/-- Constant coefficient of the typewise MSE polynomial in `β`. -/
def continuousMSEIntercept {T : Type*} (δm : ℝ) (δ γ η : T → ℝ)
    (τ : T) : ℝ :=
  PaperI.mseQuadratic (δ τ) δm (γ τ) (η τ)

/-- Linear coefficient of the typewise MSE polynomial in `β`. -/
def continuousMSELinearCoefficient {T : Type*} (δm : ℝ)
    (δ γ η e : T → ℝ) (τ : T) : ℝ :=
  2 * deanchoringRate (η τ) (e τ) *
    ((δ τ - γ τ) - η τ * (δ τ + δm - 2 * γ τ))

/-- Quadratic coefficient of the typewise MSE polynomial in `β`. -/
def continuousMSEQuadraticCoefficient {T : Type*} (δm : ℝ)
    (δ γ η e : T → ℝ) (τ : T) : ℝ :=
  deanchoringRate (η τ) (e τ) ^ 2 * (δ τ + δm - 2 * γ τ)

/--
The measurable bounded primitives and almost-everywhere conditions used by
Paper II, Theorem `thm:contA`. `MemLp · ⊤` is the Lean encoding of the
section's measurability and essential-boundedness assumptions.
-/
structure ContinuousTypeHarmAssumptions {T : Type*} [MeasurableSpace T]
    (π : Measure T) (δm : ℝ) (δ γ η e μ σ2 : T → ℝ) (m : ℝ) : Prop where
  delta_memLp : MemLp δ ⊤ π
  gamma_memLp : MemLp γ ⊤ π
  responsiveness_memLp : MemLp η ⊤ π
  extraction_memLp : MemLp e ⊤ π
  mean_memLp : MemLp μ ⊤ π
  variance_memLp : MemLp σ2 ⊤ π
  evidence_error_nonnegative : 0 ≤ δm
  type_error_nonnegative : ∀ᵐ τ ∂π, 0 ≤ δ τ
  correlation_nonnegative : ∀ᵐ τ ∂π, 0 ≤ γ τ
  correlation_bound : ∀ᵐ τ ∂π, γ τ ≤ √(δm * δ τ)
  evidence_advantage : ∀ᵐ τ ∂π, δm < δ τ
  responsiveness_range : ∀ᵐ τ ∂π, η τ ∈ Ioc (0 : ℝ) 1
  extraction_range : ∀ᵐ τ ∂π, e τ ∈ Ico (0 : ℝ) 1
  variance_nonnegative : ∀ᵐ τ ∂π, 0 ≤ σ2 τ
  dilution : ∀ᵐ τ ∂π, η τ ≤ δ τ / (δ τ + δm)
  contested_claim : GeneralizedContestedClaimCondition π
    (fun τ ↦ meanAffineIntercept (η τ) (μ τ) m)
    (fun τ ↦ meanAffineSlope (η τ) (e τ) (μ τ) m)
  strict_set_positive :
    0 < π {τ | 0 < deanchoringRate (η τ) (e τ) ∧
      η τ < δ τ / (δ τ + δm)}

/-- The typewise MSE is an exact quadratic polynomial in deference. -/
theorem continuousTypeMSE_eq_polynomial {T : Type*} (δm : ℝ)
    (δ γ η e : T → ℝ) (β : ℝ) (τ : T) :
    continuousTypeMSE δm δ γ η e β τ =
      continuousMSEIntercept δm δ γ η τ +
        continuousMSELinearCoefficient δm δ γ η e τ * β +
        continuousMSEQuadraticCoefficient δm δ γ η e τ * β ^ 2 := by
  simp only [continuousTypeMSE, continuousMSEIntercept,
    continuousMSELinearCoefficient, continuousMSEQuadraticCoefficient,
    PaperI.typeMSE, PaperI.mseQuadratic, PaperI.affineEvidenceWeight,
    deanchoringRate]
  ring

/-- The polynomial derivative is the paper's harm-incidence curve. -/
theorem continuousMarginalHarm_eq_coefficients {T : Type*} (δm : ℝ)
    (δ γ η e : T → ℝ) (β : ℝ) (τ : T) :
    continuousMarginalHarm δm δ γ η e β τ =
      continuousMSELinearCoefficient δm δ γ η e τ +
        2 * continuousMSEQuadraticCoefficient δm δ γ η e τ * β := by
  simp only [continuousMarginalHarm, continuousMSELinearCoefficient,
    continuousMSEQuadraticCoefficient, PaperI.marginalHarmBracket,
    PaperI.affineEvidenceWeight, deanchoringRate]
  ring

/-- Pointwise differentiation gives `mg(τ;β)=2r(τ)hτ(β)`. -/
theorem hasDerivAt_continuousTypeMSE {T : Type*} (δm : ℝ)
    (δ γ η e : T → ℝ) (β : ℝ) (τ : T) :
    HasDerivAt (fun x ↦ continuousTypeMSE δm δ γ η e x τ)
      (continuousMarginalHarm δm δ γ η e β τ) β := by
  convert PaperI.hasDerivAt_typeMSE
    (δ τ) δm (γ τ) (η τ) (1 - e τ) β using 1 <;>
    simp only [continuousTypeMSE, continuousMarginalHarm, deanchoringRate]
  ring

/-- Essential boundedness is preserved by the residual extraction factor. -/
theorem continuousRateFactor_memLp_top {T : Type*} [MeasurableSpace T]
    (π : Measure T) [IsProbabilityMeasure π] {e : T → ℝ}
    (he : MemLp e ⊤ π) : MemLp (fun τ ↦ 1 - e τ) ⊤ π := by
  have hOne : MemLp (fun _ : T ↦ (1 : ℝ)) ⊤ π := memLp_top_const 1
  convert hOne.sub he using 1
  ext τ
  rfl

/-- The product of two essentially bounded real functions is essentially bounded. -/
theorem memLp_top_mul {T : Type*} [MeasurableSpace T] {π : Measure T}
    {f g : T → ℝ} (hf : MemLp f ⊤ π) (hg : MemLp g ⊤ π) :
    MemLp (f * g) ⊤ π :=
  hg.mul (p := ⊤) (q := ⊤) (r := ⊤) hf

/-- The de-anchoring rate is essentially bounded. -/
theorem deanchoringRate_memLp_top {T : Type*} [MeasurableSpace T]
    (π : Measure T) [IsProbabilityMeasure π] {η e : T → ℝ}
    (hη : MemLp η ⊤ π) (he : MemLp e ⊤ π) :
    MemLp (fun τ ↦ deanchoringRate (η τ) (e τ)) ⊤ π := by
  have hr := continuousRateFactor_memLp_top π he
  convert memLp_top_mul hη hr using 1
  ext τ
  rfl

/-- Every policy slice of the typewise MSE is essentially bounded. -/
theorem continuousTypeMSE_memLp_top {T : Type*} [MeasurableSpace T]
    (π : Measure T) [IsProbabilityMeasure π] (δm β : ℝ)
    {δ γ η e : T → ℝ} (hδ : MemLp δ ⊤ π) (hγ : MemLp γ ⊤ π)
    (hη : MemLp η ⊤ π) (he : MemLp e ⊤ π) :
    MemLp (continuousTypeMSE δm δ γ η e β) ⊤ π := by
  have hOne : MemLp (fun _ : T ↦ (1 : ℝ)) ⊤ π := memLp_top_const 1
  have hr := continuousRateFactor_memLp_top π he
  have hrβ : MemLp (fun τ ↦ (1 - e τ) * β) ⊤ π := hr.mul_const β
  have hResidualPolicy : MemLp (fun τ ↦ 1 - (1 - e τ) * β) ⊤ π := by
    convert hOne.sub hrβ using 1
    ext τ
    rfl
  have hw : MemLp
      (fun τ ↦ PaperI.affineEvidenceWeight (η τ) (1 - e τ) β) ⊤ π := by
    convert memLp_top_mul hη hResidualPolicy using 1
    ext τ
    rfl
  have hResidual : MemLp
      (fun τ ↦ 1 - PaperI.affineEvidenceWeight (η τ) (1 - e τ) β) ⊤ π := by
    convert hOne.sub hw using 1
    ext τ
    rfl
  have hFirst : MemLp (fun τ ↦
      (1 - PaperI.affineEvidenceWeight (η τ) (1 - e τ) β) ^ 2 * δ τ) ⊤ π := by
    have hsq := memLp_top_mul hResidual hResidual
    convert memLp_top_mul hsq hδ using 1
    ext τ
    simp only [pow_two, Pi.mul_apply]
  have hSecond : MemLp (fun τ ↦
      PaperI.affineEvidenceWeight (η τ) (1 - e τ) β ^ 2 * δm) ⊤ π := by
    have hsq := memLp_top_mul hw hw
    simpa only [Pi.mul_apply, pow_two] using hsq.mul_const δm
  have hCross : MemLp (fun τ ↦
      2 * (1 - PaperI.affineEvidenceWeight (η τ) (1 - e τ) β) *
        PaperI.affineEvidenceWeight (η τ) (1 - e τ) β * γ τ) ⊤ π := by
    have hrw := memLp_top_mul hResidual hw
    have hrwγ := memLp_top_mul hrw hγ
    simpa only [Pi.mul_apply, mul_assoc] using hrwγ.const_mul 2
  have hsum := (hFirst.add hSecond).add hCross
  convert hsum using 1
  ext τ
  rfl

/-- Every policy slice of the marginal-harm curve is essentially bounded. -/
theorem continuousMarginalHarm_memLp_top {T : Type*} [MeasurableSpace T]
    (π : Measure T) [IsProbabilityMeasure π] (δm β : ℝ)
    {δ γ η e : T → ℝ} (hδ : MemLp δ ⊤ π) (hγ : MemLp γ ⊤ π)
    (hη : MemLp η ⊤ π) (he : MemLp e ⊤ π) :
    MemLp (continuousMarginalHarm δm δ γ η e β) ⊤ π := by
  have hr := deanchoringRate_memLp_top π hη he
  have hOne : MemLp (fun _ : T ↦ (1 : ℝ)) ⊤ π := memLp_top_const 1
  have hRateFactor := continuousRateFactor_memLp_top π he
  have hWeightBase : MemLp (fun τ ↦ 1 - (1 - e τ) * β) ⊤ π := by
    have hscaled := hRateFactor.mul_const β
    convert hOne.sub hscaled using 1
    ext τ
    rfl
  have hw : MemLp
      (fun τ ↦ PaperI.affineEvidenceWeight (η τ) (1 - e τ) β) ⊤ π := by
    convert memLp_top_mul hη hWeightBase using 1
    ext τ
    rfl
  have ha : MemLp (fun τ ↦ δ τ + δm - 2 * γ τ) ⊤ π := by
    have hδm : MemLp (fun _ : T ↦ δm) ⊤ π := memLp_top_const δm
    have htwoγ := hγ.const_mul 2
    convert (hδ.add hδm).sub htwoγ using 1
    ext τ
    rfl
  have hδsubγ : MemLp (fun τ ↦ δ τ - γ τ) ⊤ π := by
    convert hδ.sub hγ using 1
    ext τ
    rfl
  have hwa : MemLp
      (fun τ ↦ PaperI.affineEvidenceWeight (η τ) (1 - e τ) β *
        (δ τ + δm - 2 * γ τ)) ⊤ π := by
    convert memLp_top_mul hw ha using 1
    ext τ
    rfl
  have hbracket : MemLp (fun τ ↦
      PaperI.marginalHarmBracket (δ τ) δm (γ τ) (η τ) (1 - e τ) β) ⊤ π := by
    convert hδsubγ.sub hwa using 1
    ext τ
    rfl
  have hproduct : MemLp (fun τ ↦
      deanchoringRate (η τ) (e τ) *
        PaperI.marginalHarmBracket (δ τ) δm (γ τ) (η τ) (1 - e τ) β) ⊤ π := by
    convert memLp_top_mul hr hbracket using 1
    ext τ
    rfl
  convert hproduct.const_mul 2 using 1
  ext τ
  simp only [continuousMarginalHarm]
  ring

/-- The quadratic MSE coefficient is essentially bounded. -/
theorem continuousMSEQuadraticCoefficient_memLp_top
    {T : Type*} [MeasurableSpace T] (π : Measure T) [IsProbabilityMeasure π]
    (δm : ℝ) {δ γ η e : T → ℝ} (hδ : MemLp δ ⊤ π)
    (hγ : MemLp γ ⊤ π) (hη : MemLp η ⊤ π) (he : MemLp e ⊤ π) :
    MemLp (continuousMSEQuadraticCoefficient δm δ γ η e) ⊤ π := by
  have hr := deanchoringRate_memLp_top π hη he
  have hrsq : MemLp (fun τ ↦ deanchoringRate (η τ) (e τ) ^ 2) ⊤ π := by
    convert memLp_top_mul hr hr using 1
    ext τ
    simp only [pow_two, Pi.mul_apply]
  have hδm : MemLp (fun _ : T ↦ δm) ⊤ π := memLp_top_const δm
  have htwoγ := hγ.const_mul 2
  have ha : MemLp (fun τ ↦ δ τ + δm - 2 * γ τ) ⊤ π := by
    convert (hδ.add hδm).sub htwoγ using 1
    ext τ
    rfl
  convert memLp_top_mul hrsq ha using 1
  ext τ
  rfl

/-- Every policy slice of the within-type integrand is essentially bounded. -/
theorem continuousWithinIntegrand_memLp_top
    {T : Type*} [MeasurableSpace T] (π : Measure T) [IsProbabilityMeasure π]
    (β : ℝ) {η e σ2 : T → ℝ} (hη : MemLp η ⊤ π) (he : MemLp e ⊤ π)
    (hσ2 : MemLp σ2 ⊤ π) :
    MemLp (fun τ ↦ PaperI.residualVarianceFactor (η τ) (1 - e τ) β * σ2 τ)
      ⊤ π := by
  have hOne : MemLp (fun _ : T ↦ (1 : ℝ)) ⊤ π := memLp_top_const 1
  have hr := continuousRateFactor_memLp_top π he
  have hrβ := hr.mul_const β
  have hWeightBase : MemLp (fun τ ↦ 1 - (1 - e τ) * β) ⊤ π := by
    convert hOne.sub hrβ using 1
    ext τ
    rfl
  have hw : MemLp
      (fun τ ↦ PaperI.affineEvidenceWeight (η τ) (1 - e τ) β) ⊤ π := by
    convert memLp_top_mul hη hWeightBase using 1
    ext τ
    rfl
  have hResidual : MemLp
      (fun τ ↦ 1 - PaperI.affineEvidenceWeight (η τ) (1 - e τ) β) ⊤ π := by
    convert hOne.sub hw using 1
    ext τ
    rfl
  have hsq : MemLp (fun τ ↦
      (1 - PaperI.affineEvidenceWeight (η τ) (1 - e τ) β) ^ 2) ⊤ π := by
    convert memLp_top_mul hResidual hResidual using 1
    ext τ
    simp only [pow_two, Pi.mul_apply]
  convert memLp_top_mul hsq hσ2 using 1
  ext τ
  rfl

/-- The affine mean components are square-integrable under bounded primitives. -/
theorem continuousAffineComponents_memLp_two
    {T : Type*} [MeasurableSpace T] (π : Measure T) [IsProbabilityMeasure π]
    {η e μ : T → ℝ} (m : ℝ) (hη : MemLp η ⊤ π) (he : MemLp e ⊤ π)
    (hμ : MemLp μ ⊤ π) :
    MemLp (fun τ ↦ meanAffineIntercept (η τ) (μ τ) m) 2 π ∧
      MemLp (fun τ ↦ meanAffineSlope (η τ) (e τ) (μ τ) m) 2 π := by
  have hOne : MemLp (fun _ : T ↦ (1 : ℝ)) ⊤ π := memLp_top_const 1
  have hm : MemLp (fun _ : T ↦ m) ⊤ π := memLp_top_const m
  have hOneSubEta : MemLp (fun τ ↦ 1 - η τ) ⊤ π := by
    convert hOne.sub hη using 1
    ext τ
    rfl
  have hMuSubM : MemLp (fun τ ↦ μ τ - m) ⊤ π := by
    convert hμ.sub hm using 1
    ext τ
    rfl
  have hA_top : MemLp
      (fun τ ↦ meanAffineIntercept (η τ) (μ τ) m) ⊤ π := by
    convert memLp_top_mul hOneSubEta hMuSubM using 1
    ext τ
    rfl
  have hRate := deanchoringRate_memLp_top π hη he
  have hB_top : MemLp
      (fun τ ↦ meanAffineSlope (η τ) (e τ) (μ τ) m) ⊤ π := by
    convert memLp_top_mul hRate hMuSubM using 1
    ext τ
    rfl
  exact ⟨hA_top.mono_exponent (by norm_num), hB_top.mono_exponent (by norm_num)⟩

/-- Bounded typewise MSE slices are integrable under the probability measure. -/
theorem continuousTypeMSE_integrable {T : Type*} [MeasurableSpace T]
    (π : Measure T) [IsProbabilityMeasure π] (δm β : ℝ)
    {δ γ η e : T → ℝ} (hδ : MemLp δ ⊤ π) (hγ : MemLp γ ⊤ π)
    (hη : MemLp η ⊤ π) (he : MemLp e ⊤ π) :
    Integrable (continuousTypeMSE δm δ γ η e β) π :=
  (continuousTypeMSE_memLp_top π δm β hδ hγ hη he).integrable (by norm_num)

/-- Bounded marginal-harm slices are integrable under the probability measure. -/
theorem continuousMarginalHarm_integrable {T : Type*} [MeasurableSpace T]
    (π : Measure T) [IsProbabilityMeasure π] (δm β : ℝ)
    {δ γ η e : T → ℝ} (hδ : MemLp δ ⊤ π) (hγ : MemLp γ ⊤ π)
    (hη : MemLp η ⊤ π) (he : MemLp e ⊤ π) :
    Integrable (continuousMarginalHarm δm δ γ η e β) π :=
  (continuousMarginalHarm_memLp_top π δm β hδ hγ hη he).integrable (by norm_num)

/-- The bounded quadratic MSE coefficient is integrable. -/
theorem continuousMSEQuadraticCoefficient_integrable
    {T : Type*} [MeasurableSpace T] (π : Measure T) [IsProbabilityMeasure π]
    (δm : ℝ) {δ γ η e : T → ℝ} (hδ : MemLp δ ⊤ π)
    (hγ : MemLp γ ⊤ π) (hη : MemLp η ⊤ π) (he : MemLp e ⊤ π) :
    Integrable (continuousMSEQuadraticCoefficient δm δ γ η e) π :=
  (continuousMSEQuadraticCoefficient_memLp_top π δm hδ hγ hη he).integrable
    (by norm_num)

/-- Bounded within-type fragmentation slices are integrable. -/
theorem continuousWithinIntegrand_integrable
    {T : Type*} [MeasurableSpace T] (π : Measure T) [IsProbabilityMeasure π]
    (β : ℝ) {η e σ2 : T → ℝ} (hη : MemLp η ⊤ π) (he : MemLp e ⊤ π)
    (hσ2 : MemLp σ2 ⊤ π) :
    Integrable
      (fun τ ↦ PaperI.residualVarianceFactor (η τ) (1 - e τ) β * σ2 τ) π :=
  (continuousWithinIntegrand_memLp_top π β hη he hσ2).integrable (by norm_num)

/-- The continuous accuracy loss is the integral of an exact quadratic polynomial. -/
theorem continuousAccuracyLoss_eq_polynomial
    {T : Type*} [MeasurableSpace T] (π : Measure T) [IsProbabilityMeasure π]
    (δm : ℝ) {δ γ η e : T → ℝ} (hδ : MemLp δ ⊤ π)
    (hγ : MemLp γ ⊤ π) (hη : MemLp η ⊤ π) (he : MemLp e ⊤ π)
    (β : ℝ) :
    continuousAccuracyLoss π δm δ γ η e β =
      (∫ τ, continuousMSEIntercept δm δ γ η τ ∂π) +
        (∫ τ, continuousMSELinearCoefficient δm δ γ η e τ ∂π) * β +
        (∫ τ, continuousMSEQuadraticCoefficient δm δ γ η e τ ∂π) * β ^ 2 := by
  have hIntercept : Integrable (continuousMSEIntercept δm δ γ η) π := by
    convert continuousTypeMSE_integrable π δm 0 hδ hγ hη he using 1
    ext τ
    simp only [continuousTypeMSE, continuousMSEIntercept, PaperI.typeMSE,
      PaperI.affineEvidenceWeight, mul_zero, sub_zero, mul_one]
  have hLinear : Integrable (continuousMSELinearCoefficient δm δ γ η e) π := by
    convert continuousMarginalHarm_integrable π δm 0 hδ hγ hη he using 1
    ext τ
    rw [continuousMarginalHarm_eq_coefficients]
    ring
  have hQuadratic :=
    continuousMSEQuadraticCoefficient_integrable π δm hδ hγ hη he
  have hLinearScaled := hLinear.mul_const β
  have hQuadraticScaled := hQuadratic.mul_const (β ^ 2)
  have hFirstIntegral :
      integral π (continuousMSEIntercept δm δ γ η +
        fun τ ↦ continuousMSELinearCoefficient δm δ γ η e τ * β) =
        (∫ τ, continuousMSEIntercept δm δ γ η τ ∂π) +
          ∫ τ, continuousMSELinearCoefficient δm δ γ η e τ * β ∂π := by
    rw [show (continuousMSEIntercept δm δ γ η +
        fun τ ↦ continuousMSELinearCoefficient δm δ γ η e τ * β) =
      fun τ ↦ continuousMSEIntercept δm δ γ η τ +
        continuousMSELinearCoefficient δm δ γ η e τ * β by rfl]
    exact integral_add hIntercept hLinearScaled
  have hSplit :
      (fun τ ↦ continuousMSEIntercept δm δ γ η τ +
        continuousMSELinearCoefficient δm δ γ η e τ * β +
        continuousMSEQuadraticCoefficient δm δ γ η e τ * β ^ 2) =
      (continuousMSEIntercept δm δ γ η +
        (fun τ ↦ continuousMSELinearCoefficient δm δ γ η e τ * β)) +
        fun τ ↦ continuousMSEQuadraticCoefficient δm δ γ η e τ * β ^ 2 := by
    rfl
  rw [continuousAccuracyLoss]
  calc
    (∫ τ, continuousTypeMSE δm δ γ η e β τ ∂π) =
        ∫ τ, continuousMSEIntercept δm δ γ η τ +
          continuousMSELinearCoefficient δm δ γ η e τ * β +
          continuousMSEQuadraticCoefficient δm δ γ η e τ * β ^ 2 ∂π := by
      apply integral_congr_ae
      filter_upwards with τ
      exact continuousTypeMSE_eq_polynomial δm δ γ η e β τ
    _ = (∫ τ, continuousMSEIntercept δm δ γ η τ ∂π) +
          (∫ τ, continuousMSELinearCoefficient δm δ γ η e τ * β ∂π) +
          ∫ τ, continuousMSEQuadraticCoefficient δm δ γ η e τ * β ^ 2 ∂π := by
      rw [hSplit]
      calc
        integral π
            ((continuousMSEIntercept δm δ γ η +
              fun τ ↦ continuousMSELinearCoefficient δm δ γ η e τ * β) +
              fun τ ↦ continuousMSEQuadraticCoefficient δm δ γ η e τ * β ^ 2) =
            integral π (continuousMSEIntercept δm δ γ η +
              fun τ ↦ continuousMSELinearCoefficient δm δ γ η e τ * β) +
              ∫ τ, continuousMSEQuadraticCoefficient δm δ γ η e τ * β ^ 2 ∂π :=
          integral_add (hIntercept.add hLinearScaled) hQuadraticScaled
        _ = ((∫ τ, continuousMSEIntercept δm δ γ η τ ∂π) +
              ∫ τ, continuousMSELinearCoefficient δm δ γ η e τ * β ∂π) +
              ∫ τ, continuousMSEQuadraticCoefficient δm δ γ η e τ * β ^ 2 ∂π := by
          rw [hFirstIntegral]
    _ = (∫ τ, continuousMSEIntercept δm δ γ η τ ∂π) +
          (∫ τ, continuousMSELinearCoefficient δm δ γ η e τ ∂π) * β +
          (∫ τ, continuousMSEQuadraticCoefficient δm δ γ η e τ ∂π) * β ^ 2 := by
      rw [integral_mul_const, integral_mul_const]

/-- Integrating `mg(τ;β)` gives the derivative of the population accuracy loss. -/
theorem integral_continuousMarginalHarm_eq_coefficients
    {T : Type*} [MeasurableSpace T] (π : Measure T) [IsProbabilityMeasure π]
    (δm : ℝ) {δ γ η e : T → ℝ} (hδ : MemLp δ ⊤ π)
    (hγ : MemLp γ ⊤ π) (hη : MemLp η ⊤ π) (he : MemLp e ⊤ π)
    (β : ℝ) :
    (∫ τ, continuousMarginalHarm δm δ γ η e β τ ∂π) =
      (∫ τ, continuousMSELinearCoefficient δm δ γ η e τ ∂π) +
        2 * (∫ τ, continuousMSEQuadraticCoefficient δm δ γ η e τ ∂π) * β := by
  have hLinear : Integrable (continuousMSELinearCoefficient δm δ γ η e) π := by
    convert continuousMarginalHarm_integrable π δm 0 hδ hγ hη he using 1
    ext τ
    rw [continuousMarginalHarm_eq_coefficients]
    ring
  have hQuadratic :=
    continuousMSEQuadraticCoefficient_integrable π δm hδ hγ hη he
  have hScaled : Integrable
      (fun τ ↦ 2 * continuousMSEQuadraticCoefficient δm δ γ η e τ * β) π := by
    convert hQuadratic.mul_const (2 * β) using 1
    ext τ
    ring
  calc
    (∫ τ, continuousMarginalHarm δm δ γ η e β τ ∂π) =
        ∫ τ, continuousMSELinearCoefficient δm δ γ η e τ +
          2 * continuousMSEQuadraticCoefficient δm δ γ η e τ * β ∂π := by
      apply integral_congr_ae
      filter_upwards with τ
      exact continuousMarginalHarm_eq_coefficients δm δ γ η e β τ
    _ = (∫ τ, continuousMSELinearCoefficient δm δ γ η e τ ∂π) +
          ∫ τ, 2 * continuousMSEQuadraticCoefficient δm δ γ η e τ * β ∂π := by
      rw [integral_add hLinear hScaled]
    _ = (∫ τ, continuousMSELinearCoefficient δm δ γ η e τ ∂π) +
          2 * (∫ τ, continuousMSEQuadraticCoefficient δm δ γ η e τ ∂π) * β := by
      rw [show (fun τ ↦ 2 * continuousMSEQuadraticCoefficient δm δ γ η e τ * β) =
          fun τ ↦ continuousMSEQuadraticCoefficient δm δ γ η e τ * (2 * β) by
        funext τ
        ring,
        integral_mul_const]
      ring

/--
Differentiation under the type integral for Paper II, Theorem `thm:contA`.
The bounded quadratic family is integrated coefficient-by-coefficient.
-/
theorem hasDerivAt_continuousAccuracyLoss
    {T : Type*} [MeasurableSpace T] (π : Measure T) [IsProbabilityMeasure π]
    (δm : ℝ) {δ γ η e : T → ℝ} (hδ : MemLp δ ⊤ π)
    (hγ : MemLp γ ⊤ π) (hη : MemLp η ⊤ π) (he : MemLp e ⊤ π)
    (β : ℝ) :
    HasDerivAt (continuousAccuracyLoss π δm δ γ η e)
      (∫ τ, continuousMarginalHarm δm δ γ η e β τ ∂π) β := by
  let c0 : ℝ := ∫ τ, continuousMSEIntercept δm δ γ η τ ∂π
  let c1 : ℝ := ∫ τ, continuousMSELinearCoefficient δm δ γ η e τ ∂π
  let c2 : ℝ := ∫ τ, continuousMSEQuadraticCoefficient δm δ γ η e τ ∂π
  have hfun : continuousAccuracyLoss π δm δ γ η e =
      fun x ↦ c0 + c1 * x + c2 * x ^ 2 := by
    funext x
    simpa only [c0, c1, c2] using
      continuousAccuracyLoss_eq_polynomial π δm hδ hγ hη he x
  have hpoly : HasDerivAt (fun x ↦ c0 + c1 * x + c2 * x ^ 2)
      (c1 + 2 * c2 * β) β := by
    have hLinear : HasDerivAt (fun x ↦ c1 * x) c1 β := by
      simpa using (hasDerivAt_id β).const_mul c1
    have hQuadratic : HasDerivAt (fun x ↦ c2 * x ^ 2) (c2 * (2 * β)) β := by
      simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using
        (hasDerivAt_pow 2 β).const_mul c2
    have hRaw := ((hasDerivAt_const β c0).add hLinear).add hQuadratic
    simp only [zero_add] at hRaw
    have hCoefficient : c1 + c2 * (2 * β) = c1 + 2 * c2 * β := by ring
    rw [hCoefficient] at hRaw
    have hFunction :
        ((fun _ : ℝ ↦ c0) + (fun x ↦ c1 * x)) + (fun x ↦ c2 * x ^ 2) =
          fun x ↦ c0 + c1 * x + c2 * x ^ 2 := by
      rfl
    rw [← hFunction]
    simpa only [zero_add] using hRaw
  rw [hfun]
  convert hpoly using 1
  simpa only [c1, c2] using
    integral_continuousMarginalHarm_eq_coefficients π δm hδ hγ hη he β

/-- The scalar harm-incidence expression is nonnegative under dilution. -/
theorem continuousMarginalHarm_scalar_nonnegative
    {δm δ γ η e β : ℝ} (hδm : 0 ≤ δm) (hδ : 0 ≤ δ)
    (hevidence : δm < δ) (hγ : 0 ≤ γ) (hγbound : γ ≤ √(δm * δ))
    (hη : η ∈ Ioc (0 : ℝ) 1) (he : e ∈ Ico (0 : ℝ) 1)
    (hdilution : η ≤ δ / (δ + δm)) (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 ≤ 2 * deanchoringRate η e *
      PaperI.marginalHarmBracket δ δm γ η (1 - e) β := by
  have ha : 0 < δ + δm - 2 * γ :=
    PaperI.mseQuadratic_coefficient_pos hδm hδ hevidence hγ hγbound
  have hthreshold :
      δ / (δ + δm) ≤ (δ - γ) / (δ + δm - 2 * γ) :=
    PaperI.auditThreshold_le_optimalWeight hδm hδ hevidence hγ hγbound
  have hrateFactor : 0 ≤ 1 - e := sub_nonneg.mpr he.2.le
  have hweightLeEta : PaperI.affineEvidenceWeight η (1 - e) β ≤ η := by
    simp only [PaperI.affineEvidenceWeight]
    nlinarith [mul_nonneg (mul_nonneg hη.1.le hrateFactor) hβ.1]
  have hweightLeOptimal :
      PaperI.affineEvidenceWeight η (1 - e) β ≤
        (δ - γ) / (δ + δm - 2 * γ) :=
    hweightLeEta.trans (hdilution.trans hthreshold)
  have hbracket :
      0 ≤ PaperI.marginalHarmBracket δ δm γ η (1 - e) β := by
    rw [PaperI.marginalHarmBracket]
    exact sub_nonneg.mpr ((le_div_iff₀ ha).mp hweightLeOptimal)
  have hr : 0 ≤ deanchoringRate η e := by
    exact mul_nonneg hη.1.le hrateFactor
  positivity

/-- Strict dilution on a positive-rate type makes its harm incidence positive. -/
theorem continuousMarginalHarm_scalar_pos
    {δm δ γ η e β : ℝ} (hδm : 0 ≤ δm) (hδ : 0 ≤ δ)
    (hevidence : δm < δ) (hγ : 0 ≤ γ) (hγbound : γ ≤ √(δm * δ))
    (hη : η ∈ Ioc (0 : ℝ) 1) (he : e ∈ Ico (0 : ℝ) 1)
    (hr : 0 < deanchoringRate η e)
    (hstrict : η < δ / (δ + δm)) (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 < 2 * deanchoringRate η e *
      PaperI.marginalHarmBracket δ δm γ η (1 - e) β := by
  have ha : 0 < δ + δm - 2 * γ :=
    PaperI.mseQuadratic_coefficient_pos hδm hδ hevidence hγ hγbound
  have hthreshold :
      δ / (δ + δm) ≤ (δ - γ) / (δ + δm - 2 * γ) :=
    PaperI.auditThreshold_le_optimalWeight hδm hδ hevidence hγ hγbound
  have hrateFactor : 0 ≤ 1 - e := sub_nonneg.mpr he.2.le
  have hweightLeEta : PaperI.affineEvidenceWeight η (1 - e) β ≤ η := by
    simp only [PaperI.affineEvidenceWeight]
    nlinarith [mul_nonneg (mul_nonneg hη.1.le hrateFactor) hβ.1]
  have hweightLtOptimal :
      PaperI.affineEvidenceWeight η (1 - e) β <
        (δ - γ) / (δ + δm - 2 * γ) :=
    hweightLeEta.trans_lt (hstrict.trans_le hthreshold)
  have hbracket :
      0 < PaperI.marginalHarmBracket δ δm γ η (1 - e) β := by
    rw [PaperI.marginalHarmBracket]
    exact sub_pos.mpr ((lt_div_iff₀ ha).mp hweightLtOptimal)
  exact mul_pos (mul_pos two_pos hr) hbracket

/-- The population accuracy derivative is strictly positive at every policy. -/
theorem integral_continuousMarginalHarm_pos
    {T : Type*} [MeasurableSpace T] (π : Measure T) [IsProbabilityMeasure π]
    {δm : ℝ} {δ γ η e μ σ2 : T → ℝ} {m β : ℝ}
    (model : ContinuousTypeHarmAssumptions π δm δ γ η e μ σ2 m)
    (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 < ∫ τ, continuousMarginalHarm δm δ γ η e β τ ∂π := by
  have hIntegrable := continuousMarginalHarm_integrable π δm β
    model.delta_memLp model.gamma_memLp model.responsiveness_memLp model.extraction_memLp
  have hnonnegative : 0 ≤ᵐ[π] continuousMarginalHarm δm δ γ η e β := by
    filter_upwards [model.type_error_nonnegative, model.correlation_nonnegative,
      model.correlation_bound, model.evidence_advantage, model.responsiveness_range,
      model.extraction_range, model.dilution] with τ hδ hγ hγbound hevidence hη he hdilution
    simpa only [Pi.zero_apply, continuousMarginalHarm] using
      continuousMarginalHarm_scalar_nonnegative model.evidence_error_nonnegative hδ
        hevidence hγ hγbound hη he hdilution hβ
  let strictSet : Set T := {τ | 0 < deanchoringRate (η τ) (e τ) ∧
    η τ < δ τ / (δ τ + δm)}
  have hStrictSet : 0 < π strictSet := by
    simpa only [strictSet] using model.strict_set_positive
  have hSupport : strictSet ≤ᵐ[π]
      Function.support (continuousMarginalHarm δm δ γ η e β) := by
    filter_upwards [model.type_error_nonnegative, model.correlation_nonnegative,
      model.correlation_bound, model.evidence_advantage, model.responsiveness_range,
      model.extraction_range] with τ hδ hγ hγbound hevidence hη he
    intro hτ
    apply Function.mem_support.mpr
    have hpos := continuousMarginalHarm_scalar_pos model.evidence_error_nonnegative hδ
      hevidence hγ hγbound hη he hτ.1 hτ.2 hβ
    simpa only [continuousMarginalHarm] using hpos.ne'
  apply (integral_pos_iff_support_of_nonneg_ae hnonnegative hIntegrable).2
  exact hStrictSet.trans_le (measure_mono_ae hSupport)

/-- Population accuracy loss is strictly increasing throughout the policy interval. -/
theorem continuousAccuracyLoss_strictMonoOn
    {T : Type*} [MeasurableSpace T] (π : Measure T) [IsProbabilityMeasure π]
    {δm : ℝ} {δ γ η e μ σ2 : T → ℝ} {m : ℝ}
    (model : ContinuousTypeHarmAssumptions π δm δ γ η e μ σ2 m) :
    StrictMonoOn (continuousAccuracyLoss π δm δ γ η e) (Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1)
  · intro β hβ
    exact (hasDerivAt_continuousAccuracyLoss π δm model.delta_memLp model.gamma_memLp
      model.responsiveness_memLp model.extraction_memLp β).continuousAt.continuousWithinAt
  · intro β hβ
    have hβclosed : β ∈ Icc (0 : ℝ) 1 := interior_subset hβ
    rw [(hasDerivAt_continuousAccuracyLoss π δm model.delta_memLp model.gamma_memLp
      model.responsiveness_memLp model.extraction_memLp β).deriv]
    exact integral_continuousMarginalHarm_pos π model hβclosed

/-- Within-type fragmentation is nondecreasing throughout the policy interval. -/
theorem continuousWithinTypeDispersion_monotoneOn
    {T : Type*} [MeasurableSpace T] (π : Measure T) [IsProbabilityMeasure π]
    {δm : ℝ} {δ γ η e μ σ2 : T → ℝ} {m : ℝ}
    (model : ContinuousTypeHarmAssumptions π δm δ γ η e μ σ2 m) :
    MonotoneOn (continuousWithinTypeDispersion π η e σ2) (Icc (0 : ℝ) 1) := by
  change MonotoneOn
    (fun β ↦ ∫ τ, PaperI.residualVarianceFactor (η τ) (1 - e τ) β * σ2 τ ∂π)
    (Icc (0 : ℝ) 1)
  apply integral_monotoneOn_of_integrand_ae
  · filter_upwards [model.responsiveness_range, model.extraction_range,
      model.variance_nonnegative] with τ hη he hσ2
    intro β1 hβ1 β2 hβ2 hβ
    have hfactor := PaperI.residualVarianceFactor_monotoneOn
      hη.1 hη.2 (sub_nonneg.mpr he.2.le) hβ1 hβ2 hβ
    exact mul_le_mul_of_nonneg_right hfactor hσ2
  · intro β _
    exact continuousWithinIntegrand_integrable π β model.responsiveness_memLp
      model.extraction_memLp model.variance_memLp

/-- The covariance condition makes between-type stratification nondecreasing. -/
theorem continuousStratification_monotoneOn
    {T : Type*} [MeasurableSpace T] (π : Measure T) [IsProbabilityMeasure π]
    {δm : ℝ} {δ γ η e μ σ2 : T → ℝ} {m : ℝ}
    (model : ContinuousTypeHarmAssumptions π δm δ γ η e μ σ2 m) :
    MonotoneOn (continuousStratification π η e μ m) (Icc (0 : ℝ) 1) := by
  let A : T → ℝ := fun τ ↦ meanAffineIntercept (η τ) (μ τ) m
  let B : T → ℝ := fun τ ↦ meanAffineSlope (η τ) (e τ) (μ τ) m
  have hAB := continuousAffineComponents_memLp_two π m model.responsiveness_memLp
    model.extraction_memLp model.mean_memLp
  have hmono : MonotoneOn (affineDispersion π A B) (Icc (0 : ℝ) 1) :=
    (stratificationExplicitQuadratic π hAB.1 hAB.2).monotone_iff_covariance_nonnegative.mpr
      model.contested_claim.covariance_nonnegative
  change MonotoneOn (affineDispersion π A B) (Icc (0 : ℝ) 1)
  exact hmono

/-- Continuous-type collective capacity strictly falls throughout the policy interval. -/
theorem continuousCollectiveCapacity_strictAntiOn
    {T : Type*} [MeasurableSpace T] (π : Measure T) [IsProbabilityMeasure π]
    {δm : ℝ} {δ γ η e μ σ2 : T → ℝ} {m lambda nu : ℝ}
    (model : ContinuousTypeHarmAssumptions π δm δ γ η e μ σ2 m)
    (hlambda : 0 ≤ lambda) (hnu : 0 ≤ nu) :
    StrictAntiOn
      (continuousCollectiveCapacity π δm δ γ η e μ σ2 m lambda nu)
      (Icc (0 : ℝ) 1) := by
  have hAccuracy := continuousAccuracyLoss_strictMonoOn π model
  have hWithin := continuousWithinTypeDispersion_monotoneOn π model
  have hStratification := continuousStratification_monotoneOn π model
  intro β1 hβ1 β2 hβ2 hβ
  have hA := hAccuracy hβ1 hβ2 hβ
  have hW := hWithin hβ1 hβ2 hβ.le
  have hS := hStratification hβ1 hβ2 hβ.le
  have hWweighted := mul_le_mul_of_nonneg_left hW hlambda
  have hSweighted := mul_le_mul_of_nonneg_left hS hnu
  simp only [continuousCollectiveCapacity]
  linarith

/-- Positive satisfaction selection strictly sacrifices continuous-type capacity. -/
theorem continuousTypeSatisfactionOptimalDeferenceHarms
    {T : Type*} [MeasurableSpace T] (π : Measure T) [IsProbabilityMeasure π]
    {δm : ℝ} {δ γ η e μ σ2 : T → ℝ} {m lambda nu : ℝ}
    {U : ℝ → ℝ} {UPrimeZero βstar : ℝ}
    (model : ContinuousTypeHarmAssumptions π δm δ γ η e μ σ2 m)
    (hlambda : 0 ≤ lambda) (hnu : 0 ≤ nu)
    (satisfaction : PaperI.SatisfactionAssumption U UPrimeZero)
    (hβstar : βstar ∈ Icc (0 : ℝ) 1)
    (hmax : IsLocalMaxOn U (Icc (0 : ℝ) 1) βstar) :
    0 < βstar ∧
      continuousCollectiveCapacity π δm δ γ η e μ σ2 m lambda nu βstar <
        continuousCollectiveCapacity π δm δ γ η e μ σ2 m lambda nu 0 := by
  have hpositive := PaperI.satisfaction_localMax_positive satisfaction hβstar hmax
  have hcapacity := continuousCollectiveCapacity_strictAntiOn π model hlambda hnu
  refine ⟨hpositive, ?_⟩
  exact hcapacity (show (0 : ℝ) ∈ Icc 0 1 by norm_num) hβstar hpositive

/-- The two conclusions stated by Paper II's continuous-type harm theorem. -/
structure ContinuousTypeHarmConclusions
    {T : Type*} [MeasurableSpace T] (π : Measure T)
    (δm : ℝ) (δ γ η e μ σ2 : T → ℝ) (m lambda nu : ℝ) : Prop where
  capacity_strictly_decreases :
    StrictAntiOn
      (continuousCollectiveCapacity π δm δ γ η e μ σ2 m lambda nu)
      (Icc (0 : ℝ) 1)
  satisfaction_selection_harms :
    ∀ {U : ℝ → ℝ} {UPrimeZero βstar : ℝ},
      PaperI.SatisfactionAssumption U UPrimeZero →
      βstar ∈ Icc (0 : ℝ) 1 →
      IsLocalMaxOn U (Icc (0 : ℝ) 1) βstar →
      0 < βstar ∧
        continuousCollectiveCapacity π δm δ γ η e μ σ2 m lambda nu βstar <
          continuousCollectiveCapacity π δm δ γ η e μ σ2 m lambda nu 0

/--
Paper II, Theorem `thm:contA`, `civic_drift.tex:778`.

Under the paper's bounded continuous-type assumptions, strict dilution on a
positive-measure set makes accuracy loss strictly rise. The covariance condition
makes both fragmentation terms weakly rise, so capacity strictly falls for every
nonnegative pair of weights. Any constrained local satisfaction maximizer with
positive endpoint derivative therefore chooses positive deference and sacrifices
capacity relative to the safe endpoint.
-/
theorem continuousTypeHarm
    {T : Type*} [MeasurableSpace T] (π : Measure T) [IsProbabilityMeasure π]
    {δm : ℝ} {δ γ η e μ σ2 : T → ℝ} {m lambda nu : ℝ}
    (model : ContinuousTypeHarmAssumptions π δm δ γ η e μ σ2 m)
    (hlambda : 0 ≤ lambda) (hnu : 0 ≤ nu) :
    ContinuousTypeHarmConclusions π δm δ γ η e μ σ2 m lambda nu := by
  exact
    { capacity_strictly_decreases :=
        continuousCollectiveCapacity_strictAntiOn π model hlambda hnu
      satisfaction_selection_harms := fun satisfaction hβstar hmax ↦
        continuousTypeSatisfactionOptimalDeferenceHarms π model hlambda hnu
          satisfaction hβstar hmax }

/-! ## Reduced-satisfaction license -/

/-- Population mean-squared deviation across a finite type population. -/
def populationMeanSquaredDeviation {T : Type*} [Fintype T]
    (π x : T → ℝ) : ℝ :=
  ∑ τ, π τ * x τ ^ 2

/-- Exact type-level agreement reward before imposing homogeneous extraction. -/
def populationAgreementReward {T : Type*} [Fintype T]
    (π e x : T → ℝ) (β : ℝ) : ℝ :=
  -∑ τ, π τ * (1 - continuousEffectiveDeference (e τ) β) ^ 2 * x τ ^ 2

/-- The agreement coefficient averaged with the type's contribution to the
population mean-squared deviation. -/
noncomputable def deviationWeightedAgreementCoefficient
    {T : Type*} [Fintype T] (π c x : T → ℝ) : ℝ :=
  (∑ τ, π τ * x τ ^ 2 * c τ) / populationMeanSquaredDeviation π x

/-- Weighted dispersion of agreement coefficients around their
deviation-weighted mean. -/
noncomputable def deviationWeightedAgreementDispersion
    {T : Type*} [Fintype T] (π c x : T → ℝ) : ℝ :=
  ∑ τ, π τ * x τ ^ 2 *
    (c τ - deviationWeightedAgreementCoefficient π c x) ^ 2

/-- The deviation-weighted dispersion is nonnegative for nonnegative
population weights. -/
theorem deviationWeightedAgreementDispersion_nonneg
    {T : Type*} [Fintype T] (π c x : T → ℝ)
    (hπ : ∀ τ, 0 ≤ π τ) :
    0 ≤ deviationWeightedAgreementDispersion π c x := by
  simp only [deviationWeightedAgreementDispersion]
  exact Finset.sum_nonneg fun τ _ ↦
    mul_nonneg (mul_nonneg (hπ τ) (sq_nonneg _)) (sq_nonneg _)

/--
Paper II, Lemma A.1 (`lem:license`), `civic_drift.tex:964`.

When every type has the same extraction rate, the type-independent agreement
factor pulls exactly through the finite population sum. No sign, normalization,
or state restriction is needed.
-/
theorem exactAggregationUnderHomogeneousExtraction
    {T : Type*} [Fintype T] (π x : T → ℝ) (e β : ℝ) :
    populationAgreementReward π (fun _ ↦ e) x β =
      -(1 - (1 - e) * β) ^ 2 * populationMeanSquaredDeviation π x := by
  simp only [populationAgreementReward, continuousEffectiveDeference,
    populationMeanSquaredDeviation]
  rw [← Finset.sum_neg_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  ring

/-- With heterogeneous extraction, the reduced reward at the
deviation-weighted mean coefficient differs from the exact type-level reward
by exactly a weighted-dispersion term scaled by `-β²`.  The correction is
nonpositive under nonnegative population weights. -/
theorem exactAggregationUnderHeterogeneousExtraction
    {T : Type*} [Fintype T] (π c x : T → ℝ) (β : ℝ)
    (hD : populationMeanSquaredDeviation π x ≠ 0) :
    populationAgreementReward π (fun τ ↦ 1 - c τ) x β =
      -(1 - deviationWeightedAgreementCoefficient π c x * β) ^ 2 *
          populationMeanSquaredDeviation π x -
        β ^ 2 * deviationWeightedAgreementDispersion π c x := by
  let D := populationMeanSquaredDeviation π x
  let M := ∑ τ, π τ * x τ ^ 2 * c τ
  let cbar := M / D
  have hmean : ∑ τ, π τ * x τ ^ 2 * (c τ - cbar) = 0 := by
    calc
      (∑ τ, π τ * x τ ^ 2 * (c τ - cbar)) =
          ∑ τ, (π τ * x τ ^ 2 * c τ - cbar * (π τ * x τ ^ 2)) := by
        apply Finset.sum_congr rfl
        intro τ _
        ring
      _ = M - cbar * D := by
        rw [Finset.sum_sub_distrib]
        change M - (∑ τ, cbar * (π τ * x τ ^ 2)) = M - cbar * D
        have hscale : (∑ τ, cbar * (π τ * x τ ^ 2)) = cbar * D := by
          calc
            (∑ τ, cbar * (π τ * x τ ^ 2)) =
                cbar * ∑ τ, π τ * x τ ^ 2 := by
              exact (Finset.mul_sum Finset.univ
                (fun τ ↦ π τ * x τ ^ 2) cbar).symm
            _ = cbar * D := rfl
        rw [hscale]
      _ = 0 := by
        have hD' : D ≠ 0 := hD
        dsimp only [cbar]
        field_simp [hD']
        ring
  have hpointwise : ∀ τ,
      -(π τ * (1 - c τ * β) ^ 2 * x τ ^ 2) =
        -(π τ * x τ ^ 2) * (1 - cbar * β) ^ 2 -
          β ^ 2 * (π τ * x τ ^ 2 * (c τ - cbar) ^ 2) +
            2 * β * (1 - cbar * β) *
              (π τ * x τ ^ 2 * (c τ - cbar)) := by
    intro τ
    ring
  simp only [populationAgreementReward, continuousEffectiveDeference,
    deviationWeightedAgreementCoefficient,
    deviationWeightedAgreementDispersion]
  change -(∑ τ, π τ * (1 - (1 - (1 - c τ)) * β) ^ 2 * x τ ^ 2) = _
  simp only [sub_sub_cancel]
  rw [← Finset.sum_neg_distrib]
  conv_lhs =>
    enter [2, τ]
    rw [hpointwise τ]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have hfirst :
      (∑ τ, -(π τ * x τ ^ 2) * (1 - cbar * β) ^ 2) =
        -D * (1 - cbar * β) ^ 2 := by
    rw [← Finset.sum_mul]
    congr 1
    rw [Finset.sum_neg_distrib]
    rfl
  rw [hfirst]
  rw [hmean]
  simp only [mul_zero, add_zero]
  change
    -D * (1 - cbar * β) ^ 2 -
        β ^ 2 * (∑ τ, π τ * x τ ^ 2 * (c τ - cbar) ^ 2) =
      -(1 - cbar * β) ^ 2 * D -
        β ^ 2 * (∑ τ, π τ * x τ ^ 2 * (c τ - cbar) ^ 2)
  ring

/-- Away from the automatic agreement point `β = 0`, heterogeneous and
reduced aggregation coincide exactly if and only if the deviation-weighted
dispersion vanishes. -/
theorem heterogeneousExtraction_eq_reduced_iff_dispersion_eq_zero
    {T : Type*} [Fintype T] (π c x : T → ℝ) {β : ℝ}
    (hD : populationMeanSquaredDeviation π x ≠ 0) (hβ : β ≠ 0) :
    populationAgreementReward π (fun τ ↦ 1 - c τ) x β =
        -(1 - deviationWeightedAgreementCoefficient π c x * β) ^ 2 *
          populationMeanSquaredDeviation π x ↔
      deviationWeightedAgreementDispersion π c x = 0 := by
  rw [exactAggregationUnderHeterogeneousExtraction π c x β hD]
  constructor
  · intro h
    have hproduct : β ^ 2 * deviationWeightedAgreementDispersion π c x = 0 := by
      linarith
    exact (mul_eq_zero.mp hproduct).resolve_left (pow_ne_zero 2 hβ)
  · intro hdispersion
    rw [hdispersion]
    ring

#print axioms one_sub_continuousEvidenceWeight
#print axioms affineMeanDynamics
#print axioms affineDispersion_eq_quadratic
#print axioms dispersionQuadratic_convex
#print axioms dispersionQuadratic_monotoneOn_iff
#print axioms dispersionQuadratic_strictAntiOn_initial_of_covariance_neg
#print axioms continuousUpdatedMean_eq_signal_add_affine
#print axioms continuousUpdatedMean_variance_eq_quadratic
#print axioms stratificationExplicitQuadratic
#print axioms integral_pairwiseDifference_eq_two_mul_covariance
#print axioms covariance_nonneg_of_comonotone
#print axioms generalizedContestedClaimCondition_of_comonotone
#print axioms twoPointStraddle_affine_order
#print axioms twoPointStraddle_comonotone
#print axioms generalizedContestedClaimCondition_of_twoPointStraddle
#print axioms contestedClaimSufficientConditions
#print axioms continuousTypeMSE_eq_polynomial
#print axioms continuousMarginalHarm_eq_coefficients
#print axioms hasDerivAt_continuousTypeMSE
#print axioms continuousRateFactor_memLp_top
#print axioms memLp_top_mul
#print axioms deanchoringRate_memLp_top
#print axioms continuousTypeMSE_memLp_top
#print axioms continuousMarginalHarm_memLp_top
#print axioms continuousMSEQuadraticCoefficient_memLp_top
#print axioms continuousWithinIntegrand_memLp_top
#print axioms continuousAffineComponents_memLp_two
#print axioms continuousTypeMSE_integrable
#print axioms continuousMarginalHarm_integrable
#print axioms continuousMSEQuadraticCoefficient_integrable
#print axioms continuousWithinIntegrand_integrable
#print axioms continuousAccuracyLoss_eq_polynomial
#print axioms integral_continuousMarginalHarm_eq_coefficients
#print axioms hasDerivAt_continuousAccuracyLoss
#print axioms continuousMarginalHarm_scalar_nonnegative
#print axioms continuousMarginalHarm_scalar_pos
#print axioms integral_continuousMarginalHarm_pos
#print axioms continuousAccuracyLoss_strictMonoOn
#print axioms continuousWithinTypeDispersion_monotoneOn
#print axioms continuousStratification_monotoneOn
#print axioms continuousCollectiveCapacity_strictAntiOn
#print axioms continuousTypeSatisfactionOptimalDeferenceHarms
#print axioms continuousTypeHarm
#print axioms exactAggregationUnderHomogeneousExtraction
#print axioms deviationWeightedAgreementDispersion_nonneg
#print axioms exactAggregationUnderHeterogeneousExtraction
#print axioms heterogeneousExtraction_eq_reduced_iff_dispersion_eq_zero

end

end CivicAlignment.PaperII
