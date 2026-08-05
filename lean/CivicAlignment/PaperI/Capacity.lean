/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Paper I: collective epistemic capacity

This file formalizes the error geometry, MSE monotonicity, fragmentation, and
stratification chain supporting Paper I's main theorem.
-/

namespace CivicAlignment.PaperI

open Set
open MeasureTheory

/-- Paper I, definition preceding equation `eq:gamma`: squared evidence error. -/
def evidenceError (θ m : ℝ) : ℝ :=
  (m - θ) ^ 2

/-- Paper I, definition preceding equation `eq:gamma`: a type's total prior error. -/
def typeError (θ μ σ2 : ℝ) : ℝ :=
  σ2 + (μ - θ) ^ 2

/-- Paper I, equation `eq:gamma`: prior--evidence error correlation for one type. -/
def errorCorrelation (θ m μ : ℝ) : ℝ :=
  (m - θ) * (μ - θ)

/--
Paper I, Observation 4.4 (`obs:gamma`), civic_alignment.tex:220: binary truth and
unit-interval beliefs force the two error factors to have the same sign.
-/
theorem error_product_nonnegative {θ b m : ℝ} (hθ : θ = 0 ∨ θ = 1)
    (hb : b ∈ Icc (0 : ℝ) 1) (hm : m ∈ Icc (0 : ℝ) 1) :
    0 ≤ (b - θ) * (m - θ) := by
  rcases hθ with rfl | rfl
  · simpa using mul_nonneg hb.1 hm.1
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hb.2) (sub_nonpos.mpr hm.2)

/--
Paper I, Observation 4.4 (`obs:gamma`), civic_alignment.tex:220.  The correlation
is nonnegative, vanishes only in the stated degenerate cases, has the paper's
exact square-root form, and obeys its Cauchy--Schwarz bound.
-/
theorem gamma_geometry {θ m μ σ2 : ℝ} (hθ : θ = 0 ∨ θ = 1)
    (hm : m ∈ Icc (0 : ℝ) 1) (hμ : μ ∈ Icc (0 : ℝ) 1) (hσ2 : 0 ≤ σ2) :
    0 ≤ errorCorrelation θ m μ ∧
      (errorCorrelation θ m μ = 0 ↔ m = θ ∨ μ = θ) ∧
      errorCorrelation θ m μ = √(evidenceError θ m) * |μ - θ| ∧
      errorCorrelation θ m μ ≤ √(evidenceError θ m * typeError θ μ σ2) := by
  have hnonneg : 0 ≤ errorCorrelation θ m μ := by
    simpa only [errorCorrelation, mul_comm] using
      error_product_nonnegative (b := μ) (m := m) hθ hμ hm
  have hzero : errorCorrelation θ m μ = 0 ↔ m = θ ∨ μ = θ := by
    simp only [errorCorrelation, mul_eq_zero, sub_eq_zero]
  have hidentity : errorCorrelation θ m μ = √(evidenceError θ m) * |μ - θ| := by
    rw [evidenceError, Real.sqrt_sq_eq_abs]
    rcases hθ with rfl | rfl
    · simp only [errorCorrelation, sub_zero]
      rw [abs_of_nonneg hm.1, abs_of_nonneg hμ.1]
    · rw [abs_of_nonpos (sub_nonpos.mpr hm.2), abs_of_nonpos (sub_nonpos.mpr hμ.2)]
      simp only [errorCorrelation]
      ring
  have habs_le : |μ - θ| ≤ √(typeError θ μ σ2) := by
    rw [← Real.sqrt_sq_eq_abs (μ - θ)]
    exact Real.sqrt_le_sqrt (by simp only [typeError]; linarith)
  have hbound : errorCorrelation θ m μ ≤ √(evidenceError θ m * typeError θ μ σ2) := by
    calc
      errorCorrelation θ m μ = √(evidenceError θ m) * |μ - θ| := hidentity
      _ ≤ √(evidenceError θ m) * √(typeError θ μ σ2) :=
        mul_le_mul_of_nonneg_left habs_le (Real.sqrt_nonneg _)
      _ = √(evidenceError θ m * typeError θ μ σ2) := by
        simp only [evidenceError]
        rw [Real.sqrt_mul (sq_nonneg (m - θ))]
  exact ⟨hnonneg, hzero, hidentity, hbound⟩

/-! ## MSE decomposition -/

/-- Paper I, equation `eq:weightform`, written as a function of evidence weight. -/
def beliefAtWeight (w m b : ℝ) : ℝ :=
  (1 - w) * b + w * m

/-- Paper I, definition of a type's conditional mean-squared error. -/
noncomputable def populationMSE {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (b : Ω → ℝ)
    (θ m w : ℝ) : ℝ :=
  ∫ x, (beliefAtWeight w m (b x) - θ) ^ 2 ∂P

/-- The moment quadratic on the right side of Paper I equation `eq:msedecomp`. -/
def mseQuadratic (δ δm γ w : ℝ) : ℝ :=
  (1 - w) ^ 2 * δ + w ^ 2 * δm + 2 * (1 - w) * w * γ

/--
Paper I, Lemma 4.11 (`lem:decomp`), civic_alignment.tex:263.  For a conditional
type distribution, expanding the weighted belief error and taking expectation
gives exactly the paper's three-moment quadratic.
-/
theorem mse_decomposition {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (b : Ω → ℝ) (θ m w : ℝ)
    (hsq : Integrable (fun x => (b x - θ) ^ 2) P)
    (hcross : Integrable (fun x => (b x - θ) * (m - θ)) P) :
    populationMSE P b θ m w =
      mseQuadratic (∫ x, (b x - θ) ^ 2 ∂P) ((m - θ) ^ 2)
        (∫ x, (b x - θ) * (m - θ) ∂P) w := by
  have hterm1 : Integrable (fun x => (1 - w) ^ 2 * (b x - θ) ^ 2) P :=
    hsq.const_mul _
  have hterm2 : Integrable (fun _ : Ω => w ^ 2 * (m - θ) ^ 2) P :=
    integrable_const _
  have hterm3 : Integrable (fun x => (2 * (1 - w) * w) * ((b x - θ) * (m - θ))) P :=
    hcross.const_mul _
  calc
    populationMSE P b θ m w =
        ∫ x, ((1 - w) ^ 2 * (b x - θ) ^ 2 + w ^ 2 * (m - θ) ^ 2) +
          (2 * (1 - w) * w) * ((b x - θ) * (m - θ)) ∂P := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [beliefAtWeight]
      ring
    _ = mseQuadratic (∫ x, (b x - θ) ^ 2 ∂P) ((m - θ) ^ 2)
        (∫ x, (b x - θ) * (m - θ) ∂P) w := by
      have h12 := integral_add hterm1 hterm2
      have h123 := integral_add (hterm1.add hterm2) hterm3
      simp only [Pi.add_apply] at h12 h123
      rw [h123, h12]
      simp only [integral_const_mul, integral_const, measureReal_def, measure_univ,
        ENNReal.toReal_one, one_smul, mseQuadratic]

/-! ## Paper I assumption bundles -/

/-- Paper I, Assumption 4.5 (`ass:evidence`): evidence beats both type priors. -/
structure EvidenceAssumption (δm δH δL : ℝ) : Prop where
  δm_lt_δH : δm < δH
  δm_lt_δL : δm < δL

/-- Paper I, Assumption 4.6 (`ass:straddle`): the type means straddle the evidence. -/
structure StraddleAssumption (m μH μL : ℝ) : Prop where
  ordering : (μL < m ∧ m < μH) ∨ (μH < m ∧ m < μL)

/-- Paper I, Assumption 4.7 (`ass:reliance`): both response rates lie in `(0,1]`. -/
structure RelianceAssumption (ηH ηL : ℝ) : Prop where
  ηH_pos : 0 < ηH
  ηH_le_one : ηH ≤ 1
  ηL_pos : 0 < ηL
  ηL_le_one : ηL ≤ 1

/-- Paper I, Assumption 4.8 (`ass:extraction`): extraction advantage lies in `(0,1]`. -/
structure ExtractionAssumption (κ : ℝ) : Prop where
  κ_pos : 0 < κ
  κ_le_one : κ ≤ 1

/-- Paper I, Assumption 4.10 (`ass:dilution`): baseline evidence weights are conservative. -/
structure DilutionAssumption (δm δH δL ηH ηL : ℝ) : Prop where
  ηH_le : ηH ≤ δH / (δH + δm)
  ηL_le : ηL ≤ δL / (δL + δm)

/-! ## Scalar geometry behind `lem:mse` -/

/--
Paper I, proof of Lemma 4.12 (`lem:mse`): the MSE quadratic has positive leading
coefficient under the observation's correlation bound and strict evidence
advantage.
-/
theorem mseQuadratic_coefficient_pos {δ δm γ : ℝ} (hδm : 0 ≤ δm) (hδ : 0 ≤ δ)
    (hevidence : δm < δ) (hγ : 0 ≤ γ) (hγbound : γ ≤ √(δm * δ)) :
    0 < δ + δm - 2 * γ := by
  have hprod : 0 ≤ δm * δ := mul_nonneg hδm hδ
  have hsqrtSq : √(δm * δ) ^ 2 = δm * δ := Real.sq_sqrt hprod
  have hγsq : γ ^ 2 ≤ δm * δ := by
    nlinarith [Real.sqrt_nonneg (δm * δ)]
  have hright : 0 < (δ - δm) ^ 2 + 4 * (δ * δm - γ ^ 2) := by
    nlinarith [sq_pos_of_pos (sub_pos.mpr hevidence)]
  have hfactor :
      (δ + δm - 2 * γ) * (δ + δm + 2 * γ) =
        (δ - δm) ^ 2 + 4 * (δ * δm - γ ^ 2) := by
    ring
  have hmul : 0 < (δ + δm - 2 * γ) * (δ + δm + 2 * γ) := by
    rw [hfactor]
    exact hright
  have hsecond : 0 < δ + δm + 2 * γ := by nlinarith
  rcases (mul_pos_iff.mp hmul) with h | h
  · exact h.1
  · exact (not_lt_of_ge hsecond.le h.2).elim

/--
Paper I, proof of Lemma 4.12 (`lem:mse`): the paper's correlation-free dilution
threshold is no larger than the true MSE-optimal evidence weight.
-/
theorem auditThreshold_le_optimalWeight {δ δm γ : ℝ} (hδm : 0 ≤ δm) (hδ : 0 ≤ δ)
    (hevidence : δm < δ) (hγ : 0 ≤ γ) (hγbound : γ ≤ √(δm * δ)) :
    δ / (δ + δm) ≤ (δ - γ) / (δ + δm - 2 * γ) := by
  have hsum : 0 < δ + δm := by nlinarith
  have ha : 0 < δ + δm - 2 * γ :=
    mseQuadratic_coefficient_pos hδm hδ hevidence hγ hγbound
  rw [div_le_div_iff₀ hsum ha]
  nlinarith [mul_nonneg hγ (sub_nonneg.mpr hevidence.le)]

/--
Paper I, proof of Lemma 4.12 (`lem:mse`): the MSE quadratic is strictly decreasing
as evidence weight rises up to its unique minimizer.
-/
theorem mseQuadratic_strictAnti_below_optimal {δ δm γ w1 w2 : ℝ}
    (ha : 0 < δ + δm - 2 * γ) (hw : w1 < w2)
    (hw2 : w2 ≤ (δ - γ) / (δ + δm - 2 * γ)) :
    mseQuadratic δ δm γ w2 < mseQuadratic δ δm γ w1 := by
  have hlinear : w2 * (δ + δm - 2 * γ) ≤ δ - γ :=
    (le_div_iff₀ ha).mp hw2
  have hbracket :
      (δ + δm - 2 * γ) * (w1 + w2) - 2 * (δ - γ) < 0 := by
    nlinarith
  have hfactor :
      mseQuadratic δ δm γ w1 - mseQuadratic δ δm γ w2 =
        (w1 - w2) *
          ((δ + δm - 2 * γ) * (w1 + w2) - 2 * (δ - γ)) := by
    simp only [mseQuadratic]
    ring
  have hpositive :
      0 < (w1 - w2) *
        ((δ + δm - 2 * γ) * (w1 + w2) - 2 * (δ - γ)) :=
    mul_pos_of_neg_of_neg (sub_neg.mpr hw) hbracket
  nlinarith [hfactor]

/-! ## Type and population monotonicity -/

/-- Evidence weight with baseline response `η` and de-anchoring rate factor `r`. -/
def affineEvidenceWeight (η r β : ℝ) : ℝ :=
  η * (1 - r * β)

/-- A type's MSE quadratic evaluated along its affine evidence-weight path. -/
def typeMSE (δ δm γ η r β : ℝ) : ℝ :=
  mseQuadratic δ δm γ (affineEvidenceWeight η r β)

/-- Paper I's low-literacy MSE path, for which the rate factor is one. -/
def lowTypeMSE (δL δm γL ηL β : ℝ) : ℝ :=
  typeMSE δL δm γL ηL 1 β

/-- Paper I's high-literacy MSE path, attenuated by extraction advantage `κ`. -/
def highTypeMSE (δH δm γH ηH κ β : ℝ) : ℝ :=
  typeMSE δH δm γH ηH (1 - κ) β

/-- Paper I's population-weighted accuracy loss. -/
def populationAccuracyLoss (πH πL δH δL δm γH γL ηH ηL κ β : ℝ) : ℝ :=
  πH * highTypeMSE δH δm γH ηH κ β + πL * lowTypeMSE δL δm γL ηL β

/-- The paper's strictly positive type proportions summing to one. -/
structure PopulationShares (πH πL : ℝ) : Prop where
  πH_pos : 0 < πH
  πL_pos : 0 < πL
  sum_eq_one : πH + πL = 1

/--
Paper I, proof of Lemma 4.12 (`lem:mse`): any positive affine loss of evidence
weight makes the type MSE strictly increase throughout the policy interval.
-/
theorem typeMSE_strictMonoOn {δ δm γ η r : ℝ} (hδm : 0 ≤ δm) (hδ : 0 ≤ δ)
    (hevidence : δm < δ) (hγ : 0 ≤ γ) (hγbound : γ ≤ √(δm * δ))
    (hη : 0 < η) (hr : 0 < r) (hdilution : η ≤ δ / (δ + δm)) :
    StrictMonoOn (typeMSE δ δm γ η r) (Icc (0 : ℝ) 1) := by
  have ha : 0 < δ + δm - 2 * γ :=
    mseQuadratic_coefficient_pos hδm hδ hevidence hγ hγbound
  have hthreshold : δ / (δ + δm) ≤ (δ - γ) / (δ + δm - 2 * γ) :=
    auditThreshold_le_optimalWeight hδm hδ hevidence hγ hγbound
  intro β1 hβ1 β2 hβ2 hβ
  have hweight : affineEvidenceWeight η r β2 < affineEvidenceWeight η r β1 := by
    simp only [affineEvidenceWeight]
    nlinarith [mul_pos hη hr]
  have hbaseline : affineEvidenceWeight η r β1 ≤ η := by
    simp only [affineEvidenceWeight]
    have hnonneg : 0 ≤ η * r * β1 := mul_nonneg (mul_nonneg hη.le hr.le) hβ1.1
    nlinarith
  exact mseQuadratic_strictAnti_below_optimal ha hweight
    (hbaseline.trans (hdilution.trans hthreshold))

/--
Paper I, Lemma 4.12 (`lem:mse`), civic_alignment.tex:276.  Low-type MSE is strictly
increasing, high-type MSE is non-decreasing and is strict exactly when
`κ < 1`, and the population accuracy loss is strictly increasing.
-/
theorem mse_monotonicity {δm δH δL γH γL ηH ηL κ πH πL : ℝ}
    (hδm : 0 ≤ δm) (hδH : 0 ≤ δH) (hδL : 0 ≤ δL)
    (hγH : 0 ≤ γH) (hγL : 0 ≤ γL)
    (hγHbound : γH ≤ √(δm * δH)) (hγLbound : γL ≤ √(δm * δL))
    (evidence : EvidenceAssumption δm δH δL)
    (reliance : RelianceAssumption ηH ηL) (extraction : ExtractionAssumption κ)
    (dilution : DilutionAssumption δm δH δL ηH ηL)
    (shares : PopulationShares πH πL) :
    StrictMonoOn (lowTypeMSE δL δm γL ηL) (Icc (0 : ℝ) 1) ∧
      MonotoneOn (highTypeMSE δH δm γH ηH κ) (Icc (0 : ℝ) 1) ∧
      (StrictMonoOn (highTypeMSE δH δm γH ηH κ) (Icc (0 : ℝ) 1) ↔ κ < 1) ∧
      StrictMonoOn
        (populationAccuracyLoss πH πL δH δL δm γH γL ηH ηL κ) (Icc (0 : ℝ) 1) := by
  have hL : StrictMonoOn (lowTypeMSE δL δm γL ηL) (Icc (0 : ℝ) 1) := by
    change StrictMonoOn (typeMSE δL δm γL ηL 1) (Icc (0 : ℝ) 1)
    exact typeMSE_strictMonoOn hδm hδL evidence.δm_lt_δL hγL hγLbound
      reliance.ηL_pos zero_lt_one dilution.ηL_le
  have hHstrict (hκ : κ < 1) :
      StrictMonoOn (highTypeMSE δH δm γH ηH κ) (Icc (0 : ℝ) 1) := by
    change StrictMonoOn (typeMSE δH δm γH ηH (1 - κ)) (Icc (0 : ℝ) 1)
    exact typeMSE_strictMonoOn hδm hδH evidence.δm_lt_δH hγH hγHbound
      reliance.ηH_pos (sub_pos.mpr hκ) dilution.ηH_le
  have hH : MonotoneOn (highTypeMSE δH δm γH ηH κ) (Icc (0 : ℝ) 1) := by
    intro β1 hβ1 β2 hβ2 hβ
    rcases hβ.eq_or_lt with rfl | hβlt
    · exact le_rfl
    · by_cases hκ : κ < 1
      · exact (hHstrict hκ hβ1 hβ2 hβlt).le
      · have hκeq : κ = 1 := le_antisymm extraction.κ_le_one (le_of_not_gt hκ)
        simp only [highTypeMSE, typeMSE, affineEvidenceWeight, hκeq, sub_self, zero_mul,
          sub_zero]
        exact le_rfl
  have hHiff :
      StrictMonoOn (highTypeMSE δH δm γH ηH κ) (Icc (0 : ℝ) 1) ↔ κ < 1 := by
    constructor
    · intro hstrict
      by_contra hκ
      have hκeq : κ = 1 := le_antisymm extraction.κ_le_one (le_of_not_gt hκ)
      have h01 := hstrict (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
        (show (1 : ℝ) ∈ Icc 0 1 by norm_num) zero_lt_one
      have hconstant :
          highTypeMSE δH δm γH ηH κ 0 = highTypeMSE δH δm γH ηH κ 1 := by
        simp only [highTypeMSE, typeMSE, affineEvidenceWeight, hκeq, sub_self, zero_mul,
          mul_zero, sub_zero]
      exact (ne_of_lt h01) hconstant
    · exact hHstrict
  have hPopulation : StrictMonoOn
      (populationAccuracyLoss πH πL δH δL δm γH γL ηH ηL κ) (Icc (0 : ℝ) 1) := by
    intro β1 hβ1 β2 hβ2 hβ
    have hLow := hL hβ1 hβ2 hβ
    have hHigh := hH hβ1 hβ2 hβ.le
    have hLowWeighted := mul_lt_mul_of_pos_left hLow shares.πL_pos
    have hHighWeighted := mul_le_mul_of_nonneg_left hHigh shares.πH_pos.le
    simp only [populationAccuracyLoss]
    linarith
  exact ⟨hL, hH, hHiff, hPopulation⟩

/-! ## Within-type fragmentation -/

/-- The residual-prior multiplier squared in Paper I's conditional variance. -/
def residualVarianceFactor (η r β : ℝ) : ℝ :=
  (1 - affineEvidenceWeight η r β) ^ 2

/-- The residual-variance factor is non-decreasing as deference rises. -/
theorem residualVarianceFactor_monotoneOn {η r : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hr : 0 ≤ r) : MonotoneOn (residualVarianceFactor η r) (Icc (0 : ℝ) 1) := by
  intro β1 hβ1 β2 hβ2 hβ
  have hweight : affineEvidenceWeight η r β2 ≤ affineEvidenceWeight η r β1 := by
    simp only [affineEvidenceWeight]
    nlinarith [mul_nonneg hη.le hr]
  have hweight1 : affineEvidenceWeight η r β1 ≤ η := by
    simp only [affineEvidenceWeight]
    have hnonneg : 0 ≤ η * r * β1 := mul_nonneg (mul_nonneg hη.le hr) hβ1.1
    nlinarith
  have hweight2 : affineEvidenceWeight η r β2 ≤ η := by
    simp only [affineEvidenceWeight]
    have hnonneg : 0 ≤ η * r * β2 := mul_nonneg (mul_nonneg hη.le hr) hβ2.1
    nlinarith
  apply (sq_le_sq₀ (by linarith [hweight1]) (by linarith [hweight2])).2
  simpa only [residualVarianceFactor] using sub_le_sub_left hweight 1

/-- A positive de-anchoring rate makes the residual-variance factor strictly increasing. -/
theorem residualVarianceFactor_strictMonoOn {η r : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hr : 0 < r) : StrictMonoOn (residualVarianceFactor η r) (Icc (0 : ℝ) 1) := by
  intro β1 hβ1 β2 hβ2 hβ
  have hweight : affineEvidenceWeight η r β2 < affineEvidenceWeight η r β1 := by
    simp only [affineEvidenceWeight]
    nlinarith [mul_pos hη hr]
  have hweight1 : affineEvidenceWeight η r β1 ≤ η := by
    simp only [affineEvidenceWeight]
    have hnonneg : 0 ≤ η * r * β1 := mul_nonneg (mul_nonneg hη.le hr.le) hβ1.1
    nlinarith
  have hweight2 : affineEvidenceWeight η r β2 ≤ η := by
    simp only [affineEvidenceWeight]
    have hnonneg : 0 ≤ η * r * β2 := mul_nonneg (mul_nonneg hη.le hr.le) hβ2.1
    nlinarith
  apply (sq_lt_sq₀ (by linarith [hweight1]) (by linarith [hweight2])).2
  exact sub_lt_sub_left hweight 1

/-- Paper I's within-type fragmentation term `W(β)`. -/
def withinTypeDispersion (πH πL σH2 σL2 ηH ηL κ β : ℝ) : ℝ :=
  (πH * σH2) * residualVarianceFactor ηH (1 - κ) β +
    (πL * σL2) * residualVarianceFactor ηL 1 β

/--
Paper I, Lemma 4.14 (`lem:within`), civic_alignment.tex:302.  Within-type
fragmentation is non-decreasing; either stated positive-variance condition makes
it strictly increasing.
-/
theorem within_fragmentation_monotonicity {πH πL σH2 σL2 ηH ηL κ : ℝ}
    (hσH2 : 0 ≤ σH2) (hσL2 : 0 ≤ σL2) (reliance : RelianceAssumption ηH ηL)
    (extraction : ExtractionAssumption κ) (shares : PopulationShares πH πL) :
    MonotoneOn (withinTypeDispersion πH πL σH2 σL2 ηH ηL κ) (Icc (0 : ℝ) 1) ∧
      ((0 < σL2 ∨ (κ < 1 ∧ 0 < σH2)) →
        StrictMonoOn (withinTypeDispersion πH πL σH2 σL2 ηH ηL κ)
          (Icc (0 : ℝ) 1)) := by
  have hLowMono := residualVarianceFactor_monotoneOn reliance.ηL_pos
    reliance.ηL_le_one (show (0 : ℝ) ≤ 1 by norm_num)
  have hHighMono := residualVarianceFactor_monotoneOn reliance.ηH_pos
    reliance.ηH_le_one (sub_nonneg.mpr extraction.κ_le_one)
  have hMono : MonotoneOn
      (withinTypeDispersion πH πL σH2 σL2 ηH ηL κ) (Icc (0 : ℝ) 1) := by
    intro β1 hβ1 β2 hβ2 hβ
    have hL := hLowMono hβ1 hβ2 hβ
    have hH := hHighMono hβ1 hβ2 hβ
    have hLw := mul_le_mul_of_nonneg_left hL (mul_nonneg shares.πL_pos.le hσL2)
    have hHw := mul_le_mul_of_nonneg_left hH (mul_nonneg shares.πH_pos.le hσH2)
    simp only [withinTypeDispersion]
    linarith
  refine ⟨hMono, ?_⟩
  rintro (hσL2pos | ⟨hκ, hσH2pos⟩)
  · have hLowStrict := residualVarianceFactor_strictMonoOn reliance.ηL_pos
      reliance.ηL_le_one (show (0 : ℝ) < 1 by norm_num)
    intro β1 hβ1 β2 hβ2 hβ
    have hL := hLowStrict hβ1 hβ2 hβ
    have hH := hHighMono hβ1 hβ2 hβ.le
    have hLw := mul_lt_mul_of_pos_left hL (mul_pos shares.πL_pos hσL2pos)
    have hHw := mul_le_mul_of_nonneg_left hH (mul_nonneg shares.πH_pos.le hσH2)
    simp only [withinTypeDispersion]
    linarith
  · have hHighStrict := residualVarianceFactor_strictMonoOn reliance.ηH_pos
      reliance.ηH_le_one (sub_pos.mpr hκ)
    intro β1 hβ1 β2 hβ2 hβ
    have hL := hLowMono hβ1 hβ2 hβ.le
    have hH := hHighStrict hβ1 hβ2 hβ
    have hLw := mul_le_mul_of_nonneg_left hL (mul_nonneg shares.πL_pos.le hσL2)
    have hHw := mul_lt_mul_of_pos_left hH (mul_pos shares.πH_pos hσH2pos)
    simp only [withinTypeDispersion]
    linarith

/-! ## Between-type stratification -/

/-- Paper I's post-update difference between the high- and low-type means. -/
def meanGap (ηH ηL κ m μH μL β : ℝ) : ℝ :=
  beliefAtWeight (affineEvidenceWeight ηH (1 - κ) β) m μH -
    beliefAtWeight (affineEvidenceWeight ηL 1 β) m μL

/-- The constant slope in Paper I's affine gap formula. -/
def meanGapSlope (ηH ηL κ m μH μL : ℝ) : ℝ :=
  (1 - κ) * ηH * (μH - m) + ηL * (m - μL)

/-- Paper I, displayed formula in `lem:gap`. -/
theorem meanGap_eq (ηH ηL κ m μH μL β : ℝ) :
    meanGap ηH ηL κ m μH μL β =
      (1 - affineEvidenceWeight ηH (1 - κ) β) * (μH - m) -
        (1 - affineEvidenceWeight ηL 1 β) * (μL - m) := by
  simp only [meanGap, beliefAtWeight, affineEvidenceWeight]
  ring

/-- Paper I, affine form used in the proof of `lem:gap`. -/
theorem meanGap_affine (ηH ηL κ m μH μL β : ℝ) :
    meanGap ηH ηL κ m μH μL β =
      meanGap ηH ηL κ m μH μL 0 + meanGapSlope ηH ηL κ m μH μL * β := by
  simp only [meanGap, meanGapSlope, beliefAtWeight, affineEvidenceWeight]
  ring

/-- Paper I, derivative formula displayed in `lem:gap`. -/
theorem hasDerivAt_meanGap (ηH ηL κ m μH μL β : ℝ) :
    HasDerivAt (meanGap ηH ηL κ m μH μL) (meanGapSlope ηH ηL κ m μH μL) β := by
  have h := (hasDerivAt_id β).const_mul (meanGapSlope ηH ηL κ m μH μL)
  have h' := h.const_add (meanGap ηH ηL κ m μH μL 0)
  convert! h' using 1
  · funext x
    rw [meanGap_affine]
    rfl
  · ring

/--
Paper I, Lemma 4.15 (`lem:gap`), civic_alignment.tex:310.  The gap and its slope
have matching orientation in either branch of the straddle assumption; hence
its absolute value and square strictly increase on `[0,1]`.
-/
theorem stratification_gap_widens {ηH ηL κ m μH μL : ℝ}
    (straddle : StraddleAssumption m μH μL) (reliance : RelianceAssumption ηH ηL)
    (extraction : ExtractionAssumption κ) :
    (∀ β, meanGap ηH ηL κ m μH μL β =
      (1 - affineEvidenceWeight ηH (1 - κ) β) * (μH - m) -
        (1 - affineEvidenceWeight ηL 1 β) * (μL - m)) ∧
      (∀ β, HasDerivAt (meanGap ηH ηL κ m μH μL)
        (meanGapSlope ηH ηL κ m μH μL) β) ∧
      (((μL < m ∧ m < μH) ∧
          (∀ β ∈ Icc (0 : ℝ) 1, 0 ≤ meanGap ηH ηL κ m μH μL β) ∧
          0 < meanGapSlope ηH ηL κ m μH μL) ∨
        ((μH < m ∧ m < μL) ∧
          (∀ β ∈ Icc (0 : ℝ) 1, meanGap ηH ηL κ m μH μL β ≤ 0) ∧
          meanGapSlope ηH ηL κ m μH μL < 0)) ∧
      StrictMonoOn (fun β => |meanGap ηH ηL κ m μH μL β|) (Icc (0 : ℝ) 1) ∧
      StrictMonoOn (fun β => meanGap ηH ηL κ m μH μL β ^ 2) (Icc (0 : ℝ) 1) := by
  have hformula : ∀ β, meanGap ηH ηL κ m μH μL β =
      (1 - affineEvidenceWeight ηH (1 - κ) β) * (μH - m) -
        (1 - affineEvidenceWeight ηL 1 β) * (μL - m) :=
    meanGap_eq ηH ηL κ m μH μL
  have hderiv : ∀ β, HasDerivAt (meanGap ηH ηL κ m μH μL)
      (meanGapSlope ηH ηL κ m μH μL) β :=
    hasDerivAt_meanGap ηH ηL κ m μH μL
  have hHighResidual : ∀ β ∈ Icc (0 : ℝ) 1,
      0 ≤ 1 - affineEvidenceWeight ηH (1 - κ) β := by
    intro β hβ
    have hnonneg : 0 ≤ ηH * (1 - κ) * β :=
      mul_nonneg (mul_nonneg reliance.ηH_pos.le (sub_nonneg.mpr extraction.κ_le_one)) hβ.1
    simp only [affineEvidenceWeight]
    nlinarith [reliance.ηH_le_one]
  have hLowResidual : ∀ β ∈ Icc (0 : ℝ) 1,
      0 ≤ 1 - affineEvidenceWeight ηL 1 β := by
    intro β hβ
    have hnonneg : 0 ≤ ηL * 1 * β :=
      mul_nonneg (mul_nonneg reliance.ηL_pos.le zero_le_one) hβ.1
    simp only [affineEvidenceWeight]
    nlinarith [reliance.ηL_le_one]
  rcases straddle.ordering with horder | horder
  · have hslope : 0 < meanGapSlope ηH ηL κ m μH μL := by
      have hfirst : 0 ≤ (1 - κ) * ηH * (μH - m) :=
        mul_nonneg (mul_nonneg (sub_nonneg.mpr extraction.κ_le_one) reliance.ηH_pos.le)
          (sub_nonneg.mpr horder.2.le)
      have hsecond : 0 < ηL * (m - μL) :=
        mul_pos reliance.ηL_pos (sub_pos.mpr horder.1)
      simp only [meanGapSlope]
      linarith
    have hgap : ∀ β ∈ Icc (0 : ℝ) 1, 0 ≤ meanGap ηH ηL κ m μH μL β := by
      intro β hβ
      rw [hformula]
      have hfirst := mul_nonneg (hHighResidual β hβ) (sub_nonneg.mpr horder.2.le)
      have hsecond := mul_nonneg (hLowResidual β hβ) (sub_nonneg.mpr horder.1.le)
      nlinarith
    have habs : StrictMonoOn (fun β => |meanGap ηH ηL κ m μH μL β|)
        (Icc (0 : ℝ) 1) := by
      intro β1 hβ1 β2 hβ2 hβ
      have hgaplt : meanGap ηH ηL κ m μH μL β1 <
          meanGap ηH ηL κ m μH μL β2 := by
        nlinarith [meanGap_affine ηH ηL κ m μH μL β1,
          meanGap_affine ηH ηL κ m μH μL β2,
          mul_pos hslope (sub_pos.mpr hβ)]
      change |meanGap ηH ηL κ m μH μL β1| < |meanGap ηH ηL κ m μH μL β2|
      rw [abs_of_nonneg (hgap β1 hβ1), abs_of_nonneg (hgap β2 hβ2)]
      exact hgaplt
    have hsq : StrictMonoOn (fun β => meanGap ηH ηL κ m μH μL β ^ 2)
        (Icc (0 : ℝ) 1) := by
      intro β1 hβ1 β2 hβ2 hβ
      have hgaplt : meanGap ηH ηL κ m μH μL β1 <
          meanGap ηH ηL κ m μH μL β2 := by
        nlinarith [meanGap_affine ηH ηL κ m μH μL β1,
          meanGap_affine ηH ηL κ m μH μL β2,
          mul_pos hslope (sub_pos.mpr hβ)]
      exact (sq_lt_sq₀ (hgap β1 hβ1) (hgap β2 hβ2)).2 hgaplt
    exact ⟨hformula, hderiv, Or.inl ⟨horder, hgap, hslope⟩, habs, hsq⟩
  · have hslope : meanGapSlope ηH ηL κ m μH μL < 0 := by
      have hfirst : (1 - κ) * ηH * (μH - m) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg (sub_nonneg.mpr extraction.κ_le_one) reliance.ηH_pos.le)
          (sub_nonpos.mpr horder.1.le)
      have hsecond : ηL * (m - μL) < 0 :=
        mul_neg_of_pos_of_neg reliance.ηL_pos (sub_neg.mpr horder.2)
      simp only [meanGapSlope]
      linarith
    have hgap : ∀ β ∈ Icc (0 : ℝ) 1, meanGap ηH ηL κ m μH μL β ≤ 0 := by
      intro β hβ
      rw [hformula]
      have hfirst := mul_nonpos_of_nonneg_of_nonpos (hHighResidual β hβ)
        (sub_nonpos.mpr horder.1.le)
      have hsecond := mul_nonneg (hLowResidual β hβ) (sub_nonneg.mpr horder.2.le)
      linarith
    have habs : StrictMonoOn (fun β => |meanGap ηH ηL κ m μH μL β|)
        (Icc (0 : ℝ) 1) := by
      intro β1 hβ1 β2 hβ2 hβ
      have hgaplt : meanGap ηH ηL κ m μH μL β2 <
          meanGap ηH ηL κ m μH μL β1 := by
        nlinarith [meanGap_affine ηH ηL κ m μH μL β1,
          meanGap_affine ηH ηL κ m μH μL β2,
          mul_neg_of_neg_of_pos hslope (sub_pos.mpr hβ)]
      change |meanGap ηH ηL κ m μH μL β1| < |meanGap ηH ηL κ m μH μL β2|
      rw [abs_of_nonpos (hgap β1 hβ1), abs_of_nonpos (hgap β2 hβ2)]
      linarith
    have hsq : StrictMonoOn (fun β => meanGap ηH ηL κ m μH μL β ^ 2)
        (Icc (0 : ℝ) 1) := by
      intro β1 hβ1 β2 hβ2 hβ
      have hgaplt : -meanGap ηH ηL κ m μH μL β1 <
          -meanGap ηH ηL κ m μH μL β2 := by
        nlinarith [meanGap_affine ηH ηL κ m μH μL β1,
          meanGap_affine ηH ηL κ m μH μL β2,
          mul_neg_of_neg_of_pos hslope (sub_pos.mpr hβ)]
      have hsquare := (sq_lt_sq₀ (neg_nonneg.mpr (hgap β1 hβ1))
        (neg_nonneg.mpr (hgap β2 hβ2))).2 hgaplt
      nlinarith
    exact ⟨hformula, hderiv, Or.inr ⟨horder, hgap, hslope⟩, habs, hsq⟩

/-! ## Total belief variance -/

/-- Cross-sectional variance of a two-type mixture from conditional means and variances. -/
def twoTypeVariance (πH πL varianceH varianceL meanH meanL : ℝ) : ℝ :=
  let mean := πH * meanH + πL * meanL
  πH * (varianceH + (meanH - mean) ^ 2) + πL * (varianceL + (meanL - mean) ^ 2)

/--
Paper I, law of total variance used by `cor:totalvar`: the between-type variance
of a two-component mixture is `πH * πL` times the squared mean gap.
-/
theorem twoTypeVariance_decomposition {πH πL varianceH varianceL meanH meanL : ℝ}
    (shares : PopulationShares πH πL) :
    twoTypeVariance πH πL varianceH varianceL meanH meanL =
      πH * varianceH + πL * varianceL + πH * πL * (meanH - meanL) ^ 2 := by
  have hπL : πL = 1 - πH := by linarith [shares.sum_eq_one]
  rw [hπL]
  simp only [twoTypeVariance]
  ring

/-- High-type post-update mean. -/
def highUpdatedMean (ηH κ m μH β : ℝ) : ℝ :=
  beliefAtWeight (affineEvidenceWeight ηH (1 - κ) β) m μH

/-- Low-type post-update mean. -/
def lowUpdatedMean (ηL m μL β : ℝ) : ℝ :=
  beliefAtWeight (affineEvidenceWeight ηL 1 β) m μL

/-- The total variance of post-update beliefs, before applying the decomposition. -/
def totalBeliefVariance (πH πL σH2 σL2 ηH ηL κ m μH μL β : ℝ) : ℝ :=
  twoTypeVariance πH πL
    (residualVarianceFactor ηH (1 - κ) β * σH2)
    (residualVarianceFactor ηL 1 β * σL2)
    (highUpdatedMean ηH κ m μH β) (lowUpdatedMean ηL m μL β)

/-- Paper I, the displayed total-variance decomposition specialized to the update model. -/
theorem totalBeliefVariance_eq {πH πL σH2 σL2 ηH ηL κ m μH μL β : ℝ}
    (shares : PopulationShares πH πL) :
    totalBeliefVariance πH πL σH2 σL2 ηH ηL κ m μH μL β =
      withinTypeDispersion πH πL σH2 σL2 ηH ηL κ β +
        πH * πL * meanGap ηH ηL κ m μH μL β ^ 2 := by
  rw [totalBeliefVariance, twoTypeVariance_decomposition shares]
  simp only [withinTypeDispersion, highUpdatedMean, lowUpdatedMean, meanGap]
  ring

/--
Paper I, Corollary 4.17 (`cor:totalvar`), civic_alignment.tex:328.  Total
cross-sectional belief variance is strictly increasing throughout `[0,1]`.
-/
theorem total_variance_increases {πH πL σH2 σL2 ηH ηL κ m μH μL : ℝ}
    (hσH2 : 0 ≤ σH2) (hσL2 : 0 ≤ σL2) (straddle : StraddleAssumption m μH μL)
    (reliance : RelianceAssumption ηH ηL) (extraction : ExtractionAssumption κ)
    (shares : PopulationShares πH πL) :
    (∀ β, totalBeliefVariance πH πL σH2 σL2 ηH ηL κ m μH μL β =
      withinTypeDispersion πH πL σH2 σL2 ηH ηL κ β +
        πH * πL * meanGap ηH ηL κ m μH μL β ^ 2) ∧
      StrictMonoOn (totalBeliefVariance πH πL σH2 σL2 ηH ηL κ m μH μL)
        (Icc (0 : ℝ) 1) := by
  have hdecomp : ∀ β, totalBeliefVariance πH πL σH2 σL2 ηH ηL κ m μH μL β =
      withinTypeDispersion πH πL σH2 σL2 ηH ηL κ β +
        πH * πL * meanGap ηH ηL κ m μH μL β ^ 2 :=
    fun _ => totalBeliefVariance_eq shares
  have hWithin :=
    (within_fragmentation_monotonicity hσH2 hσL2 reliance extraction shares).1
  have hGap := (stratification_gap_widens straddle reliance extraction).2.2.2.2
  refine ⟨hdecomp, ?_⟩
  intro β1 hβ1 β2 hβ2 hβ
  have hW := hWithin hβ1 hβ2 hβ.le
  have hG := hGap hβ1 hβ2 hβ
  have hGweighted := mul_lt_mul_of_pos_left hG (mul_pos shares.πH_pos shares.πL_pos)
  rw [hdecomp, hdecomp]
  linarith

/-! ## Exact scope counterexample -/

/--
Paper I, Remark `rem:counter`, civic_alignment.tex:324.  At the paper's exact
rational parameters, every numbered assumption except straddling holds, the gap
is `1/20 - (3/40)β`, and both its magnitude and total variance strictly fall
until the gap vanishes at `β = 2/3`.
-/
theorem sameSide_counterexample :
    EvidenceAssumption (1 / 100 : ℝ) (9 / 25) (1 / 4) ∧
      RelianceAssumption (1 / 2 : ℝ) (1 / 2) ∧
      ExtractionAssumption (1 / 2 : ℝ) ∧
      DilutionAssumption (1 / 100 : ℝ) (9 / 25) (1 / 4) (1 / 2) (1 / 2) ∧
      (∀ β : ℝ, meanGap (1 / 2) (1 / 2) (1 / 2) (1 / 10) (3 / 5) (1 / 2) β =
        1 / 20 - (3 / 40) * β) ∧
      meanGap (1 / 2) (1 / 2) (1 / 2) (1 / 10) (3 / 5) (1 / 2) (2 / 3) = 0 ∧
      StrictAntiOn
        (fun β : ℝ =>
          |meanGap (1 / 2) (1 / 2) (1 / 2) (1 / 10) (3 / 5) (1 / 2) β|)
        (Icc (0 : ℝ) (2 / 3)) ∧
      StrictAntiOn
        (totalBeliefVariance (1 / 2) (1 / 2) 0 0 (1 / 2) (1 / 2) (1 / 2)
          (1 / 10) (3 / 5) (1 / 2)) (Icc (0 : ℝ) (2 / 3)) := by
  have hevidence : EvidenceAssumption (1 / 100 : ℝ) (9 / 25) (1 / 4) := by
    constructor <;> norm_num
  have hreliance : RelianceAssumption (1 / 2 : ℝ) (1 / 2) := by
    constructor <;> norm_num
  have hextraction : ExtractionAssumption (1 / 2 : ℝ) := by
    constructor <;> norm_num
  have hdilution :
      DilutionAssumption (1 / 100 : ℝ) (9 / 25) (1 / 4) (1 / 2) (1 / 2) := by
    constructor <;> norm_num
  have hformula : ∀ β : ℝ,
      meanGap (1 / 2) (1 / 2) (1 / 2) (1 / 10) (3 / 5) (1 / 2) β =
        1 / 20 - (3 / 40) * β := by
    intro β
    simp only [meanGap, beliefAtWeight, affineEvidenceWeight]
    ring
  have hzero :
      meanGap (1 / 2) (1 / 2) (1 / 2) (1 / 10) (3 / 5) (1 / 2) (2 / 3) = 0 := by
    rw [hformula]
    norm_num
  have habs : StrictAntiOn
      (fun β : ℝ =>
        |meanGap (1 / 2) (1 / 2) (1 / 2) (1 / 10) (3 / 5) (1 / 2) β|)
      (Icc (0 : ℝ) (2 / 3)) := by
    intro β1 hβ1 β2 hβ2 hβ
    have hgap1 : 0 ≤ meanGap (1 / 2) (1 / 2) (1 / 2) (1 / 10) (3 / 5) (1 / 2) β1 := by
      rw [hformula]
      norm_num at hβ1 ⊢
      linarith
    have hgap2 : 0 ≤ meanGap (1 / 2) (1 / 2) (1 / 2) (1 / 10) (3 / 5) (1 / 2) β2 := by
      rw [hformula]
      norm_num at hβ2 ⊢
      linarith
    have hdecrease :
        meanGap (1 / 2) (1 / 2) (1 / 2) (1 / 10) (3 / 5) (1 / 2) β2 <
          meanGap (1 / 2) (1 / 2) (1 / 2) (1 / 10) (3 / 5) (1 / 2) β1 := by
      rw [hformula, hformula]
      norm_num
      linarith
    change
      |meanGap (1 / 2) (1 / 2) (1 / 2) (1 / 10) (3 / 5) (1 / 2) β2| <
        |meanGap (1 / 2) (1 / 2) (1 / 2) (1 / 10) (3 / 5) (1 / 2) β1|
    rw [abs_of_nonneg hgap2, abs_of_nonneg hgap1]
    exact hdecrease
  have shares : PopulationShares (1 / 2 : ℝ) (1 / 2) := by
    constructor <;> norm_num
  have htotal : ∀ β : ℝ,
      totalBeliefVariance (1 / 2) (1 / 2) 0 0 (1 / 2) (1 / 2) (1 / 2)
          (1 / 10) (3 / 5) (1 / 2) β =
        (1 / 4) *
          meanGap (1 / 2) (1 / 2) (1 / 2) (1 / 10) (3 / 5) (1 / 2) β ^ 2 := by
    intro β
    rw [totalBeliefVariance_eq shares]
    norm_num [withinTypeDispersion]
  have htotalAnti : StrictAntiOn
      (totalBeliefVariance (1 / 2) (1 / 2) 0 0 (1 / 2) (1 / 2) (1 / 2)
        (1 / 10) (3 / 5) (1 / 2)) (Icc (0 : ℝ) (2 / 3)) := by
    intro β1 hβ1 β2 hβ2 hβ
    have hgap1 : 0 ≤ meanGap (1 / 2) (1 / 2) (1 / 2) (1 / 10) (3 / 5) (1 / 2) β1 := by
      rw [hformula]
      norm_num at hβ1 ⊢
      linarith
    have hgap2 : 0 ≤ meanGap (1 / 2) (1 / 2) (1 / 2) (1 / 10) (3 / 5) (1 / 2) β2 := by
      rw [hformula]
      norm_num at hβ2 ⊢
      linarith
    have hdecrease :
        meanGap (1 / 2) (1 / 2) (1 / 2) (1 / 10) (3 / 5) (1 / 2) β2 <
          meanGap (1 / 2) (1 / 2) (1 / 2) (1 / 10) (3 / 5) (1 / 2) β1 := by
      rw [hformula, hformula]
      norm_num
      linarith
    have hsquare := (sq_lt_sq₀ hgap2 hgap1).2 hdecrease
    rw [htotal, htotal]
    nlinarith
  exact ⟨hevidence, hreliance, hextraction, hdilution, hformula, hzero, habs, htotalAnti⟩

/-! ## Main capacity theorem -/

/-- Paper I, equation `eq:capacity`: one-step collective epistemic capacity. -/
def collectiveCapacity (πH πL δH δL δm γH γL ηH ηL κ σH2 σL2 m μH μL
    lambda nu β : ℝ) : ℝ :=
  -populationAccuracyLoss πH πL δH δL δm γH γL ηH ηL κ β -
    lambda * withinTypeDispersion πH πL σH2 σL2 ηH ηL κ β -
    nu * meanGap ηH ηL κ m μH μL β ^ 2

/--
Paper I, Theorem 4.18 (`thm:main`), civic_alignment.tex:338, substantive half:
collective epistemic capacity is strictly decreasing.  This result is kept
separate from the reduced-form satisfaction-selection clause.
-/
theorem capacity_strictly_decreases
    {πH πL δH δL δm γH γL ηH ηL κ σH2 σL2 m μH μL lambda nu : ℝ}
    (hδm : 0 ≤ δm) (hδH : 0 ≤ δH) (hδL : 0 ≤ δL)
    (hγH : 0 ≤ γH) (hγL : 0 ≤ γL)
    (hγHbound : γH ≤ √(δm * δH)) (hγLbound : γL ≤ √(δm * δL))
    (hσH2 : 0 ≤ σH2) (hσL2 : 0 ≤ σL2) (hlambda : 0 ≤ lambda) (hnu : 0 ≤ nu)
    (evidence : EvidenceAssumption δm δH δL) (straddle : StraddleAssumption m μH μL)
    (reliance : RelianceAssumption ηH ηL) (extraction : ExtractionAssumption κ)
    (dilution : DilutionAssumption δm δH δL ηH ηL)
    (shares : PopulationShares πH πL) :
    StrictAntiOn
      (collectiveCapacity πH πL δH δL δm γH γL ηH ηL κ σH2 σL2 m μH μL
        lambda nu) (Icc (0 : ℝ) 1) := by
  have hAccuracy :=
    (mse_monotonicity hδm hδH hδL hγH hγL hγHbound hγLbound evidence reliance
      extraction dilution shares).2.2.2
  have hWithin :=
    (within_fragmentation_monotonicity hσH2 hσL2 reliance extraction shares).1
  have hGap := (stratification_gap_widens straddle reliance extraction).2.2.2.2
  intro β1 hβ1 β2 hβ2 hβ
  have hA := hAccuracy hβ1 hβ2 hβ
  have hW := hWithin hβ1 hβ2 hβ.le
  have hG := hGap hβ1 hβ2 hβ
  have hWweighted := mul_le_mul_of_nonneg_left hW hlambda
  have hGweighted := mul_le_mul_of_nonneg_left hG.le hnu
  simp only [collectiveCapacity]
  linarith

/--
Paper I, Assumption 4.9 (`ass:satisfaction`): a continuously differentiable
satisfaction objective has strictly positive derivative at the safe endpoint.
-/
structure SatisfactionAssumption (U : ℝ → ℝ) (UPrimeZero : ℝ) : Prop where
  continuouslyDifferentiable : ContDiffOn ℝ 1 U (Icc (0 : ℝ) 1)
  hasDerivAt_zero : HasDerivAt U UPrimeZero 0
  UPrimeZero_pos : 0 < UPrimeZero

/--
Paper I, Theorem 4.18 (`thm:main`), reduced-form half: Assumption 5 alone excludes
the safe endpoint as a constrained local maximizer of satisfaction.
-/
theorem satisfaction_localMax_positive {U : ℝ → ℝ} {UPrimeZero βstar : ℝ}
    (satisfaction : SatisfactionAssumption U UPrimeZero)
    (hβstar : βstar ∈ Icc (0 : ℝ) 1)
    (hmax : IsLocalMaxOn U (Icc (0 : ℝ) 1) βstar) : 0 < βstar := by
  by_contra hnot
  have hzero : βstar = 0 := le_antisymm (le_of_not_gt hnot) hβstar.1
  subst βstar
  have hdirection : (1 : ℝ) ∈ posTangentConeAt (Icc (0 : ℝ) 1) 0 :=
    mem_posTangentConeAt_of_segment_subset (by
      simpa only [zero_add] using
        (segment_subset_Icc (𝕜 := ℝ) (show (0 : ℝ) ≤ 1 from zero_le_one)))
  have hnonpos := hmax.hasFDerivWithinAt_nonpos
    satisfaction.hasDerivAt_zero.hasFDerivAt.hasFDerivWithinAt hdirection
  have : UPrimeZero ≤ 0 := by simpa using hnonpos
  linarith [satisfaction.UPrimeZero_pos]

/--
Paper I, Theorem 4.18 (`thm:main`), civic_alignment.tex:338: any constrained local
satisfaction maximizer has positive deference and strictly lower capacity than
the safe endpoint.
-/
theorem satisfaction_optimal_deference_harms
    {πH πL δH δL δm γH γL ηH ηL κ σH2 σL2 m μH μL lambda nu : ℝ}
    {U : ℝ → ℝ} {UPrimeZero βstar : ℝ}
    (hδm : 0 ≤ δm) (hδH : 0 ≤ δH) (hδL : 0 ≤ δL)
    (hγH : 0 ≤ γH) (hγL : 0 ≤ γL)
    (hγHbound : γH ≤ √(δm * δH)) (hγLbound : γL ≤ √(δm * δL))
    (hσH2 : 0 ≤ σH2) (hσL2 : 0 ≤ σL2) (hlambda : 0 ≤ lambda) (hnu : 0 ≤ nu)
    (evidence : EvidenceAssumption δm δH δL) (straddle : StraddleAssumption m μH μL)
    (reliance : RelianceAssumption ηH ηL) (extraction : ExtractionAssumption κ)
    (dilution : DilutionAssumption δm δH δL ηH ηL) (shares : PopulationShares πH πL)
    (satisfaction : SatisfactionAssumption U UPrimeZero)
    (hβstar : βstar ∈ Icc (0 : ℝ) 1)
    (hmax : IsLocalMaxOn U (Icc (0 : ℝ) 1) βstar) :
    0 < βstar ∧
      collectiveCapacity πH πL δH δL δm γH γL ηH ηL κ σH2 σL2 m μH μL
          lambda nu βstar <
        collectiveCapacity πH πL δH δL δm γH γL ηH ηL κ σH2 σL2 m μH μL
          lambda nu 0 := by
  have hpositive := satisfaction_localMax_positive satisfaction hβstar hmax
  have hcapacity := capacity_strictly_decreases hδm hδH hδL hγH hγL hγHbound
    hγLbound hσH2 hσL2 hlambda hnu evidence straddle reliance extraction dilution shares
  refine ⟨hpositive, ?_⟩
  exact hcapacity (show (0 : ℝ) ∈ Icc 0 1 by norm_num) hβstar hpositive

#print axioms error_product_nonnegative
#print axioms gamma_geometry
#print axioms mse_decomposition
#print axioms mseQuadratic_coefficient_pos
#print axioms auditThreshold_le_optimalWeight
#print axioms mseQuadratic_strictAnti_below_optimal
#print axioms typeMSE_strictMonoOn
#print axioms mse_monotonicity
#print axioms residualVarianceFactor_monotoneOn
#print axioms residualVarianceFactor_strictMonoOn
#print axioms within_fragmentation_monotonicity
#print axioms meanGap_eq
#print axioms meanGap_affine
#print axioms hasDerivAt_meanGap
#print axioms stratification_gap_widens
#print axioms twoTypeVariance_decomposition
#print axioms totalBeliefVariance_eq
#print axioms total_variance_increases
#print axioms sameSide_counterexample
#print axioms capacity_strictly_decreases
#print axioms satisfaction_localMax_positive
#print axioms satisfaction_optimal_deference_harms

end CivicAlignment.PaperI
