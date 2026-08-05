/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperI.Capacity
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Probability.Moments.Variance

/-!
# Repeated exposure and the horizon threshold

This file formalizes Paper II's repeated-exposure weight, the exact logarithmic
threshold, and the derivative-sign dichotomy. It also records the endpoint
counterexample at full responsiveness `η = 1`, which the paper's current
primitive range permits but its logarithmic theorem does not handle.
-/

namespace CivicAlignment.PaperII

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

/-- Evidence weight under a fixed policy, written with de-anchoring rate `r`. -/
def repeatedEvidenceWeight (η r β : ℝ) : ℝ :=
  η - r * β

/-- Effective evidence weight after `t` repeated exposures. -/
def effectiveHorizonWeight (η r : ℝ) (t : ℕ) (β : ℝ) : ℝ :=
  1 - (1 - repeatedEvidenceWeight η r β) ^ t

/-- The one-event MSE quadratic evaluated at the effective horizon weight. -/
def horizonMSE (δ δm γ η r : ℝ) (t : ℕ) (β : ℝ) : ℝ :=
  PaperI.mseQuadratic δ δm γ (effectiveHorizonWeight η r t β)

/-- The unique minimizer of the MSE quadratic when its leading coefficient is positive. -/
def horizonOptimalWeight (δ δm γ : ℝ) : ℝ :=
  (δ - γ) / (δ + δm - 2 * γ)

/-- Paper II equation `eq:Tstar`. -/
def horizonThreshold (η wStar : ℝ) : ℝ :=
  Real.log (1 - wStar) / Real.log (1 - η)

/-- The positive `t`-th root of the residual optimal weight `1 - wStar`. -/
def horizonResidualRoot (wStar : ℝ) (t : ℕ) : ℝ :=
  (1 - wStar) ^ ((t : ℝ)⁻¹)

/-- Paper II equation `eq:bstaracc`, for zero extraction. -/
def accuracyOptimalDeference (η wStar : ℝ) (t : ℕ) : ℝ :=
  1 - (1 - horizonResidualRoot wStar t) / η

/-- The derivative of the moment quadratic at an arbitrary evidence weight. -/
theorem hasDerivAt_mseQuadratic (δ δm γ w : ℝ) :
    HasDerivAt (PaperI.mseQuadratic δ δm γ)
      (2 * ((δ + δm - 2 * γ) * w - (δ - γ))) w := by
  change HasDerivAt
    (fun x : ℝ ↦ (1 - x) ^ 2 * δ + x ^ 2 * δm + 2 * (1 - x) * x * γ)
    (2 * ((δ + δm - 2 * γ) * w - (δ - γ))) w
  have hOneSub : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub (1 : ℝ)
  have hFirst := (hOneSub.pow 2).mul_const δ
  have hSecond := ((hasDerivAt_id w).pow 2).mul_const δm
  have hThird := ((hOneSub.mul (hasDerivAt_id w)).const_mul 2).mul_const γ
  have hraw := (hFirst.add hSecond).add hThird
  convert! hraw using 1
  · funext x
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
    ring
  · norm_num [id_eq]
    ring

/-- Derivative of the effective horizon weight with respect to deference. -/
theorem hasDerivAt_effectiveHorizonWeight (η r : ℝ) (t : ℕ) (β : ℝ) :
    HasDerivAt (effectiveHorizonWeight η r t)
      (-(t : ℝ) * r * (1 - repeatedEvidenceWeight η r β) ^ (t - 1)) β := by
  have hw : HasDerivAt (repeatedEvidenceWeight η r) (-r) β := by
    unfold repeatedEvidenceWeight
    (convert! (hasDerivAt_const β η).sub ((hasDerivAt_id β).const_mul r) using 1; ring)
  have hresidual :
      HasDerivAt (fun x ↦ 1 - repeatedEvidenceWeight η r x) r β := by
    simpa using hw.const_sub (1 : ℝ)
  change HasDerivAt (fun x ↦ 1 - (1 - repeatedEvidenceWeight η r x) ^ t)
    (-(t : ℝ) * r * (1 - repeatedEvidenceWeight η r β) ^ (t - 1)) β
  exact ((hresidual.pow t).const_sub (1 : ℝ)).congr_deriv (by ring)

/-- Exact derivative of repeated-exposure MSE. -/
theorem hasDerivAt_horizonMSE (δ δm γ η r : ℝ) (t : ℕ) (β : ℝ) :
    HasDerivAt (horizonMSE δ δm γ η r t)
      (2 * ((δ + δm - 2 * γ) * effectiveHorizonWeight η r t β - (δ - γ)) *
        (-(t : ℝ) * r * (1 - repeatedEvidenceWeight η r β) ^ (t - 1))) β := by
  exact (hasDerivAt_mseQuadratic δ δm γ (effectiveHorizonWeight η r t β)).comp β
    (hasDerivAt_effectiveHorizonWeight η r t β)

/-- The optimal weight lies above one exactly in the no-inversion regime. -/
theorem one_le_horizonOptimalWeight_iff {δ δm γ : ℝ}
    (ha : 0 < δ + δm - 2 * γ) :
    1 ≤ horizonOptimalWeight δ δm γ ↔ δm ≤ γ := by
  rw [horizonOptimalWeight]
  constructor
  · intro h
    have hcross := (le_div_iff₀ ha).mp h
    nlinarith
  · intro h
    apply (le_div_iff₀ ha).mpr
    nlinarith

/-- The optimal weight lies below one exactly in the inversion regime. -/
theorem horizonOptimalWeight_lt_one_iff {δ δm γ : ℝ}
    (ha : 0 < δ + δm - 2 * γ) :
    horizonOptimalWeight δ δm γ < 1 ↔ γ < δm := by
  rw [horizonOptimalWeight]
  constructor
  · intro h
    have hcross := (div_lt_iff₀ ha).mp h
    nlinarith
  · intro h
    apply (div_lt_iff₀ ha).mpr
    nlinarith

/-- Standard error geometry puts the inversion-regime optimum strictly inside `(0,1)`. -/
theorem horizonOptimalWeight_mem_Ioo {δ δm γ : ℝ}
    (hδm : 0 ≤ δm) (hδ : 0 ≤ δ) (hevidence : δm < δ)
    (hγ : 0 ≤ γ) (hγbound : γ ≤ Real.sqrt (δm * δ)) (hinversion : γ < δm) :
    horizonOptimalWeight δ δm γ ∈ Ioo (0 : ℝ) 1 := by
  have ha : 0 < δ + δm - 2 * γ :=
    PaperI.mseQuadratic_coefficient_pos hδm hδ hevidence hγ hγbound
  constructor
  · exact div_pos (by linarith) ha
  · exact (horizonOptimalWeight_lt_one_iff ha).2 hinversion

/-- The logarithmic threshold is positive when both responsiveness and the optimum are interior. -/
theorem horizonThreshold_pos {η wStar : ℝ}
    (hη : η ∈ Ioo (0 : ℝ) 1) (hw : wStar ∈ Ioo (0 : ℝ) 1) :
    0 < horizonThreshold η wStar := by
  have hresη : 1 - η ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hη.1, hη.2]
  have hresw : 1 - wStar ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hw.1, hw.2]
  exact div_pos_of_neg_of_neg (Real.log_neg hresw.1 hresw.2)
    (Real.log_neg hresη.1 hresη.2)

/-- Before the log threshold, the baseline effective weight remains below the optimum. -/
theorem natCast_lt_horizonThreshold_iff {η wStar : ℝ}
    (hη : η ∈ Ioo (0 : ℝ) 1) (hw : wStar ∈ Ioo (0 : ℝ) 1)
    (r : ℝ) (t : ℕ) :
    (t : ℝ) < horizonThreshold η wStar ↔
      effectiveHorizonWeight η r t 0 < wStar := by
  have hresη : 1 - η ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hη.1, hη.2]
  have hresw : 1 - wStar ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hw.1, hw.2]
  have hlogη : Real.log (1 - η) < 0 := Real.log_neg hresη.1 hresη.2
  rw [horizonThreshold, lt_div_iff_of_neg hlogη, ← Real.log_pow,
    Real.log_lt_log_iff hresw.1 (pow_pos hresη.1 t)]
  simp only [effectiveHorizonWeight, repeatedEvidenceWeight, mul_zero, sub_zero]
  constructor <;> intro h <;> linarith

/-- After the log threshold, the baseline effective weight exceeds the optimum. -/
theorem horizonThreshold_lt_natCast_iff {η wStar : ℝ}
    (hη : η ∈ Ioo (0 : ℝ) 1) (hw : wStar ∈ Ioo (0 : ℝ) 1)
    (r : ℝ) (t : ℕ) :
    horizonThreshold η wStar < (t : ℝ) ↔
      wStar < effectiveHorizonWeight η r t 0 := by
  have hresη : 1 - η ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hη.1, hη.2]
  have hresw : 1 - wStar ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hw.1, hw.2]
  have hlogη : Real.log (1 - η) < 0 := Real.log_neg hresη.1 hresη.2
  rw [horizonThreshold, div_lt_iff_of_neg hlogη, ← Real.log_pow,
    Real.log_lt_log_iff (pow_pos hresη.1 t) hresw.1]
  simp only [effectiveHorizonWeight, repeatedEvidenceWeight, mul_zero, sub_zero]
  constructor <;> intro h <;> linarith

/--
At the permitted endpoint `η=1`, the paper's logarithmic threshold degenerates
to zero and its asserted strict derivative after that threshold fails already
at horizon two. The exact moments are feasible: `θ=0`, `m=2/5`, and a Bernoulli
prior with mean `1/4` give `δm=4/25`, `δ=1/4`, and `γ=1/10`.
-/
theorem horizon_fullResponsiveness_counterexample :
    (4 : ℝ) / 25 < 1 / 4 ∧ (1 : ℝ) / 10 < 4 / 25 ∧
      horizonOptimalWeight (1 / 4) (4 / 25) (1 / 10) = (5 : ℝ) / 7 ∧
      horizonThreshold 1 (horizonOptimalWeight (1 / 4) (4 / 25) (1 / 10)) = 0 ∧
      horizonThreshold 1 (horizonOptimalWeight (1 / 4) (4 / 25) (1 / 10)) < (2 : ℝ) ∧
      deriv (horizonMSE (1 / 4) (4 / 25) (1 / 10) 1 1 2) 0 = 0 := by
  have hderiv :=
    (hasDerivAt_horizonMSE (1 / 4) (4 / 25) (1 / 10) 1 1 2 0).deriv
  norm_num [horizonOptimalWeight, horizonThreshold, repeatedEvidenceWeight,
    effectiveHorizonWeight] at hderiv ⊢
  exact hderiv

/-- Before the threshold, marginal deference strictly raises MSE at baseline. -/
theorem horizonMSE_deriv_zero_pos_of_before_threshold
    {δ δm γ η r : ℝ} {t : ℕ}
    (ha : 0 < δ + δm - 2 * γ)
    (hη : η ∈ Ioo (0 : ℝ) 1)
    (hw : horizonOptimalWeight δ δm γ ∈ Ioo (0 : ℝ) 1)
    (hr : 0 < r) (ht : 1 ≤ t)
    (hbefore : (t : ℝ) < horizonThreshold η (horizonOptimalWeight δ δm γ)) :
    0 < deriv (horizonMSE δ δm γ η r t) 0 := by
  let a : ℝ := δ + δm - 2 * γ
  let wStar : ℝ := horizonOptimalWeight δ δm γ
  have ha' : 0 < a := by simpa only [a] using ha
  have hw' : wStar ∈ Ioo (0 : ℝ) 1 := by simpa only [wStar] using hw
  have hW : effectiveHorizonWeight η r t 0 < wStar := by
    exact (natCast_lt_horizonThreshold_iff hη hw' r t).1
      (by simpa only [wStar] using hbefore)
  have hopt : a * wStar = δ - γ := by
    dsimp only [a, wStar, horizonOptimalWeight]
    field_simp [ha.ne']
  have hq :
      2 * (a * effectiveHorizonWeight η r t 0 - (δ - γ)) < 0 := by
    have hproduct :
        0 < a * (wStar - effectiveHorizonWeight η r t 0) :=
      mul_pos ha' (sub_pos.mpr hW)
    nlinarith
  have htpos : 0 < (t : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt ht)
  have hresidual : 0 < 1 - repeatedEvidenceWeight η r 0 := by
    simp only [repeatedEvidenceWeight, mul_zero, sub_zero]
    linarith [hη.2]
  have hweightDeriv :
      -(t : ℝ) * r * (1 - repeatedEvidenceWeight η r 0) ^ (t - 1) < 0 := by
    have hp : 0 < (1 - repeatedEvidenceWeight η r 0) ^ (t - 1) :=
      pow_pos hresidual _
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (neg_neg_of_pos htpos) hr) hp
  rw [(hasDerivAt_horizonMSE δ δm γ η r t 0).deriv]
  change 0 <
    (2 * (a * effectiveHorizonWeight η r t 0 - (δ - γ))) *
      (-(t : ℝ) * r * (1 - repeatedEvidenceWeight η r 0) ^ (t - 1))
  exact mul_pos_of_neg_of_neg hq hweightDeriv

/-- After the threshold, marginal deference strictly lowers MSE at baseline. -/
theorem horizonMSE_deriv_zero_neg_of_after_threshold
    {δ δm γ η r : ℝ} {t : ℕ}
    (ha : 0 < δ + δm - 2 * γ)
    (hη : η ∈ Ioo (0 : ℝ) 1)
    (hw : horizonOptimalWeight δ δm γ ∈ Ioo (0 : ℝ) 1)
    (hr : 0 < r) (ht : 1 ≤ t)
    (hafter : horizonThreshold η (horizonOptimalWeight δ δm γ) < (t : ℝ)) :
    deriv (horizonMSE δ δm γ η r t) 0 < 0 := by
  let a : ℝ := δ + δm - 2 * γ
  let wStar : ℝ := horizonOptimalWeight δ δm γ
  have ha' : 0 < a := by simpa only [a] using ha
  have hw' : wStar ∈ Ioo (0 : ℝ) 1 := by simpa only [wStar] using hw
  have hW : wStar < effectiveHorizonWeight η r t 0 := by
    exact (horizonThreshold_lt_natCast_iff hη hw' r t).1
      (by simpa only [wStar] using hafter)
  have hopt : a * wStar = δ - γ := by
    dsimp only [a, wStar, horizonOptimalWeight]
    field_simp [ha.ne']
  have hq :
      0 < 2 * (a * effectiveHorizonWeight η r t 0 - (δ - γ)) := by
    have hproduct :
        0 < a * (effectiveHorizonWeight η r t 0 - wStar) :=
      mul_pos ha' (sub_pos.mpr hW)
    nlinarith
  have htpos : 0 < (t : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt ht)
  have hresidual : 0 < 1 - repeatedEvidenceWeight η r 0 := by
    simp only [repeatedEvidenceWeight, mul_zero, sub_zero]
    linarith [hη.2]
  have hweightDeriv :
      -(t : ℝ) * r * (1 - repeatedEvidenceWeight η r 0) ^ (t - 1) < 0 := by
    have hp : 0 < (1 - repeatedEvidenceWeight η r 0) ^ (t - 1) :=
      pow_pos hresidual _
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (neg_neg_of_pos htpos) hr) hp
  rw [(hasDerivAt_horizonMSE δ δm γ η r t 0).deriv]
  change
    (2 * (a * effectiveHorizonWeight η r t 0 - (δ - γ))) *
      (-(t : ℝ) * r * (1 - repeatedEvidenceWeight η r 0) ^ (t - 1)) < 0
  exact mul_neg_of_pos_of_neg hq hweightDeriv

/-- The paper's displacement-ratio formulation is equivalent to `γ ≥ δm`. -/
theorem one_le_displacementRatio_iff {θ m μ : ℝ} (hm : m ≠ θ) :
    1 ≤ (μ - θ) / (m - θ) ↔
      PaperI.evidenceError θ m ≤ PaperI.errorCorrelation θ m μ := by
  have hden : 0 < (m - θ) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hm)
  have hid :
      (μ - θ) / (m - θ) =
        PaperI.errorCorrelation θ m μ / PaperI.evidenceError θ m := by
    simp only [PaperI.errorCorrelation, PaperI.evidenceError]
    field_simp [sub_ne_zero.mpr hm]
  rw [hid, le_div_iff₀ (by simpa only [PaperI.evidenceError] using hden)]
  ring_nf

/-- If truth lies left of a straddling pair, the truth-side correlation is below evidence
error and the far-side correlation is above it. -/
theorem errorCorrelation_orders_of_truth_left
    {θ μNear m μFar : ℝ} (hθnear : θ < μNear)
    (hnearm : μNear < m) (hmfar : m < μFar) :
    PaperI.errorCorrelation θ m μNear < PaperI.evidenceError θ m ∧
      PaperI.evidenceError θ m < PaperI.errorCorrelation θ m μFar := by
  simp only [PaperI.errorCorrelation, PaperI.evidenceError]
  constructor
  · nlinarith [mul_pos (sub_pos.mpr hnearm) (sub_pos.mpr (hθnear.trans hnearm))]
  · nlinarith [mul_pos (sub_pos.mpr (hθnear.trans hnearm)) (sub_pos.mpr hmfar)]

/-- If truth lies right of a straddling pair, the truth-side correlation is below evidence
error and the far-side correlation is above it. -/
theorem errorCorrelation_orders_of_truth_right
    {μFar m μNear θ : ℝ} (hfarm : μFar < m)
    (hmnear : m < μNear) (hnearθ : μNear < θ) :
    PaperI.errorCorrelation θ m μNear < PaperI.evidenceError θ m ∧
      PaperI.evidenceError θ m < PaperI.errorCorrelation θ m μFar := by
  simp only [PaperI.errorCorrelation, PaperI.evidenceError]
  constructor
  · nlinarith [mul_pos (sub_pos.mpr hmnear) (sub_pos.mpr (hmnear.trans hnearθ))]
  · nlinarith [mul_pos (sub_pos.mpr (hfarm.trans hmnear)) (sub_pos.mpr hfarm)]

/-- Every finite-horizon effective weight is strictly below one when `η<1`. -/
theorem effectiveHorizonWeight_lt_one {η r β : ℝ} (t : ℕ)
    (hη : η < 1) (hr : 0 ≤ r) (hβ : 0 ≤ β) :
    effectiveHorizonWeight η r t β < 1 := by
  have hresidual : 0 < 1 - repeatedEvidenceWeight η r β := by
    simp only [repeatedEvidenceWeight]
    nlinarith [mul_nonneg hr hβ]
  have hp : 0 < (1 - repeatedEvidenceWeight η r β) ^ t := pow_pos hresidual _
  simp only [effectiveHorizonWeight]
  linarith

/-- In the no-inversion case, repeated-exposure MSE is strictly increasing in policy. -/
theorem horizonMSE_strictMonoOn_of_no_inversion
    {δ δm γ η r : ℝ} {t : ℕ}
    (ha : 0 < δ + δm - 2 * γ)
    (hη : η < 1) (hr : 0 < r) (ht : 1 ≤ t) (hno : δm ≤ γ) :
    StrictMonoOn (horizonMSE δ δm γ η r t) (Icc (0 : ℝ) 1) := by
  have hwStar : 1 ≤ horizonOptimalWeight δ δm γ :=
    (one_le_horizonOptimalWeight_iff ha).2 hno
  intro β₁ hβ₁ β₂ hβ₂ hβ
  have hresidual₁ : 0 < 1 - repeatedEvidenceWeight η r β₁ := by
    simp only [repeatedEvidenceWeight]
    nlinarith [mul_nonneg hr.le hβ₁.1]
  have hresidual_lt :
      1 - repeatedEvidenceWeight η r β₁ <
        1 - repeatedEvidenceWeight η r β₂ := by
    simp only [repeatedEvidenceWeight]
    nlinarith [mul_lt_mul_of_pos_left hβ hr]
  have hpow :
      (1 - repeatedEvidenceWeight η r β₁) ^ t <
        (1 - repeatedEvidenceWeight η r β₂) ^ t :=
    pow_lt_pow_left₀ hresidual_lt hresidual₁.le (Nat.ne_zero_of_lt ht)
  have hweight :
      effectiveHorizonWeight η r t β₂ < effectiveHorizonWeight η r t β₁ := by
    simp only [effectiveHorizonWeight]
    linarith
  have hbelow :
      effectiveHorizonWeight η r t β₁ ≤ horizonOptimalWeight δ δm γ := by
    exact (effectiveHorizonWeight_lt_one t hη hr.le hβ₁.1).le.trans hwStar
  exact PaperI.mseQuadratic_strictAnti_below_optimal ha hweight hbelow

/-- The clauses of the paper's horizon dichotomy. -/
structure HorizonDichotomyConclusions
    (δ δm γ η r : ℝ) : Prop where
  no_inversion : δm ≤ γ → ∀ t : ℕ, 1 ≤ t →
    1 ≤ horizonOptimalWeight δ δm γ ∧
      (∀ β ∈ Icc (0 : ℝ) 1, effectiveHorizonWeight η r t β < 1) ∧
      StrictMonoOn (horizonMSE δ δm γ η r t) (Icc (0 : ℝ) 1)
  inversion : γ < δm →
    horizonOptimalWeight δ δm γ ∈ Ioo (0 : ℝ) 1 ∧
      0 < horizonThreshold η (horizonOptimalWeight δ δm γ) ∧
      ∀ t : ℕ, 1 ≤ t →
        ((t : ℝ) < horizonThreshold η (horizonOptimalWeight δ δm γ) →
          0 < deriv (horizonMSE δ δm γ η r t) 0) ∧
        (horizonThreshold η (horizonOptimalWeight δ δm γ) < (t : ℝ) →
          deriv (horizonMSE δ δm γ η r t) 0 < 0)

/--
Paper II, Theorem 5.1 (`thm:horizon`), `civic_drift.tex:816`.

This is the paper's interior-responsiveness statement. The exact
endpoint witness in `horizon_fullResponsiveness_counterexample` explains the
following sharpness remark in the paper.
-/
theorem horizonDichotomy
    {δ δm γ η r : ℝ}
    (hδm : 0 ≤ δm) (hδ : 0 ≤ δ) (hevidence : δm < δ)
    (hγ : 0 ≤ γ) (hγbound : γ ≤ Real.sqrt (δm * δ))
    (hη : η ∈ Ioo (0 : ℝ) 1) (hr : 0 < r) :
    HorizonDichotomyConclusions δ δm γ η r := by
  have ha : 0 < δ + δm - 2 * γ :=
    PaperI.mseQuadratic_coefficient_pos hδm hδ hevidence hγ hγbound
  constructor
  · intro hno t ht
    exact ⟨(one_le_horizonOptimalWeight_iff ha).2 hno,
      fun β hβ ↦ effectiveHorizonWeight_lt_one t hη.2 hr.le hβ.1,
      horizonMSE_strictMonoOn_of_no_inversion ha hη.2 hr ht hno⟩
  · intro hinversion
    have hw := horizonOptimalWeight_mem_Ioo hδm hδ hevidence hγ hγbound hinversion
    refine ⟨hw, horizonThreshold_pos hη hw, ?_⟩
    intro t ht
    exact ⟨horizonMSE_deriv_zero_pos_of_before_threshold ha hη hw hr ht,
      horizonMSE_deriv_zero_neg_of_after_threshold ha hη hw hr ht⟩

/-! ## Accuracy-optimal deference after the inversion threshold -/

/-- The threshold remains nonnegative at the paper's permitted endpoint `η = 1`. -/
theorem horizonThreshold_nonneg {η wStar : ℝ}
    (hη : η ∈ Ioc (0 : ℝ) 1) (hw : wStar ∈ Ioo (0 : ℝ) 1) :
    0 ≤ horizonThreshold η wStar := by
  rcases eq_or_lt_of_le hη.2 with hηone | hηlt
  · subst η
    simp [horizonThreshold]
  · exact (horizonThreshold_pos ⟨hη.1, hηlt⟩ hw).le

/-- The residual root is strictly positive for an interior optimal weight. -/
theorem horizonResidualRoot_pos {wStar : ℝ} (hw : wStar < 1) (t : ℕ) :
    0 < horizonResidualRoot wStar t := by
  exact Real.rpow_pos_of_pos (sub_pos.mpr hw) _

/-- At every positive horizon, the residual root is strictly below one. -/
theorem horizonResidualRoot_lt_one {wStar : ℝ} (hw : wStar ∈ Ioo (0 : ℝ) 1)
    {t : ℕ} (ht : 0 < t) :
    horizonResidualRoot wStar t < 1 := by
  apply Real.rpow_lt_one (by linarith [hw.2]) (by linarith [hw.1])
  exact inv_pos.mpr (by exact_mod_cast ht)

/-- Raising the positive residual root to its horizon recovers `1 - wStar`. -/
theorem horizonResidualRoot_pow {wStar : ℝ} (hw : wStar ≤ 1)
    {t : ℕ} (ht : t ≠ 0) :
    horizonResidualRoot wStar t ^ t = 1 - wStar := by
  exact Real.rpow_inv_natCast_pow (sub_nonneg.mpr hw) ht

/-- The displayed policy in `eq:bstaracc` realizes the optimal effective weight exactly. -/
theorem effectiveHorizonWeight_accuracyOptimalDeference_eq
    {η wStar : ℝ} {t : ℕ} (hη : η ≠ 0) (hw : wStar ≤ 1) (ht : t ≠ 0) :
    effectiveHorizonWeight η η t (accuracyOptimalDeference η wStar t) = wStar := by
  have hweight :
      repeatedEvidenceWeight η η (accuracyOptimalDeference η wStar t) =
        1 - horizonResidualRoot wStar t := by
    simp only [repeatedEvidenceWeight, accuracyOptimalDeference]
    field_simp [hη]
    ring
  rw [effectiveHorizonWeight, hweight]
  have hpow := horizonResidualRoot_pow hw ht
  convert congrArg (fun x : ℝ ↦ 1 - x) hpow using 1 <;> ring

/-- With zero extraction, effective weight is strictly decreasing in deference. -/
theorem effectiveHorizonWeight_strictAntiOn_fullExtraction
    {η : ℝ} {t : ℕ} (hη : η ∈ Ioc (0 : ℝ) 1) (ht : 1 ≤ t) :
    StrictAntiOn (effectiveHorizonWeight η η t) (Icc (0 : ℝ) 1) := by
  intro β₁ hβ₁ β₂ hβ₂ hβ
  have hresidual₁ : 0 ≤ 1 - repeatedEvidenceWeight η η β₁ := by
    calc
      0 ≤ (1 - η) + η * β₁ :=
        add_nonneg (sub_nonneg.mpr hη.2) (mul_nonneg hη.1.le hβ₁.1)
      _ = 1 - repeatedEvidenceWeight η η β₁ := by
        simp only [repeatedEvidenceWeight]
        ring
  have hresidual_lt :
      1 - repeatedEvidenceWeight η η β₁ <
        1 - repeatedEvidenceWeight η η β₂ := by
    simp only [repeatedEvidenceWeight]
    nlinarith [mul_lt_mul_of_pos_left hβ hη.1]
  have hpow :
      (1 - repeatedEvidenceWeight η η β₁) ^ t <
        (1 - repeatedEvidenceWeight η η β₂) ^ t :=
    pow_lt_pow_left₀ hresidual_lt hresidual₁ (Nat.ne_zero_of_lt ht)
  simp only [effectiveHorizonWeight]
  linarith

/-- Completing the square around the unique minimizer of the moment quadratic. -/
theorem mseQuadratic_sub_horizonOptimalWeight_eq {δ δm γ w : ℝ}
    (ha : 0 < δ + δm - 2 * γ) :
    PaperI.mseQuadratic δ δm γ w -
        PaperI.mseQuadratic δ δm γ (horizonOptimalWeight δ δm γ) =
      (δ + δm - 2 * γ) * (w - horizonOptimalWeight δ δm γ) ^ 2 := by
  simp only [PaperI.mseQuadratic, horizonOptimalWeight]
  field_simp [ha.ne']
  ring

/-- Past the threshold, baseline repetition has already overshot the optimal weight. -/
theorem effectiveHorizonWeight_zero_gt_of_after_threshold
    {η wStar : ℝ} {t : ℕ}
    (hη : η ∈ Ioc (0 : ℝ) 1) (hw : wStar ∈ Ioo (0 : ℝ) 1)
    (hafter : horizonThreshold η wStar < (t : ℝ)) :
    wStar < effectiveHorizonWeight η η t 0 := by
  have htCast : (0 : ℝ) < t :=
    lt_of_le_of_lt (horizonThreshold_nonneg hη hw) hafter
  have ht : 0 < t := by exact_mod_cast htCast
  rcases eq_or_lt_of_le hη.2 with hηone | hηlt
  · subst η
    simp [effectiveHorizonWeight, repeatedEvidenceWeight, ht.ne', hw.2]
  · exact (horizonThreshold_lt_natCast_iff ⟨hη.1, hηlt⟩ hw η t).1 hafter

/-- The displayed post-threshold optimizer lies strictly inside the policy interval. -/
theorem accuracyOptimalDeference_mem_Ioo
    {η wStar : ℝ} {t : ℕ}
    (hη : η ∈ Ioc (0 : ℝ) 1) (hw : wStar ∈ Ioo (0 : ℝ) 1)
    (hafter : horizonThreshold η wStar < (t : ℝ)) :
    accuracyOptimalDeference η wStar t ∈ Ioo (0 : ℝ) 1 := by
  have htCast : (0 : ℝ) < t :=
    lt_of_le_of_lt (horizonThreshold_nonneg hη hw) hafter
  have ht : 0 < t := by exact_mod_cast htCast
  have hrootPos := horizonResidualRoot_pos hw.2 t
  have hrootLt := horizonResidualRoot_lt_one hw ht
  have hbaseline := effectiveHorizonWeight_zero_gt_of_after_threshold hη hw hafter
  have hpowRoot := horizonResidualRoot_pow hw.2.le ht.ne'
  have hpowLt :
      (1 - η) ^ t < horizonResidualRoot wStar t ^ t := by
    simp only [effectiveHorizonWeight, repeatedEvidenceWeight, mul_zero, sub_zero] at hbaseline
    rw [hpowRoot]
    linarith
  have hresidualLt : 1 - η < horizonResidualRoot wStar t :=
    (pow_lt_pow_iff_left₀ (by linarith [hη.2]) hrootPos.le ht.ne').1 hpowLt
  have hquotLt : (1 - horizonResidualRoot wStar t) / η < 1 :=
    (div_lt_one hη.1).2 (by linarith)
  have hquotPos : 0 < (1 - horizonResidualRoot wStar t) / η :=
    div_pos (sub_pos.mpr hrootLt) hη.1
  simp only [accuracyOptimalDeference]
  constructor <;> linarith

/-- The displayed optimizer is strictly increasing over all positive integer horizons. -/
theorem accuracyOptimalDeference_strictMonoOn
    {η wStar : ℝ} (hη : 0 < η) (hw : wStar ∈ Ioo (0 : ℝ) 1) :
    StrictMonoOn (accuracyOptimalDeference η wStar) {t : ℕ | 1 ≤ t} := by
  intro t₁ ht₁ t₂ ht₂ ht
  have ht₁pos : (0 : ℝ) < t₁ := by exact_mod_cast (Nat.zero_lt_of_lt ht₁)
  have ht₂pos : (0 : ℝ) < t₂ := by exact_mod_cast (Nat.zero_lt_of_lt ht₂)
  have htCast : (t₁ : ℝ) < t₂ := by exact_mod_cast ht
  have hinv : ((t₂ : ℝ)⁻¹) < (t₁ : ℝ)⁻¹ :=
    (inv_lt_inv₀ ht₂pos ht₁pos).2 htCast
  have hroot :
      horizonResidualRoot wStar t₁ < horizonResidualRoot wStar t₂ := by
    exact Real.rpow_lt_rpow_of_exponent_gt (sub_pos.mpr hw.2) (by linarith [hw.1]) hinv
  have hquot :
      (1 - horizonResidualRoot wStar t₂) / η <
        (1 - horizonResidualRoot wStar t₁) / η :=
    div_lt_div_of_pos_right (by linarith) hη
  simp only [accuracyOptimalDeference]
  linarith

/-- The residual root tends to one as the integer horizon diverges. -/
theorem horizonResidualRoot_tendsto_one {wStar : ℝ} (hw : wStar < 1) :
    Tendsto (horizonResidualRoot wStar) atTop (nhds 1) := by
  change Tendsto (fun t : ℕ ↦ (1 - wStar) ^ ((t : ℝ)⁻¹)) atTop (nhds 1)
  have hexponent :
      Tendsto (fun t : ℕ ↦ ((t : ℝ)⁻¹)) atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hbase : 1 - wStar ≠ 0 := ne_of_gt (sub_pos.mpr hw)
  have hcomp := (Real.continuousAt_const_rpow hbase).tendsto.comp hexponent
  have hcompOne :
      Tendsto ((fun x : ℝ ↦ (1 - wStar) ^ x) ∘ fun t : ℕ ↦ ((t : ℝ)⁻¹))
        atTop (nhds 1) := by
    simpa only [Real.rpow_zero] using hcomp
  exact hcompOne.congr' (Filter.Eventually.of_forall fun _ ↦ rfl)

/-- Accuracy-optimal deference tends to full deference at long horizons. -/
theorem accuracyOptimalDeference_tendsto_one
    {η wStar : ℝ} (hw : wStar < 1) :
    Tendsto (accuracyOptimalDeference η wStar) atTop (nhds 1) := by
  change Tendsto (fun t : ℕ ↦ 1 - (1 - horizonResidualRoot wStar t) / η)
    atTop (nhds 1)
  have hroot := horizonResidualRoot_tendsto_one hw
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  simpa only [sub_self, zero_div, sub_zero] using
    hone.sub ((hone.sub hroot).div_const η)

/-- The five exact claims bundled by Paper II's post-threshold optimizer proposition. -/
structure AccuracyOptimalDeferenceConclusions
    (δ δm γ η : ℝ) (t : ℕ) : Prop where
  interior :
    accuracyOptimalDeference η (horizonOptimalWeight δ δm γ) t ∈ Ioo (0 : ℝ) 1
  realizes_optimal_weight :
    effectiveHorizonWeight η η t
      (accuracyOptimalDeference η (horizonOptimalWeight δ δm γ) t) =
        horizonOptimalWeight δ δm γ
  minimizes : ∀ β ∈ Icc (0 : ℝ) 1,
    horizonMSE δ δm γ η η t
        (accuracyOptimalDeference η (horizonOptimalWeight δ δm γ) t) ≤
      horizonMSE δ δm γ η η t β
  unique : ∀ β ∈ Icc (0 : ℝ) 1,
    horizonMSE δ δm γ η η t β =
        horizonMSE δ δm γ η η t
          (accuracyOptimalDeference η (horizonOptimalWeight δ δm γ) t) →
      β = accuracyOptimalDeference η (horizonOptimalWeight δ δm γ) t
  strictly_increasing_in_horizon :
    StrictMonoOn (accuracyOptimalDeference η (horizonOptimalWeight δ δm γ))
      {n : ℕ | 1 ≤ n}
  tends_to_one :
    Tendsto (accuracyOptimalDeference η (horizonOptimalWeight δ δm γ))
      atTop (nhds 1)

/--
Paper II, Proposition 5.3 (`prop:bstar`), `civic_drift.tex:840`. In the inversion
case with zero extraction and an integer horizon past `T*`, the displayed
policy is the unique interior accuracy minimizer. The formula is strictly
increasing at every positive integer horizon and tends to full deference.
-/
theorem accuracyOptimalDeferenceUnderRepetition
    {δ δm γ η : ℝ} {t : ℕ}
    (hδm : 0 ≤ δm) (hδ : 0 ≤ δ) (hevidence : δm < δ)
    (hγ : 0 ≤ γ) (hγbound : γ ≤ Real.sqrt (δm * δ))
    (hη : η ∈ Ioc (0 : ℝ) 1) (hinversion : γ < δm)
    (hafter :
      horizonThreshold η (horizonOptimalWeight δ δm γ) < (t : ℝ)) :
    AccuracyOptimalDeferenceConclusions δ δm γ η t := by
  let wStar : ℝ := horizonOptimalWeight δ δm γ
  have ha : 0 < δ + δm - 2 * γ :=
    PaperI.mseQuadratic_coefficient_pos hδm hδ hevidence hγ hγbound
  have hw : wStar ∈ Ioo (0 : ℝ) 1 := by
    simpa only [wStar] using
      horizonOptimalWeight_mem_Ioo hδm hδ hevidence hγ hγbound hinversion
  have hafter' : horizonThreshold η wStar < (t : ℝ) := by
    simpa only [wStar] using hafter
  have htCast : (0 : ℝ) < t :=
    lt_of_le_of_lt (horizonThreshold_nonneg hη hw) hafter'
  have ht : 0 < t := by exact_mod_cast htCast
  have hstar : accuracyOptimalDeference η wStar t ∈ Ioo (0 : ℝ) 1 :=
    accuracyOptimalDeference_mem_Ioo hη hw hafter'
  have hweight :
      effectiveHorizonWeight η η t (accuracyOptimalDeference η wStar t) = wStar :=
    effectiveHorizonWeight_accuracyOptimalDeference_eq hη.1.ne' hw.2.le ht.ne'
  have hanti : StrictAntiOn (effectiveHorizonWeight η η t) (Icc (0 : ℝ) 1) :=
    effectiveHorizonWeight_strictAntiOn_fullExtraction hη (Nat.one_le_iff_ne_zero.2 ht.ne')
  constructor
  · simpa only [wStar] using hstar
  · simpa only [wStar] using hweight
  · intro β hβ
    have hdiff := mseQuadratic_sub_horizonOptimalWeight_eq
      (w := effectiveHorizonWeight η η t β) ha
    have hnonneg :
        0 ≤ (δ + δm - 2 * γ) *
          (effectiveHorizonWeight η η t β - wStar) ^ 2 :=
      mul_nonneg ha.le (sq_nonneg _)
    simp only [horizonMSE]
    rw [hweight]
    simpa only [wStar] using (show
      PaperI.mseQuadratic δ δm γ (horizonOptimalWeight δ δm γ) ≤
        PaperI.mseQuadratic δ δm γ (effectiveHorizonWeight η η t β) by
          nlinarith [hdiff, hnonneg])
  · intro β hβ heq
    have hdiff := mseQuadratic_sub_horizonOptimalWeight_eq
      (w := effectiveHorizonWeight η η t β) ha
    have hweight' :
        effectiveHorizonWeight η η t
            (accuracyOptimalDeference η (horizonOptimalWeight δ δm γ) t) =
          horizonOptimalWeight δ δm γ := by
      simpa only [wStar] using hweight
    have heq' :
        PaperI.mseQuadratic δ δm γ (effectiveHorizonWeight η η t β) =
          PaperI.mseQuadratic δ δm γ wStar := by
      simp only [horizonMSE] at heq
      rw [hweight'] at heq
      simpa only [wStar] using heq
    have hzero : effectiveHorizonWeight η η t β - wStar = 0 := by
      have hsquare :
          (δ + δm - 2 * γ) *
            (effectiveHorizonWeight η η t β - wStar) ^ 2 = 0 := by
        simpa only [wStar] using (show
          (δ + δm - 2 * γ) *
            (effectiveHorizonWeight η η t β - horizonOptimalWeight δ δm γ) ^ 2 = 0 by
              nlinarith [hdiff, heq'])
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hsquare).resolve_left ha.ne')
    have hβweight : effectiveHorizonWeight η η t β = wStar := sub_eq_zero.mp hzero
    have hstarIcc : accuracyOptimalDeference η wStar t ∈ Icc (0 : ℝ) 1 :=
      ⟨hstar.1.le, hstar.2.le⟩
    simpa only [wStar] using
      hanti.injOn hβ hstarIcc (by rw [hβweight, hweight])
  · simpa only [wStar] using accuracyOptimalDeference_strictMonoOn hη.1 hw
  · simpa only [wStar] using accuracyOptimalDeference_tendsto_one hw.2

/-! ## Inversion bands -/

/-- For a fixed interior optimum, the horizon threshold strictly decreases with responsiveness. -/
theorem horizonThreshold_strictAnti_responsiveness
    {ηH ηL wStar : ℝ}
    (hηH : ηH ∈ Ioo (0 : ℝ) 1) (hηL : ηL ∈ Ioo (0 : ℝ) 1)
    (hw : wStar ∈ Ioo (0 : ℝ) 1) (hη : ηH < ηL) :
    horizonThreshold ηL wStar < horizonThreshold ηH wStar := by
  let n : ℝ := Real.log (1 - wStar)
  let dL : ℝ := Real.log (1 - ηL)
  let dH : ℝ := Real.log (1 - ηH)
  have hn : n < 0 := by
    dsimp only [n]
    exact Real.log_neg (by linarith [hw.2]) (by linarith [hw.1])
  have hdL : dL < 0 := by
    dsimp only [dL]
    exact Real.log_neg (by linarith [hηL.2]) (by linarith [hηL.1])
  have hdH : dH < 0 := by
    dsimp only [dH]
    exact Real.log_neg (by linarith [hηH.2]) (by linarith [hηH.1])
  have hd : dL < dH := by
    dsimp only [dL, dH]
    rw [Real.log_lt_log_iff (by linarith [hηL.2]) (by linarith [hηH.2])]
    linarith
  change n / dL < n / dH
  have hx : 0 < n / dL := div_pos_of_neg_of_neg hn hdL
  by_contra hnot
  have hyx : n / dH ≤ n / dL := le_of_not_gt hnot
  have hleft : n / dL * dL < n / dL * dH := mul_lt_mul_of_pos_left hd hx
  have hright : n / dL * dH ≤ n / dH * dH :=
    mul_le_mul_of_nonpos_right hyx hdH.le
  rw [div_mul_cancel₀ n hdL.ne] at hleft
  rw [div_mul_cancel₀ n hdH.ne] at hright
  linarith

/-- The mathematically valid content of the credulity-band clause. -/
structure CredulityBandConclusions
    (δ δm γ ηL ηH rL rH : ℝ) : Prop where
  threshold_order :
    horizonThreshold ηL (horizonOptimalWeight δ δm γ) <
      horizonThreshold ηH (horizonOptimalWeight δ δm γ)
  band_signs : ∀ t : ℕ, 1 ≤ t →
    horizonThreshold ηL (horizonOptimalWeight δ δm γ) < (t : ℝ) →
    (t : ℝ) < horizonThreshold ηH (horizonOptimalWeight δ δm γ) →
      deriv (horizonMSE δ δm γ ηL rL t) 0 < 0 ∧
      0 < deriv (horizonMSE δ δm γ ηH rH t) 0 ∧
      deriv (fun β ↦
        horizonMSE δ δm γ ηL rL t β - horizonMSE δ δm γ ηH rH t β) 0 < 0

/-- A positive one-step gradient and the negative band gradient have opposite signs. -/
theorem CredulityBandConclusions.reversal_of_oneStep_positive
    {δ δm γ ηL ηH rL rH : ℝ}
    (h : CredulityBandConclusions δ δm γ ηL ηH rL rH)
    {t : ℕ} (ht : 1 ≤ t)
    (hafter :
      horizonThreshold ηL (horizonOptimalWeight δ δm γ) < (t : ℝ))
    (hbefore :
      (t : ℝ) < horizonThreshold ηH (horizonOptimalWeight δ δm γ))
    (hone : 0 < deriv (fun β ↦
      horizonMSE δ δm γ ηL rL 1 β - horizonMSE δ δm γ ηH rH 1 β) 0) :
    0 < deriv (fun β ↦
        horizonMSE δ δm γ ηL rL 1 β - horizonMSE δ δm γ ηH rH 1 β) 0 ∧
      deriv (fun β ↦
        horizonMSE δ δm γ ηL rL t β - horizonMSE δ δm γ ηH rH t β) 0 < 0 :=
  ⟨hone, (h.band_signs t ht hafter hbefore).2.2⟩

/--
Paper II, Corollary 5.4(a) (`cor:bands`), `civic_drift.tex:851`.

This proves the threshold ordering, both per-type signs in the open band, and
negativity of the horizon-`t` manipulability gradient under the paper's
interior-responsiveness hypotheses. The conditional reversal statement is
`CredulityBandConclusions.reversal_of_oneStep_positive`; the exact
example below verifies why its one-step sign hypothesis is necessary.
-/
theorem inversionBands
    {δ δm γ ηL ηH rL rH : ℝ}
    (hδm : 0 ≤ δm) (hδ : 0 ≤ δ) (hevidence : δm < δ)
    (hγ : 0 ≤ γ) (hγbound : γ ≤ Real.sqrt (δm * δ))
    (hinversion : γ < δm)
    (hηL : ηL ∈ Ioo (0 : ℝ) 1) (hηH : ηH ∈ Ioo (0 : ℝ) 1)
    (hηorder : ηH < ηL) (hrL : 0 < rL) (hrH : 0 < rH) :
    CredulityBandConclusions δ δm γ ηL ηH rL rH := by
  have ha : 0 < δ + δm - 2 * γ :=
    PaperI.mseQuadratic_coefficient_pos hδm hδ hevidence hγ hγbound
  have hw : horizonOptimalWeight δ δm γ ∈ Ioo (0 : ℝ) 1 :=
    horizonOptimalWeight_mem_Ioo hδm hδ hevidence hγ hγbound hinversion
  constructor
  · exact horizonThreshold_strictAnti_responsiveness hηH hηL hw hηorder
  · intro t ht hafter hbefore
    have hlow := horizonMSE_deriv_zero_neg_of_after_threshold
      ha hηL hw hrL ht hafter
    have hhigh := horizonMSE_deriv_zero_pos_of_before_threshold
      ha hηH hw hrH ht hbefore
    have hgradient :
        deriv (fun β ↦
          horizonMSE δ δm γ ηL rL t β - horizonMSE δ δm γ ηH rH t β) 0 =
            deriv (horizonMSE δ δm γ ηL rL t) 0 -
              deriv (horizonMSE δ δm γ ηH rH t) 0 := by
      change deriv
        (horizonMSE δ δm γ ηL rL t - horizonMSE δ δm γ ηH rH t) 0 = _
      rw [(hasDerivAt_horizonMSE δ δm γ ηL rL t 0).deriv,
        (hasDerivAt_horizonMSE δ δm γ ηH rH t 0).deriv]
      exact ((hasDerivAt_horizonMSE δ δm γ ηL rL t 0).sub
        (hasDerivAt_horizonMSE δ δm γ ηH rH t 0)).deriv
    exact ⟨hlow, hhigh, by rw [hgradient]; linarith⟩

/--
At `ηL = 1`, horizon two lies in a nonempty credulity band but the low-type
baseline derivative is zero, not negative. The moments are the same feasible
Bernoulli example used by `horizon_fullResponsiveness_counterexample`.
-/
theorem inversionBands_fullResponsiveness_counterexample :
    (4 : ℝ) / 25 < 1 / 4 ∧ (1 : ℝ) / 10 < 4 / 25 ∧ (1 : ℝ) / 10 < 1 ∧
      horizonThreshold 1 (horizonOptimalWeight (1 / 4) (4 / 25) (1 / 10)) < (2 : ℝ) ∧
      (2 : ℝ) <
        horizonThreshold (1 / 10) (horizonOptimalWeight (1 / 4) (4 / 25) (1 / 10)) ∧
      deriv (horizonMSE (1 / 4) (4 / 25) (1 / 10) 1 1 2) 0 = 0 ∧
      0 < deriv
        (horizonMSE (1 / 4) (4 / 25) (1 / 10) (1 / 10) (1 / 10) 2) 0 := by
  have hw : horizonOptimalWeight (1 / 4) (4 / 25) (1 / 10) ∈ Ioo (0 : ℝ) 1 := by
    norm_num [horizonOptimalWeight]
  have hηH : (1 : ℝ) / 10 ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hbefore :
      (2 : ℝ) <
        horizonThreshold (1 / 10) (horizonOptimalWeight (1 / 4) (4 / 25) (1 / 10)) := by
    apply (natCast_lt_horizonThreshold_iff hηH hw (1 / 10) 2).2
    norm_num [effectiveHorizonWeight, repeatedEvidenceWeight, horizonOptimalWeight]
  have hlow :=
    (hasDerivAt_horizonMSE (1 / 4) (4 / 25) (1 / 10) 1 1 2 0).deriv
  have hhigh := horizonMSE_deriv_zero_pos_of_before_threshold
    (δ := (1 : ℝ) / 4) (δm := (4 : ℝ) / 25) (γ := (1 : ℝ) / 10)
    (η := (1 : ℝ) / 10) (r := (1 : ℝ) / 10) (t := 2)
    (by norm_num) hηH hw (by norm_num) (by norm_num) hbefore
  norm_num [effectiveHorizonWeight, repeatedEvidenceWeight] at hlow
  exact ⟨by norm_num, by norm_num, by norm_num,
    by simp [horizonThreshold], hbefore, hlow, hhigh⟩

/--
Interior responsiveness does not rescue the claimed comparison with the
one-step gradient. With zero extraction for both types, horizon two is in the
open inversion band, yet both the horizon-two and horizon-one manipulability
gradients are negative.
-/
theorem inversionBands_oneStep_reversal_counterexample :
    (2 : ℝ) / 5 < 1 / 2 ∧
      horizonThreshold (1 / 2) (horizonOptimalWeight (1 / 4) (4 / 25) (1 / 10)) <
        (2 : ℝ) ∧
      (2 : ℝ) <
        horizonThreshold (2 / 5) (horizonOptimalWeight (1 / 4) (4 / 25) (1 / 10)) ∧
      deriv (fun β ↦
        horizonMSE (1 / 4) (4 / 25) (1 / 10) (1 / 2) (1 / 2) 2 β -
          horizonMSE (1 / 4) (4 / 25) (1 / 10) (2 / 5) (2 / 5) 2 β) 0 < 0 ∧
      deriv (fun β ↦
        horizonMSE (1 / 4) (4 / 25) (1 / 10) (1 / 2) (1 / 2) 1 β -
          horizonMSE (1 / 4) (4 / 25) (1 / 10) (2 / 5) (2 / 5) 1 β) 0 < 0 := by
  have hw : horizonOptimalWeight (1 / 4) (4 / 25) (1 / 10) ∈ Ioo (0 : ℝ) 1 := by
    norm_num [horizonOptimalWeight]
  have hηL : (1 : ℝ) / 2 ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hηH : (2 : ℝ) / 5 ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hafter :
      horizonThreshold (1 / 2) (horizonOptimalWeight (1 / 4) (4 / 25) (1 / 10)) <
        (2 : ℝ) := by
    apply (horizonThreshold_lt_natCast_iff hηL hw (1 / 2) 2).2
    norm_num [effectiveHorizonWeight, repeatedEvidenceWeight, horizonOptimalWeight]
  have hbefore :
      (2 : ℝ) <
        horizonThreshold (2 / 5) (horizonOptimalWeight (1 / 4) (4 / 25) (1 / 10)) := by
    apply (natCast_lt_horizonThreshold_iff hηH hw (2 / 5) 2).2
    norm_num [effectiveHorizonWeight, repeatedEvidenceWeight, horizonOptimalWeight]
  have htwoDeriv :=
    ((hasDerivAt_horizonMSE (1 / 4) (4 / 25) (1 / 10) (1 / 2) (1 / 2) 2 0).sub
      (hasDerivAt_horizonMSE (1 / 4) (4 / 25) (1 / 10) (2 / 5) (2 / 5) 2 0)).deriv
  norm_num [effectiveHorizonWeight, repeatedEvidenceWeight] at htwoDeriv
  have htwo :
      deriv (fun β ↦
        horizonMSE (1 / 4) (4 / 25) (1 / 10) (1 / 2) (1 / 2) 2 β -
          horizonMSE (1 / 4) (4 / 25) (1 / 10) (2 / 5) (2 / 5) 2 β) 0 < 0 := by
    change deriv
      (horizonMSE (1 / 4) (4 / 25) (1 / 10) (1 / 2) (1 / 2) 2 -
        horizonMSE (1 / 4) (4 / 25) (1 / 10) (2 / 5) (2 / 5) 2) 0 < 0
    rw [htwoDeriv]
    norm_num
  have honeDeriv :=
    ((hasDerivAt_horizonMSE (1 / 4) (4 / 25) (1 / 10) (1 / 2) (1 / 2) 1 0).sub
      (hasDerivAt_horizonMSE (1 / 4) (4 / 25) (1 / 10) (2 / 5) (2 / 5) 1 0)).deriv
  norm_num [effectiveHorizonWeight, repeatedEvidenceWeight] at honeDeriv
  have hone :
      deriv (fun β ↦
        horizonMSE (1 / 4) (4 / 25) (1 / 10) (1 / 2) (1 / 2) 1 β -
          horizonMSE (1 / 4) (4 / 25) (1 / 10) (2 / 5) (2 / 5) 1 β) 0 < 0 := by
    change deriv
      (horizonMSE (1 / 4) (4 / 25) (1 / 10) (1 / 2) (1 / 2) 1 -
        horizonMSE (1 / 4) (4 / 25) (1 / 10) (2 / 5) (2 / 5) 1) 0 < 0
    rw [honeDeriv]
    norm_num
  exact ⟨by norm_num, hafter, hbefore, htwo, hone⟩

/-- In the no-inversion regime, the baseline derivative is positive at every positive horizon. -/
theorem horizonMSE_deriv_zero_pos_of_no_inversion
    {δ δm γ η r : ℝ} {t : ℕ}
    (ha : 0 < δ + δm - 2 * γ) (hη : η ∈ Ioo (0 : ℝ) 1)
    (hr : 0 < r) (ht : 1 ≤ t) (hno : δm ≤ γ) :
    0 < deriv (horizonMSE δ δm γ η r t) 0 := by
  let a : ℝ := δ + δm - 2 * γ
  let wStar : ℝ := horizonOptimalWeight δ δm γ
  have ha' : 0 < a := by simpa only [a] using ha
  have hwStar : 1 ≤ wStar := by
    simpa only [wStar] using (one_le_horizonOptimalWeight_iff ha).2 hno
  have hWlt : effectiveHorizonWeight η r t 0 < 1 :=
    effectiveHorizonWeight_lt_one t hη.2 hr.le (by norm_num)
  have hW : effectiveHorizonWeight η r t 0 < wStar := hWlt.trans_le hwStar
  have hopt : a * wStar = δ - γ := by
    dsimp only [a, wStar, horizonOptimalWeight]
    field_simp [ha.ne']
  have hq :
      2 * (a * effectiveHorizonWeight η r t 0 - (δ - γ)) < 0 := by
    have hproduct :
        0 < a * (wStar - effectiveHorizonWeight η r t 0) :=
      mul_pos ha' (sub_pos.mpr hW)
    nlinarith
  have htpos : 0 < (t : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt ht)
  have hresidual : 0 < 1 - repeatedEvidenceWeight η r 0 := by
    simp only [repeatedEvidenceWeight, mul_zero, sub_zero]
    linarith [hη.2]
  have hweightDeriv :
      -(t : ℝ) * r * (1 - repeatedEvidenceWeight η r 0) ^ (t - 1) < 0 := by
    have hp : 0 < (1 - repeatedEvidenceWeight η r 0) ^ (t - 1) :=
      pow_pos hresidual _
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (neg_neg_of_pos htpos) hr) hp
  rw [(hasDerivAt_horizonMSE δ δm γ η r t 0).deriv]
  change 0 <
    (2 * (a * effectiveHorizonWeight η r t 0 - (δ - γ))) *
      (-(t : ℝ) * r * (1 - repeatedEvidenceWeight η r 0) ^ (t - 1))
  exact mul_pos_of_neg_of_neg hq hweightDeriv

/-- The mathematically valid content of the straddle-permanence clause. -/
structure StraddlePermanenceConclusions
    (δNear δmNear γNear δFar δmFar γFar ηNear ηFar rNear rFar : ℝ) : Prop where
  near_threshold_pos :
    0 < horizonThreshold ηNear (horizonOptimalWeight δNear δmNear γNear)
  far_positive : ∀ t : ℕ, 1 ≤ t →
    0 < deriv (horizonMSE δFar δmFar γFar ηFar rFar t) 0
  permanently_opposed : ∀ t : ℕ, 1 ≤ t →
    horizonThreshold ηNear (horizonOptimalWeight δNear δmNear γNear) < (t : ℝ) →
      deriv (horizonMSE δNear δmNear γNear ηNear rNear t) 0 < 0 ∧
        0 < deriv (horizonMSE δFar δmFar γFar ηFar rFar t) 0

/--
Paper II, Corollary 5.4(b) (`cor:bands`), `civic_drift.tex:851`, at the analytic
level of its parenthetical truth-side/far-side regimes.
-/
theorem straddlePermanence
    {δNear δmNear γNear δFar δmFar γFar ηNear ηFar rNear rFar : ℝ}
    (hδmNear : 0 ≤ δmNear) (hδNear : 0 ≤ δNear) (hevidenceNear : δmNear < δNear)
    (hγNear : 0 ≤ γNear) (hγboundNear : γNear ≤ Real.sqrt (δmNear * δNear))
    (hinversionNear : γNear < δmNear)
    (hδmFar : 0 ≤ δmFar) (hδFar : 0 ≤ δFar) (hevidenceFar : δmFar < δFar)
    (hγFar : 0 ≤ γFar) (hγboundFar : γFar ≤ Real.sqrt (δmFar * δFar))
    (hnoFar : δmFar < γFar)
    (hηNear : ηNear ∈ Ioo (0 : ℝ) 1) (hηFar : ηFar ∈ Ioo (0 : ℝ) 1)
    (hrNear : 0 < rNear) (hrFar : 0 < rFar) :
    StraddlePermanenceConclusions
      δNear δmNear γNear δFar δmFar γFar ηNear ηFar rNear rFar := by
  have haNear : 0 < δNear + δmNear - 2 * γNear :=
    PaperI.mseQuadratic_coefficient_pos
      hδmNear hδNear hevidenceNear hγNear hγboundNear
  have hwNear : horizonOptimalWeight δNear δmNear γNear ∈ Ioo (0 : ℝ) 1 :=
    horizonOptimalWeight_mem_Ioo
      hδmNear hδNear hevidenceNear hγNear hγboundNear hinversionNear
  have haFar : 0 < δFar + δmFar - 2 * γFar :=
    PaperI.mseQuadratic_coefficient_pos
      hδmFar hδFar hevidenceFar hγFar hγboundFar
  have hfar : ∀ t : ℕ, 1 ≤ t →
      0 < deriv (horizonMSE δFar δmFar γFar ηFar rFar t) 0 :=
    fun _ ht ↦ horizonMSE_deriv_zero_pos_of_no_inversion
      haFar hηFar hrFar ht hnoFar.le
  exact ⟨horizonThreshold_pos hηNear hwNear, hfar,
    fun t ht hafter ↦
      ⟨horizonMSE_deriv_zero_neg_of_after_threshold
        haNear hηNear hwNear hrNear ht hafter, hfar t ht⟩⟩

/--
Paper II, Corollary 5.4(b) (`cor:bands`), `civic_drift.tex:851`, from the literal
truth-outside-the-means geometry. The geometry derives the truth-side/far-side
correlation inequalities used by `straddlePermanence`.
-/
theorem straddlePermanence_of_mean_geometry
    {θ m μNear μFar δNear δFar ηNear ηFar rNear rFar : ℝ}
    (hgeometry :
      (θ < μNear ∧ μNear < m ∧ m < μFar) ∨
        (μFar < m ∧ m < μNear ∧ μNear < θ))
    (hδm : 0 ≤ PaperI.evidenceError θ m)
    (hδNear : 0 ≤ δNear) (hevidenceNear : PaperI.evidenceError θ m < δNear)
    (hγNear : 0 ≤ PaperI.errorCorrelation θ m μNear)
    (hγboundNear :
      PaperI.errorCorrelation θ m μNear ≤
        Real.sqrt (PaperI.evidenceError θ m * δNear))
    (hδFar : 0 ≤ δFar) (hevidenceFar : PaperI.evidenceError θ m < δFar)
    (hγFar : 0 ≤ PaperI.errorCorrelation θ m μFar)
    (hγboundFar :
      PaperI.errorCorrelation θ m μFar ≤
        Real.sqrt (PaperI.evidenceError θ m * δFar))
    (hηNear : ηNear ∈ Ioo (0 : ℝ) 1) (hηFar : ηFar ∈ Ioo (0 : ℝ) 1)
    (hrNear : 0 < rNear) (hrFar : 0 < rFar) :
    StraddlePermanenceConclusions
      δNear (PaperI.evidenceError θ m) (PaperI.errorCorrelation θ m μNear)
      δFar (PaperI.evidenceError θ m) (PaperI.errorCorrelation θ m μFar)
      ηNear ηFar rNear rFar := by
  have horders :
      PaperI.errorCorrelation θ m μNear < PaperI.evidenceError θ m ∧
        PaperI.evidenceError θ m < PaperI.errorCorrelation θ m μFar := by
    rcases hgeometry with hleft | hright
    · exact errorCorrelation_orders_of_truth_left hleft.1 hleft.2.1 hleft.2.2
    · exact errorCorrelation_orders_of_truth_right hright.1 hright.2.1 hright.2.2
  exact straddlePermanence
    hδm hδNear hevidenceNear hγNear hγboundNear horders.1
    hδm hδFar hevidenceFar hγFar hγboundFar horders.2
    hηNear hηFar hrNear hrFar

/-! ## Fresh noisy evidence at stationarity -/

/-- The centered AR(1) belief-error update driven by a fresh evidence error. -/
def ar1ErrorStep {Ω : Type*} (w : ℝ) (X innovation : Ω → ℝ) (ω : Ω) : ℝ :=
  (1 - w) * X ω + w * innovation ω

/-- The stationary variance forced by the AR(1) moment equation when `0 < w < 2`. -/
def stationaryEvidenceVariance (w σm2 : ℝ) : ℝ :=
  w * σm2 / (2 - w)

/-- Paper II equation `eq:ar1`: squared stationary bias plus stationary variance. -/
def stationaryEvidenceMSE (bm σm2 w : ℝ) : ℝ :=
  bm ^ 2 + stationaryEvidenceVariance w σm2

/-- The AR(1) update sends the two input means to their affine combination. -/
theorem integral_ar1ErrorStep
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X innovation : Ω → ℝ} (w : ℝ)
    (hX : Integrable X P) (hInnovation : Integrable innovation P) :
    ∫ ω, ar1ErrorStep w X innovation ω ∂P =
      (1 - w) * (∫ ω, X ω ∂P) + w * (∫ ω, innovation ω ∂P) := by
  rw [show (fun ω ↦ ar1ErrorStep w X innovation ω) =
      (fun ω ↦ (1 - w) * X ω + w * innovation ω) by rfl,
    integral_add (hX.const_mul _) (hInnovation.const_mul _),
    integral_const_mul, integral_const_mul]

/-- If state and innovation have the same mean, the AR(1) step preserves it. -/
theorem integral_ar1ErrorStep_eq_commonMean
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X innovation : Ω → ℝ} {w bm : ℝ}
    (hX : Integrable X P) (hInnovation : Integrable innovation P)
    (hXmean : ∫ ω, X ω ∂P = bm)
    (hInnovationMean : ∫ ω, innovation ω ∂P = bm) :
    ∫ ω, ar1ErrorStep w X innovation ω ∂P = bm := by
  rw [integral_ar1ErrorStep w hX hInnovation, hXmean, hInnovationMean]
  ring

/-- Independence makes the AR(1) variance recursion exact. -/
theorem variance_ar1ErrorStep
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X innovation : Ω → ℝ} {w : ℝ}
    (hX : MemLp X 2 P) (hInnovation : MemLp innovation 2 P)
    (hIndep : IndepFun X innovation P) :
    variance (ar1ErrorStep w X innovation) P =
      (1 - w) ^ 2 * variance X P + w ^ 2 * variance innovation P := by
  have hScaledIndep :
      IndepFun ((fun x : ℝ ↦ (1 - w) * x) ∘ X)
        ((fun x : ℝ ↦ w * x) ∘ innovation) P :=
    hIndep.comp (show Measurable (fun x : ℝ ↦ (1 - w) * x) by fun_prop)
      (show Measurable (fun x : ℝ ↦ w * x) by fun_prop)
  have hScaledX : MemLp ((fun x : ℝ ↦ (1 - w) * x) ∘ X) 2 P := by
    change MemLp (fun ω ↦ (1 - w) * X ω) 2 P
    exact hX.const_mul (1 - w)
  have hScaledInnovation : MemLp ((fun x : ℝ ↦ w * x) ∘ innovation) 2 P := by
    change MemLp (fun ω ↦ w * innovation ω) 2 P
    exact hInnovation.const_mul w
  have hvariance := hScaledIndep.variance_fun_add
    hScaledX hScaledInnovation
  change variance (fun ω ↦ (1 - w) * X ω + w * innovation ω) P =
    variance (fun ω ↦ (1 - w) * X ω) P +
      variance (fun ω ↦ w * innovation ω) P at hvariance
  rw [variance_const_mul, variance_const_mul] at hvariance
  change variance (fun ω ↦ (1 - w) * X ω + w * innovation ω) P = _
  exact hvariance

/-- A square-integrable variable's second moment is variance plus squared mean. -/
theorem integral_sq_eq_variance_add_sq_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : MemLp X 2 P) :
    (∫ ω, X ω ^ 2 ∂P) = variance X P + (∫ ω, X ω ∂P) ^ 2 := by
  have hvariance := variance_eq_sub hX
  simp only [Pi.pow_apply] at hvariance
  linarith

/-- A nonzero evidence weight forces the stationary mean to equal the innovation mean. -/
theorem ar1_stationaryMean_iff {w mean bm : ℝ} (hw : w ≠ 0) :
    mean = (1 - w) * mean + w * bm ↔ mean = bm := by
  constructor
  · intro h
    have hfactor :
        mean - ((1 - w) * mean + w * bm) = w * (mean - bm) := by ring
    have hzero : w * (mean - bm) = 0 :=
      hfactor.symm.trans (sub_eq_zero.mpr h)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hw)
  · rintro rfl
    ring

/-- The displayed stationary variance solves the AR(1) variance recursion. -/
theorem stationaryEvidenceVariance_fixed {w σm2 : ℝ} (hw2 : w ≠ 2) :
    stationaryEvidenceVariance w σm2 =
      (1 - w) ^ 2 * stationaryEvidenceVariance w σm2 + w ^ 2 * σm2 := by
  have hden : 2 - w ≠ 0 := sub_ne_zero.mpr hw2.symm
  simp only [stationaryEvidenceVariance]
  field_simp [hden]
  ring

/-- For `w ≠ 0,2`, the AR(1) variance equation has exactly the displayed solution. -/
theorem ar1_stationaryVariance_iff {w σm2 V : ℝ} (hw : w ≠ 0) (hw2 : w ≠ 2) :
    V = (1 - w) ^ 2 * V + w ^ 2 * σm2 ↔
      V = stationaryEvidenceVariance w σm2 := by
  have hden : 2 - w ≠ 0 := sub_ne_zero.mpr hw2.symm
  constructor
  · intro h
    have hfactor :
        V - ((1 - w) ^ 2 * V + w ^ 2 * σm2) =
          w * ((2 - w) * V - w * σm2) := by ring
    have hmul : w * ((2 - w) * V - w * σm2) = 0 :=
      hfactor.symm.trans (sub_eq_zero.mpr h)
    have hcross : (2 - w) * V = w * σm2 := by
      have := (mul_eq_zero.mp hmul).resolve_left hw
      linarith
    rw [stationaryEvidenceVariance, eq_div_iff hden]
    nlinarith
  · rintro rfl
    exact stationaryEvidenceVariance_fixed hw2

/-- Independent fresh evidence preserves the displayed stationary mean and variance. -/
theorem ar1ErrorStep_preserves_stationaryMoments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X innovation : Ω → ℝ} {w bm σm2 : ℝ}
    (hX : MemLp X 2 P) (hInnovation : MemLp innovation 2 P)
    (hIndep : IndepFun X innovation P)
    (hXmean : ∫ ω, X ω ∂P = bm)
    (hInnovationMean : ∫ ω, innovation ω ∂P = bm)
    (hXvariance : variance X P = stationaryEvidenceVariance w σm2)
    (hInnovationVariance : variance innovation P = σm2)
    (hw2 : w ≠ 2) :
    (∫ ω, ar1ErrorStep w X innovation ω ∂P) = bm ∧
      variance (ar1ErrorStep w X innovation) P = stationaryEvidenceVariance w σm2 := by
  have hXint : Integrable X P := hX.integrable one_le_two
  have hInnovationInt : Integrable innovation P := hInnovation.integrable one_le_two
  constructor
  · exact integral_ar1ErrorStep_eq_commonMean
      hXint hInnovationInt hXmean hInnovationMean
  · rw [variance_ar1ErrorStep hX hInnovation hIndep,
      hXvariance, hInnovationVariance]
    exact (stationaryEvidenceVariance_fixed hw2).symm

/-- The stationary second moment is exactly Paper II equation `eq:ar1`. -/
theorem ar1_stationaryMSE_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} {w bm σm2 : ℝ}
    (hX : MemLp X 2 P) (hmean : ∫ ω, X ω ∂P = bm)
    (hvarianceFixed :
      variance X P = (1 - w) ^ 2 * variance X P + w ^ 2 * σm2)
    (hw : w ≠ 0) (hw2 : w ≠ 2) :
    (∫ ω, X ω ^ 2 ∂P) = stationaryEvidenceMSE bm σm2 w := by
  have hvariance := (ar1_stationaryVariance_iff hw hw2).1 hvarianceFixed
  rw [integral_sq_eq_variance_add_sq_integral hX, hmean, hvariance]
  simp only [stationaryEvidenceMSE]
  ring

/-- Positive innovation variance makes stationary MSE strictly increasing in evidence weight. -/
theorem stationaryEvidenceMSE_strictMonoOn
    {bm σm2 : ℝ} (hσm2 : 0 < σm2) :
    StrictMonoOn (stationaryEvidenceMSE bm σm2) (Ioc (0 : ℝ) 1) := by
  intro w₁ hw₁ w₂ hw₂ hw
  have hden₁ : 0 < 2 - w₁ := by linarith [hw₁.2]
  have hden₂ : 0 < 2 - w₂ := by linarith [hw₂.2]
  have hdiff :
      stationaryEvidenceMSE bm σm2 w₂ - stationaryEvidenceMSE bm σm2 w₁ =
        2 * σm2 * (w₂ - w₁) / ((2 - w₂) * (2 - w₁)) := by
    simp only [stationaryEvidenceMSE, stationaryEvidenceVariance]
    field_simp [hden₁.ne', hden₂.ne']
    ring
  have hpositive :
      0 < 2 * σm2 * (w₂ - w₁) / ((2 - w₂) * (2 - w₁)) :=
    div_pos (mul_pos (mul_pos (by norm_num) hσm2) (sub_pos.mpr hw))
      (mul_pos hden₂ hden₁)
  linarith

/-- Exact derivative used in the paper's proof of `prop:ar1`. -/
theorem hasDerivAt_stationaryEvidenceMSE
    (bm σm2 w : ℝ) (hw2 : w ≠ 2) :
    HasDerivAt (stationaryEvidenceMSE bm σm2)
      (2 * σm2 / (2 - w) ^ 2) w := by
  have hnum : HasDerivAt (fun x : ℝ ↦ x * σm2) σm2 w :=
    by simpa using (hasDerivAt_id w).mul_const σm2
  have hden : HasDerivAt (fun x : ℝ ↦ 2 - x) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub (2 : ℝ)
  have hdenne : 2 - w ≠ 0 := sub_ne_zero.mpr hw2.symm
  change HasDerivAt (fun x : ℝ ↦ bm ^ 2 + x * σm2 / (2 - x))
    (2 * σm2 / (2 - w) ^ 2) w
  convert (hasDerivAt_const w (bm ^ 2)).add (hnum.div hden hdenne) using 1
  all_goals
    first
    | rfl
    | ring

/-- With unbiased evidence, reducing a positive evidence weight strictly lowers stationary MSE. -/
theorem unbiased_stationaryMSE_strictly_improves_with_deference
    {σm2 wDeferred wBaseline : ℝ} (hσm2 : 0 < σm2)
    (hDeferred : wDeferred ∈ Ioc (0 : ℝ) 1)
    (hBaseline : wBaseline ∈ Ioc (0 : ℝ) 1)
    (hweight : wDeferred < wBaseline) :
    stationaryEvidenceMSE 0 σm2 wDeferred < stationaryEvidenceMSE 0 σm2 wBaseline :=
  stationaryEvidenceMSE_strictMonoOn hσm2 hDeferred hBaseline hweight

/-- The exact, nondegenerate mathematical content of Paper II's noisy-evidence proposition. -/
structure NoisyEvidenceAtStationarityConclusions (bm σm2 : ℝ) : Prop where
  stationary_mean_unique : ∀ w ∈ Ioc (0 : ℝ) 1, ∀ mean : ℝ,
    (mean = (1 - w) * mean + w * bm ↔ mean = bm)
  stationary_variance_fixed : ∀ w ∈ Ioc (0 : ℝ) 1,
    stationaryEvidenceVariance w σm2 =
      (1 - w) ^ 2 * stationaryEvidenceVariance w σm2 + w ^ 2 * σm2
  stationary_variance_unique : ∀ w ∈ Ioc (0 : ℝ) 1, ∀ V : ℝ,
    (V = (1 - w) ^ 2 * V + w ^ 2 * σm2 ↔
      V = stationaryEvidenceVariance w σm2)
  derivative : ∀ w ∈ Ioc (0 : ℝ) 1,
    deriv (stationaryEvidenceMSE bm σm2) w = 2 * σm2 / (2 - w) ^ 2
  strictly_increasing :
    StrictMonoOn (stationaryEvidenceMSE bm σm2) (Ioc (0 : ℝ) 1)
  unbiased_deference_smoothing : ∀ wDeferred ∈ Ioc (0 : ℝ) 1,
    ∀ wBaseline ∈ Ioc (0 : ℝ) 1, wDeferred < wBaseline →
      stationaryEvidenceMSE 0 σm2 wDeferred < stationaryEvidenceMSE 0 σm2 wBaseline

/--
Paper II, Proposition 5.5 (`prop:ar1`), `civic_drift.tex:865`.

The paper's conditions `0 < w ≤ 1` and `0 < σm²` give unique stationary
moments and strict monotonicity. The stochastic one-step mean and variance
identities are `integral_ar1ErrorStep` and
`variance_ar1ErrorStep`; `ar1ErrorStep_preserves_stationaryMoments` and
`ar1_stationaryMSE_eq` connect them to the displayed stationary MSE.
-/
theorem noisyEvidenceAtStationarity
    {bm σm2 : ℝ} (hσm2 : 0 < σm2) :
    NoisyEvidenceAtStationarityConclusions bm σm2 := by
  constructor
  · intro w hw mean
    exact ar1_stationaryMean_iff (by linarith [hw.1])
  · intro w hw
    exact stationaryEvidenceVariance_fixed (by linarith [hw.2])
  · intro w hw V
    exact ar1_stationaryVariance_iff (by linarith [hw.1]) (by linarith [hw.2])
  · intro w hw
    exact (hasDerivAt_stationaryEvidenceMSE bm σm2 w (by linarith [hw.2])).deriv
  · exact stationaryEvidenceMSE_strictMonoOn hσm2
  · intro wDeferred hDeferred wBaseline hBaseline hweight
    exact unbiased_stationaryMSE_strictly_improves_with_deference
      hσm2 hDeferred hBaseline hweight

/-- At zero evidence weight every variance is stationary, so the displayed value is not unique. -/
theorem ar1_zeroWeight_stationaryVariance_nonunique (σm2 : ℝ) :
    stationaryEvidenceVariance 0 σm2 = 0 ∧
      (1 : ℝ) = (1 - 0) ^ 2 * 1 + 0 ^ 2 * σm2 ∧
      (1 : ℝ) ≠ stationaryEvidenceVariance 0 σm2 := by
  norm_num [stationaryEvidenceVariance]

/-- With deterministic evidence, the displayed stationary MSE is constant in `w`. -/
theorem stationaryEvidenceMSE_zeroVariance (bm w : ℝ) :
    stationaryEvidenceMSE bm 0 w = bm ^ 2 := by
  simp [stationaryEvidenceMSE, stationaryEvidenceVariance]

/-- Zero innovation variance refutes the paper's unqualified strict-monotonicity claim. -/
theorem stationaryEvidenceMSE_not_strictMonoOn_zeroVariance (bm : ℝ) :
    ¬StrictMonoOn (stationaryEvidenceMSE bm 0) (Ioc (0 : ℝ) 1) := by
  intro hstrict
  have hlt := hstrict (a := (1 / 2 : ℝ)) (b := 1)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [stationaryEvidenceMSE_zeroVariance] at hlt
  exact (lt_irrefl _ hlt)

#print axioms hasDerivAt_mseQuadratic
#print axioms hasDerivAt_effectiveHorizonWeight
#print axioms hasDerivAt_horizonMSE
#print axioms one_le_horizonOptimalWeight_iff
#print axioms horizonOptimalWeight_lt_one_iff
#print axioms horizonOptimalWeight_mem_Ioo
#print axioms horizonThreshold_pos
#print axioms natCast_lt_horizonThreshold_iff
#print axioms horizonThreshold_lt_natCast_iff
#print axioms horizon_fullResponsiveness_counterexample
#print axioms horizonMSE_deriv_zero_pos_of_before_threshold
#print axioms horizonMSE_deriv_zero_neg_of_after_threshold
#print axioms one_le_displacementRatio_iff
#print axioms errorCorrelation_orders_of_truth_left
#print axioms errorCorrelation_orders_of_truth_right
#print axioms effectiveHorizonWeight_lt_one
#print axioms horizonMSE_strictMonoOn_of_no_inversion
#print axioms horizonDichotomy
#print axioms horizonThreshold_nonneg
#print axioms horizonResidualRoot_pos
#print axioms horizonResidualRoot_lt_one
#print axioms horizonResidualRoot_pow
#print axioms effectiveHorizonWeight_accuracyOptimalDeference_eq
#print axioms effectiveHorizonWeight_strictAntiOn_fullExtraction
#print axioms mseQuadratic_sub_horizonOptimalWeight_eq
#print axioms effectiveHorizonWeight_zero_gt_of_after_threshold
#print axioms accuracyOptimalDeference_mem_Ioo
#print axioms accuracyOptimalDeference_strictMonoOn
#print axioms horizonResidualRoot_tendsto_one
#print axioms accuracyOptimalDeference_tendsto_one
#print axioms accuracyOptimalDeferenceUnderRepetition
#print axioms horizonThreshold_strictAnti_responsiveness
#print axioms CredulityBandConclusions.reversal_of_oneStep_positive
#print axioms inversionBands
#print axioms inversionBands_fullResponsiveness_counterexample
#print axioms inversionBands_oneStep_reversal_counterexample
#print axioms horizonMSE_deriv_zero_pos_of_no_inversion
#print axioms straddlePermanence
#print axioms straddlePermanence_of_mean_geometry
#print axioms integral_ar1ErrorStep
#print axioms integral_ar1ErrorStep_eq_commonMean
#print axioms variance_ar1ErrorStep
#print axioms integral_sq_eq_variance_add_sq_integral
#print axioms ar1_stationaryMean_iff
#print axioms stationaryEvidenceVariance_fixed
#print axioms ar1_stationaryVariance_iff
#print axioms ar1ErrorStep_preserves_stationaryMoments
#print axioms ar1_stationaryMSE_eq
#print axioms stationaryEvidenceMSE_strictMonoOn
#print axioms hasDerivAt_stationaryEvidenceMSE
#print axioms unbiased_stationaryMSE_strictly_improves_with_deference
#print axioms noisyEvidenceAtStationarity
#print axioms ar1_zeroWeight_stationaryVariance_nonunique
#print axioms stationaryEvidenceMSE_zeroVariance
#print axioms stationaryEvidenceMSE_not_strictMonoOn_zeroVariance

end

end CivicAlignment.PaperII
