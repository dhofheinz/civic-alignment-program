/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.Basic
import CivicAlignment.ClippedStep
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Endogenous deference and bistability

This file formalizes the claim-portfolio aggregation and the planar loop from
Paper II.  The aggregation theorem exposes the probabilistic mechanism behind
the paper's conditional-mean stock recursion: current claim sizes are known at
time `t`, survival has conditional mean `1 - λ₀`, and arrivals have conditional
mean `I`.
-/

open scoped BigOperators MeasureTheory

namespace CivicAlignment.PaperII

noncomputable section

open MeasureTheory

/-! ## Exact claim-portfolio aggregation -/

/-- The total squared deviation of the active finite claim portfolio. -/
def disagreementStock {ι Ω : Type*} [Fintype ι] (deviation : ι → Ω → ℝ) : Ω → ℝ :=
  ∑ i, fun ω ↦ (deviation i ω) ^ 2

/-- A claim's squared deviation after the representative evidence exposure. -/
def exposedDeviationSq (p : LoopParams) (β x : ℝ) : ℝ :=
  ((1 - p.η * (1 - β)) * x) ^ 2

/-- The next-period stock before taking its conditional expectation. -/
def nextDisagreementStock {ι Ω : Type*} [Fintype ι] (p : LoopParams) (β : ℝ)
    (deviation survival : ι → Ω → ℝ) (arrivals : Ω → ℝ) : Ω → ℝ :=
  (∑ i, fun ω ↦ exposedDeviationSq p β (deviation i ω) * survival i ω) + arrivals

/-- Exposure scales each claim's squared deviation by the exact square factor. -/
theorem exposedDeviationSq_eq (p : LoopParams) (β x : ℝ) :
    exposedDeviationSq p β x = (1 - p.η * (1 - β)) ^ 2 * x ^ 2 := by
  simp only [exposedDeviationSq]
  ring

set_option maxHeartbeats 800000 in
-- Conditional-expectation normalization over the finite portfolio needs the larger budget.
/--
Paper II, Lemma 3.1 (`lem:agg`), `civic_drift.tex:111`.

For a finite active portfolio, suppose claim sizes are measurable with respect
to the current information `𝓕ₜ`, each survival indicator has conditional mean
`1 - λ₀`, and new arrivals have conditional mean `I`.  Then the exact
conditional mean of next period's stock is `s(β) D + I`.

The constant conditional-survival hypothesis is the formal content of
"retiral is independent of size."  The variables are typed as reals so that
the theorem only assumes the two conditional moments it uses; an actual
zero-one survival indicator is an immediate instance.
-/
theorem aggregateAgreement {ι Ω : Type*} [Fintype ι] [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (𝓕 : MeasurableSpace Ω) (hm : 𝓕 ≤ mΩ)
    [SigmaFinite (μ.trim hm)] (p : LoopParams) (β : ℝ)
    (deviation survival : ι → Ω → ℝ) (arrivals : Ω → ℝ)
    (hdeviation : ∀ i, AEStronglyMeasurable[𝓕] (fun ω ↦ (deviation i ω) ^ 2) μ)
    (hsurvival : ∀ i, Integrable (survival i) μ)
    (hcontribution : ∀ i, Integrable
      (fun ω ↦ exposedDeviationSq p β (deviation i ω) * survival i ω) μ)
    (harrivals : Integrable arrivals μ)
    (hsurvivalMean : ∀ i,
      μ[survival i | 𝓕] =ᵐ[μ] fun _ ↦ 1 - p.lambda₀)
    (harrivalMean : μ[arrivals | 𝓕] =ᵐ[μ] fun _ ↦ p.I) :
    μ[nextDisagreementStock p β deviation survival arrivals | 𝓕] =ᵐ[μ]
      fun ω ↦ p.s β * disagreementStock deviation ω + p.I := by
  have hmeasurable (i : ι) : AEStronglyMeasurable[𝓕]
      (fun ω ↦ exposedDeviationSq p β (deviation i ω)) μ := by
    simpa only [exposedDeviationSq_eq] using
      (hdeviation i).const_mul ((1 - p.η * (1 - β)) ^ 2)
  have hclaim (i : ι) :
      μ[fun ω ↦ exposedDeviationSq p β (deviation i ω) * survival i ω | 𝓕] =ᵐ[μ]
        fun ω ↦ exposedDeviationSq p β (deviation i ω) * (1 - p.lambda₀) := by
    exact (condExp_mul_of_aestronglyMeasurable_left (hmeasurable i)
      (hcontribution i) (hsurvival i)).trans
        ((Filter.EventuallyEq.rfl.mul (hsurvivalMean i)))
  have hsumIntegrable : Integrable
      (∑ i, fun ω ↦ exposedDeviationSq p β (deviation i ω) * survival i ω) μ :=
    integrable_finsetSum' Finset.univ fun i _ ↦ hcontribution i
  calc
    μ[nextDisagreementStock p β deviation survival arrivals | 𝓕] =ᵐ[μ]
        μ[(∑ i, fun ω ↦ exposedDeviationSq p β (deviation i ω) * survival i ω) | 𝓕] +
          μ[arrivals | 𝓕] := by
      simpa only [nextDisagreementStock] using condExp_add hsumIntegrable harrivals 𝓕
    _ =ᵐ[μ]
        (∑ i, μ[fun ω ↦ exposedDeviationSq p β (deviation i ω) * survival i ω | 𝓕]) +
          μ[arrivals | 𝓕] :=
      (condExp_finsetSum (s := Finset.univ) (fun i _ ↦ hcontribution i) 𝓕).add
        Filter.EventuallyEq.rfl
    _ =ᵐ[μ]
        (∑ i, fun ω ↦ exposedDeviationSq p β (deviation i ω) * (1 - p.lambda₀)) +
          (fun _ ↦ p.I) := by
      exact (eventuallyEq_sum fun i _ ↦ hclaim i).add harrivalMean
    _ =ᵐ[μ] fun ω ↦ p.s β * disagreementStock deviation ω + p.I := by
      filter_upwards [] with ω
      simp only [Pi.add_apply, Finset.sum_apply, disagreementStock, exposedDeviationSq_eq,
        LoopParams.s]
      rw [Finset.mul_sum]
      apply congrArg (fun z : ℝ ↦ z + p.I)
      apply Finset.sum_congr rfl
      intro i _
      ring

/-! ## Mechanism lemmas -/

/-- The derivative of the marginal satisfaction gradient with respect to the stock. -/
theorem hasDerivAt_gradU_stock (p : LoopParams) (β D : ℝ) :
    HasDerivAt (fun stock ↦ p.gradU β stock) (2 * p.c * (1 - p.c * β)) D := by
  have hlinear : HasDerivAt (fun stock : ℝ ↦ 2 * p.c * (1 - p.c * β) * stock)
      (2 * p.c * (1 - p.c * β)) D := by
    simpa using (hasDerivAt_id D).const_mul (2 * p.c * (1 - p.c * β))
  simpa only [LoopParams.gradU] using hlinear.const_add (-p.v)

/--
Paper II, Lemma 3.3 (`lem:ratchet`), `civic_drift.tex:149`.

The mixed partial `∂²U / ∂β ∂D` is exactly `2c(1-cβ)` and is strictly
positive for the paper's primitive range `0 < c < 1`, `β ∈ [0,1]`.
-/
theorem ratchet (p : LoopParams) (β D : ℝ) (hc₀ : 0 < p.c) (hc₁ : p.c < 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun stock ↦ p.gradU β stock) (2 * p.c * (1 - p.c * β)) D ∧
      0 < 2 * p.c * (1 - p.c * β) := by
  have hcb : p.c * β < 1 := calc
    p.c * β ≤ p.c * 1 := mul_le_mul_of_nonneg_left hβ.2 hc₀.le
    _ = p.c := mul_one p.c
    _ < 1 := hc₁
  exact ⟨hasDerivAt_gradU_stock p β D, mul_pos (mul_pos two_pos hc₀) (sub_pos.mpr hcb)⟩

/-- The policy derivative of the next-period stock is `s'(β)D`. -/
theorem hasDerivAt_stockStep_policy (p : LoopParams) (β D : ℝ) :
    HasDerivAt (fun policy ↦ p.stockStep policy D) (p.sSlope β * D) β := by
  simpa only [LoopParams.stockStep, add_zero] using
    (((p.hasDerivAt_s β).add_const p.g).mul_const D).add_const p.I

/--
Paper II, Lemma 3.4 (`lem:manu`), `civic_drift.tex:153`.

Deference weakly preserves disagreement: on the paper's primitive box, the
policy derivative of the stock transition is `s'(β)D ≥ 0`.
-/
theorem manufacture (p : LoopParams) (β D : ℝ) (hη₀ : 0 < p.η) (hη₁ : p.η ≤ 1)
    (_hlambda₀ : 0 < p.lambda₀) (hlambda₁ : p.lambda₀ < 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1)
    (hD : 0 ≤ D) :
    HasDerivAt (fun policy ↦ p.stockStep policy D) (p.sSlope β * D) β ∧
      0 ≤ p.sSlope β * D := by
  have hOneSubBeta : 0 ≤ 1 - β := sub_nonneg.mpr hβ.2
  have hOneSubBeta_le : 1 - β ≤ 1 := by linarith [hβ.1]
  have hηprod_le : p.η * (1 - β) ≤ 1 := calc
    p.η * (1 - β) ≤ 1 * (1 - β) := mul_le_mul_of_nonneg_right hη₁ hOneSubBeta
    _ = 1 - β := one_mul (1 - β)
    _ ≤ 1 := hOneSubBeta_le
  have hinner : 0 ≤ 1 - p.η * (1 - β) := sub_nonneg.mpr hηprod_le
  have hsSlope : 0 ≤ p.sSlope β := by
    simp only [LoopParams.sSlope]
    positivity
  exact ⟨hasDerivAt_stockStep_policy p β D, mul_nonneg hsSlope hD⟩

/-- The per-type affine deviation update used in `lem:knife`. -/
def injectedDeviationStep (η d ι x : ℝ) : ℝ :=
  (1 - evidenceWeight η d) * x + ι

/-- The finite stationary deviation away from the zero-evidence boundary. -/
def stationaryDeviation (η d ι : ℝ) : ℝ :=
  ι / evidenceWeight η d

/-- The knife-edge identity in denominator-free form, valid even when `w = 0`. -/
theorem satisfactionConservation_crossMul (η d : ℝ) :
    η ^ 2 * (1 - d) ^ 2 = evidenceWeight η d ^ 2 := by
  simp only [evidenceWeight]
  ring

/-- The paper's quotient identity on its mathematically defined domain. -/
theorem satisfactionConservation_ratio (η d : ℝ) (hη : η ≠ 0) (hd : d ≠ 1) :
    (1 - d) ^ 2 / evidenceWeight η d ^ 2 = 1 / η ^ 2 := by
  have hOneSub : 1 - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hd)
  simp only [evidenceWeight]
  field_simp [hη, hOneSub]

/-- The stated affine stationary deviation is indeed a fixed point whenever `w ≠ 0`. -/
theorem stationaryDeviation_fixed (η d ι : ℝ) (hη : η ≠ 0) (hd : d ≠ 1) :
    injectedDeviationStep η d ι (stationaryDeviation η d ι) =
      stationaryDeviation η d ι := by
  have hOneSub : 1 - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hd)
  simp only [injectedDeviationStep, stationaryDeviation, evidenceWeight]
  field_simp [hη, hOneSub]
  ring

/-- At the affine fixed point, the squared agreement gap is policy-free. -/
theorem stationaryAgreementGap_eq (η d ι : ℝ) (hη : η ≠ 0) (hd : d ≠ 1) :
    (1 - d) ^ 2 * stationaryDeviation η d ι ^ 2 = ι ^ 2 / η ^ 2 := by
  have hOneSub : 1 - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hd)
  simp only [stationaryDeviation, evidenceWeight]
  field_simp [hη, hOneSub]

/-- With nonzero injection, full deference has no finite affine fixed point. -/
theorem no_stationaryDeviation_at_full_deference (η ι : ℝ) (hι : ι ≠ 0) :
    ∀ x, injectedDeviationStep η 1 ι x ≠ x := by
  intro x hfixed
  apply hι
  simp only [injectedDeviationStep, evidenceWeight] at hfixed
  linarith

/--
Paper II, Lemma 3.5 (`lem:knife`), `civic_drift.tex:157`.

For effective deference `d = (1-e)β`, the exact quotient identity, affine
fixed point, and policy-free stationary squared gap all hold whenever evidence
weight is nonzero.  The global cross-multiplied identity and the full-deference
nonexistence theorem above make the paper's endpoint caveat explicit.
-/
theorem satisfactionConservation (η e β ι : ℝ) (hη : η ≠ 0)
    (hdeference : (1 - e) * β ≠ 1) :
    let d := (1 - e) * β
    (1 - d) ^ 2 / evidenceWeight η d ^ 2 = 1 / η ^ 2 ∧
      injectedDeviationStep η d ι (stationaryDeviation η d ι) =
        stationaryDeviation η d ι ∧
      (1 - d) ^ 2 * stationaryDeviation η d ι ^ 2 = ι ^ 2 / η ^ 2 := by
  dsimp only
  exact ⟨satisfactionConservation_ratio η ((1 - e) * β) hη hdeference,
    stationaryDeviation_fixed η ((1 - e) * β) ι hη hdeference,
    stationaryAgreementGap_eq η ((1 - e) * β) ι hη hdeference⟩

/-- The residual output-to-prior exposure `u = 1 - d` for extraction `e`. -/
def remainingExposure (e β : ℝ) : ℝ :=
  1 - (1 - e) * β

/-- The stationary denominator `w - ζ` in the feedback model. -/
def feedbackDenominator (η e ζ β : ℝ) : ℝ :=
  η * remainingExposure e β - ζ

/-- The affine feedback update from `prop:myopia`. -/
def feedbackDeviationStep (η e ζ ι β x : ℝ) : ℝ :=
  (1 - η * remainingExposure e β + ζ) * x + ι

/-- The finite stationary deviation in the feedback model. -/
def feedbackStationaryDeviation (η e ζ ι β : ℝ) : ℝ :=
  ι / feedbackDenominator η e ζ β

/-- The stationary squared agreement gap in the feedback model. -/
def feedbackStationaryGap (η e ζ ι β : ℝ) : ℝ :=
  ι ^ 2 * remainingExposure e β ^ 2 / feedbackDenominator η e ζ β ^ 2

/-- The instantaneous agreement reward at held-fixed deviation. -/
def instantaneousAgreementGradient (e β x : ℝ) : ℝ :=
  2 * (1 - e) * remainingExposure e β * x ^ 2

/-- The feedback stationary value is an exact fixed point when `w - ζ ≠ 0`. -/
theorem feedbackStationaryDeviation_fixed (η e ζ ι β : ℝ)
    (hden : feedbackDenominator η e ζ β ≠ 0) :
    feedbackDeviationStep η e ζ ι β (feedbackStationaryDeviation η e ζ ι β) =
      feedbackStationaryDeviation η e ζ ι β := by
  have hden' : η * remainingExposure e β - ζ ≠ 0 := by
    simpa only [feedbackDenominator] using hden
  simp only [feedbackDeviationStep, feedbackStationaryDeviation, feedbackDenominator]
  field_simp [hden']
  ring

/-- The derivative of the stationary gap with respect to deference. -/
theorem hasDerivAt_feedbackStationaryGap (η e ζ ι β : ℝ)
    (hden : feedbackDenominator η e ζ β ≠ 0) :
    HasDerivAt (feedbackStationaryGap η e ζ ι)
      (2 * ι ^ 2 * ζ * (1 - e) * remainingExposure e β /
        feedbackDenominator η e ζ β ^ 3) β := by
  have hden' : η * remainingExposure e β - ζ ≠ 0 := by
    simpa only [feedbackDenominator] using hden
  have hu : HasDerivAt (remainingExposure e) (-(1 - e)) β := by
    have hlinear : HasDerivAt (fun x : ℝ ↦ (1 - e) * x) (1 - e) β := by
      simpa using (hasDerivAt_id β).const_mul (1 - e)
    change HasDerivAt (fun x : ℝ ↦ 1 - (1 - e) * x) (-(1 - e)) β
    exact hlinear.const_sub 1
  have hnum : HasDerivAt
      (fun x ↦ ι ^ 2 * remainingExposure e x ^ 2)
      (ι ^ 2 * (2 * remainingExposure e β * (-(1 - e)))) β :=
    ((hu.pow 2).const_mul (ι ^ 2)).congr_deriv (by norm_num)
  have hdenBase : HasDerivAt (feedbackDenominator η e ζ)
      (η * (-(1 - e))) β := by
    change HasDerivAt (fun x ↦ η * remainingExposure e x - ζ) (η * (-(1 - e))) β
    exact (hu.const_mul η).sub_const ζ
  have hdenSq : HasDerivAt (fun x ↦ feedbackDenominator η e ζ x ^ 2)
      (2 * feedbackDenominator η e ζ β * (η * (-(1 - e)))) β :=
    (hdenBase.pow 2).congr_deriv (by norm_num)
  exact (hnum.div hdenSq (pow_ne_zero 2 hden)).congr_deriv (by
    simp only [feedbackDenominator]
    field_simp [hden']
    ring)

/-- On every contracting policy interval, the stationary gap strictly rises with deference. -/
theorem feedbackStationaryGap_strictMonoOn (η e ζ ι B : ℝ) (hη : 0 < η)
    (_he₀ : 0 ≤ e) (he₁ : e < 1) (hζ : 0 < ζ) (hι : ι ≠ 0)
    (_hB₀ : 0 ≤ B) (_hB₁ : B ≤ 1)
    (hcontract : ζ < η * remainingExposure e B) :
    StrictMonoOn (feedbackStationaryGap η e ζ ι) (Set.Icc (0 : ℝ) B) := by
  have ha : 0 < 1 - e := sub_pos.mpr he₁
  have hdenPos : ∀ β ∈ Set.Icc (0 : ℝ) B, 0 < feedbackDenominator η e ζ β := by
    intro β hβ
    have hmul : (1 - e) * β ≤ (1 - e) * B :=
      mul_le_mul_of_nonneg_left hβ.2 ha.le
    have hu : remainingExposure e B ≤ remainingExposure e β := by
      simp only [remainingExposure]
      linarith
    have hηu : η * remainingExposure e B ≤ η * remainingExposure e β :=
      mul_le_mul_of_nonneg_left hu hη.le
    simp only [feedbackDenominator]
    linarith
  have hderiv : ∀ β ∈ Set.Icc (0 : ℝ) B,
      HasDerivAt (feedbackStationaryGap η e ζ ι)
        (2 * ι ^ 2 * ζ * (1 - e) * remainingExposure e β /
          feedbackDenominator η e ζ β ^ 3) β := by
    intro β hβ
    exact hasDerivAt_feedbackStationaryGap η e ζ ι β (ne_of_gt (hdenPos β hβ))
  refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc (0 : ℝ) B)
    (fun β hβ ↦ (hderiv β hβ).continuousAt.continuousWithinAt)
    (fun β hβ ↦ (hderiv β (interior_subset hβ)).hasDerivWithinAt) ?_
  intro β hβ
  have hβIcc : β ∈ Set.Icc (0 : ℝ) B := interior_subset hβ
  have hdenβ : 0 < feedbackDenominator η e ζ β := hdenPos β hβIcc
  have hηu : 0 < η * remainingExposure e β := by
    simp only [feedbackDenominator] at hdenβ
    linarith
  have hu : 0 < remainingExposure e β := by
    rcases mul_pos_iff.mp hηu with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge hη.le hneg.1).elim
  have hιsq : 0 < ι ^ 2 := sq_pos_of_ne_zero hι
  positivity

/-- The instantaneous agreement gradient is positive at every feedback stationary point. -/
theorem instantaneousAgreementGradient_stationary_pos (η e ζ ι β : ℝ)
    (hη : 0 < η) (he : e < 1) (hζ : 0 < ζ) (hι : ι ≠ 0)
    (hcontract : ζ < η * remainingExposure e β) :
    0 < instantaneousAgreementGradient e β
      (feedbackStationaryDeviation η e ζ ι β) := by
  have hηu : 0 < η * remainingExposure e β := lt_trans hζ hcontract
  have hu : 0 < remainingExposure e β := by
    rcases mul_pos_iff.mp hηu with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge hη.le hneg.1).elim
  have hden : feedbackDenominator η e ζ β ≠ 0 := by
    simp only [feedbackDenominator]
    linarith
  have hx : feedbackStationaryDeviation η e ζ ι β ≠ 0 := by
    simp only [feedbackStationaryDeviation]
    exact div_ne_zero hι hden
  simp only [instantaneousAgreementGradient]
  positivity

/--
Paper II, Proposition 3.6 (`prop:myopia`), `civic_drift.tex:168`.

On any policy interval where `0 < ζ < w`, the feedback fixed point has the
paper's exact closed form, its squared agreement gap strictly increases with
deference, stationary satisfaction strictly decreases, and the instantaneous
agreement gradient at that stationary belief is strictly positive.
-/
theorem myopiaTrap (η e ζ ι B : ℝ) (hη : 0 < η) (he₀ : 0 ≤ e) (he₁ : e < 1)
    (hζ : 0 < ζ) (hι : ι ≠ 0) (hB₀ : 0 ≤ B) (hB₁ : B ≤ 1)
    (hcontract : ζ < η * remainingExposure e B) :
    (∀ β ∈ Set.Icc (0 : ℝ) B,
      feedbackDeviationStep η e ζ ι β (feedbackStationaryDeviation η e ζ ι β) =
        feedbackStationaryDeviation η e ζ ι β) ∧
    StrictMonoOn (feedbackStationaryGap η e ζ ι) (Set.Icc (0 : ℝ) B) ∧
    StrictAntiOn (fun β ↦ -feedbackStationaryGap η e ζ ι β) (Set.Icc (0 : ℝ) B) ∧
    ∀ β ∈ Set.Icc (0 : ℝ) B,
      0 < instantaneousAgreementGradient e β
        (feedbackStationaryDeviation η e ζ ι β) := by
  have hmono := feedbackStationaryGap_strictMonoOn η e ζ ι B hη he₀ he₁ hζ hι
    hB₀ hB₁ hcontract
  refine ⟨?_, hmono, ?_, ?_⟩
  · intro β hβ
    have hmul : (1 - e) * β ≤ (1 - e) * B :=
      mul_le_mul_of_nonneg_left hβ.2 (sub_nonneg.mpr he₁.le)
    have hu : remainingExposure e B ≤ remainingExposure e β := by
      simp only [remainingExposure]
      linarith
    have hηu := mul_le_mul_of_nonneg_left hu hη.le
    apply feedbackStationaryDeviation_fixed
    simp only [feedbackDenominator]
    linarith
  · intro β₁ hβ₁ β₂ hβ₂ hlt
    exact neg_lt_neg (hmono hβ₁ hβ₂ hlt)
  · intro β hβ
    have hmul : (1 - e) * β ≤ (1 - e) * B :=
      mul_le_mul_of_nonneg_left hβ.2 (sub_nonneg.mpr he₁.le)
    have hu : remainingExposure e B ≤ remainingExposure e β := by
      simp only [remainingExposure]
      linarith
    have hηu := mul_le_mul_of_nonneg_left hu hη.le
    exact instantaneousAgreementGradient_stationary_pos η e ζ ι β hη he₁ hζ hι (by linarith)

/-! ## The absorbing-box claim -/

/-- The standing primitive restrictions for Paper II's scalar loop. -/
structure DriftModelAssumptions (p : LoopParams) : Prop where
  η_pos : 0 < p.η
  η_le_one : p.η ≤ 1
  lambda₀_pos : 0 < p.lambda₀
  lambda₀_lt_one : p.lambda₀ < 1
  I_pos : 0 < p.I
  v_pos : 0 < p.v
  c_pos : 0 < p.c
  c_lt_one : p.c < 1
  α_pos : 0 < p.α
  no_content_gain : p.g = 0

/-- Paper II's proposed compact stock box. -/
def absorbingBox (p : LoopParams) : Set LoopState :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc p.I (p.I / p.lambda₀)

/-- On the policy interval, the Paper II stock multiplier lies in `[0,1-λ₀]`. -/
theorem driftStockMultiplier_nonneg_le {p : LoopParams} (model : DriftModelAssumptions p)
    {β : ℝ} (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ p.s β ∧ p.s β ≤ 1 - p.lambda₀ := by
  have hresidual_nonneg : 0 ≤ 1 - β := sub_nonneg.mpr hβ.2
  have hresidual_le_one : 1 - β ≤ 1 := by linarith [hβ.1]
  have hproduct_nonneg : 0 ≤ p.η * (1 - β) :=
    mul_nonneg model.η_pos.le hresidual_nonneg
  have hproduct_le_one : p.η * (1 - β) ≤ 1 := calc
    p.η * (1 - β) ≤ p.η * 1 :=
      mul_le_mul_of_nonneg_left hresidual_le_one model.η_pos.le
    _ = p.η := mul_one p.η
    _ ≤ 1 := model.η_le_one
  have hinner_nonneg : 0 ≤ 1 - p.η * (1 - β) := sub_nonneg.mpr hproduct_le_one
  have hinner_le_one : 1 - p.η * (1 - β) ≤ 1 := by linarith
  have hsquare_le : (1 - p.η * (1 - β)) ^ 2 ≤ (1 : ℝ) ^ 2 :=
    (sq_le_sq₀ hinner_nonneg zero_le_one).2 hinner_le_one
  have hgrounding : 0 ≤ 1 - p.lambda₀ := sub_nonneg.mpr model.lambda₀_lt_one.le
  constructor
  · simp only [LoopParams.s]
    exact mul_nonneg hgrounding (sq_nonneg _)
  · simp only [LoopParams.s]
    simpa only [one_pow, mul_one] using mul_le_mul_of_nonneg_left hsquare_le hgrounding

/-- The set called `B` in `lem:box` really is forward invariant. -/
theorem invariantBox {p : LoopParams} (model : DriftModelAssumptions p) :
    Set.MapsTo p.loopMap (absorbingBox p) (absorbingBox p) := by
  intro x hx
  have hβ : x.1 ∈ Set.Icc (0 : ℝ) 1 := hx.1
  have hD : x.2 ∈ Set.Icc p.I (p.I / p.lambda₀) := hx.2
  have hs := driftStockMultiplier_nonneg_le model hβ
  have hDnonneg : 0 ≤ x.2 := le_trans model.I_pos.le hD.1
  have hlambda : p.lambda₀ ≠ 0 := ne_of_gt model.lambda₀_pos
  have hceiling_nonneg : 0 ≤ p.I / p.lambda₀ :=
    div_nonneg model.I_pos.le model.lambda₀_pos.le
  have hstockLower : p.I ≤ p.stockStep x.1 x.2 := by
    simp only [LoopParams.stockStep, model.no_content_gain, add_zero]
    exact le_add_of_nonneg_left (mul_nonneg hs.1 hDnonneg)
  have hproduct : p.s x.1 * x.2 ≤ (1 - p.lambda₀) * (p.I / p.lambda₀) :=
    mul_le_mul hs.2 hD.2 hDnonneg (sub_nonneg.mpr model.lambda₀_lt_one.le)
  have hceiling : (1 - p.lambda₀) * (p.I / p.lambda₀) + p.I =
      p.I / p.lambda₀ := by
    field_simp [hlambda]
    ring
  have hstockUpper : p.stockStep x.1 x.2 ≤ p.I / p.lambda₀ := by
    simp only [LoopParams.stockStep, model.no_content_gain, add_zero]
    linarith
  exact ⟨LoopParams.clipUnit_mem _, hstockLower, hstockUpper⟩

/-- The exact stock path above the claimed ceiling when policy stays at `β=1`. -/
def capturedAboveCeilingPath (p : LoopParams) (δ : ℝ) (n : ℕ) : ℝ :=
  p.I / p.lambda₀ + (1 - p.lambda₀) ^ n * δ

/-- A state sequence follows the simultaneous Paper II loop map. -/
def IsLoopTrajectory (p : LoopParams) (x : ℕ → LoopState) : Prop :=
  ∀ n, x (n + 1) = p.loopMap (x n)

/-- The coupled captured trajectory associated with a positive stock excess. -/
def capturedAboveCeilingTrajectory (p : LoopParams) (δ : ℝ) (n : ℕ) : LoopState :=
  (1, capturedAboveCeilingPath p δ n)

/-- The above-ceiling path obeys the Paper II stock update at `β=1`. -/
theorem capturedAboveCeilingPath_succ {p : LoopParams} (model : DriftModelAssumptions p)
    (δ : ℝ) (n : ℕ) :
    p.stockStep 1 (capturedAboveCeilingPath p δ n) =
      capturedAboveCeilingPath p δ (n + 1) := by
  have hlambda : p.lambda₀ ≠ 0 := ne_of_gt model.lambda₀_pos
  simp only [LoopParams.stockStep, LoopParams.s, capturedAboveCeilingPath,
    model.no_content_gain, add_zero, sub_self, mul_zero, sub_zero, one_pow, pow_succ]
  field_simp [hlambda]
  ring

/-- A positive initial excess stays strictly above `I/λ₀` at every finite time. -/
theorem capturedAboveCeilingPath_gt {p : LoopParams} (model : DriftModelAssumptions p)
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    p.I / p.lambda₀ < capturedAboveCeilingPath p δ n := by
  simp only [capturedAboveCeilingPath, lt_add_iff_pos_right]
  exact mul_pos (pow_pos (sub_pos.mpr model.lambda₀_lt_one) n) hδ

/-- At `β=1`, `G(1)` is the gradient at the proposed stock ceiling. -/
theorem G_one_eq_gradU_ceiling {p : LoopParams} (model : DriftModelAssumptions p) :
    p.G 1 = p.gradU 1 (p.I / p.lambda₀) := by
  have hlambda : p.lambda₀ ≠ 0 := ne_of_gt model.lambda₀_pos
  simp only [LoopParams.G, LoopParams.gradU, LoopParams.s, model.no_content_gain,
    sub_self, mul_zero, sub_zero, one_pow]
  field_simp [hlambda]
  ring

/-- The captured policy remains clipped at one along the above-ceiling path. -/
theorem deferenceStep_capturedAboveCeiling {p : LoopParams} (model : DriftModelAssumptions p)
    (hG₁ : 0 < p.G 1) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    p.deferenceStep 1 (capturedAboveCeilingPath p δ n) = 1 := by
  have hD := capturedAboveCeilingPath_gt model hδ n
  have hcoeff : 0 < 2 * p.c * (1 - p.c) :=
    mul_pos (mul_pos two_pos model.c_pos) (sub_pos.mpr model.c_lt_one)
  have hgradCeiling : 0 < p.gradU 1 (p.I / p.lambda₀) := by
    rw [← G_one_eq_gradU_ceiling model]
    exact hG₁
  have hgrad : 0 < p.gradU 1 (capturedAboveCeilingPath p δ n) := by
    simp only [LoopParams.gradU, mul_one]
    simp only [LoopParams.gradU, mul_one] at hgradCeiling
    nlinarith [mul_pos hcoeff (sub_pos.mpr hD)]
  have hright : 1 ≤ 1 + p.α * p.gradU 1 (capturedAboveCeilingPath p δ n) := by
    exact le_add_of_nonneg_right (mul_nonneg model.α_pos.le hgrad.le)
  simp only [LoopParams.deferenceStep]
  exact clipUnit_eq_one_of_le hright

/-- The explicit path is a genuine trajectory of the coupled Paper II map. -/
theorem loopMap_capturedAboveCeiling {p : LoopParams} (model : DriftModelAssumptions p)
    (hG₁ : 0 < p.G 1) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    p.loopMap (1, capturedAboveCeilingPath p δ n) =
      (1, capturedAboveCeilingPath p δ (n + 1)) := by
  apply Prod.ext
  · exact deferenceStep_capturedAboveCeiling model hG₁ hδ n
  · exact capturedAboveCeilingPath_succ model δ n

/-- The explicit captured sequence obeys the simultaneous coupled map. -/
theorem capturedAboveCeiling_isTrajectory {p : LoopParams} (model : DriftModelAssumptions p)
    (hG₁ : 0 < p.G 1) {δ : ℝ} (hδ : 0 < δ) :
    IsLoopTrajectory p (capturedAboveCeilingTrajectory p δ) := by
  intro n
  exact (loopMap_capturedAboveCeiling model hG₁ hδ n).symm

/-- The coupled captured trajectory never enters the paper's exact box. -/
theorem capturedAboveCeiling_not_mem_box {p : LoopParams} (model : DriftModelAssumptions p)
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (1, capturedAboveCeilingPath p δ n) ∉ absorbingBox p := by
  intro hmem
  exact (not_le_of_gt (capturedAboveCeilingPath_gt model hδ n)) hmem.2.2

/--
Counterexample to the finite-entry clause of Paper II `lem:box`: under its
captured-corner sign condition, a nonnegative coupled trajectory can remain
strictly above the proposed box for every finite time.
-/
theorem absorbingBox_nonentry_counterexample {p : LoopParams}
    (model : DriftModelAssumptions p) (hG₁ : 0 < p.G 1) :
    ∃ x : ℕ → LoopState,
      IsLoopTrajectory p x ∧ 0 ≤ (x 0).2 ∧ ∀ n, x n ∉ absorbingBox p := by
  let δ : ℝ := 1
  refine ⟨capturedAboveCeilingTrajectory p δ,
    capturedAboveCeiling_isTrajectory model hG₁ one_pos, ?_, ?_⟩
  · have hceiling : 0 < p.I / p.lambda₀ := div_pos model.I_pos model.lambda₀_pos
    exact (lt_trans hceiling (capturedAboveCeilingPath_gt model one_pos 0)).le
  · intro n
    exact capturedAboveCeiling_not_mem_box model one_pos n

/-! ## Order preservation on the box -/

/-- Paper II, Assumption SS (`ass:ss`): the small-step bound. -/
structure SmallStepAssumption (p : LoopParams) : Prop where
  bound : 2 * p.α * p.c ^ 2 * p.I ≤ p.lambda₀

/-- The unprojected policy update input. -/
def unclippedDeferenceInput (p : LoopParams) (β D : ℝ) : ℝ :=
  β + p.α * p.gradU β D

/-- The stock multiplier is strictly increasing on the policy interval. -/
theorem driftStockMultiplier_strictMonoOn {p : LoopParams}
    (model : DriftModelAssumptions p) :
    StrictMonoOn p.s (Set.Icc (0 : ℝ) 1) := by
  intro β₁ hβ₁ β₂ hβ₂ hβ
  have hinner₁ : 0 ≤ 1 - p.η * (1 - β₁) := by
    have hresidual : 1 - β₁ ≤ 1 := by linarith [hβ₁.1]
    have hproduct : p.η * (1 - β₁) ≤ p.η := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hresidual model.η_pos.le
    linarith [model.η_le_one]
  have hinner₂ : 0 ≤ 1 - p.η * (1 - β₂) := by
    have hresidual : 1 - β₂ ≤ 1 := by linarith [hβ₂.1]
    have hproduct : p.η * (1 - β₂) ≤ p.η := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hresidual model.η_pos.le
    linarith [model.η_le_one]
  have hinner : 1 - p.η * (1 - β₁) < 1 - p.η * (1 - β₂) := by
    nlinarith [mul_pos model.η_pos (sub_pos.mpr hβ)]
  have hsquare := (sq_lt_sq₀ hinner₁ hinner₂).2 hinner
  simp only [LoopParams.s]
  exact mul_lt_mul_of_pos_left hsquare (sub_pos.mpr model.lambda₀_lt_one)

/-- Under (SS), the unprojected controller is monotone in policy throughout the box. -/
theorem unclippedDeferenceInput_mono_policy {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    {β₁ β₂ D : ℝ} (_hβ₁ : β₁ ∈ Set.Icc (0 : ℝ) 1)
    (_hβ₂ : β₂ ∈ Set.Icc (0 : ℝ) 1) (hβ : β₁ ≤ β₂)
    (hD : D ∈ Set.Icc p.I (p.I / p.lambda₀)) :
    unclippedDeferenceInput p β₁ D ≤ unclippedDeferenceInput p β₂ D := by
  have hk : 0 ≤ 2 * p.α * p.c ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) (sq_nonneg p.c)
  have hratio : 2 * p.α * p.c ^ 2 * (p.I / p.lambda₀) ≤ 1 := by
    rw [show 2 * p.α * p.c ^ 2 * (p.I / p.lambda₀) =
      (2 * p.α * p.c ^ 2 * p.I) / p.lambda₀ by ring]
    exact (div_le_iff₀ model.lambda₀_pos).2 (by simpa only [one_mul] using ss.bound)
  have hkD : 2 * p.α * p.c ^ 2 * D ≤
      2 * p.α * p.c ^ 2 * (p.I / p.lambda₀) :=
    mul_le_mul_of_nonneg_left hD.2 hk
  have hcoefficient : 0 ≤ 1 - 2 * p.α * p.c ^ 2 * D := by linarith
  have hdelta : 0 ≤ β₂ - β₁ := sub_nonneg.mpr hβ
  have hproduct := mul_nonneg hdelta hcoefficient
  simp only [unclippedDeferenceInput, LoopParams.gradU]
  nlinarith

/-- The unprojected controller is monotone in stock throughout the box. -/
theorem unclippedDeferenceInput_mono_stock {p : LoopParams}
    (model : DriftModelAssumptions p) {β D₁ D₂ : ℝ}
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hD : D₁ ≤ D₂) :
    unclippedDeferenceInput p β D₁ ≤ unclippedDeferenceInput p β D₂ := by
  have hcβ : p.c * β ≤ p.c * 1 := mul_le_mul_of_nonneg_left hβ.2 model.c_pos.le
  have hresidual : 0 ≤ 1 - p.c * β := by
    rw [mul_one] at hcβ
    linarith [model.c_lt_one]
  have hcoefficient : 0 ≤ p.α * (2 * p.c * (1 - p.c * β)) :=
    mul_nonneg model.α_pos.le
      (mul_nonneg (mul_nonneg (by norm_num) model.c_pos.le) hresidual)
  have hproduct := mul_nonneg hcoefficient (sub_nonneg.mpr hD)
  simp only [unclippedDeferenceInput, LoopParams.gradU]
  nlinarith

/--
Paper II, Lemma 3.13 (`lem:mono`), `civic_drift.tex:230`.

Under (SS), both coordinates of the simultaneous map are nondecreasing in
both inputs on `B`; composing the first coordinate with interval projection
therefore leaves the map order-preserving.
-/
theorem loopMap_monotoneOn_box {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) :
    MonotoneOn p.loopMap (absorbingBox p) := by
  intro x hx y hy hxy
  have hβx : x.1 ∈ Set.Icc (0 : ℝ) 1 := hx.1
  have hβy : y.1 ∈ Set.Icc (0 : ℝ) 1 := hy.1
  have hDx : x.2 ∈ Set.Icc p.I (p.I / p.lambda₀) := hx.2
  have hDy : y.2 ∈ Set.Icc p.I (p.I / p.lambda₀) := hy.2
  have hdeferencePolicy :=
    unclippedDeferenceInput_mono_policy model ss hβx hβy hxy.1 hDx
  have hdeferenceStock :=
    unclippedDeferenceInput_mono_stock model hβy hxy.2
  have hdeference : p.deferenceStep x.1 x.2 ≤ p.deferenceStep y.1 y.2 := by
    exact LoopParams.monotone_clipUnit (hdeferencePolicy.trans hdeferenceStock)
  have hsOrder : p.s x.1 ≤ p.s y.1 :=
    (driftStockMultiplier_strictMonoOn model).monotoneOn hβx hβy hxy.1
  have hsY : 0 ≤ p.s y.1 := (driftStockMultiplier_nonneg_le model hβy).1
  have hDxNonneg : 0 ≤ x.2 := le_trans model.I_pos.le hDx.1
  have hstockPolicy : p.s x.1 * x.2 ≤ p.s y.1 * x.2 :=
    mul_le_mul_of_nonneg_right hsOrder hDxNonneg
  have hstockStock : p.s y.1 * x.2 ≤ p.s y.1 * y.2 :=
    mul_le_mul_of_nonneg_left hxy.2 hsY
  have hstock : p.stockStep x.1 x.2 ≤ p.stockStep y.1 y.2 := by
    simp only [LoopParams.stockStep, model.no_content_gain, add_zero]
    linarith [hstockPolicy.trans hstockStock]
  exact ⟨hdeference, hstock⟩

/-! ## Hysteresis threshold -/

/-- Paper II, Assumption H (`ass:H`), including the oriented unique crossing. -/
structure ThresholdAssumption (p : LoopParams) where
  βdagger : ℝ
  βdagger_mem : βdagger ∈ Set.Ioo (0 : ℝ) 1
  G_zero : p.G βdagger = 0
  G_zero_neg : p.G 0 < 0
  G_one_pos : 0 < p.G 1
  G_neg_before : ∀ β ∈ Set.Ioo (0 : ℝ) 1, β < βdagger → p.G β < 0
  G_pos_after : ∀ β ∈ Set.Ioo (0 : ℝ) 1, βdagger < β → 0 < p.G β
  GSlope_pos : 0 < p.GSlope βdagger

/-- The gradient after adding civic weight `ρ` with normalized harm scale one. -/
def civicWeightedGradient (p : LoopParams) (ρ β D : ℝ) : ℝ :=
  p.gradU β D - ρ * D

/-- Paper II's closed-form cure threshold. -/
def cureThreshold (p : LoopParams) : ℝ :=
  2 * p.c * (1 - p.c) - p.v * p.lambda₀ / p.I

/-- The civic-weighted gradient at the captured stock factors through `ρ_cure - ρ`. -/
theorem civicWeightedGradient_captured_eq {p : LoopParams}
    (model : DriftModelAssumptions p) (ρ : ℝ) :
    civicWeightedGradient p ρ 1 (p.I / p.lambda₀) =
      (p.I / p.lambda₀) * (cureThreshold p - ρ) := by
  have hlambda : p.lambda₀ ≠ 0 := ne_of_gt model.lambda₀_pos
  have hI : p.I ≠ 0 := ne_of_gt model.I_pos
  simp only [civicWeightedGradient, LoopParams.gradU, cureThreshold, mul_one]
  field_simp [hlambda, hI]
  ring

/-- The captured corner's inward-pointing condition is exactly `ρ ≤ ρ_cure`. -/
theorem civicWeightedGradient_captured_nonneg_iff {p : LoopParams}
    (model : DriftModelAssumptions p) (ρ : ℝ) :
    0 ≤ civicWeightedGradient p ρ 1 (p.I / p.lambda₀) ↔ ρ ≤ cureThreshold p := by
  rw [civicWeightedGradient_captured_eq model]
  have hceiling : 0 < p.I / p.lambda₀ := div_pos model.I_pos model.lambda₀_pos
  rw [mul_nonneg_iff_of_pos_left hceiling, sub_nonneg]

/-- A weight above the cure threshold makes the captured-corner gradient strictly outward. -/
theorem civicWeightedGradient_captured_neg_iff {p : LoopParams}
    (model : DriftModelAssumptions p) (ρ : ℝ) :
    civicWeightedGradient p ρ 1 (p.I / p.lambda₀) < 0 ↔ cureThreshold p < ρ := by
  rw [civicWeightedGradient_captured_eq model]
  have hceiling : 0 < p.I / p.lambda₀ := div_pos model.I_pos model.lambda₀_pos
  calc
    p.I / p.lambda₀ * (cureThreshold p - ρ) < 0 ↔
        p.I / p.lambda₀ * (cureThreshold p - ρ) < p.I / p.lambda₀ * 0 := by
      rw [mul_zero]
    _ ↔ cureThreshold p - ρ < 0 := mul_lt_mul_iff_right₀ hceiling
    _ ↔ cureThreshold p < ρ := sub_neg

/-- Assumption H makes the cure threshold strictly positive. -/
theorem cureThreshold_pos {p : LoopParams} (model : DriftModelAssumptions p)
    (threshold : ThresholdAssumption p) : 0 < cureThreshold p := by
  have hgradient : 0 < p.gradU 1 (p.I / p.lambda₀) := by
    rw [← G_one_eq_gradU_ceiling model]
    exact threshold.G_one_pos
  have hfactor : 0 < (p.I / p.lambda₀) * cureThreshold p := by
    have heq : civicWeightedGradient p 0 1 (p.I / p.lambda₀) =
        (p.I / p.lambda₀) * cureThreshold p := by
      simpa only [sub_zero] using civicWeightedGradient_captured_eq model 0
    rw [← heq]
    simpa only [civicWeightedGradient, zero_mul, sub_zero] using hgradient
  exact (mul_pos_iff_of_pos_left (div_pos model.I_pos model.lambda₀_pos)).mp hfactor

/-- Adding nonnegative civic weight can only lower the satisfaction gradient. -/
theorem civicWeightedGradient_le_unweighted (p : LoopParams) {ρ β D : ℝ}
    (hρ : 0 ≤ ρ) (hD : 0 ≤ D) :
    civicWeightedGradient p ρ β D ≤ p.gradU β D := by
  simp only [civicWeightedGradient]
  exact sub_le_self _ (mul_nonneg hρ hD)

/-- An explicit neighborhood on which the unweighted calibrated gradient has a fixed margin. -/
def calibratedGradientNeighborhood (p : LoopParams) : Set LoopState :=
  {x | p.gradU x.1 x.2 < p.G 0 / 2}

/-- `G(β)` is the fixed-stock gradient evaluated at the stationary stock. -/
theorem G_eq_gradU_stationary (p : LoopParams) (β : ℝ) :
    p.G β = p.gradU β (p.stationaryStock β) := by
  simp only [LoopParams.G, LoopParams.gradU, LoopParams.stationaryStock]
  ring

/-- The calibrated gradient-margin set is a genuine neighborhood of `p₁`. -/
theorem calibratedGradientNeighborhood_mem_nhds {p : LoopParams}
    (threshold : ThresholdAssumption p) :
    calibratedGradientNeighborhood p ∈ nhds (0, p.stationaryStock 0) := by
  have hcontinuous : Continuous (fun x : LoopState ↦ p.gradU x.1 x.2) := by
    simp only [LoopParams.gradU]
    fun_prop
  apply (isOpen_lt hcontinuous continuous_const).mem_nhds
  change p.gradU 0 (p.stationaryStock 0) < p.G 0 / 2
  rw [← G_eq_gradU_stationary]
  linarith [threshold.G_zero_neg]

/-- The same calibrated neighborhood works uniformly for every nonnegative civic weight. -/
theorem calibratedGradient_uniform_in_weight {p : LoopParams}
    (threshold : ThresholdAssumption p) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {x : LoopState} (hx : x ∈ calibratedGradientNeighborhood p) (hD : 0 ≤ x.2) :
    civicWeightedGradient p ρ x.1 x.2 < p.G 0 / 2 ∧
      civicWeightedGradient p ρ x.1 x.2 < 0 := by
  have hle : civicWeightedGradient p ρ x.1 x.2 ≤ p.gradU x.1 x.2 :=
    civicWeightedGradient_le_unweighted p (β := x.1) hρ hD
  have hmargin : p.gradU x.1 x.2 < p.G 0 / 2 := hx
  have hhalf : p.G 0 / 2 < 0 := by linarith [threshold.G_zero_neg]
  exact ⟨lt_of_le_of_lt hle hmargin, lt_trans (lt_of_le_of_lt hle hmargin) hhalf⟩

/--
The import-free algebraic and uniform-neighborhood core of Paper II, Theorem 3.15
(`thm:hyst`), `civic_drift.tex:296`.

The first clause is the exact captured-corner sign threshold. The second gives
one neighborhood of the calibrated corner that works for every `ρ ≥ 0`, which
is the quantified fact used by the paper's prevention argument.
-/
theorem hysteresisAsymmetry_core {p : LoopParams} (model : DriftModelAssumptions p)
    (threshold : ThresholdAssumption p) :
    (∀ ρ, 0 ≤ civicWeightedGradient p ρ 1 (p.I / p.lambda₀) ↔
      ρ ≤ cureThreshold p) ∧
    0 < cureThreshold p ∧
    calibratedGradientNeighborhood p ∈ nhds (0, p.stationaryStock 0) ∧
    ∀ ρ ≥ 0, ∀ x ∈ calibratedGradientNeighborhood p, 0 ≤ x.2 →
      civicWeightedGradient p ρ x.1 x.2 < 0 := by
  exact ⟨fun ρ ↦ civicWeightedGradient_captured_nonneg_iff model ρ,
    cureThreshold_pos model threshold,
    calibratedGradientNeighborhood_mem_nhds threshold,
    fun ρ hρ x hx hD ↦ (calibratedGradient_uniform_in_weight threshold hρ hx hD).2⟩

/-! ## Legacy stronger stochastic template -/

/--
This stronger stochastic template predates the proved variational Arrhenius
law and is retained as a named proposition. It is not the current manuscript's
`conj:arr`; that fixed-rate saddle-passage equality is formalized as
`saddlePassageConjecture` in `SaddlePassageContinuity.lean`.

For a supplied mean escape-time function `meanEscape ρ σ` of civic weight and
positive noise scale, this proposition is the paper's exact asymptotic claim:
there exists a barrier `V`, strictly increasing for `ρ ≥ 0`, such that
`log(meanEscape ρ σ) - V ρ / σ² = O(1)` as `σ → 0⁺`.

No theorem asserts this legacy proposition.
-/
def arrheniusEscapeConjecture (meanEscape : ℝ → ℝ → ℝ) : Prop :=
  ∃ V : ℝ → ℝ,
    StrictMonoOn V (Set.Ici (0 : ℝ)) ∧
    ∀ ρ ∈ Set.Ici (0 : ℝ),
      (∀ σ, 0 < σ → 0 < meanEscape ρ σ) ∧
      Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (fun σ ↦ Real.log (meanEscape ρ σ) - V ρ / σ ^ 2)
        (fun _ ↦ (1 : ℝ))

#print axioms exposedDeviationSq_eq
#print axioms aggregateAgreement
#print axioms hasDerivAt_gradU_stock
#print axioms ratchet
#print axioms hasDerivAt_stockStep_policy
#print axioms manufacture
#print axioms satisfactionConservation_crossMul
#print axioms satisfactionConservation_ratio
#print axioms stationaryDeviation_fixed
#print axioms stationaryAgreementGap_eq
#print axioms no_stationaryDeviation_at_full_deference
#print axioms satisfactionConservation
#print axioms feedbackStationaryDeviation_fixed
#print axioms hasDerivAt_feedbackStationaryGap
#print axioms feedbackStationaryGap_strictMonoOn
#print axioms instantaneousAgreementGradient_stationary_pos
#print axioms myopiaTrap
#print axioms driftStockMultiplier_nonneg_le
#print axioms invariantBox
#print axioms capturedAboveCeilingPath_succ
#print axioms capturedAboveCeilingPath_gt
#print axioms G_one_eq_gradU_ceiling
#print axioms deferenceStep_capturedAboveCeiling
#print axioms loopMap_capturedAboveCeiling
#print axioms capturedAboveCeiling_isTrajectory
#print axioms capturedAboveCeiling_not_mem_box
#print axioms absorbingBox_nonentry_counterexample
#print axioms driftStockMultiplier_strictMonoOn
#print axioms unclippedDeferenceInput_mono_policy
#print axioms unclippedDeferenceInput_mono_stock
#print axioms loopMap_monotoneOn_box
#print axioms civicWeightedGradient_captured_eq
#print axioms civicWeightedGradient_captured_nonneg_iff
#print axioms civicWeightedGradient_captured_neg_iff
#print axioms cureThreshold_pos
#print axioms civicWeightedGradient_le_unweighted
#print axioms G_eq_gradU_stationary
#print axioms calibratedGradientNeighborhood_mem_nhds
#print axioms calibratedGradient_uniform_in_weight
#print axioms hysteresisAsymmetry_core

end

end CivicAlignment.PaperII
