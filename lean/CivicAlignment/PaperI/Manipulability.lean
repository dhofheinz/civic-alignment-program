/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperI.Capacity
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Paper I: manipulability gradients

This file formalizes the derivative-based audit expressions and the static
civic-weighted incentive result from Paper I.
-/

namespace CivicAlignment.PaperI

open Set

/-- Paper I, equation `eq:bracket`: the marginal-harm bracket along an affine weight path. -/
def marginalHarmBracket (δ δm γ η r β : ℝ) : ℝ :=
  (δ - γ) - affineEvidenceWeight η r β * (δ + δm - 2 * γ)

/-- Paper I, equation `eq:mg`: the low-minus-high type MSE gap. -/
def typeMSEGap (δH δL δm γH γL ηH ηL κ β : ℝ) : ℝ :=
  lowTypeMSE δL δm γL ηL β - highTypeMSE δH δm γH ηH κ β

/-- Paper I, Definition 5.1 (`def:mg`): the derivative of the type MSE gap. -/
noncomputable def manipulabilityGradient
    (δH δL δm γH γL ηH ηL κ β : ℝ) : ℝ :=
  deriv (typeMSEGap δH δL δm γH γL ηH ηL κ) β

/-- The derivative of a type MSE along its affine evidence-weight path. -/
theorem hasDerivAt_typeMSE (δ δm γ η r β : ℝ) :
    HasDerivAt (typeMSE δ δm γ η r)
      (2 * η * r * marginalHarmBracket δ δm γ η r β) β := by
  have hScaledId : HasDerivAt (fun x : ℝ => r * x) r β := by
    (convert! (hasDerivAt_id β).const_mul r using 1; ring)
  have hOneSubScaled : HasDerivAt (fun x : ℝ => 1 - r * x) (-r) β := by
    convert! hScaledId.const_sub (1 : ℝ) using 1
  have hWeight : HasDerivAt (fun x : ℝ => η * (1 - r * x)) (-η * r) β := by
    (convert! hOneSubScaled.const_mul η using 1; ring)
  have hResidual : HasDerivAt (fun x : ℝ => 1 - η * (1 - r * x)) (η * r) β := by
    (convert! hWeight.const_sub (1 : ℝ) using 1; ring)
  have hFirst := (hResidual.pow 2).mul_const δ
  have hSecond := (hWeight.pow 2).mul_const δm
  have hCross := ((hResidual.const_mul 2).mul hWeight).mul_const γ
  convert! (hFirst.add hSecond).add hCross using 1
  simp only [marginalHarmBracket, affineEvidenceWeight]
  ring

/--
Paper I, Proposition 5.2 (`prop:closed`), civic_alignment.tex:374: exact closed
form for the manipulability gradient.
-/
theorem manipulabilityGradient_closedForm
    (δH δL δm γH γL ηH ηL κ β : ℝ) :
    manipulabilityGradient δH δL δm γH γL ηH ηL κ β =
      2 * (ηL * marginalHarmBracket δL δm γL ηL 1 β -
        (1 - κ) * ηH * marginalHarmBracket δH δm γH ηH (1 - κ) β) := by
  have hlow := hasDerivAt_typeMSE δL δm γL ηL 1 β
  have hhigh := hasDerivAt_typeMSE δH δm γH ηH (1 - κ) β
  have hgap : HasDerivAt (typeMSEGap δH δL δm γH γL ηH ηL κ)
      (2 * (ηL * marginalHarmBracket δL δm γL ηL 1 β -
        (1 - κ) * ηH * marginalHarmBracket δH δm γH ηH (1 - κ) β)) β := by
    (convert! hlow.sub hhigh using 1; ring)
  simpa only [manipulabilityGradient] using hgap.deriv

/-- Paper I, equation `eq:bracket`: the baseline (`β = 0`) marginal-harm bracket. -/
def baselineMarginalHarm (δ δm γ η : ℝ) : ℝ :=
  (δ - γ) - η * (δ + δm - 2 * γ)

/-- At the baseline, the marginal-harm bracket is independent of the de-anchoring rate. -/
theorem marginalHarmBracket_zero (δ δm γ η r : ℝ) :
    marginalHarmBracket δ δm γ η r 0 = baselineMarginalHarm δ δm γ η := by
  simp only [marginalHarmBracket, affineEvidenceWeight, baselineMarginalHarm]
  ring

/--
Paper I, Proposition 5.3 (`prop:baseline`), civic_alignment.tex:395: the exact
baseline audit expression for the manipulability gradient.
-/
theorem manipulabilityGradient_baseline
    (δH δL δm γH γL ηH ηL κ : ℝ) :
    manipulabilityGradient δH δL δm γH γL ηH ηL κ 0 =
      2 * (ηL * baselineMarginalHarm δL δm γL ηL -
        (1 - κ) * ηH * baselineMarginalHarm δH δm γH ηH) := by
  rw [manipulabilityGradient_closedForm]
  rw [marginalHarmBracket_zero, marginalHarmBracket_zero]

/--
Paper I, Corollary 5.4 (`cor:mgsign`), civic_alignment.tex:403: marginal-harm
dominance gives the stated strictly positive lower bound on the baseline
manipulability gradient.
-/
theorem manipulabilityGradient_baseline_sign
    {δH δL δm γH γL ηH ηL κ : ℝ}
    (reliance : RelianceAssumption ηH ηL)
    (_dilution : DilutionAssumption δm δH δL ηH ηL)
    (hdominance :
      ηH * baselineMarginalHarm δH δm γH ηH ≤
        ηL * baselineMarginalHarm δL δm γL ηL)
    (hstrict : 0 < κ * baselineMarginalHarm δH δm γH ηH) :
    2 * κ * ηH * baselineMarginalHarm δH δm γH ηH ≤
        manipulabilityGradient δH δL δm γH γL ηH ηL κ 0 ∧
      0 < manipulabilityGradient δH δL δm γH γL ηH ηL κ 0 := by
  have hpositive :
      0 < ηH * (κ * baselineMarginalHarm δH δm γH ηH) :=
    mul_pos reliance.ηH_pos hstrict
  rw [manipulabilityGradient_baseline]
  constructor <;> nlinarith

/--
Paper I, Corollary 5.4 (`cor:mgsign`), civic_alignment.tex:403, “in particular”
clause: credulity ordering and bracket dominance imply a positive gradient.
-/
theorem manipulabilityGradient_baseline_pos_of_order
    {δH δL δm γH γL ηH ηL κ : ℝ}
    (reliance : RelianceAssumption ηH ηL) (extraction : ExtractionAssumption κ)
    (dilution : DilutionAssumption δm δH δL ηH ηL) (hcredulity : ηH ≤ ηL)
    (hharm : baselineMarginalHarm δH δm γH ηH ≤
      baselineMarginalHarm δL δm γL ηL)
    (hHpos : 0 < baselineMarginalHarm δH δm γH ηH) :
    0 < manipulabilityGradient δH δL δm γH γL ηH ηL κ 0 := by
  have hdominance :
      ηH * baselineMarginalHarm δH δm γH ηH ≤
        ηL * baselineMarginalHarm δL δm γL ηL :=
    (mul_le_mul_of_nonneg_right hcredulity hHpos.le).trans
      (mul_le_mul_of_nonneg_left hharm reliance.ηL_pos.le)
  exact (manipulabilityGradient_baseline_sign reliance dilution hdominance
    (mul_pos extraction.κ_pos hHpos)).2

/-! ## Civic-weighted objectives -/

/-- Paper I, Proposition 8.1 (`prop:incentive`): satisfaction plus civic capacity at weight `ρ`. -/
def civicWeightedObjective (U C : ℝ → ℝ) (ρ β : ℝ) : ℝ :=
  U β + ρ * C β

/--
Paper I, Proposition 8.1(i) (`prop:incentive`): the revealed-preference
comparative-statics argument for any strictly decreasing capacity function.
-/
theorem civicWeighted_maximizers_antitone {U C : ℝ → ℝ} {ρ1 ρ2 β1 β2 : ℝ}
    (hC : StrictAntiOn C (Icc (0 : ℝ) 1)) (hρ : ρ1 < ρ2)
    (hβ1 : β1 ∈ Icc (0 : ℝ) 1) (hβ2 : β2 ∈ Icc (0 : ℝ) 1)
    (hmax1 : IsMaxOn (civicWeightedObjective U C ρ1) (Icc (0 : ℝ) 1) β1)
    (hmax2 : IsMaxOn (civicWeightedObjective U C ρ2) (Icc (0 : ℝ) 1) β2) :
    β2 ≤ β1 := by
  have hfirst : U β2 + ρ1 * C β2 ≤ U β1 + ρ1 * C β1 := by
    simpa only [civicWeightedObjective, Set.mem_setOf_eq] using hmax1 hβ2
  have hsecond : U β1 + ρ2 * C β1 ≤ U β2 + ρ2 * C β2 := by
    simpa only [civicWeightedObjective, Set.mem_setOf_eq] using hmax2 hβ1
  have hcapacity : C β1 ≤ C β2 := by
    by_contra hnot
    have hdiff : 0 < C β1 - C β2 := sub_pos.mpr (lt_of_not_ge hnot)
    nlinarith [mul_pos (sub_pos.mpr hρ) hdiff]
  by_contra hnot
  have hβ : β1 < β2 := lt_of_not_ge hnot
  exact (not_lt_of_ge hcapacity) (hC hβ1 hβ2 hβ)

/-- Paper I, Proposition 8.1(ii): the supremum of the within-interval satisfaction derivative. -/
noncomputable def satisfactionSlopeSup (U : ℝ → ℝ) : ℝ :=
  sSup (derivWithin U (Icc (0 : ℝ) 1) '' Icc (0 : ℝ) 1)

/-- A `C¹` satisfaction objective's within-interval derivative is bounded by its supremum. -/
theorem derivWithin_le_satisfactionSlopeSup {U : ℝ → ℝ} {UPrimeZero β : ℝ}
    (satisfaction : SatisfactionAssumption U UPrimeZero)
    (hβ : β ∈ Icc (0 : ℝ) 1) :
    derivWithin U (Icc (0 : ℝ) 1) β ≤ satisfactionSlopeSup U := by
  apply le_csSup
  · exact isCompact_Icc.bddAbove_image
      (satisfaction.continuouslyDifferentiable.continuousOn_derivWithin
        uniqueDiffOn_Icc_zero_one le_rfl)
  · exact mem_image_of_mem _ hβ

/-- The harm bracket is non-decreasing away from its baseline along a nonnegative path. -/
theorem baselineMarginalHarm_le_marginalHarmBracket
    {δ δm γ η r β : ℝ} (hη : 0 ≤ η) (hr : 0 ≤ r)
    (hcoefficient : 0 ≤ δ + δm - 2 * γ) (hβ : 0 ≤ β) :
    baselineMarginalHarm δ δm γ η ≤ marginalHarmBracket δ δm γ η r β := by
  have hproduct : 0 ≤ η * r * β * (δ + δm - 2 * γ) :=
    mul_nonneg (mul_nonneg (mul_nonneg hη hr) hβ) hcoefficient
  calc
    baselineMarginalHarm δ δm γ η ≤
        baselineMarginalHarm δ δm γ η + η * r * β * (δ + δm - 2 * γ) :=
      le_add_of_nonneg_right hproduct
    _ = marginalHarmBracket δ δm γ η r β := by
      simp only [baselineMarginalHarm, marginalHarmBracket, affineEvidenceWeight]
      ring

/-- The low-type MSE grows at least at its positive baseline derivative rate. -/
theorem lowTypeMSE_growth_lower_bound
    {δ δm γ η β1 β2 : ℝ} (hη : 0 ≤ η)
    (hcoefficient : 0 ≤ δ + δm - 2 * γ)
    (hβ1 : β1 ∈ Icc (0 : ℝ) 1) (hβ2 : β2 ∈ Icc (0 : ℝ) 1)
    (hβ : β1 ≤ β2) :
    (2 * η * baselineMarginalHarm δ δm γ η) * (β2 - β1) ≤
      lowTypeMSE δ δm γ η β2 - lowTypeMSE δ δm γ η β1 := by
  apply (convex_Icc (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv
  · intro x _
    exact (hasDerivAt_typeMSE δ δm γ η 1 x).continuousAt.continuousWithinAt
  · intro x _
    exact (hasDerivAt_typeMSE δ δm γ η 1 x).differentiableAt.differentiableWithinAt
  · intro x hx
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := interior_subset hx
    have hbracket := baselineMarginalHarm_le_marginalHarmBracket hη zero_le_one
      hcoefficient hxIcc.1
    change 2 * η * baselineMarginalHarm δ δm γ η ≤
      deriv (typeMSE δ δm γ η 1) x
    rw [(hasDerivAt_typeMSE δ δm γ η 1 x).deriv]
    nlinarith
  · exact hβ1
  · exact hβ2
  · exact hβ

/--
Paper I, Proposition 8.1(ii) (`prop:incentive`): capacity falls by at least the
integrated baseline low-type harm rate.
-/
theorem collectiveCapacity_growth_upper_bound
    {πH πL δH δL δm γH γL ηH ηL κ σH2 σL2 m μH μL lambda nu β1 β2 : ℝ}
    (hδm : 0 ≤ δm) (hδH : 0 ≤ δH) (hδL : 0 ≤ δL)
    (hγH : 0 ≤ γH) (hγL : 0 ≤ γL)
    (hγHbound : γH ≤ √(δm * δH)) (hγLbound : γL ≤ √(δm * δL))
    (hσH2 : 0 ≤ σH2) (hσL2 : 0 ≤ σL2) (hlambda : 0 ≤ lambda) (hnu : 0 ≤ nu)
    (evidence : EvidenceAssumption δm δH δL) (straddle : StraddleAssumption m μH μL)
    (reliance : RelianceAssumption ηH ηL) (extraction : ExtractionAssumption κ)
    (dilution : DilutionAssumption δm δH δL ηH ηL)
    (shares : PopulationShares πH πL) (hβ1 : β1 ∈ Icc (0 : ℝ) 1)
    (hβ2 : β2 ∈ Icc (0 : ℝ) 1) (hβ : β1 < β2) :
    collectiveCapacity πH πL δH δL δm γH γL ηH ηL κ σH2 σL2 m μH μL
          lambda nu β2 -
        collectiveCapacity πH πL δH δL δm γH γL ηH ηL κ σH2 σL2 m μH μL
          lambda nu β1 ≤
      -(2 * πL * ηL * baselineMarginalHarm δL δm γL ηL) * (β2 - β1) := by
  have hcoefficient : 0 ≤ δL + δm - 2 * γL :=
    (mseQuadratic_coefficient_pos hδm hδL evidence.δm_lt_δL hγL hγLbound).le
  have hLow := lowTypeMSE_growth_lower_bound reliance.ηL_pos.le hcoefficient
    hβ1 hβ2 hβ.le
  have hLowWeighted := mul_le_mul_of_nonneg_left hLow shares.πL_pos.le
  have hMSE := mse_monotonicity hδm hδH hδL hγH hγL hγHbound hγLbound
    evidence reliance extraction dilution shares
  have hHigh := hMSE.2.1 hβ1 hβ2 hβ.le
  have hHighWeighted :
      0 ≤ πH * (highTypeMSE δH δm γH ηH κ β2 -
        highTypeMSE δH δm γH ηH κ β1) :=
    mul_nonneg shares.πH_pos.le (sub_nonneg.mpr hHigh)
  have hAccuracy :
      (2 * πL * ηL * baselineMarginalHarm δL δm γL ηL) * (β2 - β1) ≤
        populationAccuracyLoss πH πL δH δL δm γH γL ηH ηL κ β2 -
          populationAccuracyLoss πH πL δH δL δm γH γL ηH ηL κ β1 := by
    simp only [populationAccuracyLoss]
    nlinarith
  have hWithin :=
    (within_fragmentation_monotonicity hσH2 hσL2 reliance extraction shares).1
      hβ1 hβ2 hβ.le
  have hWithinWeighted :
      0 ≤ lambda *
        (withinTypeDispersion πH πL σH2 σL2 ηH ηL κ β2 -
          withinTypeDispersion πH πL σH2 σL2 ηH ηL κ β1) :=
    mul_nonneg hlambda (sub_nonneg.mpr hWithin)
  have hGap := (stratification_gap_widens straddle reliance extraction).2.2.2.2
    hβ1 hβ2 hβ
  have hGapWeighted :
      0 ≤ nu * (meanGap ηH ηL κ m μH μL β2 ^ 2 -
        meanGap ηH ηL κ m μH μL β1 ^ 2) :=
    mul_nonneg hnu (sub_nonneg.mpr hGap.le)
  simp only [collectiveCapacity]
  nlinarith

/--
Paper I, Proposition 8.1(ii) (`prop:incentive`): above the paper's exact
derivative-supremum threshold, the civic-weighted objective is strictly
decreasing on the policy interval.
-/
theorem civicWeightedObjective_strictly_decreases
    {πH πL δH δL δm γH γL ηH ηL κ σH2 σL2 m μH μL lambda nu ρ : ℝ}
    {U : ℝ → ℝ} {UPrimeZero : ℝ}
    (hδm : 0 ≤ δm) (hδH : 0 ≤ δH) (hδL : 0 ≤ δL)
    (hγH : 0 ≤ γH) (hγL : 0 ≤ γL)
    (hγHbound : γH ≤ √(δm * δH)) (hγLbound : γL ≤ √(δm * δL))
    (hσH2 : 0 ≤ σH2) (hσL2 : 0 ≤ σL2) (hlambda : 0 ≤ lambda) (hnu : 0 ≤ nu)
    (evidence : EvidenceAssumption δm δH δL) (straddle : StraddleAssumption m μH μL)
    (reliance : RelianceAssumption ηH ηL) (extraction : ExtractionAssumption κ)
    (dilution : DilutionAssumption δm δH δL ηH ηL)
    (shares : PopulationShares πH πL) (satisfaction : SatisfactionAssumption U UPrimeZero)
    (hLpos : 0 < baselineMarginalHarm δL δm γL ηL) (hρ : 0 ≤ ρ)
    (hthreshold : satisfactionSlopeSup U /
      (2 * πL * ηL * baselineMarginalHarm δL δm γL ηL) < ρ) :
    StrictAntiOn
      (civicWeightedObjective U
        (collectiveCapacity πH πL δH δL δm γH γL ηH ηL κ σH2 σL2 m μH μL
          lambda nu) ρ) (Icc (0 : ℝ) 1) := by
  have hdenominator :
      0 < 2 * πL * ηL * baselineMarginalHarm δL δm γL ηL := by
    exact mul_pos (mul_pos (mul_pos (by norm_num) shares.πL_pos) reliance.ηL_pos) hLpos
  have hrate : satisfactionSlopeSup U <
      ρ * (2 * πL * ηL * baselineMarginalHarm δL δm γL ηL) := by
    have := (div_lt_iff₀ hdenominator).mp hthreshold
    nlinarith
  intro β1 hβ1 β2 hβ2 hβ
  have hUgrowth : U β2 - U β1 ≤ satisfactionSlopeSup U * (β2 - β1) := by
    apply (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
    · exact satisfaction.continuouslyDifferentiable.continuousOn
    · exact satisfaction.continuouslyDifferentiable.differentiableOn_one.mono interior_subset
    · intro x hx
      rw [← derivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx)]
      exact derivWithin_le_satisfactionSlopeSup satisfaction (interior_subset hx)
    · exact hβ1
    · exact hβ2
    · exact hβ.le
  have hCapacity := collectiveCapacity_growth_upper_bound hδm hδH hδL hγH hγL
    hγHbound hγLbound hσH2 hσL2 hlambda hnu evidence straddle reliance extraction
    dilution shares hβ1 hβ2 hβ
  have hWeightedCapacity := mul_le_mul_of_nonneg_left hCapacity hρ
  have hnegative :
      (satisfactionSlopeSup U -
        ρ * (2 * πL * ηL * baselineMarginalHarm δL δm γL ηL)) * (β2 - β1) < 0 :=
    mul_neg_of_neg_of_pos (sub_neg.mpr hrate) (sub_pos.mpr hβ)
  simp only [civicWeightedObjective]
  nlinarith

/--
Paper I, Proposition 8.1(ii) (`prop:incentive`): every maximizer above the
full-correction threshold is the safe corner `β = 0`.
-/
theorem civicWeightedObjective_maximizer_eq_zero
    {U C : ℝ → ℝ} {ρ βstar : ℝ}
    (hanti : StrictAntiOn (civicWeightedObjective U C ρ) (Icc (0 : ℝ) 1))
    (hβstar : βstar ∈ Icc (0 : ℝ) 1)
    (hmax : IsMaxOn (civicWeightedObjective U C ρ) (Icc (0 : ℝ) 1) βstar) :
    βstar = 0 := by
  apply le_antisymm
  · by_contra hnot
    have hpositive : 0 < βstar := lt_of_not_ge hnot
    have hstrict := hanti (show (0 : ℝ) ∈ Icc 0 1 by norm_num) hβstar hpositive
    have hmaxAtZero : civicWeightedObjective U C ρ 0 ≤
        civicWeightedObjective U C ρ βstar := hmax (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    linarith
  · exact hβstar.1

/--
Paper I, Proposition 8.1 (`prop:incentive`), civic_alignment.tex:518: increasing
the civic weight moves every maximizer weakly toward zero; when the low-type
baseline harm bracket is positive, every weight above the stated derivative
supremum threshold makes zero the unique maximizer.
-/
theorem civicWeighted_objectives_restore_safe_corner
    {πH πL δH δL δm γH γL ηH ηL κ σH2 σL2 m μH μL lambda nu : ℝ}
    {U : ℝ → ℝ} {UPrimeZero : ℝ}
    (hδm : 0 ≤ δm) (hδH : 0 ≤ δH) (hδL : 0 ≤ δL)
    (hγH : 0 ≤ γH) (hγL : 0 ≤ γL)
    (hγHbound : γH ≤ √(δm * δH)) (hγLbound : γL ≤ √(δm * δL))
    (hσH2 : 0 ≤ σH2) (hσL2 : 0 ≤ σL2) (hlambda : 0 ≤ lambda) (hnu : 0 ≤ nu)
    (evidence : EvidenceAssumption δm δH δL) (straddle : StraddleAssumption m μH μL)
    (reliance : RelianceAssumption ηH ηL) (extraction : ExtractionAssumption κ)
    (dilution : DilutionAssumption δm δH δL ηH ηL)
    (shares : PopulationShares πH πL) (satisfaction : SatisfactionAssumption U UPrimeZero) :
    let C := collectiveCapacity πH πL δH δL δm γH γL ηH ηL κ σH2 σL2 m μH μL
      lambda nu
    (∀ ⦃ρ1 ρ2 β1 β2 : ℝ⦄, 0 ≤ ρ1 → 0 ≤ ρ2 → ρ1 < ρ2 →
      β1 ∈ Icc (0 : ℝ) 1 → β2 ∈ Icc (0 : ℝ) 1 →
      IsMaxOn (civicWeightedObjective U C ρ1) (Icc (0 : ℝ) 1) β1 →
      IsMaxOn (civicWeightedObjective U C ρ2) (Icc (0 : ℝ) 1) β2 → β2 ≤ β1) ∧
    (0 < baselineMarginalHarm δL δm γL ηL →
      ∀ ⦃ρ : ℝ⦄, 0 ≤ ρ →
        satisfactionSlopeSup U /
            (2 * πL * ηL * baselineMarginalHarm δL δm γL ηL) < ρ →
        StrictAntiOn (civicWeightedObjective U C ρ) (Icc (0 : ℝ) 1) ∧
          ∀ ⦃βstar : ℝ⦄, βstar ∈ Icc (0 : ℝ) 1 →
            IsMaxOn (civicWeightedObjective U C ρ) (Icc (0 : ℝ) 1) βstar →
            βstar = 0) := by
  dsimp only
  constructor
  · intro ρ1 ρ2 β1 β2 _ _ hρ hβ1 hβ2 hmax1 hmax2
    apply civicWeighted_maximizers_antitone
    · exact capacity_strictly_decreases hδm hδH hδL hγH hγL hγHbound hγLbound
        hσH2 hσL2 hlambda hnu evidence straddle reliance extraction dilution shares
    · exact hρ
    · exact hβ1
    · exact hβ2
    · exact hmax1
    · exact hmax2
  · intro hLpos ρ hρ hthreshold
    have hanti := civicWeightedObjective_strictly_decreases hδm hδH hδL hγH hγL
      hγHbound hγLbound hσH2 hσL2 hlambda hnu evidence straddle reliance extraction
      dilution shares satisfaction hLpos hρ hthreshold
    refine ⟨hanti, ?_⟩
    intro βstar hβstar hmax
    exact civicWeightedObjective_maximizer_eq_zero hanti hβstar hmax

#print axioms hasDerivAt_typeMSE
#print axioms manipulabilityGradient_closedForm
#print axioms marginalHarmBracket_zero
#print axioms manipulabilityGradient_baseline
#print axioms manipulabilityGradient_baseline_sign
#print axioms manipulabilityGradient_baseline_pos_of_order
#print axioms civicWeighted_maximizers_antitone
#print axioms derivWithin_le_satisfactionSlopeSup
#print axioms baselineMarginalHarm_le_marginalHarmBracket
#print axioms lowTypeMSE_growth_lower_bound
#print axioms collectiveCapacity_growth_upper_bound
#print axioms civicWeightedObjective_strictly_decreases
#print axioms civicWeightedObjective_maximizer_eq_zero
#print axioms civicWeighted_objectives_restore_safe_corner

end CivicAlignment.PaperI
