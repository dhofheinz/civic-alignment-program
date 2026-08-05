/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperI.Capacity
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Paper I: personalized-deference optimizer ordering

This file isolates the comparative-statics statement in `rem:personal` from
the stronger interpretation about distributional capacity.  Derivative order
and strict concavity order the chosen deference levels.  No theorem here says
that every previously defined population-capacity term is amplified; that
would require a separate personalized capacity functional.
-/

namespace CivicAlignment.PaperI

open Set

/-- Minimal first-order comparative statics.  A strictly decreasing low-type
derivative, derivative dominance at the high-type choice, and the two
one-sided optimum signs force the low-type choice weakly to the right. -/
theorem chosenDeference_order_of_firstOrderSigns
    {dHigh dLow : ℝ → ℝ} {βHigh βLow : ℝ}
    (hLowStrictAnti : StrictAnti dLow)
    (hDerivativeOrder : dHigh βHigh ≤ dLow βHigh)
    (hHighNonnegative : 0 ≤ dHigh βHigh)
    (hLowNonpositive : dLow βLow ≤ 0) :
    βHigh ≤ βLow := by
  by_contra horder
  have hLowBeforeHigh : βLow < βHigh := lt_of_not_ge horder
  have hstrict : dLow βHigh < dLow βLow :=
    hLowStrictAnti hLowBeforeHigh
  linarith

/-- Interior strictly concave maximizers are ordered by pointwise derivative
order.  Only low-type strict concavity is needed for the ordering; high-type
strict concavity may be imposed separately for uniqueness. -/
theorem personalizedInteriorMaximizer_order
    {utilityHigh utilityLow : ℝ → ℝ} {βHigh βLow : ℝ}
    (hLowStrictConcave : StrictConcaveOn ℝ univ utilityLow)
    (hHighDifferentiable : Differentiable ℝ utilityHigh)
    (hLowDifferentiable : Differentiable ℝ utilityLow)
    (hDerivativeOrder :
      ∀ β, deriv utilityHigh β ≤ deriv utilityLow β)
    (hHighMax : IsLocalMax utilityHigh βHigh)
    (hLowMax : IsLocalMax utilityLow βLow) :
    βHigh ≤ βLow := by
  have hLowStrictAntiOn : StrictAntiOn (deriv utilityLow) univ :=
    hLowStrictConcave.strictAntiOn_deriv
      (fun β _hβ ↦ hLowDifferentiable β)
  have hLowStrictAnti : StrictAnti (deriv utilityLow) := by
    intro x y hxy
    exact hLowStrictAntiOn (mem_univ x) (mem_univ y) hxy
  have hHighZero : deriv utilityHigh βHigh = 0 :=
    hHighMax.hasDerivAt_eq_zero
      (hHighDifferentiable βHigh).hasDerivAt
  have hLowZero : deriv utilityLow βLow = 0 :=
    hLowMax.hasDerivAt_eq_zero
      (hLowDifferentiable βLow).hasDerivAt
  apply chosenDeference_order_of_firstOrderSigns
    hLowStrictAnti (hDerivativeOrder βHigh)
  · rw [hHighZero]
  · rw [hLowZero]

/-- The ordered choices have a nonnegative chosen-deference gap. -/
theorem chosenDeferenceGap_nonnegative
    {βHigh βLow : ℝ} (horder : βHigh ≤ βLow) :
    0 ≤ βLow - βHigh :=
  sub_nonneg.mpr horder

/-! ## Personalized capacity components -/

/-- Population accuracy loss with separate high- and low-type policy inputs. -/
def personalizedAccuracyLoss
    (πH πL δH δL δm γH γL ηH ηL κ βHigh βLow : ℝ) : ℝ :=
  πH * highTypeMSE δH δm γH ηH κ βHigh +
    πL * lowTypeMSE δL δm γL ηL βLow

/-- Within-type dispersion with separate high- and low-type policy inputs. -/
def personalizedWithinTypeDispersion
    (πH πL σH2 σL2 ηH ηL κ βHigh βLow : ℝ) : ℝ :=
  (πH * σH2) * residualVarianceFactor ηH (1 - κ) βHigh +
    (πL * σL2) * residualVarianceFactor ηL 1 βLow

/-- Between-type updated-mean gap with separate policy inputs. -/
def personalizedMeanGap
    (ηH ηL κ m μH μL βHigh βLow : ℝ) : ℝ :=
  beliefAtWeight (affineEvidenceWeight ηH (1 - κ) βHigh) m μH -
    beliefAtWeight (affineEvidenceWeight ηL 1 βLow) m μL

/-- Personalized collective capacity using the three separately parameterized
loss components. -/
def personalizedCollectiveCapacity
    (πH πL δH δL δm γH γL ηH ηL κ σH2 σL2 m μH μL
      lambda nu βHigh βLow : ℝ) : ℝ :=
  -personalizedAccuracyLoss πH πL δH δL δm γH γL ηH ηL κ
      βHigh βLow -
    lambda * personalizedWithinTypeDispersion πH πL σH2 σL2 ηH ηL κ
      βHigh βLow -
    nu * personalizedMeanGap ηH ηL κ m μH μL βHigh βLow ^ 2

/-- Exact change in the mean gap when only the low-type policy input moves. -/
theorem personalizedMeanGap_sub_global
    (ηH ηL κ m μH μL βHigh βLow : ℝ) :
    personalizedMeanGap ηH ηL κ m μH μL βHigh βLow -
      meanGap ηH ηL κ m μH μL βHigh =
        ηL * (βLow - βHigh) * (m - μL) := by
  simp only [personalizedMeanGap, meanGap, beliefAtWeight,
    affineEvidenceWeight]
  ring

/-- Under the paper's maintained assumptions, a weakly larger personalized
low-type choice weakly worsens each of the three capacity-loss components
relative to applying the high-type choice globally, and hence weakly lowers
personalized collective capacity. -/
theorem personalization_amplifies_capacityLossComponents
    {πH πL δH δL δm γH γL ηH ηL κ σH2 σL2 m μH μL
      lambda nu βHigh βLow : ℝ}
    (hδm : 0 ≤ δm) (hδH : 0 ≤ δH) (hδL : 0 ≤ δL)
    (hγH : 0 ≤ γH) (hγL : 0 ≤ γL)
    (hγHbound : γH ≤ √(δm * δH))
    (hγLbound : γL ≤ √(δm * δL))
    (hσL2 : 0 ≤ σL2) (hlambda : 0 ≤ lambda) (hnu : 0 ≤ nu)
    (evidence : EvidenceAssumption δm δH δL)
    (straddle : StraddleAssumption m μH μL)
    (reliance : RelianceAssumption ηH ηL)
    (extraction : ExtractionAssumption κ)
    (dilution : DilutionAssumption δm δH δL ηH ηL)
    (shares : PopulationShares πH πL)
    (hβHigh : βHigh ∈ Icc (0 : ℝ) 1)
    (hβLow : βLow ∈ Icc (0 : ℝ) 1)
    (horder : βHigh ≤ βLow) :
    populationAccuracyLoss πH πL δH δL δm γH γL ηH ηL κ βHigh ≤
        personalizedAccuracyLoss πH πL δH δL δm γH γL ηH ηL κ
          βHigh βLow ∧
      withinTypeDispersion πH πL σH2 σL2 ηH ηL κ βHigh ≤
        personalizedWithinTypeDispersion πH πL σH2 σL2 ηH ηL κ
          βHigh βLow ∧
      meanGap ηH ηL κ m μH μL βHigh ^ 2 ≤
        personalizedMeanGap ηH ηL κ m μH μL βHigh βLow ^ 2 ∧
      personalizedCollectiveCapacity πH πL δH δL δm γH γL ηH ηL κ
          σH2 σL2 m μH μL lambda nu βHigh βLow ≤
        collectiveCapacity πH πL δH δL δm γH γL ηH ηL κ
          σH2 σL2 m μH μL lambda nu βHigh := by
  have hLowMSE :=
    (mse_monotonicity hδm hδH hδL hγH hγL hγHbound hγLbound
      evidence reliance extraction dilution shares).1.monotoneOn
      hβHigh hβLow horder
  have hAccuracy :
      populationAccuracyLoss πH πL δH δL δm γH γL ηH ηL κ βHigh ≤
        personalizedAccuracyLoss πH πL δH δL δm γH γL ηH ηL κ
          βHigh βLow := by
    have hweighted := mul_le_mul_of_nonneg_left hLowMSE shares.πL_pos.le
    simp only [populationAccuracyLoss, personalizedAccuracyLoss]
    linarith
  have hLowVariance := residualVarianceFactor_monotoneOn
    reliance.ηL_pos reliance.ηL_le_one (show (0 : ℝ) ≤ 1 by norm_num)
    hβHigh hβLow horder
  have hWithin :
      withinTypeDispersion πH πL σH2 σL2 ηH ηL κ βHigh ≤
        personalizedWithinTypeDispersion πH πL σH2 σL2 ηH ηL κ
          βHigh βLow := by
    have hweight : 0 ≤ πL * σL2 :=
      mul_nonneg shares.πL_pos.le hσL2
    have hweighted := mul_le_mul_of_nonneg_left hLowVariance hweight
    simp only [withinTypeDispersion, personalizedWithinTypeDispersion]
    linarith
  have hgapDifference := personalizedMeanGap_sub_global
    ηH ηL κ m μH μL βHigh βLow
  have hGap :
      meanGap ηH ηL κ m μH μL βHigh ^ 2 ≤
        personalizedMeanGap ηH ηL κ m μH μL βHigh βLow ^ 2 := by
    have horientation :=
      (stratification_gap_widens straddle reliance extraction).2.2.1
    rcases horientation with horientation | horientation
    · have hglobal : 0 ≤ meanGap ηH ηL κ m μH μL βHigh :=
        horientation.2.1 βHigh hβHigh
      have hdelta : 0 ≤ ηL * (βLow - βHigh) * (m - μL) := by
        exact mul_nonneg
          (mul_nonneg reliance.ηL_pos.le (sub_nonneg.mpr horder))
          (sub_nonneg.mpr horientation.1.1.le)
      have hcomparison :
          meanGap ηH ηL κ m μH μL βHigh ≤
            personalizedMeanGap ηH ηL κ m μH μL βHigh βLow := by
        linarith
      have hpersonalized :
          0 ≤ personalizedMeanGap ηH ηL κ m μH μL βHigh βLow :=
        hglobal.trans hcomparison
      exact (sq_le_sq₀ hglobal hpersonalized).2 hcomparison
    · have hglobal : meanGap ηH ηL κ m μH μL βHigh ≤ 0 :=
        horientation.2.1 βHigh hβHigh
      have hdelta : ηL * (βLow - βHigh) * (m - μL) ≤ 0 := by
        have hm : m - μL < 0 := sub_neg.mpr horientation.1.2
        exact mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg reliance.ηL_pos.le (sub_nonneg.mpr horder)) hm.le
      have hcomparison :
          personalizedMeanGap ηH ηL κ m μH μL βHigh βLow ≤
            meanGap ηH ηL κ m μH μL βHigh := by
        linarith
      have hpersonalized :
          personalizedMeanGap ηH ηL κ m μH μL βHigh βLow ≤ 0 :=
        hcomparison.trans hglobal
      have hsquare :
          (-meanGap ηH ηL κ m μH μL βHigh) ^ 2 ≤
            (-personalizedMeanGap ηH ηL κ m μH μL βHigh βLow) ^ 2 :=
        (sq_le_sq₀ (neg_nonneg.mpr hglobal)
          (neg_nonneg.mpr hpersonalized)).2 (neg_le_neg hcomparison)
      nlinarith
  have hCapacity :
      personalizedCollectiveCapacity πH πL δH δL δm γH γL ηH ηL κ
          σH2 σL2 m μH μL lambda nu βHigh βLow ≤
        collectiveCapacity πH πL δH δL δm γH γL ηH ηL κ
          σH2 σL2 m μH μL lambda nu βHigh := by
    have hWithinWeighted := mul_le_mul_of_nonneg_left hWithin hlambda
    have hGapWeighted := mul_le_mul_of_nonneg_left hGap hnu
    simp only [personalizedCollectiveCapacity, collectiveCapacity]
    linarith
  exact ⟨hAccuracy, hWithin, hGap, hCapacity⟩

#print axioms chosenDeference_order_of_firstOrderSigns
#print axioms personalizedInteriorMaximizer_order
#print axioms chosenDeferenceGap_nonnegative
#print axioms personalizedMeanGap_sub_global
#print axioms personalization_amplifies_capacityLossComponents

end CivicAlignment.PaperI
