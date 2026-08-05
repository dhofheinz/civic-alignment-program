/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.ContinuousType

/-!
# Paper II: finite registered harm-incidence summaries

The manuscript proposes Lorenz/Gini summaries of the harm-incidence curve.
This file supplies the finite registered-population Gini definition with
explicit nonnegative normalized weights and the zero-mean convention.  It does
not construct a continuous-type Lorenz curve or prove empirical construct
validity for any chosen type partition.
-/

namespace CivicAlignment.PaperII

open scoped BigOperators

noncomputable section

/-- Nonnegative registered type weights normalized to unit mass. -/
structure FiniteHarmWeights (T : Type*) [Fintype T] where
  weight : T → ℝ
  nonnegative : ∀ τ, 0 ≤ weight τ
  normalized : ∑ τ, weight τ = 1

/-- Weighted mean marginal harm. -/
def weightedMeanHarm {T : Type*} [Fintype T]
    (weights : FiniteHarmWeights T) (harm : T → ℝ) : ℝ :=
  ∑ τ, weights.weight τ * harm τ

/-- Weighted pairwise absolute harm difference, the numerator of the Gini
functional before its factor-of-two mean normalization. -/
def pairwiseHarmDifference {T : Type*} [Fintype T]
    (weights : FiniteHarmWeights T) (harm : T → ℝ) : ℝ :=
  ∑ τ, ∑ υ,
    weights.weight τ * weights.weight υ * |harm τ - harm υ|

/-- Registered finite-population harm Gini.  When mean harm is zero the index
is defined to be zero, avoiding division by zero. -/
def finiteHarmGini {T : Type*} [Fintype T]
    (weights : FiniteHarmWeights T) (harm : T → ℝ) : ℝ :=
  if weightedMeanHarm weights harm = 0 then 0
  else pairwiseHarmDifference weights harm /
    (2 * weightedMeanHarm weights harm)

/-- Nonnegative harm has nonnegative weighted mean. -/
theorem weightedMeanHarm_nonnegative
    {T : Type*} [Fintype T] (weights : FiniteHarmWeights T)
    {harm : T → ℝ} (hharm : ∀ τ, 0 ≤ harm τ) :
    0 ≤ weightedMeanHarm weights harm := by
  exact Finset.sum_nonneg fun τ _hτ ↦
    mul_nonneg (weights.nonnegative τ) (hharm τ)

/-- Pairwise absolute dispersion is nonnegative. -/
theorem pairwiseHarmDifference_nonnegative
    {T : Type*} [Fintype T] (weights : FiniteHarmWeights T)
    (harm : T → ℝ) :
    0 ≤ pairwiseHarmDifference weights harm := by
  apply Finset.sum_nonneg
  intro τ _hτ
  apply Finset.sum_nonneg
  intro υ _hυ
  exact mul_nonneg
    (mul_nonneg (weights.nonnegative τ) (weights.nonnegative υ))
    (abs_nonneg _)

/-- Under nonnegative harm, the registered Gini is nonnegative, including its
zero-mean branch. -/
theorem finiteHarmGini_nonnegative
    {T : Type*} [Fintype T] (weights : FiniteHarmWeights T)
    {harm : T → ℝ} (hharm : ∀ τ, 0 ≤ harm τ) :
    0 ≤ finiteHarmGini weights harm := by
  by_cases hmean : weightedMeanHarm weights harm = 0
  · simp [finiteHarmGini, hmean]
  · rw [finiteHarmGini, if_neg hmean]
    exact div_nonneg (pairwiseHarmDifference_nonnegative weights harm)
      (mul_nonneg (by norm_num) (weightedMeanHarm_nonnegative weights hharm))

/-- A constant harm-incidence curve has Gini zero. -/
theorem finiteHarmGini_eq_zero_of_constant
    {T : Type*} [Fintype T] (weights : FiniteHarmWeights T)
    (constant : ℝ) :
    finiteHarmGini weights (fun _τ ↦ constant) = 0 := by
  classical
  simp [finiteHarmGini, pairwiseHarmDifference]

/-- With strictly positive registered weights, zero mean nonnegative harm means
every registered type has zero harm. -/
theorem weightedMeanHarm_eq_zero_iff
    {T : Type*} [Fintype T] (weights : FiniteHarmWeights T)
    (hweight : ∀ τ, 0 < weights.weight τ)
    {harm : T → ℝ} (hharm : ∀ τ, 0 ≤ harm τ) :
    weightedMeanHarm weights harm = 0 ↔ ∀ τ, harm τ = 0 := by
  constructor
  · intro hmean τ
    have hterm : weights.weight τ * harm τ = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _hi ↦ mul_nonneg (weights.nonnegative i) (hharm i))).mp
      · simpa only [weightedMeanHarm] using hmean
      · exact Finset.mem_univ τ
    exact (mul_eq_zero.mp hterm).resolve_left (hweight τ).ne'
  · intro hzero
    simp [weightedMeanHarm, hzero]

#print axioms weightedMeanHarm_nonnegative
#print axioms pairwiseHarmDifference_nonnegative
#print axioms finiteHarmGini_nonnegative
#print axioms finiteHarmGini_eq_zero_of_constant
#print axioms weightedMeanHarm_eq_zero_iff

end


end CivicAlignment.PaperII
