/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperI.Capacity

/-!
# Paper I: lifting event-level capacity to a finite claim corpus

Paper I's capacity theorem is event-by-event.  This file gives the exact
finite-corpus bridge used by an audit: nonnegative registered claim weights,
weak capacity loss on every claim, and strict loss on at least one
positive-weight claim imply strict loss of pooled capacity.  The corresponding
derivative identity makes explicit that a positive share of harmful claims is
not by itself enough when claims outside that share may have positive slopes.
-/

namespace CivicAlignment.PaperI

open scoped BigOperators
open Set

noncomputable section

/-- A finite audit corpus with nonnegative claim weights normalized to one. -/
structure FiniteCorpusWeights (J : Type*) [Fintype J] where
  weight : J → ℝ
  nonneg : ∀ j, 0 ≤ weight j
  normalized : ∑ j, weight j = 1

/-- Capacity pooled across the registered finite claim corpus. -/
def pooledCorpusCapacity {J : Type*} [Fintype J]
    (q : FiniteCorpusWeights J) (capacity : J → ℝ → ℝ) (β : ℝ) : ℝ :=
  ∑ j, q.weight j * capacity j β

/-- The weighted aggregate of event-level capacity slopes. -/
def pooledCorpusCapacitySlope {J : Type*} [Fintype J]
    (q : FiniteCorpusWeights J) (slope : J → ℝ) : ℝ :=
  ∑ j, q.weight j * slope j

/-- The contribution to the pooled slope from one registered claim subset. -/
def pooledCorpusCapacitySlopeOn {J : Type*} [Fintype J]
    (q : FiniteCorpusWeights J) (slope : J → ℝ) (A : Finset J) : ℝ :=
  ∑ j ∈ A, q.weight j * slope j

/-- Exact decomposition into a registered subset and its complement. -/
theorem pooledCorpusCapacitySlope_eq_subset_add_complement
    {J : Type*} [Fintype J] [DecidableEq J] (q : FiniteCorpusWeights J)
    (slope : J → ℝ) (A : Finset J) :
    pooledCorpusCapacitySlope q slope =
      pooledCorpusCapacitySlopeOn q slope A +
        pooledCorpusCapacitySlopeOn q slope (Finset.univ \ A) := by
  classical
  rw [pooledCorpusCapacitySlope, pooledCorpusCapacitySlopeOn,
    pooledCorpusCapacitySlopeOn]
  rw [add_comm]
  exact
    (Finset.sum_sdiff (f := fun j : J ↦ q.weight j * slope j)
      (Finset.subset_univ A)).symm

/-- A positive-weight harmful subset alone does not sign the pool: the exact
registered criterion is negativity of the subset contribution plus the
complement contribution. -/
theorem pooledCorpusCapacitySlope_neg_iff_subset_add_complement_neg
    {J : Type*} [Fintype J] [DecidableEq J] (q : FiniteCorpusWeights J)
    (slope : J → ℝ) (A : Finset J) :
    pooledCorpusCapacitySlope q slope < 0 ↔
      pooledCorpusCapacitySlopeOn q slope A +
        pooledCorpusCapacitySlopeOn q slope (Finset.univ \ A) < 0 := by
  rw [pooledCorpusCapacitySlope_eq_subset_add_complement]

/-- Differentiating a registered finite corpus is exactly differentiation
claim by claim followed by aggregation with the registered weights. -/
theorem hasDerivAt_pooledCorpusCapacity
    {J : Type*} [Fintype J] (q : FiniteCorpusWeights J)
    (capacity : J → ℝ → ℝ) (slope : J → ℝ) (β : ℝ)
    (hderiv : ∀ j, HasDerivAt (capacity j) (slope j) β) :
    HasDerivAt (pooledCorpusCapacity q capacity)
      (pooledCorpusCapacitySlope q slope) β := by
  classical
  change HasDerivAt (fun y ↦ ∑ j, q.weight j * capacity j y)
    (∑ j, q.weight j * slope j) β
  exact HasDerivAt.fun_sum (u := Finset.univ)
    (fun j _hj ↦ (hderiv j).const_mul (q.weight j))

/-- If every registered claim has weakly nonpositive capacity slope and one
positive-weight claim has strictly negative slope, the pooled slope is
strictly negative. -/
theorem pooledCorpusCapacitySlope_neg
    {J : Type*} [Fintype J] (q : FiniteCorpusWeights J)
    (slope : J → ℝ) (j₀ : J)
    (hall : ∀ j, slope j ≤ 0) (hweight : 0 < q.weight j₀)
    (hstrict : slope j₀ < 0) :
    pooledCorpusCapacitySlope q slope < 0 := by
  classical
  have hsum :
      (∑ j, q.weight j * slope j) < ∑ _j : J, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro j _hj
      exact mul_nonpos_of_nonneg_of_nonpos (q.nonneg j) (hall j)
    · exact ⟨j₀, Finset.mem_univ j₀,
        mul_neg_of_pos_of_neg hweight hstrict⟩
  simpa only [pooledCorpusCapacitySlope, Finset.sum_const_zero] using hsum

/-- Event-level monotonicity lifts exactly to the corpus: if every claim's
capacity is weakly decreasing on the registered policy domain and one
positive-weight claim is strictly decreasing there, pooled capacity is
strictly decreasing on that domain. -/
theorem pooledCorpusCapacity_strictAntiOn
    {J : Type*} [Fintype J] (q : FiniteCorpusWeights J)
    (capacity : J → ℝ → ℝ) (S : Set ℝ) (j₀ : J)
    (hall : ∀ j, AntitoneOn (capacity j) S)
    (hweight : 0 < q.weight j₀)
    (hstrict : StrictAntiOn (capacity j₀) S) :
    StrictAntiOn (pooledCorpusCapacity q capacity) S := by
  classical
  intro β₁ hβ₁ β₂ hβ₂ hβ
  simp only [pooledCorpusCapacity]
  apply Finset.sum_lt_sum
  · intro j _hj
    exact mul_le_mul_of_nonneg_left
      (hall j hβ₁ hβ₂ hβ.le) (q.nonneg j)
  · exact ⟨j₀, Finset.mem_univ j₀,
      mul_lt_mul_of_pos_left (hstrict hβ₁ hβ₂ hβ) hweight⟩

#print axioms pooledCorpusCapacitySlope_neg
#print axioms pooledCorpusCapacitySlope_eq_subset_add_complement
#print axioms pooledCorpusCapacitySlope_neg_iff_subset_add_complement_neg
#print axioms hasDerivAt_pooledCorpusCapacity
#print axioms pooledCorpusCapacity_strictAntiOn

end

end CivicAlignment.PaperI
