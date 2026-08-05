/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.Bistability

/-!
# Paper II: exact heterogeneous-stock aggregation

With heterogeneous evidence weights, the aggregate squared-deviation stock
does not generally contract by one fixed representative factor.  Its exact
factor is a stock-share-weighted mixture and therefore changes with the type
composition of the current stock.  A fixed representative factor is recovered
under homogeneous evidence weights or a fixed stock mixture.
-/

namespace CivicAlignment.PaperII

open scoped BigOperators

noncomputable section

/-- Total disagreement stock across a finite type family. -/
def finiteTypeStock {T : Type*} [Fintype T] (stock : T → ℝ) : ℝ :=
  ∑ τ, stock τ

/-- Squared-deviation contraction for one type's evidence weight. -/
def typeStockContraction {T : Type*} (evidenceWeight : T → ℝ) (τ : T) : ℝ :=
  (1 - evidenceWeight τ) ^ 2

/-- Exact post-exposure stock before grounding and new arrivals. -/
def heterogeneousContractedStock {T : Type*} [Fintype T]
    (evidenceWeight stock : T → ℝ) : ℝ :=
  ∑ τ, typeStockContraction evidenceWeight τ * stock τ

/-- The exact aggregate contraction at the current stock composition.  The
zero-stock convention is zero; under nonnegative component stocks it preserves
the exact factorization below. -/
def effectiveStockContraction {T : Type*} [Fintype T]
    (evidenceWeight stock : T → ℝ) : ℝ :=
  if finiteTypeStock stock = 0 then 0
  else heterogeneousContractedStock evidenceWeight stock /
    finiteTypeStock stock

/-- For nonzero total stock, the effective contraction is exactly the ratio
that factors the heterogeneous contracted stock. -/
theorem heterogeneousContractedStock_eq_effective_mul_of_ne_zero
    {T : Type*} [Fintype T] (evidenceWeight stock : T → ℝ)
    (htotal : finiteTypeStock stock ≠ 0) :
    heterogeneousContractedStock evidenceWeight stock =
      effectiveStockContraction evidenceWeight stock *
        finiteTypeStock stock := by
  rw [effectiveStockContraction, if_neg htotal]
  field_simp

/-- With nonnegative type stocks, the same exact factorization also holds at
zero total stock under the registered zero-stock convention. -/
theorem heterogeneousContractedStock_eq_effective_mul
    {T : Type*} [Fintype T] (evidenceWeight stock : T → ℝ)
    (hstock : ∀ τ, 0 ≤ stock τ) :
    heterogeneousContractedStock evidenceWeight stock =
      effectiveStockContraction evidenceWeight stock *
        finiteTypeStock stock := by
  by_cases htotal : finiteTypeStock stock = 0
  · have hcomponent : ∀ τ, stock τ = 0 := by
      intro τ
      apply (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _hi ↦ hstock i)).mp
      · simpa only [finiteTypeStock] using htotal
      · exact Finset.mem_univ τ
    simp [heterogeneousContractedStock, effectiveStockContraction,
      htotal, hcomponent]
  · exact heterogeneousContractedStock_eq_effective_mul_of_ne_zero
      evidenceWeight stock htotal

/-- The conditional-mean stock law with grounding and arrivals, now using the
exact state-dependent heterogeneous contraction. -/
def heterogeneousExpectedNextStock {T : Type*} [Fintype T]
    (groundingRate arrivals : ℝ) (evidenceWeight stock : T → ℝ) : ℝ :=
  (1 - groundingRate) *
    heterogeneousContractedStock evidenceWeight stock + arrivals

/-- Exact reduced form of the heterogeneous conditional-mean law. -/
theorem heterogeneousExpectedNextStock_eq_effective
    {T : Type*} [Fintype T] (groundingRate arrivals : ℝ)
    (evidenceWeight stock : T → ℝ) (hstock : ∀ τ, 0 ≤ stock τ) :
    heterogeneousExpectedNextStock groundingRate arrivals evidenceWeight stock =
      (1 - groundingRate) * effectiveStockContraction evidenceWeight stock *
        finiteTypeStock stock + arrivals := by
  rw [heterogeneousExpectedNextStock,
    heterogeneousContractedStock_eq_effective_mul evidenceWeight stock hstock]
  ring

/-- Homogeneous evidence weights recover the paper's representative squared
contraction exactly. -/
theorem heterogeneousContractedStock_eq_of_homogeneousWeight
    {T : Type*} [Fintype T] (evidenceWeight stock : T → ℝ) (w : ℝ)
    (hweight : ∀ τ, evidenceWeight τ = w) :
    heterogeneousContractedStock evidenceWeight stock =
      (1 - w) ^ 2 * finiteTypeStock stock := by
  classical
  simp only [heterogeneousContractedStock, typeStockContraction,
    finiteTypeStock, hweight]
  rw [Finset.mul_sum]

/-- Registered fixed type-stock shares. -/
structure FiniteStockMixture (T : Type*) [Fintype T] where
  share : T → ℝ
  nonnegative : ∀ τ, 0 ≤ share τ
  normalized : ∑ τ, share τ = 1

/-- The fixed-mixture contraction factor. -/
def fixedMixtureContraction {T : Type*} [Fintype T]
    (mixture : FiniteStockMixture T) (evidenceWeight : T → ℝ) : ℝ :=
  ∑ τ, mixture.share τ * typeStockContraction evidenceWeight τ

/-- A stock with fixed registered type shares has total mass equal to its
scalar stock level. -/
theorem finiteTypeStock_fixedMixture
    {T : Type*} [Fintype T] (mixture : FiniteStockMixture T) (stock : ℝ) :
    finiteTypeStock (fun τ ↦ mixture.share τ * stock) = stock := by
  classical
  rw [finiteTypeStock, ← Finset.sum_mul, mixture.normalized, one_mul]

/-- Under a fixed stock mixture, the exact heterogeneous contraction reduces
to one constant mixture factor times total stock. -/
theorem heterogeneousContractedStock_fixedMixture
    {T : Type*} [Fintype T] (mixture : FiniteStockMixture T)
    (evidenceWeight : T → ℝ) (stock : ℝ) :
    heterogeneousContractedStock evidenceWeight
        (fun τ ↦ mixture.share τ * stock) =
      fixedMixtureContraction mixture evidenceWeight * stock := by
  classical
  rw [heterogeneousContractedStock, fixedMixtureContraction,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro τ _hτ
  ring

/-- At every nonzero scalar stock level, the state-dependent effective factor
of a registered fixed mixture is exactly its constant mixture factor. -/
theorem effectiveStockContraction_fixedMixture_of_ne_zero
    {T : Type*} [Fintype T] (mixture : FiniteStockMixture T)
    (evidenceWeight : T → ℝ) {stock : ℝ} (hstock : stock ≠ 0) :
    effectiveStockContraction evidenceWeight
        (fun τ ↦ mixture.share τ * stock) =
      fixedMixtureContraction mixture evidenceWeight := by
  have htotal :
      finiteTypeStock (fun τ ↦ mixture.share τ * stock) ≠ 0 := by
    rw [finiteTypeStock_fixedMixture]
    exact hstock
  rw [effectiveStockContraction, if_neg htotal,
    heterogeneousContractedStock_fixedMixture,
    finiteTypeStock_fixedMixture]
  field_simp

/-- The selected fixed-mixture representative reduction gives the complete
conditional-mean stock law, including grounding and arrivals, exactly. -/
theorem heterogeneousExpectedNextStock_fixedMixture
    {T : Type*} [Fintype T] (mixture : FiniteStockMixture T)
    (groundingRate arrivals : ℝ) (evidenceWeight : T → ℝ) (stock : ℝ) :
    heterogeneousExpectedNextStock groundingRate arrivals evidenceWeight
        (fun τ ↦ mixture.share τ * stock) =
      (1 - groundingRate) *
          fixedMixtureContraction mixture evidenceWeight * stock + arrivals := by
  rw [heterogeneousExpectedNextStock,
    heterogeneousContractedStock_fixedMixture]
  ring

#print axioms heterogeneousContractedStock_eq_effective_mul
#print axioms heterogeneousExpectedNextStock_eq_effective
#print axioms heterogeneousContractedStock_eq_of_homogeneousWeight
#print axioms finiteTypeStock_fixedMixture
#print axioms heterogeneousContractedStock_fixedMixture
#print axioms effectiveStockContraction_fixedMixture_of_ne_zero
#print axioms heterogeneousExpectedNextStock_fixedMixture

end

end CivicAlignment.PaperII
