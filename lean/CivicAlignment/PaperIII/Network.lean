/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.Certificate
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Paper III: network stock bounds and the decentralized certificate

The import-free direction of `thm:network` is developed with the matrix
`L∞` operator norm.  This makes the Neumann-series argument explicit and keeps
the Perron converse in a separate imported-theorem layer.
-/

namespace CivicAlignment.PaperIII

open Filter Matrix Set Topology
open scoped BigOperators Norms.Operator NNReal ENNReal

variable {K : Type*} [Fintype K]

/-! ## Ordered matrix-vector algebra -/

/-- Entrywise nonnegativity for a real matrix. -/
def MatrixEntrywiseNonnegative (M : Matrix K K ℝ) : Prop :=
  ∀ i j, 0 ≤ M i j

/-- Entrywise comparison for two real matrices. -/
def MatrixEntrywiseLE (A M : Matrix K K ℝ) : Prop :=
  ∀ i j, A i j ≤ M i j

/-- A nonnegative matrix maps a nonnegative vector to a nonnegative vector. -/
theorem matrix_mulVec_nonnegative {M : Matrix K K ℝ} {x : K → ℝ}
    (hM : MatrixEntrywiseNonnegative M) (hx : 0 ≤ x) : 0 ≤ M *ᵥ x := by
  intro k
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hM k j) (hx j)

/-- Multiplication by a nonnegative matrix is monotone in the vector. -/
theorem matrix_mulVec_mono_right {M : Matrix K K ℝ} (hM : MatrixEntrywiseNonnegative M)
    {x y : K → ℝ} (hxy : x ≤ y) : M *ᵥ x ≤ M *ᵥ y := by
  intro k
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hxy j) (hM k j)

/-- On a nonnegative vector, matrix-vector multiplication is monotone in the matrix. -/
theorem matrix_mulVec_mono_left {A M : Matrix K K ℝ} (hAM : MatrixEntrywiseLE A M)
    {x : K → ℝ} (hx : 0 ≤ x) : A *ᵥ x ≤ M *ᵥ x := by
  intro k
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_right (hAM k j) (hx j)

/-- Every natural power of a nonnegative square matrix is nonnegative. -/
theorem matrix_pow_nonnegative [DecidableEq K] {M : Matrix K K ℝ}
    (hM : MatrixEntrywiseNonnegative M) :
    ∀ n : ℕ, MatrixEntrywiseNonnegative (M ^ n) := by
  intro n
  induction n with
  | zero =>
      intro i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
  | succ n ih =>
      rw [pow_succ]
      intro i k
      simp only [Matrix.mul_apply]
      exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (ih i j) (hM j k)

/-! ## The Neumann resolvent and the dominating affine path -/

variable [DecidableEq K]

/-- The network resolvent applied to the positive injection vector, written as
the convergent Neumann series used by the paper's proof. -/
noncomputable def networkResolvent (M : Matrix K K ℝ) (I : K → ℝ) : K → ℝ :=
  (∑' n : ℕ, M ^ n) *ᵥ I

/-- The time-homogeneous affine path that dominates every admissible policy path. -/
def networkUpperPath (M : Matrix K K ℝ) (I D₀ : K → ℝ) : ℕ → K → ℝ
  | 0 => D₀
  | n + 1 => M *ᵥ networkUpperPath M I D₀ n + I

/-- The dominating affine path has the usual matrix geometric-sum form. -/
theorem networkUpperPath_eq (M : Matrix K K ℝ) (I D₀ : K → ℝ) (n : ℕ) :
    networkUpperPath M I D₀ n =
      M ^ n *ᵥ D₀ + (∑ j ∈ Finset.range n, M ^ j) *ᵥ I := by
  induction n with
  | zero => simp [networkUpperPath]
  | succ n ih =>
      rw [networkUpperPath, ih, Matrix.mulVec_add, Matrix.mulVec_mulVec, pow_succ']
      rw [geom_sum_succ, Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.one_mulVec]
      abel

/-- A summable matrix geometric series is the ring inverse of `1 - M`, with
no one-step operator-norm restriction. -/
theorem geom_series_eq_ringInverse_of_summable (M : Matrix K K ℝ)
    (hsum : Summable (fun n : ℕ ↦ M ^ n)) :
    (∑' n : ℕ, M ^ n) = Ring.inverse (1 - M) := by
  let S : Matrix K K ℝ := ∑' n : ℕ, M ^ n
  have hleft : (1 - M) * S = 1 := hsum.one_sub_mul_tsum_pow
  have hright : S * (1 - M) = 1 := hsum.tsum_pow_mul_one_sub
  have hunit : IsUnit (1 - M) := (isUnit_iff_exists_inv).2 ⟨S, hleft⟩
  let u : (Matrix K K ℝ)ˣ := hunit.unit
  have huval : (u : Matrix K K ℝ) = 1 - M := hunit.unit_spec
  have hinverse : (1 - M) * Ring.inverse (1 - M) = 1 := by
    have hu : Ring.inverse (1 - M) = (↑u⁻¹ : Matrix K K ℝ) := by
      rw [← huval, Ring.inverse_unit]
    rw [hu, ← huval]
    exact u.val_inv
  change S = Ring.inverse (1 - M)
  calc
    S = S * 1 := (mul_one S).symm
    _ = S * ((1 - M) * Ring.inverse (1 - M)) := by rw [hinverse]
    _ = (S * (1 - M)) * Ring.inverse (1 - M) := (mul_assoc _ _ _).symm
    _ = Ring.inverse (1 - M) := by rw [hright, one_mul]

/-- The inverse-resolvent identity under the general summability hypothesis
implied by the paper's complex spectral-radius condition. -/
theorem networkResolvent_eq_ringInverse_mulVec_of_summable
    (M : Matrix K K ℝ) (I : K → ℝ)
    (hsum : Summable (fun n : ℕ ↦ M ^ n)) :
    networkResolvent M I = Ring.inverse (1 - M) *ᵥ I := by
  rw [networkResolvent]
  exact congrArg (fun Q : Matrix K K ℝ ↦ Q *ᵥ I)
    (geom_series_eq_ringInverse_of_summable M hsum)

/-- The Neumann resolvent is a fixed point whenever the matrix powers are
summable. -/
theorem networkResolvent_fixed_of_summable
    (M : Matrix K K ℝ) (I : K → ℝ)
    (hsum : Summable (fun n : ℕ ↦ M ^ n)) :
    M *ᵥ networkResolvent M I + I = networkResolvent M I := by
  have hgeom := hsum.one_sub_mul_tsum_pow
  ext k
  have hcoordinate := congrFun (congrArg (fun A : Matrix K K ℝ ↦ A *ᵥ I) hgeom) k
  rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec] at hcoordinate
  simp only [Matrix.one_mulVec] at hcoordinate
  simp only [Pi.add_apply, networkResolvent]
  simp only [Pi.sub_apply] at hcoordinate
  calc
    (M *ᵥ (∑' n : ℕ, M ^ n) *ᵥ I) k + I k =
        I k + (M *ᵥ (∑' n : ℕ, M ^ n) *ᵥ I) k := add_comm _ _
    _ = ((∑' n : ℕ, M ^ n) *ᵥ I) k :=
      ((sub_eq_iff_eq_add).mp hcoordinate).symm

/-- The affine upper path converges to the Neumann resolvent whenever the
matrix powers are summable. -/
theorem networkUpperPath_tendsto_of_summable
    (M : Matrix K K ℝ) (I D₀ : K → ℝ)
    (hsummable : Summable (fun n : ℕ ↦ M ^ n)) :
    Tendsto (networkUpperPath M I D₀) atTop (nhds (networkResolvent M I)) := by
  have hpow : Tendsto (fun n : ℕ ↦ M ^ n) atTop (nhds 0) :=
    hsummable.tendsto_atTop_zero
  have hpartial : Tendsto (fun n : ℕ ↦ ∑ j ∈ Finset.range n, M ^ j) atTop
      (nhds (∑' n : ℕ, M ^ n)) := hsummable.hasSum.tendsto_sum_nat
  have hcontinuous (x : K → ℝ) : Continuous (fun A : Matrix K K ℝ ↦ A *ᵥ x) := by
    fun_prop
  have htransient : Tendsto (fun n : ℕ ↦ M ^ n *ᵥ D₀) atTop (nhds 0) := by
    convert (hcontinuous D₀).continuousAt.tendsto.comp hpow using 1 <;>
      simp [Function.comp_def]
  have hforcing : Tendsto
      (fun n : ℕ ↦ (∑ j ∈ Finset.range n, M ^ j) *ᵥ I) atTop
      (nhds (networkResolvent M I)) := by
    convert (hcontinuous I).continuousAt.tendsto.comp hpartial using 1 <;>
      simp [Function.comp_def, networkResolvent]
  rw [show networkUpperPath M I D₀ = fun n ↦
      M ^ n *ᵥ D₀ + (∑ j ∈ Finset.range n, M ^ j) *ᵥ I by
    funext n
    exact networkUpperPath_eq M I D₀ n]
  simpa only [zero_add] using htransient.add hforcing

/-- The Neumann definition is the paper's inverse-resolvent formula. -/
theorem networkResolvent_eq_ringInverse_mulVec (M : Matrix K K ℝ) (I : K → ℝ)
    (hnorm : ‖M‖ < 1) :
    networkResolvent M I = Ring.inverse (1 - M) *ᵥ I := by
  rw [networkResolvent]
  exact congrArg (fun Q : Matrix K K ℝ ↦ Q *ᵥ I) (geom_series_eq_inverse M hnorm)

/-- The Neumann resolvent is a fixed point of the affine network law. -/
theorem networkResolvent_fixed (M : Matrix K K ℝ) (I : K → ℝ)
    (hnorm : ‖M‖ < 1) :
    M *ᵥ networkResolvent M I + I = networkResolvent M I := by
  have hgeom := mul_neg_geom_series M hnorm
  ext k
  have hcoordinate := congrFun (congrArg (fun A : Matrix K K ℝ ↦ A *ᵥ I) hgeom) k
  rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec] at hcoordinate
  simp only [Matrix.one_mulVec] at hcoordinate
  simp only [Pi.add_apply, networkResolvent]
  simp only [Pi.sub_apply] at hcoordinate
  calc
    (M *ᵥ (∑' n : ℕ, M ^ n) *ᵥ I) k + I k =
        I k + (M *ᵥ (∑' n : ℕ, M ^ n) *ᵥ I) k := add_comm _ _
    _ = ((∑' n : ℕ, M ^ n) *ᵥ I) k :=
      ((sub_eq_iff_eq_add).mp hcoordinate).symm

/-- Under a strict operator-norm bound, the dominating network path converges
to the Neumann resolvent. -/
theorem networkUpperPath_tendsto (M : Matrix K K ℝ) (I D₀ : K → ℝ)
    (hnorm : ‖M‖ < 1) :
    Tendsto (networkUpperPath M I D₀) atTop (nhds (networkResolvent M I)) := by
  have hsummable : Summable (fun n : ℕ ↦ M ^ n) :=
    summable_geometric_of_norm_lt_one hnorm
  have hpow : Tendsto (fun n : ℕ ↦ M ^ n) atTop (nhds 0) :=
    hsummable.tendsto_atTop_zero
  have hpartial : Tendsto (fun n : ℕ ↦ ∑ j ∈ Finset.range n, M ^ j) atTop
      (nhds (∑' n : ℕ, M ^ n)) := hsummable.hasSum.tendsto_sum_nat
  have hcontinuous (x : K → ℝ) : Continuous (fun A : Matrix K K ℝ ↦ A *ᵥ x) := by
    fun_prop
  have htransient : Tendsto (fun n : ℕ ↦ M ^ n *ᵥ D₀) atTop (nhds 0) := by
    convert (hcontinuous D₀).continuousAt.tendsto.comp hpow using 1 <;>
      simp [Function.comp_def]
  have hforcing : Tendsto
      (fun n : ℕ ↦ (∑ j ∈ Finset.range n, M ^ j) *ᵥ I) atTop
      (nhds (networkResolvent M I)) := by
    convert (hcontinuous I).continuousAt.tendsto.comp hpartial using 1 <;>
      simp [Function.comp_def, networkResolvent]
  rw [show networkUpperPath M I D₀ = fun n ↦
      M ^ n *ᵥ D₀ + (∑ j ∈ Finset.range n, M ^ j) *ᵥ I by
    funext n
    exact networkUpperPath_eq M I D₀ n]
  simpa only [zero_add] using htransient.add hforcing

omit [DecidableEq K] in
/-- A nonnegative worst-case matrix and injection produce a nonnegative
dominating affine path from a nonnegative initial stock. -/
theorem networkUpperPath_nonnegative {M : Matrix K K ℝ} {I D₀ : K → ℝ}
    (hM : MatrixEntrywiseNonnegative M) (hI : 0 ≤ I) (hD₀ : 0 ≤ D₀) :
    ∀ n, 0 ≤ networkUpperPath M I D₀ n := by
  intro n
  induction n with
  | zero => exact hD₀
  | succ n ih =>
      rw [networkUpperPath]
      exact add_nonneg (matrix_mulVec_nonnegative hM ih) hI

/-- With nonnegative data, a summable Neumann series has a strictly positive
resolvent on every coordinate. -/
theorem networkResolvent_positive_of_summable
    {M : Matrix K K ℝ} {I : K → ℝ}
    (hM : MatrixEntrywiseNonnegative M) (hI : ∀ k, 0 < I k)
    (hsum : Summable (fun n : ℕ ↦ M ^ n)) :
    ∀ k, 0 < networkResolvent M I k := by
  have hlimit := networkUpperPath_tendsto_of_summable M I 0 hsum
  have hpath_nonnegative : ∀ n, 0 ≤ networkUpperPath M I 0 n :=
    networkUpperPath_nonnegative hM (fun k ↦ (hI k).le) (by simp)
  have hresolvent_nonnegative : 0 ≤ networkResolvent M I := by
    intro k
    exact ge_of_tendsto (tendsto_pi_nhds.mp hlimit k)
      (Eventually.of_forall fun n ↦ hpath_nonnegative n k)
  have hfixed := networkResolvent_fixed_of_summable M I hsum
  have hpropagated : 0 ≤ M *ᵥ networkResolvent M I :=
    matrix_mulVec_nonnegative hM hresolvent_nonnegative
  intro k
  have hk := congrFun hfixed k
  simp only [Pi.add_apply] at hk
  calc
    0 < (M *ᵥ networkResolvent M I) k + I k :=
      add_pos_of_nonneg_of_pos (hpropagated k) (hI k)
    _ = networkResolvent M I k := hk

/-- With nonnegative data, every component of the Neumann resolvent is positive. -/
theorem networkResolvent_positive {M : Matrix K K ℝ} {I : K → ℝ}
    (hM : MatrixEntrywiseNonnegative M) (hI : ∀ k, 0 < I k) (hnorm : ‖M‖ < 1) :
    ∀ k, 0 < networkResolvent M I k := by
  have hlimit := networkUpperPath_tendsto M I 0 hnorm
  have hpath_nonnegative : ∀ n, 0 ≤ networkUpperPath M I 0 n :=
    networkUpperPath_nonnegative hM (fun k ↦ (hI k).le) (by simp)
  have hresolvent_nonnegative : 0 ≤ networkResolvent M I := by
    intro k
    exact ge_of_tendsto (tendsto_pi_nhds.mp hlimit k)
      (Eventually.of_forall fun n ↦ hpath_nonnegative n k)
  have hfixed := networkResolvent_fixed M I hnorm
  have hpropagated : 0 ≤ M *ᵥ networkResolvent M I :=
    matrix_mulVec_nonnegative hM hresolvent_nonnegative
  intro k
  have hk := congrFun hfixed k
  simp only [Pi.add_apply] at hk
  calc
    0 < (M *ᵥ networkResolvent M I) k + I k :=
      add_pos_of_nonneg_of_pos (hpropagated k) (hI k)
    _ = networkResolvent M I k := hk

/-! ## Arbitrary policy paths dominated by the worst-case matrix -/

/-- A time-varying matrix affine recursion. -/
def IsNetworkStockTrajectory (A : ℕ → Matrix K K ℝ) (I : K → ℝ)
    (D : ℕ → K → ℝ) : Prop :=
  ∀ t, D (t + 1) = A t *ᵥ D t + I

omit [DecidableEq K] in
/-- Nonnegative data and transition matrices preserve nonnegative stocks. -/
theorem networkStockTrajectory_nonnegative {A : ℕ → Matrix K K ℝ} {I : K → ℝ}
    {D : ℕ → K → ℝ} (hA : ∀ t, MatrixEntrywiseNonnegative (A t)) (hI : 0 ≤ I)
    (hstock : IsNetworkStockTrajectory A I D) (hD₀ : 0 ≤ D 0) :
    ∀ t, 0 ≤ D t := by
  intro t
  induction t with
  | zero => exact hD₀
  | succ t ih =>
      rw [hstock t]
      exact add_nonneg (matrix_mulVec_nonnegative (hA t) ih) hI

omit [DecidableEq K] in
/-- Any time-varying nonnegative transition bounded by `M` is dominated by the
homogeneous affine path with transition `M`. -/
theorem networkStockTrajectory_le_upper {A : ℕ → Matrix K K ℝ} {M : Matrix K K ℝ}
    {I : K → ℝ} {D : ℕ → K → ℝ}
    (hA : ∀ t, MatrixEntrywiseNonnegative (A t))
    (hAM : ∀ t, MatrixEntrywiseLE (A t) M)
    (hM : MatrixEntrywiseNonnegative M) (hI : 0 ≤ I)
    (hstock : IsNetworkStockTrajectory A I D) (hD₀ : 0 ≤ D 0) :
    ∀ t, D t ≤ networkUpperPath M I (D 0) t := by
  have hDnonnegative := networkStockTrajectory_nonnegative hA hI hstock hD₀
  intro t
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
      rw [hstock t, networkUpperPath]
      have hleft : A t *ᵥ D t ≤ M *ᵥ D t :=
        matrix_mulVec_mono_left (hAM t) (hDnonnegative t)
      have hright : M *ᵥ D t ≤ M *ᵥ networkUpperPath M I (D 0) t :=
        matrix_mulVec_mono_right hM ih
      exact add_le_add (hleft.trans hright) le_rfl

/-- Policy-free componentwise limsup bound under the general summability
hypothesis supplied by the paper's spectral-radius premise. -/
theorem network_policyFree_bound_of_summable
    {A : ℕ → Matrix K K ℝ} {M : Matrix K K ℝ}
    {I : K → ℝ} {D : ℕ → K → ℝ}
    (hA : ∀ t, MatrixEntrywiseNonnegative (A t))
    (hAM : ∀ t, MatrixEntrywiseLE (A t) M)
    (hM : MatrixEntrywiseNonnegative M) (hI : ∀ k, 0 < I k)
    (hsum : Summable (fun n : ℕ ↦ M ^ n))
    (hstock : IsNetworkStockTrajectory A I D) (hD₀ : 0 ≤ D 0) :
    ∀ k, limsup (fun t ↦ D t k) atTop ≤ networkResolvent M I k := by
  have hI_nonnegative : 0 ≤ I := fun k ↦ (hI k).le
  have hcomparison := networkStockTrajectory_le_upper hA hAM hM hI_nonnegative hstock hD₀
  have hDnonnegative := networkStockTrajectory_nonnegative hA hI_nonnegative hstock hD₀
  have hlimit := networkUpperPath_tendsto_of_summable M I (D 0) hsum
  intro k
  have hlimit_k : Tendsto (fun t ↦ networkUpperPath M I (D 0) t k) atTop
      (nhds (networkResolvent M I k)) := tendsto_pi_nhds.mp hlimit k
  calc
    limsup (fun t ↦ D t k) atTop ≤
        limsup (fun t ↦ networkUpperPath M I (D 0) t k) atTop :=
      limsup_le_limsup (Eventually.of_forall fun t ↦ hcomparison t k)
        (isCoboundedUnder_le_of_le atTop fun t ↦ hDnonnegative t k)
        hlimit_k.isBoundedUnder_le
    _ = networkResolvent M I k := hlimit_k.limsup_eq

/-- Import-free core of Paper III, Theorem 5.2(i): every admissible policy path
has componentwise limsup bounded by the worst-case Neumann resolvent. -/
theorem network_policyFree_bound {A : ℕ → Matrix K K ℝ} {M : Matrix K K ℝ}
    {I : K → ℝ} {D : ℕ → K → ℝ}
    (hA : ∀ t, MatrixEntrywiseNonnegative (A t))
    (hAM : ∀ t, MatrixEntrywiseLE (A t) M)
    (hM : MatrixEntrywiseNonnegative M) (hI : ∀ k, 0 < I k)
    (hnorm : ‖M‖ < 1) (hstock : IsNetworkStockTrajectory A I D)
    (hD₀ : 0 ≤ D 0) :
    ∀ k, limsup (fun t ↦ D t k) atTop ≤ networkResolvent M I k := by
  have hI_nonnegative : 0 ≤ I := fun k ↦ (hI k).le
  have hcomparison := networkStockTrajectory_le_upper hA hAM hM hI_nonnegative hstock hD₀
  have hDnonnegative := networkStockTrajectory_nonnegative hA hI_nonnegative hstock hD₀
  have hlimit := networkUpperPath_tendsto M I (D 0) hnorm
  intro k
  have hlimit_k : Tendsto (fun t ↦ networkUpperPath M I (D 0) t k) atTop
      (nhds (networkResolvent M I k)) := tendsto_pi_nhds.mp hlimit k
  calc
    limsup (fun t ↦ D t k) atTop ≤
        limsup (fun t ↦ networkUpperPath M I (D 0) t k) atTop :=
      limsup_le_limsup (Eventually.of_forall fun t ↦ hcomparison t k)
        (isCoboundedUnder_le_of_le atTop fun t ↦ hDnonnegative t k)
        hlimit_k.isBoundedUnder_le
    _ = networkResolvent M I k := hlimit_k.limsup_eq

/-! ## The paper's network matrices -/

/-- Paper III, equation `eq:netstock`: the policy-dependent diagonal persistence matrix. -/
def networkPersistence (lambda₀ η β : K → ℝ) : Matrix K K ℝ :=
  Matrix.diagonal fun k ↦ (1 - lambda₀ k) * (1 - η k * (1 - β k)) ^ 2

/-- The policy-dependent transition matrix `S(β) + G`. -/
def networkTransition (lambda₀ η β : K → ℝ) (G : Matrix K K ℝ) : Matrix K K ℝ :=
  networkPersistence lambda₀ η β + G

/-- The worst-case transition matrix `bar S + G`. -/
def networkWorstMatrix (lambda₀ : K → ℝ) (G : Matrix K K ℝ) : Matrix K K ℝ :=
  Matrix.diagonal (fun k ↦ 1 - lambda₀ k) + G

/-- Standing restrictions from Paper III's network-model paragraph. -/
structure NetworkModelAssumptions
    (lambda₀ η I v c : K → ℝ) (G : Matrix K K ℝ) : Prop where
  lambda₀_pos : ∀ k, 0 < lambda₀ k
  lambda₀_le_one : ∀ k, lambda₀ k ≤ 1
  η_nonneg : ∀ k, 0 ≤ η k
  η_le_one : ∀ k, η k ≤ 1
  I_pos : ∀ k, 0 < I k
  v_pos : ∀ k, 0 < v k
  c_pos : ∀ k, 0 < c k
  c_lt_one : ∀ k, c k < 1
  G_nonnegative : MatrixEntrywiseNonnegative G

/-- Each scalar diagonal persistence term lies between zero and its full-capture value. -/
theorem networkPersistenceScalar_nonnegative_le
    {lambda₀ η β : ℝ} (hlambda₀_le_one : lambda₀ ≤ 1)
    (hη_nonneg : 0 ≤ η) (hη_le_one : η ≤ 1) (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 ≤ (1 - lambda₀) * (1 - η * (1 - β)) ^ 2 ∧
      (1 - lambda₀) * (1 - η * (1 - β)) ^ 2 ≤ 1 - lambda₀ := by
  have hresidual_nonnegative : 0 ≤ 1 - β := sub_nonneg.mpr hβ.2
  have hresidual_le_one : 1 - β ≤ 1 := by linarith [hβ.1]
  have hproduct_nonnegative : 0 ≤ η * (1 - β) :=
    mul_nonneg hη_nonneg hresidual_nonnegative
  have hproduct_le_eta : η * (1 - β) ≤ η := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hresidual_le_one hη_nonneg
  have hproduct_le_one : η * (1 - β) ≤ 1 := hproduct_le_eta.trans hη_le_one
  have hinner_nonnegative : 0 ≤ 1 - η * (1 - β) := by linarith
  have hinner_le_one : 1 - η * (1 - β) ≤ 1 := by linarith
  have hsquare_le_one : (1 - η * (1 - β)) ^ 2 ≤ (1 : ℝ) ^ 2 :=
    (sq_le_sq₀ hinner_nonnegative zero_le_one).2 hinner_le_one
  have hgrounding_nonnegative : 0 ≤ 1 - lambda₀ := sub_nonneg.mpr hlambda₀_le_one
  constructor
  · exact mul_nonneg hgrounding_nonnegative (sq_nonneg _)
  · simpa only [one_pow, mul_one] using
      mul_le_mul_of_nonneg_left hsquare_le_one hgrounding_nonnegative

omit [Fintype K] in
/-- Every admissible policy transition is entrywise nonnegative. -/
theorem networkTransition_nonnegative
    {lambda₀ η I v c : K → ℝ} {G : Matrix K K ℝ}
    (model : NetworkModelAssumptions lambda₀ η I v c G)
    {β : K → ℝ} (hβ : ∀ k, β k ∈ Icc (0 : ℝ) 1) :
    MatrixEntrywiseNonnegative (networkTransition lambda₀ η β G) := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp only [networkTransition, networkPersistence, Matrix.add_apply,
      Matrix.diagonal_apply_eq]
    have hpersistence := networkPersistenceScalar_nonnegative_le
      (model.lambda₀_le_one i)
      (model.η_nonneg i) (model.η_le_one i) (hβ i)
    exact add_nonneg hpersistence.1 (model.G_nonnegative i i)
  · simp only [networkTransition, networkPersistence, Matrix.add_apply,
      Matrix.diagonal_apply_ne _ hij, zero_add]
    exact model.G_nonnegative i j

omit [Fintype K] in
/-- Every admissible policy transition is entrywise bounded by `bar S + G`. -/
theorem networkTransition_le_worst
    {lambda₀ η I v c : K → ℝ} {G : Matrix K K ℝ}
    (model : NetworkModelAssumptions lambda₀ η I v c G)
    {β : K → ℝ} (hβ : ∀ k, β k ∈ Icc (0 : ℝ) 1) :
    MatrixEntrywiseLE (networkTransition lambda₀ η β G) (networkWorstMatrix lambda₀ G) := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp only [networkTransition, networkPersistence, networkWorstMatrix, Matrix.add_apply,
      Matrix.diagonal_apply_eq, add_le_add_iff_right]
    exact (networkPersistenceScalar_nonnegative_le
      (model.lambda₀_le_one i)
      (model.η_nonneg i) (model.η_le_one i) (hβ i)).2
  · simp only [networkTransition, networkPersistence, networkWorstMatrix, Matrix.add_apply,
      Matrix.diagonal_apply_ne _ hij, zero_add]
    exact le_rfl

omit [Fintype K] in
/-- The worst-case network matrix is entrywise nonnegative. -/
theorem networkWorstMatrix_nonnegative
    {lambda₀ η I v c : K → ℝ} {G : Matrix K K ℝ}
    (model : NetworkModelAssumptions lambda₀ η I v c G) :
    MatrixEntrywiseNonnegative (networkWorstMatrix lambda₀ G) := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp only [networkWorstMatrix, Matrix.add_apply, Matrix.diagonal_apply_eq]
    exact add_nonneg (sub_nonneg.mpr (model.lambda₀_le_one i))
      (model.G_nonnegative i i)
  · simp only [networkWorstMatrix, Matrix.add_apply, Matrix.diagonal_apply_ne _ hij]
    simpa only [zero_add] using model.G_nonnegative i j

/-- For a nonnegative real matrix, strict row sums below one are exactly the
usable `L∞` operator-norm certificate. -/
theorem linfty_opNorm_lt_one_of_rowSums
    [Nonempty K] {M : Matrix K K ℝ} (hM : MatrixEntrywiseNonnegative M)
    (hrows : ∀ i, ∑ j, M i j < 1) : ‖M‖ < 1 := by
  rw [Matrix.linfty_opNorm_def]
  have hsup : Finset.sup (α := NNReal) (Finset.univ : Finset K)
      (fun i ↦ ∑ j, ‖M i j‖₊) < (1 : NNReal) := by
    apply (Finset.sup_lt_iff (α := NNReal) (by norm_num : (0 : NNReal) < 1)).2
    intro i _
    change (∑ j, ‖M i j‖₊) < (1 : NNReal)
    apply NNReal.coe_lt_coe.mp
    simp only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs]
    calc
      ∑ j, |M i j| = ∑ j, M i j := by
        apply Finset.sum_congr rfl
        intro j _
        exact abs_of_nonneg (hM i j)
      _ < 1 := hrows i
  exact_mod_cast hsup

/-- Paper III, Theorem 5.2(iv), in its stronger and computation-ready form:
per-row content gain below local grounding forces the `L∞` norm below one. -/
theorem decentralizedGain_implies_norm_lt_one
    [Nonempty K] {lambda₀ η I v c : K → ℝ} {G : Matrix K K ℝ}
    (model : NetworkModelAssumptions lambda₀ η I v c G)
    (hgain : ∀ k, ∑ j, G k j < lambda₀ k) :
    ‖networkWorstMatrix lambda₀ G‖ < 1 := by
  apply linfty_opNorm_lt_one_of_rowSums (networkWorstMatrix_nonnegative model)
  intro k
  have hrow : (∑ j, networkWorstMatrix lambda₀ G k j) =
      1 - lambda₀ k + ∑ j, G k j := by
    simp [networkWorstMatrix, Matrix.diagonal_apply, Finset.sum_add_distrib]
  rw [hrow]
  linarith [hgain k]

/-- A real network matrix regarded as a complex matrix, so its spectral radius
captures non-real eigenvalues honestly. -/
def complexifyNetworkMatrix (M : Matrix K K ℝ) : Matrix K K ℂ :=
  M.map Complex.ofRealHom

/-- Complexification preserves the matrix `L∞` operator norm. -/
theorem complexifyNetworkMatrix_norm (M : Matrix K K ℝ) :
    ‖complexifyNetworkMatrix M‖ = ‖M‖ := by
  simp only [Matrix.linfty_opNorm_def]
  norm_cast
  congr 1 with i
  simp [complexifyNetworkMatrix]

/-- Gelfand's formula supplies a contracting matrix power whenever the complex
spectral radius is below one. -/
theorem exists_pow_norm_lt_one_of_spectralRadius_lt_one
    [Nonempty K] {A : Matrix K K ℂ}
    (hrho : spectralRadius ℂ A < 1) :
    ∃ N : ℕ, 0 < N ∧ ‖A ^ N‖ < 1 := by
  have hgelfand := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius A
  have hroot : ∀ᶠ n : ℕ in atTop,
      (‖A ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ) < 1 :=
    hgelfand (Iio_mem_nhds hrho)
  obtain ⟨n, hnroot, hnpos⟩ := (hroot.and (eventually_gt_atTop 0)).exists
  refine ⟨n, hnpos, ?_⟩
  have hexponent : 0 < (1 / n : ℝ) := by positivity
  have hbase : (‖A ^ n‖₊ : ℝ≥0∞) < 1 :=
    (ENNReal.rpow_lt_rpow_iff hexponent).mp (by simpa using hnroot)
  exact_mod_cast hbase

/-- A contracting positive power makes the full matrix geometric series
summable: split the powers into the finitely many residue classes modulo that
power. -/
theorem summable_complex_matrix_powers_of_pow_norm_lt_one
    {A : Matrix K K ℂ} {N : ℕ} (hN : 0 < N) (hpow : ‖A ^ N‖ < 1) :
    Summable (fun n : ℕ ↦ A ^ n) := by
  letI : NeZero N := ⟨hN.ne'⟩
  have hgeom : Summable (fun q : ℕ ↦ (A ^ N) ^ q) :=
    summable_geometric_of_norm_lt_one hpow
  have hfiber : ∀ r : Fin N, Summable (fun q : ℕ ↦ A ^ (q * N + (r : ℕ))) := by
    intro r
    simpa only [pow_add, pow_mul, Nat.mul_comm] using (hgeom.mul_right (A ^ (r : ℕ)))
  let e : Fin N × ℕ ≃ ℕ :=
    (Equiv.prodComm (Fin N) ℕ).trans (Nat.divModEquiv N).symm
  apply (e.summable_iff (f := fun n : ℕ ↦ A ^ n)).mp
  have hnormProduct : Summable
      (fun p : Fin N × ℕ ↦ ‖A ^ (p.2 * N + (p.1 : ℕ))‖) := by
    apply (summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)).mpr
    constructor
    · intro r
      exact (hfiber r).norm
    · exact Summable.of_finite
  have hproduct : Summable
      (fun p : Fin N × ℕ ↦ A ^ (p.2 * N + (p.1 : ℕ))) :=
    hnormProduct.of_norm
  simpa [e, Function.comp_def] using hproduct

/-- Complex spectral radius below one implies summability of the complete
matrix Neumann series. -/
theorem summable_complex_matrix_powers_of_spectralRadius_lt_one
    [Nonempty K] {A : Matrix K K ℂ}
    (hrho : spectralRadius ℂ A < 1) :
    Summable (fun n : ℕ ↦ A ^ n) := by
  obtain ⟨N, hN, hpow⟩ := exists_pow_norm_lt_one_of_spectralRadius_lt_one hrho
  exact summable_complex_matrix_powers_of_pow_norm_lt_one hN hpow

/-- Conversely, summability of all complex matrix powers forces spectral radius
strictly below one. A summable power sequence eventually has a power of norm
below one, and spectral-radius monotonicity under powers closes the argument. -/
theorem spectralRadius_lt_one_of_summable_complex_matrix_powers
    [Nonempty K] {A : Matrix K K ℂ}
    (hsum : Summable (fun n : ℕ ↦ A ^ n)) :
    spectralRadius ℂ A < 1 := by
  have hnormzero : Tendsto (fun n : ℕ ↦ ‖A ^ n‖) atTop (nhds 0) :=
    hsum.norm.tendsto_atTop_zero
  have hevent : ∀ᶠ n : ℕ in atTop, ‖A ^ n‖ < 1 :=
    (tendsto_order.1 hnormzero).2 1 zero_lt_one
  obtain ⟨N, hNnorm, hNpos⟩ := (hevent.and (eventually_gt_atTop 0)).exists
  have hNnorm' : (‖A ^ N‖₊ : ℝ≥0∞) < 1 := by exact_mod_cast hNnorm
  have hpow : (spectralRadius ℂ A) ^ N < 1 :=
    calc
      (spectralRadius ℂ A) ^ N ≤ spectralRadius ℂ (A ^ N) :=
        spectrum.spectralRadius_pow_le A N hNpos.ne'
      _ ≤ (‖A ^ N‖₊ : ℝ≥0∞) :=
        spectrum.spectralRadius_le_nnnorm (𝕜 := ℂ) (A ^ N)
      _ < 1 := hNnorm'
  exact (pow_lt_one_iff hNpos.ne').mp hpow

/-- The paper's honest complex spectral-radius premise implies summability of
the powers of the underlying real network matrix. -/
theorem summable_real_matrix_powers_of_spectralRadius_lt_one
    [Nonempty K] {M : Matrix K K ℝ}
    (hrho : spectralRadius ℂ (complexifyNetworkMatrix M) < 1) :
    Summable (fun n : ℕ ↦ M ^ n) := by
  have hcomplex : Summable (fun n : ℕ ↦ (complexifyNetworkMatrix M) ^ n) :=
    summable_complex_matrix_powers_of_spectralRadius_lt_one hrho
  have hnorm : Summable (fun n : ℕ ↦ ‖M ^ n‖) := by
    simpa only [← complexifyNetworkMatrix_norm, complexifyNetworkMatrix,
      Matrix.map_pow] using hcomplex.norm
  exact hnorm.of_norm

/-- Summability of the real matrix powers forces the honest complex spectral
radius below one. -/
theorem spectralRadius_lt_one_of_summable_real_matrix_powers
    [Nonempty K] {M : Matrix K K ℝ}
    (hsum : Summable (fun n : ℕ ↦ M ^ n)) :
    spectralRadius ℂ (complexifyNetworkMatrix M) < 1 := by
  have hnorm : Summable
      (fun n : ℕ ↦ ‖(complexifyNetworkMatrix M) ^ n‖) := by
    simpa only [← complexifyNetworkMatrix_norm, complexifyNetworkMatrix,
      Matrix.map_pow] using hsum.norm
  exact spectralRadius_lt_one_of_summable_complex_matrix_powers hnorm.of_norm

/-- The standard finite-dimensional Neumann characterization used for
interpretation in Paper III, Theorem 5.2(iii). -/
theorem summable_real_matrix_powers_iff_spectralRadius_lt_one
    [Nonempty K] {M : Matrix K K ℝ} :
    Summable (fun n : ℕ ↦ M ^ n) ↔
      spectralRadius ℂ (complexifyNetworkMatrix M) < 1 :=
  ⟨spectralRadius_lt_one_of_summable_real_matrix_powers,
    summable_real_matrix_powers_of_spectralRadius_lt_one⟩

/-- The operator-norm certificate implies the paper's spectral condition. -/
theorem norm_lt_one_implies_spectralRadius_lt_one
    [Nonempty K] {M : Matrix K K ℝ} (hnorm : ‖M‖ < 1) :
    spectralRadius ℂ (complexifyNetworkMatrix M) < 1 := by
  calc
    spectralRadius ℂ (complexifyNetworkMatrix M) ≤
        ‖complexifyNetworkMatrix M‖₊ :=
      spectrum.spectralRadius_le_nnnorm (𝕜 := ℂ) (complexifyNetworkMatrix M)
    _ < 1 := by
      exact_mod_cast (show ‖complexifyNetworkMatrix M‖ < 1 by
        rw [complexifyNetworkMatrix_norm]
        exact hnorm)

/-- Paper III, Theorem 5.2(iv), spectral corollary of the row-sum certificate. -/
theorem decentralizedGain_implies_spectralRadius_lt_one
    [Nonempty K] {lambda₀ η I v c : K → ℝ} {G : Matrix K K ℝ}
    (model : NetworkModelAssumptions lambda₀ η I v c G)
    (hgain : ∀ k, ∑ j, G k j < lambda₀ k) :
    spectralRadius ℂ
      (complexifyNetworkMatrix (networkWorstMatrix lambda₀ G)) < 1 :=
  norm_lt_one_implies_spectralRadius_lt_one
    (decentralizedGain_implies_norm_lt_one model hgain)

/-- A network stock path driven by the paper's policy-dependent transition matrices. -/
def IsNetworkLoopTrajectory (lambda₀ η : K → ℝ) (G : Matrix K K ℝ)
    (I : K → ℝ) (β D : ℕ → K → ℝ) : Prop :=
  IsNetworkStockTrajectory (fun t ↦ networkTransition lambda₀ η (β t) G) I D

/-- Paper III, Theorem 5.2(i), from the theorem's literal complex
spectral-radius premise. -/
theorem networkPolicyFreeBound_of_spectralRadius
    [Nonempty K] {lambda₀ η I v c : K → ℝ} {G : Matrix K K ℝ}
    (model : NetworkModelAssumptions lambda₀ η I v c G)
    (hrho : spectralRadius ℂ
      (complexifyNetworkMatrix (networkWorstMatrix lambda₀ G)) < 1)
    {β D : ℕ → K → ℝ} (hβ : ∀ t k, β t k ∈ Icc (0 : ℝ) 1)
    (hstock : IsNetworkLoopTrajectory lambda₀ η G I β D) (hD₀ : 0 ≤ D 0) :
    ∀ k, limsup (fun t ↦ D t k) atTop ≤
      networkResolvent (networkWorstMatrix lambda₀ G) I k := by
  let M := networkWorstMatrix lambda₀ G
  have hsum : Summable (fun n : ℕ ↦ M ^ n) :=
    summable_real_matrix_powers_of_spectralRadius_lt_one hrho
  exact network_policyFree_bound_of_summable
    (fun t ↦ networkTransition_nonnegative model (hβ t))
    (fun t ↦ networkTransition_le_worst model (hβ t))
    (networkWorstMatrix_nonnegative model) model.I_pos hsum hstock hD₀

/-- Paper III, Theorem 5.2(i), under the operator-norm sufficient condition:
the policy-free componentwise limsup bound for every network policy path. -/
theorem networkPolicyFreeBound
    [Nonempty K] {lambda₀ η I v c : K → ℝ} {G : Matrix K K ℝ}
    (model : NetworkModelAssumptions lambda₀ η I v c G)
    (hnorm : ‖networkWorstMatrix lambda₀ G‖ < 1)
    {β D : ℕ → K → ℝ} (hβ : ∀ t k, β t k ∈ Icc (0 : ℝ) 1)
    (hstock : IsNetworkLoopTrajectory lambda₀ η G I β D) (hD₀ : 0 ≤ D 0) :
    ∀ k, limsup (fun t ↦ D t k) atTop ≤ networkResolvent (networkWorstMatrix lambda₀ G) I k := by
  apply network_policyFree_bound
    (fun t ↦ networkTransition_nonnegative model (hβ t))
    (fun t ↦ networkTransition_le_worst model (hβ t))
    (networkWorstMatrix_nonnegative model) model.I_pos hnorm hstock hD₀

/-! ## Static multi-coordinate certificate -/

/-- The coordinate gradient of the separable network satisfaction objective. -/
def networkGradient (v c β D : K → ℝ) (k : K) : ℝ :=
  -v k + 2 * c k * (1 - c k * β k) * D k

omit [Fintype K] [DecidableEq K] in
/-- The exact inequality chain in Paper III, Theorem 5.2(ii). -/
theorem networkGradient_le_certificate
    {lambda₀ η I v c : K → ℝ} {G : Matrix K K ℝ}
    (model : NetworkModelAssumptions lambda₀ η I v c G)
    {R β D : K → ℝ} (hcertificate : ∀ k, 2 * c k * R k ≤ v k)
    (hβ : ∀ k, β k ∈ Icc (0 : ℝ) 1) (hD : D ≤ R) :
    ∀ k, networkGradient v c β D k ≤ -2 * c k ^ 2 * β k * R k := by
  intro k
  have hcβ_nonnegative : 0 ≤ 1 - c k * β k := by
    have hproduct : c k * β k ≤ c k := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hβ k).2 (model.c_pos k).le
    linarith [(model.c_lt_one k).le]
  have hfactor_nonnegative : 0 ≤ 2 * c k * (1 - c k * β k) :=
    mul_nonneg (mul_nonneg (by norm_num) (model.c_pos k).le) hcβ_nonnegative
  have hstock := mul_le_mul_of_nonneg_left (hD k) hfactor_nonnegative
  calc
    networkGradient v c β D k ≤
        -v k + 2 * c k * (1 - c k * β k) * R k := by
      simp only [networkGradient]
      linarith
    _ ≤ -(2 * c k * R k) + 2 * c k * (1 - c k * β k) * R k := by
      linarith [hcertificate k]
    _ = -2 * c k ^ 2 * β k * R k := by ring

omit [Fintype K] [DecidableEq K] in
/-- Every positive coordinate has a strictly negative satisfaction gradient
under the network certificate. -/
theorem networkGradient_neg_of_pos
    {lambda₀ η I v c : K → ℝ} {G : Matrix K K ℝ}
    (model : NetworkModelAssumptions lambda₀ η I v c G)
    {R β D : K → ℝ} (hR : ∀ k, 0 < R k)
    (hcertificate : ∀ k, 2 * c k * R k ≤ v k)
    (hβ : ∀ k, β k ∈ Icc (0 : ℝ) 1) (hD : D ≤ R)
    {k : K} (hβk : 0 < β k) : networkGradient v c β D k < 0 := by
  have hbound := networkGradient_le_certificate model hcertificate hβ hD k
  have hnegative : -2 * c k ^ 2 * β k * R k < 0 := by
    have hcSquare : 0 < c k ^ 2 := pow_pos (model.c_pos k) 2
    have : 0 < 2 * c k ^ 2 * β k * R k :=
      mul_pos (mul_pos (mul_pos (by norm_num) hcSquare) hβk) (hR k)
    linarith
  exact hbound.trans_lt hnegative

/-! ## Coordinatewise responsive rules -/

/-- The network version of Paper III's sign-consistent responsive rule: each
coordinate obeys Definition 1 with its own satisfaction gradient. -/
structure NetworkSignConsistentResponsive (v c : K → ℝ)
    (β D : ℕ → K → ℝ) : Prop where
  unit_interval : ∀ t k, β t k ∈ Icc (0 : ℝ) 1
  sign_consistent : ∀ k t,
    networkGradient v c (β t) (D t) k ≤ 0 → β (t + 1) k ≤ β t k
  responsive : ∀ k, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ t, networkGradient v c (β t) (D t) k ≤ -ε →
      ε ≤ β t k → δ ≤ β t k - β (t + 1) k

omit [Fintype K] [DecidableEq K] in
/-- Once the stock vector is eventually below the resolvent, the paper's
coordinatewise convergence argument is valid verbatim. -/
theorem networkDeference_tendsto_zero_of_eventually_bounded
    {lambda₀ η I v c : K → ℝ} {G : Matrix K K ℝ}
    (model : NetworkModelAssumptions lambda₀ η I v c G)
    {R : K → ℝ} (hR : ∀ k, 0 < R k)
    (hcertificate : ∀ k, 2 * c k * R k ≤ v k)
    {β D : ℕ → K → ℝ} (rule : NetworkSignConsistentResponsive v c β D)
    (heventualStock : ∃ T, ∀ t, T ≤ t → D t ≤ R) :
    Tendsto β atTop (nhds 0) := by
  obtain ⟨T, hT⟩ := heventualStock
  apply tendsto_pi_nhds.mpr
  intro k
  change Tendsto (fun t ↦ β t k) atTop (nhds (0 : ℝ))
  have hgradient : ∀ t, T ≤ t →
      networkGradient v c (β t) (D t) k ≤ -2 * c k ^ 2 * β t k * R k := by
    intro t ht
    exact networkGradient_le_certificate model hcertificate (rule.unit_interval t) (hT t ht) k
  have hcoefficient_pos : 0 < 2 * c k ^ 2 * R k := by
    exact mul_pos (mul_pos (by norm_num) (pow_pos (model.c_pos k) 2)) (hR k)
  have hstep : ∀ t, T ≤ t → β (t + 1) k ≤ β t k := by
    intro t ht
    apply rule.sign_consistent k t
    have hβnonnegative := (rule.unit_interval t k).1
    have hterm_nonnegative : 0 ≤ 2 * c k ^ 2 * β t k * R k := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg (c k))) hβnonnegative)
        (hR k).le
    exact (hgradient t ht).trans (by nlinarith)
  have hanti : Antitone (fun n ↦ β (T + n) k) := by
    apply antitone_nat_of_succ_le
    intro n
    have h := hstep (T + n) (by omega)
    simpa only [Nat.add_assoc] using h
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun n ↦ ha.trans_le (rule.unit_interval n k).1
  · intro b hb
    let r : ℝ := min ((2 * c k ^ 2 * R k) * b) b
    have hscaled_pos : 0 < (2 * c k ^ 2 * R k) * b :=
      mul_pos hcoefficient_pos hb
    have hrpos : 0 < r := by
      dsimp only [r]
      exact lt_min hscaled_pos hb
    have hrGradient : r ≤ (2 * c k ^ 2 * R k) * b := min_le_left _ _
    have hrBeta : r ≤ b := min_le_right _ _
    obtain ⟨d, hdpos, hresponsive⟩ := rule.responsive k r hrpos
    have hbelow : ∃ n, β (T + n) k < b := by
      apply exists_lt_of_uniform_descent (u := fun n ↦ β (T + n) k)
      · intro n
        exact (rule.unit_interval (T + n) k).1
      · exact hdpos
      · intro n hn
        have hscaled : (2 * c k ^ 2 * R k) * b ≤
            (2 * c k ^ 2 * R k) * β (T + n) k :=
          mul_le_mul_of_nonneg_left hn hcoefficient_pos.le
        have hgrad : networkGradient v c (β (T + n)) (D (T + n)) k ≤ -r :=
          (hgradient (T + n) (by omega)).trans (by nlinarith)
        have hdec := hresponsive (T + n) hgrad (hrBeta.trans hn)
        have hnext : β (T + n + 1) k ≤ β (T + n) k - d := by linarith
        simpa only [Nat.add_assoc] using hnext
    obtain ⟨n, hn⟩ := hbelow
    refine Filter.eventually_atTop.2 ⟨T + n, ?_⟩
    intro t ht
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ht
    have hle := hanti (Nat.le_add_right n j)
    have hle' : β ((T + n) + j) k ≤ β (T + n) k := by
      simpa only [Nat.add_assoc] using hle
    exact hle'.trans_lt hn

/-! ## Import-free forward theorem -/

/-- The clauses of the network certificate that do not use a Perron vector.
The dynamic field records the exact eventual-stock condition under which the
paper's coordinatewise Definition 1 argument closes. -/
structure NetworkCertificateForwardOfNormConclusions
    (lambda₀ η I v c : K → ℝ) (G : Matrix K K ℝ) : Prop where
  resolvent_inverse :
    networkResolvent (networkWorstMatrix lambda₀ G) I =
      Ring.inverse (1 - networkWorstMatrix lambda₀ G) *ᵥ I
  resolvent_positive :
    ∀ k, 0 < networkResolvent (networkWorstMatrix lambda₀ G) I k
  policy_free_bound : ∀ {β D : ℕ → K → ℝ},
    (∀ t k, β t k ∈ Icc (0 : ℝ) 1) →
    IsNetworkLoopTrajectory lambda₀ η G I β D → 0 ≤ D 0 →
    ∀ k, limsup (fun t ↦ D t k) atTop ≤
      networkResolvent (networkWorstMatrix lambda₀ G) I k
  certificate_gradient : ∀ {β D : K → ℝ},
    (∀ k, β k ∈ Icc (0 : ℝ) 1) →
    D ≤ networkResolvent (networkWorstMatrix lambda₀ G) I →
    ∀ k, networkGradient v c β D k ≤
      -2 * c k ^ 2 * β k * networkResolvent (networkWorstMatrix lambda₀ G) I k
  certificate_strict : ∀ {β D : K → ℝ},
    (∀ k, β k ∈ Icc (0 : ℝ) 1) →
    D ≤ networkResolvent (networkWorstMatrix lambda₀ G) I →
    ∀ {k}, 0 < β k → networkGradient v c β D k < 0
  calibration_of_eventual_stock_bound : ∀ {β D : ℕ → K → ℝ},
    NetworkSignConsistentResponsive v c β D →
    (∃ T, ∀ t, T ≤ t → D t ≤ networkResolvent (networkWorstMatrix lambda₀ G) I) →
    Tendsto β atTop (nhds 0)
  norm_implies_spectral :
    spectralRadius ℂ (complexifyNetworkMatrix (networkWorstMatrix lambda₀ G)) < 1
  decentralized_condition :
    (∀ k, ∑ j, G k j < lambda₀ k) →
      ‖networkWorstMatrix lambda₀ G‖ < 1 ∧
        spectralRadius ℂ
          (complexifyNetworkMatrix (networkWorstMatrix lambda₀ G)) < 1

/--
Paper III, Theorem 5.2 (`thm:network`), `civic_loops.tex:336`, import-free
forward direction.

Under the `L∞` operator-norm condition, the Neumann resolvent is positive and
equals the paper's inverse formula; it bounds every policy path
componentwise, gives the coordinate certificate inequality, and implies the
complex spectral-radius condition.  The per-row decentralized gain condition
implies both norm and spectral forms.  The Perron-dependent converse is kept
out of this declaration.
-/
theorem networkCertificateForward_of_norm
    [Nonempty K] {lambda₀ η I v c : K → ℝ} {G : Matrix K K ℝ}
    (model : NetworkModelAssumptions lambda₀ η I v c G)
    (hnorm : ‖networkWorstMatrix lambda₀ G‖ < 1)
    (hcertificate : ∀ k,
      2 * c k * networkResolvent (networkWorstMatrix lambda₀ G) I k ≤ v k) :
    NetworkCertificateForwardOfNormConclusions lambda₀ η I v c G := by
  let M := networkWorstMatrix lambda₀ G
  have hM : MatrixEntrywiseNonnegative M := networkWorstMatrix_nonnegative model
  have hR : ∀ k, 0 < networkResolvent M I k :=
    networkResolvent_positive hM model.I_pos hnorm
  constructor
  · exact networkResolvent_eq_ringInverse_mulVec M I hnorm
  · exact hR
  · intro β D hβ hstock hD₀
    exact networkPolicyFreeBound model hnorm hβ hstock hD₀
  · intro β D hβ hD
    exact networkGradient_le_certificate model hcertificate hβ hD
  · intro β D hβ hD k hβk
    exact networkGradient_neg_of_pos model hR hcertificate hβ hD hβk
  · intro β D rule heventual
    exact networkDeference_tendsto_zero_of_eventually_bounded
      model hR hcertificate rule heventual
  · exact norm_lt_one_implies_spectralRadius_lt_one hnorm
  · intro hgain
    exact ⟨decentralizedGain_implies_norm_lt_one model hgain,
      decentralizedGain_implies_spectralRadius_lt_one model hgain⟩

#print axioms matrix_mulVec_nonnegative
#print axioms matrix_mulVec_mono_right
#print axioms matrix_mulVec_mono_left
#print axioms matrix_pow_nonnegative
#print axioms networkUpperPath_eq
#print axioms geom_series_eq_ringInverse_of_summable
#print axioms networkResolvent_eq_ringInverse_mulVec_of_summable
#print axioms networkResolvent_fixed_of_summable
#print axioms networkUpperPath_tendsto_of_summable
#print axioms networkResolvent_eq_ringInverse_mulVec
#print axioms networkResolvent_fixed
#print axioms networkResolvent_positive
#print axioms networkResolvent_positive_of_summable
#print axioms networkUpperPath_tendsto
#print axioms networkUpperPath_nonnegative
#print axioms networkStockTrajectory_nonnegative
#print axioms networkStockTrajectory_le_upper
#print axioms network_policyFree_bound_of_summable
#print axioms network_policyFree_bound
#print axioms networkPersistenceScalar_nonnegative_le
#print axioms networkTransition_nonnegative
#print axioms networkTransition_le_worst
#print axioms networkWorstMatrix_nonnegative
#print axioms linfty_opNorm_lt_one_of_rowSums
#print axioms decentralizedGain_implies_norm_lt_one
#print axioms complexifyNetworkMatrix_norm
#print axioms exists_pow_norm_lt_one_of_spectralRadius_lt_one
#print axioms summable_complex_matrix_powers_of_pow_norm_lt_one
#print axioms summable_complex_matrix_powers_of_spectralRadius_lt_one
#print axioms spectralRadius_lt_one_of_summable_complex_matrix_powers
#print axioms summable_real_matrix_powers_of_spectralRadius_lt_one
#print axioms spectralRadius_lt_one_of_summable_real_matrix_powers
#print axioms summable_real_matrix_powers_iff_spectralRadius_lt_one
#print axioms norm_lt_one_implies_spectralRadius_lt_one
#print axioms decentralizedGain_implies_spectralRadius_lt_one
#print axioms networkPolicyFreeBound_of_spectralRadius
#print axioms networkPolicyFreeBound
#print axioms networkGradient_le_certificate
#print axioms networkGradient_neg_of_pos
#print axioms networkDeference_tendsto_zero_of_eventually_bounded
#print axioms networkCertificateForward_of_norm

end CivicAlignment.PaperIII
