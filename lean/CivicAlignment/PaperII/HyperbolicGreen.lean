/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.NemytskiiSubstitution

/-!
# The hyperbolic Green operator on bounded planar sequences

Irwin's proof of the local stable-manifold theorem solves the orbit equation
of a hyperbolic germ in the Banach space of bounded sequences.  This file
supplies the linear skeleton for the planar diagonal case `diag(μ, ν)` with
`0 < ν < 1 < μ`: the Green operator that sums the contracting coordinate
forward and the expanding coordinate backward, the injection of an initial
contracting coordinate, and the exact correspondence between fixed points of
the resulting affine equation and bounded orbits of the nonlinear germ with
prescribed contracting initial coordinate.  The key point, used for the
implicit function theorem downstream, is that boundedness *forces* the
backward representation of the expanding coordinate, because a nonzero
homogeneous solution grows like `μⁿ`.

Nothing in this file mentions the loop model; `PaperII/PlanarHadamardPerron.lean`
applies it.
-/

namespace CivicAlignment
namespace PaperII

open BoundedContinuousFunction Metric Set Filter Topology

/-- Bounded planar sequences: the Banach space in which the orbit equation of
a planar hyperbolic germ is solved. -/
abbrev SeqPair := ℕ →ᵇ (ℝ × ℝ)

/-- A planar `C¹` germ with diagonal hyperbolic linear part: expansion rate
`μ` on the first coordinate, contraction rate `ν` on the second, and a
remainder vanishing to first order at the origin. -/
structure PlanarHyperbolicGerm where
  /-- The expanding rate. -/
  μ : ℝ
  /-- The contracting rate. -/
  ν : ℝ
  /-- The nonlinear remainder. -/
  r : ℝ × ℝ → ℝ × ℝ
  /-- The derivative field of the remainder. -/
  r' : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)
  one_lt_μ : 1 < μ
  ν_pos : 0 < ν
  ν_lt_one : ν < 1
  r_hasFDerivAt : ∀ z, HasFDerivAt r (r' z) z
  r'_continuous : Continuous r'
  r_zero : r 0 = 0
  r'_zero : r' 0 = 0

namespace PlanarHyperbolicGerm

variable (Γ : PlanarHyperbolicGerm)

/-- The germ's full map: diagonal linear part plus remainder. -/
def map (z : ℝ × ℝ) : ℝ × ℝ :=
  (Γ.μ * z.1 + (Γ.r z).1, Γ.ν * z.2 + (Γ.r z).2)

/-- The remainder of a germ is continuous. -/
theorem r_continuous : Continuous Γ.r :=
  continuous_iff_continuousAt.mpr fun z => (Γ.r_hasFDerivAt z).continuousAt

theorem μ_pos : 0 < Γ.μ := lt_trans one_pos Γ.one_lt_μ

theorem μ_inv_lt_one : Γ.μ⁻¹ < 1 := inv_lt_one_of_one_lt₀ Γ.one_lt_μ

theorem μ_inv_pos : 0 < Γ.μ⁻¹ := inv_pos.mpr Γ.μ_pos

/-! ## The two Green sums -/

/-- The backward (expanding-coordinate) Green sum at slot `n`. -/
noncomputable def greenExpand (w : SeqPair) (n : ℕ) : ℝ :=
  -∑' j : ℕ, Γ.μ⁻¹ ^ (j + 1) * (w (n + j)).1

/-- The forward (contracting-coordinate) Green sum at slot `n`. -/
noncomputable def greenContract (w : SeqPair) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, Γ.ν ^ (n - 1 - k) * (w k).2

/-- Summability of the backward Green sum. -/
theorem summable_greenExpand (w : SeqPair) (n : ℕ) :
    Summable fun j : ℕ => Γ.μ⁻¹ ^ (j + 1) * (w (n + j)).1 := by
  apply Summable.of_norm_bounded
    (g := fun j : ℕ => ‖w‖ * (Γ.μ⁻¹ * Γ.μ⁻¹ ^ j))
  · exact ((summable_geometric_of_lt_one Γ.μ_inv_pos.le Γ.μ_inv_lt_one).mul_left
      Γ.μ⁻¹).mul_left ‖w‖
  · intro j
    have habs : ‖(w (n + j)).1‖ ≤ ‖w‖ :=
      (norm_fst_le (w (n + j))).trans (w.norm_coe_le_norm (n + j))
    have hpow : (0 : ℝ) ≤ Γ.μ⁻¹ ^ (j + 1) := pow_nonneg Γ.μ_inv_pos.le _
    calc ‖Γ.μ⁻¹ ^ (j + 1) * (w (n + j)).1‖
        = Γ.μ⁻¹ ^ (j + 1) * ‖(w (n + j)).1‖ := by
          rw [norm_mul, Real.norm_of_nonneg hpow]
      _ ≤ Γ.μ⁻¹ ^ (j + 1) * ‖w‖ := by
          exact mul_le_mul_of_nonneg_left habs hpow
      _ = ‖w‖ * (Γ.μ⁻¹ * Γ.μ⁻¹ ^ j) := by ring

/-- The backward Green sum is bounded by `‖w‖ / (μ - 1)`. -/
theorem abs_greenExpand_le (w : SeqPair) (n : ℕ) :
    |Γ.greenExpand w n| ≤ ‖w‖ / (Γ.μ - 1) := by
  have hsum := Γ.summable_greenExpand w n
  have habs : Summable fun j : ℕ => |Γ.μ⁻¹ ^ (j + 1) * (w (n + j)).1| := hsum.abs
  have hgeom : Summable fun j : ℕ => ‖w‖ * (Γ.μ⁻¹ * Γ.μ⁻¹ ^ j) :=
    ((summable_geometric_of_lt_one Γ.μ_inv_pos.le Γ.μ_inv_lt_one).mul_left
      Γ.μ⁻¹).mul_left ‖w‖
  have hterm : ∀ j : ℕ, |Γ.μ⁻¹ ^ (j + 1) * (w (n + j)).1| ≤
      ‖w‖ * (Γ.μ⁻¹ * Γ.μ⁻¹ ^ j) := by
    intro j
    have hval : |(w (n + j)).1| ≤ ‖w‖ :=
      (norm_fst_le (w (n + j))).trans (w.norm_coe_le_norm (n + j))
    have hpow : (0 : ℝ) ≤ Γ.μ⁻¹ ^ (j + 1) := pow_nonneg Γ.μ_inv_pos.le _
    calc |Γ.μ⁻¹ ^ (j + 1) * (w (n + j)).1|
        = Γ.μ⁻¹ ^ (j + 1) * |(w (n + j)).1| := by
          rw [abs_mul, abs_of_nonneg hpow]
      _ ≤ Γ.μ⁻¹ ^ (j + 1) * ‖w‖ := mul_le_mul_of_nonneg_left hval hpow
      _ = ‖w‖ * (Γ.μ⁻¹ * Γ.μ⁻¹ ^ j) := by ring
  have htsum : ∑' j : ℕ, ‖w‖ * (Γ.μ⁻¹ * Γ.μ⁻¹ ^ j) = ‖w‖ / (Γ.μ - 1) := by
    rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one Γ.μ_inv_pos.le
      Γ.μ_inv_lt_one]
    have hμ : Γ.μ ≠ 0 := ne_of_gt Γ.μ_pos
    have hμ1 : 1 - Γ.μ⁻¹ ≠ 0 := by
      have : Γ.μ⁻¹ < 1 := Γ.μ_inv_lt_one
      linarith
    field_simp
  have htri : |∑' j : ℕ, Γ.μ⁻¹ ^ (j + 1) * (w (n + j)).1| ≤
      ∑' j : ℕ, |Γ.μ⁻¹ ^ (j + 1) * (w (n + j)).1| := by
    simpa [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun j : ℕ => Γ.μ⁻¹ ^ (j + 1) * (w (n + j)).1)
        (by simpa [Real.norm_eq_abs] using habs)
  calc |Γ.greenExpand w n|
      = |∑' j : ℕ, Γ.μ⁻¹ ^ (j + 1) * (w (n + j)).1| := by
        rw [greenExpand, abs_neg]
    _ ≤ ∑' j : ℕ, |Γ.μ⁻¹ ^ (j + 1) * (w (n + j)).1| := htri
    _ ≤ ∑' j : ℕ, ‖w‖ * (Γ.μ⁻¹ * Γ.μ⁻¹ ^ j) := habs.tsum_mono hgeom hterm
    _ = ‖w‖ / (Γ.μ - 1) := htsum

/-- The forward Green sum is bounded by `‖w‖ / (1 - ν)`. -/
theorem abs_greenContract_le (w : SeqPair) (n : ℕ) :
    |Γ.greenContract w n| ≤ ‖w‖ / (1 - Γ.ν) := by
  have hν0 : (0 : ℝ) ≤ Γ.ν := Γ.ν_pos.le
  have hterm : ∀ k ∈ Finset.range n,
      |Γ.ν ^ (n - 1 - k) * (w k).2| ≤ Γ.ν ^ (n - 1 - k) * ‖w‖ := by
    intro k _
    have habs : |(w k).2| ≤ ‖w‖ :=
      (norm_snd_le (w k)).trans (w.norm_coe_le_norm k)
    have hpow : (0 : ℝ) ≤ Γ.ν ^ (n - 1 - k) := pow_nonneg hν0 _
    rw [abs_mul, abs_of_nonneg hpow]
    exact mul_le_mul_of_nonneg_left habs hpow
  calc |Γ.greenContract w n|
      ≤ ∑ k ∈ Finset.range n, |Γ.ν ^ (n - 1 - k) * (w k).2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, Γ.ν ^ (n - 1 - k) * ‖w‖ :=
        Finset.sum_le_sum hterm
    _ = (∑ k ∈ Finset.range n, Γ.ν ^ (n - 1 - k)) * ‖w‖ := by
        rw [Finset.sum_mul]
    _ = (∑ k ∈ Finset.range n, Γ.ν ^ k) * ‖w‖ := by
        rw [Finset.sum_range_reflect]
    _ ≤ (1 - Γ.ν)⁻¹ * ‖w‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg w)
        have hsum : Summable fun k : ℕ => Γ.ν ^ k :=
          summable_geometric_of_lt_one hν0 Γ.ν_lt_one
        calc ∑ k ∈ Finset.range n, Γ.ν ^ k
            ≤ ∑' k : ℕ, Γ.ν ^ k :=
              hsum.sum_le_tsum _ (fun k _ => pow_nonneg hν0 k)
          _ = (1 - Γ.ν)⁻¹ := tsum_geometric_of_lt_one hν0 Γ.ν_lt_one
    _ = ‖w‖ / (1 - Γ.ν) := by rw [div_eq_inv_mul]

/-! ## Recursions of the Green sums -/

/-- The backward Green sum satisfies the expanding recursion. -/
theorem greenExpand_succ (w : SeqPair) (n : ℕ) :
    Γ.greenExpand w (n + 1) = Γ.μ * Γ.greenExpand w n + (w n).1 := by
  have hsum := Γ.summable_greenExpand w n
  have hμ : Γ.μ ≠ 0 := ne_of_gt Γ.μ_pos
  have hmul : Γ.μ * Γ.greenExpand w n =
      -∑' j : ℕ, Γ.μ⁻¹ ^ j * (w (n + j)).1 := by
    rw [greenExpand, mul_neg, ← tsum_mul_left]
    congr 1
    apply tsum_congr
    intro j
    rw [pow_succ']
    field_simp
  have hpeel : ∑' j : ℕ, Γ.μ⁻¹ ^ j * (w (n + j)).1 =
      (w n).1 + ∑' j : ℕ, Γ.μ⁻¹ ^ (j + 1) * (w (n + (j + 1))).1 := by
    have hs : Summable fun j : ℕ => Γ.μ⁻¹ ^ j * (w (n + j)).1 := by
      apply Summable.of_norm_bounded
        (g := fun j : ℕ => ‖w‖ * Γ.μ⁻¹ ^ j)
      · exact (summable_geometric_of_lt_one Γ.μ_inv_pos.le
          Γ.μ_inv_lt_one).mul_left ‖w‖
      · intro j
        have habs : ‖(w (n + j)).1‖ ≤ ‖w‖ :=
          (norm_fst_le (w (n + j))).trans (w.norm_coe_le_norm (n + j))
        have hpow : (0 : ℝ) ≤ Γ.μ⁻¹ ^ j := pow_nonneg Γ.μ_inv_pos.le _
        calc ‖Γ.μ⁻¹ ^ j * (w (n + j)).1‖
            = Γ.μ⁻¹ ^ j * ‖(w (n + j)).1‖ := by
              rw [norm_mul, Real.norm_of_nonneg hpow]
          _ ≤ Γ.μ⁻¹ ^ j * ‖w‖ := mul_le_mul_of_nonneg_left habs hpow
          _ = ‖w‖ * Γ.μ⁻¹ ^ j := mul_comm _ _
    have := hs.tsum_eq_zero_add
    simpa using this
  have hshift : ∑' j : ℕ, Γ.μ⁻¹ ^ (j + 1) * (w (n + (j + 1))).1 =
      ∑' j : ℕ, Γ.μ⁻¹ ^ (j + 1) * (w (n + 1 + j)).1 := by
    apply tsum_congr
    intro j
    rw [show n + (j + 1) = n + 1 + j from by omega]
  rw [hmul, hpeel, hshift, greenExpand]
  ring

/-- The forward Green sum satisfies the contracting recursion. -/
theorem greenContract_succ (w : SeqPair) (n : ℕ) :
    Γ.greenContract w (n + 1) = Γ.ν * Γ.greenContract w n + (w n).2 := by
  rw [greenContract, greenContract, Finset.sum_range_succ]
  have hlast : Γ.ν ^ (n + 1 - 1 - n) * (w n).2 = (w n).2 := by
    have : n + 1 - 1 - n = 0 := by omega
    rw [this, pow_zero, one_mul]
  have hfactor : ∑ k ∈ Finset.range n, Γ.ν ^ (n + 1 - 1 - k) * (w k).2 =
      Γ.ν * ∑ k ∈ Finset.range n, Γ.ν ^ (n - 1 - k) * (w k).2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hexp : n + 1 - 1 - k = (n - 1 - k) + 1 := by omega
    rw [hexp, pow_succ]
    ring
  rw [hfactor, hlast]

/-- At slot zero, the forward Green sum vanishes. -/
theorem greenContract_zero (w : SeqPair) : Γ.greenContract w 0 = 0 := by
  simp [greenContract]

/-! ## The Green operator and the initial-coordinate injection -/

/-- The nonnegative uniform bound for the Green operator. -/
noncomputable def greenBound : ℝ :=
  max ((Γ.μ - 1)⁻¹) ((1 - Γ.ν)⁻¹)

theorem greenBound_nonneg : 0 ≤ Γ.greenBound := by
  have h1 : (0 : ℝ) ≤ (Γ.μ - 1)⁻¹ := by
    have : (0 : ℝ) < Γ.μ - 1 := by linarith [Γ.one_lt_μ]
    positivity
  exact le_trans h1 (le_max_left _ _)

/-- The pointwise pair of Green sums is uniformly bounded. -/
theorem greenPair_norm_le (w : SeqPair) (n : ℕ) :
    ‖(Γ.greenExpand w n, Γ.greenContract w n)‖ ≤ Γ.greenBound * ‖w‖ := by
  have hμ1 : (0 : ℝ) < Γ.μ - 1 := by linarith [Γ.one_lt_μ]
  have hν1 : (0 : ℝ) < 1 - Γ.ν := by linarith [Γ.ν_lt_one]
  rw [Prod.norm_def]
  apply max_le
  · calc ‖Γ.greenExpand w n‖ = |Γ.greenExpand w n| := rfl
      _ ≤ ‖w‖ / (Γ.μ - 1) := Γ.abs_greenExpand_le w n
      _ = (Γ.μ - 1)⁻¹ * ‖w‖ := by rw [div_eq_inv_mul]
      _ ≤ Γ.greenBound * ‖w‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg w)
  · calc ‖Γ.greenContract w n‖ = |Γ.greenContract w n| := rfl
      _ ≤ ‖w‖ / (1 - Γ.ν) := Γ.abs_greenContract_le w n
      _ = (1 - Γ.ν)⁻¹ * ‖w‖ := by rw [div_eq_inv_mul]
      _ ≤ Γ.greenBound * ‖w‖ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg w)

/-- The Green sums are additive in the source sequence. -/
theorem greenExpand_add (w₁ w₂ : SeqPair) (n : ℕ) :
    Γ.greenExpand (w₁ + w₂) n = Γ.greenExpand w₁ n + Γ.greenExpand w₂ n := by
  rw [greenExpand, greenExpand, greenExpand]
  have h : ∀ j : ℕ, Γ.μ⁻¹ ^ (j + 1) * ((w₁ + w₂) (n + j)).1 =
      Γ.μ⁻¹ ^ (j + 1) * (w₁ (n + j)).1 + Γ.μ⁻¹ ^ (j + 1) * (w₂ (n + j)).1 := by
    intro j
    have : ((w₁ + w₂) (n + j)) = w₁ (n + j) + w₂ (n + j) := rfl
    rw [this, Prod.fst_add]
    ring
  rw [tsum_congr h, (Γ.summable_greenExpand w₁ n).tsum_add
    (Γ.summable_greenExpand w₂ n)]
  ring

theorem greenContract_add (w₁ w₂ : SeqPair) (n : ℕ) :
    Γ.greenContract (w₁ + w₂) n = Γ.greenContract w₁ n + Γ.greenContract w₂ n := by
  rw [greenContract, greenContract, greenContract, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have : ((w₁ + w₂) k) = w₁ k + w₂ k := rfl
  rw [this, Prod.snd_add]
  ring

/-- The Green sums are homogeneous in the source sequence. -/
theorem greenExpand_smul (c : ℝ) (w : SeqPair) (n : ℕ) :
    Γ.greenExpand (c • w) n = c * Γ.greenExpand w n := by
  rw [greenExpand, greenExpand]
  have h : ∀ j : ℕ, Γ.μ⁻¹ ^ (j + 1) * ((c • w) (n + j)).1 =
      c * (Γ.μ⁻¹ ^ (j + 1) * (w (n + j)).1) := by
    intro j
    have : ((c • w) (n + j)) = c • w (n + j) := rfl
    rw [this, Prod.smul_fst, smul_eq_mul]
    ring
  rw [tsum_congr h, tsum_mul_left]
  ring

theorem greenContract_smul (c : ℝ) (w : SeqPair) (n : ℕ) :
    Γ.greenContract (c • w) n = c * Γ.greenContract w n := by
  rw [greenContract, greenContract, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have : ((c • w) k) = c • w k := rfl
  rw [this, Prod.smul_snd, smul_eq_mul]
  ring

/-- The hyperbolic Green operator: backward sum in the expanding coordinate,
forward sum in the contracting coordinate. -/
noncomputable def green : SeqPair →L[ℝ] SeqPair :=
  LinearMap.mkContinuous
    { toFun := fun w => ofNormedAddCommGroupDiscrete
        (fun n => (Γ.greenExpand w n, Γ.greenContract w n))
        (Γ.greenBound * ‖w‖) (Γ.greenPair_norm_le w)
      map_add' := by
        intro w₁ w₂
        refine BoundedContinuousFunction.ext fun n => ?_
        exact Prod.ext (Γ.greenExpand_add w₁ w₂ n) (Γ.greenContract_add w₁ w₂ n)
      map_smul' := by
        intro c w
        refine BoundedContinuousFunction.ext fun n => ?_
        exact Prod.ext (Γ.greenExpand_smul c w n) (Γ.greenContract_smul c w n) }
    Γ.greenBound
    (fun w => by
      apply (norm_le (mul_nonneg Γ.greenBound_nonneg (norm_nonneg w))).mpr
      intro n
      exact Γ.greenPair_norm_le w n)

@[simp] theorem green_apply (w : SeqPair) (n : ℕ) :
    Γ.green w n = (Γ.greenExpand w n, Γ.greenContract w n) := rfl

/-- Injection of an initial contracting coordinate as the linear model orbit
`n ↦ (0, νⁿ σ)`. -/
noncomputable def contractInjection : ℝ →L[ℝ] SeqPair :=
  LinearMap.mkContinuous
    { toFun := fun σ => ofNormedAddCommGroupDiscrete
        (fun n => ((0 : ℝ), Γ.ν ^ n * σ)) ‖σ‖
        (fun n => by
          rw [Prod.norm_def]
          apply max_le (by simp)
          have hpow : Γ.ν ^ n ≤ 1 :=
            pow_le_one₀ Γ.ν_pos.le Γ.ν_lt_one.le
          have hpow0 : (0 : ℝ) ≤ Γ.ν ^ n := pow_nonneg Γ.ν_pos.le n
          calc ‖Γ.ν ^ n * σ‖ = Γ.ν ^ n * |σ| := by
                rw [norm_mul, Real.norm_of_nonneg hpow0]; rfl
            _ ≤ 1 * |σ| := mul_le_mul_of_nonneg_right hpow (abs_nonneg σ)
            _ = ‖σ‖ := by rw [one_mul]; rfl)
      map_add' := by
        intro σ₁ σ₂
        refine BoundedContinuousFunction.ext fun n => ?_
        exact Prod.ext (by simp) (by simp [mul_add])
      map_smul' := by
        intro c σ
        refine BoundedContinuousFunction.ext fun n => ?_
        exact Prod.ext (by simp) (by simp [smul_eq_mul]; ring) }
    1
    (fun σ => by
      apply (norm_le (by positivity)).mpr
      intro n
      have : ‖((0 : ℝ), Γ.ν ^ n * σ)‖ ≤ ‖σ‖ := by
        rw [Prod.norm_def]
        apply max_le (by simp)
        have hpow : Γ.ν ^ n ≤ 1 := pow_le_one₀ Γ.ν_pos.le Γ.ν_lt_one.le
        have hpow0 : (0 : ℝ) ≤ Γ.ν ^ n := pow_nonneg Γ.ν_pos.le n
        calc ‖Γ.ν ^ n * σ‖ = Γ.ν ^ n * |σ| := by
              rw [norm_mul, Real.norm_of_nonneg hpow0]; rfl
          _ ≤ 1 * |σ| := mul_le_mul_of_nonneg_right hpow (abs_nonneg σ)
          _ = ‖σ‖ := by rw [one_mul]; rfl
      simpa [one_mul] using this)

@[simp] theorem contractInjection_apply (σ : ℝ) (n : ℕ) :
    Γ.contractInjection σ n = ((0 : ℝ), Γ.ν ^ n * σ) := rfl

/-! ## Fixed points of the affine Green equation are exactly bounded orbits -/

/-- The substituted remainder sequence of a bounded sequence. -/
noncomputable def remainderSeq (x : SeqPair) : SeqPair :=
  substitutionMap Γ.r Γ.r_continuous x

@[simp] theorem remainderSeq_apply (x : SeqPair) (n : ℕ) :
    Γ.remainderSeq x n = Γ.r (x n) := rfl

/-- The affine Green equation with initial contracting coordinate `σ`. -/
def IsGreenSolution (σ : ℝ) (x : SeqPair) : Prop :=
  x = Γ.contractInjection σ + Γ.green (Γ.remainderSeq x)

/-- A Green solution has the explicit componentwise form. -/
theorem IsGreenSolution.components {Γ : PlanarHyperbolicGerm} {σ : ℝ}
    {x : SeqPair} (hx : Γ.IsGreenSolution σ x) (n : ℕ) :
    x n = (Γ.greenExpand (Γ.remainderSeq x) n,
      Γ.ν ^ n * σ + Γ.greenContract (Γ.remainderSeq x) n) := by
  have hxn : x n = (Γ.contractInjection σ) n + (Γ.green (Γ.remainderSeq x)) n := by
    conv_lhs => rw [hx]
    rfl
  rw [hxn, contractInjection_apply, green_apply, Prod.mk_add_mk, zero_add]

/-- Green solutions are bounded orbits of the germ with prescribed initial
contracting coordinate. -/
theorem IsGreenSolution.orbit {Γ : PlanarHyperbolicGerm} {σ : ℝ} {x : SeqPair}
    (hx : Γ.IsGreenSolution σ x) :
    (x 0).2 = σ ∧ ∀ n, x (n + 1) = Γ.map (x n) := by
  have hA : ∀ m, (x m).1 = Γ.greenExpand (Γ.remainderSeq x) m := by
    intro m
    rw [hx.components m]
  have hB : ∀ m, (x m).2 =
      Γ.ν ^ m * σ + Γ.greenContract (Γ.remainderSeq x) m := by
    intro m
    rw [hx.components m]
  constructor
  · rw [hB 0, pow_zero, one_mul, Γ.greenContract_zero, add_zero]
  · intro n
    have hE := Γ.greenExpand_succ (Γ.remainderSeq x) n
    have hC := Γ.greenContract_succ (Γ.remainderSeq x) n
    have hmapfst : (Γ.map (x n)).1 = Γ.μ * (x n).1 + (Γ.r (x n)).1 := rfl
    have hmapsnd : (Γ.map (x n)).2 = Γ.ν * (x n).2 + (Γ.r (x n)).2 := rfl
    have hrfst : (Γ.remainderSeq x n).1 = (Γ.r (x n)).1 := rfl
    have hrsnd : (Γ.remainderSeq x n).2 = (Γ.r (x n)).2 := rfl
    refine Prod.ext ?_ ?_
    · rw [hmapfst, hA (n + 1), hA n, hE, hrfst]
    · rw [hmapsnd, hB (n + 1), hB n, hC, hrsnd, pow_succ]
      ring

/-- Conversely, every bounded orbit with initial contracting coordinate `σ`
solves the affine Green equation: boundedness forces the backward
representation of the expanding coordinate. -/
theorem isGreenSolution_of_orbit {Γ : PlanarHyperbolicGerm} {σ : ℝ} {x : SeqPair}
    (h0 : (x 0).2 = σ) (horbit : ∀ n, x (n + 1) = Γ.map (x n)) :
    Γ.IsGreenSolution σ x := by
  set w := Γ.remainderSeq x with hw
  -- the contracting coordinate: forward induction
  have hcontract : ∀ n, (x n).2 = Γ.ν ^ n * σ + Γ.greenContract w n := by
    intro n
    induction n with
    | zero => simp [h0, Γ.greenContract_zero]
    | succ n ih =>
        have hstep : (x (n + 1)).2 = Γ.ν * (x n).2 + (Γ.r (x n)).2 :=
          (congrArg Prod.snd (horbit n)).trans rfl
        have hwn : (w n).2 = (Γ.r (x n)).2 := rfl
        rw [hstep, ih, Γ.greenContract_succ, hwn, pow_succ]
        ring
  -- the expanding coordinate: the deviation from the backward sum grows
  -- geometrically, so boundedness kills it
  have hexpandRec : ∀ n, (x (n + 1)).1 = Γ.μ * (x n).1 + (w n).1 := by
    intro n
    exact (congrArg Prod.fst (horbit n)).trans rfl
  have hdev : ∀ n, (x n).1 - Γ.greenExpand w n =
      Γ.μ ^ n * ((x 0).1 - Γ.greenExpand w 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [hexpandRec n, Γ.greenExpand_succ w n, pow_succ]
        have : Γ.μ * (x n).1 + (w n).1 - (Γ.μ * Γ.greenExpand w n + (w n).1) =
            Γ.μ * ((x n).1 - Γ.greenExpand w n) := by ring
        rw [this, ih]
        ring
  have hbound : ∀ n, |(x n).1 - Γ.greenExpand w n| ≤ ‖x‖ + ‖w‖ / (Γ.μ - 1) := by
    intro n
    have h1 : |(x n).1| ≤ ‖x‖ :=
      (norm_fst_le (x n)).trans (x.norm_coe_le_norm n)
    have h2 := Γ.abs_greenExpand_le w n
    calc |(x n).1 - Γ.greenExpand w n|
        ≤ |(x n).1| + |Γ.greenExpand w n| := abs_sub _ _
      _ ≤ ‖x‖ + ‖w‖ / (Γ.μ - 1) := add_le_add h1 h2
  have hzero : (x 0).1 - Γ.greenExpand w 0 = 0 := by
    by_contra hne
    set e := (x 0).1 - Γ.greenExpand w 0 with he
    have hepos : 0 < |e| := abs_pos.mpr hne
    set M := ‖x‖ + ‖w‖ / (Γ.μ - 1) with hM
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / |e|) Γ.one_lt_μ
    have hgrow : |(x n).1 - Γ.greenExpand w n| = Γ.μ ^ n * |e| := by
      rw [hdev n, abs_mul, abs_of_nonneg (pow_nonneg Γ.μ_pos.le n)]
    have hMn : Γ.μ ^ n * |e| ≤ M := hgrow ▸ hbound n
    have : M / |e| < Γ.μ ^ n := hn
    have hcontra : M < Γ.μ ^ n * |e| := by
      rwa [div_lt_iff₀ hepos] at this
    linarith
  have hexpand : ∀ n, (x n).1 = Γ.greenExpand w n := by
    intro n
    have := hdev n
    rw [hzero, mul_zero] at this
    linarith [this]
  rw [IsGreenSolution]
  refine BoundedContinuousFunction.ext fun n => ?_
  have hsplit : (Γ.contractInjection σ + Γ.green w) n =
      (Γ.contractInjection σ) n + (Γ.green w) n := rfl
  have hrhs : (Γ.contractInjection σ + Γ.green w) n =
      (Γ.greenExpand w n, Γ.ν ^ n * σ + Γ.greenContract w n) := by
    rw [hsplit, contractInjection_apply, green_apply, Prod.mk_add_mk, zero_add]
  rw [hrhs]
  exact Prod.ext (hexpand n) (hcontract n)

end PlanarHyperbolicGerm

end PaperII
end CivicAlignment

#print axioms CivicAlignment.PaperII.PlanarHyperbolicGerm.IsGreenSolution.orbit
#print axioms CivicAlignment.PaperII.PlanarHyperbolicGerm.isGreenSolution_of_orbit
