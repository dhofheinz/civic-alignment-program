/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.Basic

/-!
# Paper III: aggregation and conservation

This file formalizes the four cells of Paper III's aggregation--conservation
map. The variable `u = 1 - β` is the residual independence weight.
-/

namespace CivicAlignment.PaperIII

open Set

/-- The stationary deviation of the single-claim amplitude recursion. -/
noncomputable def singleClaimStationary (injection η ζ u : ℝ) : ℝ :=
  injection / (η * u - ζ)

/-- The single-claim measured gap for loss degree `p`. -/
noncomputable def singleClaimGap (p : ℕ) (injection η ζ u : ℝ) : ℝ :=
  (|injection| * u / (η * u - ζ)) ^ p

/-- The stationary mass of an `L¹` portfolio. -/
noncomputable def l1PortfolioStationary (J lambda₀ η g u : ℝ) : ℝ :=
  J / (lambda₀ - g + (1 - lambda₀) * η * u)

/-- The stationary measured gap of an `L¹` portfolio. -/
noncomputable def l1PortfolioGap (J lambda₀ η g u : ℝ) : ℝ :=
  u * J / (lambda₀ - g + (1 - lambda₀) * η * u)

/-- The stationary mass of an `L²` portfolio. -/
noncomputable def l2PortfolioStationary (I lambda₀ η g u : ℝ) : ℝ :=
  I / (1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g)

/-- The stationary measured gap of an `L²` portfolio. -/
noncomputable def l2PortfolioGap (I lambda₀ η g u : ℝ) : ℝ :=
  u ^ 2 * I / (1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g)

/-- The interior critical residual weight in the super-grounding band. -/
noncomputable def l2CriticalResidual (lambda₀ η g : ℝ) : ℝ :=
  (g - lambda₀) / (η * (1 - lambda₀))

/-- Policies for which the single-claim affine law has a finite stable fixed point. -/
def singleClaimStablePolicies (η ζ : ℝ) : Set ℝ :=
  {β | β ∈ Icc (0 : ℝ) 1 ∧ ζ < η * (1 - β)}

/-- Policies for which the `L¹` affine law has a finite stable fixed point. -/
def l1StablePolicies (lambda₀ η g : ℝ) : Set ℝ :=
  {β | β ∈ Icc (0 : ℝ) 1 ∧
    0 < lambda₀ - g + (1 - lambda₀) * η * (1 - β)}

/-- Policies for which the `L²` affine law has a finite stable fixed point. -/
def l2StablePolicies (lambda₀ η g : ℝ) : Set ℝ :=
  {β | β ∈ Icc (0 : ℝ) 1 ∧
    0 < 1 - (1 - lambda₀) * (1 - η * (1 - β)) ^ 2 - g}

/-- The paper's single-claim stationary value is a fixed point of its affine law. -/
theorem singleClaimStationary_fixed {injection η ζ u : ℝ}
    (hdenominator : η * u - ζ ≠ 0) :
    (1 - η * u + ζ) * singleClaimStationary injection η ζ u + injection =
      singleClaimStationary injection η ζ u := by
  simp only [singleClaimStationary]
  field_simp [hdenominator]
  ring

/-- The first table cell is the measured loss at the single-claim fixed point. -/
theorem singleClaimGap_eq_measuredStationary {p : ℕ} {injection η ζ u : ℝ}
    (hdenominator : 0 < η * u - ζ) :
    (u * |singleClaimStationary injection η ζ u|) ^ p =
      singleClaimGap p injection η ζ u := by
  simp only [singleClaimStationary, singleClaimGap, abs_div,
    abs_of_pos hdenominator]
  congr 1
  field_simp [hdenominator.ne']

/-- The paper's `L¹` stationary mass is a fixed point of its affine law. -/
theorem l1PortfolioStationary_fixed {J lambda₀ η g u : ℝ}
    (hdenominator : lambda₀ - g + (1 - lambda₀) * η * u ≠ 0) :
    ((1 - lambda₀) * (1 - η * u) + g) *
        l1PortfolioStationary J lambda₀ η g u + J =
      l1PortfolioStationary J lambda₀ η g u := by
  simp only [l1PortfolioStationary]
  field_simp [hdenominator]
  ring

/-- The second table cell is residual weight times stationary `L¹` mass. -/
theorem l1PortfolioGap_eq_measuredStationary {J lambda₀ η g u : ℝ} :
    u * l1PortfolioStationary J lambda₀ η g u =
      l1PortfolioGap J lambda₀ η g u := by
  simp only [l1PortfolioStationary, l1PortfolioGap]
  ring

/-- The paper's `L²` stationary mass is a fixed point of its affine law. -/
theorem l2PortfolioStationary_fixed {I lambda₀ η g u : ℝ}
    (hdenominator : 1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g ≠ 0) :
    ((1 - lambda₀) * (1 - η * u) ^ 2 + g) *
        l2PortfolioStationary I lambda₀ η g u + I =
      l2PortfolioStationary I lambda₀ η g u := by
  simp only [l2PortfolioStationary]
  field_simp [hdenominator]
  ring

/-- The third table cell is squared residual weight times stationary `L²` mass. -/
theorem l2PortfolioGap_eq_measuredStationary {I lambda₀ η g u : ℝ} :
    u ^ 2 * l2PortfolioStationary I lambda₀ η g u =
      l2PortfolioGap I lambda₀ η g u := by
  simp only [l2PortfolioStationary, l2PortfolioGap]
  ring

/-! ## Exact derivatives behind the behavior column -/

/-- Derivative of the single-claim residual-weight ratio. -/
theorem hasDerivAt_singleClaimRatio {injection η ζ u : ℝ}
    (hdenominator : η * u - ζ ≠ 0) :
    HasDerivAt (fun x ↦ |injection| * x / (η * x - ζ))
      (-|injection| * ζ / (η * u - ζ) ^ 2) u := by
  have hnum : HasDerivAt (fun x : ℝ ↦ |injection| * x) |injection| u := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id u).const_mul |injection|
  have hden : HasDerivAt (fun x : ℝ ↦ η * x - ζ) η u := by
    simpa only [id_eq, mul_one, sub_zero] using
      ((hasDerivAt_id u).const_mul η).sub_const ζ
  exact (hnum.div hden hdenominator).congr_deriv (by ring)

/-- Derivative of the `L¹` portfolio gap. -/
theorem hasDerivAt_l1PortfolioGap {J lambda₀ η g u : ℝ}
    (hdenominator : lambda₀ - g + (1 - lambda₀) * η * u ≠ 0) :
    HasDerivAt (l1PortfolioGap J lambda₀ η g)
      (J * (lambda₀ - g) /
        (lambda₀ - g + (1 - lambda₀) * η * u) ^ 2) u := by
  have hnum : HasDerivAt (fun x : ℝ ↦ x * J) J u := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id u).mul_const J
  have hden : HasDerivAt
      (fun x : ℝ ↦ lambda₀ - g + (1 - lambda₀) * η * x)
      ((1 - lambda₀) * η) u := by
    simpa only [id_eq, mul_one, add_comm] using
      ((hasDerivAt_id u).const_mul ((1 - lambda₀) * η)).const_add
        (lambda₀ - g)
  exact (hnum.div hden hdenominator).congr_deriv (by ring)

/--
Derivative of the `L²` portfolio gap; its sign is the sign of the paper's
affine bracket.
-/
theorem hasDerivAt_l2PortfolioGap {I lambda₀ η g u : ℝ}
    (hdenominator : 1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g ≠ 0) :
    HasDerivAt (l2PortfolioGap I lambda₀ η g)
      (2 * I * u * (lambda₀ + η * u * (1 - lambda₀) - g) /
        (1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g) ^ 2) u := by
  have hnum : HasDerivAt (fun x : ℝ ↦ x ^ 2 * I) (2 * u * I) u := by
    simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, pow_one, mul_one] using
      (((hasDerivAt_id u).pow 2).mul_const I).congr_deriv (by simp only [id_eq]; ring)
  have hinner : HasDerivAt (fun x : ℝ ↦ 1 - η * x) (-η) u := by
    simpa only [id_eq, mul_one, neg_mul, one_mul] using
      ((hasDerivAt_id u).const_mul η).const_sub 1
  have hsquare : HasDerivAt (fun x : ℝ ↦ (1 - η * x) ^ 2)
      (-2 * η * (1 - η * u)) u := by
    exact (hinner.pow 2).congr_deriv (by norm_num; ring)
  have hscaled : HasDerivAt
      (fun x : ℝ ↦ (1 - lambda₀) * (1 - η * x) ^ 2)
      (-2 * (1 - lambda₀) * η * (1 - η * u)) u := by
    exact (hsquare.const_mul (1 - lambda₀)).congr_deriv (by ring)
  have hden : HasDerivAt
      (fun x : ℝ ↦ 1 - (1 - lambda₀) * (1 - η * x) ^ 2 - g)
      (2 * (1 - lambda₀) * η * (1 - η * u)) u := by
    exact ((hscaled.const_sub 1).sub_const g).congr_deriv (by ring)
  exact (hnum.div hden hdenominator).congr_deriv (by ring)

/-! ## Conservation loci and monotonic behavior -/

/-- With no amplitude feedback, both single-claim loss degrees are exactly conserved. -/
theorem singleClaimGap_noFeedback {p : ℕ} {injection η u : ℝ}
    (hη : η ≠ 0) (hu : u ≠ 0) :
    singleClaimGap p injection η 0 u = (|injection| / η) ^ p := by
  simp only [singleClaimGap, sub_zero]
  congr 1
  field_simp [hη, hu]

/-- Positive amplitude feedback makes either single-claim loss rise strictly with `β`. -/
theorem singleClaimGap_strictMonoOn_policy {p : ℕ} {injection η ζ : ℝ}
    (hp : p = 1 ∨ p = 2) (hinjection : injection ≠ 0)
    (hη : 0 < η) (hζ : 0 < ζ) :
    StrictMonoOn (fun β ↦ singleClaimGap p injection η ζ (1 - β))
      (singleClaimStablePolicies η ζ) := by
  intro β₁ hβ₁ β₂ hβ₂ hβ
  let u₁ : ℝ := 1 - β₁
  let u₂ : ℝ := 1 - β₂
  have huOrder : u₂ < u₁ := by dsimp only [u₁, u₂]; linarith
  have hden₁ : 0 < η * u₁ - ζ := by
    dsimp only [singleClaimStablePolicies, Set.mem_setOf_eq] at hβ₁
    dsimp only [u₁]
    linarith [hβ₁.2]
  have hden₂ : 0 < η * u₂ - ζ := by
    dsimp only [singleClaimStablePolicies, Set.mem_setOf_eq] at hβ₂
    dsimp only [u₂]
    linarith [hβ₂.2]
  have hu₁pos : 0 < u₁ := by
    have hproduct : 0 < η * u₁ := by linarith
    rcases (mul_pos_iff.mp hproduct) with h | h
    · exact h.2
    · exact (not_lt_of_ge hη.le h.1).elim
  have hu₂pos : 0 < u₂ := by
    have hproduct : 0 < η * u₂ := by linarith
    rcases (mul_pos_iff.mp hproduct) with h | h
    · exact h.2
    · exact (not_lt_of_ge hη.le h.1).elim
  have habs : 0 < |injection| := abs_pos.mpr hinjection
  have hratio : |injection| * u₁ / (η * u₁ - ζ) <
      |injection| * u₂ / (η * u₂ - ζ) := by
    apply (div_lt_div_iff₀ hden₁ hden₂).2
    nlinarith [mul_pos (mul_pos habs hζ) (sub_pos.mpr huOrder)]
  rcases hp with rfl | rfl
  · simpa only [singleClaimGap, pow_one, u₁, u₂] using hratio
  · have hleft : 0 ≤ |injection| * u₁ / (η * u₁ - ζ) :=
      (div_pos (mul_pos habs hu₁pos) hden₁).le
    have hright : 0 ≤ |injection| * u₂ / (η * u₂ - ζ) :=
      (div_pos (mul_pos habs hu₂pos) hden₂).le
    have hsquare := (sq_lt_sq₀ hleft hright).2 hratio
    simpa only [singleClaimGap, u₁, u₂] using hsquare

/-- At `g = λ₀`, the `L¹` portfolio gap is exactly constant away from capture. -/
theorem l1PortfolioGap_at_conservation {J lambda₀ η u : ℝ}
    (hlambda : lambda₀ ≠ 1) (hη : η ≠ 0) (hu : u ≠ 0) :
    l1PortfolioGap J lambda₀ η lambda₀ u = J / ((1 - lambda₀) * η) := by
  simp only [l1PortfolioGap, sub_self, zero_add]
  field_simp [sub_ne_zero.mpr hlambda, hη, hu]

/-- Below grounding, the `L¹` portfolio gap falls strictly with `β`. -/
theorem l1PortfolioGap_strictAntiOn_policy {J lambda₀ η g : ℝ}
    (hJ : 0 < J) (hgain : g < lambda₀) :
    StrictAntiOn (fun β ↦ l1PortfolioGap J lambda₀ η g (1 - β))
      (l1StablePolicies lambda₀ η g) := by
  intro β₁ hβ₁ β₂ hβ₂ hβ
  let u₁ : ℝ := 1 - β₁
  let u₂ : ℝ := 1 - β₂
  have huOrder : u₂ < u₁ := by dsimp only [u₁, u₂]; linarith
  have hden₁ : 0 < lambda₀ - g + (1 - lambda₀) * η * u₁ := by
    exact hβ₁.2
  have hden₂ : 0 < lambda₀ - g + (1 - lambda₀) * η * u₂ := by
    exact hβ₂.2
  simp only [l1PortfolioGap]
  apply (div_lt_div_iff₀ hden₂ hden₁).2
  nlinarith [mul_pos (mul_pos hJ (sub_pos.mpr hgain)) (sub_pos.mpr huOrder)]

/-- Above grounding, the finite part of the `L¹` gap instead rises with `β`. -/
theorem l1PortfolioGap_strictMonoOn_policy {J lambda₀ η g : ℝ}
    (hJ : 0 < J) (hgain : lambda₀ < g) :
    StrictMonoOn (fun β ↦ l1PortfolioGap J lambda₀ η g (1 - β))
      (l1StablePolicies lambda₀ η g) := by
  intro β₁ hβ₁ β₂ hβ₂ hβ
  let u₁ : ℝ := 1 - β₁
  let u₂ : ℝ := 1 - β₂
  have huOrder : u₂ < u₁ := by dsimp only [u₁, u₂]; linarith
  have hden₁ : 0 < lambda₀ - g + (1 - lambda₀) * η * u₁ := hβ₁.2
  have hden₂ : 0 < lambda₀ - g + (1 - lambda₀) * η * u₂ := hβ₂.2
  simp only [l1PortfolioGap]
  apply (div_lt_div_iff₀ hden₁ hden₂).2
  nlinarith [mul_pos (mul_pos hJ (sub_pos.mpr hgain)) (sub_pos.mpr huOrder)]

/-- On the stable region, the `L²` derivative has exactly the paper's bracket sign. -/
theorem l2PortfolioGap_deriv_pos_iff {I lambda₀ η g u : ℝ}
    (hI : 0 < I) (hu : 0 < u)
    (hdenominator : 1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g ≠ 0) :
    0 < deriv (l2PortfolioGap I lambda₀ η g) u ↔
      0 < lambda₀ + η * u * (1 - lambda₀) - g := by
  rw [(hasDerivAt_l2PortfolioGap hdenominator).deriv]
  have hdenSquare : 0 < (1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g) ^ 2 :=
    sq_pos_of_ne_zero hdenominator
  have hfactor : 0 < 2 * I * u /
      (1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g) ^ 2 :=
    div_pos (mul_pos (mul_pos (by norm_num) hI) hu) hdenSquare
  have hrearrange :
      2 * I * u * (lambda₀ + η * u * (1 - lambda₀) - g) /
          (1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g) ^ 2 =
        (2 * I * u /
          (1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g) ^ 2) *
            (lambda₀ + η * u * (1 - lambda₀) - g) := by ring
  rw [hrearrange, mul_pos_iff_of_pos_left hfactor]

/-- The `L²` derivative vanishes at exactly one possible residual weight. -/
theorem l2PortfolioGap_deriv_eq_zero_iff {I lambda₀ η g u : ℝ}
    (hI : 0 < I) (hu : 0 < u)
    (hdenominator : 1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g ≠ 0) :
    deriv (l2PortfolioGap I lambda₀ η g) u = 0 ↔
      lambda₀ + η * u * (1 - lambda₀) - g = 0 := by
  rw [(hasDerivAt_l2PortfolioGap hdenominator).deriv]
  have hdenSquare : 0 < (1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g) ^ 2 :=
    sq_pos_of_ne_zero hdenominator
  have hfactor : 0 < 2 * I * u /
      (1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g) ^ 2 :=
    div_pos (mul_pos (mul_pos (by norm_num) hI) hu) hdenSquare
  have hrearrange :
      2 * I * u * (lambda₀ + η * u * (1 - lambda₀) - g) /
          (1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g) ^ 2 =
        (2 * I * u /
          (1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g) ^ 2) *
            (lambda₀ + η * u * (1 - lambda₀) - g) := by ring
  rw [hrearrange, mul_eq_zero]
  simp only [hfactor.ne', false_or]

/-- Thus the quadratic portfolio gap cannot be flat on any nontrivial stable interval. -/
theorem l2PortfolioGap_deriv_not_zero_at_two_points {I lambda₀ η g u₁ u₂ : ℝ}
    (hI : 0 < I) (hη : 0 < η) (hlambda : lambda₀ < 1)
    (hu₁ : 0 < u₁) (hu₂ : 0 < u₂) (hne : u₁ ≠ u₂)
    (hden₁ : 1 - (1 - lambda₀) * (1 - η * u₁) ^ 2 - g ≠ 0)
    (hden₂ : 1 - (1 - lambda₀) * (1 - η * u₂) ^ 2 - g ≠ 0) :
    ¬ (deriv (l2PortfolioGap I lambda₀ η g) u₁ = 0 ∧
      deriv (l2PortfolioGap I lambda₀ η g) u₂ = 0) := by
  intro hzero
  have hbracket₁ := (l2PortfolioGap_deriv_eq_zero_iff hI hu₁ hden₁).1 hzero.1
  have hbracket₂ := (l2PortfolioGap_deriv_eq_zero_iff hI hu₂ hden₂).1 hzero.2
  have hslope : 0 < η * (1 - lambda₀) := mul_pos hη (sub_pos.mpr hlambda)
  apply hne
  nlinarith

/-- At and below grounding, the quadratic gap's derivative in `u` is positive. -/
theorem l2PortfolioGap_deriv_pos_of_gain_le {I lambda₀ η g u : ℝ}
    (hI : 0 < I) (hη : 0 < η) (hlambda : lambda₀ < 1)
    (hu : 0 < u) (hgain : g ≤ lambda₀)
    (hdenominator : 1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g ≠ 0) :
    0 < deriv (l2PortfolioGap I lambda₀ η g) u := by
  apply (l2PortfolioGap_deriv_pos_iff hI hu hdenominator).2
  have hpositive := mul_pos (mul_pos hη hu) (sub_pos.mpr hlambda)
  nlinarith

/-- For `g ≤ λ₀`, the finite quadratic portfolio gap falls strictly with `β`. -/
theorem l2PortfolioGap_strictAntiOn_policy {I lambda₀ η g : ℝ}
    (hI : 0 < I) (hη : 0 < η) (hlambda : lambda₀ < 1)
    (hgain : g ≤ lambda₀) :
    StrictAntiOn (fun β ↦ l2PortfolioGap I lambda₀ η g (1 - β))
      (l2StablePolicies lambda₀ η g) := by
  intro β₁ hβ₁ β₂ hβ₂ hβ
  let u₁ : ℝ := 1 - β₁
  let u₂ : ℝ := 1 - β₂
  have huOrder : u₂ < u₁ := by dsimp only [u₁, u₂]; linarith
  have hu₁nonneg : 0 ≤ u₁ := by dsimp only [u₁]; linarith [hβ₁.1.2]
  have hu₂nonneg : 0 ≤ u₂ := by dsimp only [u₂]; linarith [hβ₂.1.2]
  have hu₁pos : 0 < u₁ := hu₂nonneg.trans_lt huOrder
  have hden₁ : 0 < 1 - (1 - lambda₀) * (1 - η * u₁) ^ 2 - g := hβ₁.2
  have hden₂ : 0 < 1 - (1 - lambda₀) * (1 - η * u₂) ^ 2 - g := hβ₂.2
  have hbracket : 0 <
      (lambda₀ - g) * (u₁ + u₂) +
        2 * (1 - lambda₀) * η * u₁ * u₂ := by
    rcases hgain.eq_or_lt with hgainEq | hgainLt
    · have hu₂ne : u₂ ≠ 0 := by
        intro hu₂zero
        have hzero : 1 - (1 - lambda₀) * (1 - η * u₂) ^ 2 - g = 0 := by
          rw [← hgainEq, hu₂zero]
          ring
        linarith
      have hu₂pos : 0 < u₂ := lt_of_le_of_ne hu₂nonneg (Ne.symm hu₂ne)
      have hterm : 0 < 2 * (1 - lambda₀) * η * u₁ * u₂ := by positivity
      rw [hgainEq]
      simpa only [sub_self, zero_mul, zero_add, mul_assoc] using hterm
    · have hfirst := mul_pos (sub_pos.mpr hgainLt)
        (add_pos_of_pos_of_nonneg hu₁pos hu₂nonneg)
      have hsecond : 0 ≤ 2 * (1 - lambda₀) * η * u₁ * u₂ :=
        mul_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
            (sub_pos.mpr hlambda).le) hη.le) hu₁nonneg) hu₂nonneg
      linarith
  simp only [l2PortfolioGap]
  apply (div_lt_div_iff₀ hden₂ hden₁).2
  nlinarith [mul_pos (mul_pos hI (sub_pos.mpr huOrder)) hbracket]

/--
In the intermediate gain band, `u_c` is interior, stable, and the unique
global minimum throughout the finite-stock region.
-/
theorem l2CriticalResidual_unique_minimum {I lambda₀ η g : ℝ}
    (hI : 0 < I) (hη : 0 < η) (hηlt : η < 1) (hlambda : lambda₀ < 1)
    (hgainLower : lambda₀ < g)
    (hgainUpper : g < lambda₀ + η * (1 - lambda₀)) :
    l2CriticalResidual lambda₀ η g ∈ Ioo (0 : ℝ) 1 ∧
    0 < 1 - (1 - lambda₀) *
      (1 - η * l2CriticalResidual lambda₀ η g) ^ 2 - g ∧
    ∀ u, 0 < 1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g →
      l2PortfolioGap I lambda₀ η g (l2CriticalResidual lambda₀ η g) ≤
        l2PortfolioGap I lambda₀ η g u ∧
      (l2PortfolioGap I lambda₀ η g (l2CriticalResidual lambda₀ η g) =
        l2PortfolioGap I lambda₀ η g u ↔
          u = l2CriticalResidual lambda₀ η g) := by
  let uCritical : ℝ := l2CriticalResidual lambda₀ η g
  have hslope : 0 < η * (1 - lambda₀) := mul_pos hη (sub_pos.mpr hlambda)
  have huCriticalPos : 0 < uCritical := by
    dsimp only [uCritical, l2CriticalResidual]
    exact div_pos (sub_pos.mpr hgainLower) hslope
  have huCriticalLt : uCritical < 1 := by
    apply (div_lt_one hslope).2
    linarith
  have hcriticalRelation : η * (1 - lambda₀) * uCritical = g - lambda₀ := by
    dsimp only [uCritical, l2CriticalResidual]
    field_simp [hslope.ne', (sub_pos.mpr hlambda).ne']
  have hηuCriticalLt : η * uCritical < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left hη.le hηlt huCriticalLt.le
  have hcriticalIdentity :
      1 - (1 - lambda₀) * (1 - η * uCritical) ^ 2 - g =
        (1 - lambda₀) * η * uCritical * (1 - η * uCritical) := by
    linear_combination hcriticalRelation
  have hcriticalDenominator :
      0 < 1 - (1 - lambda₀) * (1 - η * uCritical) ^ 2 - g := by
    rw [hcriticalIdentity]
    exact mul_pos
      (mul_pos (mul_pos (sub_pos.mpr hlambda) hη) huCriticalPos)
      (sub_pos.mpr hηuCriticalLt)
  refine ⟨⟨huCriticalPos, huCriticalLt⟩, hcriticalDenominator, ?_⟩
  intro u huDenominator
  have hcrossIdentity :
      u ^ 2 * I *
          (1 - (1 - lambda₀) * (1 - η * uCritical) ^ 2 - g) -
        uCritical ^ 2 * I *
          (1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g) =
      I * (1 - lambda₀) * η * uCritical * (u - uCritical) ^ 2 := by
    linear_combination I * (u - uCritical) * (u + uCritical) * hcriticalRelation
  have hfactor : 0 < I * (1 - lambda₀) * η * uCritical :=
    mul_pos (mul_pos (mul_pos hI (sub_pos.mpr hlambda)) hη) huCriticalPos
  have hcross :
      uCritical ^ 2 * I *
          (1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g) ≤
        u ^ 2 * I *
          (1 - (1 - lambda₀) * (1 - η * uCritical) ^ 2 - g) := by
    nlinarith [mul_nonneg hfactor.le (sq_nonneg (u - uCritical))]
  constructor
  · simp only [l2PortfolioGap]
    exact (div_le_div_iff₀ hcriticalDenominator huDenominator).2 hcross
  · constructor
    · intro hequal
      have hcrossEqual :
          uCritical ^ 2 * I *
              (1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g) =
            u ^ 2 * I *
              (1 - (1 - lambda₀) * (1 - η * uCritical) ^ 2 - g) := by
        apply (div_eq_div_iff hcriticalDenominator.ne' huDenominator.ne').1
        simpa only [l2PortfolioGap] using hequal
      have hsquare : (u - uCritical) ^ 2 = 0 := by
        have hproduct : I * (1 - lambda₀) * η * uCritical *
            (u - uCritical) ^ 2 = 0 := by
          nlinarith [hcrossIdentity]
        exact (mul_eq_zero.mp hproduct).resolve_left hfactor.ne'
      nlinarith [sq_nonneg (u - uCritical)]
    · intro hequal
      subst u
      rfl

/-! ## The paper theorem -/

/-- The full collection of conclusions in Paper III's aggregation--conservation table. -/
structure AggregationConservationMap
    (injection J I lambda₀ η : ℝ) : Prop where
  single_fixed : ∀ {ζ u : ℝ}, η * u - ζ ≠ 0 →
    (1 - η * u + ζ) * singleClaimStationary injection η ζ u + injection =
      singleClaimStationary injection η ζ u
  single_formula : ∀ {p : ℕ} {ζ u : ℝ}, 0 < η * u - ζ →
    (u * |singleClaimStationary injection η ζ u|) ^ p =
      singleClaimGap p injection η ζ u
  single_conserved : ∀ {p : ℕ}, (p = 1 ∨ p = 2) → ∀ {u : ℝ}, 0 < u →
    singleClaimGap p injection η 0 u = (|injection| / η) ^ p
  single_feedback_rises : ∀ {p : ℕ}, (p = 1 ∨ p = 2) → ∀ {ζ : ℝ}, 0 < ζ →
    StrictMonoOn (fun β ↦ singleClaimGap p injection η ζ (1 - β))
      (singleClaimStablePolicies η ζ)
  l1_fixed : ∀ {g u : ℝ}, lambda₀ - g + (1 - lambda₀) * η * u ≠ 0 →
    ((1 - lambda₀) * (1 - η * u) + g) *
        l1PortfolioStationary J lambda₀ η g u + J =
      l1PortfolioStationary J lambda₀ η g u
  l1_formula : ∀ {g u : ℝ},
    u * l1PortfolioStationary J lambda₀ η g u =
      l1PortfolioGap J lambda₀ η g u
  l1_conserved : ∀ {u : ℝ}, 0 < u →
    l1PortfolioGap J lambda₀ η lambda₀ u = J / ((1 - lambda₀) * η)
  l1_below_falls : ∀ {g : ℝ}, g < lambda₀ →
    StrictAntiOn (fun β ↦ l1PortfolioGap J lambda₀ η g (1 - β))
      (l1StablePolicies lambda₀ η g)
  l1_above_rises : ∀ {g : ℝ}, lambda₀ < g →
    StrictMonoOn (fun β ↦ l1PortfolioGap J lambda₀ η g (1 - β))
      (l1StablePolicies lambda₀ η g)
  l2_fixed : ∀ {g u : ℝ},
    1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g ≠ 0 →
    ((1 - lambda₀) * (1 - η * u) ^ 2 + g) *
        l2PortfolioStationary I lambda₀ η g u + I =
      l2PortfolioStationary I lambda₀ η g u
  l2_formula : ∀ {g u : ℝ},
    u ^ 2 * l2PortfolioStationary I lambda₀ η g u =
      l2PortfolioGap I lambda₀ η g u
  l2_derivative : ∀ {g u : ℝ},
    1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g ≠ 0 →
    HasDerivAt (l2PortfolioGap I lambda₀ η g)
      (2 * I * u * (lambda₀ + η * u * (1 - lambda₀) - g) /
        (1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g) ^ 2) u
  l2_never_flat : ∀ {g u₁ u₂ : ℝ}, 0 < u₁ → 0 < u₂ → u₁ ≠ u₂ →
    1 - (1 - lambda₀) * (1 - η * u₁) ^ 2 - g ≠ 0 →
    1 - (1 - lambda₀) * (1 - η * u₂) ^ 2 - g ≠ 0 →
    ¬ (deriv (l2PortfolioGap I lambda₀ η g) u₁ = 0 ∧
      deriv (l2PortfolioGap I lambda₀ η g) u₂ = 0)
  l2_below_falls : ∀ {g : ℝ}, g ≤ lambda₀ →
    StrictAntiOn (fun β ↦ l2PortfolioGap I lambda₀ η g (1 - β))
      (l2StablePolicies lambda₀ η g)
  l2_interior_minimum : ∀ {g : ℝ}, lambda₀ < g →
    g < lambda₀ + η * (1 - lambda₀) →
    l2CriticalResidual lambda₀ η g ∈ Ioo (0 : ℝ) 1 ∧
    0 < 1 - (1 - lambda₀) *
      (1 - η * l2CriticalResidual lambda₀ η g) ^ 2 - g ∧
    ∀ u, 0 < 1 - (1 - lambda₀) * (1 - η * u) ^ 2 - g →
      l2PortfolioGap I lambda₀ η g (l2CriticalResidual lambda₀ η g) ≤
        l2PortfolioGap I lambda₀ η g u ∧
      (l2PortfolioGap I lambda₀ η g (l2CriticalResidual lambda₀ η g) =
        l2PortfolioGap I lambda₀ η g u ↔
          u = l2CriticalResidual lambda₀ η g)

/--
Paper III, Theorem 3.1 (`thm:conservation`), civic_loops.tex:184. All stationary
forms, both conservation loci, all monotonicity claims, the quadratic sign
formula, and the unique interior minimum are included.
-/
theorem aggregationConservation {injection J I lambda₀ η : ℝ}
    (hinjection : injection ≠ 0) (hJ : 0 < J) (hI : 0 < I)
    (hη : η ∈ Ioo (0 : ℝ) 1) (hlambda : lambda₀ ∈ Ioo (0 : ℝ) 1) :
    AggregationConservationMap injection J I lambda₀ η := by
  refine {
    single_fixed := fun hdenominator ↦ singleClaimStationary_fixed hdenominator
    single_formula := fun hdenominator ↦ singleClaimGap_eq_measuredStationary hdenominator
    single_conserved := ?_
    single_feedback_rises := ?_
    l1_fixed := fun hdenominator ↦ l1PortfolioStationary_fixed hdenominator
    l1_formula := l1PortfolioGap_eq_measuredStationary
    l1_conserved := ?_
    l1_below_falls := ?_
    l1_above_rises := ?_
    l2_fixed := fun hdenominator ↦ l2PortfolioStationary_fixed hdenominator
    l2_formula := l2PortfolioGap_eq_measuredStationary
    l2_derivative := fun hdenominator ↦ hasDerivAt_l2PortfolioGap hdenominator
    l2_never_flat := ?_
    l2_below_falls := ?_
    l2_interior_minimum := ?_ }
  · intro p hp u hu
    exact singleClaimGap_noFeedback hη.1.ne' hu.ne'
  · intro p hp ζ hζ
    exact singleClaimGap_strictMonoOn_policy hp hinjection hη.1 hζ
  · intro u hu
    exact l1PortfolioGap_at_conservation (ne_of_lt hlambda.2) hη.1.ne' hu.ne'
  · intro g hg
    exact l1PortfolioGap_strictAntiOn_policy hJ hg
  · intro g hg
    exact l1PortfolioGap_strictMonoOn_policy hJ hg
  · intro g u₁ u₂ hu₁ hu₂ hne hden₁ hden₂
    exact l2PortfolioGap_deriv_not_zero_at_two_points
      hI hη.1 hlambda.2 hu₁ hu₂ hne hden₁ hden₂
  · intro g hg
    exact l2PortfolioGap_strictAntiOn_policy hI hη.1 hlambda.2 hg
  · intro g hgLower hgUpper
    exact l2CriticalResidual_unique_minimum
      hI hη.1 hη.2 hlambda.2 hgLower hgUpper

#print axioms singleClaimStationary_fixed
#print axioms singleClaimGap_eq_measuredStationary
#print axioms l1PortfolioStationary_fixed
#print axioms l1PortfolioGap_eq_measuredStationary
#print axioms l2PortfolioStationary_fixed
#print axioms l2PortfolioGap_eq_measuredStationary
#print axioms hasDerivAt_singleClaimRatio
#print axioms hasDerivAt_l1PortfolioGap
#print axioms hasDerivAt_l2PortfolioGap
#print axioms singleClaimGap_noFeedback
#print axioms singleClaimGap_strictMonoOn_policy
#print axioms l1PortfolioGap_at_conservation
#print axioms l1PortfolioGap_strictAntiOn_policy
#print axioms l1PortfolioGap_strictMonoOn_policy
#print axioms l2PortfolioGap_deriv_pos_iff
#print axioms l2PortfolioGap_deriv_eq_zero_iff
#print axioms l2PortfolioGap_deriv_not_zero_at_two_points
#print axioms l2PortfolioGap_deriv_pos_of_gain_le
#print axioms l2PortfolioGap_strictAntiOn_policy
#print axioms l2CriticalResidual_unique_minimum
#print axioms aggregationConservation

end CivicAlignment.PaperIII
