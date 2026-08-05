/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.Basic

/-!
# Papers II--III: the projection calculus (`lem:clip`)

`Π_J` is part of the model rather than a technical device: deference is bounded
and full deference is attainable.  The consequences used at every boundary in
Papers II and III are proved here once, for a general compact interval, and
specialized to the policy clip `Π_[0,1]` of `eq:map` and to the belief bound
`Π_[-x̄, x̄]` of `cor:sat`.

The four clauses are order and `1`-Lipschitz transfer; the deadzone --- a strict
inequality survives only where the projection is inactive, and a raw rate
`1 - k` toward a face becomes `max {0, 1 - k}`; face absorption under a
uniformly outward raw drive; and non-injectivity.
-/

namespace CivicAlignment

open Set

noncomputable section

/-- Projection onto a compact interval, the papers' `Π_J`. -/
def clipTo (lo hi x : ℝ) : ℝ := max lo (min hi x)

/-- The policy clip of `eq:map` is the unit-interval case. -/
theorem clipUnit_eq_clipTo (x : ℝ) : LoopParams.clipUnit x = clipTo 0 1 x := by
  simp only [LoopParams.clipUnit, clipTo, Set.coe_projIcc]

variable {lo hi : ℝ}

/-! ### Basic behaviour -/

/-- The projection lands in its interval. -/
theorem clipTo_mem (hle : lo ≤ hi) (x : ℝ) : clipTo lo hi x ∈ Icc lo hi :=
  ⟨le_max_left _ _, max_le hle (min_le_left _ _)⟩

/-- Where the projection is inactive it is the identity. -/
theorem clipTo_eq_self {x : ℝ} (hx : x ∈ Icc lo hi) : clipTo lo hi x = x := by
  simp only [clipTo, min_eq_right hx.2, max_eq_right hx.1]

/-- Above the upper endpoint the projection is constant. -/
theorem clipTo_eq_hi (hle : lo ≤ hi) {x : ℝ} (hx : hi ≤ x) :
    clipTo lo hi x = hi := by
  simp only [clipTo, min_eq_left hx, max_eq_right hle]

/-- Below the lower endpoint the projection is constant. -/
theorem clipTo_eq_lo {x : ℝ} (hx : x ≤ lo) : clipTo lo hi x = lo := by
  simp only [clipTo, max_eq_left (min_le_of_right_le hx)]

/-! ### Clause (i): order and `1`-Lipschitz transfer -/

/-- `Π_J` is order-preserving, so it transfers monotonicity of any raw update. -/
theorem monotone_clipTo : Monotone (clipTo lo hi) := fun _ _ hxy =>
  max_le_max le_rfl (min_le_min le_rfl hxy)

/-- `Π_J` is continuous, so it transfers continuity of any raw update. -/
theorem continuous_clipTo : Continuous (clipTo lo hi) :=
  continuous_const.max (continuous_const.min continuous_id)

/-- `Π_J` contracts differences: it is `1`-Lipschitz. -/
theorem clipTo_dist_le (x y : ℝ) :
    |clipTo lo hi x - clipTo lo hi y| ≤ |x - y| := by
  rcases le_total x y with hxy | hxy
  · have hmono := monotone_clipTo (lo := lo) (hi := hi) hxy
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    simp only [clipTo, max_def, min_def] at hmono ⊢
    split_ifs at hmono ⊢ <;> linarith
  · have hmono := monotone_clipTo (lo := lo) (hi := hi) hxy
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    simp only [clipTo, max_def, min_def] at hmono ⊢
    split_ifs at hmono ⊢ <;> linarith

/-! ### Clause (ii): the deadzone -/

/--
A strict inequality between raw values survives the projection exactly where the
projection is inactive.
-/
theorem clipTo_lt_clipTo_iff_of_mem {x y : ℝ}
    (hx : x ∈ Icc lo hi) (hy : y ∈ Icc lo hi) :
    clipTo lo hi x < clipTo lo hi y ↔ x < y := by
  rw [clipTo_eq_self hx, clipTo_eq_self hy]

/-- The projection hits the lower endpoint exactly on inputs at or below it. -/
theorem clipTo_eq_lo_iff (hlt : lo < hi) (x : ℝ) :
    clipTo lo hi x = lo ↔ x ≤ lo := by
  refine ⟨fun h => ?_, clipTo_eq_lo⟩
  have hmin : min hi x ≤ lo := by
    rw [← h]; exact le_max_right _ _
  rcases min_le_iff.mp hmin with hfalse | hx
  · exact absurd hfalse (not_le.mpr hlt)
  · exact hx

/-- The projection hits the upper endpoint exactly on inputs at or above it. -/
theorem clipTo_eq_hi_iff (hlt : lo < hi) (x : ℝ) :
    clipTo lo hi x = hi ↔ hi ≤ x := by
  refine ⟨fun h => ?_, clipTo_eq_hi hlt.le⟩
  rcases max_cases lo (min hi x) with ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [clipTo, heq] at h; exact absurd h hlt.ne
  · rw [clipTo, heq] at h; exact min_eq_left_iff.mp h

/--
An interior output of the projection has that output as its unique preimage: the
deadzone is confined to the two faces.
-/
theorem clipTo_eq_interior_iff {x β : ℝ} (hβ : β ∈ Ioo lo hi) :
    clipTo lo hi x = β ↔ x = β := by
  constructor
  · intro h
    by_cases hxlo : x ≤ lo
    · rw [clipTo_eq_lo hxlo] at h
      exact absurd h hβ.1.ne
    by_cases hxhi : hi ≤ x
    · rw [clipTo_eq_hi (hβ.1.trans hβ.2).le hxhi] at h
      exact absurd h hβ.2.ne'
    · rwa [clipTo_eq_self ⟨(not_le.mp hxlo).le, (not_le.mp hxhi).le⟩] at h
  · rintro rfl
    exact clipTo_eq_self ⟨hβ.1.le, hβ.2.le⟩

/-- Projecting a value strictly below an interior point stays strictly below it. -/
theorem clipTo_lt_of_lt {x β : ℝ} (hx : x < β) (hlo : lo < β) :
    clipTo lo hi x < β :=
  max_lt hlo ((min_le_right _ _).trans_lt hx)

/-- Projecting a value strictly above a sub-face point stays strictly above it. -/
theorem lt_clipTo {x β : ℝ} (hx : β < x) (hhi : β < hi) :
    β < clipTo lo hi x :=
  (lt_min hhi hx).trans_le (le_max_right _ _)

/-- A projected value above the lower endpoint never exceeds its input. -/
theorem clipTo_le_input {z : ℝ} (hpos : lo < clipTo lo hi z) :
    clipTo lo hi z ≤ z := by
  rcases max_cases lo (min hi z) with ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [clipTo, heq] at hpos; exact absurd hpos (lt_irrefl lo)
  · rw [clipTo, heq]; exact min_le_right _ _

/-- The clipped residual never exceeds the truncated raw residual. -/
theorem hi_sub_clipTo_le (x : ℝ) :
    hi - clipTo lo hi x ≤ max 0 (hi - x) := by
  simp only [clipTo, max_def, min_def]
  split_ifs <;> linarith

/--
The rate clause of `lem:clip`(ii).  A raw contraction factor `1 - k` toward the
upper face becomes `max {0, 1 - k}` after projection, which is the valid factor
for *every* `k` --- including `k > 1`, where the raw factor is negative while the
clipped residual is not.
-/
theorem clipTo_rate {z x k : ℝ} (hz : z ≤ hi)
    (hraw : hi - x ≤ (hi - z) * (1 - k)) :
    hi - clipTo lo hi x ≤ (hi - z) * max 0 (1 - k) := by
  have hgap : (0 : ℝ) ≤ hi - z := by linarith
  have hmax : (hi - z) * max 0 (1 - k) = max 0 ((hi - z) * (1 - k)) := by
    rw [mul_max_of_nonneg _ _ hgap, mul_zero]
  calc hi - clipTo lo hi x ≤ max 0 (hi - x) := hi_sub_clipTo_le x
    _ ≤ max 0 ((hi - z) * (1 - k)) := max_le_max le_rfl hraw
    _ = (hi - z) * max 0 (1 - k) := hmax.symm

/-! ### Clause (iii): face absorption -/

/-- An outward raw drive at the upper face makes that face invariant. -/
theorem clipTo_face_fixed (hle : lo ≤ hi) {f : ℝ → ℝ} (hf : hi ≤ f hi) :
    clipTo lo hi (f hi) = hi :=
  clipTo_eq_hi hle hf

/-- The upper face is invariant for the whole clipped orbit. -/
theorem clipTo_iterate_face (hle : lo ≤ hi) {f : ℝ → ℝ} (hf : hi ≤ f hi) (n : ℕ) :
    (fun z => clipTo lo hi (f z))^[n] hi = hi := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      exact clipTo_face_fixed hle hf

/-- A uniformly outward raw drive advances the clipped orbit by at least `δ`. -/
theorem clipTo_orbit_lower_bound (hle : lo ≤ hi) {f : ℝ → ℝ} {δ z₀ : ℝ}
    (hδ : 0 < δ) (hz₀ : z₀ ∈ Icc lo hi)
    (hdrive : ∀ z ∈ Icc lo hi, z + δ ≤ f z) (n : ℕ) :
    min hi (z₀ + n * δ) ≤ (fun z => clipTo lo hi (f z))^[n] z₀ := by
  set T : ℝ → ℝ := fun z => clipTo lo hi (f z) with hT
  have hmem : ∀ m : ℕ, T^[m] z₀ ∈ Icc lo hi := by
    intro m
    cases m with
    | zero => simpa only [Function.iterate_zero_apply] using hz₀
    | succ m =>
        rw [Function.iterate_succ_apply']
        exact clipTo_mem hle _
  induction n with
  | zero =>
      rw [Function.iterate_zero_apply]
      simpa only [Nat.cast_zero, zero_mul, add_zero] using min_le_right hi z₀
  | succ n ih =>
      have hcur := hmem n
      have hstep : T^[n] z₀ + δ ≤ f (T^[n] z₀) := hdrive _ hcur
      have hchain : min hi (z₀ + n * δ) + δ ≤ f (T^[n] z₀) := by linarith
      have hclip : min hi (f (T^[n] z₀)) ≤ T^[n + 1] z₀ := by
        rw [Function.iterate_succ_apply', hT]
        exact le_max_right _ _
      refine le_trans ?_ hclip
      refine le_min (min_le_left _ _) ?_
      push_cast
      rcases le_total (z₀ + n * δ) hi with hcase | hcase
      · rw [min_eq_right hcase] at hchain
        calc min hi (z₀ + ((n : ℝ) + 1) * δ) ≤ z₀ + ((n : ℝ) + 1) * δ :=
              min_le_right _ _
          _ = z₀ + n * δ + δ := by ring
          _ ≤ f (T^[n] z₀) := hchain
      · rw [min_eq_left hcase] at hchain
        calc min hi (z₀ + ((n : ℝ) + 1) * δ) ≤ hi := min_le_left _ _
          _ ≤ hi + δ := by linarith
          _ ≤ f (T^[n] z₀) := hchain

/--
Clause (iii) of `lem:clip`: under a uniformly outward raw drive the upper face is
attained in finitely many steps, and is invariant thereafter.
-/
theorem clipTo_reaches_face (hle : lo ≤ hi) {f : ℝ → ℝ} {δ z₀ : ℝ} (hδ : 0 < δ)
    (hz₀ : z₀ ∈ Icc lo hi) (hdrive : ∀ z ∈ Icc lo hi, z + δ ≤ f z) :
    ∃ N : ℕ, ∀ n ≥ N, (fun z => clipTo lo hi (f z))^[n] z₀ = hi := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((hi - z₀) / δ)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hmem : (fun z => clipTo lo hi (f z))^[n] z₀ ∈ Icc lo hi := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Function.iterate_succ_apply']
    exact clipTo_mem hle _
  have hbound := clipTo_orbit_lower_bound hle hδ hz₀ hdrive n
  have hge : hi ≤ z₀ + n * δ := by
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : N ≤ n)
    have hNlt : (hi - z₀) / δ < (n : ℝ) := by linarith
    have := (div_lt_iff₀ hδ).1 hNlt
    linarith
  rw [min_eq_left hge] at hbound
  exact le_antisymm hmem.2 hbound

/-! ### Clause (iv): non-injectivity -/

/-- `Π_J` is not injective on a nondegenerate interval. -/
theorem clipTo_not_injective (hlt : lo < hi) :
    ¬ Function.Injective (clipTo lo hi) := by
  intro hinj
  have h₁ : clipTo lo hi hi = hi := clipTo_eq_hi hlt.le le_rfl
  have h₂ : clipTo lo hi (hi + 1) = hi := clipTo_eq_hi hlt.le (by linarith)
  have := hinj (h₁.trans h₂.symm)
  linarith

/--
Clause (iv) of `lem:clip`: the projection identifies any two states whose raw
updates overshoot the same endpoint, so the composite is not injective as soon as
the raw update leaves the interval at two distinct arguments on one side --- which
is what the loop map does, every raw policy input at or above one being sent to
one.  Injectivity, and with it the orientation hypothesis of the convergence
theory of unclipped planar cooperative maps, is therefore unavailable.

The hypothesis that the raw update overshoots at *two* arguments is not
removable: a raw update leaving the interval at a single argument can compose
with the projection injectively.
-/
theorem clipTo_comp_not_injective (hle : lo ≤ hi) {α : Type*} {f : α → ℝ}
    {x₁ x₂ : α} (hne : x₁ ≠ x₂) (h₁ : hi ≤ f x₁) (h₂ : hi ≤ f x₂) :
    ¬ Function.Injective (clipTo lo hi ∘ f) := fun hinj =>
  hne (hinj (by
    simp only [Function.comp_apply, clipTo_eq_hi hle h₁, clipTo_eq_hi hle h₂]))

/-! ## Specialization to the policy clip `Π_[0,1]` -/

/-- The policy clip is order-preserving (`lem:clip`(i)). -/
theorem monotone_clipUnit' : Monotone LoopParams.clipUnit := by
  intro x y hxy
  simp only [clipUnit_eq_clipTo]
  exact monotone_clipTo hxy

/-- The policy clip is `1`-Lipschitz (`lem:clip`(i)). -/
theorem clipUnit_dist_le (x y : ℝ) :
    |LoopParams.clipUnit x - LoopParams.clipUnit y| ≤ |x - y| := by
  simp only [clipUnit_eq_clipTo]
  exact clipTo_dist_le x y

/-- Where inactive, the policy clip is the identity (`lem:clip`(ii)). -/
theorem clipUnit_eq_self' {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    LoopParams.clipUnit x = x := by
  simp only [clipUnit_eq_clipTo]
  exact clipTo_eq_self hx

/-- The captured face absorbs every raw policy input at or above one. -/
theorem clipUnit_eq_one_of_le {x : ℝ} (hx : (1 : ℝ) ≤ x) :
    LoopParams.clipUnit x = 1 := by
  simp only [clipUnit_eq_clipTo]
  exact clipTo_eq_hi zero_le_one hx

/-- The calibrated face absorbs every raw policy input at or below zero. -/
theorem clipUnit_eq_zero_of_le {x : ℝ} (hx : x ≤ 0) :
    LoopParams.clipUnit x = 0 := by
  simp only [clipUnit_eq_clipTo]
  exact clipTo_eq_lo hx

/--
The rate clause at the captured face (`lem:clip`(ii)), as used by
`thm:launder`(i): a raw contraction factor `1 - k` on `1 - β` becomes
`max {0, 1 - k}` after projection.
-/
theorem clipUnit_rate {β x k : ℝ} (hβ : β ≤ 1)
    (hraw : 1 - x ≤ (1 - β) * (1 - k)) :
    1 - LoopParams.clipUnit x ≤ (1 - β) * max 0 (1 - k) := by
  simp only [clipUnit_eq_clipTo]
  exact clipTo_rate (lo := (0 : ℝ)) hβ hraw

/-! ## The packaged lemma -/

/--
Paper II, Lemma `lem:clip` (`civic_drift.tex:179`), all four clauses for a
general compact interval: order and `1`-Lipschitz transfer; the deadzone, with
the identity where inactive and the truncated rate `max {0, 1 - k}` at the face;
face absorption under a uniformly outward raw drive, attained in finitely many
steps and invariant thereafter; and non-injectivity of the projection on a
nondegenerate interval.
-/
theorem clippedStep (hle : lo ≤ hi) :
    Monotone (clipTo lo hi) ∧
    (∀ x y : ℝ, |clipTo lo hi x - clipTo lo hi y| ≤ |x - y|) ∧
    (∀ x ∈ Icc lo hi, clipTo lo hi x = x) ∧
    (∀ {z x k : ℝ}, z ≤ hi → hi - x ≤ (hi - z) * (1 - k) →
      hi - clipTo lo hi x ≤ (hi - z) * max 0 (1 - k)) ∧
    (∀ {f : ℝ → ℝ} {δ z₀ : ℝ}, 0 < δ → z₀ ∈ Icc lo hi →
      (∀ z ∈ Icc lo hi, z + δ ≤ f z) →
      ∃ N : ℕ, ∀ n ≥ N, (fun z => clipTo lo hi (f z))^[n] z₀ = hi) ∧
    (lo < hi → ¬ Function.Injective (clipTo lo hi)) :=
  ⟨monotone_clipTo, clipTo_dist_le, fun _ hx => clipTo_eq_self hx,
    fun hz hraw => clipTo_rate hz hraw,
    fun hδ hz₀ hdrive => clipTo_reaches_face hle hδ hz₀ hdrive,
    fun hlt => clipTo_not_injective hlt⟩

#print axioms clipUnit_eq_clipTo
#print axioms clipTo_mem
#print axioms clipTo_eq_self
#print axioms clipTo_eq_hi
#print axioms clipTo_eq_lo
#print axioms monotone_clipTo
#print axioms continuous_clipTo
#print axioms clipTo_dist_le
#print axioms clipTo_lt_clipTo_iff_of_mem
#print axioms clipTo_eq_lo_iff
#print axioms clipTo_eq_hi_iff
#print axioms clipTo_eq_interior_iff
#print axioms clipTo_lt_of_lt
#print axioms lt_clipTo
#print axioms clipUnit_eq_zero_of_le
#print axioms clipTo_le_input
#print axioms hi_sub_clipTo_le
#print axioms clipTo_rate
#print axioms clipTo_face_fixed
#print axioms clipTo_iterate_face
#print axioms clipTo_orbit_lower_bound
#print axioms clipTo_reaches_face
#print axioms clipTo_not_injective
#print axioms clipTo_comp_not_injective
#print axioms monotone_clipUnit'
#print axioms clipUnit_dist_le
#print axioms clipUnit_eq_self'
#print axioms clipUnit_eq_one_of_le
#print axioms clipUnit_rate
#print axioms clippedStep

end

end CivicAlignment
