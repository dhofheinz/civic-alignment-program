/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.Burn

/-!
# Paper III: the monotonicity trichotomy of `prop:burn`(ii)

Strict monotonicity of the projected policy limit fails on the full
admissible interval `[0, 1/(2c^2))` — `Burn.lean` carries an exact rational
witness at the benchmark.  This file proves the trichotomy the paper
states: the limit exists and is non-decreasing on the whole admissible
interval, it is strictly increasing between any two excesses whose larger orbit
never clips, and it is identically one once the orbit clips.  The unclipped
excesses form an initial segment, so the plateau is an up-set; since the
critical orbit's limit is the saddle policy, strictly below one, the plateau
lies strictly above the critical excess and `prop:seplimit`'s two-sided
separation follows.
-/

namespace CivicAlignment.PaperIII

open Filter Function Set Topology

noncomputable section

/-! ## The projected jump orbit -/

/-- The orbit of the projected jump map from a rescaled initial state. -/
def projJumpOrbit (p : LoopParams) (x₀ : LoopState) (n : ℕ) : LoopState :=
  ((projectedJumpMap p)^[n]) x₀

@[simp]
theorem projJumpOrbit_zero (p : LoopParams) (x₀ : LoopState) :
    projJumpOrbit p x₀ 0 = x₀ := by
  simp [projJumpOrbit]

theorem projJumpOrbit_succ (p : LoopParams) (x₀ : LoopState) (n : ℕ) :
    projJumpOrbit p x₀ (n + 1) = projectedJumpMap p (projJumpOrbit p x₀ n) := by
  simp only [projJumpOrbit, Function.iterate_succ_apply']

/-- The projected policy coordinate always lies in the policy interval. -/
theorem projJumpOrbit_policy_mem {p : LoopParams} {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    (projJumpOrbit p x₀ n).1 ∈ Icc (0 : ℝ) 1 := by
  cases n with
  | zero => simpa only [projJumpOrbit_zero] using hx₀
  | succ n =>
      rw [projJumpOrbit_succ]
      exact LoopParams.clipUnit_mem _

/-- Nonnegative excess is preserved along a projected orbit. -/
theorem projJumpOrbit_excess_nonneg {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀) {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hE₀ : 0 ≤ x₀.2) (n : ℕ) :
    0 ≤ (projJumpOrbit p x₀ n).2 := by
  induction n with
  | zero => simpa only [projJumpOrbit_zero] using hE₀
  | succ n ih =>
      rw [projJumpOrbit_succ]
      exact mul_nonneg
        (jumpPersistence_nonneg_le_uniform model hgain
          (projJumpOrbit_policy_mem (p := p) hx₀ n)).1 ih

/-- The excess coordinate decays under the uniform geometric envelope. -/
theorem projJumpOrbit_excess_le_geometric {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀) {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hE₀ : 0 ≤ x₀.2) (n : ℕ) :
    (projJumpOrbit p x₀ n).2 ≤ x₀.2 * (1 - p.lambda₀ + p.g) ^ n := by
  have hq : 0 ≤ 1 - p.lambda₀ + p.g :=
    add_nonneg (sub_nonneg.mpr model.lambda₀_lt_one.le) model.g_nonneg
  induction n with
  | zero => simp [projJumpOrbit]
  | succ n ih =>
      rw [projJumpOrbit_succ, pow_succ]
      have hpers := jumpPersistence_nonneg_le_uniform model hgain
        (projJumpOrbit_policy_mem (p := p) hx₀ n)
      have hEn := projJumpOrbit_excess_nonneg model hgain hx₀ hE₀ n
      calc
        jumpPersistence p (projJumpOrbit p x₀ n).1 * (projJumpOrbit p x₀ n).2
            ≤ (1 - p.lambda₀ + p.g) * (projJumpOrbit p x₀ n).2 :=
          mul_le_mul_of_nonneg_right hpers.2.1 hEn
        _ ≤ (1 - p.lambda₀ + p.g) * (x₀.2 * (1 - p.lambda₀ + p.g) ^ n) :=
          mul_le_mul_of_nonneg_left ih hq
        _ = x₀.2 * ((1 - p.lambda₀ + p.g) ^ n * (1 - p.lambda₀ + p.g)) := by ring

/-- The excess of a projected orbit never exceeds its initial value. -/
theorem projJumpOrbit_excess_le_initial {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀) {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hE₀ : 0 ≤ x₀.2) (n : ℕ) :
    (projJumpOrbit p x₀ n).2 ≤ x₀.2 := by
  have hq : 0 ≤ 1 - p.lambda₀ + p.g :=
    add_nonneg (sub_nonneg.mpr model.lambda₀_lt_one.le) model.g_nonneg
  have hq1 : 1 - p.lambda₀ + p.g ≤ 1 := by linarith [model.lambda₀_pos, hgain]
  calc (projJumpOrbit p x₀ n).2 ≤ x₀.2 * (1 - p.lambda₀ + p.g) ^ n :=
        projJumpOrbit_excess_le_geometric model hgain hx₀ hE₀ n
    _ ≤ x₀.2 * 1 := by
        exact mul_le_mul_of_nonneg_left (pow_le_one₀ hq hq1) hE₀
    _ = x₀.2 := mul_one _

/-- With nonnegative excess the projected policy path is non-decreasing. -/
theorem projJumpOrbit_policy_monotone {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀) {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hE₀ : 0 ≤ x₀.2) :
    Monotone fun n ↦ (projJumpOrbit p x₀ n).1 := by
  apply monotone_nat_of_le_succ
  intro n
  have hβ := projJumpOrbit_policy_mem (p := p) hx₀ n
  have hA : 0 ≤ jumpGain p (projJumpOrbit p x₀ n).1 :=
    (jumpGain_pos_of_mem model hβ).le
  have hE := projJumpOrbit_excess_nonneg model hgain hx₀ hE₀ n
  rw [projJumpOrbit_succ]
  change (projJumpOrbit p x₀ n).1 ≤
    LoopParams.clipUnit ((projJumpOrbit p x₀ n).1 +
      jumpGain p (projJumpOrbit p x₀ n).1 * (projJumpOrbit p x₀ n).2)
  calc (projJumpOrbit p x₀ n).1
      = LoopParams.clipUnit (projJumpOrbit p x₀ n).1 :=
        (clipUnit_eq_self' hβ).symm
    _ ≤ _ := monotone_clipUnit' (le_add_of_nonneg_right (mul_nonneg hA hE))

/-- Every projected orbit has a policy limit in the unit interval. -/
theorem projJumpOrbit_policy_tendsto {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀) {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hE₀ : 0 ≤ x₀.2) :
    ∃ L ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n ↦ (projJumpOrbit p x₀ n).1) atTop (nhds L) := by
  have hmono := projJumpOrbit_policy_monotone model hgain hx₀ hE₀
  have hbdd : BddAbove (Set.range fun n ↦ (projJumpOrbit p x₀ n).1) :=
    ⟨1, by rintro y ⟨n, rfl⟩; exact (projJumpOrbit_policy_mem hx₀ n).2⟩
  refine ⟨_, ⟨?_, ?_⟩, tendsto_atTop_ciSup hmono hbdd⟩
  · exact le_ciSup_of_le hbdd 0 (by
      simpa only [projJumpOrbit_zero] using hx₀.1)
  · exact ciSup_le fun n ↦ (projJumpOrbit_policy_mem hx₀ n).2

/-! ## Order preservation in the initial excess -/

/--
The raw policy input is monotone in the state, provided the *smaller* excess
lies below the cooperativity ceiling `1/(2c^2)`.
-/
theorem rawInput_mono {p : LoopParams} (model : LoopModelAssumptions p)
    {β₁ E₁ β₂ E₂ : ℝ} (hβ₂ : β₂ ∈ Icc (0 : ℝ) 1)
    (hE₁cap : 2 * p.c ^ 2 * E₁ ≤ 1)
    (hβ : β₁ ≤ β₂) (hE : E₁ ≤ E₂) :
    β₁ + jumpGain p β₁ * E₁ ≤ β₂ + jumpGain p β₂ * E₂ := by
  have hA₂ : 0 ≤ jumpGain p β₂ := (jumpGain_pos_of_mem model hβ₂).le
  have hidentity :
      β₂ + jumpGain p β₂ * E₂ - (β₁ + jumpGain p β₁ * E₁) =
        (β₂ - β₁) * (1 - 2 * p.c ^ 2 * E₁) + jumpGain p β₂ * (E₂ - E₁) := by
    simp only [jumpGain]; ring
  nlinarith [mul_nonneg (sub_nonneg.mpr hβ) (sub_nonneg.mpr hE₁cap),
    mul_nonneg hA₂ (sub_nonneg.mpr hE)]

/-- One projected jump step is order-preserving under the same ceiling. -/
theorem projectedJumpMap_mono {p : LoopParams} (model : LoopModelAssumptions p)
    {x y : LoopState} (hx : x.1 ∈ Icc (0 : ℝ) 1) (hy : y.1 ∈ Icc (0 : ℝ) 1)
    (hxE : 0 ≤ x.2) (hcap : 2 * p.c ^ 2 * x.2 ≤ 1)
    (hβ : x.1 ≤ y.1) (hE : x.2 ≤ y.2) :
    (projectedJumpMap p x).1 ≤ (projectedJumpMap p y).1 ∧
      (projectedJumpMap p x).2 ≤ (projectedJumpMap p y).2 := by
  have hσ : jumpPersistence p x.1 ≤ jumpPersistence p y.1 := by
    simp only [jumpPersistence]
    have := (stockMultiplier_strictMonoOn model).monotoneOn hx hy hβ
    linarith
  exact ⟨monotone_clipUnit' (rawInput_mono model hy hcap hβ hE),
    mul_le_mul hσ hE hxE (jumpPersistence_pos_of_mem model hy).le⟩

/-- Order preservation propagates along the projected orbit. -/
theorem projJumpOrbit_mono {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {x₀ y₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hy₀ : y₀.1 ∈ Icc (0 : ℝ) 1)
    (hE₀ : 0 ≤ x₀.2) (hcap : 2 * p.c ^ 2 * x₀.2 ≤ 1)
    (hβ : x₀.1 ≤ y₀.1) (hE : x₀.2 ≤ y₀.2) (n : ℕ) :
    (projJumpOrbit p x₀ n).1 ≤ (projJumpOrbit p y₀ n).1 ∧
      (projJumpOrbit p x₀ n).2 ≤ (projJumpOrbit p y₀ n).2 := by
  have hcsq : (0 : ℝ) ≤ 2 * p.c ^ 2 := by positivity
  induction n with
  | zero => simpa only [projJumpOrbit_zero] using ⟨hβ, hE⟩
  | succ n ih =>
      rw [projJumpOrbit_succ, projJumpOrbit_succ]
      have hcapn : 2 * p.c ^ 2 * (projJumpOrbit p x₀ n).2 ≤ 1 := by
        have := projJumpOrbit_excess_le_initial model hgain hx₀ hE₀ n
        nlinarith
      exact projectedJumpMap_mono model (projJumpOrbit_policy_mem (p := p) hx₀ n)
        (projJumpOrbit_policy_mem (p := p) hy₀ n)
        (projJumpOrbit_excess_nonneg model hgain hx₀ hE₀ n) hcapn ih.1 ih.2

/-! ## The unclipped initial segment and the plateau -/

/-- Every raw policy input of the projected orbit stays inside the interval. -/
def ProjOrbitUnclipped (p : LoopParams) (x₀ : LoopState) : Prop :=
  ∀ n, (projJumpOrbit p x₀ n).1
    + jumpGain p (projJumpOrbit p x₀ n).1 * (projJumpOrbit p x₀ n).2 ≤ 1

/-- Shifting the base point of a projected orbit. -/
theorem projJumpOrbit_add (p : LoopParams) (x₀ : LoopState) (m n : ℕ) :
    projJumpOrbit p x₀ (m + n) = projJumpOrbit p (projJumpOrbit p x₀ m) n := by
  simp only [projJumpOrbit, add_comm m n, Function.iterate_add_apply]

/--
The unclipped excesses form a down-set: an orbit dominated by an unclipped orbit
never clips either.  This is what makes the plateau an up-set.
-/
theorem projOrbitUnclipped_of_le {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {x₀ y₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hy₀ : y₀.1 ∈ Icc (0 : ℝ) 1)
    (hE₀ : 0 ≤ x₀.2) (hcap : 2 * p.c ^ 2 * x₀.2 ≤ 1)
    (hβ : x₀.1 ≤ y₀.1) (hE : x₀.2 ≤ y₀.2)
    (hy : ProjOrbitUnclipped p y₀) :
    ProjOrbitUnclipped p x₀ := by
  intro n
  have hord := projJumpOrbit_mono model hgain hx₀ hy₀ hE₀ hcap hβ hE n
  have hcapn : 2 * p.c ^ 2 * (projJumpOrbit p x₀ n).2 ≤ 1 := by
    have := projJumpOrbit_excess_le_initial model hgain hx₀ hE₀ n
    nlinarith [sq_nonneg p.c, model.c_pos]
  exact le_trans
    (rawInput_mono model (projJumpOrbit_policy_mem (p := p) hy₀ n) hcapn hord.1 hord.2)
    (hy n)

/-- Once a raw policy input exceeds one, the policy is one from the next step on. -/
theorem projJumpOrbit_policy_eq_one_of_clip {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀) {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hE₀ : 0 ≤ x₀.2) {n : ℕ}
    (hclip : 1 ≤ (projJumpOrbit p x₀ n).1
      + jumpGain p (projJumpOrbit p x₀ n).1 * (projJumpOrbit p x₀ n).2) (k : ℕ) :
    (projJumpOrbit p x₀ (n + 1 + k)).1 = 1 := by
  have hone : (projJumpOrbit p x₀ (n + 1)).1 = 1 := by
    rw [projJumpOrbit_succ]
    exact clipUnit_eq_one_of_le hclip
  have hnonneg : 0 ≤ (projJumpOrbit p x₀ (n + 1)).2 :=
    projJumpOrbit_excess_nonneg model hgain hx₀ hE₀ (n + 1)
  rw [projJumpOrbit_add]
  have hstate : projJumpOrbit p x₀ (n + 1) =
      ((1 : ℝ), (projJumpOrbit p x₀ (n + 1)).2) := by
    rw [← hone]
  rw [hstate]
  exact (projectedJumpOrbit_policy_one model hgain hnonneg k).1

/-- A clipping orbit has policy limit exactly one: the plateau value. -/
theorem projJumpOrbit_policy_tendsto_one_of_clip {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀) {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hE₀ : 0 ≤ x₀.2)
    (hclip : ¬ ProjOrbitUnclipped p x₀) :
    Tendsto (fun n ↦ (projJumpOrbit p x₀ n).1) atTop (nhds 1) := by
  simp only [ProjOrbitUnclipped, not_forall, not_le] at hclip
  obtain ⟨n, hn⟩ := hclip
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (n + 1)] with m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = n + 1 + k := ⟨m - (n + 1), by omega⟩
  exact (projJumpOrbit_policy_eq_one_of_clip model hgain hx₀ hE₀ hn.le k).symm

/-! ## Strict monotonicity on the unclipped segment -/

/-- On an unclipped orbit the projected step is the raw affine step. -/
theorem projJumpOrbit_policy_succ_of_unclipped {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀) {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hE₀ : 0 ≤ x₀.2)
    (hun : ProjOrbitUnclipped p x₀) (n : ℕ) :
    (projJumpOrbit p x₀ (n + 1)).1 = (projJumpOrbit p x₀ n).1
      + jumpGain p (projJumpOrbit p x₀ n).1 * (projJumpOrbit p x₀ n).2 := by
  have hβ := projJumpOrbit_policy_mem (p := p) hx₀ n
  have hlow : 0 ≤ (projJumpOrbit p x₀ n).1
      + jumpGain p (projJumpOrbit p x₀ n).1 * (projJumpOrbit p x₀ n).2 :=
    add_nonneg hβ.1 (mul_nonneg (jumpGain_pos_of_mem model hβ).le
      (projJumpOrbit_excess_nonneg model hgain hx₀ hE₀ n))
  rw [projJumpOrbit_succ]
  exact clipUnit_eq_self' ⟨hlow, hun n⟩

/-- The ordered policy gap obeys the contraction bound printed in `prop:burn`(ii). -/
theorem gap_succ_ge {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β₀ E₀ E₀' : ℝ} (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1)
    (hE₀ : 0 ≤ E₀) (hcap : 2 * p.c ^ 2 * E₀ ≤ 1) (hlt : E₀ ≤ E₀')
    (hxun : ProjOrbitUnclipped p (β₀, E₀))
    (hyun : ProjOrbitUnclipped p (β₀, E₀')) (n : ℕ) :
    (projJumpOrbit p (β₀, E₀') (n + 1)).1 - (projJumpOrbit p (β₀, E₀) (n + 1)).1 ≥
      ((projJumpOrbit p (β₀, E₀') n).1 - (projJumpOrbit p (β₀, E₀) n).1) *
        (1 - 2 * p.c ^ 2 * (projJumpOrbit p (β₀, E₀') n).2) := by
  have hE₀' : 0 ≤ E₀' := le_trans hE₀ hlt
  have hord := projJumpOrbit_mono model hgain (x₀ := (β₀, E₀)) (y₀ := (β₀, E₀'))
    hβ₀ hβ₀ hE₀ hcap le_rfl hlt n
  have hxs := projJumpOrbit_policy_succ_of_unclipped model hgain hβ₀ hE₀ hxun n
  have hys := projJumpOrbit_policy_succ_of_unclipped model hgain hβ₀ hE₀' hyun n
  have hAy : 0 ≤ jumpGain p (projJumpOrbit p (β₀, E₀') n).1 :=
    (jumpGain_pos_of_mem model (projJumpOrbit_policy_mem (p := p) hβ₀ n)).le
  have hgap : 0 ≤ (projJumpOrbit p (β₀, E₀') n).1 - (projJumpOrbit p (β₀, E₀) n).1 :=
    sub_nonneg.mpr hord.1
  have hident :
      ((projJumpOrbit p (β₀, E₀') n).1
          + jumpGain p (projJumpOrbit p (β₀, E₀') n).1 * (projJumpOrbit p (β₀, E₀') n).2)
        - ((projJumpOrbit p (β₀, E₀) n).1
          + jumpGain p (projJumpOrbit p (β₀, E₀) n).1 * (projJumpOrbit p (β₀, E₀) n).2)
      = ((projJumpOrbit p (β₀, E₀') n).1 - (projJumpOrbit p (β₀, E₀) n).1)
          * (1 - 2 * p.c ^ 2 * (projJumpOrbit p (β₀, E₀) n).2)
        + jumpGain p (projJumpOrbit p (β₀, E₀') n).1
          * ((projJumpOrbit p (β₀, E₀') n).2 - (projJumpOrbit p (β₀, E₀) n).2) := by
    simp only [jumpGain]; ring
  rw [hxs, hys]
  nlinarith [mul_nonneg hAy (sub_nonneg.mpr hord.2),
    mul_nonneg hgap (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * p.c ^ 2)
      (sub_nonneg.mpr hord.2))]

/--
Paper III, `prop:burn`(ii), strict half: between two admissible excesses whose
larger orbit never clips, the projected policy limits are strictly ordered.
-/
theorem projJumpOrbit_policy_limit_strict {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {β₀ E₀ E₀' L L' : ℝ} (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1)
    (hE₀ : 0 ≤ E₀) (hcap : 2 * p.c ^ 2 * E₀' < 1) (hlt : E₀ < E₀')
    (hxun : ProjOrbitUnclipped p (β₀, E₀))
    (hyun : ProjOrbitUnclipped p (β₀, E₀'))
    (hL : Tendsto (fun n ↦ (projJumpOrbit p (β₀, E₀) n).1) atTop (nhds L))
    (hL' : Tendsto (fun n ↦ (projJumpOrbit p (β₀, E₀') n).1) atTop (nhds L')) :
    L < L' := by
  have hE₀' : 0 ≤ E₀' := le_trans hE₀ hlt.le
  have hcapx : 2 * p.c ^ 2 * E₀ ≤ 1 := by nlinarith [sq_nonneg p.c, model.c_pos]
  set b : ℕ → ℝ := fun n ↦
    (projJumpOrbit p (β₀, E₀') n).1 - (projJumpOrbit p (β₀, E₀) n).1 with hb
  set x : ℕ → ℝ := fun n ↦ 2 * p.c ^ 2 * (projJumpOrbit p (β₀, E₀') n).2 with hx
  have hσ : (0 : ℝ) ≤ 1 - p.lambda₀ + p.g :=
    add_nonneg (sub_nonneg.mpr model.lambda₀_lt_one.le) model.g_nonneg
  have hσ1 : 1 - p.lambda₀ + p.g < 1 := by linarith [hgain]
  have hxnonneg : ∀ n, 0 ≤ x n := fun n => by
    exact mul_nonneg (by positivity)
      (projJumpOrbit_excess_nonneg model hgain hβ₀ hE₀' n)
  have hxgeom : ∀ n, x n ≤ (2 * p.c ^ 2 * E₀') * (1 - p.lambda₀ + p.g) ^ n := by
    intro n
    have := projJumpOrbit_excess_le_geometric model hgain (x₀ := (β₀, E₀')) hβ₀ hE₀' n
    calc x n ≤ 2 * p.c ^ 2 * (E₀' * (1 - p.lambda₀ + p.g) ^ n) := by
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have hbnonneg : ∀ n, 0 ≤ b n := fun n =>
    sub_nonneg.mpr (projJumpOrbit_mono model hgain (x₀ := (β₀, E₀)) (y₀ := (β₀, E₀'))
      hβ₀ hβ₀ hE₀ hcapx le_rfl hlt.le n).1
  have hstep : ∀ n, b n * (1 - x n) ≤ b (n + 1) :=
    fun n => gap_succ_ge model hgain hβ₀ hE₀ hcapx hlt.le hxun hyun n
  -- the first gap is strictly positive
  have hb1 : 0 < b 1 := by
    have hxs := projJumpOrbit_policy_succ_of_unclipped model hgain hβ₀ hE₀ hxun 0
    have hys := projJumpOrbit_policy_succ_of_unclipped model hgain hβ₀ hE₀' hyun 0
    have hA : 0 < jumpGain p β₀ := jumpGain_pos_of_mem model hβ₀
    simp only [hb, hxs, hys, projJumpOrbit_zero]
    have : jumpGain p β₀ * E₀ < jumpGain p β₀ * E₀' :=
      mul_lt_mul_of_pos_left hlt hA
    linarith
  -- all gaps past the first stay positive
  have hxlt1 : ∀ n, x n < 1 := by
    intro n
    have hle := projJumpOrbit_excess_le_initial model hgain (x₀ := (β₀, E₀')) hβ₀ hE₀' n
    have : 2 * p.c ^ 2 * (projJumpOrbit p (β₀, E₀') n).2 ≤ 2 * p.c ^ 2 * E₀' := by
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    simp only [hx]; linarith
  have hbpos : ∀ n, 1 ≤ n → 0 < b n := by
    intro n hn
    induction n with
    | zero => omega
    | succ k ih =>
        rcases Nat.eq_or_lt_of_le hn with h | h
        · simpa [← h] using hb1
        · have hk : 1 ≤ k := by omega
          have := hstep k
          nlinarith [ih hk, hxlt1 k]
  -- a tail on which the scaled excesses sum to at most one half
  have hgeom : HasSum (fun n : ℕ ↦ (1 - p.lambda₀ + p.g) ^ n)
      (1 - (1 - p.lambda₀ + p.g))⁻¹ := hasSum_geometric_of_lt_one hσ hσ1
  obtain ⟨N, hN, hN1⟩ : ∃ N : ℕ, (2 * p.c ^ 2 * E₀') * (1 - p.lambda₀ + p.g) ^ N
      * (1 - (1 - p.lambda₀ + p.g))⁻¹ ≤ 1 / 2 ∧ 1 ≤ N := by
    have hpow : Tendsto (fun n : ℕ ↦
        (2 * p.c ^ 2 * E₀') * (1 - p.lambda₀ + p.g) ^ n
          * (1 - (1 - p.lambda₀ + p.g))⁻¹) atTop (nhds 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one hσ hσ1
      simpa using (this.const_mul (2 * p.c ^ 2 * E₀')).mul_const
        (1 - (1 - p.lambda₀ + p.g))⁻¹
    obtain ⟨N, hN, hN1⟩ :=
      ((hpow.eventually (ge_mem_nhds (by norm_num : (0:ℝ) < 1/2))).and
        (eventually_ge_atTop 1)).exists
    exact ⟨N, hN, hN1⟩
  have htail : ∀ k, ∑ j ∈ Finset.range k, x (N + j) ≤ 1 / 2 := by
    intro k
    have hbound : ∑ j ∈ Finset.range k, x (N + j)
        ≤ ∑ j ∈ Finset.range k,
            (2 * p.c ^ 2 * E₀') * (1 - p.lambda₀ + p.g) ^ (N + j) :=
      Finset.sum_le_sum fun j _ => hxgeom (N + j)
    have hfactor : ∑ j ∈ Finset.range k,
        (2 * p.c ^ 2 * E₀') * (1 - p.lambda₀ + p.g) ^ (N + j)
        = ((2 * p.c ^ 2 * E₀') * (1 - p.lambda₀ + p.g) ^ N)
            * ∑ j ∈ Finset.range k, (1 - p.lambda₀ + p.g) ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [pow_add]; ring
    have hpartial : ∑ j ∈ Finset.range k, (1 - p.lambda₀ + p.g) ^ j
        ≤ (1 - (1 - p.lambda₀ + p.g))⁻¹ :=
      sum_le_hasSum _ (fun j _ => pow_nonneg hσ j) hgeom
    have hcoef : (0 : ℝ) ≤ (2 * p.c ^ 2 * E₀') * (1 - p.lambda₀ + p.g) ^ N := by
      positivity
    calc ∑ j ∈ Finset.range k, x (N + j) ≤ _ := hbound
      _ = _ := hfactor
      _ ≤ ((2 * p.c ^ 2 * E₀') * (1 - p.lambda₀ + p.g) ^ N)
            * (1 - (1 - p.lambda₀ + p.g))⁻¹ :=
          mul_le_mul_of_nonneg_left hpartial hcoef
      _ ≤ 1 / 2 := hN
  -- Weierstrass-style induction: the gap never falls below half its value at N
  have hlower : ∀ k, b N * (1 - ∑ j ∈ Finset.range k, x (N + j)) ≤ b (N + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hxk : 0 ≤ x (N + k) := hxnonneg _
        have hxk1 : x (N + k) ≤ 1 / 2 := by
          have := htail (k + 1)
          have hnn : (0:ℝ) ≤ ∑ j ∈ Finset.range k, x (N + j) :=
            Finset.sum_nonneg fun j _ => hxnonneg _
          rw [Finset.sum_range_succ] at this
          linarith
        have hmul := mul_le_mul_of_nonneg_right ih
          (by linarith : (0:ℝ) ≤ 1 - x (N + k))
        have hnext := hstep (N + k)
        have hSnn : (0:ℝ) ≤ ∑ j ∈ Finset.range k, x (N + j) :=
          Finset.sum_nonneg fun j _ => hxnonneg _
        have hbN : 0 ≤ b N := hbnonneg N
        rw [Finset.sum_range_succ, ← Nat.add_assoc]
        nlinarith [mul_nonneg hbN (mul_nonneg hSnn hxk)]
  have hhalf : ∀ k, b N / 2 ≤ b (k + N) := by
    intro k
    have := hlower k
    rw [Nat.add_comm k N]
    have hbN : 0 ≤ b N := hbnonneg N
    nlinarith [htail k, Finset.sum_nonneg (fun j (_ : j ∈ Finset.range k) => hxnonneg (N + j))]
  have hbNpos : 0 < b N := hbpos N hN1
  -- pass to the limit
  have hlim : Tendsto (fun n ↦ b n) atTop (nhds (L' - L)) := hL'.sub hL
  have hlimshift : Tendsto (fun k ↦ b (k + N)) atTop (nhds (L' - L)) :=
    hlim.comp (tendsto_add_atTop_nat N)
  have hfinal : b N / 2 ≤ L' - L := ge_of_tendsto' hlimshift hhalf
  linarith

/-! ## The trichotomy -/

/-- The projected policy limit is non-decreasing in the initial excess. -/
theorem projJumpOrbit_policy_limit_mono {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {β₀ E₀ E₀' L L' : ℝ} (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1)
    (hE₀ : 0 ≤ E₀) (hcap : 2 * p.c ^ 2 * E₀ ≤ 1) (hle : E₀ ≤ E₀')
    (hL : Tendsto (fun n ↦ (projJumpOrbit p (β₀, E₀) n).1) atTop (nhds L))
    (hL' : Tendsto (fun n ↦ (projJumpOrbit p (β₀, E₀') n).1) atTop (nhds L')) :
    L ≤ L' := by
  refine le_of_tendsto_of_tendsto hL hL' (Filter.Eventually.of_forall fun n => ?_)
  exact (projJumpOrbit_mono model hgain (x₀ := (β₀, E₀)) (y₀ := (β₀, E₀'))
    hβ₀ hβ₀ hE₀ hcap le_rfl hle n).1

/--
Paper III, Proposition 7.4 (`prop:burn`), clause (ii)
(`civic_loops.tex:550`).  On the admissible excess interval the projected policy
limit is non-decreasing; the excesses whose orbits never clip form an initial
segment, on which it is strictly increasing; and above that segment it is
identically one.  Global strict monotonicity is refuted by
`burnPolicyLimit_not_strictOn_admissibleInterval`; since the critical orbit's
limit is the saddle policy, strictly below one, the plateau lies strictly above
the critical excess, which is what `prop:seplimit` invokes.
-/
theorem burnPolicyLimit_trichotomy {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {β₀ : ℝ} (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1)
    {E₀ E₀' L L' : ℝ} (hE₀ : 0 ≤ E₀) (hlt : E₀ < E₀')
    (hcap : 2 * p.c ^ 2 * E₀' < 1)
    (hL : Tendsto (fun n ↦ (projJumpOrbit p (β₀, E₀) n).1) atTop (nhds L))
    (hL' : Tendsto (fun n ↦ (projJumpOrbit p (β₀, E₀') n).1) atTop (nhds L')) :
    L ≤ L' ∧
      (ProjOrbitUnclipped p (β₀, E₀') → ProjOrbitUnclipped p (β₀, E₀) ∧ L < L') ∧
      (¬ ProjOrbitUnclipped p (β₀, E₀') → L' = 1) := by
  have hE₀' : 0 ≤ E₀' := le_trans hE₀ hlt.le
  have hcapx : 2 * p.c ^ 2 * E₀ ≤ 1 := by nlinarith [sq_nonneg p.c, model.c_pos]
  refine ⟨projJumpOrbit_policy_limit_mono model hgain hβ₀ hE₀ hcapx hlt.le hL hL',
    fun hyun => ?_, fun hclip => ?_⟩
  · have hxun : ProjOrbitUnclipped p (β₀, E₀) :=
      projOrbitUnclipped_of_le model hgain (x₀ := (β₀, E₀)) (y₀ := (β₀, E₀'))
        hβ₀ hβ₀ hE₀ hcapx le_rfl hlt.le hyun
    exact ⟨hxun, projJumpOrbit_policy_limit_strict model hgain hβ₀ hE₀ hcap hlt
      hxun hyun hL hL'⟩
  · exact tendsto_nhds_unique hL'
      (projJumpOrbit_policy_tendsto_one_of_clip model hgain hβ₀ hE₀' hclip)

#print axioms projJumpOrbit_policy_mem
#print axioms projJumpOrbit_excess_le_initial
#print axioms projJumpOrbit_policy_monotone
#print axioms projJumpOrbit_policy_tendsto
#print axioms rawInput_mono
#print axioms projectedJumpMap_mono
#print axioms projJumpOrbit_mono
#print axioms projOrbitUnclipped_of_le
#print axioms projJumpOrbit_policy_eq_one_of_clip
#print axioms projJumpOrbit_policy_tendsto_one_of_clip
#print axioms projJumpOrbit_policy_succ_of_unclipped
#print axioms gap_succ_ge
#print axioms projJumpOrbit_policy_limit_strict
#print axioms projJumpOrbit_policy_limit_mono
#print axioms burnPolicyLimit_trichotomy

/-! ## Continuity of the policy limit -/

/-- The projected policy limit, as a function of the initial rescaled excess. -/
def burnPolicyLimit (p : LoopParams) (β₀ E₀ : ℝ) : ℝ :=
  ⨆ n, (projJumpOrbit p (β₀, E₀) n).1

theorem burnPolicyLimit_tendsto {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β₀ E₀ : ℝ} (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1) (hE₀ : 0 ≤ E₀) :
    Tendsto (fun n ↦ (projJumpOrbit p (β₀, E₀) n).1) atTop
      (nhds (burnPolicyLimit p β₀ E₀)) := by
  have hbdd : BddAbove (Set.range fun n ↦ (projJumpOrbit p (β₀, E₀) n).1) :=
    ⟨1, by rintro y ⟨n, rfl⟩; exact (projJumpOrbit_policy_mem hβ₀ n).2⟩
  exact tendsto_atTop_ciSup (projJumpOrbit_policy_monotone model hgain hβ₀ hE₀) hbdd

/-- One projected policy step advances by at most the raw jump. -/
theorem projJumpOrbit_policy_step_le {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀) {β₀ E₀ : ℝ}
    (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1) (hE₀ : 0 ≤ E₀) (n : ℕ) :
    (projJumpOrbit p (β₀, E₀) (n + 1)).1 - (projJumpOrbit p (β₀, E₀) n).1 ≤
      2 * p.c * (E₀ * (1 - p.lambda₀ + p.g) ^ n) := by
  have hβ := projJumpOrbit_policy_mem (p := p) (x₀ := (β₀, E₀)) hβ₀ n
  have hE := projJumpOrbit_excess_nonneg model hgain (x₀ := (β₀, E₀)) hβ₀ hE₀ n
  have hAnn : 0 ≤ jumpGain p (projJumpOrbit p (β₀, E₀) n).1 :=
    (jumpGain_pos_of_mem model hβ).le
  have hA : jumpGain p (projJumpOrbit p (β₀, E₀) n).1 ≤ 2 * p.c := by
    have hnonneg : 0 ≤ 2 * p.c ^ 2 * (projJumpOrbit p (β₀, E₀) n).1 :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg p.c)) hβ.1
    simp only [jumpGain]
    nlinarith
  have hnn : 0 ≤ (projJumpOrbit p (β₀, E₀) n).1
      + jumpGain p (projJumpOrbit p (β₀, E₀) n).1 * (projJumpOrbit p (β₀, E₀) n).2 :=
    add_nonneg hβ.1 (mul_nonneg hAnn hE)
  have hstep : (projJumpOrbit p (β₀, E₀) (n + 1)).1 ≤
      (projJumpOrbit p (β₀, E₀) n).1
        + jumpGain p (projJumpOrbit p (β₀, E₀) n).1 * (projJumpOrbit p (β₀, E₀) n).2 := by
    rw [projJumpOrbit_succ]
    simp only [projectedJumpMap, clipUnit_eq_clipTo]
    rw [clipTo, max_eq_right (le_min zero_le_one hnn)]
    exact min_le_right _ _
  have hgeom := projJumpOrbit_excess_le_geometric model hgain
    (x₀ := ((β₀, E₀) : LoopState)) hβ₀ hE₀ n
  nlinarith [hstep, hA, hAnn, hE, hgeom, model.c_pos]

/--
The uniform tail estimate behind continuity: the limit is approached at a
geometric rate that depends on the initial excess only through a bound on it.
-/
theorem burnPolicyLimit_sub_le {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β₀ E₀ Emax : ℝ} (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1)
    (hE₀ : 0 ≤ E₀) (hEmax : E₀ ≤ Emax) (n : ℕ) :
    burnPolicyLimit p β₀ E₀ - (projJumpOrbit p (β₀, E₀) n).1 ≤
      2 * p.c * Emax * (1 - p.lambda₀ + p.g) ^ n / (p.lambda₀ - p.g) := by
  set σ : ℝ := 1 - p.lambda₀ + p.g with hσdef
  have hσ0 : 0 ≤ σ :=
    add_nonneg (sub_nonneg.mpr model.lambda₀_lt_one.le) model.g_nonneg
  have hσ1 : σ < 1 := by rw [hσdef]; linarith
  have hgap : 0 < p.lambda₀ - p.g := sub_pos.mpr hgain
  have hone_sub : 1 - σ = p.lambda₀ - p.g := by rw [hσdef]; ring
  have hEmax0 : 0 ≤ Emax := le_trans hE₀ hEmax
  have hpartial : ∀ m, (projJumpOrbit p (β₀, E₀) (n + m)).1
      - (projJumpOrbit p (β₀, E₀) n).1 ≤
        2 * p.c * Emax * σ ^ n / (p.lambda₀ - p.g) := by
    intro m
    induction m with
    | zero =>
        have hσn : (0:ℝ) ≤ σ ^ n := pow_nonneg hσ0 n
        have hc : (0:ℝ) ≤ 2 * p.c * Emax * σ ^ n :=
          mul_nonneg (mul_nonneg (by linarith [model.c_pos]) hEmax0) hσn
        simp only [Nat.add_zero, sub_self]
        exact div_nonneg hc hgap.le
    | succ m ih =>
        have hstep := projJumpOrbit_policy_step_le model hgain hβ₀ hE₀ (n + m)
        have hmono : (projJumpOrbit p (β₀, E₀) (n + m)).1 ≤
            (projJumpOrbit p (β₀, E₀) (n + m + 1)).1 :=
          projJumpOrbit_policy_monotone model hgain hβ₀ hE₀ (Nat.le_succ _)
        have hsum : ∀ k : ℕ, 2 * p.c * (E₀ * σ ^ (n + k)) ≤
            2 * p.c * Emax * σ ^ n * σ ^ k := by
          intro k
          have : E₀ * σ ^ (n + k) ≤ Emax * (σ ^ n * σ ^ k) := by
            rw [pow_add]
            exact mul_le_mul hEmax le_rfl (by positivity) hEmax0
          nlinarith [model.c_pos, this]
        -- crude but sufficient: bound the whole tail by the geometric series
        have htail : (projJumpOrbit p (β₀, E₀) (n + m + 1)).1
            - (projJumpOrbit p (β₀, E₀) n).1 ≤
              2 * p.c * Emax * σ ^ n / (p.lambda₀ - p.g) := by
          have hgeomSum : ∀ j : ℕ, (projJumpOrbit p (β₀, E₀) (n + j)).1
              - (projJumpOrbit p (β₀, E₀) n).1 ≤
                2 * p.c * Emax * σ ^ n * ((1 - σ ^ j) / (1 - σ)) := by
            intro j
            induction j with
            | zero => simp
            | succ j ihj =>
                have hs := projJumpOrbit_policy_step_le model hgain hβ₀ hE₀ (n + j)
                have hb := hsum j
                have hσj : (0 : ℝ) ≤ σ ^ j := pow_nonneg hσ0 j
                have hfac : (1 - σ ^ (j + 1)) / (1 - σ)
                    = (1 - σ ^ j) / (1 - σ) + σ ^ j := by
                  field_simp [show (1 : ℝ) - σ ≠ 0 by linarith]
                  ring
                rw [show n + (j + 1) = n + j + 1 by omega, hfac]
                nlinarith [ihj, hs, hb]
          have := hgeomSum (m + 1)
          have hpow : (0 : ℝ) ≤ σ ^ (m + 1) := pow_nonneg hσ0 (m + 1)
          have hfrac : (1 - σ ^ (m + 1)) / (1 - σ) ≤ 1 / (1 - σ) := by
            apply div_le_div_of_nonneg_right (by linarith) (by linarith)
          have hσn : (0:ℝ) ≤ σ ^ n := pow_nonneg hσ0 n
          have hc : (0 : ℝ) ≤ 2 * p.c * Emax * σ ^ n :=
            mul_nonneg (mul_nonneg (by linarith [model.c_pos]) hEmax0) hσn
          calc (projJumpOrbit p (β₀, E₀) (n + m + 1)).1
              - (projJumpOrbit p (β₀, E₀) n).1
              ≤ 2 * p.c * Emax * σ ^ n * ((1 - σ ^ (m + 1)) / (1 - σ)) := by
                simpa only [show n + (m + 1) = n + m + 1 by omega] using this
            _ ≤ 2 * p.c * Emax * σ ^ n * (1 / (1 - σ)) :=
                mul_le_mul_of_nonneg_left hfrac hc
            _ = 2 * p.c * Emax * σ ^ n / (p.lambda₀ - p.g) := by
                rw [hone_sub]; ring
        simpa only [show n + (m + 1) = n + m + 1 by omega] using htail
  have hlim := burnPolicyLimit_tendsto model hgain hβ₀ hE₀
  have hshift : Tendsto (fun m ↦ (projJumpOrbit p (β₀, E₀) (n + m)).1) atTop
      (nhds (burnPolicyLimit p β₀ E₀)) :=
    hlim.comp (tendsto_add_atTop_nat n) |>.congr (by
      intro m; simp only [Function.comp_apply, Nat.add_comm])
  exact le_of_tendsto' (hshift.sub_const _) hpartial

#print axioms burnPolicyLimit_tendsto
#print axioms projJumpOrbit_policy_step_le
#print axioms burnPolicyLimit_sub_le

/-- Each finite projected iterate is continuous in the initial excess. -/
theorem continuous_projJumpOrbit_policy (p : LoopParams) (β₀ : ℝ) (n : ℕ) :
    Continuous fun E₀ : ℝ ↦ (projJumpOrbit p (β₀, E₀) n).1 := by
  have hstate : ∀ m : ℕ, Continuous fun E₀ : ℝ ↦ projJumpOrbit p (β₀, E₀) m := by
    intro m
    induction m with
    | zero =>
        simp only [projJumpOrbit_zero]
        exact continuous_const.prodMk continuous_id
    | succ m ih =>
        have hA : Continuous fun E₀ : ℝ ↦
            jumpGain p (projJumpOrbit p (β₀, E₀) m).1 := by
          simp only [jumpGain]
          exact continuous_const.mul (continuous_const.sub (continuous_const.mul ih.fst))
        have hs : Continuous fun E₀ : ℝ ↦
            jumpPersistence p (projJumpOrbit p (β₀, E₀) m).1 := by
          simp only [jumpPersistence, LoopParams.s]
          exact (continuous_const.mul
            ((continuous_const.sub (continuous_const.mul
              (continuous_const.sub ih.fst))).pow 2)).add continuous_const
        simp only [projJumpOrbit_succ, projectedJumpMap]
        exact (continuous_clipUnit.comp (ih.fst.add (hA.mul ih.snd))).prodMk
          (hs.mul ih.snd)
  exact (hstate n).fst

/--
Paper III, `prop:burn`(ii), continuity.  On every compact subinterval of the
admissible range the projected policy limit is a uniform limit of the continuous
finite iterates, hence continuous: the tail estimate is uniform in the initial
excess once that excess is bounded.
-/
theorem continuousOn_burnPolicyLimit {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β₀ Emax : ℝ} (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (burnPolicyLimit p β₀) (Icc 0 Emax) := by
  set σ : ℝ := 1 - p.lambda₀ + p.g with hσdef
  have hσ0 : 0 ≤ σ :=
    add_nonneg (sub_nonneg.mpr model.lambda₀_lt_one.le) model.g_nonneg
  have hσ1 : σ < 1 := by rw [hσdef]; linarith
  have hgap : 0 < p.lambda₀ - p.g := sub_pos.mpr hgain
  have hbound : Tendsto
      (fun n : ℕ ↦ 2 * p.c * Emax * σ ^ n / (p.lambda₀ - p.g)) atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one hσ0 hσ1
    simpa using ((this.const_mul (2 * p.c * Emax)).div_const (p.lambda₀ - p.g))
  have huniform : TendstoUniformlyOn
      (fun n (E₀ : ℝ) ↦ (projJumpOrbit p (β₀, E₀) n).1)
      (burnPolicyLimit p β₀) atTop (Icc 0 Emax) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hbound.eventually (gt_mem_nhds hε)] with n hn E₀ hE₀
    have hle : (projJumpOrbit p (β₀, E₀) n).1 ≤ burnPolicyLimit p β₀ E₀ := by
      have hbdd : BddAbove (Set.range fun m ↦ (projJumpOrbit p (β₀, E₀) m).1) :=
        ⟨1, by rintro y ⟨m, rfl⟩; exact (projJumpOrbit_policy_mem (p := p) hβ₀ m).2⟩
      exact le_ciSup hbdd n
    have htail := burnPolicyLimit_sub_le model hgain hβ₀ hE₀.1 hE₀.2 n
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]
    linarith
  exact huniform.continuousOn ((Eventually.of_forall fun n ↦
    (continuous_projJumpOrbit_policy p β₀ n).continuousOn).frequently)

#print axioms continuous_projJumpOrbit_policy
#print axioms continuousOn_burnPolicyLimit

end

end CivicAlignment.PaperIII
