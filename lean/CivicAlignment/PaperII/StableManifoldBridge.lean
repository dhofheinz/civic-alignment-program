/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.SaddleGerm

/-!
# Stable orbits never leave the box they start in

For a general planar map, the ambient stable set of a saddle can thread any
neighborhood with extra strands, and the local stable-manifold theorem says
nothing about them.  Here the internally proved order structure closes that
gap with no additional analysis: the stable set is invariant and an
antichain, so no orbit step on it is strictly comparable; an equal step would
be a fixed point, forcing the saddle itself; and under `(SS⁺)` the
quadrant-exclusion machinery then makes every stable orbit componentwise
monotone toward the saddle.  A componentwise-monotone sequence converging to
its limit never exceeds its initial distance in the sup metric.  Hence a
stable orbit starting in a centered box stays in that box — the staying-set
and the ambient stable set agree locally, which is exactly the bridge
`PaperII/StableManifold.lean` needs.

The file also records that the saddle stock is strictly interior to the
absorbing box.
-/

namespace CivicAlignment
namespace PaperII

open BoundedContinuousFunction Metric Set Filter Topology LoopParams

variable {p : LoopParams}

/-! ## The saddle is strictly interior -/

/-- At an interior policy, the stationary stock is strictly between the
injection floor and the retirement ceiling. -/
theorem stationaryStock_mem_Ioo (model : DriftModelAssumptions p)
    (threshold : ThresholdAssumption p) :
    p.stationaryStock threshold.βdagger ∈ Ioo p.I (p.I / p.lambda₀) := by
  have hβ := threshold.βdagger_mem
  have hbase : 0 < 1 - p.η * (1 - threshold.βdagger) := by
    have h1 : p.η * (1 - threshold.βdagger) < p.η * 1 := by
      apply mul_lt_mul_of_pos_left _ model.η_pos
      linarith [hβ.1]
    have h2 : p.η * 1 ≤ 1 := by
      rw [mul_one]
      exact model.η_le_one
    linarith
  have hbase_lt : 1 - p.η * (1 - threshold.βdagger) < 1 := by
    have h1 : 0 < p.η * (1 - threshold.βdagger) :=
      mul_pos model.η_pos (by linarith [hβ.2])
    linarith
  have hs_pos : 0 < p.s threshold.βdagger := by
    simp only [LoopParams.s]
    have h2 : 0 < 1 - p.lambda₀ := by linarith [model.lambda₀_lt_one]
    positivity
  have hs_lt : p.s threshold.βdagger < 1 - p.lambda₀ := by
    simp only [LoopParams.s]
    have h2 : 0 < 1 - p.lambda₀ := by linarith [model.lambda₀_lt_one]
    have hsq : (1 - p.η * (1 - threshold.βdagger)) ^ 2 < 1 := by
      nlinarith
    nlinarith
  have hden_pos : 0 < 1 - p.s threshold.βdagger := by
    linarith [model.lambda₀_pos]
  have hgz : p.g = 0 := model.no_content_gain
  simp only [LoopParams.stationaryStock, hgz, sub_zero]
  constructor
  · rw [lt_div_iff₀ hden_pos]
    nlinarith [model.I_pos]
  · rw [div_lt_div_iff₀ hden_pos model.lambda₀_pos]
    nlinarith [model.I_pos]

/-! ## Componentwise monotone convergence bounds -/

/-- A monotone real sequence converging to its limit never exceeds its
initial distance from that limit. -/
theorem abs_sub_limit_le_of_monotone {u : ℕ → ℝ} {l : ℝ} (hu : Monotone u)
    (hl : Tendsto u atTop (𝓝 l)) (n : ℕ) : |u n - l| ≤ |u 0 - l| := by
  have h1 : u 0 ≤ u n := hu (Nat.zero_le n)
  have h2 : u n ≤ l :=
    ge_of_tendsto hl (Filter.eventually_atTop.mpr ⟨n, fun m hm => hu hm⟩)
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  linarith

/-- The antitone counterpart. -/
theorem abs_sub_limit_le_of_antitone {u : ℕ → ℝ} {l : ℝ} (hu : Antitone u)
    (hl : Tendsto u atTop (𝓝 l)) (n : ℕ) : |u n - l| ≤ |u 0 - l| := by
  have h1 : u n ≤ u 0 := hu (Nat.zero_le n)
  have h2 : l ≤ u n :=
    le_of_tendsto hl (Filter.eventually_atTop.mpr ⟨n, fun m hm => hu hm⟩)
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  linarith

/-! ## The bridge -/

/-- The saddle is a fixed point of the loop map. -/
theorem loopMap_saddlePoint (model : DriftModelAssumptions p)
    (threshold : ThresholdAssumption p) :
    p.loopMap (saddlePoint p threshold) = saddlePoint p threshold :=
  saddlePoint_fixed model threshold

/-- The only fixed point on the ambient stable set is the saddle itself. -/
theorem eq_saddle_of_fixed_of_mem_stable
    (threshold : ThresholdAssumption p) {y : LoopState}
    (hy : y ∈ ambientSaddleStableSet p threshold)
    (hfix : p.loopMap y = y) : y = saddlePoint p threshold := by
  have hconst : ∀ k, p.loopMap^[k] y = y := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply, hfix, ih]
  have htends : Tendsto (fun _ : ℕ => y) atTop (𝓝 (saddlePoint p threshold)) := by
    have horb : loopOrbit p y = fun _ : ℕ => y := funext hconst
    rw [← horb]
    exact hy.2
  exact tendsto_nhds_unique tendsto_const_nhds htends

/-- Every orbit point of an ambient stable point is ambient stable. -/
theorem loopOrbit_mem_stable (model : DriftModelAssumptions p)
    (threshold : ThresholdAssumption p) {x : LoopState}
    (hx : x ∈ ambientSaddleStableSet p threshold) (n : ℕ) :
    loopOrbit p x n ∈ ambientSaddleStableSet p threshold := by
  refine ⟨loopOrbit_mem_absorbingBox model hx.1 n, ?_⟩
  exact (loopOrbit_tendsto_iff_tail p x (saddlePoint p threshold) n).mpr hx.2

/-- Along an ambient stable orbit, every step is either strictly
incomparable or already at the saddle. -/
theorem stable_step_incomparable_or_saddle (model : DriftModelAssumptions p)
    (ssplus : ConvergentStepAssumption p) (threshold : ThresholdAssumption p)
    {x : LoopState} (hx : x ∈ ambientSaddleStableSet p threshold) (k : ℕ) :
    ¬(loopOrbit p x k ≤ loopOrbit p x (k + 1) ∨
        loopOrbit p x (k + 1) ≤ loopOrbit p x k) ∨
      loopOrbit p x k = saddlePoint p threshold := by
  by_cases hq : loopOrbit p x k = saddlePoint p threshold
  · exact Or.inr hq
  left
  have h1 := loopOrbit_mem_stable model threshold hx k
  have h2 := loopOrbit_mem_stable model threshold hx (k + 1)
  have hstep : loopOrbit p x (k + 1) = p.loopMap (loopOrbit p x k) :=
    Function.iterate_succ_apply' _ _ _
  by_cases heq : loopOrbit p x k = loopOrbit p x (k + 1)
  · exfalso
    apply hq
    apply eq_saddle_of_fixed_of_mem_stable threshold h1
    rw [← hstep, ← heq]
  have hA := saddleStableSetInBox_isAntichain model ssplus threshold
  have hb1 : (⟨loopOrbit p x k, h1.1⟩ : LoopBox p) ∈
      saddleStableSetInBox p threshold := h1.2
  have hb2 : (⟨loopOrbit p x (k + 1), h2.1⟩ : LoopBox p) ∈
      saddleStableSetInBox p threshold := h2.2
  rintro (hle | hle)
  · exact hA hb1 hb2 (by simpa [Subtype.ext_iff] using heq)
      (Subtype.mk_le_mk.mpr hle)
  · exact hA hb2 hb1 (by simpa [Subtype.ext_iff, ne_comm] using heq)
      (Subtype.mk_le_mk.mpr hle)

/-- **The bridge.** An ambient stable orbit never exceeds its initial sup
distance from the saddle: componentwise monotonicity from the antichain and
quadrant-exclusion machinery, then monotone convergence. -/
theorem stable_orbit_dist_le (model : DriftModelAssumptions p)
    (ssplus : ConvergentStepAssumption p) (threshold : ThresholdAssumption p)
    {x : LoopState} (hx : x ∈ ambientSaddleStableSet p threshold) (n : ℕ) :
    dist (loopOrbit p x n) (saddlePoint p threshold) ≤
      dist x (saddlePoint p threshold) := by
  classical
  set q := saddlePoint p threshold with hqdef
  -- componentwise monotonicity suffices
  suffices hmono : (Monotone (fun k => (loopOrbit p x k).1) ∧
      Antitone (fun k => (loopOrbit p x k).2)) ∨
      (Antitone (fun k => (loopOrbit p x k).1) ∧
      Monotone (fun k => (loopOrbit p x k).2)) by
    have hu_lim : Tendsto (fun k => (loopOrbit p x k).1) atTop (𝓝 q.1) :=
      ((continuous_fst.tendsto q).comp hx.2)
    have hv_lim : Tendsto (fun k => (loopOrbit p x k).2) atTop (𝓝 q.2) :=
      ((continuous_snd.tendsto q).comp hx.2)
    have hu_bound : |(loopOrbit p x n).1 - q.1| ≤ |x.1 - q.1| := by
      rcases hmono with ⟨hu, _⟩ | ⟨hu, _⟩
      · exact abs_sub_limit_le_of_monotone hu hu_lim n
      · exact abs_sub_limit_le_of_antitone hu hu_lim n
    have hv_bound : |(loopOrbit p x n).2 - q.2| ≤ |x.2 - q.2| := by
      rcases hmono with ⟨_, hv⟩ | ⟨_, hv⟩
      · exact abs_sub_limit_le_of_antitone hv hv_lim n
      · exact abs_sub_limit_le_of_monotone hv hv_lim n
    rw [Prod.dist_eq, Prod.dist_eq]
    apply max_le
    · calc dist (loopOrbit p x n).1 q.1 = |(loopOrbit p x n).1 - q.1| :=
          Real.dist_eq _ _
        _ ≤ |x.1 - q.1| := hu_bound
        _ = dist x.1 q.1 := (Real.dist_eq _ _).symm
        _ ≤ max (dist x.1 q.1) (dist x.2 q.2) := le_max_left _ _
    · calc dist (loopOrbit p x n).2 q.2 = |(loopOrbit p x n).2 - q.2| :=
          Real.dist_eq _ _
        _ ≤ |x.2 - q.2| := hv_bound
        _ = dist x.2 q.2 := (Real.dist_eq _ _).symm
        _ ≤ max (dist x.1 q.1) (dist x.2 q.2) := le_max_right _ _
  -- establish componentwise monotonicity
  have htraj := loopOrbit_isTrajectory p x
  have hmem : ∀ k, loopOrbit p x k ∈ absorbingBox p :=
    loopOrbit_mem_absorbingBox model hx.1
  by_cases hq_hit : ∃ k, loopOrbit p x k = q
  · -- the orbit reaches the saddle in finite time and freezes there
    set N := Nat.find hq_hit with hNdef
    have hN : loopOrbit p x N = q := Nat.find_spec hq_hit
    have hfrozen : ∀ k, N ≤ k → loopOrbit p x k = q := by
      intro k hk
      induction k with
      | zero =>
          have : N = 0 := Nat.le_zero.mp hk
          rw [← this]
          exact hN
      | succ k ih =>
          rcases Nat.lt_or_ge N (k + 1) with hlt | hge
          · have hk' : N ≤ k := Nat.lt_succ_iff.mp hlt
            have hstep : loopOrbit p x (k + 1) = p.loopMap (loopOrbit p x k) :=
              Function.iterate_succ_apply' _ _ _
            rw [hstep, ih hk', hqdef]
            exact loopMap_saddlePoint model threshold
          · have : N = k + 1 := le_antisymm hk hge
            rw [← this]
            exact hN
    -- before the hitting time, steps are incomparable and of constant quadrant
    have hpre : ∀ k, k < N →
        ¬(loopOrbit p x k ≤ loopOrbit p x (k + 1) ∨
          loopOrbit p x (k + 1) ≤ loopOrbit p x k) := by
      intro k hk
      rcases stable_step_incomparable_or_saddle model ssplus threshold hx k with
        h | h
      · exact h
      · exact absurd h (Nat.find_min hq_hit hk)
    -- per-step componentwise comparisons
    have hstepwise : (∀ k, (loopOrbit p x k).1 ≤ (loopOrbit p x (k + 1)).1 ∧
        (loopOrbit p x (k + 1)).2 ≤ (loopOrbit p x k).2) ∨
        (∀ k, (loopOrbit p x (k + 1)).1 ≤ (loopOrbit p x k).1 ∧
        (loopOrbit p x k).2 ≤ (loopOrbit p x (k + 1)).2) := by
      rcases Nat.eq_zero_or_pos N with hN0 | hNpos
      · -- the orbit starts at the saddle: constant, both branches hold
        left
        intro k
        have h1 : loopOrbit p x k = q := hfrozen k (hN0 ▸ Nat.zero_le k)
        have h2 : loopOrbit p x (k + 1) = q := hfrozen (k + 1)
          (hN0 ▸ Nat.zero_le (k + 1))
        rw [h1, h2]
        exact ⟨le_refl _, le_refl _⟩
      · rcases southeast_or_northwest_of_not_comparable
          (hpre 0 hNpos) with hfirst | hfirst
        · -- southeast throughout the prefix, frozen afterwards
          left
          have hSE : ∀ k, k < N → Southeast (loopOrbit p x k)
              (loopOrbit p x (k + 1)) := by
            intro k
            induction k with
            | zero => intro _; exact hfirst
            | succ k ih =>
                intro hk1
                have hk : k < N := Nat.lt_of_succ_lt hk1
                rcases southeast_or_northwest_of_not_comparable
                  (hpre (k + 1) hk1) with h | h
                · exact h
                · exact absurd h (trajectory_no_southeast_to_northwest model
                    ssplus htraj hmem (ih hk))
          intro k
          rcases Nat.lt_or_ge k N with hk | hk
          · exact ⟨(hSE k hk).1.le, (hSE k hk).2.le⟩
          · have h1 : loopOrbit p x k = q := hfrozen k hk
            have h2 : loopOrbit p x (k + 1) = q := hfrozen (k + 1)
              (le_trans hk (Nat.le_succ k))
            rw [h1, h2]
            exact ⟨le_refl _, le_refl _⟩
        · -- northwest throughout the prefix
          right
          have hNW : ∀ k, k < N → Northwest (loopOrbit p x k)
              (loopOrbit p x (k + 1)) := by
            intro k
            induction k with
            | zero => intro _; exact hfirst
            | succ k ih =>
                intro hk1
                have hk : k < N := Nat.lt_of_succ_lt hk1
                rcases southeast_or_northwest_of_not_comparable
                  (hpre (k + 1) hk1) with h | h
                · exact absurd h (trajectory_no_northwest_to_southeast model
                    ssplus htraj hmem (ih hk))
                · exact h
          intro k
          rcases Nat.lt_or_ge k N with hk | hk
          · exact ⟨(hNW k hk).1.le, (hNW k hk).2.le⟩
          · have h1 : loopOrbit p x k = q := hfrozen k hk
            have h2 : loopOrbit p x (k + 1) = q := hfrozen (k + 1)
              (le_trans hk (Nat.le_succ k))
            rw [h1, h2]
            exact ⟨le_refl _, le_refl _⟩
    rcases hstepwise with h | h
    · exact Or.inl ⟨monotone_nat_of_le_succ (fun k => (h k).1),
        antitone_nat_of_succ_le (fun k => (h k).2)⟩
    · exact Or.inr ⟨antitone_nat_of_succ_le (fun k => (h k).1),
        monotone_nat_of_le_succ (fun k => (h k).2)⟩
  · -- the orbit never reaches the saddle: incomparable steps forever
    have hnone : ∀ k, ¬(loopOrbit p x k ≤ loopOrbit p x (k + 1) ∨
        loopOrbit p x (k + 1) ≤ loopOrbit p x k) := by
      intro k
      rcases stable_step_incomparable_or_saddle model ssplus threshold hx k with
        h | h
      · exact h
      · exact absurd ⟨k, h⟩ hq_hit
    rcases southeast_or_northwest_of_not_comparable (hnone 0) with hfirst | hfirst
    · have hall := trajectory_southeast_of_no_comparable_step model ssplus
        htraj hmem hnone hfirst
      exact Or.inl ⟨monotone_nat_of_le_succ (fun k => (hall k).1.le),
        antitone_nat_of_succ_le (fun k => (hall k).2.le)⟩
    · have hall := trajectory_northwest_of_no_comparable_step model ssplus
        htraj hmem hnone hfirst
      exact Or.inr ⟨antitone_nat_of_succ_le (fun k => (hall k).1.le),
        monotone_nat_of_le_succ (fun k => (hall k).2.le)⟩

end PaperII
end CivicAlignment

#print axioms CivicAlignment.PaperII.stable_orbit_dist_le
#print axioms CivicAlignment.PaperII.stationaryStock_mem_Ioo
