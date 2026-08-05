/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# The substitution operator on bounded sequences is `C¹`

For a globally `C¹` map `r` between real normed spaces whose domain has
compact closed balls, postcomposition `x ↦ (n ↦ r (x n))` defines an operator
on the Banach space `ℕ →ᵇ E` of bounded sequences.  This file proves that the
operator is `C¹` with the expected diagonal derivative
`h ↦ (n ↦ (r' (x n)) (h n))` — the Nemytskii (superposition) lemma, which
Mathlib does not carry and which Irwin's proof of the local stable-manifold
theorem consumes.  Heine–Cantor uniform continuity of the derivative on closed
balls supplies the uniform little-o; nothing deeper is needed.

Infrastructure for `PaperII/PlanarHadamardPerron.lean`; nothing in this file
mentions the loop model.
-/

namespace CivicAlignment
namespace PaperII

open BoundedContinuousFunction Metric Set Filter Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [ProperSpace E] in
/-- Every value of a bounded sequence lies in the closed ball of its norm. -/
theorem seqValue_mem_closedBall (x : ℕ →ᵇ E) (n : ℕ) :
    x n ∈ closedBall (0 : E) ‖x‖ := by
  simpa [mem_closedBall, dist_zero_right] using x.norm_coe_le_norm n

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- A continuous map is uniformly bounded along any bounded sequence. -/
theorem exists_substitution_bound (r : E → F) (hr : Continuous r) (x : ℕ →ᵇ E) :
    ∃ C, ∀ n, ‖r (x n)‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : E) ‖x‖).exists_bound_of_continuousOn hr.continuousOn
  exact ⟨C, fun n => hC _ (seqValue_mem_closedBall x n)⟩

/-- The substitution (Nemytskii) operator: postcomposition of a bounded
sequence by a continuous map. -/
noncomputable def substitutionMap (r : E → F) (hr : Continuous r) (x : ℕ →ᵇ E) :
    ℕ →ᵇ F :=
  ofNormedAddCommGroupDiscrete (fun n => r (x n))
    (exists_substitution_bound r hr x).choose
    (exists_substitution_bound r hr x).choose_spec

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
@[simp] theorem substitutionMap_apply (r : E → F) (hr : Continuous r)
    (x : ℕ →ᵇ E) (n : ℕ) :
    substitutionMap r hr x n = r (x n) := rfl

/-- A continuous operator-valued map admits a nonnegative uniform bound along
any bounded sequence. -/
theorem exists_substitutionDeriv_bound (r' : E → E →L[ℝ] F)
    (hr' : Continuous r') (x : ℕ →ᵇ E) :
    ∃ C, 0 ≤ C ∧ ∀ n, ‖r' (x n)‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_substitution_bound r' hr' x
  exact ⟨max C 0, le_max_right C 0, fun n => (hC n).trans (le_max_left C 0)⟩

/-- The diagonal candidate derivative of the substitution operator at a
bounded sequence `x`: apply the derivative of `r` at `x n` in slot `n`. -/
noncomputable def substitutionDeriv (r' : E → E →L[ℝ] F) (hr' : Continuous r')
    (x : ℕ →ᵇ E) : (ℕ →ᵇ E) →L[ℝ] ℕ →ᵇ F :=
  LinearMap.mkContinuous
    { toFun := fun h => ofNormedAddCommGroupDiscrete
        (fun n => r' (x n) (h n))
        ((exists_substitutionDeriv_bound r' hr' x).choose * ‖h‖)
        (fun n =>
          ((r' (x n)).le_opNorm (h n)).trans
            (mul_le_mul ((exists_substitutionDeriv_bound r' hr' x).choose_spec.2 n)
              (h.norm_coe_le_norm n) (norm_nonneg _)
              (exists_substitutionDeriv_bound r' hr' x).choose_spec.1))
      map_add' := by
        intro h₁ h₂
        ext n
        simp
      map_smul' := by
        intro c h
        ext n
        simp }
    (exists_substitutionDeriv_bound r' hr' x).choose
    (by
      intro h
      apply (norm_le (mul_nonneg
        (exists_substitutionDeriv_bound r' hr' x).choose_spec.1 (norm_nonneg h))).mpr
      intro n
      exact ((r' (x n)).le_opNorm (h n)).trans
        (mul_le_mul ((exists_substitutionDeriv_bound r' hr' x).choose_spec.2 n)
          (h.norm_coe_le_norm n) (norm_nonneg _)
          (exists_substitutionDeriv_bound r' hr' x).choose_spec.1))

@[simp] theorem substitutionDeriv_apply (r' : E → E →L[ℝ] F) (hr' : Continuous r')
    (x h : ℕ →ᵇ E) (n : ℕ) :
    substitutionDeriv r' hr' x h n = r' (x n) (h n) := rfl

omit [ProperSpace E] in
/-- The one-slot mean-value estimate: where the derivative moves by at most
`c` on the segment, the increment differs from its linearization by at most
`c` times the step. -/
theorem norm_increment_sub_deriv_le {r : E → F} {r' : E → E →L[ℝ] F}
    (hd : ∀ z, HasFDerivAt r (r' z) z) {a b : E} {c : ℝ}
    (hc : ∀ z ∈ segment ℝ a (a + b), ‖r' z - r' a‖ ≤ c) :
    ‖r (a + b) - r a - r' a b‖ ≤ c * ‖b‖ := by
  have hseg : Convex ℝ (segment ℝ a (a + b)) := convex_segment a (a + b)
  have hder : ∀ z ∈ segment ℝ a (a + b),
      HasFDerivWithinAt (fun w => r w - r' a w) (r' z - r' a)
        (segment ℝ a (a + b)) z := fun z _ =>
    ((hd z).sub ((r' a).hasFDerivAt)).hasFDerivWithinAt
  have hmvt := hseg.norm_image_sub_le_of_norm_hasFDerivWithin_le hder hc
    (left_mem_segment ℝ a (a + b)) (right_mem_segment ℝ a (a + b))
  have hrewrite : r (a + b) - r' a (a + b) - (r a - r' a a) =
      r (a + b) - r a - r' a b := by
    have : r' a (a + b) = r' a a + r' a b := by
      rw [← ContinuousLinearMap.map_add]
    rw [this]
    abel
  calc ‖r (a + b) - r a - r' a b‖
      = ‖r (a + b) - r' a (a + b) - (r a - r' a a)‖ := by rw [hrewrite]
    _ ≤ c * ‖a + b - a‖ := hmvt
    _ = c * ‖b‖ := by rw [add_sub_cancel_left]

/-- The substitution operator is Fréchet differentiable at every bounded
sequence, with the diagonal derivative. -/
theorem substitutionMap_hasFDerivAt {r : E → F} {r' : E → E →L[ℝ] F}
    (hd : ∀ z, HasFDerivAt r (r' z) z) (hr : Continuous r)
    (hr' : Continuous r') (x : ℕ →ᵇ E) :
    HasFDerivAt (substitutionMap r hr) (substitutionDeriv r' hr' x) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hK : IsCompact (closedBall (0 : E) (‖x‖ + 1)) :=
    isCompact_closedBall (0 : E) (‖x‖ + 1)
  have huc : UniformContinuousOn r' (closedBall (0 : E) (‖x‖ + 1)) :=
    hK.uniformContinuousOn_of_continuous hr'.continuousOn
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp huc c hc
  have hmem : Metric.ball (0 : ℕ →ᵇ E) (min δ 1) ∈ 𝓝 (0 : ℕ →ᵇ E) :=
    Metric.ball_mem_nhds _ (lt_min hδpos one_pos)
  filter_upwards [hmem] with h hh
  have hnorm : ‖h‖ < min δ 1 := by
    simpa [mem_ball, dist_zero_right] using hh
  have hpoint : ∀ n : ℕ,
      ‖r (x n + h n) - r (x n) - r' (x n) (h n)‖ ≤ c * ‖h‖ := by
    intro n
    have hsegK : segment ℝ (x n) (x n + h n) ⊆ closedBall (0 : E) (‖x‖ + 1) := by
      apply (convex_closedBall (0 : E) (‖x‖ + 1)).segment_subset
      · exact mem_closedBall_zero_iff.mpr
          ((x.norm_coe_le_norm n).trans (by linarith [norm_nonneg h]))
      · refine mem_closedBall_zero_iff.mpr ((norm_add_le _ _).trans ?_)
        have h1 : ‖h n‖ ≤ 1 := (h.norm_coe_le_norm n).trans
          (hnorm.le.trans (min_le_right δ 1))
        have h2 : ‖x n‖ ≤ ‖x‖ := x.norm_coe_le_norm n
        linarith
    have hstep : ∀ z ∈ segment ℝ (x n) (x n + h n), ‖r' z - r' (x n)‖ ≤ c := by
      intro z hz
      have hzK := hsegK hz
      have hxK : x n ∈ closedBall (0 : E) (‖x‖ + 1) :=
        mem_closedBall_zero_iff.mpr ((x.norm_coe_le_norm n).trans (by linarith))
      have hclose : dist z (x n) < δ := by
        obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
        have : s • x n + t • (x n + h n) - x n = t • h n := by
          have hs' : s = 1 - t := by linarith
          rw [hs']
          module
        rw [dist_eq_norm, this, norm_smul]
        have ht1 : t ≤ 1 := by linarith
        have : t * ‖h n‖ ≤ ‖h n‖ := by
          calc t * ‖h n‖ ≤ 1 * ‖h n‖ :=
            mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
            _ = ‖h n‖ := one_mul _
        calc |t| * ‖h n‖ = t * ‖h n‖ := by rw [abs_of_nonneg ht]
          _ ≤ ‖h n‖ := this
          _ ≤ ‖h‖ := h.norm_coe_le_norm n
          _ < δ := hnorm.trans_le (min_le_left δ 1)
      have := hδ z hzK (x n) hxK hclose
      rw [dist_eq_norm] at this
      exact this.le
    exact (norm_increment_sub_deriv_le hd hstep).trans
      (mul_le_mul_of_nonneg_left (h.norm_coe_le_norm n) hc.le)
  have hfinal : ‖substitutionMap r hr (x + h) - substitutionMap r hr x -
      substitutionDeriv r' hr' x h‖ ≤ c * ‖h‖ := by
    apply (norm_le (mul_nonneg hc.le (norm_nonneg h))).mpr
    intro n
    have hxh : (x + h) n = x n + h n := rfl
    simpa [hxh] using hpoint n
  simpa using hfinal

/-- The diagonal derivative varies continuously in the base sequence. -/
theorem continuous_substitutionDeriv (r' : E → E →L[ℝ] F) (hr' : Continuous r') :
    Continuous (substitutionDeriv r' hr') := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hK : IsCompact (closedBall (0 : E) (‖x‖ + 1)) :=
    isCompact_closedBall (0 : E) (‖x‖ + 1)
  have huc : UniformContinuousOn r' (closedBall (0 : E) (‖x‖ + 1)) :=
    hK.uniformContinuousOn_of_continuous hr'.continuousOn
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) (half_pos hε)
  refine ⟨min δ 1, lt_min hδpos one_pos, fun {y} hy => ?_⟩
  have hdist : ‖y - x‖ < min δ 1 := by rwa [← dist_eq_norm]
  have hopbound : ‖substitutionDeriv r' hr' y - substitutionDeriv r' hr' x‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (half_pos hε).le
    intro h
    apply (norm_le (mul_nonneg (half_pos hε).le (norm_nonneg h))).mpr
    intro n
    have happly : (substitutionDeriv r' hr' y - substitutionDeriv r' hr' x) h n =
        (r' (y n) - r' (x n)) (h n) := rfl
    rw [happly]
    have hyK : y n ∈ closedBall (0 : E) (‖x‖ + 1) := by
      apply mem_closedBall_zero_iff.mpr
      have h1 : ‖y n‖ ≤ ‖y‖ := y.norm_coe_le_norm n
      have h2 : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
        calc ‖y‖ = ‖x + (y - x)‖ := by abel_nf
          _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
      have h3 : ‖y - x‖ ≤ 1 := hdist.le.trans (min_le_right δ 1)
      linarith
    have hxK : x n ∈ closedBall (0 : E) (‖x‖ + 1) :=
      mem_closedBall_zero_iff.mpr ((x.norm_coe_le_norm n).trans (by linarith))
    have hclose : dist (y n) (x n) < δ := by
      have : dist (y n) (x n) ≤ dist y x := dist_coe_le_dist n
      calc dist (y n) (x n) ≤ dist y x := this
        _ = ‖y - x‖ := dist_eq_norm y x
        _ < δ := hdist.trans_le (min_le_left δ 1)
    have hδclose := hδ (y n) hyK (x n) hxK hclose
    rw [dist_eq_norm] at hδclose
    calc ‖(r' (y n) - r' (x n)) (h n)‖
        ≤ ‖r' (y n) - r' (x n)‖ * ‖h n‖ := (r' (y n) - r' (x n)).le_opNorm (h n)
      _ ≤ (ε / 2) * ‖h‖ := mul_le_mul hδclose.le (h.norm_coe_le_norm n)
          (norm_nonneg _) (half_pos hε).le
  calc dist (substitutionDeriv r' hr' y) (substitutionDeriv r' hr' x)
      = ‖substitutionDeriv r' hr' y - substitutionDeriv r' hr' x‖ := dist_eq_norm _ _
    _ ≤ ε / 2 := hopbound
    _ < ε := half_lt_self hε

/-- The diagonal derivative inherits any uniform slot-wise bound on the
derivative field. -/
theorem substitutionDeriv_opNorm_le (r' : E → E →L[ℝ] F) (hr' : Continuous r')
    (x : ℕ →ᵇ E) {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ n, ‖r' (x n)‖ ≤ C) :
    ‖substitutionDeriv r' hr' x‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro h
  apply (norm_le (mul_nonneg hC (norm_nonneg h))).mpr
  intro n
  calc ‖substitutionDeriv r' hr' x h n‖
      = ‖r' (x n) (h n)‖ := by rw [substitutionDeriv_apply]
    _ ≤ ‖r' (x n)‖ * ‖h n‖ := (r' (x n)).le_opNorm (h n)
    _ ≤ C * ‖h‖ := mul_le_mul (hbound n) (h.norm_coe_le_norm n)
        (norm_nonneg _) hC

/-- The substitution operator is `C¹` at every bounded sequence. -/
theorem substitutionMap_contDiffAt {r : E → F} {r' : E → E →L[ℝ] F}
    (hd : ∀ z, HasFDerivAt r (r' z) z) (hr : Continuous r)
    (hr' : Continuous r') (x : ℕ →ᵇ E) :
    ContDiffAt ℝ 1 (substitutionMap r hr) x := by
  have h1 : (1 : WithTop ℕ∞) = (0 : ℕ) + 1 := by norm_num
  rw [h1, contDiffAt_succ_iff_hasFDerivAt]
  refine ⟨substitutionDeriv r' hr',
    ⟨Set.univ, Filter.univ_mem, fun y _ => substitutionMap_hasFDerivAt hd hr hr' y⟩, ?_⟩
  exact (contDiff_zero.mpr (continuous_substitutionDeriv r' hr')).contDiffAt

end PaperII
end CivicAlignment

#print axioms CivicAlignment.PaperII.substitutionMap_hasFDerivAt
#print axioms CivicAlignment.PaperII.continuous_substitutionDeriv
#print axioms CivicAlignment.PaperII.substitutionMap_contDiffAt
