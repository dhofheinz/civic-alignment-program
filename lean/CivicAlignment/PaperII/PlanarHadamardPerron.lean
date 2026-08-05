/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.HyperbolicGreen
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Irwin's implicit-function step for the planar hyperbolic germ

The orbit equation of `PaperII/HyperbolicGreen.lean` is `Φ(σ, x) = 0` with
`Φ(σ, x) = x - Kσ - S(N x)`, where `K` injects the initial contracting
coordinate, `S` is the hyperbolic Green operator, and `N` is the substitution
operator of the remainder.  Because the remainder vanishes to first order at
the origin, `∂ₓΦ(0,0)` is the identity, so Mathlib's `C¹` implicit function
theorem applies with no separate invertibility argument.  This file
constructs the implicit solution family `stableGraph : ℝ → SeqPair`, computes
its strict derivative at zero (the contracting injection — tangency), and
propagates `C¹`-ness to a neighborhood of zero via the openness of the
Neumann-series invertibility of `∂ₓΦ`.

`PaperII/StableCurve.lean` packages these facts into the local
stable-manifold statement; nothing here mentions the loop model.
-/

namespace CivicAlignment
namespace PaperII
namespace PlanarHyperbolicGerm

open BoundedContinuousFunction Metric Set Filter Topology

variable (Γ : PlanarHyperbolicGerm)

/-! ## The orbit-equation map and its derivative -/

/-- The orbit-equation map `Φ(σ, x) = x - Kσ - S(N x)`. -/
noncomputable def orbitEquationMap : ℝ × SeqPair → SeqPair := fun p =>
  p.2 - Γ.contractInjection p.1 - Γ.green (Γ.remainderSeq p.2)

/-- Zeros of the orbit-equation map are exactly the Green solutions. -/
theorem orbitEquationMap_eq_zero_iff (σ : ℝ) (x : SeqPair) :
    Γ.orbitEquationMap (σ, x) = 0 ↔ Γ.IsGreenSolution σ x := by
  rw [orbitEquationMap, sub_sub, sub_eq_zero]
  exact Iff.rfl

/-- The substituted remainder of the zero sequence vanishes. -/
theorem remainderSeq_zero : Γ.remainderSeq 0 = 0 := by
  refine BoundedContinuousFunction.ext fun n => ?_
  have h : Γ.remainderSeq 0 n = Γ.r ((0 : SeqPair) n) := rfl
  rw [h]
  simp [Γ.r_zero]

/-- The base point solves the orbit equation. -/
theorem orbitEquationMap_base :
    Γ.orbitEquationMap ((0 : ℝ), (0 : SeqPair)) = 0 := by
  rw [orbitEquationMap]
  simp [Γ.remainderSeq_zero]

/-- The substituted remainder is `C¹` at every bounded sequence. -/
theorem remainderSeq_contDiffAt (x : SeqPair) :
    ContDiffAt ℝ 1 Γ.remainderSeq x :=
  substitutionMap_contDiffAt Γ.r_hasFDerivAt Γ.r_continuous Γ.r'_continuous x

/-- The diagonal derivative of the substituted remainder. -/
noncomputable def remainderDeriv (x : SeqPair) : SeqPair →L[ℝ] SeqPair :=
  substitutionDeriv Γ.r' Γ.r'_continuous x

/-- Differentiability of the substituted remainder. -/
theorem remainderSeq_hasFDerivAt (x : SeqPair) :
    HasFDerivAt Γ.remainderSeq (Γ.remainderDeriv x) x :=
  substitutionMap_hasFDerivAt Γ.r_hasFDerivAt Γ.r_continuous Γ.r'_continuous x

/-- The derivative of the orbit-equation map at second coordinate `x₀`. -/
noncomputable def orbitEquationDeriv (x₀ : SeqPair) :
    (ℝ × SeqPair) →L[ℝ] SeqPair :=
  ContinuousLinearMap.snd ℝ ℝ SeqPair
    - Γ.contractInjection.comp (ContinuousLinearMap.fst ℝ ℝ SeqPair)
    - Γ.green.comp ((Γ.remainderDeriv x₀).comp (ContinuousLinearMap.snd ℝ ℝ SeqPair))

/-- The orbit-equation map is differentiable, with the expected derivative. -/
theorem orbitEquationMap_hasFDerivAt (p : ℝ × SeqPair) :
    HasFDerivAt Γ.orbitEquationMap (Γ.orbitEquationDeriv p.2) p := by
  have h1 : HasFDerivAt (fun q : ℝ × SeqPair => q.2)
      (ContinuousLinearMap.snd ℝ ℝ SeqPair) p := hasFDerivAt_snd
  have h2 : HasFDerivAt (fun q : ℝ × SeqPair => Γ.contractInjection q.1)
      (Γ.contractInjection.comp (ContinuousLinearMap.fst ℝ ℝ SeqPair)) p :=
    Γ.contractInjection.hasFDerivAt.comp p hasFDerivAt_fst
  have hinner : HasFDerivAt (fun q : ℝ × SeqPair => Γ.remainderSeq q.2)
      ((Γ.remainderDeriv p.2).comp (ContinuousLinearMap.snd ℝ ℝ SeqPair)) p :=
    (Γ.remainderSeq_hasFDerivAt p.2).comp p hasFDerivAt_snd
  have h3 : HasFDerivAt (fun q : ℝ × SeqPair => Γ.green (Γ.remainderSeq q.2))
      (Γ.green.comp ((Γ.remainderDeriv p.2).comp
        (ContinuousLinearMap.snd ℝ ℝ SeqPair))) p :=
    Γ.green.hasFDerivAt.comp p hinner
  exact (h1.sub h2).sub h3

/-- The orbit-equation map is `C¹` at every point. -/
theorem orbitEquationMap_contDiffAt (p : ℝ × SeqPair) :
    ContDiffAt ℝ 1 Γ.orbitEquationMap p := by
  have h1 : ContDiffAt ℝ 1 (fun q : ℝ × SeqPair => q.2) p := contDiffAt_snd
  have h2 : ContDiffAt ℝ 1 (fun q : ℝ × SeqPair => Γ.contractInjection q.1) p :=
    Γ.contractInjection.contDiff.contDiffAt.comp p contDiffAt_fst
  have h3 : ContDiffAt ℝ 1 (fun q : ℝ × SeqPair => Γ.green (Γ.remainderSeq q.2)) p :=
    Γ.green.contDiff.contDiffAt.comp p
      ((Γ.remainderSeq_contDiffAt p.2).comp p contDiffAt_snd)
  exact (h1.sub h2).sub h3

/-- The recorded derivative is the Fréchet derivative. -/
theorem fderiv_orbitEquationMap (p : ℝ × SeqPair) :
    fderiv ℝ Γ.orbitEquationMap p = Γ.orbitEquationDeriv p.2 :=
  (Γ.orbitEquationMap_hasFDerivAt p).fderiv

/-! ## Base-point invertibility -/

/-- The diagonal derivative vanishes at the zero sequence. -/
theorem remainderDeriv_zero : Γ.remainderDeriv 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro h
  refine BoundedContinuousFunction.ext fun n => ?_
  have hl : Γ.remainderDeriv 0 h n = Γ.r' ((0 : SeqPair) n) (h n) := rfl
  rw [hl]
  simp [Γ.r'_zero]

/-- Restricted to the second slot, the derivative at `x₀` is
`id - S ∘ N'(x₀)`. -/
theorem orbitEquationDeriv_comp_inr (x₀ : SeqPair) :
    (Γ.orbitEquationDeriv x₀).comp (ContinuousLinearMap.inr ℝ ℝ SeqPair) =
      ContinuousLinearMap.id ℝ SeqPair - Γ.green.comp (Γ.remainderDeriv x₀) := by
  apply ContinuousLinearMap.ext
  intro x
  simp [orbitEquationDeriv]

/-- At the base point, the second-slot derivative is the identity. -/
theorem baseDeriv_comp_inr :
    (fderiv ℝ Γ.orbitEquationMap ((0 : ℝ), (0 : SeqPair))).comp
        (ContinuousLinearMap.inr ℝ ℝ SeqPair) =
      ContinuousLinearMap.id ℝ SeqPair := by
  rw [fderiv_orbitEquationMap, orbitEquationDeriv_comp_inr]
  rw [show ((0 : ℝ), (0 : SeqPair)).2 = (0 : SeqPair) from rfl,
    remainderDeriv_zero]
  rw [ContinuousLinearMap.comp_zero]
  exact sub_zero (ContinuousLinearMap.id ℝ SeqPair)

/-- The base invertibility hypothesis of the implicit function theorem. -/
theorem baseInvertible :
    ((fderiv ℝ Γ.orbitEquationMap ((0 : ℝ), (0 : SeqPair))).comp
      (ContinuousLinearMap.inr ℝ ℝ SeqPair)).IsInvertible := by
  rw [Γ.baseDeriv_comp_inr]
  exact ⟨ContinuousLinearEquiv.refl ℝ SeqPair, rfl⟩

/-! ## The implicit solution family -/

/-- The implicit solution family of the orbit equation: for each initial
contracting coordinate near zero, the unique small bounded orbit. -/
noncomputable def stableGraph : ℝ → SeqPair :=
  (Γ.orbitEquationMap_contDiffAt ((0 : ℝ), (0 : SeqPair))).implicitFunction
    one_ne_zero Γ.baseInvertible

/-- The graph passes through the origin. -/
theorem stableGraph_zero : Γ.stableGraph 0 = 0 :=
  ContDiffAt.implicitFunction_apply_self _ _ _

/-- The local two-sided characterization: near the base point, zeros of the
orbit equation are exactly the graph. -/
theorem stableGraph_iff :
    ∀ᶠ v : ℝ × SeqPair in 𝓝 ((0 : ℝ), (0 : SeqPair)),
      (Γ.orbitEquationMap v = 0 ↔ Γ.stableGraph v.1 = v.2) := by
  have h := ContDiffAt.eventually_apply_eq_iff_implicitFunction
    (Γ.orbitEquationMap_contDiffAt ((0 : ℝ), (0 : SeqPair)))
    one_ne_zero Γ.baseInvertible
  filter_upwards [h] with v hv
  rw [Γ.orbitEquationMap_base] at hv
  exact hv

/-- The graph solves the orbit equation near zero. -/
theorem stableGraph_solves :
    ∀ᶠ σ in 𝓝 (0 : ℝ), Γ.IsGreenSolution σ (Γ.stableGraph σ) := by
  have h := ContDiffAt.eventually_apply_implicitFunction
    (Γ.orbitEquationMap_contDiffAt ((0 : ℝ), (0 : SeqPair)))
    one_ne_zero Γ.baseInvertible
  filter_upwards [h] with σ hσ
  rw [Γ.orbitEquationMap_base] at hσ
  exact (Γ.orbitEquationMap_eq_zero_iff σ _).mp hσ

/-- The graph is `C¹` at zero. -/
theorem stableGraph_contDiffAt_zero : ContDiffAt ℝ 1 Γ.stableGraph 0 :=
  ContDiffAt.contDiffAt_implicitFunction _ _ _

/-- Tangency: the strict derivative of the graph at zero is the contracting
injection, i.e. the graph is tangent to the contracting eigendirection. -/
theorem stableGraph_hasStrictFDerivAt :
    HasStrictFDerivAt Γ.stableGraph Γ.contractInjection 0 := by
  have h := ContDiffAt.hasStrictFDerivAt_implicitFunction
    (Γ.orbitEquationMap_contDiffAt ((0 : ℝ), (0 : SeqPair)))
    one_ne_zero Γ.baseInvertible
  have hD : -((fderiv ℝ Γ.orbitEquationMap ((0 : ℝ), (0 : SeqPair))).comp
        (ContinuousLinearMap.inr ℝ ℝ SeqPair)).inverse ∘L
      ((fderiv ℝ Γ.orbitEquationMap ((0 : ℝ), (0 : SeqPair))).comp
        (ContinuousLinearMap.inl ℝ ℝ SeqPair)) = Γ.contractInjection := by
    rw [Γ.baseDeriv_comp_inr, ContinuousLinearMap.inverse_id,
      fderiv_orbitEquationMap]
    apply ContinuousLinearMap.ext
    intro t
    simp [orbitEquationDeriv, remainderDeriv_zero]
  rw [← hD]
  exact h

/-! ## Openness of the invertibility, and eventual `C¹`-ness -/

/-- The Neumann-series invertibility of `id - T` for a small operator. -/
theorem isInvertible_one_sub_of_small {T : SeqPair →L[ℝ] SeqPair}
    (hsmall : ‖T‖ < 1) :
    (ContinuousLinearMap.id ℝ SeqPair - T).IsInvertible := by
  let u : (SeqPair →L[ℝ] SeqPair)ˣ := Units.oneSub T hsmall
  have hval : (u : SeqPair →L[ℝ] SeqPair) =
      ContinuousLinearMap.id ℝ SeqPair - T := rfl
  refine ContinuousLinearMap.IsInvertible.of_inverse
    (g := ((u⁻¹ : (SeqPair →L[ℝ] SeqPair)ˣ) : SeqPair →L[ℝ] SeqPair)) ?_ ?_
  · have h := u.mul_inv
    rw [hval] at h
    exact h
  · have h := u.inv_mul
    rw [hval] at h
    exact h

/-- Near the zero sequence, the second-slot derivative of the orbit-equation
map is invertible, uniformly from smallness of the remainder derivative. -/
theorem derivInvertible_of_small {σ₀ : ℝ} {x₀ : SeqPair}
    (hsmall : ‖Γ.green.comp (Γ.remainderDeriv x₀)‖ < 1) :
    ((fderiv ℝ Γ.orbitEquationMap (σ₀, x₀)).comp
      (ContinuousLinearMap.inr ℝ ℝ SeqPair)).IsInvertible := by
  have h1 : fderiv ℝ Γ.orbitEquationMap (σ₀, x₀) = Γ.orbitEquationDeriv x₀ :=
    Γ.fderiv_orbitEquationMap (σ₀, x₀)
  rw [h1, orbitEquationDeriv_comp_inr]
  exact isInvertible_one_sub_of_small hsmall

/-- The graph is `C¹` on a neighborhood of zero, by re-running the implicit
function theorem at nearby base points and gluing through the base
uniqueness. -/
theorem stableGraph_eventually_contDiffAt :
    ∀ᶠ σ in 𝓝 (0 : ℝ), ContDiffAt ℝ 1 Γ.stableGraph σ := by
  -- smallness radius for the remainder derivative
  have hεpos : (0 : ℝ) < (2 * (‖Γ.green‖ + 1))⁻¹ := by positivity
  have hcont : ContinuousAt Γ.r' 0 := Γ.r'_continuous.continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨ρ₀, hρ₀pos, hρ₀⟩ := hcont ((2 * (‖Γ.green‖ + 1))⁻¹) hεpos
  have hbound : ∀ x₀ : SeqPair, ‖x₀‖ < ρ₀ →
      ‖Γ.green.comp (Γ.remainderDeriv x₀)‖ < 1 := by
    intro x₀ hx₀
    have hD : ‖Γ.remainderDeriv x₀‖ ≤ (2 * (‖Γ.green‖ + 1))⁻¹ := by
      apply substitutionDeriv_opNorm_le _ _ _ hεpos.le
      intro n
      have hz : dist (x₀ n) 0 < ρ₀ :=
        lt_of_le_of_lt (by simpa [dist_zero_right] using x₀.norm_coe_le_norm n) hx₀
      have := hρ₀ hz
      rw [Γ.r'_zero, dist_zero_right] at this
      exact this.le
    calc ‖Γ.green.comp (Γ.remainderDeriv x₀)‖
        ≤ ‖Γ.green‖ * ‖Γ.remainderDeriv x₀‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖Γ.green‖ * (2 * (‖Γ.green‖ + 1))⁻¹ :=
          mul_le_mul_of_nonneg_left hD (norm_nonneg Γ.green)
      _ < 1 := by
          rw [mul_inv_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg Γ.green]
  -- the base uniqueness neighborhood, as an open set
  obtain ⟨U, hU, hUiff⟩ := eventually_iff_exists_mem.mp Γ.stableGraph_iff
  obtain ⟨O, hOU, hOopen, hO0⟩ := _root_.mem_nhds_iff.mp hU
  -- the graph is continuous at zero and passes through the origin
  have hψc0 : ContinuousAt Γ.stableGraph 0 :=
    Γ.stableGraph_contDiffAt_zero.continuousAt
  have hpair : ContinuousAt (fun σ : ℝ => (σ, Γ.stableGraph σ)) 0 :=
    continuousAt_id.prodMk hψc0
  have hO0' : ((0 : ℝ), Γ.stableGraph 0) ∈ O := by
    rw [Γ.stableGraph_zero]; exact hO0
  have hOpre : ∀ᶠ σ in 𝓝 (0 : ℝ), (σ, Γ.stableGraph σ) ∈ O := by
    have hmem : O ∈ 𝓝 ((0 : ℝ), Γ.stableGraph 0) := hOopen.mem_nhds hO0'
    exact hpair hmem
  have hψsmall : ∀ᶠ σ in 𝓝 (0 : ℝ), ‖Γ.stableGraph σ‖ < ρ₀ := by
    have hmem : Metric.ball (0 : SeqPair) ρ₀ ∈ 𝓝 (Γ.stableGraph 0) := by
      rw [Γ.stableGraph_zero]
      exact Metric.ball_mem_nhds _ hρ₀pos
    filter_upwards [hψc0 hmem] with σ hσ
    simpa [mem_ball, dist_zero_right] using hσ
  filter_upwards [hOpre, hψsmall] with σ₀ hσO hσsmall
  -- rerun the implicit function theorem at the nearby base point
  have hfu' : Γ.orbitEquationMap (σ₀, Γ.stableGraph σ₀) = 0 :=
    (hUiff _ (hOU hσO)).mpr rfl
  have hinv' : ((fderiv ℝ Γ.orbitEquationMap (σ₀, Γ.stableGraph σ₀)).comp
      (ContinuousLinearMap.inr ℝ ℝ SeqPair)).IsInvertible :=
    Γ.derivInvertible_of_small (hbound _ hσsmall)
  set ψ₂ := (Γ.orbitEquationMap_contDiffAt (σ₀, Γ.stableGraph σ₀)).implicitFunction
    one_ne_zero hinv' with hψ₂def
  have hψ₂c : ContDiffAt ℝ 1 ψ₂ σ₀ :=
    ContDiffAt.contDiffAt_implicitFunction _ _ _
  have hψ₂self : ψ₂ σ₀ = Γ.stableGraph σ₀ :=
    ContDiffAt.implicitFunction_apply_self _ _ _
  have hψ₂ev : ∀ᶠ σ in 𝓝 σ₀, Γ.orbitEquationMap (σ, ψ₂ σ) = 0 := by
    have h := ContDiffAt.eventually_apply_implicitFunction
      (Γ.orbitEquationMap_contDiffAt (σ₀, Γ.stableGraph σ₀)) one_ne_zero hinv'
    filter_upwards [h] with σ hσ
    rw [hfu'] at hσ
    exact hσ
  have hψ₂O : ∀ᶠ σ in 𝓝 σ₀, (σ, ψ₂ σ) ∈ O := by
    have hc : ContinuousAt (fun σ : ℝ => (σ, ψ₂ σ)) σ₀ :=
      continuousAt_id.prodMk hψ₂c.continuousAt
    have hmem : O ∈ 𝓝 (σ₀, ψ₂ σ₀) := by
      rw [hψ₂self]
      exact hOopen.mem_nhds hσO
    exact hc hmem
  have heq : Γ.stableGraph =ᶠ[𝓝 σ₀] ψ₂ := by
    filter_upwards [hψ₂ev, hψ₂O] with σ h1 h2
    exact (hUiff _ (hOU h2)).mp h1
  exact hψ₂c.congr_of_eventuallyEq heq

end PlanarHyperbolicGerm
end PaperII
end CivicAlignment

#print axioms CivicAlignment.PaperII.PlanarHyperbolicGerm.stableGraph_iff
#print axioms CivicAlignment.PaperII.PlanarHyperbolicGerm.stableGraph_hasStrictFDerivAt
#print axioms CivicAlignment.PaperII.PlanarHyperbolicGerm.stableGraph_eventually_contDiffAt
