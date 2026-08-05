/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.DescendingStability

/-!
# Paper III: the interior spectrum of `thm:classify`

`thm:classify` reads stability off the sign of `G_g'` at an interior root.  The
descending branch is settled in `DescendingStability.lean`.  This file supplies
the ascending branch — a transversal ascending crossing is a saddle — by
instantiating Paper II's generic planar-Jacobian eigenvalue API at Paper III's
interior fixed point, so the two papers share one spectral development rather
than two.

The asymmetry between the branches is the one recorded in `thm:classify`: the
proviso `2η(1-λ₀) ≤ c(1+s(0)+g)` is needed here and only here.
-/

namespace CivicAlignment.PaperIII

open Set

noncomputable section

variable {p : LoopParams}

/-- Paper III's interior Jacobian, as an instance of Paper II's planar API. -/
def loopJacobianAt (p : LoopParams) (β D : ℝ) : PaperII.LoopJacobian where
  a := 1 - 2 * p.α * p.c ^ 2 * D
  b := 2 * p.α * p.c * (1 - p.c * β)
  cJ := p.sSlope β * D
  d := p.s β + p.g

theorem loopJacobianAt_charPoly_one (p : LoopParams) (β D : ℝ) :
    (loopJacobianAt p β D).charPoly 1 = p.jacobianPAtOne β D := by
  simp only [loopJacobianAt, PaperII.LoopJacobian.charPoly, PaperII.LoopJacobian.trace,
    PaperII.LoopJacobian.det, LoopParams.jacobianPAtOne]
  ring

theorem loopJacobianAt_charPoly_negOne (p : LoopParams) (β D : ℝ) :
    (loopJacobianAt p β D).charPoly (-1) = p.jacobianPAtNegOne β D := by
  simp only [loopJacobianAt, PaperII.LoopJacobian.charPoly, PaperII.LoopJacobian.trace,
    PaperII.LoopJacobian.det, LoopParams.jacobianPAtNegOne]
  ring

/-- On the box the off-diagonal product is nonnegative, so the spectrum is real. -/
theorem loopJacobianAt_offDiagonal_nonneg (model : LoopModelAssumptions p)
    {β D : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) (hD : 0 ≤ D) :
    0 ≤ (loopJacobianAt p β D).b * (loopJacobianAt p β D).cJ := by
  have hb : 0 ≤ 2 * p.α * p.c * (1 - p.c * β) := by
    have : p.c * β ≤ 1 := by nlinarith [model.c_pos, model.c_lt_one, hβ.1, hβ.2]
    have h2 : 0 ≤ 2 * p.α * p.c :=
      mul_nonneg (mul_nonneg two_pos.le model.α_pos.le) model.c_pos.le
    exact mul_nonneg h2 (by linarith)
  have hs : 0 ≤ p.sSlope β := by
    simp only [LoopParams.sSlope]
    have : 0 ≤ 1 - p.η * (1 - β) := by nlinarith [model.η_pos, model.η_lt_one, hβ.1, hβ.2]
    have h2 : 0 ≤ 2 * p.η * (1 - p.lambda₀) :=
      mul_nonneg (mul_nonneg two_pos.le model.η_pos.le)
        (sub_nonneg.mpr model.lambda₀_lt_one.le)
    exact mul_nonneg h2 this
  exact mul_nonneg hb (mul_nonneg hs hD)

theorem loopJacobianAt_discriminant_nonneg (model : LoopModelAssumptions p)
    {β D : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) (hD : 0 ≤ D) :
    0 ≤ (loopJacobianAt p β D).discriminant := by
  have := loopJacobianAt_offDiagonal_nonneg model hβ hD
  simp only [PaperII.LoopJacobian.discriminant]
  nlinarith [sq_nonneg ((loopJacobianAt p β D).a - (loopJacobianAt p β D).d)]

/-- The stock row's diagonal entry is below one off the divergence wall. -/
theorem loopJacobianAt_d_lt_one (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β D : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    (loopJacobianAt p β D).d < 1 := by
  have hs := stockMultiplier_nonneg_le model hβ
  simp only [loopJacobianAt]
  linarith [hs.2]

/--
The eigenvalue proviso of `thm:classify`, in force.  Under `(SS_g)` on the box
and `2η(1-λ₀) ≤ c(1+s(0)+g)`, the characteristic polynomial is positive at `-1`,
which is what keeps the saddle's second eigenvalue above `-1`.
-/
theorem jacobianPAtNegOne_pos_of_proviso (model : LoopModelAssumptions p)
    (_hgain : p.g < p.lambda₀) {β D : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1)
    (_hD : 0 ≤ D) (hstep : 2 * p.α * p.c ^ 2 * D < 1)
    (hproviso : 2 * p.η * (1 - p.lambda₀) ≤ p.c * (1 + p.s 0 + p.g)) :
    0 < p.jacobianPAtNegOne β D := by
  have hs := stockMultiplier_nonneg_le model hβ
  have hs0 : p.s 0 ≤ p.s β :=
    (stockMultiplier_strictMonoOn model).monotoneOn ⟨le_rfl, zero_le_one⟩ hβ hβ.1
  have hcβ0 : 0 ≤ 1 - p.c * β := by nlinarith [model.c_pos, model.c_lt_one, hβ.2]
  have hcβ1 : 1 - p.c * β ≤ 1 := by nlinarith [model.c_pos, hβ.1]
  have hsSlope0 : 0 ≤ p.sSlope β := by
    simp only [LoopParams.sSlope]
    have hinner : 0 ≤ 1 - p.η * (1 - β) := by
      nlinarith [model.η_pos, model.η_lt_one, hβ.1, hβ.2]
    have h2 : 0 ≤ 2 * p.η * (1 - p.lambda₀) :=
      mul_nonneg (mul_nonneg two_pos.le model.η_pos.le)
        (sub_nonneg.mpr model.lambda₀_lt_one.le)
    exact mul_nonneg h2 hinner
  have hsSlope1 : p.sSlope β ≤ 2 * p.η * (1 - p.lambda₀) := by
    simp only [LoopParams.sSlope]
    have hinner : 1 - p.η * (1 - β) ≤ 1 := by nlinarith [model.η_pos, hβ.2]
    have h2 : 0 ≤ 2 * p.η * (1 - p.lambda₀) :=
      mul_nonneg (mul_nonneg two_pos.le model.η_pos.le)
        (sub_nonneg.mpr model.lambda₀_lt_one.le)
    nlinarith
  -- the cross term, factored so the step condition applies to a single factor
  have hfactor : p.c * (2 * p.α * p.c * (1 - p.c * β) * (p.sSlope β * D))
      = (1 - p.c * β) * p.sSlope β * (2 * p.α * p.c ^ 2 * D) := by ring
  have hcross : p.c * (2 * p.α * p.c * (1 - p.c * β) * (p.sSlope β * D))
      ≤ p.c * (1 + p.s 0 + p.g) := by
    rw [hfactor]
    calc (1 - p.c * β) * p.sSlope β * (2 * p.α * p.c ^ 2 * D)
        ≤ (1 - p.c * β) * p.sSlope β * 1 :=
          mul_le_mul_of_nonneg_left hstep.le (mul_nonneg hcβ0 hsSlope0)
      _ = (1 - p.c * β) * p.sSlope β := mul_one _
      _ ≤ 1 * (2 * p.η * (1 - p.lambda₀)) :=
          mul_le_mul hcβ1 hsSlope1 hsSlope0 zero_le_one
      _ = 2 * p.η * (1 - p.lambda₀) := one_mul _
      _ ≤ p.c * (1 + p.s 0 + p.g) := hproviso
  have hbc : 2 * p.α * p.c * (1 - p.c * β) * (p.sSlope β * D) ≤ 1 + p.s 0 + p.g :=
    le_of_mul_le_mul_left (by linarith [hcross]) model.c_pos
  -- the strict step condition makes the diagonal product strictly larger
  have hapos : 0 < 1 - 2 * p.α * p.c ^ 2 * D := by linarith
  have hdiag : 1 + p.s 0 + p.g <
      (1 + (1 - 2 * p.α * p.c ^ 2 * D)) * (1 + (p.s β + p.g)) := by
    nlinarith [hs.1, model.g_nonneg, hs0, hapos]
  simp only [LoopParams.jacobianPAtNegOne]
  linarith [hbc, hdiag]

/--
Paper III, `thm:classify`, ascending branch: at a transversal ascending crossing
inside the box the interior fixed point is a saddle — the Perron eigenvalue
exceeds one and the second lies strictly inside the unit circle.  The proviso is
used only for the lower bound, exactly as the paper states.
-/
theorem ascendingCrossing_saddle (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β D : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) (hD : 0 ≤ D)
    (hstep : 2 * p.α * p.c ^ 2 * D < 1)
    (hproviso : 2 * p.η * (1 - p.lambda₀) ≤ p.c * (1 + p.s 0 + p.g))
    (hascending : p.jacobianPAtOne β D < 0) :
    1 < (loopJacobianAt p β D).largerEigenvalue ∧
      (loopJacobianAt p β D).smallerEigenvalue ∈ Ioo (-1 : ℝ) 1 := by
  have hbc := loopJacobianAt_offDiagonal_nonneg model hβ hD
  have hdisc := loopJacobianAt_discriminant_nonneg model hβ hD
  have hd := loopJacobianAt_d_lt_one model hgain (D := D) hβ
  have hsmall_lt := PaperII.LoopJacobian.smallerEigenvalue_lt_one _ hd hbc
  have hone : (loopJacobianAt p β D).charPoly 1 < 0 := by
    rw [loopJacobianAt_charPoly_one]; exact hascending
  have hlarge : 1 < (loopJacobianAt p β D).largerEigenvalue :=
    (PaperII.LoopJacobian.largerEigenvalue_gt_one_iff_charPoly_one_neg _ hdisc
      hsmall_lt).2 hone
  have hnegone : 0 < (loopJacobianAt p β D).charPoly (-1) := by
    rw [loopJacobianAt_charPoly_negOne]
    exact jacobianPAtNegOne_pos_of_proviso model hgain hβ hD hstep hproviso
  exact ⟨hlarge, PaperII.LoopJacobian.smallerEigenvalue_gt_neg_one_of_charPoly_neg_one_pos
    _ hdisc (by linarith) hnegone, hsmall_lt⟩

#print axioms loopJacobianAt_charPoly_one
#print axioms loopJacobianAt_charPoly_negOne
#print axioms jacobianPAtNegOne_pos_of_proviso
#print axioms ascendingCrossing_saddle

end

end CivicAlignment.PaperIII
