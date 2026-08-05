/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.Classification

/-!
# Papers II--III: descending crossings are stable without the eigenvalue proviso

`thm:classify` reads its stability catalogue off the sign of `G_g'` at an
interior root, "provided additionally `2η(1-λ₀) ≤ c(1+s(0)+g)`".  That proviso
is attached to both branches.  This file shows it is needed only for the
*ascending* branch: at a transversal *descending* crossing it is redundant,
because `(SS_g)` already forces its conclusion.

The mechanism is the exact identity, complementing `jacobianPAtOne` in
`Basic.lean`,

  `p(-1) = 2 (1 + s + g - u) + p(1)`,   `u := 2 α c² D`,

so at a descending crossing (`p(1) > 0`) the step condition `u < 1` alone gives
`p(-1) > 0`.  With the trace bound this places both eigenvalues in `(-1, 1)`,
which is exactly the local-attractor conclusion of `thm:zones`(B).

The proviso is not removable on the ascending branch: Paper II's period-two
witness satisfies `(SS)` strictly yet has `p(-1) < 0` at its saddle.
-/

namespace CivicAlignment

noncomputable section

namespace LoopParams

/-- The interior loop Jacobian's characteristic polynomial evaluated at `-1`. -/
def jacobianPAtNegOne (p : LoopParams) (β D : ℝ) : ℝ :=
  let a := 1 - 2 * p.α * p.c ^ 2 * D
  let b := 2 * p.α * p.c * (1 - p.c * β)
  let cJ := p.sSlope β * D
  let d := p.s β + p.g
  (1 + a) * (1 + d) - b * cJ

/--
The exact link between the two endpoint values of the characteristic
polynomial: `p(-1) - p(1) = 2(a + d)`, in the model's coordinates.
-/
theorem jacobianPAtNegOne_eq_add (p : LoopParams) (β D : ℝ) :
    p.jacobianPAtNegOne β D =
      2 * (1 + p.s β + p.g - 2 * p.α * p.c ^ 2 * D) + p.jacobianPAtOne β D := by
  simp only [jacobianPAtNegOne, jacobianPAtOne]
  ring

/--
At a transversal descending crossing the step condition alone keeps the
characteristic polynomial positive at `-1`: no eigenvalue proviso is needed.
-/
theorem jacobianPAtNegOne_pos_of_descending (p : LoopParams) {β D : ℝ}
    (hstep : 2 * p.α * p.c ^ 2 * D < 1) (hs : 0 ≤ p.s β) (hg : 0 ≤ p.g)
    (hp1 : 0 < p.jacobianPAtOne β D) :
    0 < p.jacobianPAtNegOne β D := by
  rw [jacobianPAtNegOne_eq_add]
  linarith

end LoopParams

namespace PaperIII

open Set

/--
A real root of `λ² - Tλ + Δ` lies in `(-1, 1)` as soon as the polynomial is
positive at both endpoints and the trace lies in `(0, 2)`.  This is the Jury
criterion in the only form the loop needs.
-/
theorem root_mem_Ioo_of_endpoints_pos {T Δ lam : ℝ}
    (hT₀ : 0 < T) (hT₂ : T < 2)
    (hone : 0 < 1 - T + Δ) (hnegone : 0 < 1 + T + Δ)
    (hroot : lam ^ 2 - T * lam + Δ = 0) :
    lam ∈ Ioo (-1 : ℝ) 1 := by
  have hΔ : Δ = T * lam - lam ^ 2 := by linarith
  constructor
  · rcases lt_or_ge (-1 : ℝ) lam with h | h
    · exact h
    · exfalso
      have hfac : 1 + T + Δ = (1 + lam) * (1 + (T - lam)) := by rw [hΔ]; ring
      have hpos : 0 < (1 + lam) * (1 + (T - lam)) := hfac ▸ hnegone
      nlinarith [hpos, h, hT₀]
  · rcases lt_or_ge lam (1 : ℝ) with h | h
    · exact h
    · exfalso
      have hfac : 1 - T + Δ = (1 - lam) * (1 - (T - lam)) := by rw [hΔ]; ring
      have hpos : 0 < (1 - lam) * (1 - (T - lam)) := hfac ▸ hone
      nlinarith [hpos, h, hT₂]

/--
Paper III, the local-attractor half of `thm:zones`(B): at a transversal
descending crossing inside the cooperative box, both Jacobian eigenvalues lie
strictly inside the unit circle under `(SS_g)` alone.  `thm:classify`'s
eigenvalue proviso is not required on this branch.
-/
theorem descendingCrossing_eigenvalues_mem_Ioo {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {β D lam : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) (hD : 0 < D)
    (hstep : 2 * p.α * p.c ^ 2 * D < 1)
    (hp1 : 0 < p.jacobianPAtOne β D)
    (hroot : lam ^ 2 - (1 - 2 * p.α * p.c ^ 2 * D + (p.s β + p.g)) * lam
        + ((1 - 2 * p.α * p.c ^ 2 * D) * (p.s β + p.g)
          - 2 * p.α * p.c * (1 - p.c * β) * (p.sSlope β * D)) = 0) :
    lam ∈ Ioo (-1 : ℝ) 1 := by
  have hsbound := stockMultiplier_nonneg_le model hβ
  have hu : 0 < 2 * p.α * p.c ^ 2 * D :=
    mul_pos (mul_pos (mul_pos two_pos model.α_pos) (pow_pos model.c_pos 2)) hD
  have hT₀ : 0 < 1 - 2 * p.α * p.c ^ 2 * D + (p.s β + p.g) := by
    linarith [hsbound.1, model.g_nonneg]
  have hT₂ : 1 - 2 * p.α * p.c ^ 2 * D + (p.s β + p.g) < 2 := by
    linarith [hsbound.2, hgain, model.lambda₀_pos]
  have hpm1 := p.jacobianPAtNegOne_pos_of_descending hstep hsbound.1
    model.g_nonneg hp1
  refine root_mem_Ioo_of_endpoints_pos hT₀ hT₂ ?_ ?_ hroot
  · have heq : 1 - (1 - 2 * p.α * p.c ^ 2 * D + (p.s β + p.g))
        + ((1 - 2 * p.α * p.c ^ 2 * D) * (p.s β + p.g)
          - 2 * p.α * p.c * (1 - p.c * β) * (p.sSlope β * D))
        = p.jacobianPAtOne β D := by
      simp only [LoopParams.jacobianPAtOne]; ring
    rw [heq]; exact hp1
  · have heq : 1 + (1 - 2 * p.α * p.c ^ 2 * D + (p.s β + p.g))
        + ((1 - 2 * p.α * p.c ^ 2 * D) * (p.s β + p.g)
          - 2 * p.α * p.c * (1 - p.c * β) * (p.sSlope β * D))
        = p.jacobianPAtNegOne β D := by
      simp only [LoopParams.jacobianPAtNegOne]; ring
    rw [heq]; exact hpm1

#print axioms LoopParams.jacobianPAtNegOne_eq_add
#print axioms LoopParams.jacobianPAtNegOne_pos_of_descending
#print axioms root_mem_Ioo_of_endpoints_pos
#print axioms descendingCrossing_eigenvalues_mem_Ioo

end PaperIII

end

end CivicAlignment
