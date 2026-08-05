/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.Bistability

/-!
# Paper II: a global stationary-gradient condition for civic weighting

`thm:hyst` (`civic_drift.tex:296--324`) concludes that a transient civic weight
`ρ > ρ_cure` *cures*.  What its argument establishes is that the captured corner
stops being a fixed point — outward motion from `β = 1`.  Convergence to the
*calibrated* corner additionally requires ruling out weighted interior
equilibria, which does not follow from (SS) and (H).

This file supplies a missing stationary condition, sharper than a crude box bound. Along
the stationary characteristic the weighted gradient is negative exactly when `ρ`
exceeds

  `Ψ(β) := 2c(1-cβ) - v(1-s β)/I`,

and `Ψ(1) = ρ_cure`.  So the paper's claim is correct precisely when `Ψ` attains
its maximum at `β = 1`.  An explicit checkable sufficient condition is

  `c²I < vη(1-λ₀)(1-η)`,

under which `Ψ` is monotone, `max Ψ = ρ_cure`, and every `ρ > ρ_cure` leaves no
interior weighted equilibrium. This rules out one obstruction to cure; it does
not by itself prove convergence of the weighted two-dimensional dynamics.
-/

namespace CivicAlignment.PaperII

open Set

noncomputable section

/-- The weight at which the civic-weighted gradient vanishes on the stationary
characteristic at policy `β` — `ρ_cure` generalized off the corner. -/
def weightedCureThreshold (p : LoopParams) (β : ℝ) : ℝ :=
  2 * p.c * (1 - p.c * β) - p.v * (1 - p.s β) / p.I

/-- The explicit sufficient condition making `ρ_cure` the *global* cure price. -/
structure CureDominance (p : LoopParams) : Prop where
  bound : p.c ^ 2 * p.I < p.v * p.η * (1 - p.lambda₀) * (1 - p.η)

section

variable {p : LoopParams}

/-- **`ρ_cure` is `Ψ` at the captured corner.** -/
theorem weightedCureThreshold_one : weightedCureThreshold p 1 = cureThreshold p := by
  have hs : p.s 1 = 1 - p.lambda₀ := by
    simp only [LoopParams.s]; ring
  simp only [weightedCureThreshold, cureThreshold, hs]
  ring_nf

/-- The stock multiplier increments at least linearly in the policy. -/
theorem stockMultiplier_increment_lower (model : DriftModelAssumptions p)
    {β₁ β₂ : ℝ} (h₁ : 0 ≤ β₁) (h₂ : β₁ ≤ β₂) :
    2 * p.η * (1 - p.lambda₀) * (1 - p.η) * (β₂ - β₁) ≤ p.s β₂ - p.s β₁ := by
  have hη := model.η_pos
  have hlam := model.lambda₀_lt_one
  have hgap : 0 ≤ β₂ - β₁ := sub_nonneg.mpr h₂
  have hbase : (0 : ℝ) ≤ 1 - p.lambda₀ := by linarith
  have hu₁ : 1 - p.η ≤ 1 - p.η * (1 - β₁) := by nlinarith
  have hu₂ : 1 - p.η ≤ 1 - p.η * (1 - β₂) := by nlinarith
  have hfactor : p.s β₂ - p.s β₁
      = (1 - p.lambda₀) * (p.η * (β₂ - β₁))
        * ((1 - p.η * (1 - β₂)) + (1 - p.η * (1 - β₁))) := by
    simp only [LoopParams.s]; ring
  have hK : 0 ≤ (1 - p.lambda₀) * (p.η * (β₂ - β₁)) :=
    mul_nonneg hbase (mul_nonneg hη.le hgap)
  have hsum : 2 * (1 - p.η)
      ≤ (1 - p.η * (1 - β₂)) + (1 - p.η * (1 - β₁)) := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hsum hK
  rw [hfactor]
  nlinarith [hscaled]

/-- **`Ψ` is monotone under `CureDominance`.** -/
theorem weightedCureThreshold_mono (model : DriftModelAssumptions p)
    (dom : CureDominance p) {β₁ β₂ : ℝ} (h₁ : 0 ≤ β₁) (h₂ : β₁ ≤ β₂) :
    weightedCureThreshold p β₁ ≤ weightedCureThreshold p β₂ := by
  have hI := model.I_pos
  have hv := model.v_pos
  have hincr := stockMultiplier_increment_lower model h₁ h₂
  have hgap : 0 ≤ β₂ - β₁ := sub_nonneg.mpr h₂
  have hstep : 2 * p.c ^ 2 * (β₂ - β₁) ≤ p.v * (p.s β₂ - p.s β₁) / p.I := by
    rw [le_div_iff₀ hI]
    nlinarith [dom.bound, hincr, hgap, hv, hI]
  have hexpand : p.v * (1 - p.s β₂) / p.I
      = p.v * (1 - p.s β₁) / p.I - p.v * (p.s β₂ - p.s β₁) / p.I := by
    field_simp
    ring
  simp only [weightedCureThreshold]
  rw [hexpand]
  nlinarith [hstep]

/-- **`max Ψ = ρ_cure`.** Under `CureDominance` the captured corner is where the
weighted gradient is hardest to sign, so the corner threshold is the global one. -/
theorem weightedCureThreshold_le_cureThreshold (model : DriftModelAssumptions p)
    (dom : CureDominance p) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    weightedCureThreshold p β ≤ cureThreshold p := by
  rw [← weightedCureThreshold_one (p := p)]
  exact weightedCureThreshold_mono model dom hβ.1 hβ.2

/--
**The global negative-gradient property.** Under `CureDominance`, every civic
weight above `ρ_cure` makes the weighted gradient strictly negative along the
whole stationary characteristic, so there is no weighted interior equilibrium.
A separate dynamical argument would still be needed to prove convergence to the
calibrated corner.
-/
theorem civicWeightedGradient_stationary_neg (model : DriftModelAssumptions p)
    (dom : CureDominance p) {ρ β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1)
    (hρ : cureThreshold p < ρ) :
    civicWeightedGradient p ρ β (p.stationaryStock β) < 0 := by
  have hI := model.I_pos
  have hs := driftStockMultiplier_nonneg_le model hβ
  have hden : 0 < 1 - p.s β := by linarith [hs.2, model.lambda₀_pos]
  have hDpos : 0 < p.stationaryStock β := by
    simp only [LoopParams.stationaryStock, model.no_content_gain, sub_zero]
    exact div_pos hI hden
  have hΨ : weightedCureThreshold p β < ρ :=
    lt_of_le_of_lt (weightedCureThreshold_le_cureThreshold model dom hβ) hρ
  have hvalue : p.v / p.stationaryStock β = p.v * (1 - p.s β) / p.I := by
    simp only [LoopParams.stationaryStock, model.no_content_gain, sub_zero]
    rw [div_div_eq_mul_div]
  have hlt : 2 * p.c * (1 - p.c * β) - ρ < p.v / p.stationaryStock β := by
    rw [hvalue]
    simp only [weightedCureThreshold] at hΨ
    linarith [hΨ]
  have hprod : (2 * p.c * (1 - p.c * β) - ρ) * p.stationaryStock β < p.v :=
    (lt_div_iff₀ hDpos).mp hlt
  simp only [civicWeightedGradient, LoopParams.gradU]
  nlinarith [hprod]

end

#print axioms weightedCureThreshold_one
#print axioms stockMultiplier_increment_lower
#print axioms weightedCureThreshold_mono
#print axioms weightedCureThreshold_le_cureThreshold
#print axioms civicWeightedGradient_stationary_neg

end

end CivicAlignment.PaperII
