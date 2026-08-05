/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.InflatedBox

/-!
# Paper III: zone (A)'s gradient-loop clause

`thm:zones`(A) splits three ways.  The scalar half (`v ≥ F_max ⇒ G_g ≤ 0`) and
the all-rule half (global calibration under the knob-free certificate, via
`thm:cert`) are already proved.  The third is the dynamical one: for the
gradient loop itself, `(SS_g^+)` together with the *strict* inequality
`v > F_max` suffices.

That clause was blocked on the `ε`-inflation bridge, because it quantifies over
every orbit rather than every orbit in `B`.  With
`globalConvergence_of_nonnegative_stock` the argument is short: every orbit from
nonnegative stock converges to *some* loop equilibrium, and the sign catalogue
leaves only the calibrated corner once `G_g` is strictly negative throughout.
-/

namespace CivicAlignment.PaperIII

open Filter Set Topology

noncomputable section

variable {p : LoopParams}

/-- Zone (A) with the strict inequality `v > F_max` that the dynamic clause uses. -/
def StrictCalibrationZone (p : LoopParams) : Prop :=
  ∀ β ∈ Icc (0 : ℝ) 1, zoneForce p β < p.v

/-- The strict zone is a zone. -/
theorem CalibrationZone.of_strict (hzone : StrictCalibrationZone p) :
    CalibrationZone p := fun β hβ => (hzone β hβ).le

/-- In the strict zone the stationary gradient is strictly negative throughout. -/
theorem strictCalibrationZone_stationaryGradient_neg
    (hzone : StrictCalibrationZone p) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    p.G β < 0 := by
  rw [G_eq_neg_v_add_zoneForce]
  linarith [hzone β hβ]

/--
In the strict zone the calibrated corner is the only loop equilibrium: the
interior case needs a vanishing stationary gradient and the captured corner
needs a nonnegative one, and both are excluded.
-/
theorem strictCalibrationZone_equilibrium_eq_calibrated
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hzone : StrictCalibrationZone p) {β D : ℝ}
    (hequilibrium : IsLoopEquilibrium p β D) :
    β = 0 ∧ D = p.stationaryStock 0 := by
  rcases (loopEquilibrium_iff_stationary_sign_catalogue model hgain β D).1
    hequilibrium with ⟨hβ, hD, _⟩ | ⟨hβ, _, hG⟩ | ⟨hβ, _, hG⟩
  · exact ⟨hβ, hD⟩
  · exact absurd hG
      (strictCalibrationZone_stationaryGradient_neg hzone
        ⟨hβ.1.le, hβ.2.le⟩).ne
  · exact absurd hG
      (not_le.mpr (by
        simpa only [hβ] using
          strictCalibrationZone_stationaryGradient_neg hzone
            (right_mem_Icc.mpr zero_le_one)))

/--
Paper III, `thm:zones`(A), gradient-loop clause (`civic_loops.tex:287`).  Under
`(SS_g^+)` and the strict zone-(A) inequality `v > F_max`, every orbit of the
simultaneous loop from arbitrary nonnegative stock converges to the calibrated
corner.  No step-size condition beyond `(SS_g^+)` and no restriction to `B`.
-/
theorem strictCalibrationZone_globalCalibration
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (ssplus : ConvergentStepAssumption p) (hzone : StrictCalibrationZone p)
    {x : ℕ → LoopState} (traj : IsLoopOrbit p x)
    (hβ₀ : (x 0).1 ∈ Icc (0 : ℝ) 1) (hD₀ : 0 ≤ (x 0).2) :
    Tendsto x atTop (𝓝 ((0 : ℝ), p.stationaryStock 0)) := by
  obtain ⟨q, hlim, hq⟩ :=
    globalConvergence_of_nonnegative_stock model hgain ssplus traj hβ₀ hD₀
  obtain ⟨hβ, hD⟩ :=
    strictCalibrationZone_equilibrium_eq_calibrated model hgain hzone hq
  have : q = ((0 : ℝ), p.stationaryStock 0) := Prod.ext hβ hD
  rwa [this] at hlim

/--
The knob-free certificate with a strictly positive margin puts the loop in the
strict zone, so `thm:cert`'s hypothesis also delivers the gradient-loop
conclusion without any appeal to sign-consistency or responsiveness.
-/
theorem strictCalibrationZone_of_strict_certificate
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hmargin : 0 < certificateMargin p) :
    StrictCalibrationZone p := by
  intro β hβ
  have hgap : 0 < p.lambda₀ - p.g := sub_pos.mpr hgain
  have hforce := zoneForce_le_policyFreeBound model hgain hβ
  have hbound : 2 * p.c * p.I / (p.lambda₀ - p.g) < p.v := by
    apply (div_lt_iff₀ hgap).2
    simp only [certificateMargin] at hmargin
    nlinarith
  exact hforce.trans_lt hbound

#print axioms strictCalibrationZone_stationaryGradient_neg
#print axioms strictCalibrationZone_equilibrium_eq_calibrated
#print axioms strictCalibrationZone_globalCalibration
#print axioms strictCalibrationZone_of_strict_certificate

end

end CivicAlignment.PaperIII
