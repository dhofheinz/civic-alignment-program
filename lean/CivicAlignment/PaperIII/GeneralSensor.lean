/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.Observability

/-!
# Paper III: arbitrary auxiliary sensors on the captured face

The paper displays one unweighted-error audit sensor.  The linear conclusion
depends only on its coordinate sensitivities: any auxiliary sensor with a
nonzero low-coordinate loading sees the hidden unstable mode, and it restores
rank two whenever captured satisfaction retains a nonzero healthy loading.
At the healthy-zero boundary, one auxiliary scalar sensor can still restore
rank two when it loads on both coordinates and the diagonal rates differ.
-/

namespace CivicAlignment.PaperIII

open Matrix

/-- Captured satisfaction stacked with an arbitrary auxiliary scalar sensor. -/
def capturedAuxiliarySensorObservability
    (piH kappa xH sensorH sensorL aH aL : ℝ) :
    Matrix (Fin 4) (Fin 2) ℝ :=
  twoSensorObservabilityMatrix
    (capturedSatisfactionSensitivity piH kappa xH) 0
    sensorH sensorL aH aL

/-- Any nonzero auxiliary low-coordinate sensitivity observes the low mode,
independently of its healthy loading and of the diagonal rates. -/
theorem twoSensorObservabilityMatrix_lowMode_ne_zero_of_second_low
    {c1H c2H c2L aH aL : ℝ} (hc2L : c2L ≠ 0) :
    (twoSensorObservabilityMatrix c1H 0 c2H c2L aH aL) *ᵥ lowMode ≠ 0 := by
  intro hzero
  have hrow := congrFun hzero (1 : Fin 4)
  apply hc2L
  simpa [twoSensorObservabilityMatrix, lowMode, Matrix.mulVec, dotProduct]
    using hrow

/-- Every arbitrary auxiliary sensor with nonzero low loading sees the hidden
captured-face low mode. -/
theorem capturedAuxiliarySensorObservability_lowMode_ne_zero
    {piH kappa xH sensorH sensorL aH aL : ℝ}
    (hsensorL : sensorL ≠ 0) :
    (capturedAuxiliarySensorObservability
        piH kappa xH sensorH sensorL aH aL) *ᵥ lowMode ≠ 0 := by
  exact twoSensorObservabilityMatrix_lowMode_ne_zero_of_second_low hsensorL

/-- If captured satisfaction still loads on the healthy coordinate, every
auxiliary sensor with nonzero low loading restores full observability. -/
theorem capturedAuxiliarySensorObservability_rank_two
    {piH kappa xH sensorH sensorL aH aL : ℝ}
    (hpiH : piH ≠ 0) (hkappa : kappa ≠ 0) (hxH : xH ≠ 0)
    (hsensorL : sensorL ≠ 0) :
    (capturedAuxiliarySensorObservability
      piH kappa xH sensorH sensorL aH aL).rank = 2 := by
  apply twoSensorObservabilityMatrix_rank_two
  simp only [zero_mul, sub_zero]
  have hsatisfaction :
      capturedSatisfactionSensitivity piH kappa xH ≠ 0 := by
    simp only [capturedSatisfactionSensitivity]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) hpiH)
        (pow_ne_zero 2 hkappa)) hxH
  exact mul_ne_zero hsatisfaction hsensorL

/-- With zero healthy satisfaction sensitivity, the two informative rows of
the arbitrary auxiliary sensor are its ordinary scalar observability matrix. -/
theorem scalarObservabilityMatrix_eq_auxiliary_submatrix
    (sensorH sensorL aH aL : ℝ) :
    scalarObservabilityMatrix sensorH sensorL aH aL =
      (twoSensorObservabilityMatrix 0 0 sensorH sensorL aH aL).submatrix
        (fun i : Fin 2 ↦ if i = 0 then (1 : Fin 4) else (3 : Fin 4)) id := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarObservabilityMatrix, twoSensorObservabilityMatrix]

/-- At the healthy-zero boundary, a single arbitrary auxiliary sensor restores
rank two exactly under the familiar nonzero-loadings and distinct-rate
sufficient conditions. -/
theorem capturedAuxiliarySensorObservability_rank_two_at_healthy_zero
    {piH kappa sensorH sensorL aH aL : ℝ}
    (hsensorH : sensorH ≠ 0) (hsensorL : sensorL ≠ 0)
    (hrates : aH ≠ aL) :
    (capturedAuxiliarySensorObservability
      piH kappa 0 sensorH sensorL aH aL).rank = 2 := by
  have hscalar :
      (scalarObservabilityMatrix sensorH sensorL aH aL).rank = 2 :=
    scalarObservabilityMatrix_rank_two hsensorH hsensorL hrates
  have hsub :
      scalarObservabilityMatrix sensorH sensorL aH aL =
        (capturedAuxiliarySensorObservability
          piH kappa 0 sensorH sensorL aH aL).submatrix
          (fun i : Fin 2 ↦ if i = 0 then (1 : Fin 4) else (3 : Fin 4)) id := by
    simpa [capturedAuxiliarySensorObservability,
      capturedSatisfactionSensitivity] using
      scalarObservabilityMatrix_eq_auxiliary_submatrix sensorH sensorL aH aL
  have hlower :
      (scalarObservabilityMatrix sensorH sensorL aH aL).rank ≤
        (capturedAuxiliarySensorObservability
          piH kappa 0 sensorH sensorL aH aL).rank := by
    rw [hsub]
    exact Matrix.rank_submatrix_le _ _ _
  have hupper :
      (capturedAuxiliarySensorObservability
        piH kappa 0 sensorH sensorL aH aL).rank ≤ 2 :=
    Matrix.rank_le_width _
  omega

#print axioms twoSensorObservabilityMatrix_lowMode_ne_zero_of_second_low
#print axioms capturedAuxiliarySensorObservability_lowMode_ne_zero
#print axioms capturedAuxiliarySensorObservability_rank_two
#print axioms scalarObservabilityMatrix_eq_auxiliary_submatrix
#print axioms capturedAuxiliarySensorObservability_rank_two_at_healthy_zero

end CivicAlignment.PaperIII
