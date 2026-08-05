/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.Ceiling
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Paper III: exact nonlinear indistinguishability

This file begins the observability layer with the captured-face theorem.  The
argument is global and exact: the product dynamics decouple, while the
satisfaction output factors through the healthy coordinate.
-/

namespace CivicAlignment.PaperIII

open Filter Matrix Topology

/-! ## Captured-face dynamics and output -/

/-- One affine coordinate of the captured-face dynamics. -/
def affineCoordinateStep (a injection x : ℝ) : ℝ :=
  a * x + injection

/-- The decoupled two-coordinate captured-face state map. -/
def capturedFaceMap (aH injectionH aL injectionL : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (affineCoordinateStep aH injectionH x.1,
    affineCoordinateStep aL injectionL x.2)

/-- Satisfaction on the captured face; the low coordinate has identically zero weight. -/
def capturedSatisfaction (piH kappa : ℝ) (x : ℝ × ℝ) : ℝ :=
  -piH * kappa ^ 2 * x.1 ^ 2

/-- The healthy-coordinate output function through which captured satisfaction factors. -/
def healthySatisfaction (piH kappa xH : ℝ) : ℝ :=
  -piH * kappa ^ 2 * xH ^ 2

/-- Iteration of an affine coordinate is exactly `arithGeom`. -/
theorem affineCoordinateStep_iterate_eq_arithGeom
    (a injection x₀ : ℝ) (t : ℕ) :
    (affineCoordinateStep a injection)^[t] x₀ = arithGeom a injection x₀ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih, arithGeom_succ]
      rfl

/-- Every iterate of the captured-face product map remains decoupled. -/
theorem capturedFaceMap_iterate
    (aH injectionH aL injectionL : ℝ) (xH xL : ℝ) (t : ℕ) :
    (capturedFaceMap aH injectionH aL injectionL)^[t] (xH, xL) =
      ((affineCoordinateStep aH injectionH)^[t] xH,
        (affineCoordinateStep aL injectionL)^[t] xL) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [capturedFaceMap, Function.iterate_succ_apply']

/-- Along every captured-face orbit, satisfaction is a function of the
healthy coordinate's initial condition alone. -/
theorem capturedSatisfaction_iterate_eq_healthy
    (piH kappa aH injectionH aL injectionL xH xL : ℝ) (t : ℕ) :
    capturedSatisfaction piH kappa
        ((capturedFaceMap aH injectionH aL injectionL)^[t] (xH, xL)) =
      healthySatisfaction piH kappa
        ((affineCoordinateStep aH injectionH)^[t] xH) := by
  rw [capturedFaceMap_iterate]
  rfl

/-- Any two captured-face states with the same healthy coordinate have
identical satisfaction outputs at every time. -/
theorem capturedFace_output_indistinguishable
    (piH kappa aH injectionH aL injectionL : ℝ)
    {x z : ℝ × ℝ} (hhealthy : x.1 = z.1) (t : ℕ) :
    capturedSatisfaction piH kappa
        ((capturedFaceMap aH injectionH aL injectionL)^[t] x) =
      capturedSatisfaction piH kappa
        ((capturedFaceMap aH injectionH aL injectionL)^[t] z) := by
  obtain ⟨xH, xL⟩ := x
  obtain ⟨zH, zL⟩ := z
  simp only at hhealthy
  subst zH
  rw [capturedSatisfaction_iterate_eq_healthy,
    capturedSatisfaction_iterate_eq_healthy]

/-! ## The invisible coordinate's geometric instability -/

/-- Negating the injection and initial value negates the entire affine path. -/
theorem arithGeom_neg (a b u₀ : ℝ) (n : ℕ) :
    arithGeom a (-b) (-u₀) n = -arithGeom a b u₀ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [arithGeom_succ, arithGeom_succ, ih]
      ring

/-- A supercritical sign-aligned affine path diverges in absolute value. -/
theorem tendsto_abs_arithGeom_of_signAligned
    {a b u₀ : ℝ} (ha : 1 < a) (hb : b ≠ 0) (hsign : 0 ≤ u₀ * b) :
    Tendsto (fun n ↦ |arithGeom a b u₀ n|) atTop atTop := by
  rcases lt_or_gt_of_ne hb with hbneg | hbpos
  · have hu₀nonpos : u₀ ≤ 0 := nonpos_of_mul_nonneg_left hsign hbneg
    have hnegated : Tendsto (arithGeom a (-b) (-u₀)) atTop atTop :=
      tendsto_arithGeom_supercritical ha (neg_pos.mpr hbneg) (neg_nonneg.mpr hu₀nonpos)
    have habs := tendsto_abs_atTop_atTop.comp hnegated
    apply habs.congr'
    exact Eventually.of_forall fun n ↦ by
      change |arithGeom a (-b) (-u₀) n| = |arithGeom a b u₀ n|
      rw [arithGeom_neg, abs_neg]
  · have hu₀nonnegative : 0 ≤ u₀ := nonneg_of_mul_nonneg_left hsign hbpos
    exact tendsto_abs_atTop_atTop.comp
      (tendsto_arithGeom_supercritical ha hbpos hu₀nonnegative)

/-- A supercritical sign-aligned affine path has successive-term ratio equal
asymptotically to its multiplier, regardless of the common sign. -/
theorem tendsto_arithGeom_ratio_of_signAligned
    {a b u₀ : ℝ} (ha : 1 < a) (hb : b ≠ 0) (hsign : 0 ≤ u₀ * b) :
    Tendsto (fun n ↦ arithGeom a b u₀ (n + 1) / arithGeom a b u₀ n)
      atTop (nhds a) := by
  rcases lt_or_gt_of_ne hb with hbneg | hbpos
  · have hu₀nonpos : u₀ ≤ 0 := nonpos_of_mul_nonneg_left hsign hbneg
    have hratio := tendsto_arithGeom_supercritical_ratio ha
      (neg_pos.mpr hbneg) (neg_nonneg.mpr hu₀nonpos)
    apply hratio.congr'
    exact Eventually.of_forall fun n ↦ by
      change arithGeom a (-b) (-u₀) (n + 1) / arithGeom a (-b) (-u₀) n =
        arithGeom a b u₀ (n + 1) / arithGeom a b u₀ n
      rw [arithGeom_neg, arithGeom_neg]
      ring
  · have hu₀nonnegative : 0 ≤ u₀ := nonneg_of_mul_nonneg_left hsign hbpos
    exact tendsto_arithGeom_supercritical_ratio ha hbpos hu₀nonnegative

/-- The exact claims packaged by the nonlinear indistinguishability theorem. -/
structure ExactNonlinearIndistinguishabilityConclusions
    (piH kappa aH injectionH ζ injectionL xH xL : ℝ) : Prop where
  output_formula : ∀ t,
    capturedSatisfaction piH kappa
        ((capturedFaceMap aH injectionH (1 + ζ) injectionL)^[t] (xH, xL)) =
      healthySatisfaction piH kappa
        ((affineCoordinateStep aH injectionH)^[t] xH)
  indistinguishable : ∀ zL t,
    capturedSatisfaction piH kappa
        ((capturedFaceMap aH injectionH (1 + ζ) injectionL)^[t] (xH, xL)) =
      capturedSatisfaction piH kappa
        ((capturedFaceMap aH injectionH (1 + ζ) injectionL)^[t] (xH, zL))
  low_coordinate_closed_form : ∀ t,
    ((capturedFaceMap aH injectionH (1 + ζ) injectionL)^[t] (xH, xL)).2 =
      arithGeom (1 + ζ) injectionL xL t
  low_coordinate_abs_diverges :
    Tendsto
      (fun t ↦
        |((capturedFaceMap aH injectionH (1 + ζ) injectionL)^[t] (xH, xL)).2|)
      atTop atTop
  low_coordinate_geometric_rate :
    Tendsto
      (fun t ↦
        ((capturedFaceMap aH injectionH (1 + ζ) injectionL)^[t + 1] (xH, xL)).2 /
          ((capturedFaceMap aH injectionH (1 + ζ) injectionL)^[t] (xH, xL)).2)
      atTop (nhds (1 + ζ))

/--
Paper III, Theorem 6.1 (`thm:exact`), `civic_loops.tex:364`.

The captured-face output sequence factors exactly through the healthy initial
coordinate, so changing the low coordinate cannot change satisfaction at any
time.  Under the paper's positive feedback, nonzero injection, and sign
alignment assumptions, the invisible low coordinate diverges in magnitude
with successive-term ratio `1 + ζ`.
-/
theorem exactNonlinearIndistinguishability
    {piH kappa aH injectionH ζ injectionL xH xL : ℝ}
    (hζ : 0 < ζ) (hinjectionL : injectionL ≠ 0)
    (hsign : 0 ≤ xL * injectionL) :
    ExactNonlinearIndistinguishabilityConclusions
      piH kappa aH injectionH ζ injectionL xH xL := by
  have hmultiplier : 1 < 1 + ζ := by linarith
  constructor
  · intro t
    exact capturedSatisfaction_iterate_eq_healthy
      piH kappa aH injectionH (1 + ζ) injectionL xH xL t
  · intro zL t
    exact capturedFace_output_indistinguishable
      piH kappa aH injectionH (1 + ζ) injectionL
        (x := (xH, xL)) (z := (xH, zL)) rfl t
  · intro t
    rw [capturedFaceMap_iterate]
    exact affineCoordinateStep_iterate_eq_arithGeom (1 + ζ) injectionL xL t
  · have hdivergence := tendsto_abs_arithGeom_of_signAligned
      hmultiplier hinjectionL hsign
    apply hdivergence.congr'
    exact Eventually.of_forall fun t ↦ by
      change |arithGeom (1 + ζ) injectionL xL t| =
        |((capturedFaceMap aH injectionH (1 + ζ) injectionL)^[t] (xH, xL)).2|
      rw [capturedFaceMap_iterate]
      change |arithGeom (1 + ζ) injectionL xL t| =
        |(affineCoordinateStep (1 + ζ) injectionL)^[t] xL|
      rw [affineCoordinateStep_iterate_eq_arithGeom]
  · have hrate := tendsto_arithGeom_ratio_of_signAligned
      hmultiplier hinjectionL hsign
    apply hrate.congr'
    exact Eventually.of_forall fun t ↦ by
      change arithGeom (1 + ζ) injectionL xL (t + 1) /
          arithGeom (1 + ζ) injectionL xL t =
        ((capturedFaceMap aH injectionH (1 + ζ) injectionL)^[t + 1] (xH, xL)).2 /
          ((capturedFaceMap aH injectionH (1 + ζ) injectionL)^[t] (xH, xL)).2
      rw [capturedFaceMap_iterate, capturedFaceMap_iterate]
      change arithGeom (1 + ζ) injectionL xL (t + 1) /
          arithGeom (1 + ζ) injectionL xL t =
        (affineCoordinateStep (1 + ζ) injectionL)^[t + 1] xL /
          (affineCoordinateStep (1 + ζ) injectionL)^[t] xL
      rw [affineCoordinateStep_iterate_eq_arithGeom,
        affineCoordinateStep_iterate_eq_arithGeom]

/-! ## Linearized observability ranks -/

/-- The two-state diagonal linearization used in `cor:kalman`. -/
def diagonalDynamics (aH aL : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![aH, 0; 0, aL]

/-- The Kalman observability matrix for one scalar sensor and diagonal dynamics. -/
def scalarObservabilityMatrix (cH cL aH aL : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cH, cL; cH * aH, cL * aL]

/--
The observability matrix for two scalar sensors.  Its first two rows are the
output Jacobian `C`; its last two rows are `C A`.
-/
def twoSensorObservabilityMatrix
    (c1H c1L c2H c2L aH aL : ℝ) : Matrix (Fin 4) (Fin 2) ℝ :=
  !![c1H, c1L; c2H, c2L; c1H * aH, c1L * aL; c2H * aH, c2L * aL]

/-- The low-coordinate basis vector `e_L`. -/
def lowMode : Fin 2 → ℝ :=
  ![0, 1]

/-- The healthy-coordinate basis vector `e_H`. -/
def healthyMode : Fin 2 → ℝ :=
  ![1, 0]

/-- The scalar observability determinant is the product of both sensitivities and rate gap. -/
theorem scalarObservabilityMatrix_det (cH cL aH aL : ℝ) :
    (scalarObservabilityMatrix cH cL aH aL).det = cH * cL * (aL - aH) := by
  rw [scalarObservabilityMatrix, Matrix.det_fin_two_of]
  ring

/-- A nonsingular real `2×2` matrix has rank two. -/
theorem rank_fin_two_eq_two_of_det_ne_zero
    (M : Matrix (Fin 2) (Fin 2) ℝ) (hdet : M.det ≠ 0) :
    M.rank = 2 := by
  have hunitDet : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 hunitDet
  simpa using Matrix.rank_of_isUnit M hunit

/-- A nonzero outer-product matrix has rank exactly one. -/
theorem rank_vecMulVec_eq_one
    {m n : Type*} [Fintype n] (w : m → ℝ) (v : n → ℝ)
    (i : m) (j : n) (hentry : w i * v j ≠ 0) :
    (Matrix.vecMulVec w v).rank = 1 := by
  let B : Matrix (Fin 1) (Fin 1) ℝ :=
    (Matrix.vecMulVec w v).submatrix (fun _ ↦ i) (fun _ ↦ j)
  have hB : B = !![w i * v j] := by
    ext r c
    fin_cases r
    fin_cases c
    rfl
  have hunitB : IsUnit B := by
    apply (Matrix.isUnit_iff_isUnit_det B).2
    rw [hB, Matrix.det_fin_one_of]
    exact isUnit_iff_ne_zero.mpr hentry
  have hrankB : B.rank = 1 := by
    simpa using Matrix.rank_of_isUnit B hunitB
  have hlower : B.rank ≤ (Matrix.vecMulVec w v).rank :=
    Matrix.rank_submatrix_le (Matrix.vecMulVec w v) (fun _ ↦ i) (fun _ ↦ j)
  have hupper : (Matrix.vecMulVec w v).rank ≤ 1 :=
    Matrix.rank_vecMulVec_le w v
  omega

/-- A scalar sensor observes both modes exactly when both sensitivities and the rate gap persist. -/
theorem scalarObservabilityMatrix_rank_two
    {cH cL aH aL : ℝ} (hcH : cH ≠ 0) (hcL : cL ≠ 0) (hrates : aH ≠ aL) :
    (scalarObservabilityMatrix cH cL aH aL).rank = 2 := by
  apply rank_fin_two_eq_two_of_det_ne_zero
  rw [scalarObservabilityMatrix_det]
  exact mul_ne_zero (mul_ne_zero hcH hcL) (sub_ne_zero.mpr hrates.symm)

/-- If the low-coordinate sensitivity vanishes, a nonzero healthy sensitivity gives rank one. -/
theorem scalarObservabilityMatrix_rank_one_of_low_blind
    {cH aH aL : ℝ} (hcH : cH ≠ 0) :
    (scalarObservabilityMatrix cH 0 aH aL).rank = 1 := by
  have houter :
      scalarObservabilityMatrix cH 0 aH aL =
        Matrix.vecMulVec ![1, aH] ![cH, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [scalarObservabilityMatrix, Matrix.vecMulVec, mul_comm]
  rw [houter]
  exact rank_vecMulVec_eq_one ![1, aH] ![cH, 0] 0 0 (by simpa using hcH)

/-- If the healthy sensitivity vanishes, a nonzero low sensitivity still gives only rank one. -/
theorem scalarObservabilityMatrix_rank_one_of_healthy_blind
    {cL aH aL : ℝ} (hcL : cL ≠ 0) :
    (scalarObservabilityMatrix 0 cL aH aL).rank = 1 := by
  have houter :
      scalarObservabilityMatrix 0 cL aH aL =
        Matrix.vecMulVec ![1, aL] ![0, cL] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [scalarObservabilityMatrix, Matrix.vecMulVec, mul_comm]
  rw [houter]
  exact rank_vecMulVec_eq_one ![1, aL] ![0, cL] 0 1 (by simpa using hcL)

/-- With a repeated eigenvalue, any nonzero scalar sensor has rank exactly one. -/
theorem scalarObservabilityMatrix_rank_one_of_equal_rates
    {cH cL a : ℝ} (hsensor : cH ≠ 0 ∨ cL ≠ 0) :
    (scalarObservabilityMatrix cH cL a a).rank = 1 := by
  have houter :
      scalarObservabilityMatrix cH cL a a =
        Matrix.vecMulVec ![1, a] ![cH, cL] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [scalarObservabilityMatrix, Matrix.vecMulVec, mul_comm]
  rw [houter]
  rcases hsensor with hcH | hcL
  · exact rank_vecMulVec_eq_one ![1, a] ![cH, cL] 0 0 (by simpa using hcH)
  · exact rank_vecMulVec_eq_one ![1, a] ![cH, cL] 0 1 (by simpa using hcL)

/-- A scalar sensor with both sensitivities zero has observability rank zero. -/
theorem scalarObservabilityMatrix_rank_zero_of_sensor_zero (aH aL : ℝ) :
    (scalarObservabilityMatrix 0 0 aH aL).rank = 0 := by
  have hzero : scalarObservabilityMatrix 0 0 aH aL = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [scalarObservabilityMatrix]
  rw [hzero, Matrix.rank_zero]

/-- The captured satisfaction observability matrix annihilates the low mode. -/
theorem scalarObservabilityMatrix_mulVec_lowMode
    (cH aH aL : ℝ) :
    scalarObservabilityMatrix cH 0 aH aL *ᵥ lowMode = 0 := by
  ext i
  fin_cases i <;>
    simp [scalarObservabilityMatrix, lowMode, Matrix.mulVec, dotProduct]

/-- With a low-blind scalar sensor, the low mode spans the full unobservable subspace. -/
theorem scalarObservabilityMatrix_kernel_eq_span_lowMode
    {cH aH aL : ℝ} (hcH : cH ≠ 0) (z : Fin 2 → ℝ) :
    scalarObservabilityMatrix cH 0 aH aL *ᵥ z = 0 ↔
      ∃ q : ℝ, z = q • lowMode := by
  constructor
  · intro hz
    have hrow := congrFun hz (0 : Fin 2)
    have hzH : z 0 = 0 := by
      have : cH * z 0 = 0 := by
        simpa [scalarObservabilityMatrix, Matrix.mulVec, dotProduct] using hrow
      exact (mul_eq_zero.mp this).resolve_left hcH
    refine ⟨z 1, ?_⟩
    funext i
    fin_cases i <;> simp [lowMode, hzH]
  · rintro ⟨q, rfl⟩
    ext i
    fin_cases i <;>
      simp [scalarObservabilityMatrix, lowMode, Matrix.mulVec, dotProduct]

/-- A healthy-blind scalar sensor annihilates the healthy mode. -/
theorem scalarObservabilityMatrix_mulVec_healthyMode
    (cL aH aL : ℝ) :
    scalarObservabilityMatrix 0 cL aH aL *ᵥ healthyMode = 0 := by
  ext i
  fin_cases i <;>
    simp [scalarObservabilityMatrix, healthyMode, Matrix.mulVec, dotProduct]

/-- With a healthy-blind scalar sensor, the healthy mode spans the unobservable subspace. -/
theorem scalarObservabilityMatrix_kernel_eq_span_healthyMode
    {cL aH aL : ℝ} (hcL : cL ≠ 0) (z : Fin 2 → ℝ) :
    scalarObservabilityMatrix 0 cL aH aL *ᵥ z = 0 ↔
      ∃ q : ℝ, z = q • healthyMode := by
  constructor
  · intro hz
    have hrow := congrFun hz (0 : Fin 2)
    have hzL : z 1 = 0 := by
      have : cL * z 1 = 0 := by
        simpa [scalarObservabilityMatrix, Matrix.mulVec, dotProduct] using hrow
      exact (mul_eq_zero.mp this).resolve_left hcL
    refine ⟨z 0, ?_⟩
    funext i
    fin_cases i <;> simp [healthyMode, hzL]
  · rintro ⟨q, rfl⟩
    ext i
    fin_cases i <;>
      simp [scalarObservabilityMatrix, healthyMode, Matrix.mulVec, dotProduct]

/-- The invisible low mode is the `aL` eigenvector of the diagonal dynamics. -/
theorem diagonalDynamics_mulVec_lowMode (aH aL : ℝ) :
    diagonalDynamics aH aL *ᵥ lowMode = aL • lowMode := by
  ext i
  fin_cases i <;>
    simp [diagonalDynamics, lowMode, Matrix.mulVec, dotProduct]

/-- The healthy mode is the `aH` eigenvector of the diagonal dynamics. -/
theorem diagonalDynamics_mulVec_healthyMode (aH aL : ℝ) :
    diagonalDynamics aH aL *ᵥ healthyMode = aH • healthyMode := by
  ext i
  fin_cases i <;>
    simp [diagonalDynamics, healthyMode, Matrix.mulVec, dotProduct]

/-- Full-rank output sensitivity in the first two rows forces two-sensor observability rank two. -/
theorem twoSensorObservabilityMatrix_rank_two
    {c1H c1L c2H c2L aH aL : ℝ}
    (hdet : c1H * c2L - c1L * c2H ≠ 0) :
    (twoSensorObservabilityMatrix c1H c1L c2H c2L aH aL).rank = 2 := by
  let C : Matrix (Fin 2) (Fin 2) ℝ := !![c1H, c1L; c2H, c2L]
  let row : Fin 2 → Fin 4 := fun i ↦ Fin.castAdd 2 i
  have hdetC : C.det ≠ 0 := by
    rw [show C.det = c1H * c2L - c1L * c2H by
      simp only [C, Matrix.det_fin_two_of]]
    exact hdet
  have hrankC : C.rank = 2 := rank_fin_two_eq_two_of_det_ne_zero C hdetC
  have hsub :
      C = (twoSensorObservabilityMatrix c1H c1L c2H c2L aH aL).submatrix row id := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [C, row, twoSensorObservabilityMatrix]
  have hlower :
      C.rank ≤ (twoSensorObservabilityMatrix c1H c1L c2H c2L aH aL).rank := by
    rw [hsub]
    exact Matrix.rank_submatrix_le
      (twoSensorObservabilityMatrix c1H c1L c2H c2L aH aL) row id
  have hupper :
      (twoSensorObservabilityMatrix c1H c1L c2H c2L aH aL).rank ≤ 2 :=
    Matrix.rank_le_width _
  omega

/-- With only the first sensor's healthy sensitivity nonzero, the stacked rank is one. -/
theorem twoSensorObservabilityMatrix_rank_one_of_only_first_healthy
    {cH aH aL : ℝ} (hcH : cH ≠ 0) :
    (twoSensorObservabilityMatrix cH 0 0 0 aH aL).rank = 1 := by
  have houter :
      twoSensorObservabilityMatrix cH 0 0 0 aH aL =
        Matrix.vecMulVec ![1, 0, aH, 0] ![cH, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [twoSensorObservabilityMatrix, Matrix.vecMulVec, mul_comm]
  rw [houter]
  exact rank_vecMulVec_eq_one ![1, 0, aH, 0] ![cH, 0] 0 0 (by simpa using hcH)

/-- With only the second sensor's low sensitivity nonzero, the stacked rank is one. -/
theorem twoSensorObservabilityMatrix_rank_one_of_only_second_low
    {cL aH aL : ℝ} (hcL : cL ≠ 0) :
    (twoSensorObservabilityMatrix 0 0 0 cL aH aL).rank = 1 := by
  have houter :
      twoSensorObservabilityMatrix 0 0 0 cL aH aL =
        Matrix.vecMulVec ![0, 1, 0, aL] ![0, cL] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [twoSensorObservabilityMatrix, Matrix.vecMulVec, mul_comm]
  rw [houter]
  exact rank_vecMulVec_eq_one ![0, 1, 0, aL] ![0, cL] 1 1 (by simpa using hcL)

/-- With only a low-coordinate sensitivity, the healthy mode is unobservable. -/
theorem twoSensorObservabilityMatrix_mulVec_healthyMode_of_only_second_low
    (cL aH aL : ℝ) :
    twoSensorObservabilityMatrix 0 0 0 cL aH aL *ᵥ healthyMode = 0 := by
  ext i
  fin_cases i <;>
    simp [twoSensorObservabilityMatrix, healthyMode, Matrix.mulVec, dotProduct]

/-- With only a nonzero low sensitivity, the healthy mode spans the unobservable subspace. -/
theorem twoSensorObservabilityMatrix_kernel_eq_span_healthyMode_of_only_second_low
    {cL aH aL : ℝ} (hcL : cL ≠ 0) (z : Fin 2 → ℝ) :
    twoSensorObservabilityMatrix 0 0 0 cL aH aL *ᵥ z = 0 ↔
      ∃ q : ℝ, z = q • healthyMode := by
  constructor
  · intro hz
    have hrow := congrFun hz (1 : Fin 4)
    have hzL : z 1 = 0 := by
      have : cL * z 1 = 0 := by
        simpa [twoSensorObservabilityMatrix, Matrix.mulVec, dotProduct] using hrow
      exact (mul_eq_zero.mp this).resolve_left hcL
    refine ⟨z 0, ?_⟩
    funext i
    fin_cases i <;> simp [healthyMode, hzL]
  · rintro ⟨q, rfl⟩
    ext i
    fin_cases i <;>
      simp [twoSensorObservabilityMatrix, healthyMode, Matrix.mulVec, dotProduct]

/-- A nonzero low sensitivity makes the low mode observable. -/
theorem twoSensorObservabilityMatrix_mulVec_lowMode_ne_zero_of_only_second_low
    {cL aH aL : ℝ} (hcL : cL ≠ 0) :
    twoSensorObservabilityMatrix 0 0 0 cL aH aL *ᵥ lowMode ≠ 0 := by
  intro hz
  have hrow := congrFun hz (1 : Fin 4)
  apply hcL
  simpa [twoSensorObservabilityMatrix, lowMode, Matrix.mulVec, dotProduct] using hrow

/-! ### The paper's two sensors -/

/-- The healthy captured-face fixed point `xH*=ιH/(ηHκ-ζ)`. -/
noncomputable def faceHealthyEquilibrium (injectionH etaH kappa ζ : ℝ) : ℝ :=
  injectionH / (etaH * kappa - ζ)

/-- Linear sensitivity of captured satisfaction to the healthy coordinate. -/
def capturedSatisfactionSensitivity (piH kappa xH : ℝ) : ℝ :=
  -2 * piH * kappa ^ 2 * xH

/-- Linear sensitivity of the unweighted audit sensor to the healthy coordinate. -/
def auditHealthySensitivity (eps piH xH : ℝ) : ℝ :=
  -2 * eps * piH * xH

/-- Linear sensitivity of the unweighted audit sensor to the low coordinate. -/
def auditLowSensitivity (eps piL xL : ℝ) : ℝ :=
  -2 * eps * piL * xL

/-- The satisfaction-only observability matrix on the captured face. -/
def capturedSatisfactionObservability
    (piH kappa xH aH aL : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  scalarObservabilityMatrix (capturedSatisfactionSensitivity piH kappa xH) 0 aH aL

/-- The stacked satisfaction-plus-audit observability matrix on the captured face. -/
def capturedAuditObservability
    (piH piL kappa eps xH xL aH aL : ℝ) : Matrix (Fin 4) (Fin 2) ℝ :=
  twoSensorObservabilityMatrix
    (capturedSatisfactionSensitivity piH kappa xH) 0
    (auditHealthySensitivity eps piH xH) (auditLowSensitivity eps piL xL)
    aH aL

/-- A nonzero healthy injection gives a nonzero healthy face equilibrium off the pole. -/
theorem faceHealthyEquilibrium_ne_zero
    {injectionH etaH kappa ζ : ℝ} (hinjection : injectionH ≠ 0)
    (hden : etaH * kappa - ζ ≠ 0) :
    faceHealthyEquilibrium injectionH etaH kappa ζ ≠ 0 := by
  exact div_ne_zero hinjection hden

/-- Off the standing pole, the healthy face equilibrium is nonzero exactly when injection is. -/
theorem faceHealthyEquilibrium_ne_zero_iff
    {injectionH etaH kappa ζ : ℝ} (hden : etaH * kappa - ζ ≠ 0) :
    faceHealthyEquilibrium injectionH etaH kappa ζ ≠ 0 ↔ injectionH ≠ 0 := by
  constructor
  · intro hequilibrium hinjection
    subst injectionH
    exact hequilibrium (by simp [faceHealthyEquilibrium])
  · intro hinjection
    exact faceHealthyEquilibrium_ne_zero hinjection hden

/-- Captured satisfaction has rank one when its healthy-coordinate sensitivity is nonzero. -/
theorem capturedSatisfactionObservability_rank_one
    {piH kappa xH aH aL : ℝ}
    (hpiH : piH ≠ 0) (hkappa : kappa ≠ 0) (hxH : xH ≠ 0) :
    (capturedSatisfactionObservability piH kappa xH aH aL).rank = 1 := by
  apply scalarObservabilityMatrix_rank_one_of_low_blind
  simp only [capturedSatisfactionSensitivity]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) hpiH) (pow_ne_zero 2 hkappa)) hxH

/-- Captured satisfaction annihilates the unstable low-coordinate mode. -/
theorem capturedSatisfactionObservability_lowMode
    (piH kappa xH aH aL : ℝ) :
    capturedSatisfactionObservability piH kappa xH aH aL *ᵥ lowMode = 0 := by
  exact scalarObservabilityMatrix_mulVec_lowMode _ _ _

/-- When captured satisfaction has rank one, `e_L` spans its unobservable subspace. -/
theorem capturedSatisfactionObservability_kernel_eq_span_lowMode
    {piH kappa xH aH aL : ℝ}
    (hpiH : piH ≠ 0) (hkappa : kappa ≠ 0) (hxH : xH ≠ 0)
    (z : Fin 2 → ℝ) :
    capturedSatisfactionObservability piH kappa xH aH aL *ᵥ z = 0 ↔
      ∃ q : ℝ, z = q • lowMode := by
  apply scalarObservabilityMatrix_kernel_eq_span_lowMode
  simp only [capturedSatisfactionSensitivity]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) hpiH) (pow_ne_zero 2 hkappa)) hxH

/-- A positive-weight audit restores rank two when both linearization coordinates are nonzero. -/
theorem capturedAuditObservability_rank_two
    {piH piL kappa eps xH xL aH aL : ℝ}
    (hpiH : piH ≠ 0) (hpiL : piL ≠ 0) (hkappa : kappa ≠ 0)
    (heps : eps ≠ 0) (hxH : xH ≠ 0) (hxL : xL ≠ 0) :
    (capturedAuditObservability piH piL kappa eps xH xL aH aL).rank = 2 := by
  apply twoSensorObservabilityMatrix_rank_two
  simp only [capturedSatisfactionSensitivity, auditHealthySensitivity,
    auditLowSensitivity, zero_mul, sub_zero]
  have hfirst : -2 * piH * kappa ^ 2 * xH ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) hpiH) (pow_ne_zero 2 hkappa)) hxH
  have hsecond : -2 * eps * piL * xL ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) heps) hpiL) hxL
  exact mul_ne_zero hfirst hsecond

/-- At zero audit weight, the added sensor contributes no rank. -/
theorem capturedAuditObservability_rank_one_at_zero_weight
    {piH piL kappa xH xL aH aL : ℝ}
    (hpiH : piH ≠ 0) (hkappa : kappa ≠ 0) (hxH : xH ≠ 0) :
    (capturedAuditObservability piH piL kappa 0 xH xL aH aL).rank = 1 := by
  simp only [capturedAuditObservability, auditHealthySensitivity,
    auditLowSensitivity, zero_mul, mul_zero]
  apply twoSensorObservabilityMatrix_rank_one_of_only_first_healthy
  simp only [capturedSatisfactionSensitivity]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) hpiH) (pow_ne_zero 2 hkappa)) hxH

/--
If the healthy coordinate is zero, even a positive audit weight and nonzero low
coordinate give only rank one.  This is the missing case in the paper's
"every face point with `xL≠0`" assertion.
-/
theorem capturedAuditObservability_rank_one_of_healthy_zero
    {piH piL kappa eps xL aH aL : ℝ}
    (heps : eps ≠ 0) (hpiL : piL ≠ 0) (hxL : xL ≠ 0) :
    (capturedAuditObservability piH piL kappa eps 0 xL aH aL).rank = 1 := by
  simp only [capturedAuditObservability, capturedSatisfactionSensitivity,
    auditHealthySensitivity, mul_zero]
  apply twoSensorObservabilityMatrix_rank_one_of_only_second_low
  simp only [auditLowSensitivity]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) heps) hpiL) hxL

/-- At the healthy-zero boundary, the augmented sensor annihilates `e_H`. -/
theorem capturedAuditObservability_healthyMode_at_healthy_zero
    (piH piL kappa eps xL aH aL : ℝ) :
    capturedAuditObservability piH piL kappa eps 0 xL aH aL *ᵥ healthyMode = 0 := by
  simp only [capturedAuditObservability, capturedSatisfactionSensitivity,
    auditHealthySensitivity, mul_zero]
  exact twoSensorObservabilityMatrix_mulVec_healthyMode_of_only_second_low
    (auditLowSensitivity eps piL xL) aH aL

/-- At the healthy-zero boundary, `e_H` spans the augmented sensor's kernel. -/
theorem capturedAuditObservability_kernel_eq_span_healthyMode
    {piH piL kappa eps xL aH aL : ℝ}
    (heps : eps ≠ 0) (hpiL : piL ≠ 0) (hxL : xL ≠ 0)
    (z : Fin 2 → ℝ) :
    capturedAuditObservability piH piL kappa eps 0 xL aH aL *ᵥ z = 0 ↔
      ∃ q : ℝ, z = q • healthyMode := by
  simp only [capturedAuditObservability, capturedSatisfactionSensitivity,
    auditHealthySensitivity, mul_zero]
  apply twoSensorObservabilityMatrix_kernel_eq_span_healthyMode_of_only_second_low
  simp only [auditLowSensitivity]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) heps) hpiL) hxL

/-- Every nonzero audit weight sees the low mode at the healthy-zero boundary. -/
theorem capturedAuditObservability_lowMode_ne_zero_at_healthy_zero
    {piH piL kappa eps xL aH aL : ℝ}
    (heps : eps ≠ 0) (hpiL : piL ≠ 0) (hxL : xL ≠ 0) :
    capturedAuditObservability piH piL kappa eps 0 xL aH aL *ᵥ lowMode ≠ 0 := by
  simp only [capturedAuditObservability, capturedSatisfactionSensitivity,
    auditHealthySensitivity, mul_zero]
  apply twoSensorObservabilityMatrix_mulVec_lowMode_ne_zero_of_only_second_low
  simp only [auditLowSensitivity]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) heps) hpiL) hxL

/-- With zero audit weight and zero healthy sensitivity, the unstable low mode is invisible. -/
theorem capturedAuditObservability_lowMode_at_zero_weight_healthy_zero
    (piH piL kappa xL aH aL : ℝ) :
    capturedAuditObservability piH piL kappa 0 0 xL aH aL *ᵥ lowMode = 0 := by
  ext i
  fin_cases i <;>
    simp [capturedAuditObservability, capturedSatisfactionSensitivity,
      auditHealthySensitivity, auditLowSensitivity, lowMode,
      twoSensorObservabilityMatrix, Matrix.mulVec, dotProduct]

/-- The healthy-zero boundary is detectable although it is not observable. -/
structure CapturedAuditBoundaryDetectabilityConclusions
    (piH piL kappa eps xL aH aL : ℝ) : Prop where
  rank_one :
    (capturedAuditObservability piH piL kappa eps 0 xL aH aL).rank = 1
  healthy_mode_unobservable :
    capturedAuditObservability piH piL kappa eps 0 xL aH aL *ᵥ healthyMode = 0
  unobservable_subspace : ∀ z : Fin 2 → ℝ,
    capturedAuditObservability piH piL kappa eps 0 xL aH aL *ᵥ z = 0 ↔
      ∃ q : ℝ, z = q • healthyMode
  healthy_mode_eigenvector :
    diagonalDynamics aH aL *ᵥ healthyMode = aH • healthyMode
  healthy_multiplier_stable : |aH| < 1
  low_mode_observed :
    capturedAuditObservability piH piL kappa eps 0 xL aH aL *ᵥ lowMode ≠ 0
  zero_weight_low_mode_unobservable :
    capturedAuditObservability piH piL kappa 0 0 xL aH aL *ᵥ lowMode = 0

/--
Paper III, Corollary `cor:kalman`, `civic_loops.tex:372`, healthy-zero branch.

For every positive audit weight, the only unobservable direction is the stable
healthy mode, while the unstable low mode is observed. At zero audit weight the
low mode is again invisible. This is the paper's binary-in-`ε` detectability
claim written without importing control-theory terminology.
-/
theorem capturedAuditBoundary_detectable
    {piH piL kappa eps xL aH aL : ℝ}
    (heps : 0 < eps) (hpiL : piL ≠ 0) (hxL : xL ≠ 0)
    (haHnonneg : 0 ≤ aH) (haHlt : aH < 1) :
    CapturedAuditBoundaryDetectabilityConclusions piH piL kappa eps xL aH aL := by
  have hepsne : eps ≠ 0 := ne_of_gt heps
  constructor
  · exact capturedAuditObservability_rank_one_of_healthy_zero hepsne hpiL hxL
  · exact capturedAuditObservability_healthyMode_at_healthy_zero _ _ _ _ _ _ _
  · intro z
    exact capturedAuditObservability_kernel_eq_span_healthyMode hepsne hpiL hxL z
  · exact diagonalDynamics_mulVec_healthyMode _ _
  · rw [abs_of_nonneg haHnonneg]
    exact haHlt
  · exact capturedAuditObservability_lowMode_ne_zero_at_healthy_zero
      hepsne hpiL hxL
  · exact capturedAuditObservability_lowMode_at_zero_weight_healthy_zero
      _ _ _ _ _ _

/-- The exact conclusions of Paper III's Kalman-rank corollary. -/
structure KalmanObservabilityRanksConclusions
    (piH piL kappa eps xH xL aH aL calibratedCH calibratedCL
      calibratedAH calibratedAL : ℝ) : Prop where
  captured_rank :
    (capturedSatisfactionObservability piH kappa xH aH aL).rank = 1
  low_mode_unobservable :
    capturedSatisfactionObservability piH kappa xH aH aL *ᵥ lowMode = 0
  low_mode_spans_unobservable : ∀ z : Fin 2 → ℝ,
    capturedSatisfactionObservability piH kappa xH aH aL *ᵥ z = 0 ↔
      ∃ q : ℝ, z = q • lowMode
  low_mode_eigenvector :
    diagonalDynamics aH aL *ᵥ lowMode = aL • lowMode
  audited_rank :
    (capturedAuditObservability piH piL kappa eps xH xL aH aL).rank = 2
  zero_audit_rank :
    (capturedAuditObservability piH piL kappa 0 xH xL aH aL).rank = 1
  calibrated_rank :
    (scalarObservabilityMatrix calibratedCH calibratedCL calibratedAH calibratedAL).rank = 2
  repeated_rate_rank : ∀ a,
    (scalarObservabilityMatrix calibratedCH calibratedCL a a).rank = 1

/--
Paper III, Corollary `cor:kalman`, `civic_loops.tex:372`, nondegenerate branch.

The three claimed ranks, the exact captured kernel, and the calibrated
equal-rate clause hold when every linearized sensor coefficient used to
separate a mode is nonzero. The paper's healthy-zero detectable boundary
is `capturedAuditBoundary_detectable`; its zero-sensitivity rank is
`kalmanFaceRank_zero_of_healthy_injection_zero`.
-/
theorem kalmanObservabilityRanks
    {piH piL kappa eps xH xL aH aL calibratedCH calibratedCL
      calibratedAH calibratedAL : ℝ}
    (hpiH : piH ≠ 0) (hpiL : piL ≠ 0) (hkappa : kappa ≠ 0)
    (heps : eps ≠ 0) (hxH : xH ≠ 0) (hxL : xL ≠ 0)
    (hcalibratedH : calibratedCH ≠ 0) (hcalibratedL : calibratedCL ≠ 0)
    (hrates : calibratedAH ≠ calibratedAL) :
    KalmanObservabilityRanksConclusions
      piH piL kappa eps xH xL aH aL calibratedCH calibratedCL
        calibratedAH calibratedAL := by
  constructor
  · exact capturedSatisfactionObservability_rank_one hpiH hkappa hxH
  · exact capturedSatisfactionObservability_lowMode _ _ _ _ _
  · intro z
    exact capturedSatisfactionObservability_kernel_eq_span_lowMode
      hpiH hkappa hxH z
  · exact diagonalDynamics_mulVec_lowMode _ _
  · exact capturedAuditObservability_rank_two
      hpiH hpiL hkappa heps hxH hxL
  · exact capturedAuditObservability_rank_one_at_zero_weight hpiH hkappa hxH
  · exact scalarObservabilityMatrix_rank_two
      hcalibratedH hcalibratedL hrates
  · intro a
    exact scalarObservabilityMatrix_rank_one_of_equal_rates
      (Or.inl hcalibratedH)

/--
At the permitted boundary `ιH=0`, the healthy face equilibrium is zero and
the satisfaction linearization has rank zero, not the paper's claimed rank
one.
-/
theorem kalmanFaceRank_zero_of_healthy_injection_zero
    {piH kappa etaH ζ aH aL : ℝ} (_hden : etaH * kappa - ζ ≠ 0) :
    faceHealthyEquilibrium 0 etaH kappa ζ = 0 ∧
      (capturedSatisfactionObservability piH kappa
        (faceHealthyEquilibrium 0 etaH kappa ζ) aH aL).rank = 0 := by
  have hxH : faceHealthyEquilibrium 0 etaH kappa ζ = 0 := by
    simp only [faceHealthyEquilibrium, zero_div]
  refine ⟨hxH, ?_⟩
  rw [hxH]
  simp only [capturedSatisfactionObservability, capturedSatisfactionSensitivity, mul_zero]
  have hzero : scalarObservabilityMatrix 0 0 aH aL = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [scalarObservabilityMatrix]
  rw [hzero, Matrix.rank_zero]

/--
Exact admissible face data with `ε>0` and `xL≠0` for which the augmented
observability rank is one because `xH=0`.
-/
theorem kalmanAuditRank_counterexample :
    (capturedAuditObservability
      (1 / 2) (1 / 2) (1 / 2) (1 / 10) 0 1 (1 / 2) 2).rank = 1 ∧
      (0 : ℝ) < 1 / 10 ∧ (1 : ℝ) ≠ 0 ∧
      (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 ∧
      (1 / 2 : ℝ) < 1 ∧ (1 : ℝ) < 2 := by
  refine ⟨capturedAuditObservability_rank_one_of_healthy_zero
    (by norm_num) (by norm_num) (by norm_num), ?_⟩
  norm_num

/-- Distinct rates alone do not give calibrated observability when one sensitivity vanishes. -/
theorem kalmanCalibratedDistinctRates_counterexample :
    (scalarObservabilityMatrix 0 1 (1 / 2) (1 / 3)).rank = 1 ∧
      (1 / 2 : ℝ) ≠ 1 / 3 := by
  exact ⟨scalarObservabilityMatrix_rank_one_of_healthy_blind (by norm_num), by norm_num⟩

#print axioms affineCoordinateStep_iterate_eq_arithGeom
#print axioms capturedFaceMap_iterate
#print axioms capturedSatisfaction_iterate_eq_healthy
#print axioms capturedFace_output_indistinguishable
#print axioms arithGeom_neg
#print axioms tendsto_abs_arithGeom_of_signAligned
#print axioms tendsto_arithGeom_ratio_of_signAligned
#print axioms exactNonlinearIndistinguishability
#print axioms scalarObservabilityMatrix_det
#print axioms rank_fin_two_eq_two_of_det_ne_zero
#print axioms rank_vecMulVec_eq_one
#print axioms scalarObservabilityMatrix_rank_two
#print axioms scalarObservabilityMatrix_rank_one_of_low_blind
#print axioms scalarObservabilityMatrix_rank_one_of_healthy_blind
#print axioms scalarObservabilityMatrix_rank_one_of_equal_rates
#print axioms scalarObservabilityMatrix_rank_zero_of_sensor_zero
#print axioms scalarObservabilityMatrix_mulVec_lowMode
#print axioms scalarObservabilityMatrix_kernel_eq_span_lowMode
#print axioms scalarObservabilityMatrix_mulVec_healthyMode
#print axioms scalarObservabilityMatrix_kernel_eq_span_healthyMode
#print axioms diagonalDynamics_mulVec_lowMode
#print axioms diagonalDynamics_mulVec_healthyMode
#print axioms twoSensorObservabilityMatrix_rank_two
#print axioms twoSensorObservabilityMatrix_rank_one_of_only_first_healthy
#print axioms twoSensorObservabilityMatrix_rank_one_of_only_second_low
#print axioms twoSensorObservabilityMatrix_mulVec_healthyMode_of_only_second_low
#print axioms twoSensorObservabilityMatrix_kernel_eq_span_healthyMode_of_only_second_low
#print axioms twoSensorObservabilityMatrix_mulVec_lowMode_ne_zero_of_only_second_low
#print axioms faceHealthyEquilibrium_ne_zero
#print axioms faceHealthyEquilibrium_ne_zero_iff
#print axioms capturedSatisfactionObservability_rank_one
#print axioms capturedSatisfactionObservability_lowMode
#print axioms capturedSatisfactionObservability_kernel_eq_span_lowMode
#print axioms capturedAuditObservability_rank_two
#print axioms capturedAuditObservability_rank_one_at_zero_weight
#print axioms capturedAuditObservability_rank_one_of_healthy_zero
#print axioms capturedAuditObservability_healthyMode_at_healthy_zero
#print axioms capturedAuditObservability_kernel_eq_span_healthyMode
#print axioms capturedAuditObservability_lowMode_ne_zero_at_healthy_zero
#print axioms capturedAuditObservability_lowMode_at_zero_weight_healthy_zero
#print axioms capturedAuditBoundary_detectable
#print axioms kalmanObservabilityRanks
#print axioms kalmanFaceRank_zero_of_healthy_injection_zero
#print axioms kalmanAuditRank_counterexample
#print axioms kalmanCalibratedDistinctRates_counterexample

end CivicAlignment.PaperIII
