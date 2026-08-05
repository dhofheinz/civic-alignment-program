/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.SafeSide

/-!
# Paper III / IV: full five-parameter certificate-margin geometry

The exact variance identity in `SafeSide.lean` treats the operator-side
parameters `v` and `c` as fixed.  An audit estimates all five inputs.  This
file records the exact perturbation identity, the resulting five-coordinate
gradient, and the full covariance quadratic form used by the delta method.
No independence or diagonal-covariance shortcut is built into the definition.
-/

namespace CivicAlignment.PaperIII

open scoped BigOperators

noncomputable section

/-- One point in the five-dimensional certificate-parameter space. -/
structure FiveParameterMarginPoint where
  v : ℝ
  c : ℝ
  lambda₀ : ℝ
  g : ℝ
  I₀ : ℝ

/-- Coordinatewise addition, used to state the exact perturbation identity. -/
def FiveParameterMarginPoint.add
    (p Δ : FiveParameterMarginPoint) : FiveParameterMarginPoint where
  v := p.v + Δ.v
  c := p.c + Δ.c
  lambda₀ := p.lambda₀ + Δ.lambda₀
  g := p.g + Δ.g
  I₀ := p.I₀ + Δ.I₀

/-- Certificate margin evaluated on all five estimated inputs. -/
def fiveParameterMargin (p : FiveParameterMarginPoint) : ℝ :=
  p.v * (p.lambda₀ - p.g) - 2 * p.c * p.I₀

/-- The first-order change of the margin at `p` in direction `Δ`. -/
def fiveParameterMarginLinearTerm
    (p Δ : FiveParameterMarginPoint) : ℝ :=
  (p.lambda₀ - p.g) * Δ.v - 2 * p.I₀ * Δ.c +
    p.v * Δ.lambda₀ - p.v * Δ.g - 2 * p.c * Δ.I₀

/-- The exact second-order remainder left after the five-parameter linear term. -/
def fiveParameterMarginRemainder (Δ : FiveParameterMarginPoint) : ℝ :=
  Δ.v * (Δ.lambda₀ - Δ.g) - 2 * Δ.c * Δ.I₀

/-- The plug-in margin increment is exactly its five-parameter linearization
plus the displayed bilinear remainder. -/
theorem fiveParameterMargin_increment_exact
    (p Δ : FiveParameterMarginPoint) :
    fiveParameterMargin (p.add Δ) - fiveParameterMargin p =
      fiveParameterMarginLinearTerm p Δ +
        fiveParameterMarginRemainder Δ := by
  simp only [fiveParameterMargin, FiveParameterMarginPoint.add,
    fiveParameterMarginLinearTerm, fiveParameterMarginRemainder]
  ring

/-- A finite-sample coverage event for the nonlinear five-parameter margin.
The radius is arbitrary: it may come from an exact confidence construction,
a deterministic sensitivity bound, or an asymptotic standard error. -/
def FiveParameterCoverageEvent
    (truth estimate : FiveParameterMarginPoint) (radius : ℝ) : Prop :=
  |fiveParameterMargin estimate - fiveParameterMargin truth| ≤ radius

/-- The one-sided certificate decision at a supplied error radius. -/
def FiveParameterSafeSideCertificate
    (estimate : FiveParameterMarginPoint) (radius : ℝ) : Prop :=
  radius < fiveParameterMargin estimate

/-- Safe-side soundness is exact on the registered coverage event, with no
normal approximation or independence assumption. -/
theorem fiveParameterSafeSideCertificate_sound
    {truth estimate : FiveParameterMarginPoint} {radius : ℝ}
    (hcoverage : FiveParameterCoverageEvent truth estimate radius)
    (hcertificate : FiveParameterSafeSideCertificate estimate radius) :
    0 < fiveParameterMargin truth := by
  rw [FiveParameterCoverageEvent] at hcoverage
  rw [FiveParameterSafeSideCertificate] at hcertificate
  have herror :
      fiveParameterMargin estimate - fiveParameterMargin truth ≤ radius :=
    (le_abs_self _).trans hcoverage
  linarith

/-- The exact linear term plus the exact bilinear remainder is a deterministic
finite-error radius for a five-parameter perturbation. -/
theorem fiveParameterLinearRemainder_isCoverageRadius
    (truth Δ : FiveParameterMarginPoint) :
    FiveParameterCoverageEvent truth (truth.add Δ)
      (|fiveParameterMarginLinearTerm truth Δ| +
        |fiveParameterMarginRemainder Δ|) := by
  rw [FiveParameterCoverageEvent, fiveParameterMargin_increment_exact]
  exact abs_add_le _ _

/-- A plug-in margin exceeding its exact linear-plus-remainder radius certifies
the true margin without an asymptotic approximation. -/
theorem fiveParameterSafeSide_of_linearRemainder
    (truth Δ : FiveParameterMarginPoint)
    (hcertificate :
      |fiveParameterMarginLinearTerm truth Δ| +
          |fiveParameterMarginRemainder Δ| <
        fiveParameterMargin (truth.add Δ)) :
    0 < fiveParameterMargin truth := by
  exact fiveParameterSafeSideCertificate_sound
    (fiveParameterLinearRemainder_isCoverageRadius truth Δ) hcertificate

/-- The five coordinates of the audit margin, in order
`(v,c,lambda₀,g,I₀)`. -/
abbrev MarginCoordinate := Fin 5

/-- Gradient of `m=v(lambda₀-g)-2cI₀` in coordinate order
`(v,c,lambda₀,g,I₀)`. -/
def fiveParameterMarginGradient
    (p : FiveParameterMarginPoint) : MarginCoordinate → ℝ :=
  ![p.lambda₀ - p.g, -2 * p.I₀, p.v, -p.v, -2 * p.c]

/-- A symmetric positive-semidefinite covariance matrix for the five jointly
estimated inputs. -/
structure FiveParameterCovariance where
  matrix : MarginCoordinate → MarginCoordinate → ℝ
  symmetric : ∀ i j, matrix i j = matrix j i
  positiveSemidefinite : ∀ a : MarginCoordinate → ℝ,
    0 ≤ ∑ i, ∑ j, a i * matrix i j * a j

/-- Full five-parameter delta-method variance `gradientᵀ Sigma gradient`. -/
def fiveParameterDeltaVariance
    (p : FiveParameterMarginPoint) (covariance : FiveParameterCovariance) : ℝ :=
  ∑ i, ∑ j,
    fiveParameterMarginGradient p i * covariance.matrix i j *
      fiveParameterMarginGradient p j

/-- The full delta variance is nonnegative whenever the supplied covariance
matrix is positive semidefinite. -/
theorem fiveParameterDeltaVariance_nonneg
    (p : FiveParameterMarginPoint) (covariance : FiveParameterCovariance) :
    0 ≤ fiveParameterDeltaVariance p covariance := by
  exact covariance.positiveSemidefinite (fiveParameterMarginGradient p)

/-- The diagonal-only variance used by an independence approximation. -/
def fiveParameterDiagonalVariance
    (p : FiveParameterMarginPoint) (covariance : FiveParameterCovariance) : ℝ :=
  ∑ i, (fiveParameterMarginGradient p i) ^ 2 * covariance.matrix i i

/-- The diagonal shortcut equals the full covariance quadratic form when all
off-diagonal covariances are zero.  This hypothesis is the precise condition
that a diagonal implementation must justify. -/
theorem fiveParameterDeltaVariance_eq_diagonal_of_offDiagonal_zero
    (p : FiveParameterMarginPoint) (covariance : FiveParameterCovariance)
    (hoff : ∀ i j, i ≠ j → covariance.matrix i j = 0) :
    fiveParameterDeltaVariance p covariance =
      fiveParameterDiagonalVariance p covariance := by
  classical
  simp only [fiveParameterDeltaVariance, fiveParameterDiagonalVariance]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_eq_single i]
  · ring
  · intro j _hj hji
    rw [hoff i j hji.symm]
    ring
  · simp

#print axioms fiveParameterMargin_increment_exact
#print axioms fiveParameterSafeSideCertificate_sound
#print axioms fiveParameterLinearRemainder_isCoverageRadius
#print axioms fiveParameterSafeSide_of_linearRemainder
#print axioms fiveParameterDeltaVariance_nonneg
#print axioms fiveParameterDeltaVariance_eq_diagonal_of_offDiagonal_zero

end

end CivicAlignment.PaperIII
