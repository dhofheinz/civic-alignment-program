/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Order.Interval.Set.ProjIcc

/-!
# Shared definitions for the Civic Alignment program

This file contains the scalar primitives shared across Papers I--III.  Paper I
uses the belief-output and evidence-weight definitions.  Papers II and III use
the same simultaneous two-dimensional loop, with Paper II recovered by setting
the content gain `g` to zero.

The common Jacobian identity (`eq:p1`) is proved here once because it is used by
both Paper II's bistability theorem and Paper III's loop-classification theorem.
-/

namespace CivicAlignment

noncomputable section

/-! ## Paper I belief primitives -/

/-- The two literacy types in Paper I. -/
inductive LiteracyType
  | high
  | low
  deriving DecidableEq, Repr

/-- Paper I, equations `eq:deference`: type-specific effective deference. -/
def effectiveDeference (κ β : ℝ) : LiteracyType → ℝ
  | .high => (1 - κ) * β
  | .low => β

/-- Paper I, equation `eq:policy`: the system output at effective deference `d`. -/
def systemOutput (d m b : ℝ) : ℝ :=
  (1 - d) * m + d * b

/-- Paper I, equation `eq:update`: the user's post-interaction belief. -/
def updatedBelief (η d m b : ℝ) : ℝ :=
  (1 - η) * b + η * systemOutput d m b

/-- Paper I, definition preceding `eq:weightform`: weight placed on evidence. -/
def evidenceWeight (η d : ℝ) : ℝ :=
  η * (1 - d)

/--
Paper I, equation `eq:weightform`: the direct update and evidence-weight forms
are identical.
-/
theorem updatedBelief_eq_weightForm (η d m b : ℝ) :
    updatedBelief η d m b = (1 - evidenceWeight η d) * b + evidenceWeight η d * m := by
  simp only [updatedBelief, systemOutput, evidenceWeight]
  ring

/--
Paper I, Assumption 4.9 discussion: the output-to-prior agreement gap is scaled by
`1 - d`.
-/
theorem systemOutput_sub_prior (d m b : ℝ) :
    systemOutput d m b - b = (1 - d) * (m - b) := by
  simp only [systemOutput]
  ring

/-! ## Papers II--III loop primitives -/

/-- Reduced deference and disagreement coordinates used by the loop map. -/
abbrev LoopState := ℝ × ℝ

/--
The common loop parameters.  Paper II is the specialization `g = 0`; Paper III
allows nonnegative content gain `g`.
-/
structure LoopParams where
  η : ℝ
  lambda₀ : ℝ
  I : ℝ
  v : ℝ
  c : ℝ
  α : ℝ
  g : ℝ

namespace LoopParams

/-- Papers II--III, the claim-portfolio persistence multiplier `s(β)`. -/
def s (p : LoopParams) (β : ℝ) : ℝ :=
  (1 - p.lambda₀) * (1 - p.η * (1 - β)) ^ 2

/-- The algebraic derivative of `s`; used in both loop Jacobians. -/
def sSlope (p : LoopParams) (β : ℝ) : ℝ :=
  2 * p.η * (1 - p.lambda₀) * (1 - p.η * (1 - β))

/-- Papers II--III, reduced operator satisfaction `U(β,D)`. -/
def U (p : LoopParams) (β D : ℝ) : ℝ :=
  -p.v * β - (1 - p.c * β) ^ 2 * D

/-- Papers II--III, the partial derivative `∂U/∂β` at fixed stock. -/
def gradU (p : LoopParams) (β D : ℝ) : ℝ :=
  -p.v + 2 * p.c * (1 - p.c * β) * D

/-- Papers II--III, the stationary stock at a fixed deference value. -/
def stationaryStock (p : LoopParams) (β : ℝ) : ℝ :=
  p.I / (1 - p.s β - p.g)

/-- Papers II--III, the stationary satisfaction gradient `G_g(β)`. -/
def G (p : LoopParams) (β : ℝ) : ℝ :=
  -p.v + 2 * p.c * (1 - p.c * β) * p.I / (1 - p.s β - p.g)

/-- The algebraic derivative of `G_g` away from the divergence wall. -/
def GSlope (p : LoopParams) (β : ℝ) : ℝ :=
  2 * p.c * p.I *
      (-p.c * (1 - p.s β - p.g) + (1 - p.c * β) * p.sSlope β) /
    (1 - p.s β - p.g) ^ 2

/-- Projection to the closed unit interval, the papers' `Π_[0,1]`. -/
def clipUnit (x : ℝ) : ℝ :=
  Set.projIcc 0 1 zero_le_one x

/-- Papers II--III, the simultaneous stock update. -/
def stockStep (p : LoopParams) (β D : ℝ) : ℝ :=
  (p.s β + p.g) * D + p.I

/-- Papers II--III, the projected-gradient operator update. -/
def deferenceStep (p : LoopParams) (β D : ℝ) : ℝ :=
  clipUnit (β + p.α * p.gradU β D)

/--
Papers II--III, the simultaneous loop map.  Both coordinates use the same input
state, matching the timing convention in `eq:map`.
-/
def loopMap (p : LoopParams) (x : LoopState) : LoopState :=
  (p.deferenceStep x.1 x.2, p.stockStep x.1 x.2)

/-- The interval projection always returns a value in `[0,1]`. -/
theorem clipUnit_mem (x : ℝ) : clipUnit x ∈ Set.Icc (0 : ℝ) 1 := by
  exact (Set.projIcc 0 1 zero_le_one x).property

/-- The interval projection used by the controller is order-preserving. -/
theorem monotone_clipUnit : Monotone clipUnit := by
  intro x y hxy
  exact_mod_cast Set.monotone_projIcc zero_le_one hxy

/-- Papers II--III: `sSlope` is the derivative of the stock multiplier. -/
theorem hasDerivAt_s (p : LoopParams) (β : ℝ) :
    HasDerivAt p.s (p.sSlope β) β := by
  have hOneSub : HasDerivAt (fun x : ℝ => 1 - x) (-1) β := by
    simpa using (hasDerivAt_id β).const_sub (1 : ℝ)
  have hScaled : HasDerivAt (fun x : ℝ => p.η * (1 - x)) (-p.η) β := by
    (convert! hOneSub.const_mul p.η using 1; ring)
  have hinner : HasDerivAt (fun x : ℝ => 1 - p.η * (1 - x)) p.η β := by
    (convert! hScaled.const_sub (1 : ℝ) using 1; ring)
  (convert! (hinner.pow 2).const_mul (1 - p.lambda₀) using 1;
    simp only [sSlope]; norm_num; ring)

/-- Papers II--III: `gradU` is the derivative of satisfaction at fixed stock. -/
theorem hasDerivAt_U (p : LoopParams) (β D : ℝ) :
    HasDerivAt (fun x : ℝ => p.U x D) (p.gradU β D) β := by
  have hlin : HasDerivAt (fun x : ℝ => 1 - p.c * x) (-p.c) β := by
    (convert! ((hasDerivAt_id β).const_mul p.c).const_sub (1 : ℝ) using 1; ring)
  have hsquare : HasDerivAt (fun x : ℝ => (1 - p.c * x) ^ 2)
      (-2 * p.c * (1 - p.c * β)) β := by
    (convert! hlin.pow 2 using 1; norm_num; ring)
  have hfirst : HasDerivAt (fun x : ℝ => -p.v * x) (-p.v) β := by
    (convert! (hasDerivAt_id β).const_mul (-p.v) using 1; ring)
  have hsecond : HasDerivAt (fun x : ℝ => (1 - p.c * x) ^ 2 * D)
      (-2 * p.c * (1 - p.c * β) * D) β := by
    convert! hsquare.mul_const D using 1
  (convert! HasDerivAt.sub hfirst hsecond using 1; simp only [gradU]; ring)

/-- Papers II--III: `GSlope` is the derivative of `G_g` off the divergence wall. -/
theorem hasDerivAt_G (p : LoopParams) (β : ℝ)
    (hwall : 1 - p.s β - p.g ≠ 0) : HasDerivAt p.G (p.GSlope β) β := by
  have hs : HasDerivAt p.s (p.sSlope β) β := p.hasDerivAt_s β
  have hlin : HasDerivAt (fun x : ℝ => 1 - p.c * x) (-p.c) β := by
    (convert! ((hasDerivAt_id β).const_mul p.c).const_sub (1 : ℝ) using 1; ring)
  have hnum : HasDerivAt
      (fun x : ℝ => 2 * p.c * (1 - p.c * x) * p.I) (-2 * p.c ^ 2 * p.I) β := by
    (convert! (hlin.const_mul (2 * p.c)).mul_const p.I using 1; ring)
  have hden : HasDerivAt (fun x : ℝ => 1 - p.s x - p.g) (-p.sSlope β) β := by
    convert! (hs.const_sub (1 : ℝ)).sub_const p.g using 1
  (convert! (hasDerivAt_const β (-p.v)).add (hnum.div hden hwall) using 1;
    simp only [GSlope]; field_simp [hwall]; ring)

/--
The characteristic polynomial of the interior loop Jacobian evaluated at one.
This is the left side of Papers II--III equation `eq:p1`.
-/
def jacobianPAtOne (p : LoopParams) (β D : ℝ) : ℝ :=
  let a := 1 - 2 * p.α * p.c ^ 2 * D
  let b := 2 * p.α * p.c * (1 - p.c * β)
  let cJ := p.sSlope β * D
  let d := p.s β + p.g
  (1 - a) * (1 - d) - b * cJ

/--
Papers II--III, algebra preceding `eq:p1`: simplification of the Jacobian
characteristic polynomial at one.
-/
theorem jacobianPAtOne_eq (p : LoopParams) (β D : ℝ) :
    p.jacobianPAtOne β D =
      2 * p.α * p.c * D *
        (p.c * (1 - p.s β - p.g) - (1 - p.c * β) * p.sSlope β) := by
  simp only [jacobianPAtOne]
  ring

/--
Papers II--III, equation `eq:p1`: the sign of the characteristic polynomial at
one is the opposite of the stationary-gradient crossing orientation.
-/
theorem jacobianPAtOne_eq_neg_GSlope (p : LoopParams) (β D : ℝ)
    (hI : p.I ≠ 0) (hwall : 1 - p.s β - p.g ≠ 0) :
    p.jacobianPAtOne β D =
      -(p.α * D * (1 - p.s β - p.g) ^ 2 / p.I) * p.GSlope β := by
  rw [p.jacobianPAtOne_eq]
  simp only [GSlope]
  field_simp [hI, hwall]
  ring

end LoopParams

/-! ## Shared affine recursion API -/

/--
Papers II--III: every stable affine stock law converges to its unique stationary
value.  This is the common scalar core used by `lem:box`, `lem:bound`,
`prop:ceiling`, and the AR(1) results.
-/
theorem tendsto_affineRecursion (a b u₀ : ℝ) (ha₀ : 0 ≤ a) (ha : a < 1) :
    Filter.Tendsto (arithGeom a b u₀) Filter.atTop (nhds (b / (1 - a))) :=
  tendsto_arithGeom_nhds_of_lt_one ha₀ ha

#print axioms updatedBelief_eq_weightForm
#print axioms systemOutput_sub_prior
#print axioms LoopParams.clipUnit_mem
#print axioms LoopParams.monotone_clipUnit
#print axioms LoopParams.hasDerivAt_s
#print axioms LoopParams.hasDerivAt_U
#print axioms LoopParams.hasDerivAt_G
#print axioms LoopParams.jacobianPAtOne_eq
#print axioms LoopParams.jacobianPAtOne_eq_neg_GSlope
#print axioms tendsto_affineRecursion

end

end CivicAlignment
