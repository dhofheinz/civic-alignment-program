/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.Imported.LocalStableManifold

/-!
# Paper II: assembled bistability theorem

This file gives the paper's six-clause theorem a single Lean name.  The local
`C¹` stable-arc field is the only imported field; every global convergence,
basin, boundary, spectrum, and sharpness field is proved in the preceding
modules.
-/

namespace CivicAlignment.PaperII

open Filter Set Topology

noncomputable section

/-- Clause (a): the exact fixed-point catalogue and its componentwise order. -/
def BistabilityEquilibria (p : LoopParams)
    (threshold : ThresholdAssumption p) : Prop :=
  (∀ β D : ℝ, IsLoopEquilibrium p β D ↔
    (β = 0 ∧ D = p.stationaryStock 0) ∨
    (β = threshold.βdagger ∧
      D = p.stationaryStock threshold.βdagger) ∨
    (β = 1 ∧ D = p.stationaryStock 1)) ∧
  (0 : ℝ) < threshold.βdagger ∧
    p.stationaryStock 0 < p.stationaryStock threshold.βdagger ∧
    threshold.βdagger < 1 ∧
    p.stationaryStock threshold.βdagger < p.stationaryStock 1

/-- Clause (b): explicit relative trapping neighborhoods for both corners. -/
def BistabilityCornerAttractors (p : LoopParams) : Prop :=
  (∃ N : Set LoopState, N ∈ 𝓝 (calibratedPoint p) ∧
    ∀ {x : ℕ → LoopState}, IsLoopTrajectory p x →
      x 0 ∈ absorbingBox p → x 0 ∈ N →
      Tendsto x atTop (𝓝 (calibratedPoint p))) ∧
  (∃ N : Set LoopState, N ∈ 𝓝 (capturedPoint p) ∧
    ∀ {x : ℕ → LoopState}, IsLoopTrajectory p x →
      x 0 ∈ absorbingBox p → x 0 ∈ N →
      Tendsto x atTop (𝓝 (capturedPoint p)))

/-- Clause (c): nonnegative real saddle spectrum, the exact crossing
equivalence, and the paper's unconditional and conditional eigenvalue bounds. -/
def BistabilitySaddleSpectrum (p : LoopParams)
    (threshold : ThresholdAssumption p) : Prop :=
  let J := interiorLoopJacobian p threshold.βdagger
    (p.stationaryStock threshold.βdagger)
  (0 ≤ J.a ∧ J.a ≤ 1 ∧ 0 < J.b ∧ 0 < J.cJ ∧
      0 ≤ J.d ∧ J.d < 1) ∧
    0 ≤ J.discriminant ∧
    (1 < J.largerEigenvalue ↔ 0 < p.GSlope threshold.βdagger) ∧
    1 < J.largerEigenvalue ∧
    J.smallerEigenvalue < 1 ∧
    (2 * p.η ≤ p.c * (1 + p.s 0) →
      (-1 : ℝ) < J.smallerEigenvalue)

/-- Clause (d): a single comparable step forces a monotone tail and convergence
to a fixed point in the invariant box. -/
def BistabilityMonotoneStep (p : LoopParams) : Prop :=
  ∀ {x : ℕ → LoopState}, IsLoopTrajectory p x →
    x 0 ∈ absorbingBox p → ∀ {t : ℕ},
    (x t ≤ x (t + 1) ∨ x (t + 1) ≤ x t) →
    ∃ q ∈ absorbingBox p,
      Tendsto x atTop (𝓝 q) ∧ IsLoopEquilibrium p q.1 q.2

/-- Clause (e), under `(SS⁺)`: global convergence, positive determinant and
hyperbolicity, and the complete relative topology of the saddle stable set and
the two corner basins. -/
def BistabilitySSPlusGeometry (p : LoopParams)
    (model : DriftModelAssumptions p)
    (threshold : ThresholdAssumption p) : Prop :=
  (∀ {x : ℕ → LoopState}, IsLoopTrajectory p x →
    x 0 ∈ absorbingBox p →
    ∃ q ∈ absorbingBox p, Tendsto x atTop (𝓝 q) ∧
      (q = calibratedPoint p ∨ q = saddlePoint p threshold ∨
        q = capturedPoint p)) ∧
  (∀ {x : LoopState}, x ∈ absorbingBox p →
    0 < (interiorLoopJacobian p x.1 x.2).det) ∧
  (let J := interiorLoopJacobian p threshold.βdagger
      (p.stationaryStock threshold.βdagger);
    1 < J.largerEigenvalue ∧ J.smallerEigenvalue ∈ Ioo (0 : ℝ) 1) ∧
  IsClosed (saddleStableSetInBox p threshold) ∧
  (∀ x : LoopBox p,
    loopMapOnBox p model x ∈ saddleStableSetInBox p threshold ↔
      x ∈ saddleStableSetInBox p threshold) ∧
  interior (saddleStableSetInBox p threshold) = ∅ ∧
  IsLocalC1DecreasingArcAt (ambientSaddleStableSet p threshold)
    (saddlePoint p threshold) ∧
  (saddleStableSetInBox p threshold)ᶜ =
    loopBasinInBox p (calibratedPoint p) ∪
      loopBasinInBox p (capturedPoint p) ∧
  IsOpen (loopBasinInBox p (calibratedPoint p)) ∧
  IsOpen (loopBasinInBox p (capturedPoint p)) ∧
  Disjoint (loopBasinInBox p (calibratedPoint p))
    (loopBasinInBox p (capturedPoint p)) ∧
  frontier (loopBasinInBox p (calibratedPoint p)) =
      saddleStableSetInBox p threshold ∧
  frontier (loopBasinInBox p (capturedPoint p)) =
      saddleStableSetInBox p threshold

/-- Clause (f): the exact rational period-two witness satisfying the primitive
model assumptions, strict `(SS)`, and `(H)`. -/
def BistabilitySharpness : Prop :=
  DriftModelAssumptions bistabilityCycleParams ∧
    StrictSmallStepAssumption bistabilityCycleParams ∧
    Nonempty (ThresholdAssumption bistabilityCycleParams) ∧
    IsLoopTrajectory bistabilityCycleParams bistabilityCycleTrajectory ∧
    (∀ n, bistabilityCycleTrajectory n ∈
      absorbingBox bistabilityCycleParams) ∧
    ¬PolicyCoordinateConverges bistabilityCycleTrajectory

/-- The six clauses of Paper II's bistability theorem, separated so that
clause (e)'s stronger step hypothesis remains visibly conditional. -/
structure BistabilityConclusions (p : LoopParams)
    (model : DriftModelAssumptions p)
    (threshold : ThresholdAssumption p) : Prop where
  equilibria : BistabilityEquilibria p threshold
  cornerAttractors : BistabilityCornerAttractors p
  saddleSpectrum : BistabilitySaddleSpectrum p threshold
  monotoneStep : BistabilityMonotoneStep p
  ssplusGeometry : ConvergentStepAssumption p →
    BistabilitySSPlusGeometry p model threshold
  sharpness : BistabilitySharpness

/-- Paper II, Theorem 3.14(e) (`thm:bistable`), `civic_drift.tex:237`:
the local saddle stable set is a `C¹` decreasing arc.  This is the transparent
project-level wrapper around `Imported.localStableManifoldForBistableLoop`. -/
theorem bistability_localC1DecreasingArc {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) :
    IsLocalC1DecreasingArcAt (ambientSaddleStableSet p threshold)
      (saddlePoint p threshold) :=
  Imported.localStableManifoldForBistableLoop model ssplus threshold

/-- Paper II, Theorem 3.14 (`thm:bistable`), `civic_drift.tex:237`.

All six clauses are assembled here.  The words “near `p₂`, a
`C¹` decreasing arc” are supplied by the local stable-manifold theorem,
itself proved from first principles; all global claims in clause (e) are
self-contained. -/
theorem bistability {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : StrictSmallStepAssumption p)
    (threshold : ThresholdAssumption p) :
    BistabilityConclusions p model threshold := by
  constructor
  · exact ⟨loopEquilibrium_iff_three_points model threshold,
      bistableFixedPoints_componentwise_order model threshold⟩
  · exact bistability_cornerAttractors model ss.toSmallStep threshold
  · let J := interiorLoopJacobian p threshold.βdagger
      (p.stationaryStock threshold.βdagger)
    have hentries := saddleJacobian_entry_bounds model ss threshold
    have hdisc : 0 ≤ J.discriminant :=
      J.discriminant_nonneg hentries.2.2.1.le hentries.2.2.2.1.le
    exact ⟨hentries, hdisc,
      saddle_largerEigenvalue_gt_one_iff_GSlope_pos model ss threshold,
      (saddle_largerEigenvalue_gt_one_iff_GSlope_pos model ss threshold).2
        threshold.GSlope_pos,
      saddle_smallerEigenvalue_lt_one model ss threshold,
      saddle_smallerEigenvalue_gt_neg_one model ss threshold⟩
  · intro x traj hx₀ t hstep
    exact comparableStep_convergesToFixedPoint model ss.toSmallStep traj hx₀ hstep
  · intro ssplus
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x traj hx₀
      exact bistability_globalConvergence_of_convergentStep model ssplus threshold traj hx₀
    · intro x hx
      exact interiorLoopJacobian_det_pos_on_box model ssplus hx
    · exact bistability_saddle_hyperbolic_spectrum model ssplus threshold
    · exact saddleStableSetInBox_isClosed model ssplus threshold
    · exact saddleStableSetInBox_invariant model threshold
    · exact saddleStableSetInBox_interior_eq_empty model ssplus threshold
    · exact bistability_localC1DecreasingArc model ssplus threshold
    · exact compl_saddleStableSetInBox_eq_cornerBasins model ssplus threshold
    · exact calibratedBasinInBox_isOpen model
        (ssplus.toStrictSmallStep model).toSmallStep threshold
    · exact capturedBasinInBox_isOpen model
        (ssplus.toStrictSmallStep model).toSmallStep threshold
    · exact (bistableBasins_pairwiseDisjoint threshold).2.1
    · exact bistability_commonBasinBoundary model ssplus threshold
  · exact ⟨bistabilityCycle_model, bistabilityCycle_strictSmallStep,
      ⟨bistabilityCycleThreshold⟩, bistability_global_convergence_counterexample.1,
      bistability_global_convergence_counterexample.2.1,
      bistability_global_convergence_counterexample.2.2⟩

#print axioms bistability_localC1DecreasingArc
#print axioms bistability

end

end CivicAlignment.PaperII
