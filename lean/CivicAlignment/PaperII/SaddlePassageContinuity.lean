/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.Passage

/-!
# Paper II: the exact fixed-rate saddle-passage remainder

The crossing quasipotential is already known to be no larger than the
basin-exit quasipotential.  The missing reverse inequality is a variational
continuity statement: near-minimal crossing prefixes must be selectable with
an above-saddle endpoint whose stationary-stock lag, and hence canonical exit
continuation, has vanishing action.

This file states that remaining property without asymptotic shorthand and
proves that it implies the conjectured equality.  It does not assert the
property itself.
-/

namespace CivicAlignment.PaperII

open Set
open scoped Interval

noncomputable section

/-- The exact sign-free upper price of the canonical cancelling-hold exit
continuation from `(b, D)`. -/
def saddlePassageContinuationPrice (p : LoopParams) (b D : ℝ) : ℝ :=
  2 * p.c ^ 2 * |p.stationaryStock b - D| ^ 2 / p.lambda₀

/-- The still-unproved fixed-rate variational continuity property.

For every positive tolerance there is a finite prefix from the calibrated
state which ends strictly above the saddle, costs less than `V^x + epsilon`,
and has canonical exit-continuation price below `epsilon`.  The stock
membership condition is recorded explicitly because it is required by the
finite basin-exit construction.

The two strict inequalities force the near-minimal crossing approximation
and its residual saddle-passage surcharge to vanish jointly. -/
def HasVanishingSaddlePassageContinuation
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ (N : ℕ) (u : Fin N → ℝ) (b D : ℝ),
      finiteControlledOrbit p rho u N = (b, D) ∧
      b ∈ Ioc weighted.βdagger 1 ∧
      D ∈ Icc p.I (p.I / p.lambda₀) ∧
      gaussianVectorAction u <
        civicCrossingQuasipotential weighted + epsilon ∧
      saddlePassageContinuationPrice p b D < epsilon

/-- The current manuscript's exact open claim, separated from the already
proved Arrhenius-rate theorem. -/
def saddlePassageConjecture
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) : Prop :=
  civicCrossingQuasipotential weighted = civicQuasipotential p rho

/-- Any exhibited exit action upper-bounds the exit quasipotential. -/
theorem civicQuasipotential_le_of_mem_quasipotentialActionSet
    {p : LoopParams} {rho a : ℝ}
    (ha : a ∈ quasipotentialActionSet p rho) :
    civicQuasipotential p rho ≤ a := by
  change sInf (quasipotentialActionSet p rho) ≤ a
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro z ⟨N, u, _x, _path, _hexit, rfl⟩
    exact controlAction_nonneg u N
  · exact ha

/-- Exact reduction of Paper II's fixed-rate saddle-passage conjecture.

The established sign-free cancelling-hold construction turns the joint
near-minimality/vanishing-lag property into `V ≤ V^x`.  The previously proved
crossing-before-exit comparison supplies `V^x ≤ V`, so the two
quasipotentials are equal. -/
theorem saddlePassageConjecture_of_vanishingContinuation
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (continuity : HasVanishingSaddlePassageContinuation weighted) :
    saddlePassageConjecture weighted := by
  apply le_antisymm
  · exact civicCrossingQuasipotential_le_civicQuasipotential
      model ss threshold hrho hrhoCure hcoop weighted
  · apply le_of_forall_pos_le_add
    intro epsilon hepsilon
    have hhalf : 0 < epsilon / 2 := half_pos hepsilon
    obtain ⟨N, u, b, D, hend, hb, hD, haction, hcontinuation⟩ :=
      continuity (epsilon / 2) hhalf
    obtain ⟨e, heMem, heBound⟩ :=
      exists_exitAction_le_prefix_add_absLag_sq
        model ss hrho hrhoCure hcoop weighted u hend hb hD
    have hVle : civicQuasipotential p rho ≤ e :=
      civicQuasipotential_le_of_mem_quasipotentialActionSet heMem
    have heBound' : e ≤ gaussianVectorAction u +
        saddlePassageContinuationPrice p b D := by
      simpa only [saddlePassageContinuationPrice] using heBound
    calc
      civicQuasipotential p rho ≤ e := hVle
      _ ≤ gaussianVectorAction u +
          saddlePassageContinuationPrice p b D := heBound'
      _ ≤ (civicCrossingQuasipotential weighted + epsilon / 2) +
          epsilon / 2 := (add_lt_add haction hcontinuation).le
      _ = civicCrossingQuasipotential weighted + epsilon := by ring

#print axioms civicQuasipotential_le_of_mem_quasipotentialActionSet
#print axioms saddlePassageConjecture_of_vanishingContinuation

end

end CivicAlignment.PaperII
