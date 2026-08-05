/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.NonlinearRobustness

/-!
# Paper II: the affine loop as a nonlinear-robustness specialization

This file proves that the original affine stock recursion supplies every
hypothesis of the nonlinear robustness theorem.  It is therefore a literal
special case of that theorem, not a competing replacement.
-/

namespace CivicAlignment.PaperII

open Filter Function Set Topology

noncomputable section

/-- The paper's affine stock recursion, packaged as a nonlinear stock law. -/
def affineStockLaw (p : LoopParams) (model : DriftModelAssumptions p) :
    NonlinearStockLaw where
  step := p.stockStep
  characteristic := p.stationaryStock
  stockLower := p.I
  stockUpper := p.I / p.lambda₀
  stockLower_le_stockUpper := by
    exact (le_div_iff₀ model.lambda₀_pos).2 <| by
      nlinarith [model.I_pos, model.lambda₀_lt_one]

@[simp] theorem affineStockLaw_step
    {p : LoopParams} (model : DriftModelAssumptions p) (β D : ℝ) :
    (affineStockLaw p model).step β D = p.stockStep β D := rfl

@[simp] theorem affineStockLaw_characteristic
    {p : LoopParams} (model : DriftModelAssumptions p) (β : ℝ) :
    (affineStockLaw p model).characteristic β = p.stationaryStock β := rfl

@[simp] theorem nonlinearLoopBox_affineStockLaw
    {p : LoopParams} (model : DriftModelAssumptions p) :
    nonlinearLoopBox (affineStockLaw p model) = absorbingBox p := rfl

@[simp] theorem nonlinearLoopMap_affineStockLaw
    {p : LoopParams} (model : DriftModelAssumptions p) (x : LoopState) :
    nonlinearLoopMap p (affineStockLaw p model) x = p.loopMap x := rfl

/-- The affine invariant box, continuity, and cooperativity instantiate the
nonlinear core interface. -/
theorem affineNonlinearCore
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ssplus : ConvergentStepAssumption p) :
    NonlinearLoopCoreAssumptions p (affineStockLaw p model) where
  mapsTo := by
    change MapsTo p.loopMap (absorbingBox p) (absorbingBox p)
    exact invariantBox model
  continuous := by
    change Continuous p.loopMap
    exact continuous_loopMap p
  monotoneOn := by
    change MonotoneOn p.loopMap (absorbingBox p)
    exact loopMap_monotoneOn_box model
      (ssplus.toStrictSmallStep model).toSmallStep

/-- The four affine estimates are exactly an instance of the nonlinear
cross-bound interface. -/
def affineNonlinearCrossBounds
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ssplus : ConvergentStepAssumption p) :
    NonlinearCrossBounds p (affineStockLaw p model) where
  policyDiagonalLower := policyDiagonalLower p
  policyStockUpper := policyStockUpper p
  stockPolicyUpper := stockPolicyUpper p
  stockDiagonalLower := stockDiagonalLower p
  policyStockUpper_pos := policyStockUpper_pos model
  stockDiagonalLower_pos := ssplus.stockDiagonalLower_pos model
  crossProduct_lt := ssplus.crossProduct_lt_diagonalProduct model
  southeast_policy_lower := by
    intro x y hx hy hβ hD
    exact southeast_unclipped_difference_lower model hx hy hβ hD
  southeast_stock_upper := by
    intro x y hx hy hβ hD
    exact southeast_stock_difference_upper model hx hy hβ hD
  northwest_policy_upper := by
    intro x y hx hy hβ hD
    exact northwest_unclipped_difference_upper model hx hy hβ hD
  northwest_stock_lower := by
    intro x y hx hy hβ hD
    exact northwest_stock_difference_lower model hx hy hβ hD

/-- The affine threshold hypothesis supplies the nonlinear theorem's purely
algebraic three-fixed-point catalogue. -/
def affineNonlinearEquilibriumCatalogue
    {p : LoopParams} (model : DriftModelAssumptions p)
    (threshold : ThresholdAssumption p) :
    NonlinearEquilibriumCatalogue p (affineStockLaw p model) where
  βdagger := threshold.βdagger
  βdagger_mem := threshold.βdagger_mem
  calibrated_mem := by
    change (0, p.stationaryStock 0) ∈ absorbingBox p
    exact ⟨by norm_num, stationaryStock_mem_stockInterval model (by norm_num)⟩
  saddle_mem := by
    have hβ : threshold.βdagger ∈ Icc (0 : ℝ) 1 :=
      ⟨threshold.βdagger_mem.1.le, threshold.βdagger_mem.2.le⟩
    exact ⟨hβ, stationaryStock_mem_stockInterval model hβ⟩
  captured_mem := by
    change (1, p.stationaryStock 1) ∈ absorbingBox p
    exact ⟨by norm_num, stationaryStock_mem_stockInterval model (by norm_num)⟩
  exactly_three := by
    rintro ⟨β, D⟩ _hmem
    simpa only [IsNonlinearLoopEquilibrium, nonlinearLoopMap_affineStockLaw,
      nonlinearCalibratedPoint, nonlinearSaddlePoint, nonlinearCapturedPoint,
      affineStockLaw_characteristic, IsLoopEquilibrium, Prod.mk.injEq] using
      loopEquilibrium_iff_three_points model threshold β D
  characteristic_strictMono := stationaryStock_strictMonoOn model

/-- The existing affine result is recovered by the nonlinear robustness
theorem without changing any affine definition or hypothesis. -/
theorem affine_global_bistability_via_nonlinear_robustness
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) :
    NonlinearGlobalBistabilityConclusions p (affineStockLaw p model)
      (affineNonlinearEquilibriumCatalogue model threshold) :=
  nonlinear_global_bistability
    (affineNonlinearCore model ssplus)
    (affineNonlinearCrossBounds model ssplus)
    (affineNonlinearEquilibriumCatalogue model threshold)

#print axioms affine_global_bistability_via_nonlinear_robustness

end

end CivicAlignment.PaperII
