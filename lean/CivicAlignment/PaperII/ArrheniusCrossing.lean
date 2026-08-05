/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.ArrheniusFunnel
import CivicAlignment.PaperII.QuasipotentialLimit

/-!
# Paper II: the saddle-crossing quasipotential

The noisy saddle-crossing event is first passage of the policy running maximum through
the weighted saddle.  Its natural variational rate is therefore the infimum of
finite control actions which realize exactly that crossing event.  This file
defines that rate and proves the deterministic comparison chain with the
basin-exit quasipotential and the two bounds from `prop:qpbounds`.
-/

namespace CivicAlignment.PaperII

open Filter Set Topology
open scoped Interval

noncomputable section

/-! ## Definition and elementary infimum facts -/

/-- Actions of finite controls from the calibrated corner whose policy
running maximum reaches the weighted saddle. -/
def crossingActionSet {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) : Set ℝ :=
  {a | ∃ (T : ℕ) (u : Fin T → ℝ),
    weighted.βdagger ≤
        policyRunningMax (finiteControlledOrbit p rho u) T ∧
      a = gaussianVectorAction u}

/-- The saddle-crossing quasipotential `V^x`: the least finite action needed
to realize the event used by the noisy first-passage time. -/
def civicCrossingQuasipotential {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) : ℝ :=
  sInf (crossingActionSet weighted)

/-- The crossing action set is nonempty: forcing policy to one crosses every
interior weighted saddle in one step. -/
theorem crossingActionSet_nonempty {p : LoopParams} {rho : ℝ}
    (model : DriftModelAssumptions p)
    (weighted : WeightedThresholdAssumption p rho) :
    (crossingActionSet weighted).Nonempty := by
  let x := forcedCapturedPath p
  let u := forcedCapturedControl p rho
  have path : IsControlledCivicWeightedPath p rho u x :=
    forcedCapturedPath_isControlled model rho
  let v : Fin 1 → ℝ := fun i ↦ u i
  have horbit : finiteControlledOrbit p rho v 1 = x 1 := by
    exact finiteControlledOrbit_restrict_eq path le_rfl
  have hcross : weighted.βdagger ≤
      policyRunningMax (finiteControlledOrbit p rho v) 1 := by
    calc
      weighted.βdagger ≤ 1 := weighted.βdagger_mem.2.le
      _ = (finiteControlledOrbit p rho v 1).1 := by
        rw [horbit]
        rfl
      _ ≤ policyRunningMax (finiteControlledOrbit p rho v) 1 :=
        policy_le_runningMax _ _
  exact ⟨gaussianVectorAction v, 1, v, hcross, rfl⟩

/-- All crossing actions are nonnegative. -/
theorem crossingActionSet_bddBelow {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) :
    BddBelow (crossingActionSet weighted) := by
  refine ⟨0, ?_⟩
  rintro a ⟨T, u, _hcross, rfl⟩
  simp only [gaussianVectorAction]
  positivity

/-- The crossing quasipotential is nonnegative. -/
theorem civicCrossingQuasipotential_nonneg
    {p : LoopParams} {rho : ℝ}
    (model : DriftModelAssumptions p)
    (weighted : WeightedThresholdAssumption p rho) :
    0 ≤ civicCrossingQuasipotential weighted := by
  change 0 ≤ sInf (crossingActionSet weighted)
  apply le_csInf (crossingActionSet_nonempty model weighted)
  rintro a ⟨T, u, _hcross, rfl⟩
  simp only [gaussianVectorAction]
  positivity

/-- Any exhibited finite crossing control upper-bounds `V^x`. -/
theorem civicCrossingQuasipotential_le_gaussianVectorAction
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    {T : ℕ} {u : Fin T → ℝ}
    (hcross : weighted.βdagger ≤
      policyRunningMax (finiteControlledOrbit p rho u) T) :
    civicCrossingQuasipotential weighted ≤ gaussianVectorAction u := by
  exact csInf_le (crossingActionSet_bddBelow weighted)
    ⟨T, u, hcross, rfl⟩

/-- Every positive tolerance admits a finite crossing control with action
within that tolerance of `V^x`. -/
theorem exists_crossing_control_lt_quasipotential_add
    {p : LoopParams} {rho delta : ℝ}
    (model : DriftModelAssumptions p)
    (weighted : WeightedThresholdAssumption p rho) (hdelta : 0 < delta) :
    ∃ (T : ℕ) (u : Fin T → ℝ),
      weighted.βdagger ≤
          policyRunningMax (finiteControlledOrbit p rho u) T ∧
        gaussianVectorAction u <
          civicCrossingQuasipotential weighted + delta := by
  have hinf : sInf (crossingActionSet weighted) <
      civicCrossingQuasipotential weighted + delta := by
    simp only [civicCrossingQuasipotential]
    linarith
  obtain ⟨a, ha, halt⟩ := exists_lt_of_csInf_lt
    (crossingActionSet_nonempty model weighted) hinf
  rcases ha with ⟨T, u, hcross, rfl⟩
  exact ⟨T, u, hcross, halt⟩

/-! ## Comparison with the printed quasipotential bracket -/

/-- The corrected crossing ledger lower-bounds the crossing quasipotential. -/
theorem correctedBarrier_le_civicCrossingQuasipotential
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho L : ℝ}
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    (2 / (p.α * (1 + 2 * p.α * L))) *
        (∫ b in (0 : ℝ)..weighted.βdagger,
          weightedBarrierIntegrand p rho b) ≤
      civicCrossingQuasipotential weighted := by
  change _ ≤ sInf (crossingActionSet weighted)
  apply le_csInf (crossingActionSet_nonempty model weighted)
  rintro a ⟨T, u, hcross, rfl⟩
  have path := finiteControlledOrbit_isControlled p rho u
  have haction := path.action_lower_bound_of_crossing
    model ss hcoop weighted hL hcross
  rwa [controlAction_extendFiniteControl] at haction

/-- Saddle crossing is no harder than leaving the calibrated basin: every
basin-exiting path crosses first. -/
theorem civicCrossingQuasipotential_le_civicQuasipotential
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho) :
    civicCrossingQuasipotential weighted ≤ civicQuasipotential p rho := by
  change sInf (crossingActionSet weighted) ≤
    sInf (quasipotentialActionSet p rho)
  apply le_csInf (quasipotentialActionSet_nonempty model ss hrho hrhoCure)
  rintro a ⟨N, u, x, path, hexit, rfl⟩
  have hcross : weighted.βdagger ≤ policyRunningMax x N :=
    path.exit_forces_runningMax_ge
      model ss threshold hrho hcoop weighted hexit
  let v : Fin N → ℝ := fun i ↦ u i
  have horbit : finiteControlledOrbit p rho v N = x N :=
    finiteControlledOrbit_restrict_eq path le_rfl
  have hcrossFinite : weighted.βdagger ≤
      policyRunningMax (finiteControlledOrbit p rho v) N := by
    have hmax : policyRunningMax (finiteControlledOrbit p rho v) N =
        policyRunningMax x N := by
      apply le_antisymm
      · apply runningMax_le_of_forall_le
        intro k hk
        rw [finiteControlledOrbit_restrict_eq path hk]
        exact (policy_le_runningMax x k).trans
          ((monotone_runningMax fun j ↦ (x j).1) hk)
      · apply runningMax_le_of_forall_le
        intro k hk
        rw [← finiteControlledOrbit_restrict_eq path hk]
        exact (policy_le_runningMax (finiteControlledOrbit p rho v) k).trans
          ((monotone_runningMax
            fun j ↦ (finiteControlledOrbit p rho v j).1) hk)
    rwa [hmax]
  have hV := civicCrossingQuasipotential_le_gaussianVectorAction
    weighted hcrossFinite
  rw [gaussianVectorAction_restrict] at hV
  exact hV

/-- The full deterministic comparison chain
`Vminus ≤ V^x ≤ V ≤ Vplus`. -/
theorem crossingQuasipotential_bracket
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho L : ℝ} (hrho : 0 ≤ rho) (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    (2 / (p.α * (1 + 2 * p.α * L))) *
        (∫ b in (0 : ℝ)..weighted.βdagger,
          weightedBarrierIntegrand p rho b) ≤
      civicCrossingQuasipotential weighted ∧
    civicCrossingQuasipotential weighted ≤ civicQuasipotential p rho ∧
    civicQuasipotential p rho ≤ upwardStrategyCost weighted := by
  exact ⟨correctedBarrier_le_civicCrossingQuasipotential
      model ss hcoop weighted hL,
    civicCrossingQuasipotential_le_civicQuasipotential
      model ss threshold hrho hrhoCure hcoop weighted,
    civicQuasipotential_le_upwardStrategyCost
      model ss hrhoCure hcoop weighted⟩

/-! ## Fixed-primitives small-adaptation-rate limit -/

/-- The crossing quasipotential along the family which varies only the
operator adaptation rate. -/
def civicCrossingQuasipotentialAtRate
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (alpha : ℝ) : ℝ :=
  civicCrossingQuasipotential (weighted.withOperatorRate alpha)

/-- The scaled corrected barrier lower-bounds the crossing quasipotential at
each smaller positive adaptation rate. -/
theorem civicCrossingQuasipotentialAtRate_lower_bound
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho L alpha : ℝ}
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (halpha : 0 < alpha) (halphaLe : alpha ≤ p.α) :
    (2 * weightedBarrierArea weighted) / (1 + 2 * alpha * L) ≤
      alpha * civicCrossingQuasipotentialAtRate weighted alpha := by
  let q := withOperatorRate p alpha
  let modelq : DriftModelAssumptions q := model.withOperatorRate halpha
  let ssq : SmallStepAssumption q :=
    ss.withOperatorRate model halpha.le halphaLe
  let weightedq : WeightedThresholdAssumption q rho :=
    weighted.withOperatorRate alpha
  have hLq : IsLipschitzConstantOn (weightedBarrierIntegrand q rho) L
      0 weightedq.βdagger := by
    change IsLipschitzConstantOn
      (weightedBarrierIntegrand (withOperatorRate p alpha) rho) L
        0 weighted.βdagger
    have hfun : weightedBarrierIntegrand (withOperatorRate p alpha) rho =
        weightedBarrierIntegrand p rho := by
      funext beta
      exact withOperatorRate_weightedBarrierIntegrand p alpha rho beta
    rw [hfun]
    exact hL
  have hlower := correctedBarrier_le_civicCrossingQuasipotential
    modelq ssq (by simpa [q] using hcoop) weightedq hLq
  have hscaled := mul_le_mul_of_nonneg_left hlower halpha.le
  change alpha * ((2 / (alpha * (1 + 2 * alpha * L))) *
      weightedBarrierArea (weighted.withOperatorRate alpha)) ≤
    alpha * civicCrossingQuasipotentialAtRate weighted alpha at hscaled
  rw [weightedBarrierArea_withOperatorRate] at hscaled
  calc
    (2 * weightedBarrierArea weighted) / (1 + 2 * alpha * L) =
        alpha * ((2 / (alpha * (1 + 2 * alpha * L))) *
          weightedBarrierArea weighted) := by
      field_simp [halpha.ne']
    _ ≤ alpha * civicCrossingQuasipotentialAtRate weighted alpha := hscaled

/-- At every positive smaller rate, the crossing quasipotential is bounded by
the basin-exit quasipotential in the same fixed-primitives family. -/
theorem civicCrossingQuasipotentialAtRate_le_civicQuasipotentialAtRate
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho alpha : ℝ} (hrho : 0 ≤ rho)
    (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (halpha : 0 < alpha) (halphaLe : alpha ≤ p.α) :
    civicCrossingQuasipotentialAtRate weighted alpha ≤
      civicQuasipotentialAtRate p rho alpha := by
  let q := withOperatorRate p alpha
  let modelq : DriftModelAssumptions q := model.withOperatorRate halpha
  let ssq : SmallStepAssumption q :=
    ss.withOperatorRate model halpha.le halphaLe
  let thresholdq : ThresholdAssumption q := threshold.withOperatorRate alpha
  let weightedq : WeightedThresholdAssumption q rho :=
    weighted.withOperatorRate alpha
  simpa only [civicCrossingQuasipotentialAtRate,
    civicQuasipotentialAtRate, q, weightedq] using
    civicCrossingQuasipotential_le_civicQuasipotential
      modelq ssq thresholdq hrho (by simpa [q] using hrhoCure)
        (by simpa [q] using hcoop) weightedq

/-- The crossing rate has the same exact leading small-adaptation-rate limit
as both bounds in `cor:qplimit`. -/
theorem civicCrossingQuasipotentialAtRate_tendsto_barrier
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho) (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho) :
    Tendsto
      (fun alpha : ℝ ↦
        alpha * civicCrossingQuasipotentialAtRate weighted alpha)
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds (2 * weightedBarrierArea weighted)) := by
  obtain ⟨L, hL⟩ :=
    exists_lipschitzConstantOn_weightedBarrierIntegrand model weighted
  let A := weightedBarrierArea weighted
  have hbaseNhds : ∀ᶠ alpha : ℝ in nhds 0, alpha < p.α :=
    Iio_mem_nhds model.α_pos
  have hbase : ∀ᶠ alpha : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      alpha < p.α := hbaseNhds.filter_mono inf_le_left
  have hlowerTendsto : Tendsto
      (fun alpha : ℝ ↦ (2 * A) / (1 + 2 * alpha * L))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds (2 * A)) := by
    have hcont : ContinuousAt
        (fun alpha : ℝ ↦ (2 * A) / (1 + 2 * alpha * L)) 0 := by
      fun_prop (disch := norm_num)
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hupperTendsto : Tendsto
      (fun alpha : ℝ ↦ alpha * civicQuasipotentialAtRate p rho alpha)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds (2 * A)) := by
    simpa only [A] using civicQuasipotentialAtRate_tendsto_barrier
      model ss threshold hrho hrhoCure hcoop weighted
  have hlowerEventually : ∀ᶠ alpha : ℝ in
      nhdsWithin 0 (Ioi (0 : ℝ)),
      (2 * A) / (1 + 2 * alpha * L) ≤
        alpha * civicCrossingQuasipotentialAtRate weighted alpha := by
    filter_upwards [self_mem_nhdsWithin, hbase] with alpha halphaMem halphaBase
    simpa only [A] using civicCrossingQuasipotentialAtRate_lower_bound
      model ss hcoop weighted hL halphaMem halphaBase.le
  have hupperEventually : ∀ᶠ alpha : ℝ in
      nhdsWithin 0 (Ioi (0 : ℝ)),
      alpha * civicCrossingQuasipotentialAtRate weighted alpha ≤
        alpha * civicQuasipotentialAtRate p rho alpha := by
    filter_upwards [self_mem_nhdsWithin, hbase] with alpha halphaMem halphaBase
    exact mul_le_mul_of_nonneg_left
      (civicCrossingQuasipotentialAtRate_le_civicQuasipotentialAtRate
        model ss threshold hrho hrhoCure hcoop weighted
          halphaMem halphaBase.le) halphaMem.le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlowerTendsto hupperTendsto hlowerEventually hupperEventually

#print axioms crossingActionSet_nonempty
#print axioms crossingActionSet_bddBelow
#print axioms civicCrossingQuasipotential_nonneg
#print axioms civicCrossingQuasipotential_le_gaussianVectorAction
#print axioms exists_crossing_control_lt_quasipotential_add
#print axioms correctedBarrier_le_civicCrossingQuasipotential
#print axioms civicCrossingQuasipotential_le_civicQuasipotential
#print axioms crossingQuasipotential_bracket
#print axioms civicCrossingQuasipotentialAtRate_lower_bound
#print axioms civicCrossingQuasipotentialAtRate_le_civicQuasipotentialAtRate
#print axioms civicCrossingQuasipotentialAtRate_tendsto_barrier

end

end CivicAlignment.PaperII
