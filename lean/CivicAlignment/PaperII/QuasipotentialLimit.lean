/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.Quasipotential

/-!
# Paper II: the small-adaptation-rate quasipotential limit

This file packages `cor:qplimit` from the pointwise lower and explicit-strategy
upper bounds proved in `Quasipotential.lean`.  Every primitive except the
operator adaptation rate is held literally fixed by `withOperatorRate`.
-/

namespace CivicAlignment.PaperII

open Filter Set Topology
open scoped Interval

noncomputable section

/-- The Paper II quasipotential along the family which varies only the
operator adaptation rate. -/
def civicQuasipotentialAtRate (p : LoopParams) (ρ α : ℝ) : ℝ :=
  civicQuasipotential (withOperatorRate p α) ρ

/-- The small-rate barrier as a function of the standing civic weight.  The
extension through `weightedBarrierAreaFamily` is differentiable wherever the
paper's oriented weighted saddle exists. -/
noncomputable def smallRateQuasipotentialBarrier (p : LoopParams) (ρ : ℝ) : ℝ :=
  2 * weightedBarrierAreaFamily p ρ

/-- The fixed-primitives lower bound after multiplication by the replacement
adaptation rate. -/
theorem civicQuasipotentialAtRate_lower_bound
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {ρ L α : ℝ} (hρ : 0 ≤ ρ) (hρcure : ρ < cureThreshold p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p ρ) L
      0 weighted.βdagger)
    (hα : 0 < α) (hαle : α ≤ p.α) :
    (2 * weightedBarrierArea weighted) / (1 + 2 * α * L) ≤
      α * civicQuasipotentialAtRate p ρ α := by
  let q := withOperatorRate p α
  let modelq : DriftModelAssumptions q := model.withOperatorRate hα
  let ssq : SmallStepAssumption q :=
    ss.withOperatorRate model hα.le hαle
  let thresholdq : ThresholdAssumption q := threshold.withOperatorRate α
  let weightedq : WeightedThresholdAssumption q ρ := weighted.withOperatorRate α
  have hLq : IsLipschitzConstantOn (weightedBarrierIntegrand q ρ) L
      0 weightedq.βdagger := by
    change IsLipschitzConstantOn
      (weightedBarrierIntegrand (withOperatorRate p α) ρ) L
        0 weighted.βdagger
    have hfun : weightedBarrierIntegrand (withOperatorRate p α) ρ =
        weightedBarrierIntegrand p ρ := by
      funext β
      exact withOperatorRate_weightedBarrierIntegrand p α ρ β
    rw [hfun]
    exact hL
  have hlower := civicQuasipotential_lower_bound
    modelq ssq thresholdq hρ (by simpa [q] using hρcure)
      (by simpa [q] using hcoop) weightedq hLq
  have hscaled := mul_le_mul_of_nonneg_left hlower hα.le
  change α * ((2 / (α * (1 + 2 * α * L))) *
      weightedBarrierArea (weighted.withOperatorRate α)) ≤
    α * civicQuasipotentialAtRate p ρ α at hscaled
  rw [weightedBarrierArea_withOperatorRate] at hscaled
  calc
    (2 * weightedBarrierArea weighted) / (1 + 2 * α * L) =
        α * ((2 / (α * (1 + 2 * α * L))) *
          weightedBarrierArea weighted) := by
      field_simp [hα.ne']
    _ ≤ α * civicQuasipotentialAtRate p ρ α := hscaled

/-- The explicit two-phase strategy gives a constant-order upper remainder
after the quasipotential is multiplied by the replacement adaptation rate. -/
theorem civicQuasipotentialAtRate_upper_bound
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {ρ L α : ℝ}
    (hρ : 0 ≤ ρ) (hρcure : ρ < cureThreshold p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p ρ) L
      0 weighted.βdagger)
    (hα : 0 < α) (hαle : α ≤ p.α) (hαone : α ≤ 1)
    (hroom : α * (p.v + α) ≤ 1 - weighted.βdagger) :
    α * civicQuasipotentialAtRate p ρ α ≤
      2 * weightedBarrierArea weighted +
        α * smallRateStrategyRemainderBound p L := by
  let q := withOperatorRate p α
  let modelq : DriftModelAssumptions q := model.withOperatorRate hα
  let ssq : SmallStepAssumption q :=
    ss.withOperatorRate model hα.le hαle
  let weightedq : WeightedThresholdAssumption q ρ := weighted.withOperatorRate α
  have hVleS := civicQuasipotential_le_upwardStrategyCost
    modelq ssq (by simpa [q] using hρcure)
      (by simpa [q] using hcoop) weightedq
  have hVleS' : civicQuasipotentialAtRate p ρ α ≤
      upwardStrategyCostAtRate weighted α := by
    simpa only [civicQuasipotentialAtRate, upwardStrategyCostAtRate,
      q, weightedq] using hVleS
  have hSupper := upwardStrategyCostAtRate_upper_bound
    model ss hρ hcoop weighted hL hα hαle hαone hroom
  have hscaled := mul_le_mul_of_nonneg_left (hVleS'.trans hSupper) hα.le
  calc
    α * civicQuasipotentialAtRate p ρ α ≤
        α * ((2 / α) * weightedBarrierArea weighted +
          smallRateStrategyRemainderBound p L) := hscaled
    _ = 2 * weightedBarrierArea weighted +
        α * smallRateStrategyRemainderBound p L := by
      field_simp [hα.ne']

/-- Paper II, Corollary `cor:qplimit`, `civic_drift.tex:376`: holding every
primitive except the operator adaptation rate fixed, the scaled
quasipotential converges from the right to twice the weighted barrier area. -/
theorem civicQuasipotentialAtRate_tendsto_barrier
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρcure : ρ < cureThreshold p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) :
    Tendsto (fun α : ℝ ↦ α * civicQuasipotentialAtRate p ρ α)
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (𝓝 (2 * weightedBarrierArea weighted)) := by
  obtain ⟨L, hL⟩ :=
    exists_lipschitzConstantOn_weightedBarrierIntegrand model weighted
  let A := weightedBarrierArea weighted
  let C := smallRateStrategyRemainderBound p L
  let d := (1 - weighted.βdagger) / (p.v + 1)
  have hd : 0 < d := by
    dsimp only [d]
    exact div_pos (sub_pos.mpr weighted.βdagger_mem.2)
      (by linarith [model.v_pos])
  have hbaseNhds : ∀ᶠ α : ℝ in 𝓝 0, α < p.α :=
    Iio_mem_nhds model.α_pos
  have honeNhds : ∀ᶠ α : ℝ in 𝓝 0, α < 1 :=
    Iio_mem_nhds zero_lt_one
  have hdNhds : ∀ᶠ α : ℝ in 𝓝 0, α < d :=
    Iio_mem_nhds hd
  have hbase : ∀ᶠ α : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)), α < p.α :=
    hbaseNhds.filter_mono inf_le_left
  have hone : ∀ᶠ α : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)), α < 1 :=
    honeNhds.filter_mono inf_le_left
  have hdsmall : ∀ᶠ α : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)), α < d :=
    hdNhds.filter_mono inf_le_left
  have hlowerTendsto : Tendsto
      (fun α : ℝ ↦ (2 * A) / (1 + 2 * α * L))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (𝓝 (2 * A)) := by
    have hcont : ContinuousAt
        (fun α : ℝ ↦ (2 * A) / (1 + 2 * α * L)) 0 := by
      fun_prop (disch := norm_num)
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hupperTendsto : Tendsto
      (fun α : ℝ ↦ 2 * A + α * C)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (𝓝 (2 * A)) := by
    have hcont : ContinuousAt (fun α : ℝ ↦ 2 * A + α * C) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hlowerEventually : ∀ᶠ α : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      (2 * A) / (1 + 2 * α * L) ≤
        α * civicQuasipotentialAtRate p ρ α := by
    filter_upwards [self_mem_nhdsWithin, hbase] with α hαmem hαbase
    simpa only [A] using civicQuasipotentialAtRate_lower_bound
      model ss threshold hρ hρcure hcoop weighted hL hαmem hαbase.le
  have hupperEventually : ∀ᶠ α : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      α * civicQuasipotentialAtRate p ρ α ≤ 2 * A + α * C := by
    filter_upwards [self_mem_nhdsWithin, hbase, hone, hdsmall] with α hαmem
        hαbase hαone hαd
    have hroom : α * (p.v + α) ≤ 1 - weighted.βdagger := by
      have hvα : p.v + α ≤ p.v + 1 := by linarith
      have hfirst : α * (p.v + α) ≤ α * (p.v + 1) :=
        mul_le_mul_of_nonneg_left hvα hαmem.le
      have hvOne : 0 < p.v + 1 := by linarith [model.v_pos]
      have hαd' : α ≤ (1 - weighted.βdagger) / (p.v + 1) := by
        simpa only [d] using hαd.le
      exact hfirst.trans ((le_div_iff₀ hvOne).mp hαd')
    simpa only [A, C] using civicQuasipotentialAtRate_upper_bound
      model ss hρ hρcure hcoop weighted hL hαmem hαbase.le hαone.le hroom
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlowerTendsto hupperTendsto hlowerEventually hupperEventually

/-- At an oriented weighted saddle, the limiting barrier is exactly twice
the integral displayed in `cor:qplimit`. -/
theorem smallRateQuasipotentialBarrier_eq
    {p : LoopParams} (model : DriftModelAssumptions p) {ρ : ℝ}
    (weighted : WeightedThresholdAssumption p ρ) :
    smallRateQuasipotentialBarrier p ρ =
      2 * weightedBarrierArea weighted := by
  simp only [smallRateQuasipotentialBarrier,
    weightedBarrierAreaFamily_eq model weighted]

/-- The limit in `cor:qplimit` has the claimed elementary logarithmic closed
form. -/
theorem smallRateQuasipotentialBarrier_closedForm
    {p : LoopParams} (model : DriftModelAssumptions p) {ρ : ℝ}
    (weighted : WeightedThresholdAssumption p ρ) :
    smallRateQuasipotentialBarrier p ρ =
      2 * (weightedBarrierClosedPrimitive p ρ weighted.βdagger -
        weightedBarrierClosedPrimitive p ρ 0) := by
  rw [smallRateQuasipotentialBarrier_eq model weighted,
    weightedBarrierArea_closedForm model weighted]

/-- The derivative of the small-rate limit is twice the integrated
characteristic stock, as claimed in `cor:qplimit`. -/
theorem hasDerivAt_smallRateQuasipotentialBarrier
    {p : LoopParams} (model : DriftModelAssumptions p) {ρ : ℝ}
    (weighted : WeightedThresholdAssumption p ρ) :
    HasDerivAt (smallRateQuasipotentialBarrier p)
      (2 * ∫ b in (0 : ℝ)..weighted.βdagger, p.stationaryStock b) ρ := by
  exact (hasDerivAt_weightedBarrierAreaFamily model weighted).const_mul 2

/-- Paper II, Corollary `cor:qplimit`, `civic_drift.tex:376`: the complete
small-rate conclusion, collecting convergence, the logarithmic closed form,
and the exact civic-weight derivative.  The weighted-threshold bundle is
constructed from the corollary's printed hypotheses by
`weightedThresholdAutomatic`. -/
theorem smallRateQuasipotentialLimit
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρcure : ρ < cureThreshold p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p ρ) :
    Tendsto (fun α : ℝ ↦ α * civicQuasipotentialAtRate p ρ α)
        (nhdsWithin 0 (Ioi (0 : ℝ)))
        (𝓝 (2 * weightedBarrierArea weighted)) ∧
      smallRateQuasipotentialBarrier p ρ =
        2 * (weightedBarrierClosedPrimitive p ρ weighted.βdagger -
          weightedBarrierClosedPrimitive p ρ 0) ∧
      HasDerivAt (smallRateQuasipotentialBarrier p)
        (2 * ∫ b in (0 : ℝ)..weighted.βdagger, p.stationaryStock b) ρ := by
  exact ⟨civicQuasipotentialAtRate_tendsto_barrier
      model ss threshold hρ hρcure hcoop weighted,
    smallRateQuasipotentialBarrier_closedForm model weighted,
    hasDerivAt_smallRateQuasipotentialBarrier model weighted⟩

#print axioms civicQuasipotentialAtRate_lower_bound
#print axioms civicQuasipotentialAtRate_upper_bound
#print axioms civicQuasipotentialAtRate_tendsto_barrier
#print axioms smallRateQuasipotentialBarrier_eq
#print axioms smallRateQuasipotentialBarrier_closedForm
#print axioms hasDerivAt_smallRateQuasipotentialBarrier
#print axioms smallRateQuasipotentialLimit

end

end CivicAlignment.PaperII
