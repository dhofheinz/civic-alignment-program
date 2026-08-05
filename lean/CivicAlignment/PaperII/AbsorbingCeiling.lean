/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.Bistability

/-!
# Paper II: the monotonicity-ceiling absorbing box

The compact box `B = [0,1] × [I, I/λ₀]` of `lem:box` (`civic_drift.tex:223`)
is invariant but not absorbing:
`absorbingBox_nonentry_counterexample` exhibits a captured trajectory staying
strictly above the upper face at every finite time.

Absorption holds once the ceiling is raised to the level at which monotonicity itself binds,
`M := 1/(2αc²)`.  Under a *strict* small-step condition `M > I/λ₀`, and the
enlarged box `[0,1] × [I, M]` is simultaneously

* **cooperative** — `D ≤ M` is exactly the condition `1 - 2αc²D ≥ 0`,
* **invariant**, and
* **absorbing**, because the stock excess above `I/λ₀` contracts geometrically
  uniformly in the policy.

That is what `thm:bistable`(i) needs, with no hypothesis on the initial stock.
Strictness is load-bearing: at equality the gap `M - I/λ₀` closes and absorption
fails, which is exactly the configuration the counterexample exploits.
-/

namespace CivicAlignment.PaperII

open Filter Set Topology

noncomputable section

/-- Strict form of Paper II's small-step condition (SS). -/
structure StrictSmallStepAssumption (p : LoopParams) : Prop where
  bound : 2 * p.α * p.c ^ 2 * p.I < p.lambda₀

/-- Strictness implies the weak small-step condition used elsewhere. -/
theorem StrictSmallStepAssumption.toSmallStep {p : LoopParams}
    (ss : StrictSmallStepAssumption p) : SmallStepAssumption p :=
  ⟨le_of_lt ss.bound⟩

/-- The stock level at which the monotonicity condition `1 - 2αc²D ≥ 0` binds. -/
def monotonicityCeiling (p : LoopParams) : ℝ := 1 / (2 * p.α * p.c ^ 2)

/-- The enlarged box, cooperative by construction. -/
def ceilingBox (p : LoopParams) : Set LoopState :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc p.I (monotonicityCeiling p)

section Geometry

variable {p : LoopParams}

theorem twoAlphaCSq_pos (model : DriftModelAssumptions p) :
    0 < 2 * p.α * p.c ^ 2 := by
  have hα := model.α_pos
  have hc := model.c_pos
  positivity

theorem monotonicityCeiling_pos (model : DriftModelAssumptions p) :
    0 < monotonicityCeiling p :=
  one_div_pos.mpr (twoAlphaCSq_pos model)

/-- **Strictness is exactly what opens the gap.** Under the strict small-step
condition the monotonicity ceiling lies strictly above the captured stationary
stock `I/λ₀`. -/
theorem stockCeiling_lt_monotonicityCeiling (model : DriftModelAssumptions p)
    (ss : StrictSmallStepAssumption p) :
    p.I / p.lambda₀ < monotonicityCeiling p := by
  have hα := twoAlphaCSq_pos model
  have hlam := model.lambda₀_pos
  have hαne : p.α ≠ 0 := ne_of_gt model.α_pos
  have hcne : p.c ≠ 0 := ne_of_gt model.c_pos
  have hlamne : p.lambda₀ ≠ 0 := ne_of_gt hlam
  rw [monotonicityCeiling, ← sub_pos]
  have hrw : 1 / (2 * p.α * p.c ^ 2) - p.I / p.lambda₀
      = (p.lambda₀ - 2 * p.α * p.c ^ 2 * p.I) / (2 * p.α * p.c ^ 2 * p.lambda₀) := by
    field_simp
  rw [hrw]
  exact div_pos (by linarith [ss.bound]) (by positivity)

/-- The original box sits inside the enlarged one. -/
theorem absorbingBox_subset_ceilingBox (model : DriftModelAssumptions p)
    (ss : StrictSmallStepAssumption p) :
    absorbingBox p ⊆ ceilingBox p := fun _ hx =>
  ⟨hx.1, hx.2.1, hx.2.2.trans (stockCeiling_lt_monotonicityCeiling model ss).le⟩

/-- `I ≤ λ₀ M`: the algebraic content of invariance at the upper face. -/
theorem injection_le_lambda_mul_ceiling (model : DriftModelAssumptions p)
    (ss : StrictSmallStepAssumption p) :
    p.I ≤ p.lambda₀ * monotonicityCeiling p := by
  have h := stockCeiling_lt_monotonicityCeiling model ss
  rw [div_lt_iff₀ model.lambda₀_pos] at h
  nlinarith [h]

/-- **Invariance.** The enlarged box maps into itself. -/
theorem ceilingBox_invariant (model : DriftModelAssumptions p)
    (ss : StrictSmallStepAssumption p) :
    Set.MapsTo p.loopMap (ceilingBox p) (ceilingBox p) := by
  intro y hy
  have hβ : y.1 ∈ Set.Icc (0 : ℝ) 1 := hy.1
  have hD : y.2 ∈ Set.Icc p.I (monotonicityCeiling p) := hy.2
  have hs := driftStockMultiplier_nonneg_le model hβ
  have hDnonneg : 0 ≤ y.2 := le_trans model.I_pos.le hD.1
  refine ⟨LoopParams.clipUnit_mem _, ?_, ?_⟩
  · simp only [LoopParams.loopMap, LoopParams.stockStep, model.no_content_gain, add_zero]
    exact le_add_of_nonneg_left (mul_nonneg hs.1 hDnonneg)
  · simp only [LoopParams.loopMap, LoopParams.stockStep, model.no_content_gain, add_zero]
    have hstep : p.s y.1 * y.2 ≤ (1 - p.lambda₀) * monotonicityCeiling p :=
      mul_le_mul hs.2 hD.2 hDnonneg (by linarith [model.lambda₀_lt_one])
    have hface := injection_le_lambda_mul_ceiling model ss
    nlinarith [hstep, hface]

/-- **The engine of absorption.** The stock excess above `I/λ₀` contracts by a
factor `1-λ₀` per step, uniformly in the policy — so no adaptation rule can
prevent it. -/
theorem excess_contraction (model : DriftModelAssumptions p)
    {β D : ℝ} (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hD : 0 ≤ D) :
    p.stockStep β D - p.I / p.lambda₀
      ≤ (1 - p.lambda₀) * (D - p.I / p.lambda₀) := by
  have hs := driftStockMultiplier_nonneg_le model hβ
  have hlambda : p.lambda₀ ≠ 0 := ne_of_gt model.lambda₀_pos
  have hgap : (1 - p.lambda₀) * (p.I / p.lambda₀) = p.I / p.lambda₀ - p.I := by
    field_simp
  simp only [LoopParams.stockStep, model.no_content_gain, add_zero]
  have hmul : p.s β * D ≤ (1 - p.lambda₀) * D :=
    mul_le_mul_of_nonneg_right hs.2 hD
  nlinarith [hmul, hgap]

/-- **Cooperativity is free on the enlarged box.** `D ≤ M` *is* the condition
`1 - 2αc²D ≥ 0`, so no step-size assumption is needed here — unlike on `B`,
where it must be imported from (SS). -/
theorem monotonicity_coefficient_nonneg (model : DriftModelAssumptions p)
    {D : ℝ} (hD : D ≤ monotonicityCeiling p) :
    0 ≤ 1 - 2 * p.α * p.c ^ 2 * D := by
  have hα := twoAlphaCSq_pos model
  have hαne : p.α ≠ 0 := ne_of_gt model.α_pos
  have hcne : p.c ≠ 0 := ne_of_gt model.c_pos
  have hscaled : 2 * p.α * p.c ^ 2 * D ≤ 2 * p.α * p.c ^ 2 * monotonicityCeiling p :=
    mul_le_mul_of_nonneg_left hD hα.le
  have heq : 2 * p.α * p.c ^ 2 * monotonicityCeiling p = 1 := by
    simp only [monotonicityCeiling]
    field_simp
  linarith [hscaled, heq]

/-- Policy-monotonicity of the unprojected controller, on the enlarged box. -/
theorem unclippedDeferenceInput_mono_policy_ceiling (model : DriftModelAssumptions p)
    {β₁ β₂ D : ℝ} (hβ : β₁ ≤ β₂) (hD : D ≤ monotonicityCeiling p) :
    unclippedDeferenceInput p β₁ D ≤ unclippedDeferenceInput p β₂ D := by
  have hcoefficient := monotonicity_coefficient_nonneg model hD
  have hproduct := mul_nonneg (sub_nonneg.mpr hβ) hcoefficient
  simp only [unclippedDeferenceInput, LoopParams.gradU]
  nlinarith

/-- **`lem:mono` on the enlarged box.** The simultaneous map is order-preserving
on `[0,1] × [I, M]`, so the cooperative structure `thm:bistable`(i) relies on
survives the enlargement. -/
theorem loopMap_monotoneOn_ceilingBox (model : DriftModelAssumptions p) :
    MonotoneOn p.loopMap (ceilingBox p) := by
  intro y hy z hz hyz
  have hβz : z.1 ∈ Set.Icc (0 : ℝ) 1 := hz.1
  have hβy : y.1 ∈ Set.Icc (0 : ℝ) 1 := hy.1
  have hDy : y.2 ∈ Set.Icc p.I (monotonicityCeiling p) := hy.2
  have hdeferencePolicy :=
    unclippedDeferenceInput_mono_policy_ceiling model hyz.1 hDy.2
  have hdeferenceStock := unclippedDeferenceInput_mono_stock model hβz hyz.2
  have hdeference : p.deferenceStep y.1 y.2 ≤ p.deferenceStep z.1 z.2 :=
    LoopParams.monotone_clipUnit (hdeferencePolicy.trans hdeferenceStock)
  have hsOrder : p.s y.1 ≤ p.s z.1 :=
    (driftStockMultiplier_strictMonoOn model).monotoneOn hβy hβz hyz.1
  have hsZ : 0 ≤ p.s z.1 := (driftStockMultiplier_nonneg_le model hβz).1
  have hDyNonneg : 0 ≤ y.2 := le_trans model.I_pos.le hDy.1
  have hstockPolicy : p.s y.1 * y.2 ≤ p.s z.1 * y.2 :=
    mul_le_mul_of_nonneg_right hsOrder hDyNonneg
  have hstockStock : p.s z.1 * y.2 ≤ p.s z.1 * z.2 :=
    mul_le_mul_of_nonneg_left hyz.2 hsZ
  have hstock : p.stockStep y.1 y.2 ≤ p.stockStep z.1 z.2 := by
    simp only [LoopParams.stockStep, model.no_content_gain, add_zero]
    linarith [hstockPolicy.trans hstockStock]
  exact ⟨hdeference, hstock⟩

end Geometry

section Absorption

variable {p : LoopParams} {x : ℕ → LoopState}

/-- Policy coordinates lie in `[0,1]` at every time. -/
theorem policy_mem_unit (traj : IsLoopTrajectory p x)
    (hβ0 : (x 0).1 ∈ Set.Icc (0 : ℝ) 1) : ∀ n, (x n).1 ∈ Set.Icc (0 : ℝ) 1 := by
  intro n
  cases n with
  | zero => exact hβ0
  | succ k =>
      rw [traj k]
      exact LoopParams.clipUnit_mem _

/-- Stocks stay nonnegative. -/
theorem stock_nonneg (model : DriftModelAssumptions p) (traj : IsLoopTrajectory p x)
    (hβ0 : (x 0).1 ∈ Set.Icc (0 : ℝ) 1) (hD0 : 0 ≤ (x 0).2) :
    ∀ n, 0 ≤ (x n).2 := by
  intro n
  induction n with
  | zero => exact hD0
  | succ k ih =>
      rw [traj k]
      have hs := driftStockMultiplier_nonneg_le model (policy_mem_unit traj hβ0 k)
      simp only [LoopParams.loopMap, LoopParams.stockStep, model.no_content_gain, add_zero]
      have := mul_nonneg hs.1 ih
      linarith [model.I_pos]

/-- From the first step on, the stock is at least the injection rate. -/
theorem injection_le_stock_succ (model : DriftModelAssumptions p)
    (traj : IsLoopTrajectory p x) (hβ0 : (x 0).1 ∈ Set.Icc (0 : ℝ) 1)
    (hD0 : 0 ≤ (x 0).2) (n : ℕ) : p.I ≤ (x (n + 1)).2 := by
  rw [traj n]
  have hs := driftStockMultiplier_nonneg_le model (policy_mem_unit traj hβ0 n)
  simp only [LoopParams.loopMap, LoopParams.stockStep, model.no_content_gain, add_zero]
  exact le_add_of_nonneg_left
    (mul_nonneg hs.1 (stock_nonneg model traj hβ0 hD0 n))

/-- Geometric decay of the stock excess above `I/λ₀`. -/
theorem excess_le_geometric (model : DriftModelAssumptions p)
    (traj : IsLoopTrajectory p x) (hβ0 : (x 0).1 ∈ Set.Icc (0 : ℝ) 1)
    (hD0 : 0 ≤ (x 0).2) : ∀ n,
    (x n).2 - p.I / p.lambda₀
      ≤ (1 - p.lambda₀) ^ n * ((x 0).2 - p.I / p.lambda₀) := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      have hstep : (x (k + 1)).2 - p.I / p.lambda₀
          ≤ (1 - p.lambda₀) * ((x k).2 - p.I / p.lambda₀) := by
        rw [traj k]
        exact excess_contraction model (policy_mem_unit traj hβ0 k)
          (stock_nonneg model traj hβ0 hD0 k)
      have hmul : (1 - p.lambda₀) * ((x k).2 - p.I / p.lambda₀)
          ≤ (1 - p.lambda₀) * ((1 - p.lambda₀) ^ k * ((x 0).2 - p.I / p.lambda₀)) :=
        mul_le_mul_of_nonneg_left ih (by linarith [model.lambda₀_lt_one])
      calc (x (k + 1)).2 - p.I / p.lambda₀
          ≤ (1 - p.lambda₀) * ((x k).2 - p.I / p.lambda₀) := hstep
        _ ≤ (1 - p.lambda₀) * ((1 - p.lambda₀) ^ k * ((x 0).2 - p.I / p.lambda₀)) := hmul
        _ = (1 - p.lambda₀) ^ (k + 1) * ((x 0).2 - p.I / p.lambda₀) := by ring

/--
**`lem:box`.** The enlarged box `[0,1] × [I, 1/(2αc²)]` is absorbing:
every trajectory enters it in finite time and stays, from *any* nonnegative
initial stock. Combined with `ceilingBox_invariant` and the monotonicity
condition `D ≤ M`, this is what `thm:bistable`(i) needs — with no hypothesis on
`D₀`, which a ceiling of `max(D₀, I/λ₀)` cannot avoid.
-/
theorem ceilingBox_absorbing (model : DriftModelAssumptions p)
    (ss : StrictSmallStepAssumption p) (traj : IsLoopTrajectory p x)
    (hβ0 : (x 0).1 ∈ Set.Icc (0 : ℝ) 1) (hD0 : 0 ≤ (x 0).2) :
    ∃ T, ∀ t, T ≤ t → x t ∈ ceilingBox p := by
  set gap := monotonicityCeiling p - p.I / p.lambda₀ with hgapdef
  have hgap : 0 < gap := sub_pos.mpr (stockCeiling_lt_monotonicityCeiling model ss)
  have hbase : (0 : ℝ) ≤ 1 - p.lambda₀ := by linarith [model.lambda₀_lt_one]
  have hlt : (1 : ℝ) - p.lambda₀ < 1 := by linarith [model.lambda₀_pos]
  have hpow : Tendsto (fun n : ℕ => (1 - p.lambda₀) ^ n
      * ((x 0).2 - p.I / p.lambda₀)) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hbase hlt).mul_const
      ((x 0).2 - p.I / p.lambda₀)
  obtain ⟨T, hT⟩ := (hpow.eventually_lt_const hgap).exists_forall_of_atTop
  refine ⟨T + 1, fun t ht => ?_⟩
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  refine ⟨policy_mem_unit traj hβ0 _, injection_le_stock_succ model traj hβ0 hD0 s, ?_⟩
  have hdecay := excess_le_geometric model traj hβ0 hD0 (s + 1)
  have hsmall := hT (s + 1) (by omega)
  have : (x (s + 1)).2 - p.I / p.lambda₀ < gap := lt_of_le_of_lt hdecay hsmall
  rw [hgapdef] at this
  linarith

end Absorption

#print axioms stockCeiling_lt_monotonicityCeiling
#print axioms ceilingBox_invariant
#print axioms excess_contraction
#print axioms loopMap_monotoneOn_ceilingBox
#print axioms ceilingBox_absorbing

end

end CivicAlignment.PaperII
