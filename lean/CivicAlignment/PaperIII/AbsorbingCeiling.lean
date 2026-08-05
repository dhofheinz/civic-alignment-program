/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.Certificate

/-!
# Paper III: the monotonicity-ceiling absorbing box

The box `B = [0,1] × [I, I/(λ₀-g)]` of `thm:classify` (`civic_loops.tex:130`)
is invariant but
not absorbing — the Paper II counterexample transfers with `λ₀ → λ₀ - g`.

This file ports the Paper II argument.  The ceiling is raised to the level at
which monotonicity binds, `M := 1/(2αc²)`; under a *strict* step-size condition
`M > I/(λ₀-g)`, and `[0,1] × [I, M]` is invariant, cooperative by construction,
and absorbing from any nonnegative initial stock.
-/

namespace CivicAlignment.PaperIII

open Filter Set Topology

noncomputable section

/-- Strict form of Paper III's step-size condition `(SS_g)`. -/
structure StrictStepSize (p : LoopParams) : Prop where
  bound : 2 * p.α * p.c ^ 2 * p.I < p.lambda₀ - p.g

/-- The captured stationary stock, the upper face of `B`. -/
def stockCeiling (p : LoopParams) : ℝ := p.I / (p.lambda₀ - p.g)

/-- The stock level at which `1 - 2αc²D ≥ 0` binds. -/
def monotonicityCeiling (p : LoopParams) : ℝ := 1 / (2 * p.α * p.c ^ 2)

/-- The enlarged box, cooperative by construction. -/
def ceilingBox (p : LoopParams) : Set LoopState :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc p.I (monotonicityCeiling p)

section Geometry

variable {p : LoopParams}

theorem twoAlphaCSq_pos (model : LoopModelAssumptions p) :
    0 < 2 * p.α * p.c ^ 2 := by
  have hα := model.α_pos
  have hc := model.c_pos
  positivity

/-- **Strictness opens the gap.** Under strict `(SS_g)` the monotonicity ceiling
lies strictly above the captured stationary stock. -/
theorem stockCeiling_lt_monotonicityCeiling (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) (ss : StrictStepSize p) :
    stockCeiling p < monotonicityCeiling p := by
  have hα := twoAlphaCSq_pos model
  have hgap : 0 < p.lambda₀ - p.g := sub_pos.mpr hgain
  have hαne : p.α ≠ 0 := ne_of_gt model.α_pos
  have hcne : p.c ≠ 0 := ne_of_gt model.c_pos
  have hgapne : p.lambda₀ - p.g ≠ 0 := ne_of_gt hgap
  rw [stockCeiling, monotonicityCeiling, ← sub_pos]
  have hrw : 1 / (2 * p.α * p.c ^ 2) - p.I / (p.lambda₀ - p.g)
      = (p.lambda₀ - p.g - 2 * p.α * p.c ^ 2 * p.I)
        / (2 * p.α * p.c ^ 2 * (p.lambda₀ - p.g)) := by
    field_simp
  rw [hrw]
  exact div_pos (by linarith [ss.bound]) (by positivity)

/-- `I ≤ (λ₀ - g) M`: the algebraic content of invariance at the upper face. -/
theorem injection_le_gap_mul_ceiling (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) (ss : StrictStepSize p) :
    p.I ≤ (p.lambda₀ - p.g) * monotonicityCeiling p := by
  have h := stockCeiling_lt_monotonicityCeiling model hgain ss
  rw [stockCeiling, div_lt_iff₀ (sub_pos.mpr hgain)] at h
  nlinarith [h]

/-- **Invariance.** The enlarged box maps into itself. -/
theorem ceilingBox_invariant (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) (ss : StrictStepSize p) :
    Set.MapsTo p.loopMap (ceilingBox p) (ceilingBox p) := by
  intro y hy
  have hβ : y.1 ∈ Set.Icc (0 : ℝ) 1 := hy.1
  have hD : y.2 ∈ Set.Icc p.I (monotonicityCeiling p) := hy.2
  have hs := stockMultiplier_nonneg_le model hβ
  have hDnonneg : 0 ≤ y.2 := le_trans model.I_pos.le hD.1
  refine ⟨LoopParams.clipUnit_mem _, ?_, ?_⟩
  · simp only [LoopParams.loopMap, LoopParams.stockStep]
    have : 0 ≤ (p.s y.1 + p.g) * y.2 :=
      mul_nonneg (by linarith [hs.1, model.g_nonneg]) hDnonneg
    linarith
  · simp only [LoopParams.loopMap, LoopParams.stockStep]
    have hmult : p.s y.1 + p.g ≤ 1 - p.lambda₀ + p.g := by linarith [hs.2]
    have hstep : (p.s y.1 + p.g) * y.2
        ≤ (1 - p.lambda₀ + p.g) * monotonicityCeiling p := by
      exact mul_le_mul hmult hD.2 hDnonneg
        (by linarith [model.lambda₀_lt_one, model.g_nonneg])
    have hface := injection_le_gap_mul_ceiling model hgain ss
    nlinarith [hstep, hface]

/-- **The engine of absorption.** The stock excess above `I/(λ₀-g)` contracts by
`1-λ₀+g` per step, uniformly in the policy. -/
theorem excess_contraction (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β D : ℝ} (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hD : 0 ≤ D) :
    p.stockStep β D - stockCeiling p
      ≤ (1 - p.lambda₀ + p.g) * (D - stockCeiling p) := by
  have hs := stockMultiplier_nonneg_le model hβ
  have hgapne : p.lambda₀ - p.g ≠ 0 := ne_of_gt (sub_pos.mpr hgain)
  have hgap : (1 - p.lambda₀ + p.g) * stockCeiling p = stockCeiling p - p.I := by
    simp only [stockCeiling]
    field_simp
    ring
  simp only [LoopParams.stockStep]
  have hmul : p.s β * D ≤ (1 - p.lambda₀) * D :=
    mul_le_mul_of_nonneg_right hs.2 hD
  nlinarith [hmul, hgap]

/-- **Cooperativity is free on the enlarged box.** `D ≤ M` *is* the condition
`1 - 2αc²D ≥ 0`, so no step-size assumption is needed. -/
theorem monotonicity_coefficient_nonneg (model : LoopModelAssumptions p)
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

end Geometry

section Absorption

variable {p : LoopParams} {x : ℕ → LoopState}

/-- A state sequence follows the simultaneous Paper III loop map. -/
def IsLoopOrbit (p : LoopParams) (x : ℕ → LoopState) : Prop :=
  ∀ n, x (n + 1) = p.loopMap (x n)

theorem policy_mem_unit (traj : IsLoopOrbit p x)
    (hβ0 : (x 0).1 ∈ Set.Icc (0 : ℝ) 1) : ∀ n, (x n).1 ∈ Set.Icc (0 : ℝ) 1 := by
  intro n
  cases n with
  | zero => exact hβ0
  | succ k => rw [traj k]; exact LoopParams.clipUnit_mem _

theorem stock_nonneg (model : LoopModelAssumptions p) (traj : IsLoopOrbit p x)
    (hβ0 : (x 0).1 ∈ Set.Icc (0 : ℝ) 1) (hD0 : 0 ≤ (x 0).2) :
    ∀ n, 0 ≤ (x n).2 := by
  intro n
  induction n with
  | zero => exact hD0
  | succ k ih =>
      rw [traj k]
      have hs := stockMultiplier_nonneg_le model (policy_mem_unit traj hβ0 k)
      simp only [LoopParams.loopMap, LoopParams.stockStep]
      have : 0 ≤ (p.s (x k).1 + p.g) * (x k).2 :=
        mul_nonneg (by linarith [hs.1, model.g_nonneg]) ih
      linarith [model.I_pos]

theorem injection_le_stock_succ (model : LoopModelAssumptions p)
    (traj : IsLoopOrbit p x) (hβ0 : (x 0).1 ∈ Set.Icc (0 : ℝ) 1)
    (hD0 : 0 ≤ (x 0).2) (n : ℕ) : p.I ≤ (x (n + 1)).2 := by
  rw [traj n]
  have hs := stockMultiplier_nonneg_le model (policy_mem_unit traj hβ0 n)
  simp only [LoopParams.loopMap, LoopParams.stockStep]
  have : 0 ≤ (p.s (x n).1 + p.g) * (x n).2 :=
    mul_nonneg (by linarith [hs.1, model.g_nonneg])
      (stock_nonneg model traj hβ0 hD0 n)
  linarith

theorem excess_le_geometric (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) (traj : IsLoopOrbit p x)
    (hβ0 : (x 0).1 ∈ Set.Icc (0 : ℝ) 1) (hD0 : 0 ≤ (x 0).2) : ∀ n,
    (x n).2 - stockCeiling p
      ≤ (1 - p.lambda₀ + p.g) ^ n * ((x 0).2 - stockCeiling p) := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      have hstep : (x (k + 1)).2 - stockCeiling p
          ≤ (1 - p.lambda₀ + p.g) * ((x k).2 - stockCeiling p) := by
        rw [traj k]
        exact excess_contraction model hgain (policy_mem_unit traj hβ0 k)
          (stock_nonneg model traj hβ0 hD0 k)
      have hbase : (0 : ℝ) ≤ 1 - p.lambda₀ + p.g := by
        linarith [model.lambda₀_lt_one, model.g_nonneg]
      have hmul := mul_le_mul_of_nonneg_left ih hbase
      calc (x (k + 1)).2 - stockCeiling p
          ≤ (1 - p.lambda₀ + p.g) * ((x k).2 - stockCeiling p) := hstep
        _ ≤ (1 - p.lambda₀ + p.g)
              * ((1 - p.lambda₀ + p.g) ^ k * ((x 0).2 - stockCeiling p)) := hmul
        _ = (1 - p.lambda₀ + p.g) ^ (k + 1) * ((x 0).2 - stockCeiling p) := by ring

/--
**`thm:classify`'s box clause.** `B` is invariant but not absorbing;
the enlarged box `[0,1] × [I, 1/(2αc²)]` is absorbing, from any nonnegative
initial stock and with no hypothesis on `D₀`.
-/
theorem ceilingBox_absorbing (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) (ss : StrictStepSize p) (traj : IsLoopOrbit p x)
    (hβ0 : (x 0).1 ∈ Set.Icc (0 : ℝ) 1) (hD0 : 0 ≤ (x 0).2) :
    ∃ T, ∀ t, T ≤ t → x t ∈ ceilingBox p := by
  set gap := monotonicityCeiling p - stockCeiling p with hgapdef
  have hgap : 0 < gap :=
    sub_pos.mpr (stockCeiling_lt_monotonicityCeiling model hgain ss)
  have hbase : (0 : ℝ) ≤ 1 - p.lambda₀ + p.g := by
    linarith [model.lambda₀_lt_one, model.g_nonneg]
  have hlt : (1 : ℝ) - p.lambda₀ + p.g < 1 := by linarith [hgain]
  have hpow : Tendsto (fun n : ℕ => (1 - p.lambda₀ + p.g) ^ n
      * ((x 0).2 - stockCeiling p)) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hbase hlt).mul_const
      ((x 0).2 - stockCeiling p)
  obtain ⟨T, hT⟩ := (hpow.eventually_lt_const hgap).exists_forall_of_atTop
  refine ⟨T + 1, fun t ht => ?_⟩
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  refine ⟨policy_mem_unit traj hβ0 _, injection_le_stock_succ model traj hβ0 hD0 s, ?_⟩
  have hdecay := excess_le_geometric model hgain traj hβ0 hD0 (s + 1)
  have hsmall := hT (s + 1) (by omega)
  have hlt' : (x (s + 1)).2 - stockCeiling p < gap := lt_of_le_of_lt hdecay hsmall
  rw [hgapdef] at hlt'
  linarith

end Absorption

#print axioms stockCeiling_lt_monotonicityCeiling
#print axioms ceilingBox_invariant
#print axioms excess_contraction
#print axioms monotonicity_coefficient_nonneg
#print axioms ceilingBox_absorbing

end

end CivicAlignment.PaperIII
