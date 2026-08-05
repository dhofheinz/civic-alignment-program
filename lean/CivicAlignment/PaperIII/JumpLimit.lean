/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.Certificate
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.ProjIcc

/-!
# Paper III: the rescaled jump-map limit

This file isolates the exact algebra behind `thm:jump`.  In rescaled excess
coordinates, the full simultaneous loop has a continuous extension to zero
adaptation rate.  Its zero-rate map is the interval-projected jump map.  The
raw jump map printed in the paper is recovered when every compared jump stays
inside the policy interval.

The separatrix limit is proved in `PaperIII/SeparatrixLimit.lean`.  The
uniform linear-horizon estimate, named logarithmic projected stopping horizon,
and exact-orbit joint-range consequence are proved in
`PaperIII/JumpGrowingHorizon.lean`.
-/

namespace CivicAlignment.PaperIII

open Filter Function Set Topology

noncomputable section

/-! ## Rescaled and limiting maps -/

/-- Replace only the operator adaptation rate in a loop parameter bundle. -/
def withAdaptationRate (p : LoopParams) (α : ℝ) : LoopParams :=
  { p with α := α }

/-- The coefficient `A(β)=2c(1-cβ)` in Paper III's jump map. -/
def jumpGain (p : LoopParams) (β : ℝ) : ℝ :=
  2 * p.c * (1 - p.c * β)

/-- The stock multiplier `σ(β)=s(β)+g` in Paper III's jump map. -/
def jumpPersistence (p : LoopParams) (β : ℝ) : ℝ :=
  p.s β + p.g

/-- Paper III's displayed, unprojected jump map. -/
def jumpMap (p : LoopParams) (x : LoopState) : LoopState :=
  (x.1 + jumpGain p x.1 * x.2, jumpPersistence p x.1 * x.2)

/--
The globally faithful limiting map.  The full loop projects policy to `[0,1]`,
so its literal zero-rate limit retains that projection.
-/
def projectedJumpMap (p : LoopParams) (x : LoopState) : LoopState :=
  (LoopParams.clipUnit (x.1 + jumpGain p x.1 * x.2),
    jumpPersistence p x.1 * x.2)

/-- An admissible projected jump orbit has policy supremum strictly below the
saddle.  The admissibility interval is the one fixed in `prop:burn`. -/
def JumpOrbitUniformlyBelow
    (p : LoopParams) (βdagger β₀ excess₀ : ℝ) : Prop :=
  0 ≤ excess₀ ∧ 2 * p.c ^ 2 * excess₀ < 1 ∧
    sSup (Set.range fun t : ℕ ↦
      (((projectedJumpMap p)^[t]) (β₀, excess₀)).1) < βdagger

/-- The projected jump-map separatrix scale `κ*(β₀)` defined in
`rem:sepscale`, restricted to the admissible interval of `prop:burn`. -/
noncomputable def jumpSeparatrixScale
    (p : LoopParams) (βdagger β₀ : ℝ) : ℝ :=
  sSup {excess₀ : ℝ | JumpOrbitUniformlyBelow p βdagger β₀ excess₀}

/-- The left-endpoint stock-excess burn rate `(1-σ(β))/A(β)`. -/
def jumpBurnRate (p : LoopParams) (β : ℝ) : ℝ :=
  (1 - jumpPersistence p β) / jumpGain p β

/-- The continuum integral `K(β₀)` displayed in `thm:jump`. -/
noncomputable def jumpContinuumApproximation
    (p : LoopParams) (β₀ βdagger : ℝ) : ℝ :=
  ∫ β in β₀..βdagger, jumpBurnRate p β

/-- Convert a stock state to the paper's rescaled excess coordinates. -/
def rescaleStockExcess (p : LoopParams) (α : ℝ) (x : LoopState) : LoopState :=
  (x.1, α * (x.2 - p.stationaryStock x.1))

/-- Reconstruct a stock state from nonzero-rate rescaled excess coordinates. -/
def unscaleStockExcess (p : LoopParams) (α : ℝ) (x : LoopState) : LoopState :=
  (x.1, p.stationaryStock x.1 + x.2 / α)

/--
The exact rescaled full step, continuously extended to `α=0`.  The second
coordinate contains the moving-stationary-stock correction omitted at leading
order in the paper's derivation.
-/
def scaledLoopMap (p : LoopParams) (α : ℝ) (x : LoopState) : LoopState :=
  let β' := LoopParams.clipUnit
    (x.1 + jumpGain p x.1 * x.2 + α * p.G x.1)
  (β', jumpPersistence p x.1 * x.2 +
    α * (p.stationaryStock x.1 - p.stationaryStock β'))

/-- The rescaled map at zero rate is exactly the projected jump map. -/
theorem scaledLoopMap_zero (p : LoopParams) (x : LoopState) :
    scaledLoopMap p 0 x = projectedJumpMap p x := by
  simp [scaledLoopMap, projectedJumpMap]

/-- The projected and displayed jump maps agree for an interior retained step. -/
theorem projectedJumpMap_eq_jumpMap {p : LoopParams} {x : LoopState}
    (hstep : x.1 + jumpGain p x.1 * x.2 ∈ Icc (0 : ℝ) 1) :
    projectedJumpMap p x = jumpMap p x := by
  simp only [projectedJumpMap, jumpMap]
  rw [clipUnit_eq_self hstep]

/-! ## Exact conjugacy with the simultaneous loop -/

/-- Stationary stock is fixed by the stock law whenever its denominator is nonzero. -/
theorem stockStep_stationaryStock_eq_self_of_ne {p : LoopParams} {β : ℝ}
    (hwall : 1 - p.s β - p.g ≠ 0) :
    p.stockStep β (p.stationaryStock β) = p.stationaryStock β := by
  simp only [LoopParams.stockStep, LoopParams.stationaryStock]
  field_simp [hwall]
  ring

/-- The instantaneous gradient splits into stationary and excess terms. -/
theorem gradU_unscaleStockExcess {p : LoopParams} {α : ℝ} {x : LoopState}
    (hα : α ≠ 0) :
    (withAdaptationRate p α).gradU x.1 (unscaleStockExcess p α x).2 =
      p.G x.1 + jumpGain p x.1 * x.2 / α := by
  simp only [withAdaptationRate, unscaleStockExcess, LoopParams.gradU,
    LoopParams.G, LoopParams.stationaryStock, jumpGain]
  field_simp [hα]
  ring

/--
Paper III, Theorem 7.1 (`thm:jump`), exact one-step rescaling identity,
`civic_loops.tex:463--533`.

At every nonzero adaptation rate, the continuously extended formula
`scaledLoopMap` is exactly the original simultaneous loop conjugated by the
paper's excess-stock rescaling.
-/
theorem rescale_loopMap_unscale_eq_scaledLoopMap
    {p : LoopParams} {α : ℝ} {x : LoopState}
    (hα : α ≠ 0) (hwall : 1 - p.s x.1 - p.g ≠ 0) :
    rescaleStockExcess p α
        ((withAdaptationRate p α).loopMap (unscaleStockExcess p α x)) =
      scaledLoopMap p α x := by
  have hfixed := stockStep_stationaryStock_eq_self_of_ne hwall
  have hgradient := gradU_unscaleStockExcess (p := p) (x := x) hα
  have hpolicy :
      (withAdaptationRate p α).deferenceStep x.1
          (unscaleStockExcess p α x).2 =
        LoopParams.clipUnit
          (x.1 + jumpGain p x.1 * x.2 + α * p.G x.1) := by
    rw [LoopParams.deferenceStep]
    change LoopParams.clipUnit
        (x.1 + α *
          ((withAdaptationRate p α).gradU x.1 (unscaleStockExcess p α x).2)) = _
    rw [hgradient]
    congr 1
    field_simp [hα]
    ring
  have hfixed' :
      (p.s x.1 + p.g) * p.stationaryStock x.1 + p.I =
        p.stationaryStock x.1 := by
    simpa only [LoopParams.stockStep, add_mul] using hfixed
  have hstock :
      (withAdaptationRate p α).stockStep x.1
          (unscaleStockExcess p α x).2 =
        p.stationaryStock x.1 + jumpPersistence p x.1 * x.2 / α := by
    change (p.s x.1 + p.g) *
        (p.stationaryStock x.1 + x.2 / α) + p.I = _
    simp only [jumpPersistence]
    calc
      _ = ((p.s x.1 + p.g) * p.stationaryStock x.1 + p.I) +
          (p.s x.1 + p.g) * (x.2 / α) := by ring
      _ = p.stationaryStock x.1 + (p.s x.1 + p.g) * (x.2 / α) := by
        rw [hfixed']
      _ = _ := by ring
  have hpolicy' :
      (withAdaptationRate p α).deferenceStep x.1
          (p.stationaryStock x.1 + x.2 / α) =
        LoopParams.clipUnit
          (x.1 + jumpGain p x.1 * x.2 + α * p.G x.1) := by
    simpa only [unscaleStockExcess] using hpolicy
  have hstock' :
      (withAdaptationRate p α).stockStep x.1
          (p.stationaryStock x.1 + x.2 / α) =
        p.stationaryStock x.1 + jumpPersistence p x.1 * x.2 / α := by
    simpa only [unscaleStockExcess] using hstock
  simp only [rescaleStockExcess, LoopParams.loopMap, unscaleStockExcess]
  rw [hpolicy', hstock']
  apply Prod.ext
  · rfl
  · simp only [scaledLoopMap, jumpPersistence]
    field_simp [hα]
    ring

/-- Rescaling after unscaling is the identity at every nonzero rate. -/
theorem rescaleStockExcess_unscaleStockExcess
    {p : LoopParams} {α : ℝ} (hα : α ≠ 0) (x : LoopState) :
    rescaleStockExcess p α (unscaleStockExcess p α x) = x := by
  ext <;> simp only [rescaleStockExcess, unscaleStockExcess]
  field_simp [hα]
  ring

/-- Unscaling after rescaling is the identity at every nonzero rate. -/
theorem unscaleStockExcess_rescaleStockExcess
    {p : LoopParams} {α : ℝ} (hα : α ≠ 0) (x : LoopState) :
    unscaleStockExcess p α (rescaleStockExcess p α x) = x := by
  ext <;> simp only [rescaleStockExcess, unscaleStockExcess]
  field_simp [hα]
  ring

/-! ## Fixed-horizon convergence -/

/-- The polynomial stock multiplier is continuous. -/
theorem continuous_s (p : LoopParams) : Continuous p.s := by
  change Continuous
    (fun β : ℝ ↦ (1 - p.lambda₀) * (1 - p.η * (1 - β)) ^ 2)
  fun_prop

/-- The policy projection is continuous: `lem:clip`(i). -/
theorem continuous_clipUnit : Continuous LoopParams.clipUnit := by
  have hfun : LoopParams.clipUnit = clipTo 0 1 := funext clipUnit_eq_clipTo
  rw [hfun]
  exact continuous_clipTo

/-- Below the gain ceiling, the stationary-stock wall is avoided on `[0,1]`. -/
theorem stationaryWall_pos_of_mem {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 < 1 - p.s β - p.g := by
  have hs := stockMultiplier_nonneg_le model hβ
  linarith

/-- The stationary-stock characteristic is continuous away from its wall. -/
theorem continuousAt_stationaryStock_of_ne {p : LoopParams} {β : ℝ}
    (hwall : 1 - p.s β - p.g ≠ 0) :
    ContinuousAt p.stationaryStock β := by
  change ContinuousAt (fun x : ℝ ↦ p.I / (1 - p.s x - p.g)) β
  have hden : ContinuousAt (fun x : ℝ ↦ 1 - p.s x - p.g) β :=
    (continuousAt_const.sub (continuous_s p).continuousAt).sub continuousAt_const
  exact continuousAt_const.div hden hwall

/-- The stationary gradient is continuous away from its wall. -/
theorem continuousAt_G_of_ne {p : LoopParams} {β : ℝ}
    (hwall : 1 - p.s β - p.g ≠ 0) :
    ContinuousAt p.G β := by
  change ContinuousAt
    (fun x : ℝ ↦ -p.v +
      2 * p.c * (1 - p.c * x) * p.I / (1 - p.s x - p.g)) β
  have hden : ContinuousAt (fun x : ℝ ↦ 1 - p.s x - p.g) β :=
    (continuousAt_const.sub (continuous_s p).continuousAt).sub continuousAt_const
  have hnum : ContinuousAt
      (fun x : ℝ ↦ 2 * p.c * (1 - p.c * x) * p.I) β := by
    fun_prop
  exact continuousAt_const.add (hnum.div hden hwall)

/--
The rate-parameterized rescaled step is continuous at rate zero while policy
lies in the paper's interval and content gain remains below grounding.
-/
theorem continuousAt_scaledLoopMap_zero
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {x : LoopState}
    (hx : x.1 ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (fun q : ℝ × LoopState ↦ scaledLoopMap p q.1 q.2) (0, x) := by
  let policy : ℝ × LoopState → ℝ := fun q ↦ q.2.1
  let excess : ℝ × LoopState → ℝ := fun q ↦ q.2.2
  let rate : ℝ × LoopState → ℝ := fun q ↦ q.1
  let policyInput : ℝ × LoopState → ℝ := fun q ↦
    policy q + jumpGain p (policy q) * excess q + rate q * p.G (policy q)
  let nextPolicy : ℝ × LoopState → ℝ := fun q ↦ LoopParams.clipUnit (policyInput q)
  have hpolicy : ContinuousAt policy (0, x) := by
    dsimp only [policy]
    fun_prop
  have hexcess : ContinuousAt excess (0, x) := by
    dsimp only [excess]
    fun_prop
  have hrate : ContinuousAt rate (0, x) := by
    dsimp only [rate]
    fun_prop
  have hwall : 1 - p.s x.1 - p.g ≠ 0 :=
    (stationaryWall_pos_of_mem model hgain hx).ne'
  have hG : ContinuousAt (fun q : ℝ × LoopState ↦ p.G (policy q)) (0, x) := by
    exact (continuousAt_G_of_ne hwall).comp_of_eq hpolicy rfl
  have hjumpGain :
      ContinuousAt (fun q : ℝ × LoopState ↦ jumpGain p (policy q)) (0, x) := by
    dsimp only [jumpGain]
    fun_prop
  have hinput : ContinuousAt policyInput (0, x) := by
    dsimp only [policyInput]
    exact (hpolicy.add (hjumpGain.mul hexcess)).add (hrate.mul hG)
  have hnext : ContinuousAt nextPolicy (0, x) := by
    exact continuous_clipUnit.continuousAt.comp hinput
  have hnextMem : nextPolicy (0, x) ∈ Icc (0 : ℝ) 1 := by
    exact LoopParams.clipUnit_mem _
  have hnextWall : 1 - p.s (nextPolicy (0, x)) - p.g ≠ 0 :=
    (stationaryWall_pos_of_mem model hgain hnextMem).ne'
  have hstock :
      ContinuousAt (fun q : ℝ × LoopState ↦ p.stationaryStock (policy q))
        (0, x) := by
    exact (continuousAt_stationaryStock_of_ne hwall).comp_of_eq hpolicy rfl
  have hnextStock :
      ContinuousAt (fun q : ℝ × LoopState ↦ p.stationaryStock (nextPolicy q))
        (0, x) := by
    exact (continuousAt_stationaryStock_of_ne hnextWall).comp hnext
  have hpersistence :
      ContinuousAt (fun q : ℝ × LoopState ↦ jumpPersistence p (policy q))
        (0, x) := by
    dsimp only [jumpPersistence]
    exact ((continuous_s p).continuousAt.comp hpolicy).add continuousAt_const
  have hsecond : ContinuousAt
      (fun q : ℝ × LoopState ↦
        jumpPersistence p (policy q) * excess q +
          rate q *
            (p.stationaryStock (policy q) - p.stationaryStock (nextPolicy q)))
      (0, x) :=
    (hpersistence.mul hexcess).add (hrate.mul (hstock.sub hnextStock))
  have hpair := hnext.prodMk hsecond
  simpa only [scaledLoopMap, policy, excess, rate, policyInput, nextPolicy] using hpair

/-- A projected jump always returns policy to `[0,1]`. -/
theorem projectedJumpMap_policy_mem (p : LoopParams) (x : LoopState) :
    (projectedJumpMap p x).1 ∈ Icc (0 : ℝ) 1 := by
  exact LoopParams.clipUnit_mem _

/-- Every positive- or zero-rate rescaled step returns policy to `[0,1]`. -/
theorem scaledLoopMap_policy_mem (p : LoopParams) (α : ℝ) (x : LoopState) :
    (scaledLoopMap p α x).1 ∈ Icc (0 : ℝ) 1 := by
  exact LoopParams.clipUnit_mem _

/-- Every projected-jump orbit starting in `[0,1]` stays there. -/
theorem projectedJumpMap_iterate_policy_mem
    {p : LoopParams} {x : LoopState} (hx : x.1 ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    (((projectedJumpMap p)^[n]) x).1 ∈ Icc (0 : ℝ) 1 := by
  cases n with
  | zero => simpa only [iterate_zero_apply] using hx
  | succ n =>
      rw [iterate_succ_apply']
      exact projectedJumpMap_policy_mem p _

/-- Every exact rescaled orbit starting in `[0,1]` stays there. -/
theorem scaledLoopMap_iterate_policy_mem
    {p : LoopParams} {α : ℝ} {x : LoopState}
    (hx : x.1 ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    (((scaledLoopMap p α)^[n]) x).1 ∈ Icc (0 : ℝ) 1 := by
  cases n with
  | zero => simpa only [iterate_zero_apply] using hx
  | succ n =>
      rw [iterate_succ_apply']
      exact scaledLoopMap_policy_mem p α _

/--
At every nonzero rate, rescaling an actual full-loop orbit gives exactly the
orbit of `scaledLoopMap`; this is the finite-time conjugacy used by the limit.
-/
theorem rescale_loopMap_iterate_unscale_eq_scaledLoopMap_iterate
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {α : ℝ} (hα : α ≠ 0)
    {x : LoopState} (hx : x.1 ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    rescaleStockExcess p α
        ((((withAdaptationRate p α).loopMap)^[n])
          (unscaleStockExcess p α x)) =
      ((scaledLoopMap p α)^[n]) x := by
  induction n with
  | zero =>
      simpa only [iterate_zero_apply] using
        rescaleStockExcess_unscaleStockExcess hα x
  | succ n ih =>
      simp only [iterate_succ_apply']
      have horbitMem := scaledLoopMap_iterate_policy_mem (p := p) (α := α) hx n
      have hwall :
          1 - p.s (((scaledLoopMap p α)^[n] x).1) - p.g ≠ 0 :=
        (stationaryWall_pos_of_mem model hgain horbitMem).ne'
      have hcurrent :
          (((withAdaptationRate p α).loopMap)^[n])
              (unscaleStockExcess p α x) =
            unscaleStockExcess p α (((scaledLoopMap p α)^[n]) x) := by
        calc
          _ = unscaleStockExcess p α
              (rescaleStockExcess p α
                ((((withAdaptationRate p α).loopMap)^[n])
                  (unscaleStockExcess p α x))) :=
            (unscaleStockExcess_rescaleStockExcess hα _).symm
          _ = _ := congrArg (unscaleStockExcess p α) ih
      rw [hcurrent]
      exact rescale_loopMap_unscale_eq_scaledLoopMap hα hwall

/-- A general filter form of the one-step zero-rate limit. -/
theorem scaledLoopMap_tendsto_projectedJumpMap
    {ι : Type*} {l : Filter ι} {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {rate : ι → ℝ} {state : ι → LoopState} {x : LoopState}
    (hrate : Tendsto rate l (nhds 0)) (hstate : Tendsto state l (nhds x))
    (hx : x.1 ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun i ↦ scaledLoopMap p (rate i) (state i)) l
      (nhds (projectedJumpMap p x)) := by
  have hpair : Tendsto (fun i ↦ (rate i, state i)) l (nhds (0, x)) :=
    hrate.prodMk_nhds hstate
  have hlimit := (continuousAt_scaledLoopMap_zero model hgain hx).tendsto.comp hpair
  change Tendsto (fun i ↦ scaledLoopMap p (rate i) (state i)) l
    (nhds (scaledLoopMap p 0 x)) at hlimit
  rwa [scaledLoopMap_zero] at hlimit

/--
Paper III, Theorem 7.1 (`thm:jump`), fixed-horizon jump-map limit,
`civic_loops.tex:463--533`.

For every fixed finite horizon, the orbit of the exact rescaled full map
converges to the orbit of the projected jump map as the adaptation rate tends
to zero.
-/
theorem scaledLoopOrbit_tendsto_projectedJumpOrbit
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {x : LoopState}
    (hx : x.1 ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    Tendsto (fun α : ℝ ↦ ((scaledLoopMap p α)^[n]) x) (nhds 0)
      (nhds (((projectedJumpMap p)^[n]) x)) := by
  induction n with
  | zero =>
      simpa only [iterate_zero_apply] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ x) (nhds 0) (nhds x))
  | succ n ih =>
      have horbitMem := projectedJumpMap_iterate_policy_mem (p := p) hx n
      have hstep := scaledLoopMap_tendsto_projectedJumpMap model hgain
        (rate := fun α : ℝ ↦ α)
        (state := fun α : ℝ ↦ ((scaledLoopMap p α)^[n]) x)
        tendsto_id ih horbitMem
      simpa only [iterate_succ_apply'] using hstep

/-- The actual full-loop orbit expressed in the paper's rescaled coordinates. -/
def rescaledFullLoopOrbit
    (p : LoopParams) (α : ℝ) (x : LoopState) (n : ℕ) : LoopState :=
  rescaleStockExcess p α
    ((((withAdaptationRate p α).loopMap)^[n]) (unscaleStockExcess p α x))

/-- At nonzero rate, the rescaled full orbit is exactly the extended-map orbit. -/
theorem rescaledFullLoopOrbit_eq_scaledLoopOrbit
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {α : ℝ} (hα : α ≠ 0)
    {x : LoopState} (hx : x.1 ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    rescaledFullLoopOrbit p α x n = ((scaledLoopMap p α)^[n]) x := by
  exact rescale_loopMap_iterate_unscale_eq_scaledLoopMap_iterate
    model hgain hα hx n

/--
Paper III, Theorem 7.1 (`thm:jump`), full-loop fixed-horizon limit,
`civic_loops.tex:463--533`.

Starting at stock `D*(β₀)+κ/α`, the original simultaneous loop, expressed in
coordinates `(β, α(D-D*(β)))`, converges at every fixed finite time to the
projected jump orbit as `α→0⁺`.
-/
theorem rescaledFullLoopOrbit_tendsto_projectedJumpOrbit
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {x : LoopState}
    (hx : x.1 ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    Tendsto (fun α : ℝ ↦ rescaledFullLoopOrbit p α x n) (nhdsWithin 0 (Ioi 0))
      (nhds (((projectedJumpMap p)^[n]) x)) := by
  have hscaled :
      Tendsto (fun α : ℝ ↦ ((scaledLoopMap p α)^[n]) x)
        (nhdsWithin 0 (Ioi 0))
        (nhds (((projectedJumpMap p)^[n]) x)) :=
    (scaledLoopOrbit_tendsto_projectedJumpOrbit model hgain hx n).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
  refine hscaled.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with α hα
  exact (rescaledFullLoopOrbit_eq_scaledLoopOrbit model hgain hα.ne' hx n).symm

/-! ## Recovery of the paper's raw jump map -/

/-- Every raw jump through time `n` stays inside the policy interval. -/
def RawJumpTransit (p : LoopParams) (x : LoopState) (n : ℕ) : Prop :=
  ∀ k < n,
    let y := ((jumpMap p)^[k]) x
    y.1 + jumpGain p y.1 * y.2 ∈ Icc (0 : ℝ) 1

/-- Under the explicit transit condition, projection does not change the raw orbit. -/
theorem projectedJumpMap_iterate_eq_jumpMap_iterate
    {p : LoopParams} {x : LoopState} {n : ℕ}
    (htransit : RawJumpTransit p x n) :
    ((projectedJumpMap p)^[n]) x = ((jumpMap p)^[n]) x := by
  induction n with
  | zero => simp only [iterate_zero_apply]
  | succ n ih =>
      have hprevious : RawJumpTransit p x n := by
        intro k hk
        exact htransit k (hk.trans (Nat.lt_succ_self n))
      rw [iterate_succ_apply', iterate_succ_apply', ih hprevious]
      exact projectedJumpMap_eq_jumpMap (htransit n (Nat.lt_succ_self n))

/--
The fixed-horizon limit has exactly the unprojected map printed in the paper
when that raw jump orbit stays inside `[0,1]` over the compared transit.
-/
theorem scaledLoopOrbit_tendsto_jumpOrbit
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {x : LoopState}
    (hx : x.1 ∈ Icc (0 : ℝ) 1) {n : ℕ}
    (htransit : RawJumpTransit p x n) :
    Tendsto (fun α : ℝ ↦ ((scaledLoopMap p α)^[n]) x) (nhds 0)
      (nhds (((jumpMap p)^[n]) x)) := by
  rw [← projectedJumpMap_iterate_eq_jumpMap_iterate htransit]
  exact scaledLoopOrbit_tendsto_projectedJumpOrbit model hgain hx n

/--
Under the explicit no-clipping transit condition, the rescaled original loop
converges to the raw jump orbit displayed in the paper.
-/
theorem rescaledFullLoopOrbit_tendsto_jumpOrbit
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {x : LoopState}
    (hx : x.1 ∈ Icc (0 : ℝ) 1) {n : ℕ}
    (htransit : RawJumpTransit p x n) :
    Tendsto (fun α : ℝ ↦ rescaledFullLoopOrbit p α x n) (nhdsWithin 0 (Ioi 0))
      (nhds (((jumpMap p)^[n]) x)) := by
  rw [← projectedJumpMap_iterate_eq_jumpMap_iterate htransit]
  exact rescaledFullLoopOrbit_tendsto_projectedJumpOrbit model hgain hx n

/-- The displayed jump's policy increment is independent of the adaptation rate. -/
theorem jumpMap_policy_increment (p : LoopParams) (x : LoopState) :
    (jumpMap p x).1 - x.1 = jumpGain p x.1 * x.2 := by
  simp only [jumpMap]
  ring

/-- The jump map obeys the exact left-endpoint excess-burn identity. -/
theorem jumpMap_excess_burn_crossMul (p : LoopParams) (x : LoopState) :
    jumpGain p x.1 * (x.2 - (jumpMap p x).2) =
      (1 - jumpPersistence p x.1) * ((jumpMap p x).1 - x.1) := by
  simp only [jumpMap]
  ring

/--
When `A(β)≠0`, the exact discrete jump is the left-endpoint differential
relation used to motivate the continuum integral, before any small-jump
approximation is made.
-/
theorem jumpMap_excess_change_eq_neg_burnRate_mul_policy_change
    {p : LoopParams} {x : LoopState} (hA : jumpGain p x.1 ≠ 0) :
    (jumpMap p x).2 - x.2 =
      -jumpBurnRate p x.1 * ((jumpMap p x).1 - x.1) := by
  simp only [jumpMap, jumpBurnRate]
  field_simp [hA]
  ring

/--
Without an interior-transit condition, the paper's raw jump map is not
the limit of the clipped full loop: any raw step above one differs from the
projected limiting step.
-/
theorem projectedJumpMap_ne_jumpMap_of_policy_gt_one
    {p : LoopParams} {x : LoopState}
    (hstep : 1 < x.1 + jumpGain p x.1 * x.2) :
    projectedJumpMap p x ≠ jumpMap p x := by
  have hclip :
      LoopParams.clipUnit (x.1 + jumpGain p x.1 * x.2) = 1 := by
    exact clipUnit_eq_one_of_le hstep.le
  intro heq
  have hfirst := congrArg Prod.fst heq
  simp only [projectedJumpMap, jumpMap, hclip] at hfirst
  linarith

#print axioms scaledLoopMap_zero
#print axioms projectedJumpMap_eq_jumpMap
#print axioms stockStep_stationaryStock_eq_self_of_ne
#print axioms gradU_unscaleStockExcess
#print axioms rescale_loopMap_unscale_eq_scaledLoopMap
#print axioms continuous_s
#print axioms continuous_clipUnit
#print axioms stationaryWall_pos_of_mem
#print axioms continuousAt_stationaryStock_of_ne
#print axioms continuousAt_G_of_ne
#print axioms continuousAt_scaledLoopMap_zero
#print axioms projectedJumpMap_policy_mem
#print axioms scaledLoopMap_policy_mem
#print axioms projectedJumpMap_iterate_policy_mem
#print axioms scaledLoopMap_iterate_policy_mem
#print axioms rescaleStockExcess_unscaleStockExcess
#print axioms unscaleStockExcess_rescaleStockExcess
#print axioms rescale_loopMap_iterate_unscale_eq_scaledLoopMap_iterate
#print axioms scaledLoopMap_tendsto_projectedJumpMap
#print axioms scaledLoopOrbit_tendsto_projectedJumpOrbit
#print axioms rescaledFullLoopOrbit_eq_scaledLoopOrbit
#print axioms rescaledFullLoopOrbit_tendsto_projectedJumpOrbit
#print axioms projectedJumpMap_iterate_eq_jumpMap_iterate
#print axioms scaledLoopOrbit_tendsto_jumpOrbit
#print axioms rescaledFullLoopOrbit_tendsto_jumpOrbit
#print axioms jumpMap_policy_increment
#print axioms jumpMap_excess_burn_crossMul
#print axioms jumpMap_excess_change_eq_neg_burnRate_mul_policy_change
#print axioms projectedJumpMap_ne_jumpMap_of_policy_gt_one

end

end CivicAlignment.PaperIII
