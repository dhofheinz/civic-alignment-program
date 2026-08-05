/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.ArrheniusLaw

/-!
# Paper II: quantitative saddle passage

This file isolates the deterministic algebra behind Paper II's quantitative
saddle-passage proposition.  In particular, it records the exact transport
law for lag from the stationary characteristic and a sharper cellwise action
ledger.  The latter is useful independently of the passage construction: it
keeps the barrier and mesh terms coupled instead of bounding them separately.
-/

namespace CivicAlignment.PaperII

open Filter Set Topology
open scoped BigOperators Interval

noncomputable section

/-! ## Exact deficit transport -/

/-- Subtracting the stock recursion from its stationary fixed-point identity
gives the exact one-step contraction of a fixed-policy stock deficit. -/
theorem stationaryStock_sub_stockStep
    {p : LoopParams} (model : DriftModelAssumptions p)
    {beta D : ℝ} (hbeta : beta ∈ Icc (0 : ℝ) 1) :
    p.stationaryStock beta - p.stockStep beta D =
      p.s beta * (p.stationaryStock beta - D) := by
  have hfixed := stationaryStock_fixed model hbeta
  simp only [LoopParams.stockStep, model.no_content_gain, add_zero] at hfixed ⊢
  linarith

/-- Exact old-level decomposition of a stock step.  Evaluating the deficit
at a level `b` above the current policy `beta` introduces the additional
term `(s b - s beta) D`; it vanishes only when the step begins at `b`. -/
theorem stationaryStock_sub_stockStep_at_oldLevel
    {p : LoopParams} (model : DriftModelAssumptions p)
    {beta b D : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) :
    p.stationaryStock b - p.stockStep beta D =
      p.s b * (p.stationaryStock b - D) +
        (p.s b - p.s beta) * D := by
  have hlevel := stationaryStock_sub_stockStep model (beta := b) (D := D) hb
  have hstepDiff : p.stockStep b D - p.stockStep beta D =
      (p.s b - p.s beta) * D := by
    simp only [LoopParams.stockStep, model.no_content_gain, add_zero]
    ring
  linarith

/-- Exact controlled one-step transport of the deficit
`D*(beta) - D`.  This identity is valid through projection because the stock
update uses the old policy while the final term uses the realized new policy. -/
theorem stationaryStockLag_controlledCivicWeightedStep
    {p : LoopParams} (model : DriftModelAssumptions p)
    (rho u : ℝ) {x : LoopState} (hx : x.1 ∈ Icc (0 : ℝ) 1) :
    stationaryStockLag p (controlledCivicWeightedStep p rho u x) =
      p.s x.1 * stationaryStockLag p x +
        (p.stationaryStock (controlledCivicWeightedStep p rho u x).1 -
          p.stationaryStock x.1) := by
  have hstock := stationaryStock_sub_stockStep model (D := x.2) hx
  simp only [stationaryStockLag, controlledCivicWeightedStep]
  linarith

/-- Paper II, Proposition `prop:passage`, transport step: along every
controlled path, the deficit is the old deficit contracted by `s(beta_t)`
plus the stationary-characteristic increment caused by policy movement. -/
theorem IsControlledCivicWeightedPath.stationaryStockLag_succ
    {p : LoopParams} {rho : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p)
    (path : IsControlledCivicWeightedPath p rho u x) (n : ℕ) :
    stationaryStockLag p (x (n + 1)) =
      p.s (x n).1 * stationaryStockLag p (x n) +
        (p.stationaryStock (x (n + 1)).1 - p.stationaryStock (x n).1) := by
  rw [path.step n]
  exact stationaryStockLag_controlledCivicWeightedStep
    model rho (u n) (path.policy_mem n)

/-- Exact transport through an advancing stopped level `b`.  The middle
term is the retreat correction omitted by the printed truncation argument:
it is present whenever the old policy is below the old running maximum. -/
theorem IsControlledCivicWeightedPath.stationaryStockLag_succ_at_oldLevel
    {p : LoopParams} {rho b : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p)
    (path : IsControlledCivicWeightedPath p rho u x) (n : ℕ)
    (hb : b ∈ Icc (0 : ℝ) 1) :
    stationaryStockLag p (x (n + 1)) =
      p.s b * (p.stationaryStock b - (x n).2) +
        (p.s b - p.s (x n).1) * (x n).2 +
          (p.stationaryStock (x (n + 1)).1 - p.stationaryStock b) := by
  have hlevel := stationaryStock_sub_stockStep_at_oldLevel
    model (beta := (x n).1) (D := (x n).2) hb
  have hstock := congrArg Prod.snd (path.step n)
  simp only [controlledCivicWeightedStep] at hstock
  simp only [stationaryStockLag]
  linarith

/-- Uniform coefficient converting retreat depth into next-step stock
deficit. -/
def passageRetreatTransportSlope (p : LoopParams) : ℝ :=
  2 * p.η * (1 - p.lambda₀) * (p.I / p.lambda₀)

/-- Correct burden-aware replacement for the paper's truncation-state
estimate.  Besides the old-level deficit and the new maximum's advance, a
retreat below the old maximum contributes linearly to the next deficit. -/
theorem IsControlledCivicWeightedPath.stationaryStockLag_succ_le_oldLevel_add_retreat
    {p : LoopParams} {rho b : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p)
    (path : IsControlledCivicWeightedPath p rho u x) (n : ℕ)
    (hb : b ∈ Icc (0 : ℝ) 1)
    (hbetaLe : (x n).1 ≤ b) (hbnext : b ≤ (x (n + 1)).1)
    (hstock : (x n).2 ≤ p.stationaryStock b) :
    stationaryStockLag p (x (n + 1)) ≤
      (p.stationaryStock b - (x n).2) +
        passageRetreatTransportSlope p * (b - (x n).1) +
          driftStationaryStockLipschitzBound p *
            ((x (n + 1)).1 - b) := by
  let beta := (x n).1
  let beta' := (x (n + 1)).1
  let D := (x n).2
  let theta := p.stationaryStock b - D
  have hbeta := path.policy_mem n
  have hbeta' := path.policy_mem (n + 1)
  have htheta : 0 ≤ theta := by
    simpa only [theta, D] using sub_nonneg.mpr hstock
  have hs := driftStockMultiplier_nonneg_le model hb
  have hsOne : p.s b ≤ 1 := hs.2.trans (sub_le_self 1 model.lambda₀_pos.le)
  have hcontract : p.s b * theta ≤ theta := by
    exact mul_le_of_le_one_left htheta hsOne
  have hsdiff := stockMultiplier_sub_le model hbeta hb hbetaLe
  have hDmem := path.mem_absorbingBox model n
  have hDnonneg : 0 ≤ D := by
    dsimp only [D]
    exact model.I_pos.le.trans hDmem.2.1
  have hDupper : D ≤ p.I / p.lambda₀ := by
    simpa only [D] using hDmem.2.2
  have hretreat₁ : (p.s b - p.s beta) * D ≤
      (2 * p.η * (1 - p.lambda₀) * (b - beta)) * D := by
    exact mul_le_mul_of_nonneg_right (by simpa only [beta] using hsdiff) hDnonneg
  have hk : 0 ≤ 2 * p.η * (1 - p.lambda₀) :=
    mul_nonneg (mul_nonneg (by norm_num) model.η_pos.le)
      (sub_nonneg.mpr model.lambda₀_lt_one.le)
  have hdelta : 0 ≤ b - beta := sub_nonneg.mpr hbetaLe
  have hfactor : 0 ≤ 2 * p.η * (1 - p.lambda₀) * (b - beta) :=
    mul_nonneg hk hdelta
  have hretreat₂ :
      (2 * p.η * (1 - p.lambda₀) * (b - beta)) * D ≤
        passageRetreatTransportSlope p * (b - beta) := by
    have hmul := mul_le_mul_of_nonneg_left hDupper hfactor
    dsimp only [passageRetreatTransportSlope]
    nlinarith
  have hretreat : (p.s b - p.s beta) * D ≤
      passageRetreatTransportSlope p * (b - beta) :=
    hretreat₁.trans hretreat₂
  have hchar := stationaryStock_sub_le_driftLipschitz
    model hb hbeta' hbnext
  have hexact := path.stationaryStockLag_succ_at_oldLevel model n hb
  dsimp only [beta, beta', D, theta] at hcontract hretreat hchar hexact ⊢
  linarith

/-! ## Exact holds below the saddle -/

/-- Paper II, Proposition `prop:passage`: below the weighted saddle, a
nonnegative stock deficit keeps the fixed-policy hold gradient nonpositive at
every finite time. -/
theorem cancellingHoldGradient_nonpos_of_before_saddle
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho b D₀ : ℝ} (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hb : b ∈ Icc (0 : ℝ) weighted.βdagger)
    (hgap : 0 ≤ p.stationaryStock b - D₀) (n : ℕ) :
    cancellingHoldGradient p rho b D₀ n ≤ 0 := by
  have hbUnit : b ∈ Icc (0 : ℝ) 1 :=
    ⟨hb.1, hb.2.trans weighted.βdagger_mem.2.le⟩
  have hs := driftStockMultiplier_nonneg_le model hbUnit
  have hlag := stationaryStock_sub_cancellingHoldStockPath
    model (D₀ := D₀) hbUnit n
  have hlagNonneg :
      0 ≤ p.stationaryStock b - cancellingHoldStockPath p b D₀ n := by
    rw [hlag]
    exact mul_nonneg (pow_nonneg hs.1 n) hgap
  have hcoefficient : 0 ≤ 2 * p.c * (1 - p.c * b) - rho :=
    weighted_stock_coefficient_nonnegative model hcoop hbUnit
  have hbarrier : 0 ≤ weightedBarrierIntegrand p rho b :=
    weighted.barrier_nonneg_before hb
  have hid := neg_civicWeightedGradient_eq_barrier_add_lag
    p rho b (cancellingHoldStockPath p b D₀ n)
  simp only [stationaryStockLag] at hid
  simp only [cancellingHoldGradient]
  nlinarith [mul_nonneg hcoefficient hlagNonneg]

/-- Paper II, Proposition `prop:passage`, exact-hold step: the positive-part
control cancels the entire negative drift and therefore holds policy fixed
while stock follows its unforced recursion. -/
theorem cancellingHoldPath_step_of_before_saddle
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho b D₀ : ℝ} (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hb : b ∈ Icc (0 : ℝ) weighted.βdagger)
    (hgap : 0 ≤ p.stationaryStock b - D₀) (n : ℕ) :
    cancellingHoldPath p b D₀ (n + 1) =
      controlledCivicWeightedStep p rho
        (cancellingHoldControl p rho b D₀ n)
        (cancellingHoldPath p b D₀ n) := by
  have hbUnit : b ∈ Icc (0 : ℝ) 1 :=
    ⟨hb.1, hb.2.trans weighted.βdagger_mem.2.le⟩
  exact cancellingHoldPath_step_of_gradient_nonpos model hbUnit n
    (cancellingHoldGradient_nonpos_of_before_saddle
      model hcoop weighted hb hgap n)

/-- Paper II, Proposition `prop:passage`, exact-hold control formula.  Its
two summands are the rent for holding at `b` and the geometrically decaying
stock-deficit cancellation cost. -/
theorem cancellingHoldControl_eq_barrier_add_geometric
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho b D₀ : ℝ} (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hb : b ∈ Icc (0 : ℝ) weighted.βdagger)
    (hgap : 0 ≤ p.stationaryStock b - D₀) (n : ℕ) :
    cancellingHoldControl p rho b D₀ n =
      weightedBarrierIntegrand p rho b +
        (2 * p.c * (1 - p.c * b) - rho) *
          (p.s b) ^ n * (p.stationaryStock b - D₀) := by
  have hbUnit : b ∈ Icc (0 : ℝ) 1 :=
    ⟨hb.1, hb.2.trans weighted.βdagger_mem.2.le⟩
  have hgradient := cancellingHoldGradient_nonpos_of_before_saddle
    model hcoop weighted hb hgap n
  have hcontrol : cancellingHoldControl p rho b D₀ n =
      -civicWeightedGradient p rho b
        (cancellingHoldStockPath p b D₀ n) := by
    simp only [cancellingHoldControl, cancellingHoldGradient] at hgradient ⊢
    exact max_eq_left (neg_nonneg.mpr hgradient)
  have hid := neg_civicWeightedGradient_eq_barrier_add_lag
    p rho b (cancellingHoldStockPath p b D₀ n)
  simp only [stationaryStockLag] at hid
  have hlag := stationaryStock_sub_cancellingHoldStockPath
    model (D₀ := D₀) hbUnit n
  rw [hcontrol, hid, hlag]
  ring

/-- Paper II, Proposition `prop:passage`, exact finite-horizon hold action.
This sum form is the kernel-checked version of the three geometric sums in
the paper's saddle-passage proof. -/
theorem cancellingHoldAction_eq_before_saddle
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho b D₀ : ℝ} (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hb : b ∈ Icc (0 : ℝ) weighted.βdagger)
    (hgap : 0 ≤ p.stationaryStock b - D₀) (N : ℕ) :
    controlAction (cancellingHoldControl p rho b D₀) N =
      (1 / 2 : ℝ) * ∑ n ∈ Finset.range N,
        (weightedBarrierIntegrand p rho b +
          (2 * p.c * (1 - p.c * b) - rho) *
            (p.s b) ^ n * (p.stationaryStock b - D₀)) ^ 2 := by
  simp only [controlAction]
  congr 1
  apply Finset.sum_congr rfl
  intro n _hn
  rw [cancellingHoldControl_eq_barrier_add_geometric
    model hcoop weighted hb hgap n]

/-- Limiting action of cancelling an initial stock deficit while holding the
policy exactly at the weighted saddle. -/
def saddleDeficitHoldPrice
    (p : LoopParams) (rho beta theta : ℝ) : ℝ :=
  (2 * p.c * (1 - p.c * beta) - rho) ^ 2 * theta ^ 2 /
    (2 * (1 - (p.s beta) ^ 2))

/-- The finite saddle hold has an exact geometric-tail formula.  This is the
quantified version of the sharp quadratic coefficient discussed after the
saddle-passage theorem. -/
theorem cancellingHoldAction_at_saddle_eq_price_sub_tail
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho theta : ℝ} (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (htheta : 0 ≤ theta) (N : ℕ) :
    controlAction
        (cancellingHoldControl p rho weighted.βdagger
          (p.stationaryStock weighted.βdagger - theta)) N =
      saddleDeficitHoldPrice p rho weighted.βdagger theta *
        (1 - (p.s weighted.βdagger) ^ (2 * N)) := by
  let b := weighted.βdagger
  let s := p.s b
  let A := 2 * p.c * (1 - p.c * b) - rho
  have hb : b ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨weighted.βdagger_mem.1.le, le_rfl⟩
  have hbUnit : b ∈ Icc (0 : ℝ) 1 :=
    ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩
  have hgap : 0 ≤ p.stationaryStock b -
      (p.stationaryStock b - theta) := by linarith
  have hbarrier : weightedBarrierIntegrand p rho b = 0 := by
    change -weightedStationaryGradient p rho weighted.βdagger = 0
    rw [weighted.gradient_zero]
    norm_num
  have hs := driftStockMultiplier_nonneg_le model hbUnit
  have hslt : s < 1 := by
    dsimp only [s]
    linarith [model.lambda₀_pos]
  have hsqLt : s ^ 2 < 1 := by
    simpa only [one_pow] using (sq_lt_sq₀ (by simpa only [s] using hs.1)
      (zero_le_one : (0 : ℝ) ≤ 1)).2 hslt
  have hdenom : 1 - s ^ 2 ≠ 0 := ne_of_gt (sub_pos.mpr hsqLt)
  have hsum :
      (∑ n ∈ Finset.range N, ((s ^ n) ^ 2)) =
        ∑ n ∈ Finset.range N, (s ^ 2) ^ n := by
    apply Finset.sum_congr rfl
    intro n _hn
    simp only [← pow_mul, Nat.mul_comm]
  have hgeom :
      (∑ n ∈ Finset.range N, (s ^ 2) ^ n) * (1 - s ^ 2) =
        1 - (s ^ 2) ^ N := geom_sum_mul_neg (s ^ 2) N
  rw [cancellingHoldAction_eq_before_saddle
    model hcoop weighted hb hgap N]
  simp only [hbarrier, zero_add,
    sub_sub_cancel, saddleDeficitHoldPrice]
  change
    (1 / 2 : ℝ) * ∑ n ∈ Finset.range N,
        (A * s ^ n * theta) ^ 2 =
      (A ^ 2 * theta ^ 2 / (2 * (1 - s ^ 2))) *
        (1 - s ^ (2 * N))
  rw [show (∑ n ∈ Finset.range N, (A * s ^ n * theta) ^ 2) =
      A ^ 2 * theta ^ 2 * (∑ n ∈ Finset.range N, ((s ^ n) ^ 2)) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    ring]
  rw [hsum]
  have hpowMul : s ^ (2 * N) = (s ^ 2) ^ N := by rw [pow_mul]
  rw [hpowMul, ← hgeom]
  field_simp [hdenom]

/-- The sharp saddle-deficit coefficient is the actual large-horizon limit of
the finite cancelling-hold action. -/
theorem tendsto_cancellingHoldAction_at_saddle
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho theta : ℝ} (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (htheta : 0 ≤ theta) :
    Tendsto
      (fun N ↦ controlAction
        (cancellingHoldControl p rho weighted.βdagger
          (p.stationaryStock weighted.βdagger - theta)) N)
      atTop (nhds (saddleDeficitHoldPrice p rho weighted.βdagger theta)) := by
  have hbUnit : weighted.βdagger ∈ Icc (0 : ℝ) 1 :=
    ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩
  have hs := driftStockMultiplier_nonneg_le model hbUnit
  have hslt : p.s weighted.βdagger < 1 := by
    linarith [model.lambda₀_pos]
  have hsqLt : (p.s weighted.βdagger) ^ 2 < 1 := by
    simpa only [one_pow] using
      (sq_lt_sq₀ hs.1 (zero_le_one : (0 : ℝ) ≤ 1)).2 hslt
  have hpow : Tendsto (fun N : ℕ ↦ (p.s weighted.βdagger ^ 2) ^ N)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg _) hsqLt
  have hfactor : Tendsto
      (fun N : ℕ ↦ 1 - (p.s weighted.βdagger ^ 2) ^ N)
      atTop (nhds 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hpow
  have hscaled : Tendsto
      (fun N : ℕ ↦ saddleDeficitHoldPrice p rho weighted.βdagger theta *
        (1 - (p.s weighted.βdagger ^ 2) ^ N))
      atTop
      (nhds (saddleDeficitHoldPrice p rho weighted.βdagger theta * 1)) :=
    tendsto_const_nhds.mul hfactor
  simp only [mul_one] at hscaled
  apply hscaled.congr'
  exact Eventually.of_forall fun N ↦ by
    symm
    change controlAction
        (cancellingHoldControl p rho weighted.βdagger
          (p.stationaryStock weighted.βdagger - theta)) N =
      saddleDeficitHoldPrice p rho weighted.βdagger theta *
        (1 - (p.s weighted.βdagger ^ 2) ^ N)
    rw [cancellingHoldAction_at_saddle_eq_price_sub_tail
      model hcoop weighted htheta N]
    congr 2
    rw [pow_mul]

/-- Paper II, Proposition `prop:passage`, quantitative exact-hold estimate:
the holding rent is linear in the number of steps, while the transient stock
deficit has a horizon-independent geometric bound. -/
theorem cancellingHoldAction_le_rent_add_transient
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho b D₀ : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hb : b ∈ Icc (0 : ℝ) weighted.βdagger)
    (hgap : 0 ≤ p.stationaryStock b - D₀) (N : ℕ) :
    controlAction (cancellingHoldControl p rho b D₀) N ≤
      (N : ℝ) * (weightedBarrierIntegrand p rho b) ^ 2 +
        4 * p.c ^ 2 * (p.stationaryStock b - D₀) ^ 2 / p.lambda₀ := by
  let G := weightedBarrierIntegrand p rho b
  let A := 2 * p.c * (1 - p.c * b) - rho
  let theta := p.stationaryStock b - D₀
  have hbUnit : b ∈ Icc (0 : ℝ) 1 :=
    ⟨hb.1, hb.2.trans weighted.βdagger_mem.2.le⟩
  have hs := driftStockMultiplier_nonneg_le model hbUnit
  have hA0 : 0 ≤ A := by
    simpa only [A] using
      weighted_stock_coefficient_nonnegative model hcoop hbUnit
  have hAupper : A ≤ 2 * p.c := by
    simpa only [A] using weighted_stock_coefficient_le_two_c model hrho hbUnit
  have htwoC : 0 ≤ 2 * p.c := mul_nonneg (by norm_num) model.c_pos.le
  have hAsq : A ^ 2 ≤ (2 * p.c) ^ 2 :=
    (sq_le_sq₀ hA0 htwoC).2 hAupper
  have hgeom := sum_sq_geometric_le_inv_gap
    hs.1 hs.2 model.lambda₀_pos N
  rw [cancellingHoldAction_eq_before_saddle
    model hcoop weighted hb hgap N]
  have hsummand : ∀ n ∈ Finset.range N,
      (G + A * (p.s b) ^ n * theta) ^ 2 ≤
        2 * G ^ 2 + 2 * A ^ 2 * theta ^ 2 * ((p.s b) ^ n) ^ 2 := by
    intro n _hn
    nlinarith [sq_nonneg (G - A * (p.s b) ^ n * theta)]
  have hsum := Finset.sum_le_sum hsummand
  have hhalf := mul_le_mul_of_nonneg_left hsum
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    (1 / 2 : ℝ) * ∑ n ∈ Finset.range N,
        (weightedBarrierIntegrand p rho b +
          (2 * p.c * (1 - p.c * b) - rho) *
            (p.s b) ^ n * (p.stationaryStock b - D₀)) ^ 2 =
        (1 / 2 : ℝ) * ∑ n ∈ Finset.range N,
          (G + A * (p.s b) ^ n * theta) ^ 2 := by rfl
    _ ≤ (1 / 2 : ℝ) * ∑ n ∈ Finset.range N,
          (2 * G ^ 2 + 2 * A ^ 2 * theta ^ 2 * ((p.s b) ^ n) ^ 2) := hhalf
    _ = (N : ℝ) * G ^ 2 +
        A ^ 2 * theta ^ 2 *
          (∑ n ∈ Finset.range N, ((p.s b) ^ n) ^ 2) := by
      rw [Finset.mul_sum]
      calc
        (∑ n ∈ Finset.range N,
            (1 / 2 : ℝ) *
              (2 * G ^ 2 + 2 * A ^ 2 * theta ^ 2 * ((p.s b) ^ n) ^ 2)) =
            ∑ n ∈ Finset.range N,
              (G ^ 2 + A ^ 2 * theta ^ 2 * ((p.s b) ^ n) ^ 2) := by
          apply Finset.sum_congr rfl
          intro n _hn
          ring
        _ = _ := by
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_range, Finset.mul_sum]
          ring
    _ ≤ (N : ℝ) * G ^ 2 + A ^ 2 * theta ^ 2 * (1 / p.lambda₀) := by
      gcongr
    _ ≤ (N : ℝ) * G ^ 2 + (2 * p.c) ^ 2 * theta ^ 2 * (1 / p.lambda₀) := by
      have hmul := mul_le_mul_of_nonneg_right hAsq
        (mul_nonneg (sq_nonneg theta)
          (one_div_nonneg.mpr model.lambda₀_pos.le))
      exact add_le_add_right (by simpa only [mul_assoc] using hmul) _
    _ = (N : ℝ) * (weightedBarrierIntegrand p rho b) ^ 2 +
        4 * p.c ^ 2 * (p.stationaryStock b - D₀) ^ 2 / p.lambda₀ := by
      dsimp only [G, theta]
      ring

/-! ## Sign-free exact holds -/

/-- A signed cancelling control pins the policy exactly even when the stock
starts slightly above its stationary characteristic.  The Freidlin--Wentzell
control space is all of `ℝ`, so this is the convenient surgery primitive at
a truncation state whose own-level lag need not have a known sign. -/
def signedHoldControl (p : LoopParams) (rho b D₀ : ℝ) (n : ℕ) : ℝ :=
  -civicWeightedGradient p rho b (cancellingHoldStockPath p b D₀ n)

/-- The signed hold follows the exact fixed-policy stock recursion from any
initial stock value. -/
theorem signedHoldPath_step
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho b D₀ : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    cancellingHoldPath p b D₀ (n + 1) =
      controlledCivicWeightedStep p rho
        (signedHoldControl p rho b D₀ n)
        (cancellingHoldPath p b D₀ n) := by
  have hstock := cancellingHoldStockPath_succ model (b := b) (D₀ := D₀) n
  have hcancel :
      civicWeightedGradient p rho b (cancellingHoldStockPath p b D₀ n) +
          -civicWeightedGradient p rho b (cancellingHoldStockPath p b D₀ n) = 0 := by
    ring
  simp only [cancellingHoldPath, signedHoldControl,
    controlledCivicWeightedStep]
  rw [hcancel, mul_zero, add_zero, clipUnit_eq_self hb, hstock]

/-- Exact barrier-plus-geometric formula for the signed hold.  Unlike the
positive-part version, it needs no sign assumption on the initial lag. -/
theorem signedHoldControl_eq_barrier_add_geometric
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho b D₀ : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    signedHoldControl p rho b D₀ n =
      weightedBarrierIntegrand p rho b +
        (2 * p.c * (1 - p.c * b) - rho) *
          (p.s b) ^ n * (p.stationaryStock b - D₀) := by
  have hid := neg_civicWeightedGradient_eq_barrier_add_lag
    p rho b (cancellingHoldStockPath p b D₀ n)
  simp only [stationaryStockLag] at hid
  have hlag := stationaryStock_sub_cancellingHoldStockPath
    model (D₀ := D₀) hb n
  simp only [signedHoldControl]
  rw [hid, hlag]
  ring

/-- A finite signed hold pays linear positional rent plus a horizon-free
quadratic transient, uniformly for either sign of the initial stock lag. -/
theorem signedHoldAction_le_rent_add_transient
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho b D₀ : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (hb : b ∈ Icc (0 : ℝ) 1) (N : ℕ) :
    controlAction (signedHoldControl p rho b D₀) N ≤
      (N : ℝ) * (weightedBarrierIntegrand p rho b) ^ 2 +
        4 * p.c ^ 2 * (p.stationaryStock b - D₀) ^ 2 / p.lambda₀ := by
  let G := weightedBarrierIntegrand p rho b
  let A := 2 * p.c * (1 - p.c * b) - rho
  let theta := p.stationaryStock b - D₀
  have hs := driftStockMultiplier_nonneg_le model hb
  have hA₀ : 0 ≤ A := by
    simpa only [A] using
      weighted_stock_coefficient_nonnegative model hcoop hb
  have hAupper : A ≤ 2 * p.c := by
    simpa only [A] using weighted_stock_coefficient_le_two_c model hrho hb
  have htwoC : 0 ≤ 2 * p.c := mul_nonneg (by norm_num) model.c_pos.le
  have hAsq : A ^ 2 ≤ (2 * p.c) ^ 2 :=
    (sq_le_sq₀ hA₀ htwoC).2 hAupper
  have hgeom := sum_sq_geometric_le_inv_gap
    hs.1 hs.2 model.lambda₀_pos N
  have hsummand : ∀ n ∈ Finset.range N,
      (G + A * (p.s b) ^ n * theta) ^ 2 ≤
        2 * G ^ 2 + 2 * A ^ 2 * theta ^ 2 * ((p.s b) ^ n) ^ 2 := by
    intro n _hn
    nlinarith [sq_nonneg (G - A * (p.s b) ^ n * theta)]
  have hsum := Finset.sum_le_sum hsummand
  have hhalf := mul_le_mul_of_nonneg_left hsum
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [controlAction]
  have hcontrols :
      (∑ n ∈ Finset.range N, (signedHoldControl p rho b D₀ n) ^ 2) =
        ∑ n ∈ Finset.range N,
          (G + A * (p.s b) ^ n * theta) ^ 2 := by
    apply Finset.sum_congr rfl
    intro n _hn
    rw [signedHoldControl_eq_barrier_add_geometric model hb n]
  rw [hcontrols]
  calc
    (1 / 2 : ℝ) * ∑ n ∈ Finset.range N,
        (G + A * (p.s b) ^ n * theta) ^ 2 ≤
        (1 / 2 : ℝ) * ∑ n ∈ Finset.range N,
          (2 * G ^ 2 + 2 * A ^ 2 * theta ^ 2 * ((p.s b) ^ n) ^ 2) := hhalf
    _ = (N : ℝ) * G ^ 2 + A ^ 2 * theta ^ 2 *
          (∑ n ∈ Finset.range N, ((p.s b) ^ n) ^ 2) := by
      rw [Finset.mul_sum]
      calc
        (∑ n ∈ Finset.range N,
            (1 / 2 : ℝ) *
              (2 * G ^ 2 + 2 * A ^ 2 * theta ^ 2 * ((p.s b) ^ n) ^ 2)) =
            ∑ n ∈ Finset.range N,
              (G ^ 2 + A ^ 2 * theta ^ 2 * ((p.s b) ^ n) ^ 2) := by
          apply Finset.sum_congr rfl
          intro n _hn
          ring
        _ = _ := by
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_range, Finset.mul_sum]
          ring
    _ ≤ (N : ℝ) * G ^ 2 + A ^ 2 * theta ^ 2 * (1 / p.lambda₀) := by
      gcongr
    _ ≤ (N : ℝ) * G ^ 2 + (2 * p.c) ^ 2 * theta ^ 2 *
          (1 / p.lambda₀) := by
      have hmul := mul_le_mul_of_nonneg_right hAsq
        (mul_nonneg (sq_nonneg theta)
          (one_div_nonneg.mpr model.lambda₀_pos.le))
      exact add_le_add_right (by simpa only [mul_assoc] using hmul) _
    _ = (N : ℝ) * (weightedBarrierIntegrand p rho b) ^ 2 +
        4 * p.c ^ 2 * (p.stationaryStock b - D₀) ^ 2 / p.lambda₀ := by
      dsimp only [G, theta]
      ring

/-! ## Arbitrary-start margin climbs -/

/-- The positive-margin feedback climb restarted from an arbitrary state.
This is the suffix primitive needed after the selected crossing path has
been truncated; the older `marginClimbPath` is fixed at the calibrated
corner. -/
def marginClimbPathFrom (p : LoopParams) (rho epsilon : ℝ)
    (x₀ : LoopState) (n : ℕ) : LoopState :=
  ((marginClimbStep p rho epsilon)^[n]) x₀

/-- Feedback controls along the arbitrary-start margin climb. -/
def marginClimbControlSequenceFrom (p : LoopParams) (rho epsilon : ℝ)
    (x₀ : LoopState) (n : ℕ) : ℝ :=
  marginClimbControl p rho epsilon
    (marginClimbPathFrom p rho epsilon x₀ n)

@[simp]
theorem marginClimbPathFrom_zero
    (p : LoopParams) (rho epsilon : ℝ) (x₀ : LoopState) :
    marginClimbPathFrom p rho epsilon x₀ 0 = x₀ := by
  simp only [marginClimbPathFrom, Function.iterate_zero_apply]

@[simp]
theorem marginClimbPathFrom_succ
    (p : LoopParams) (rho epsilon : ℝ) (x₀ : LoopState) (n : ℕ) :
    marginClimbPathFrom p rho epsilon x₀ (n + 1) =
      controlledCivicWeightedStep p rho
        (marginClimbControlSequenceFrom p rho epsilon x₀ n)
        (marginClimbPathFrom p rho epsilon x₀ n) := by
  simp only [marginClimbPathFrom, marginClimbStep,
    marginClimbControlSequenceFrom, Function.iterate_succ_apply']

/-- The restarted feedback orbit is a controlled path from its stated
initial state. -/
theorem marginClimbPathFrom_isControlled
    (p : LoopParams) (rho epsilon : ℝ) (x₀ : LoopState) :
    IsControlledCivicWeightedPathFrom p rho x₀
      (marginClimbControlSequenceFrom p rho epsilon x₀)
      (marginClimbPathFrom p rho epsilon x₀) where
  initial := marginClimbPathFrom_zero p rho epsilon x₀
  step := marginClimbPathFrom_succ p rho epsilon x₀

/-- The feedback's controlled gradient is exactly the absolute uncontrolled
gradient plus its positive margin. -/
theorem marginClimb_net_gradient_eq_abs
    (p : LoopParams) (rho epsilon : ℝ) (x : LoopState) :
    civicWeightedGradient p rho x.1 x.2 +
        marginClimbControl p rho epsilon x =
      |civicWeightedGradient p rho x.1 x.2| + epsilon := by
  let g := civicWeightedGradient p rho x.1 x.2
  by_cases hg : 0 ≤ g
  · rw [abs_of_nonneg hg]
    simp only [marginClimbControl, doublingControl, g]
    rw [max_eq_right (neg_nonpos.mpr hg)]
    ring
  · have hg' : g < 0 := lt_of_not_ge hg
    rw [abs_of_neg hg']
    simp only [marginClimbControl, doublingControl, g]
    rw [max_eq_left (neg_nonneg.mpr hg'.le)]
    ring

/-- With a nonnegative margin, policy is nondecreasing along every
arbitrary-start margin climb whose initial policy lies in `[0,1]`. -/
theorem monotone_marginClimbPolicyFrom
    {p : LoopParams} (model : DriftModelAssumptions p)
    (rho epsilon : ℝ) {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hepsilon : 0 ≤ epsilon) :
    Monotone (fun n ↦ (marginClimbPathFrom p rho epsilon x₀ n).1) := by
  let path := marginClimbPathFrom_isControlled p rho epsilon x₀
  apply monotone_nat_of_le_succ
  intro n
  let x := marginClimbPathFrom p rho epsilon x₀ n
  have hx : x.1 ∈ Icc (0 : ℝ) 1 := path.policy_mem hx₀ n
  have hnet := marginClimb_net_gradient_ge p rho epsilon x
  have hraw : x.1 ≤ x.1 + p.α *
      (civicWeightedGradient p rho x.1 x.2 +
        marginClimbControl p rho epsilon x) := by
    nlinarith [model.α_pos]
  rw [marginClimbPathFrom_succ]
  simp only [controlledCivicWeightedStep, marginClimbControlSequenceFrom]
  calc
    x.1 = LoopParams.clipUnit x.1 := (clipUnit_eq_self hx).symm
    _ ≤ LoopParams.clipUnit
        (x.1 + p.α *
          (civicWeightedGradient p rho x.1 x.2 +
            marginClimbControl p rho epsilon x)) :=
      LoopParams.monotone_clipUnit hraw

/-- A positive margin drives an arbitrary admissible starting policy past
every target strictly below one in finite time. -/
theorem marginClimbPathFrom_eventually_crosses
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho epsilon target : ℝ} {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1)
    (_hstart : x₀.1 ≤ target) (htarget : target < 1)
    (hepsilon : 0 < epsilon) :
    ∃ N, target < (marginClimbPathFrom p rho epsilon x₀ N).1 := by
  let beta : ℕ → ℝ :=
    fun n ↦ (marginClimbPathFrom p rho epsilon x₀ n).1
  let delta : ℝ := min (p.α * epsilon) ((1 - target) / 2)
  have hgap : 0 < 1 - target := sub_pos.mpr htarget
  have hdeltaPos : 0 < delta := by
    dsimp only [delta]
    exact lt_min (mul_pos model.α_pos hepsilon) (half_pos hgap)
  have hdeltaAlpha : delta ≤ p.α * epsilon := min_le_left _ _
  have hdeltaGap : delta ≤ (1 - target) / 2 := min_le_right _ _
  by_contra hnever
  push Not at hnever
  have hstep : ∀ n, beta n + delta ≤ beta (n + 1) := by
    intro n
    have hbetaMem : beta n ∈ Icc (0 : ℝ) 1 :=
      (marginClimbPathFrom_isControlled p rho epsilon x₀).policy_mem hx₀ n
    have hbetaTarget : beta n ≤ target := hnever n
    have htargetMem : beta n + delta ∈ Icc (0 : ℝ) 1 := by
      constructor
      · nlinarith [hbetaMem.1, hdeltaPos]
      · nlinarith [hdeltaGap, hgap]
    have hnet := marginClimb_net_gradient_ge p rho epsilon
      (marginClimbPathFrom p rho epsilon x₀ n)
    have hraw : beta n + delta ≤ beta n + p.α *
        (civicWeightedGradient p rho
            (marginClimbPathFrom p rho epsilon x₀ n).1
            (marginClimbPathFrom p rho epsilon x₀ n).2 +
          marginClimbControl p rho epsilon
            (marginClimbPathFrom p rho epsilon x₀ n)) := by
      dsimp only [beta]
      nlinarith [model.α_pos]
    change (marginClimbPathFrom p rho epsilon x₀ n).1 + delta ≤
      (marginClimbPathFrom p rho epsilon x₀ (n + 1)).1
    rw [marginClimbPathFrom_succ]
    simp only [controlledCivicWeightedStep, marginClimbControlSequenceFrom]
    calc
      beta n + delta = LoopParams.clipUnit (beta n + delta) :=
        (clipUnit_eq_self htargetMem).symm
      _ ≤ LoopParams.clipUnit
          ((marginClimbPathFrom p rho epsilon x₀ n).1 + p.α *
            (civicWeightedGradient p rho
                (marginClimbPathFrom p rho epsilon x₀ n).1
                (marginClimbPathFrom p rho epsilon x₀ n).2 +
              marginClimbControl p rho epsilon
                (marginClimbPathFrom p rho epsilon x₀ n))) :=
        LoopParams.monotone_clipUnit (by simpa only [beta] using hraw)
  have hlinear : ∀ n : ℕ, x₀.1 + (n : ℝ) * delta ≤ beta n := by
    intro n
    induction n with
    | zero =>
        simp only [Nat.cast_zero, zero_mul, add_zero, beta,
          marginClimbPathFrom_zero]
        exact le_rfl
    | succ n ih =>
        have hn := hstep n
        norm_num [Nat.cast_succ] at ⊢
        nlinarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((target - x₀.1) / delta)
  have htargetLt : target < x₀.1 + (N : ℝ) * delta := by
    have hscaled : target - x₀.1 < (N : ℝ) * delta :=
      (div_lt_iff₀ hdeltaPos).mp hN
    linarith
  exact (not_lt_of_ge (hnever N) (htargetLt.trans_le (hlinear N))).elim

/-- First strict target-crossing time for an arbitrary-start margin climb.
The definition is total; the crossing theorems below supply nonemptiness in
the passage regime. -/
noncomputable def marginClimbStopFrom
    (p : LoopParams) (rho epsilon target : ℝ) (x₀ : LoopState) : ℕ :=
  firstPositiveIndex (fun n ↦
    (marginClimbPathFrom p rho epsilon x₀ n).1 - target)

/-- The arbitrary-start climb is strictly past its target at its canonical
stopping time. -/
theorem marginClimbStopFrom_crosses
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho epsilon target : ℝ} {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1)
    (hstart : x₀.1 ≤ target) (htarget : target < 1)
    (hepsilon : 0 < epsilon) :
    target < (marginClimbPathFrom p rho epsilon x₀
      (marginClimbStopFrom p rho epsilon target x₀)).1 := by
  have hexists := marginClimbPathFrom_eventually_crosses
    model (rho := rho) hx₀ hstart htarget hepsilon
  have hspec := firstPositiveIndex_spec (show
    ∃ n, 0 < (marginClimbPathFrom p rho epsilon x₀ n).1 - target by
      simpa only [sub_pos] using hexists)
  simpa only [marginClimbStopFrom, sub_pos] using hspec

/-- Every state before the canonical stopping time remains at or below the
target. -/
theorem marginClimbPathFrom_le_target_before_stop
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho epsilon target : ℝ} {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1)
    (hstart : x₀.1 ≤ target) (htarget : target < 1)
    (hepsilon : 0 < epsilon) {n : ℕ}
    (hn : n < marginClimbStopFrom p rho epsilon target x₀) :
    (marginClimbPathFrom p rho epsilon x₀ n).1 ≤ target := by
  have hexists := marginClimbPathFrom_eventually_crosses
    model (rho := rho) hx₀ hstart htarget hepsilon
  have hbefore := firstPositiveIndex_nonpos_before (show
    ∃ k, 0 < (marginClimbPathFrom p rho epsilon x₀ k).1 - target by
      simpa only [sub_pos] using hexists) (by
        simpa only [marginClimbStopFrom] using hn)
  linarith

/-- A primitive-only absolute gradient bound on the invariant box. -/
def passageGradientBound (p : LoopParams) : ℝ :=
  p.v + 2 * p.c * (p.I / p.lambda₀)

/-- The primitive gradient bound is strictly positive. -/
theorem passageGradientBound_pos
    {p : LoopParams} (model : DriftModelAssumptions p) :
    0 < passageGradientBound p := by
  have hterm : 0 ≤ 2 * p.c * (p.I / p.lambda₀) := by
    exact mul_nonneg (mul_nonneg (by norm_num) model.c_pos.le)
      (div_nonneg model.I_pos.le model.lambda₀_pos.le)
  simp only [passageGradientBound]
  linarith [model.v_pos]

/-- The weighted gradient is uniformly bounded in absolute value on the
paper's invariant rectangle. -/
theorem abs_civicWeightedGradient_le_passageGradientBound
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    {x : LoopState} (hx : x ∈ absorbingBox p) :
    |civicWeightedGradient p rho x.1 x.2| ≤ passageGradientBound p := by
  have hcoef₀ := weighted_stock_coefficient_nonnegative model hcoop hx.1
  have hcoefLe := weighted_stock_coefficient_le_two_c model hrho hx.1
  have hstock₀ : 0 ≤ x.2 := model.I_pos.le.trans hx.2.1
  have hstockLe : x.2 ≤ p.I / p.lambda₀ := hx.2.2
  have htwoC₀ : 0 ≤ 2 * p.c := mul_nonneg (by norm_num) model.c_pos.le
  have hprod₀ : 0 ≤
      (2 * p.c * (1 - p.c * x.1) - rho) * x.2 :=
    mul_nonneg hcoef₀ hstock₀
  have hprodLe :
      (2 * p.c * (1 - p.c * x.1) - rho) * x.2 ≤
        2 * p.c * (p.I / p.lambda₀) :=
    mul_le_mul hcoefLe hstockLe hstock₀ htwoC₀
  have hterm₀ : 0 ≤ 2 * p.c * (p.I / p.lambda₀) := by
    exact mul_nonneg htwoC₀
      (div_nonneg model.I_pos.le model.lambda₀_pos.le)
  rw [abs_le]
  constructor
  · simp only [civicWeightedGradient, LoopParams.gradU,
      passageGradientBound]
    linarith [model.v_pos]
  · simp only [civicWeightedGradient, LoopParams.gradU,
      passageGradientBound]
    linarith [model.v_pos]

/-- Below the saddle, the adverse part of the off-characteristic gradient
is bounded by stationary barrier height plus absolute stock lag. -/
theorem max_neg_civicWeightedGradient_le_barrier_add_abs_lag
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho beta D : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hbeta : beta ∈ Icc (0 : ℝ) weighted.βdagger) :
    max (-civicWeightedGradient p rho beta D) 0 ≤
      weightedBarrierIntegrand p rho beta +
        2 * p.c * |stationaryStockLag p (beta, D)| := by
  have hbetaUnit : beta ∈ Icc (0 : ℝ) 1 :=
    ⟨hbeta.1, hbeta.2.trans weighted.βdagger_mem.2.le⟩
  let A := 2 * p.c * (1 - p.c * beta) - rho
  have hA₀ : 0 ≤ A := by
    simpa only [A] using
      weighted_stock_coefficient_nonnegative model hcoop hbetaUnit
  have hAle : A ≤ 2 * p.c := by
    simpa only [A] using weighted_stock_coefficient_le_two_c model hrho hbetaUnit
  have htwoC₀ : 0 ≤ 2 * p.c := mul_nonneg (by norm_num) model.c_pos.le
  have hlagLe : stationaryStockLag p (beta, D) ≤
      |stationaryStockLag p (beta, D)| := le_abs_self _
  have hmul : A * stationaryStockLag p (beta, D) ≤
      2 * p.c * |stationaryStockLag p (beta, D)| := by
    calc
      A * stationaryStockLag p (beta, D) ≤
          A * |stationaryStockLag p (beta, D)| :=
        mul_le_mul_of_nonneg_left hlagLe hA₀
      _ ≤ 2 * p.c * |stationaryStockLag p (beta, D)| :=
        mul_le_mul_of_nonneg_right hAle (abs_nonneg _)
  have hid := neg_civicWeightedGradient_eq_barrier_add_lag p rho beta D
  have hright₀ : 0 ≤ weightedBarrierIntegrand p rho beta +
      2 * p.c * |stationaryStockLag p (beta, D)| :=
    add_nonneg (weighted.barrier_nonneg_before hbeta)
      (mul_nonneg htwoC₀ (abs_nonneg _))
  rw [max_le_iff]
  constructor
  · rw [hid]
    dsimp only [A] at hmul
    linarith
  · exact hright₀

/-- On the saddle segment, the full absolute off-characteristic gradient is
bounded by stationary barrier height plus absolute stock lag. -/
theorem abs_civicWeightedGradient_le_barrier_add_abs_lag
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho beta D : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hbeta : beta ∈ Icc (0 : ℝ) weighted.βdagger) :
    |civicWeightedGradient p rho beta D| ≤
      weightedBarrierIntegrand p rho beta +
        2 * p.c * |stationaryStockLag p (beta, D)| := by
  have hbetaUnit : beta ∈ Icc (0 : ℝ) 1 :=
    ⟨hbeta.1, hbeta.2.trans weighted.βdagger_mem.2.le⟩
  let A := 2 * p.c * (1 - p.c * beta) - rho
  have hA₀ : 0 ≤ A := by
    simpa only [A] using
      weighted_stock_coefficient_nonnegative model hcoop hbetaUnit
  have hAle : A ≤ 2 * p.c := by
    simpa only [A] using weighted_stock_coefficient_le_two_c model hrho hbetaUnit
  have htwoC₀ : 0 ≤ 2 * p.c := mul_nonneg (by norm_num) model.c_pos.le
  have hmul : |A * stationaryStockLag p (beta, D)| ≤
      2 * p.c * |stationaryStockLag p (beta, D)| := by
    rw [abs_mul, abs_of_nonneg hA₀]
    exact mul_le_mul_of_nonneg_right hAle (abs_nonneg _)
  have hid := neg_civicWeightedGradient_eq_barrier_add_lag p rho beta D
  have hbarrier₀ := weighted.barrier_nonneg_before hbeta
  calc
    |civicWeightedGradient p rho beta D| =
        |-civicWeightedGradient p rho beta D| := (abs_neg _).symm
    _ =
        |weightedBarrierIntegrand p rho beta +
          A * stationaryStockLag p (beta, D)| := by
      rw [hid]
    _ ≤ |weightedBarrierIntegrand p rho beta| +
        |A * stationaryStockLag p (beta, D)| := abs_add_le _ _
    _ ≤ weightedBarrierIntegrand p rho beta +
        2 * p.c * |stationaryStockLag p (beta, D)| := by
      rw [abs_of_nonneg hbarrier₀]
      linarith

/-- A Lipschitz barrier which vanishes at the saddle is at most its
Lipschitz constant times the remaining saddle distance. -/
theorem weightedBarrierIntegrand_le_lipschitz_saddle_distance
    {p : LoopParams} {rho L beta : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (hbeta : beta ∈ Icc (0 : ℝ) weighted.βdagger) :
    weightedBarrierIntegrand p rho beta ≤
      L * (weighted.βdagger - beta) := by
  have hsaddle : weightedBarrierIntegrand p rho weighted.βdagger = 0 := by
    simp only [weightedBarrierIntegrand, weighted.gradient_zero, neg_zero]
  have hsaddleMem : weighted.βdagger ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨weighted.βdagger_mem.1.le, le_rfl⟩
  have hdist := hL.bound hbeta hsaddleMem
  have hbarrier₀ := weighted.barrier_nonneg_before hbeta
  simpa only [hsaddle, sub_zero, abs_of_nonneg hbarrier₀,
    abs_of_nonpos (sub_nonpos.mpr hbeta.2), neg_sub] using hdist

/-- Re-climbing a retreat of size at most `2 alpha q` costs only a quadratic
amount after the action's `2 / alpha` scaling.  This is the integral part of
the truncate-before comparison. -/
theorem scaled_weightedBarrierRetreatIntegral_le_quadratic
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho L alpha beta b w q : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (halpha : 0 < alpha) (halphaOne : alpha ≤ 1)
    (hbeta : beta ∈ Icc (0 : ℝ) weighted.βdagger)
    (hb : b ∈ Icc (0 : ℝ) weighted.βdagger) (hbetaB : beta ≤ b)
    (hw : 0 ≤ w) (hq : 0 ≤ q)
    (hdistance : weighted.βdagger - beta ≤ w + 2 * alpha * q)
    (hretreat : b - beta ≤ 2 * alpha * q) :
    (2 / alpha) *
        (∫ z in beta..b, weightedBarrierIntegrand p rho z) ≤
      14 * L * (w ^ 2 + q ^ 2) := by
  let f := weightedBarrierIntegrand p rho
  have hcont : ContinuousOn f (Icc (0 : ℝ) weighted.βdagger) := by
    simpa only [f] using continuousOn_weightedBarrierIntegrand model rho weighted
  have hintegral := integral_le_left_rectangle_add_lipschitz
    hcont hL hbeta hb hbetaB
  have hheight := weightedBarrierIntegrand_le_lipschitz_saddle_distance
    weighted hL hbeta
  have hwidth₀ : 0 ≤ b - beta := sub_nonneg.mpr hbetaB
  have hdistance₀ : 0 ≤ weighted.βdagger - beta :=
    sub_nonneg.mpr hbeta.2
  have hL₀ : 0 ≤ L := hL.nonneg
  have hwidthSq : (b - beta) ^ 2 ≤ (2 * alpha * q) ^ 2 :=
    (sq_le_sq₀ hwidth₀
      (mul_nonneg (mul_nonneg (by norm_num) halpha.le) hq)).2 hretreat
  have hhalfNonneg : 0 ≤ L / 2 :=
    div_nonneg hL₀ (by norm_num)
  have hhalfWidth : (L / 2) * (b - beta) ^ 2 ≤
      (L / 2) * (2 * alpha * q) ^ 2 :=
    mul_le_mul_of_nonneg_left hwidthSq hhalfNonneg
  have hupper :
      (∫ z in beta..b, weightedBarrierIntegrand p rho z) ≤
        L * (w + 2 * alpha * q) * (2 * alpha * q) +
          (L / 2) * (2 * alpha * q) ^ 2 := by
    dsimp only [f] at hintegral
    have hdistanceScaled := mul_le_mul_of_nonneg_left hdistance hL₀
    have hfirst :
        weightedBarrierIntegrand p rho beta * (b - beta) ≤
          (L * (w + 2 * alpha * q)) * (2 * alpha * q) := by
      calc
        _ ≤ (L * (weighted.βdagger - beta)) * (b - beta) :=
          mul_le_mul_of_nonneg_right hheight hwidth₀
        _ ≤ (L * (w + 2 * alpha * q)) * (2 * alpha * q) :=
          mul_le_mul hdistanceScaled hretreat hwidth₀
            (mul_nonneg hL₀
              (add_nonneg hw
                (mul_nonneg (mul_nonneg (by norm_num) halpha.le) hq)))
    linarith
  have hscale₀ : 0 ≤ 2 / alpha := div_nonneg (by norm_num) halpha.le
  have hscaled := mul_le_mul_of_nonneg_left hupper hscale₀
  have hscaledUpper :
      (2 / alpha) *
          (L * (w + 2 * alpha * q) * (2 * alpha * q) +
            (L / 2) * (2 * alpha * q) ^ 2) =
        4 * L * w * q + 12 * alpha * L * q ^ 2 := by
    field_simp [halpha.ne']
    ring
  rw [hscaledUpper] at hscaled
  have hcross := sq_nonneg (w - q)
  have hcrossScaled :
      4 * L * w * q ≤ 2 * L * (w ^ 2 + q ^ 2) := by
    have hnonneg := mul_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hL₀) hcross
    nlinarith
  have halphaTerm : 12 * alpha * L * q ^ 2 ≤ 12 * L * q ^ 2 := by
    have hfactor : 0 ≤ 12 * L * q ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_right halphaOne hfactor
    nlinarith
  have htarget :
      4 * L * w * q + 12 * alpha * L * q ^ 2 ≤
        14 * L * (w ^ 2 + q ^ 2) := by
    have hwSq : 0 ≤ L * w ^ 2 := mul_nonneg hL₀ (sq_nonneg w)
    nlinarith
  exact hscaled.trans htarget

/-- Before its first target crossing, an arbitrary-start margin climb has
inactive projection and exact increment `alpha * (|g| + epsilon)`. -/
theorem marginClimbPathFrom_before_stop_step_data
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho epsilon target : ℝ} {x₀ : LoopState}
    (hrho : 0 ≤ rho) (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (hx₀ : x₀ ∈ absorbingBox p) (hstart : x₀.1 ≤ target)
    (htarget : target < 1) (hepsilon : 0 < epsilon)
    (hroom : p.α * (passageGradientBound p + epsilon) ≤ 1 - target)
    {n : ℕ} (hn : n < marginClimbStopFrom p rho epsilon target x₀) :
    let g := civicWeightedGradient p rho
      (marginClimbPathFrom p rho epsilon x₀ n).1
      (marginClimbPathFrom p rho epsilon x₀ n).2
    (marginClimbPathFrom p rho epsilon x₀ (n + 1)).1 -
          (marginClimbPathFrom p rho epsilon x₀ n).1 =
        p.α * (|g| + epsilon) ∧
      |g| ≤ passageGradientBound p := by
  let x := marginClimbPathFrom p rho epsilon x₀ n
  let g := civicWeightedGradient p rho x.1 x.2
  let path := marginClimbPathFrom_isControlled p rho epsilon x₀
  have hxBox : x ∈ absorbingBox p := path.mem_absorbingBox model hx₀ n
  have hxTarget : x.1 ≤ target :=
    marginClimbPathFrom_le_target_before_stop
      model hx₀.1 hstart htarget hepsilon hn
  have hgBound : |g| ≤ passageGradientBound p := by
    exact abs_civicWeightedGradient_le_passageGradientBound
      model hrho hcoop hxBox
  have hnet : civicWeightedGradient p rho x.1 x.2 +
      marginClimbControl p rho epsilon x = |g| + epsilon := by
    simpa only [g] using marginClimb_net_gradient_eq_abs p rho epsilon x
  have hnet₀ : 0 ≤ |g| + epsilon := by positivity
  have hnetLe : |g| + epsilon ≤ passageGradientBound p + epsilon := by
    linarith
  have hrawMem : x.1 + p.α * (|g| + epsilon) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · nlinarith [hxBox.1.1, model.α_pos]
    · have hscaled := mul_le_mul_of_nonneg_left hnetLe model.α_pos.le
      linarith
  have hnext :
      (marginClimbPathFrom p rho epsilon x₀ (n + 1)).1 =
        x.1 + p.α * (|g| + epsilon) := by
    rw [marginClimbPathFrom_succ]
    simp only [controlledCivicWeightedStep, marginClimbControlSequenceFrom]
    rw [hnet, clipUnit_eq_self hrawMem]
  dsimp only [x] at hnext ⊢
  exact ⟨by linarith, hgBound⟩

/-- Uniform lower and upper policy increments before the first target
crossing. -/
theorem marginClimbPathFrom_before_stop_increment_bounds
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho epsilon target : ℝ} {x₀ : LoopState}
    (hrho : 0 ≤ rho) (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (hx₀ : x₀ ∈ absorbingBox p) (hstart : x₀.1 ≤ target)
    (htarget : target < 1) (hepsilon : 0 < epsilon)
    (hroom : p.α * (passageGradientBound p + epsilon) ≤ 1 - target)
    {n : ℕ} (hn : n < marginClimbStopFrom p rho epsilon target x₀) :
    p.α * epsilon ≤
        (marginClimbPathFrom p rho epsilon x₀ (n + 1)).1 -
          (marginClimbPathFrom p rho epsilon x₀ n).1 ∧
      (marginClimbPathFrom p rho epsilon x₀ (n + 1)).1 -
          (marginClimbPathFrom p rho epsilon x₀ n).1 ≤
        p.α * (passageGradientBound p + epsilon) := by
  obtain ⟨hstep, hgBound⟩ := marginClimbPathFrom_before_stop_step_data
    model hrho hcoop hx₀ hstart htarget hepsilon hroom hn
  rw [hstep]
  constructor
  · exact mul_le_mul_of_nonneg_left
      (by exact le_add_of_nonneg_left (abs_nonneg _)) model.α_pos.le
  · exact mul_le_mul_of_nonneg_left (by linarith) model.α_pos.le

/-- Exact action decomposition for the restarted climb.  The positive part
of `-g` is the work-bearing term; a favorable positive gradient pays only
the margin cost. -/
theorem marginClimbPathFrom_action_summand_eq
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho epsilon target : ℝ} {x₀ : LoopState}
    (hrho : 0 ≤ rho) (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (hx₀ : x₀ ∈ absorbingBox p) (hstart : x₀.1 ≤ target)
    (htarget : target < 1) (hepsilon : 0 < epsilon)
    (hroom : p.α * (passageGradientBound p + epsilon) ≤ 1 - target)
    {n : ℕ} (hn : n < marginClimbStopFrom p rho epsilon target x₀) :
    let g := civicWeightedGradient p rho
      (marginClimbPathFrom p rho epsilon x₀ n).1
      (marginClimbPathFrom p rho epsilon x₀ n).2
    (marginClimbControlSequenceFrom p rho epsilon x₀ n) ^ 2 / 2 =
      (2 / p.α) * max (-g) 0 *
        ((marginClimbPathFrom p rho epsilon x₀ (n + 1)).1 -
          (marginClimbPathFrom p rho epsilon x₀ n).1) +
        epsilon ^ 2 / 2 := by
  let g := civicWeightedGradient p rho
    (marginClimbPathFrom p rho epsilon x₀ n).1
    (marginClimbPathFrom p rho epsilon x₀ n).2
  obtain ⟨hstep, _hgBound⟩ := marginClimbPathFrom_before_stop_step_data
    model hrho hcoop hx₀ hstart htarget hepsilon hroom hn
  by_cases hg : 0 ≤ g
  · have hmax : max (-g) 0 = 0 := max_eq_right (neg_nonpos.mpr hg)
    simp only [marginClimbControlSequenceFrom, marginClimbControl,
      doublingControl, g, hmax]
    ring
  · have hg' : g < 0 := lt_of_not_ge hg
    have hmax : max (-g) 0 = -g := max_eq_left (neg_nonneg.mpr hg'.le)
    have habs : |g| = -g := abs_of_neg hg'
    simp only [marginClimbControlSequenceFrom, marginClimbControl,
      doublingControl, g, hmax]
    rw [hstep, habs]
    field_simp [model.α_pos.ne']
    ring

/-- Exact lag transport for a controlled path with an arbitrary initial
state. -/
theorem IsControlledCivicWeightedPathFrom.stationaryStockLag_succ
    {p : LoopParams} {rho : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    stationaryStockLag p (x (n + 1)) =
      p.s (x n).1 * stationaryStockLag p (x n) +
        (p.stationaryStock (x (n + 1)).1 -
          p.stationaryStock (x n).1) := by
  rw [path.step n]
  exact stationaryStockLag_controlledCivicWeightedStep
    model rho (u n) (path.policy_mem hx₀ n)

/-- The arbitrary-start margin climb obeys the same exact forced-contraction
lag recursion as the calibrated climb. -/
theorem marginClimbPathFrom_stationaryStockLag_succ
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho epsilon : ℝ} {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    stationaryStockLag p
        (marginClimbPathFrom p rho epsilon x₀ (n + 1)) =
      p.s (marginClimbPathFrom p rho epsilon x₀ n).1 *
          stationaryStockLag p
            (marginClimbPathFrom p rho epsilon x₀ n) +
        (p.stationaryStock
            (marginClimbPathFrom p rho epsilon x₀ (n + 1)).1 -
          p.stationaryStock
            (marginClimbPathFrom p rho epsilon x₀ n).1) := by
  exact (marginClimbPathFrom_isControlled p rho epsilon x₀).stationaryStockLag_succ
    model hx₀ n

/-- Sharp one-step absolute-lag recursion for an arbitrary-start margin
climb.  The forcing is the realized policy increment, not a global mesh
bound. -/
theorem marginClimbPathFrom_abs_lag_succ_le_increment
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho epsilon : ℝ} {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hepsilon : 0 ≤ epsilon)
    (n : ℕ) :
    |stationaryStockLag p
        (marginClimbPathFrom p rho epsilon x₀ (n + 1))| ≤
      p.s (marginClimbPathFrom p rho epsilon x₀ n).1 *
          |stationaryStockLag p
            (marginClimbPathFrom p rho epsilon x₀ n)| +
        driftStationaryStockLipschitzBound p *
          ((marginClimbPathFrom p rho epsilon x₀ (n + 1)).1 -
            (marginClimbPathFrom p rho epsilon x₀ n).1) := by
  let x : ℕ → LoopState := marginClimbPathFrom p rho epsilon x₀
  let K := driftStationaryStockLipschitzBound p
  have hrec := marginClimbPathFrom_stationaryStockLag_succ
    model (rho := rho) (epsilon := epsilon) hx₀ n
  have hmono : Monotone (fun k ↦ (x k).1) := by
    simpa only [x] using
      monotone_marginClimbPolicyFrom model rho epsilon hx₀ hepsilon
  have hpolicy : (x n).1 ∈ Icc (0 : ℝ) 1 :=
    (marginClimbPathFrom_isControlled p rho epsilon x₀).policy_mem hx₀ n
  have hnextPolicy : (x (n + 1)).1 ∈ Icc (0 : ℝ) 1 :=
    (marginClimbPathFrom_isControlled p rho epsilon x₀).policy_mem hx₀ (n + 1)
  have hchar₀ : 0 ≤ p.stationaryStock (x (n + 1)).1 -
      p.stationaryStock (x n).1 := sub_nonneg.mpr <|
    (stationaryStock_strictMonoOn model).monotoneOn
      hpolicy hnextPolicy (hmono n.le_succ)
  have hchar := stationaryStock_sub_le_driftLipschitz
    model hpolicy hnextPolicy (hmono n.le_succ)
  have hs₀ : 0 ≤ p.s (x n).1 :=
    (driftStockMultiplier_nonneg_le model hpolicy).1
  rw [show stationaryStockLag p (x (n + 1)) =
      p.s (x n).1 * stationaryStockLag p (x n) +
        (p.stationaryStock (x (n + 1)).1 -
          p.stationaryStock (x n).1) by simpa only [x] using hrec]
  calc
    |p.s (x n).1 * stationaryStockLag p (x n) +
        (p.stationaryStock (x (n + 1)).1 -
          p.stationaryStock (x n).1)| ≤
        |p.s (x n).1 * stationaryStockLag p (x n)| +
          |p.stationaryStock (x (n + 1)).1 -
            p.stationaryStock (x n).1| := abs_add_le _ _
    _ = p.s (x n).1 * |stationaryStockLag p (x n)| +
          (p.stationaryStock (x (n + 1)).1 -
            p.stationaryStock (x n).1) := by
      rw [abs_mul, abs_of_nonneg hs₀, abs_of_nonneg hchar₀]
    _ ≤ p.s (x n).1 * |stationaryStockLag p (x n)| +
          K * ((x (n + 1)).1 - (x n).1) := by
      linarith
    _ = _ := by rfl

/-- Dropping contraction and telescoping the characteristic displacement
gives a horizon-free pointwise lag bound along a restarted climb. -/
theorem marginClimbPathFrom_abs_lag_le_initial_add_advance
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho epsilon : ℝ} {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hepsilon : 0 ≤ epsilon)
    (n : ℕ) :
    |stationaryStockLag p
        (marginClimbPathFrom p rho epsilon x₀ n)| ≤
      |stationaryStockLag p x₀| +
        driftStationaryStockLipschitzBound p *
          ((marginClimbPathFrom p rho epsilon x₀ n).1 - x₀.1) := by
  let x : ℕ → LoopState := marginClimbPathFrom p rho epsilon x₀
  let K := driftStationaryStockLipschitzBound p
  have hmono : Monotone (fun k ↦ (x k).1) := by
    simpa only [x] using
      monotone_marginClimbPolicyFrom model rho epsilon hx₀ hepsilon
  have hK₀ : 0 ≤ K := (driftStationaryStockLipschitzBound_pos model).le
  induction n with
  | zero =>
      simp only [marginClimbPathFrom_zero, sub_self, mul_zero, add_zero]
      exact le_rfl
  | succ n ih =>
      have hpolicy : (x n).1 ∈ Icc (0 : ℝ) 1 :=
        (marginClimbPathFrom_isControlled p rho epsilon x₀).policy_mem hx₀ n
      have hs := driftStockMultiplier_nonneg_le model hpolicy
      have hstep := marginClimbPathFrom_abs_lag_succ_le_increment
        model (rho := rho) hx₀ hepsilon n
      have hcontract : p.s (x n).1 * |stationaryStockLag p (x n)| ≤
          |stationaryStockLag p (x n)| := by
        exact mul_le_of_le_one_left (abs_nonneg _)
          (hs.2.trans (sub_le_self 1 model.lambda₀_pos.le))
      change |stationaryStockLag p (x (n + 1))| ≤
        |stationaryStockLag p x₀| + K * ((x (n + 1)).1 - x₀.1)
      change |stationaryStockLag p (x (n + 1))| ≤
        p.s (x n).1 * |stationaryStockLag p (x n)| +
          K * ((x (n + 1)).1 - (x n).1) at hstep
      linarith

/-- Telescoping lag budget: contraction turns the sum of all absolute lags
into initial lag plus total characteristic displacement. -/
theorem marginClimbPathFrom_lambda_mul_sum_abs_lag_le
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho epsilon : ℝ} {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hepsilon : 0 ≤ epsilon)
    (N : ℕ) :
    p.lambda₀ *
        ∑ n ∈ Finset.range N,
          |stationaryStockLag p
            (marginClimbPathFrom p rho epsilon x₀ n)| ≤
      |stationaryStockLag p x₀| +
        driftStationaryStockLipschitzBound p *
          ((marginClimbPathFrom p rho epsilon x₀ N).1 - x₀.1) := by
  let x : ℕ → LoopState := marginClimbPathFrom p rho epsilon x₀
  let a : ℕ → ℝ := fun n ↦ |stationaryStockLag p (x n)|
  let K := driftStationaryStockLipschitzBound p
  have hpolicy : ∀ n, (x n).1 ∈ Icc (0 : ℝ) 1 := fun n ↦
    (marginClimbPathFrom_isControlled p rho epsilon x₀).policy_mem hx₀ n
  have hcell : ∀ n, p.lambda₀ * a n ≤
      a n - a (n + 1) + K * ((x (n + 1)).1 - (x n).1) := by
    intro n
    have hlag := marginClimbPathFrom_abs_lag_succ_le_increment
      model (rho := rho) hx₀ hepsilon n
    have hs := driftStockMultiplier_nonneg_le model (hpolicy n)
    dsimp only [a]
    have hcontract :
        |stationaryStockLag p (x (n + 1))| ≤
          (1 - p.lambda₀) * |stationaryStockLag p (x n)| +
            K * ((x (n + 1)).1 - (x n).1) := by
      calc
        _ ≤ p.s (x n).1 * |stationaryStockLag p (x n)| +
            K * ((x (n + 1)).1 - (x n).1) := by
          simpa only [x, K] using hlag
        _ ≤ (1 - p.lambda₀) * |stationaryStockLag p (x n)| +
            K * ((x (n + 1)).1 - (x n).1) := by
          have hmul := mul_le_mul_of_nonneg_right hs.2
            (abs_nonneg (stationaryStockLag p (x n)))
          linarith
    linarith
  have hsum := Finset.sum_le_sum fun n (_hn : n ∈ Finset.range N) ↦ hcell n
  have hleft :
      (∑ n ∈ Finset.range N, p.lambda₀ * a n) =
        p.lambda₀ * ∑ n ∈ Finset.range N, a n := by
    rw [Finset.mul_sum]
  have hright :
      (∑ n ∈ Finset.range N,
          (a n - a (n + 1) + K * ((x (n + 1)).1 - (x n).1))) =
        a 0 - a N + K * ((x N).1 - (x 0).1) := by
    have haTel := Finset.sum_range_sub (fun n ↦ -a n) N
    have hxTel := Finset.sum_range_sub (fun n ↦ (x n).1) N
    simp only [neg_sub_neg] at haTel
    calc
      _ = (∑ n ∈ Finset.range N, (a n - a (n + 1))) +
          K * ∑ n ∈ Finset.range N, ((x (n + 1)).1 - (x n).1) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = _ := by rw [haTel, hxTel]
  rw [hleft, hright] at hsum
  have hfinal :
      p.lambda₀ * ∑ n ∈ Finset.range N, a n ≤
        a 0 + K * ((x N).1 - (x 0).1) := by
    linarith [abs_nonneg (stationaryStockLag p (x N))]
  simpa only [x, a, K, marginClimbPathFrom_zero] using hfinal

/-- The contraction budget also controls the sum of squared lags by the
square of initial lag plus total characteristic displacement. -/
theorem marginClimbPathFrom_sum_abs_lag_sq_le
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho epsilon : ℝ} {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hepsilon : 0 ≤ epsilon)
    (N : ℕ) :
    (∑ n ∈ Finset.range N,
        |stationaryStockLag p
          (marginClimbPathFrom p rho epsilon x₀ n)| ^ 2) ≤
      (|stationaryStockLag p x₀| +
          driftStationaryStockLipschitzBound p *
            ((marginClimbPathFrom p rho epsilon x₀ N).1 - x₀.1)) ^ 2 /
        p.lambda₀ := by
  let x : ℕ → LoopState := marginClimbPathFrom p rho epsilon x₀
  let a : ℕ → ℝ := fun n ↦ |stationaryStockLag p (x n)|
  let K := driftStationaryStockLipschitzBound p
  let R := a 0 + K * ((x N).1 - (x 0).1)
  have hmono : Monotone (fun k ↦ (x k).1) := by
    simpa only [x] using
      monotone_marginClimbPolicyFrom model rho epsilon hx₀ hepsilon
  have hK₀ : 0 ≤ K := (driftStationaryStockLipschitzBound_pos model).le
  have hR₀ : 0 ≤ R := by
    exact add_nonneg (abs_nonneg _)
      (mul_nonneg hK₀ (sub_nonneg.mpr (hmono (Nat.zero_le N))))
  have haLe : ∀ n < N, a n ≤ R := by
    intro n hn
    have hpoint := marginClimbPathFrom_abs_lag_le_initial_add_advance
      model (rho := rho) hx₀ hepsilon n
    have hbeta : (x n).1 ≤ (x N).1 := hmono (Nat.le_of_lt hn)
    have hdisp : K * ((x n).1 - (x 0).1) ≤
        K * ((x N).1 - (x 0).1) :=
      mul_le_mul_of_nonneg_left (by linarith) hK₀
    have hpoint' : a n ≤ a 0 + K * ((x n).1 - (x 0).1) := by
      simpa only [a, x, marginClimbPathFrom_zero] using hpoint
    dsimp only [R]
    linarith
  have hsquares : (∑ n ∈ Finset.range N, a n ^ 2) ≤
      R * ∑ n ∈ Finset.range N, a n := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, R * a n := by
        apply Finset.sum_le_sum
        intro n hn
        have hanonneg : 0 ≤ a n := abs_nonneg _
        nlinarith [haLe n (Finset.mem_range.mp hn)]
      _ = R * ∑ n ∈ Finset.range N, a n := by
        rw [Finset.mul_sum]
  have hlags := marginClimbPathFrom_lambda_mul_sum_abs_lag_le
    model (rho := rho) hx₀ hepsilon N
  have hsum : (∑ n ∈ Finset.range N, a n) ≤ R / p.lambda₀ := by
    apply (le_div_iff₀ model.lambda₀_pos).2
    dsimp only [a, R, x] at hlags ⊢
    simpa only [marginClimbPathFrom_zero, mul_comm] using hlags
  calc
    (∑ n ∈ Finset.range N,
        |stationaryStockLag p
          (marginClimbPathFrom p rho epsilon x₀ n)| ^ 2) =
        ∑ n ∈ Finset.range N, a n ^ 2 := by rfl
    _ ≤ R * ∑ n ∈ Finset.range N, a n := hsquares
    _ ≤ R * (R / p.lambda₀) :=
      mul_le_mul_of_nonneg_left hsum hR₀
    _ = R ^ 2 / p.lambda₀ := by ring
    _ = _ := by
      simp only [R, a, K, x, marginClimbPathFrom_zero]

/-- Natural-pace lag work is quadratic: the realized increment contributes
one factor of the adaptation rate, while contraction sums the remaining lag
over time.  This is the key estimate that lets the passage surgery use one
restarted climb instead of an explicit dyadic hold cascade. -/
theorem marginClimbPathFrom_abs_lag_work_le_quadratic
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho epsilon L : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    {x₀ : LoopState} (hx₀ : x₀ ∈ absorbingBox p)
    (hstart : x₀.1 ≤ weighted.βdagger) (hepsilon : 0 < epsilon)
    (hroom : p.α * (passageGradientBound p + epsilon) ≤
      1 - weighted.βdagger) :
    let T := marginClimbStopFrom p rho epsilon weighted.βdagger x₀
    let R := |stationaryStockLag p x₀| +
      driftStationaryStockLipschitzBound p *
        ((marginClimbPathFrom p rho epsilon x₀ T).1 - x₀.1)
    (∑ n ∈ Finset.range T,
        |stationaryStockLag p
            (marginClimbPathFrom p rho epsilon x₀ n)| *
          ((marginClimbPathFrom p rho epsilon x₀ (n + 1)).1 -
            (marginClimbPathFrom p rho epsilon x₀ n).1)) ≤
      (p.α / p.lambda₀) *
        ((L * (weighted.βdagger - x₀.1) + epsilon) * R +
          2 * p.c * R ^ 2) := by
  let x : ℕ → LoopState := marginClimbPathFrom p rho epsilon x₀
  let T := marginClimbStopFrom p rho epsilon weighted.βdagger x₀
  let a : ℕ → ℝ := fun n ↦ |stationaryStockLag p (x n)|
  let R := a 0 + driftStationaryStockLipschitzBound p *
    ((x T).1 - (x 0).1)
  let H := L * (weighted.βdagger - x₀.1) + epsilon
  have hmono : Monotone (fun n ↦ (x n).1) := by
    simpa only [x] using
      monotone_marginClimbPolicyFrom model rho epsilon hx₀.1 hepsilon.le
  have hL₀ : 0 ≤ L := hL.nonneg
  have hH₀ : 0 ≤ H := by
    dsimp only [H]
    exact add_nonneg
      (mul_nonneg hL₀ (sub_nonneg.mpr hstart)) hepsilon.le
  have hcell : ∀ n < T,
      a n * ((x (n + 1)).1 - (x n).1) ≤
        p.α * (H * a n + 2 * p.c * a n ^ 2) := by
    intro n hn
    have hbetaUnit : (x n).1 ∈ Icc (0 : ℝ) 1 :=
      (marginClimbPathFrom_isControlled p rho epsilon x₀).policy_mem hx₀.1 n
    have hbetaLe : (x n).1 ≤ weighted.βdagger :=
      marginClimbPathFrom_le_target_before_stop
        model hx₀.1 hstart weighted.βdagger_mem.2 hepsilon hn
    have hbeta : (x n).1 ∈ Icc (0 : ℝ) weighted.βdagger :=
      ⟨hbetaUnit.1, hbetaLe⟩
    have hf := weightedBarrierIntegrand_le_lipschitz_saddle_distance
      weighted hL hbeta
    have hdist : weighted.βdagger - (x n).1 ≤
        weighted.βdagger - x₀.1 := by
      have hstartMono : x₀.1 ≤ (x n).1 := by
        simpa only [x, marginClimbPathFrom_zero] using hmono (Nat.zero_le n)
      linarith
    have hfH : weightedBarrierIntegrand p rho (x n).1 ≤
        L * (weighted.βdagger - x₀.1) := by
      exact hf.trans (mul_le_mul_of_nonneg_left hdist hL₀)
    have hg := abs_civicWeightedGradient_le_barrier_add_abs_lag
      model hrho hcoop weighted hbeta (D := (x n).2)
    obtain ⟨hinc, _hgBound⟩ := marginClimbPathFrom_before_stop_step_data
      model hrho hcoop hx₀ hstart weighted.βdagger_mem.2
        hepsilon hroom hn
    have ha₀ : 0 ≤ a n := abs_nonneg _
    have htwoC₀ : 0 ≤ 2 * p.c :=
      mul_nonneg (by norm_num) model.c_pos.le
    have hraw :
        |civicWeightedGradient p rho (x n).1 (x n).2| + epsilon ≤
          H + 2 * p.c * a n := by
      dsimp only [H, a]
      linarith
    have hscaled := mul_le_mul_of_nonneg_left hraw
      (mul_nonneg model.α_pos.le ha₀)
    rw [show (x (n + 1)).1 - (x n).1 =
        p.α * (|civicWeightedGradient p rho (x n).1 (x n).2| + epsilon) by
      simpa only [x] using hinc]
    dsimp only [a, H] at hscaled ⊢
    nlinarith
  have hsumCell := Finset.sum_le_sum fun n hn ↦
    hcell n (Finset.mem_range.mp hn)
  have hlags := marginClimbPathFrom_lambda_mul_sum_abs_lag_le
    model (rho := rho) hx₀.1 hepsilon.le T
  have hsumLag : (∑ n ∈ Finset.range T, a n) ≤ R / p.lambda₀ := by
    apply (le_div_iff₀ model.lambda₀_pos).2
    dsimp only [a, R, x] at hlags ⊢
    simpa only [marginClimbPathFrom_zero, mul_comm] using hlags
  have hsumSq := marginClimbPathFrom_sum_abs_lag_sq_le
    model (rho := rho) hx₀.1 hepsilon.le T
  have hsumSq' : (∑ n ∈ Finset.range T, a n ^ 2) ≤
      R ^ 2 / p.lambda₀ := by
    simpa only [a, R, x, marginClimbPathFrom_zero] using hsumSq
  have hright :
      (∑ n ∈ Finset.range T,
          p.α * (H * a n + 2 * p.c * a n ^ 2)) =
        p.α * (H * (∑ n ∈ Finset.range T, a n) +
          2 * p.c * (∑ n ∈ Finset.range T, a n ^ 2)) := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hright] at hsumCell
  have hinside : H * (∑ n ∈ Finset.range T, a n) +
      2 * p.c * (∑ n ∈ Finset.range T, a n ^ 2) ≤
        H * (R / p.lambda₀) +
          2 * p.c * (R ^ 2 / p.lambda₀) :=
    add_le_add
      (mul_le_mul_of_nonneg_left hsumLag hH₀)
      (mul_le_mul_of_nonneg_left hsumSq'
        (mul_nonneg (by norm_num) model.c_pos.le))
  have htotal := hsumCell.trans
    (mul_le_mul_of_nonneg_left hinside model.α_pos.le)
  have hrearrange : p.α *
      (H * (R / p.lambda₀) + 2 * p.c * (R ^ 2 / p.lambda₀)) =
      (p.α / p.lambda₀) * (H * R + 2 * p.c * R ^ 2) := by
    rw [div_eq_mul_inv]
    ring
  rw [hrearrange] at htotal
  simpa only [T, R, H, a, x, marginClimbPathFrom_zero] using htotal

/-- Left barrier work for an arbitrary-start climb is the exact remaining
barrier integral plus a quadratic mesh term.  The single saddle-crossing
rectangle is included explicitly, so no Lipschitz hypothesis is used beyond
the closed saddle segment. -/
theorem marginClimbPathFrom_barrier_work_le
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho epsilon L : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    {x₀ : LoopState} (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1)
    (hstart : x₀.1 ≤ weighted.βdagger) (hepsilon : 0 < epsilon) :
    let T := marginClimbStopFrom p rho epsilon weighted.βdagger x₀
    (∑ n ∈ Finset.range T,
        weightedBarrierIntegrand p rho
            (marginClimbPathFrom p rho epsilon x₀ n).1 *
          ((marginClimbPathFrom p rho epsilon x₀ (n + 1)).1 -
            (marginClimbPathFrom p rho epsilon x₀ n).1)) ≤
      (∫ z in x₀.1..weighted.βdagger,
          weightedBarrierIntegrand p rho z) +
        L * ∑ n ∈ Finset.range T,
          ((marginClimbPathFrom p rho epsilon x₀ (n + 1)).1 -
            (marginClimbPathFrom p rho epsilon x₀ n).1) ^ 2 := by
  let β : ℕ → ℝ := fun n ↦ (marginClimbPathFrom p rho epsilon x₀ n).1
  let f := weightedBarrierIntegrand p rho
  let T := marginClimbStopFrom p rho epsilon weighted.βdagger x₀
  let M := T - 1
  have hcross : weighted.βdagger < β T := by
    simpa only [β, T] using marginClimbStopFrom_crosses
      model hx₀ hstart weighted.βdagger_mem.2 hepsilon
  have hTpos : 0 < T := by
    by_contra hnot
    have hTzero : T = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hTzero] at hcross
    simp only [β, marginClimbPathFrom_zero] at hcross
    exact (not_lt_of_ge hstart hcross).elim
  have hMsucc : M + 1 = T := by
    dsimp only [M]
    omega
  have hMlt : M < T := by omega
  have hmono : Monotone β := by
    simpa only [β] using
      monotone_marginClimbPolicyFrom model rho epsilon hx₀ hepsilon.le
  have hβmem : ∀ n ≤ M, β n ∈ Icc (0 : ℝ) weighted.βdagger := by
    intro n hn
    have hnT : n < T := by omega
    have hunit :=
      (marginClimbPathFrom_isControlled p rho epsilon x₀).policy_mem hx₀ n
    exact ⟨hunit.1, by
      simpa only [β, T] using marginClimbPathFrom_le_target_before_stop
        model hx₀ hstart weighted.βdagger_mem.2 hepsilon hnT⟩
  have hcont : ContinuousOn f (Icc (0 : ℝ) weighted.βdagger) := by
    simpa only [f] using continuousOn_weightedBarrierIntegrand model rho weighted
  have hpartial := leftRiemannSum_le_integral_add_lipschitz
    hcont hL hβmem (fun n _hn ↦ hmono n.le_succ)
  have htail : 0 ≤ ∫ z in β M..weighted.βdagger, f z := by
    apply intervalIntegral.integral_nonneg (hβmem M le_rfl).2
    intro z hz
    exact weighted.barrier_nonneg_before
      ⟨(hβmem M le_rfl).1.trans hz.1, hz.2⟩
  have hleftInt : IntervalIntegrable f MeasureTheory.volume (β 0) (β M) := by
    have hsubset : [[β 0, β M]] ⊆ Icc (0 : ℝ) weighted.βdagger := by
      rw [uIcc_of_le (hmono (Nat.zero_le M))]
      intro z hz
      exact ⟨(hβmem 0 (Nat.zero_le M)).1.trans hz.1,
        hz.2.trans (hβmem M le_rfl).2⟩
    exact (hcont.mono hsubset).intervalIntegrable
  have hrightInt : IntervalIntegrable f MeasureTheory.volume
      (β M) weighted.βdagger := by
    have hsubset : [[β M, weighted.βdagger]] ⊆
        Icc (0 : ℝ) weighted.βdagger := by
      rw [uIcc_of_le (hβmem M le_rfl).2]
      intro z hz
      exact ⟨(hβmem M le_rfl).1.trans hz.1, hz.2⟩
    exact (hcont.mono hsubset).intervalIntegrable
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    hleftInt hrightInt
  have hintegral : (∫ z in β 0..β M, f z) ≤
      ∫ z in β 0..weighted.βdagger, f z := by
    linarith
  have hpartial' :
      (∑ n ∈ Finset.range M, f (β n) * (β (n + 1) - β n)) ≤
        (∫ z in β 0..weighted.βdagger, f z) +
          (L / 2) * ∑ n ∈ Finset.range M,
            (β (n + 1) - β n) ^ 2 := by
    linarith
  have hfinalBarrier := weightedBarrierIntegrand_le_lipschitz_saddle_distance
    weighted hL (hβmem M le_rfl)
  have hfinalInc₀ : 0 ≤ β (M + 1) - β M :=
    sub_nonneg.mpr (hmono M.le_succ)
  have hremaining₀ : 0 ≤ weighted.βdagger - β M :=
    sub_nonneg.mpr (hβmem M le_rfl).2
  have hremainingLe : weighted.βdagger - β M ≤
      β (M + 1) - β M := by
    rw [← hMsucc] at hcross
    linarith
  have hfinalNonneg : 0 ≤ f (β M) := by
    simpa only [f] using weighted.barrier_nonneg_before (hβmem M le_rfl)
  have hL₀ : 0 ≤ L := hL.nonneg
  have hfinal : f (β M) * (β (M + 1) - β M) ≤
      L * (β (M + 1) - β M) ^ 2 := by
    have hfirst := mul_le_mul_of_nonneg_right hfinalBarrier hfinalInc₀
    have hsecond := mul_le_mul_of_nonneg_left hremainingLe hL₀
    nlinarith
  have hsquares₀ : 0 ≤
      ∑ n ∈ Finset.range M, (β (n + 1) - β n) ^ 2 := by
    positivity
  change (∑ n ∈ Finset.range T,
      f (β n) * (β (n + 1) - β n)) ≤
    (∫ z in x₀.1..weighted.βdagger, f z) +
      L * ∑ n ∈ Finset.range T, (β (n + 1) - β n) ^ 2
  rw [← hMsucc, Finset.sum_range_succ, Finset.sum_range_succ]
  have hstartEq : β 0 = x₀.1 := by
    simp only [β, marginClimbPathFrom_zero]
  rw [← hstartEq]
  nlinarith

/-- The guaranteed positive margin bounds the crossing horizon by the total
realized policy advance. -/
theorem marginClimbStopFrom_mul_margin_le_advance
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho epsilon target : ℝ} {x₀ : LoopState}
    (hrho : 0 ≤ rho) (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (hx₀ : x₀ ∈ absorbingBox p) (hstart : x₀.1 ≤ target)
    (htarget : target < 1) (hepsilon : 0 < epsilon)
    (hroom : p.α * (passageGradientBound p + epsilon) ≤ 1 - target) :
    let T := marginClimbStopFrom p rho epsilon target x₀
    (T : ℝ) * (p.α * epsilon) ≤
      (marginClimbPathFrom p rho epsilon x₀ T).1 - x₀.1 := by
  let x : ℕ → LoopState := marginClimbPathFrom p rho epsilon x₀
  let T := marginClimbStopFrom p rho epsilon target x₀
  have hcell : ∀ n < T, p.α * epsilon ≤
      (x (n + 1)).1 - (x n).1 := by
    intro n hn
    simpa only [x] using
      (marginClimbPathFrom_before_stop_increment_bounds
        model hrho hcoop hx₀ hstart htarget hepsilon hroom hn).1
  have hsum := Finset.sum_le_sum fun n hn ↦
    hcell n (Finset.mem_range.mp hn)
  have htel := Finset.sum_range_sub (fun n ↦ (x n).1) T
  have hconst : (∑ _n ∈ Finset.range T, p.α * epsilon) =
      (T : ℝ) * (p.α * epsilon) := by simp
  rw [hconst, htel] at hsum
  simpa only [T, x, marginClimbPathFrom_zero] using hsum

/-- The first target crossing overshoots by at most one uniform mesh step. -/
theorem marginClimbStopFrom_advance_le_distance_add_mesh
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho epsilon target : ℝ} {x₀ : LoopState}
    (hrho : 0 ≤ rho) (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (hx₀ : x₀ ∈ absorbingBox p) (hstart : x₀.1 ≤ target)
    (htarget : target < 1) (hepsilon : 0 < epsilon)
    (hroom : p.α * (passageGradientBound p + epsilon) ≤ 1 - target) :
    let T := marginClimbStopFrom p rho epsilon target x₀
    (marginClimbPathFrom p rho epsilon x₀ T).1 - x₀.1 ≤
      target - x₀.1 + p.α * (passageGradientBound p + epsilon) := by
  let x : ℕ → LoopState := marginClimbPathFrom p rho epsilon x₀
  let T := marginClimbStopFrom p rho epsilon target x₀
  let M := T - 1
  have hcross : target < (x T).1 := by
    simpa only [x, T] using
      marginClimbStopFrom_crosses model hx₀.1 hstart htarget hepsilon
  have hTpos : 0 < T := by
    by_contra hnot
    have hTzero : T = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hTzero] at hcross
    simp only [x, marginClimbPathFrom_zero] at hcross
    exact (not_lt_of_ge hstart hcross).elim
  have hMsucc : M + 1 = T := by
    dsimp only [M]
    omega
  have hMlt : M < T := by omega
  have hbefore : (x M).1 ≤ target := by
    simpa only [x, T] using
      marginClimbPathFrom_le_target_before_stop
        model hx₀.1 hstart htarget hepsilon hMlt
  have hinc := marginClimbPathFrom_before_stop_increment_bounds
    model hrho hcoop hx₀ hstart htarget hepsilon hroom hMlt
  change (x T).1 - x₀.1 ≤
    target - x₀.1 + p.α * (passageGradientBound p + epsilon)
  rw [← hMsucc]
  dsimp only [x] at hbefore hinc ⊢
  linarith

/-- The sum of squared natural-pace increments is quadratic in the local
barrier height and lag work. -/
theorem marginClimbPathFrom_step_sq_sum_le
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho epsilon L : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    {x₀ : LoopState} (hx₀ : x₀ ∈ absorbingBox p)
    (hstart : x₀.1 ≤ weighted.βdagger) (hepsilon : 0 < epsilon)
    (hroom : p.α * (passageGradientBound p + epsilon) ≤
      1 - weighted.βdagger) :
    let T := marginClimbStopFrom p rho epsilon weighted.βdagger x₀
    let A := (marginClimbPathFrom p rho epsilon x₀ T).1 - x₀.1
    let W := ∑ n ∈ Finset.range T,
      |stationaryStockLag p
          (marginClimbPathFrom p rho epsilon x₀ n)| *
        ((marginClimbPathFrom p rho epsilon x₀ (n + 1)).1 -
          (marginClimbPathFrom p rho epsilon x₀ n).1)
    (∑ n ∈ Finset.range T,
        ((marginClimbPathFrom p rho epsilon x₀ (n + 1)).1 -
          (marginClimbPathFrom p rho epsilon x₀ n).1) ^ 2) ≤
      p.α * ((L * (weighted.βdagger - x₀.1) + epsilon) * A +
        2 * p.c * W) := by
  let x : ℕ → LoopState := marginClimbPathFrom p rho epsilon x₀
  let T := marginClimbStopFrom p rho epsilon weighted.βdagger x₀
  let a : ℕ → ℝ := fun n ↦ |stationaryStockLag p (x n)|
  let H := L * (weighted.βdagger - x₀.1) + epsilon
  have hmono : Monotone (fun n ↦ (x n).1) := by
    simpa only [x] using
      monotone_marginClimbPolicyFrom model rho epsilon hx₀.1 hepsilon.le
  have hL₀ : 0 ≤ L := hL.nonneg
  have hcell : ∀ n < T,
      ((x (n + 1)).1 - (x n).1) ^ 2 ≤
        p.α * (H + 2 * p.c * a n) * ((x (n + 1)).1 - (x n).1) := by
    intro n hn
    have hbetaUnit : (x n).1 ∈ Icc (0 : ℝ) 1 :=
      (marginClimbPathFrom_isControlled p rho epsilon x₀).policy_mem hx₀.1 n
    have hbetaLe : (x n).1 ≤ weighted.βdagger :=
      marginClimbPathFrom_le_target_before_stop
        model hx₀.1 hstart weighted.βdagger_mem.2 hepsilon hn
    have hbeta : (x n).1 ∈ Icc (0 : ℝ) weighted.βdagger :=
      ⟨hbetaUnit.1, hbetaLe⟩
    have hf := weightedBarrierIntegrand_le_lipschitz_saddle_distance
      weighted hL hbeta
    have hdist : weighted.βdagger - (x n).1 ≤
        weighted.βdagger - x₀.1 := by
      have hstartMono : x₀.1 ≤ (x n).1 := by
        simpa only [x, marginClimbPathFrom_zero] using hmono (Nat.zero_le n)
      linarith
    have hfH : weightedBarrierIntegrand p rho (x n).1 ≤
        L * (weighted.βdagger - x₀.1) :=
      hf.trans (mul_le_mul_of_nonneg_left hdist hL₀)
    have hg := abs_civicWeightedGradient_le_barrier_add_abs_lag
      model hrho hcoop weighted hbeta (D := (x n).2)
    obtain ⟨hinc, _hgBound⟩ := marginClimbPathFrom_before_stop_step_data
      model hrho hcoop hx₀ hstart weighted.βdagger_mem.2
        hepsilon hroom hn
    have hinc₀ : 0 ≤ (x (n + 1)).1 - (x n).1 :=
      sub_nonneg.mpr (hmono n.le_succ)
    have hraw :
        |civicWeightedGradient p rho (x n).1 (x n).2| + epsilon ≤
          H + 2 * p.c * a n := by
      dsimp only [H, a]
      linarith
    have hscaled := mul_le_mul_of_nonneg_right hraw
      (mul_nonneg model.α_pos.le hinc₀)
    have hincEq : (x (n + 1)).1 - (x n).1 =
        p.α * (|civicWeightedGradient p rho (x n).1 (x n).2| + epsilon) := by
      simpa only [x] using hinc
    rw [hincEq]
    rw [hincEq] at hscaled
    nlinarith
  have hsum := Finset.sum_le_sum fun n hn ↦
    hcell n (Finset.mem_range.mp hn)
  have htel := Finset.sum_range_sub (fun n ↦ (x n).1) T
  have hright :
      (∑ n ∈ Finset.range T,
          p.α * (H + 2 * p.c * a n) * ((x (n + 1)).1 - (x n).1)) =
        p.α * (H * ((x T).1 - (x 0).1) +
          2 * p.c * ∑ n ∈ Finset.range T,
            a n * ((x (n + 1)).1 - (x n).1)) := by
    calc
      _ = p.α * ∑ n ∈ Finset.range T,
          ((H + 2 * p.c * a n) * ((x (n + 1)).1 - (x n).1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _hn
        ring
      _ = p.α * ∑ n ∈ Finset.range T,
          (H * ((x (n + 1)).1 - (x n).1) +
            2 * p.c * a n * ((x (n + 1)).1 - (x n).1)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro n _hn
        ring
      _ = p.α *
          ((∑ n ∈ Finset.range T,
              H * ((x (n + 1)).1 - (x n).1)) +
            ∑ n ∈ Finset.range T,
              2 * p.c * a n * ((x (n + 1)).1 - (x n).1)) := by
        rw [Finset.sum_add_distrib]
      _ = p.α *
          (H * (∑ n ∈ Finset.range T, ((x (n + 1)).1 - (x n).1)) +
            2 * p.c * ∑ n ∈ Finset.range T,
              a n * ((x (n + 1)).1 - (x n).1)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        simp only [mul_assoc]
      _ = _ := by rw [htel]
  rw [hright] at hsum
  simpa only [T, H, a, x, marginClimbPathFrom_zero] using hsum

/-- Exact finite action identity for the restarted climb. -/
theorem marginClimbPathFrom_action_eq
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho epsilon : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    {x₀ : LoopState} (hx₀ : x₀ ∈ absorbingBox p)
    (hstart : x₀.1 ≤ weighted.βdagger) (hepsilon : 0 < epsilon)
    (hroom : p.α * (passageGradientBound p + epsilon) ≤
      1 - weighted.βdagger) :
    let T := marginClimbStopFrom p rho epsilon weighted.βdagger x₀
    controlAction (marginClimbControlSequenceFrom p rho epsilon x₀) T =
      (2 / p.α) * ∑ n ∈ Finset.range T,
        max (-civicWeightedGradient p rho
            (marginClimbPathFrom p rho epsilon x₀ n).1
            (marginClimbPathFrom p rho epsilon x₀ n).2) 0 *
          ((marginClimbPathFrom p rho epsilon x₀ (n + 1)).1 -
            (marginClimbPathFrom p rho epsilon x₀ n).1) +
        (T : ℝ) * (epsilon ^ 2 / 2) := by
  let T := marginClimbStopFrom p rho epsilon weighted.βdagger x₀
  simp only [controlAction]
  calc
    (1 / 2 : ℝ) * ∑ n ∈ Finset.range T,
        (marginClimbControlSequenceFrom p rho epsilon x₀ n) ^ 2 =
      ∑ n ∈ Finset.range T,
        (marginClimbControlSequenceFrom p rho epsilon x₀ n) ^ 2 / 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      ring
    _ = ∑ n ∈ Finset.range T,
        ((2 / p.α) * max (-civicWeightedGradient p rho
            (marginClimbPathFrom p rho epsilon x₀ n).1
            (marginClimbPathFrom p rho epsilon x₀ n).2) 0 *
          ((marginClimbPathFrom p rho epsilon x₀ (n + 1)).1 -
            (marginClimbPathFrom p rho epsilon x₀ n).1) +
          epsilon ^ 2 / 2) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact marginClimbPathFrom_action_summand_eq
        model hrho hcoop hx₀ hstart weighted.βdagger_mem.2
          hepsilon hroom (Finset.mem_range.mp hn)
    _ = _ := by
      have hfactor :
          (∑ n ∈ Finset.range T,
              (2 / p.α) * max (-civicWeightedGradient p rho
                  (marginClimbPathFrom p rho epsilon x₀ n).1
                  (marginClimbPathFrom p rho epsilon x₀ n).2) 0 *
                ((marginClimbPathFrom p rho epsilon x₀ (n + 1)).1 -
                  (marginClimbPathFrom p rho epsilon x₀ n).1)) =
            (2 / p.α) * ∑ n ∈ Finset.range T,
              max (-civicWeightedGradient p rho
                  (marginClimbPathFrom p rho epsilon x₀ n).1
                  (marginClimbPathFrom p rho epsilon x₀ n).2) 0 *
                ((marginClimbPathFrom p rho epsilon x₀ (n + 1)).1 -
                  (marginClimbPathFrom p rho epsilon x₀ n).1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _hn
        ring
      have hconst : (∑ _n ∈ Finset.range T, epsilon ^ 2 / 2) =
          (T : ℝ) * (epsilon ^ 2 / 2) := by simp
      rw [Finset.sum_add_distrib, hfactor, hconst]

/-- Quantitative action bound for one arbitrary-start natural climb.  The
remaining barrier is paid exactly; every other term is quadratic in the
local saddle distance and the initial stock lag.  In particular, the bound
does not contain the (possibly long) crossing horizon. -/
theorem marginClimbPathFrom_action_le_integral_add_quadratic
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho epsilon L : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    {x₀ : LoopState} (hx₀ : x₀ ∈ absorbingBox p)
    (hstart : x₀.1 ≤ weighted.βdagger) (hepsilon : 0 < epsilon)
    (hroom : p.α * (passageGradientBound p + epsilon) ≤
      1 - weighted.βdagger) :
    let T := marginClimbStopFrom p rho epsilon weighted.βdagger x₀
    let A := (marginClimbPathFrom p rho epsilon x₀ T).1 - x₀.1
    let R := |stationaryStockLag p x₀| +
      driftStationaryStockLipschitzBound p * A
    let H := L * (weighted.βdagger - x₀.1) + epsilon
    controlAction (marginClimbControlSequenceFrom p rho epsilon x₀) T ≤
      (2 / p.α) *
          (∫ z in x₀.1..weighted.βdagger,
            weightedBarrierIntegrand p rho z) +
        2 * L * H * A +
        (4 * p.c * (1 + p.α * L) / p.lambda₀) *
          (H * R + 2 * p.c * R ^ 2) +
        (epsilon / (2 * p.α)) * A := by
  let x : ℕ → LoopState := marginClimbPathFrom p rho epsilon x₀
  let T := marginClimbStopFrom p rho epsilon weighted.βdagger x₀
  let A := (x T).1 - x₀.1
  let R := |stationaryStockLag p x₀| +
    driftStationaryStockLipschitzBound p * A
  let H := L * (weighted.βdagger - x₀.1) + epsilon
  let W := ∑ n ∈ Finset.range T,
    |stationaryStockLag p (x n)| * ((x (n + 1)).1 - (x n).1)
  let Q := H * R + 2 * p.c * R ^ 2
  let I := ∫ z in x₀.1..weighted.βdagger,
    weightedBarrierIntegrand p rho z
  have hmono : Monotone (fun n ↦ (x n).1) := by
    simpa only [x] using
      monotone_marginClimbPolicyFrom model rho epsilon hx₀.1 hepsilon.le
  have hA₀ : 0 ≤ A := by
    dsimp only [A]
    simpa only [x, marginClimbPathFrom_zero] using
      sub_nonneg.mpr (hmono (Nat.zero_le T))
  have hK₀ : 0 ≤ driftStationaryStockLipschitzBound p :=
    (driftStationaryStockLipschitzBound_pos model).le
  have hR₀ : 0 ≤ R := by
    dsimp only [R]
    positivity
  have hH₀ : 0 ≤ H := by
    dsimp only [H]
    exact add_nonneg
      (mul_nonneg hL.nonneg (sub_nonneg.mpr hstart)) hepsilon.le
  have hQ₀ : 0 ≤ Q := by
    dsimp only [Q]
    exact add_nonneg (mul_nonneg hH₀ hR₀)
      (mul_nonneg (mul_nonneg (by norm_num) model.c_pos.le) (sq_nonneg R))
  have hW₀ : 0 ≤ W := by
    dsimp only [W]
    apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg (abs_nonneg _)
      (sub_nonneg.mpr (hmono n.le_succ))
  have hmaxWork :
      (∑ n ∈ Finset.range T,
          max (-civicWeightedGradient p rho (x n).1 (x n).2) 0 *
            ((x (n + 1)).1 - (x n).1)) ≤
        (∑ n ∈ Finset.range T,
          weightedBarrierIntegrand p rho (x n).1 *
            ((x (n + 1)).1 - (x n).1)) + 2 * p.c * W := by
    have hcell : ∀ n ∈ Finset.range T,
        max (-civicWeightedGradient p rho (x n).1 (x n).2) 0 *
              ((x (n + 1)).1 - (x n).1) ≤
          (weightedBarrierIntegrand p rho (x n).1 +
              2 * p.c * |stationaryStockLag p (x n)|) *
            ((x (n + 1)).1 - (x n).1) := by
      intro n hn
      have hnT : n < T := Finset.mem_range.mp hn
      have hpolicy : (x n).1 ∈ Icc (0 : ℝ) 1 :=
        (marginClimbPathFrom_isControlled p rho epsilon x₀).policy_mem
          hx₀.1 n
      have htarget : (x n).1 ≤ weighted.βdagger := by
        simpa only [x, T] using
          marginClimbPathFrom_le_target_before_stop
            model hx₀.1 hstart weighted.βdagger_mem.2 hepsilon hnT
      have hbeta : (x n).1 ∈ Icc (0 : ℝ) weighted.βdagger :=
        ⟨hpolicy.1, htarget⟩
      have hg := abs_civicWeightedGradient_le_barrier_add_abs_lag
        model hrho hcoop weighted hbeta (D := (x n).2)
      have hmaxAbs :
          max (-civicWeightedGradient p rho (x n).1 (x n).2) 0 ≤
            |civicWeightedGradient p rho (x n).1 (x n).2| := by
        apply max_le
        · simpa only [abs_neg] using
            le_abs_self (-civicWeightedGradient p rho (x n).1 (x n).2)
        · exact abs_nonneg _
      have hinc₀ : 0 ≤ (x (n + 1)).1 - (x n).1 :=
        sub_nonneg.mpr (hmono n.le_succ)
      exact mul_le_mul_of_nonneg_right (hmaxAbs.trans hg) hinc₀
    calc
      _ ≤ ∑ n ∈ Finset.range T,
          (weightedBarrierIntegrand p rho (x n).1 +
              2 * p.c * |stationaryStockLag p (x n)|) *
            ((x (n + 1)).1 - (x n).1) := Finset.sum_le_sum hcell
      _ = ∑ n ∈ Finset.range T,
          (weightedBarrierIntegrand p rho (x n).1 *
              ((x (n + 1)).1 - (x n).1) +
            2 * p.c *
              (|stationaryStockLag p (x n)| *
                ((x (n + 1)).1 - (x n).1))) := by
        apply Finset.sum_congr rfl
        intro n _hn
        ring
      _ = (∑ n ∈ Finset.range T,
          weightedBarrierIntegrand p rho (x n).1 *
            ((x (n + 1)).1 - (x n).1)) + 2 * p.c * W := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hbarrier := marginClimbPathFrom_barrier_work_le
    model weighted hL hx₀.1 hstart hepsilon
  have hstepSq := marginClimbPathFrom_step_sq_sum_le
    model hrho hcoop weighted hL hx₀ hstart hepsilon hroom
  have hlagWork := marginClimbPathFrom_abs_lag_work_le_quadratic
    model hrho hcoop weighted hL hx₀ hstart hepsilon hroom
  have hbarrier' :
      (∑ n ∈ Finset.range T,
          weightedBarrierIntegrand p rho (x n).1 *
            ((x (n + 1)).1 - (x n).1)) ≤
        I + L * (p.α * (H * A + 2 * p.c * W)) := by
    have hscaled := mul_le_mul_of_nonneg_left
      (by simpa only [T, A, H, W, x, marginClimbPathFrom_zero] using hstepSq)
      hL.nonneg
    have hbarrierRaw :
        (∑ n ∈ Finset.range T,
            weightedBarrierIntegrand p rho (x n).1 *
              ((x (n + 1)).1 - (x n).1)) ≤
          I + L * ∑ n ∈ Finset.range T,
            ((x (n + 1)).1 - (x n).1) ^ 2 := by
      simpa only [T, I, x] using hbarrier
    linarith
  have hlagWork' : W ≤ (p.α / p.lambda₀) * Q := by
    simpa only [T, R, H, W, Q, A, x,
      marginClimbPathFrom_zero] using hlagWork
  have hcoefficient₀ : 0 ≤ 2 * p.c * (1 + p.α * L) := by
    exact mul_nonneg (mul_nonneg (by norm_num) model.c_pos.le)
      (by nlinarith [model.α_pos, hL.nonneg])
  have hworkTotal :
      (∑ n ∈ Finset.range T,
          max (-civicWeightedGradient p rho (x n).1 (x n).2) 0 *
            ((x (n + 1)).1 - (x n).1)) ≤
        I + p.α * L * H * A +
          2 * p.c * (1 + p.α * L) * ((p.α / p.lambda₀) * Q) := by
    calc
      _ ≤ (∑ n ∈ Finset.range T,
          weightedBarrierIntegrand p rho (x n).1 *
            ((x (n + 1)).1 - (x n).1)) + 2 * p.c * W := hmaxWork
      _ ≤ (I + L * (p.α * (H * A + 2 * p.c * W))) +
          2 * p.c * W := add_le_add hbarrier' le_rfl
      _ = I + p.α * L * H * A +
          2 * p.c * (1 + p.α * L) * W := by ring
      _ ≤ I + p.α * L * H * A +
          2 * p.c * (1 + p.α * L) * ((p.α / p.lambda₀) * Q) :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hlagWork' hcoefficient₀)
  have hmarginRaw := marginClimbStopFrom_mul_margin_le_advance
    model hrho hcoop hx₀ hstart weighted.βdagger_mem.2
      hepsilon hroom
  have hmargin : (T : ℝ) * (epsilon ^ 2 / 2) ≤
      (epsilon / (2 * p.α)) * A := by
    have hscale₀ : 0 ≤ epsilon / (2 * p.α) :=
      div_nonneg hepsilon.le
        (mul_nonneg (by norm_num) model.α_pos.le)
    have hscaled := mul_le_mul_of_nonneg_left
      (by simpa only [T, A, x, marginClimbPathFrom_zero] using hmarginRaw)
      hscale₀
    calc
      (T : ℝ) * (epsilon ^ 2 / 2) =
          (epsilon / (2 * p.α)) * ((T : ℝ) * (p.α * epsilon)) := by
        field_simp [model.α_pos.ne']
      _ ≤ (epsilon / (2 * p.α)) * A := hscaled
  have hscale₀ : 0 ≤ 2 / p.α :=
    div_nonneg (by norm_num) model.α_pos.le
  change controlAction (marginClimbControlSequenceFrom p rho epsilon x₀) T ≤
    (2 / p.α) * I + 2 * L * H * A +
      (4 * p.c * (1 + p.α * L) / p.lambda₀) * Q +
      (epsilon / (2 * p.α)) * A
  rw [marginClimbPathFrom_action_eq
    model hrho hcoop weighted hx₀ hstart hepsilon hroom]
  have hscaledWork := mul_le_mul_of_nonneg_left hworkTotal hscale₀
  calc
    (2 / p.α) *
          (∑ n ∈ Finset.range T,
            max (-civicWeightedGradient p rho (x n).1 (x n).2) 0 *
              ((x (n + 1)).1 - (x n).1)) +
        (T : ℝ) * (epsilon ^ 2 / 2) ≤
      (2 / p.α) *
          (I + p.α * L * H * A +
            2 * p.c * (1 + p.α * L) * ((p.α / p.lambda₀) * Q)) +
        (epsilon / (2 * p.α)) * A := add_le_add hscaledWork hmargin
    _ = (2 / p.α) * I + 2 * L * H * A +
        (4 * p.c * (1 + p.α * L) / p.lambda₀) * Q +
        (epsilon / (2 * p.α)) * A := by
      field_simp [model.α_pos.ne', model.lambda₀_pos.ne']
      ring

/-- Weighted lag-work bound.  If every policy increment is at most `delta`,
the exact telescoping budget gains that mesh factor before it enters the
action estimate. -/
theorem marginClimbPathFrom_abs_lag_work_le
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho epsilon delta : ℝ} {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hepsilon : 0 ≤ epsilon)
    (hdelta : 0 ≤ delta) {N : ℕ}
    (hincrement : ∀ n < N,
      (marginClimbPathFrom p rho epsilon x₀ (n + 1)).1 -
          (marginClimbPathFrom p rho epsilon x₀ n).1 ≤ delta) :
    (∑ n ∈ Finset.range N,
        |stationaryStockLag p
            (marginClimbPathFrom p rho epsilon x₀ n)| *
          ((marginClimbPathFrom p rho epsilon x₀ (n + 1)).1 -
            (marginClimbPathFrom p rho epsilon x₀ n).1)) ≤
      (delta / p.lambda₀) *
        (|stationaryStockLag p x₀| +
          driftStationaryStockLipschitzBound p *
            ((marginClimbPathFrom p rho epsilon x₀ N).1 - x₀.1)) := by
  let x : ℕ → LoopState := marginClimbPathFrom p rho epsilon x₀
  let a : ℕ → ℝ := fun n ↦ |stationaryStockLag p (x n)|
  let R := |stationaryStockLag p x₀| +
    driftStationaryStockLipschitzBound p * ((x N).1 - x₀.1)
  have hlag := marginClimbPathFrom_lambda_mul_sum_abs_lag_le
    model (rho := rho) hx₀ hepsilon N
  have hsumLag : (∑ n ∈ Finset.range N, a n) ≤ R / p.lambda₀ := by
    apply (le_div_iff₀ model.lambda₀_pos).2
    dsimp only [a, R, x] at hlag ⊢
    simpa only [mul_comm] using hlag
  have hterm : ∀ n ∈ Finset.range N,
      a n * ((x (n + 1)).1 - (x n).1) ≤ a n * delta := by
    intro n hn
    exact mul_le_mul_of_nonneg_left
      (hincrement n (Finset.mem_range.mp hn)) (abs_nonneg _)
  have hsum := Finset.sum_le_sum hterm
  calc
    (∑ n ∈ Finset.range N,
        |stationaryStockLag p
            (marginClimbPathFrom p rho epsilon x₀ n)| *
          ((marginClimbPathFrom p rho epsilon x₀ (n + 1)).1 -
            (marginClimbPathFrom p rho epsilon x₀ n).1)) =
        ∑ n ∈ Finset.range N,
          a n * ((x (n + 1)).1 - (x n).1) := by rfl
    _ ≤ ∑ n ∈ Finset.range N, a n * delta := hsum
    _ = delta * ∑ n ∈ Finset.range N, a n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      ring
    _ ≤ delta * (R / p.lambda₀) :=
      mul_le_mul_of_nonneg_left hsumLag hdelta
    _ = (delta / p.lambda₀) * R := by ring
    _ = _ := by rfl

/-- Absolute lag along the restarted climb contracts by the old stock
multiplier, up to the Lipschitz displacement of the stationary
characteristic. -/
theorem marginClimbPathFrom_abs_lag_succ_le
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho epsilon target : ℝ} {x₀ : LoopState}
    (hrho : 0 ≤ rho) (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (hx₀ : x₀ ∈ absorbingBox p) (hstart : x₀.1 ≤ target)
    (htarget : target < 1) (hepsilon : 0 < epsilon)
    (hroom : p.α * (passageGradientBound p + epsilon) ≤ 1 - target)
    {n : ℕ} (hn : n < marginClimbStopFrom p rho epsilon target x₀) :
    |stationaryStockLag p
        (marginClimbPathFrom p rho epsilon x₀ (n + 1))| ≤
      p.s (marginClimbPathFrom p rho epsilon x₀ n).1 *
          |stationaryStockLag p
            (marginClimbPathFrom p rho epsilon x₀ n)| +
        driftStationaryStockLipschitzBound p *
          (p.α * (passageGradientBound p + epsilon)) := by
  let x : ℕ → LoopState := marginClimbPathFrom p rho epsilon x₀
  let K := driftStationaryStockLipschitzBound p
  let delta := p.α * (passageGradientBound p + epsilon)
  have hrec := marginClimbPathFrom_stationaryStockLag_succ
    model (rho := rho) (epsilon := epsilon) hx₀.1 n
  have hmono : Monotone (fun k ↦ (x k).1) := by
    simpa only [x] using
      monotone_marginClimbPolicyFrom model rho epsilon hx₀.1 hepsilon.le
  have hpolicy : (x n).1 ∈ Icc (0 : ℝ) 1 :=
    (marginClimbPathFrom_isControlled p rho epsilon x₀).policy_mem hx₀.1 n
  have hnextPolicy : (x (n + 1)).1 ∈ Icc (0 : ℝ) 1 :=
    (marginClimbPathFrom_isControlled p rho epsilon x₀).policy_mem
      hx₀.1 (n + 1)
  have hchar₀ : 0 ≤ p.stationaryStock (x (n + 1)).1 -
      p.stationaryStock (x n).1 := sub_nonneg.mpr <|
    (stationaryStock_strictMonoOn model).monotoneOn
      hpolicy hnextPolicy (hmono n.le_succ)
  have hchar := stationaryStock_sub_le_driftLipschitz
    model hpolicy hnextPolicy (hmono n.le_succ)
  have hinc := marginClimbPathFrom_before_stop_increment_bounds
    model hrho hcoop hx₀ hstart htarget hepsilon hroom hn
  have hcharLe : p.stationaryStock (x (n + 1)).1 -
      p.stationaryStock (x n).1 ≤ K * delta := by
    calc
      _ ≤ K * ((x (n + 1)).1 - (x n).1) := by
        simpa only [K] using hchar
      _ ≤ K * delta := mul_le_mul_of_nonneg_left
        (by simpa only [x, delta] using hinc.2)
        (driftStationaryStockLipschitzBound_pos model).le
  have hs₀ : 0 ≤ p.s (x n).1 :=
    (driftStockMultiplier_nonneg_le model hpolicy).1
  rw [show stationaryStockLag p (x (n + 1)) =
      p.s (x n).1 * stationaryStockLag p (x n) +
        (p.stationaryStock (x (n + 1)).1 -
          p.stationaryStock (x n).1) by simpa only [x] using hrec]
  calc
    |p.s (x n).1 * stationaryStockLag p (x n) +
        (p.stationaryStock (x (n + 1)).1 -
          p.stationaryStock (x n).1)| ≤
        |p.s (x n).1 * stationaryStockLag p (x n)| +
          |p.stationaryStock (x (n + 1)).1 -
            p.stationaryStock (x n).1| := abs_add_le _ _
    _ = p.s (x n).1 * |stationaryStockLag p (x n)| +
          (p.stationaryStock (x (n + 1)).1 -
            p.stationaryStock (x n).1) := by
      rw [abs_mul, abs_of_nonneg hs₀, abs_of_nonneg hchar₀]
    _ ≤ p.s (x n).1 * |stationaryStockLag p (x n)| + K * delta :=
      by linarith
    _ = _ := by rfl

/-- Uniform absolute-lag envelope through the first target crossing.  The
initial lag may have either sign; all later characteristic forcing is
absorbed by the contraction reserve `lambda₀`. -/
theorem marginClimbPathFrom_abs_lag_le
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho epsilon target : ℝ} {x₀ : LoopState}
    (hrho : 0 ≤ rho) (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (hx₀ : x₀ ∈ absorbingBox p) (hstart : x₀.1 ≤ target)
    (htarget : target < 1) (hepsilon : 0 < epsilon)
    (hroom : p.α * (passageGradientBound p + epsilon) ≤ 1 - target)
    {n : ℕ} (hn : n ≤ marginClimbStopFrom p rho epsilon target x₀) :
    |stationaryStockLag p
        (marginClimbPathFrom p rho epsilon x₀ n)| ≤
      |stationaryStockLag p x₀| +
        driftStationaryStockLipschitzBound p *
          (p.α * (passageGradientBound p + epsilon)) / p.lambda₀ := by
  let x : ℕ → LoopState := marginClimbPathFrom p rho epsilon x₀
  let K := driftStationaryStockLipschitzBound p
  let delta := p.α * (passageGradientBound p + epsilon)
  let B := |stationaryStockLag p x₀| + K * delta / p.lambda₀
  have hK₀ : 0 ≤ K := (driftStationaryStockLipschitzBound_pos model).le
  have hdelta₀ : 0 ≤ delta := by
    dsimp only [delta]
    exact mul_nonneg model.α_pos.le
      (add_pos (passageGradientBound_pos model) hepsilon).le
  have hforcing₀ : 0 ≤ K * delta := mul_nonneg hK₀ hdelta₀
  have hB₀ : 0 ≤ B := by
    dsimp only [B]
    exact add_nonneg (abs_nonneg _)
      (div_nonneg hforcing₀ model.lambda₀_pos.le)
  have hforcingLe : K * delta ≤ p.lambda₀ * B := by
    have hcancel : p.lambda₀ * (K * delta / p.lambda₀) = K * delta := by
      field_simp [model.lambda₀_pos.ne']
    dsimp only [B]
    rw [mul_add, hcancel]
    exact le_add_of_nonneg_left
      (mul_nonneg model.lambda₀_pos.le (abs_nonneg _))
  change |stationaryStockLag p (x n)| ≤ B
  induction n with
  | zero =>
      simp only [x, marginClimbPathFrom_zero]
      dsimp only [B]
      exact le_add_of_nonneg_right
        (div_nonneg hforcing₀ model.lambda₀_pos.le)
  | succ n ih =>
      have hnlt : n < marginClimbStopFrom p rho epsilon target x₀ := by
        omega
      have hnle : n ≤ marginClimbStopFrom p rho epsilon target x₀ := by
        omega
      have ih' := ih hnle
      have hstep := marginClimbPathFrom_abs_lag_succ_le
        model hrho hcoop hx₀ hstart htarget hepsilon hroom hnlt
      have hpolicy : (x n).1 ∈ Icc (0 : ℝ) 1 :=
        (marginClimbPathFrom_isControlled p rho epsilon x₀).policy_mem
          hx₀.1 n
      have hs := driftStockMultiplier_nonneg_le model hpolicy
      have hmul₁ : p.s (x n).1 * |stationaryStockLag p (x n)| ≤
          p.s (x n).1 * B :=
        mul_le_mul_of_nonneg_left ih' hs.1
      have hmul₂ : p.s (x n).1 * B ≤ (1 - p.lambda₀) * B :=
        mul_le_mul_of_nonneg_right hs.2 hB₀
      have hcontract : (1 - p.lambda₀) * B + K * delta ≤ B := by
        nlinarith
      calc
        |stationaryStockLag p (x (n + 1))| ≤
            p.s (x n).1 * |stationaryStockLag p (x n)| + K * delta := by
          simpa only [x, K, delta] using hstep
        _ ≤ p.s (x n).1 * B + K * delta := by linarith
        _ ≤ (1 - p.lambda₀) * B + K * delta := by linarith
        _ ≤ B := hcontract

/-- Restricting the feedback controls to the canonical stopping horizon
reproduces the arbitrary-start climb through that horizon. -/
theorem finiteControlledOrbitFrom_marginClimb_eq
    {p : LoopParams} {rho epsilon target : ℝ} {x₀ : LoopState}
    {n : ℕ}
    (hn : n ≤ marginClimbStopFrom p rho epsilon target x₀) :
    finiteControlledOrbitFrom p rho x₀
        (fun i : Fin (marginClimbStopFrom p rho epsilon target x₀) ↦
          marginClimbControlSequenceFrom p rho epsilon x₀ i) n =
      marginClimbPathFrom p rho epsilon x₀ n := by
  exact finiteControlledOrbitFrom_restrict_eq
    (marginClimbPathFrom_isControlled p rho epsilon x₀) hn

/-! ## Finite above-saddle exit continuation -/

/-- Up to its first-positive-gradient stopping time, the finite control
vector cut from a cancelling hold reproduces that hold exactly from an
arbitrary initial state. -/
theorem finiteControlledOrbitFrom_cancellingHold_eq
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho b D₀ : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (hb : b ∈ Ioc weighted.βdagger 1)
    {k : ℕ} (hk : k ≤ cancellingHoldStop p rho b D₀) :
    finiteControlledOrbitFrom p rho (b, D₀)
        (fun i : Fin (cancellingHoldStop p rho b D₀) ↦
          cancellingHoldControl p rho b D₀ i) k =
      cancellingHoldPath p b D₀ k := by
  let T := cancellingHoldStop p rho b D₀
  have hbclosed : b ∈ Icc (0 : ℝ) 1 :=
    ⟨weighted.βdagger_mem.1.le.trans hb.1.le, hb.2⟩
  have hstationary : 0 < weightedStationaryGradient p rho b :=
    weighted.gradient_pos_of_mem_Ioc hb
  induction k with
  | zero =>
      simp only [finiteControlledOrbitFrom, cancellingHoldPath_zero]
  | succ k ih =>
      have hklt : k < cancellingHoldStop p rho b D₀ := by omega
      rw [finiteControlledOrbitFrom, ih (by omega)]
      simp only [extendFiniteControl, hklt, dite_true]
      exact (cancellingHoldPath_step_before_stop
        model hbclosed hstationary hklt).symm

/-- The finite cancelling-hold continuation from an above-saddle state
leaves the calibrated basin.  This is the standalone finite-path form of
the Exit paragraph in Paper II's quantitative saddle-passage proof. -/
theorem finiteControlledOrbitFrom_cancellingHoldStop_exits
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho b D₀ : ℝ}
    (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hb : b ∈ Ioc weighted.βdagger 1)
    (hD₀ : D₀ ∈ Icc p.I (p.I / p.lambda₀)) :
    finiteControlledOrbitFrom p rho (b, D₀)
        (fun i : Fin (cancellingHoldStop p rho b D₀) ↦
          cancellingHoldControl p rho b D₀ i)
        (cancellingHoldStop p rho b D₀) ∉
      civicWeightedCalibratedBasin p rho := by
  let T := cancellingHoldStop p rho b D₀
  let y := cancellingHoldPath p b D₀ T
  have hyEq :
      finiteControlledOrbitFrom p rho (b, D₀)
          (fun i : Fin T ↦ cancellingHoldControl p rho b D₀ i) T = y := by
    simpa only [T, y] using
      finiteControlledOrbitFrom_cancellingHold_eq
        model weighted hb (k := T) le_rfl
  have hbclosed : b ∈ Icc (0 : ℝ) 1 :=
    ⟨weighted.βdagger_mem.1.le.trans hb.1.le, hb.2⟩
  have hyBox : y ∈ absorbingBox p := by
    simpa only [y, T] using
      cancellingHoldPath_mem_absorbingBox model hbclosed hD₀ T
  obtain ⟨r, hr, hdom⟩ :=
    cancellingHoldStop_dominates_characteristic
      model hcoop weighted hb (D₀ := D₀)
  have hr' : r ∈ Ioc weighted.βdagger 1 :=
    ⟨hr.1, hr.2.trans hyBox.1.2⟩
  have hcaptured :
      Tendsto (civicWeightedOrbit p rho y) atTop (nhds (capturedPoint p)) :=
    civicWeightedOrbit_tendsto_captured_of_dominates_characteristic
      model ss hrhoCure hcoop weighted hr' hyBox (by
        simpa only [y, T] using hdom)
  rw [hyEq]
  intro hcalibrated
  have heq : capturedPoint p = calibratedPoint p :=
    tendsto_nhds_unique hcaptured hcalibrated
  have hfirst := congrArg Prod.fst heq
  norm_num [capturedPoint, calibratedPoint] at hfirst

/-- Appending the canonical above-saddle hold to any finite prefix produces
an actual member of the exit-action set. -/
theorem append_cancellingHoldAction_mem_quasipotentialActionSet
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho b D₀ : ℝ}
    (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    {N : ℕ} (u : Fin N → ℝ)
    (hend : finiteControlledOrbit p rho u N = (b, D₀))
    (hb : b ∈ Ioc weighted.βdagger 1)
    (hD₀ : D₀ ∈ Icc p.I (p.I / p.lambda₀)) :
    gaussianVectorAction u +
        controlAction (cancellingHoldControl p rho b D₀)
          (cancellingHoldStop p rho b D₀) ∈
      quasipotentialActionSet p rho := by
  let T := cancellingHoldStop p rho b D₀
  let v : Fin T → ℝ := fun i ↦ cancellingHoldControl p rho b D₀ i
  let w : Fin (N + T) → ℝ := Fin.append u v
  let x := finiteControlledOrbit p rho w
  have hendpoint :
      x (N + T) = finiteControlledOrbitFrom p rho (b, D₀) v T := by
    dsimp only [x]
    rw [← finiteControlledOrbitFrom_calibratedPoint]
    rw [finiteControlledOrbitFrom_append_right p rho
      (calibratedPoint p) u v le_rfl]
    rw [finiteControlledOrbitFrom_calibratedPoint, hend]
  have hexit : x (N + T) ∉ civicWeightedCalibratedBasin p rho := by
    rw [hendpoint]
    simpa only [v, T] using
      finiteControlledOrbitFrom_cancellingHoldStop_exits
        model ss hrhoCure hcoop weighted hb hD₀
  refine ⟨N + T, extendFiniteControl w, x,
    finiteControlledOrbit_isControlled p rho w, hexit, ?_⟩
  rw [controlAction_extendFiniteControl, show w = Fin.append u v from rfl,
    gaussianVectorAction_append, gaussianVectorAction_restrict]

/-- The above-saddle cancelling-hold price is controlled by the square of
the absolute initial stationary-stock lag, with no sign assumption.  A
negative lag makes the held gradient positive already at time zero, so the
canonical hold then has zero length. -/
theorem cancellingHoldAction_le_abs_lag
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho b D₀ : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hb : b ∈ Ioc weighted.βdagger 1) :
    controlAction (cancellingHoldControl p rho b D₀)
        (cancellingHoldStop p rho b D₀) ≤
      2 * p.c ^ 2 * |p.stationaryStock b - D₀| ^ 2 / p.lambda₀ := by
  have hbclosed : b ∈ Icc (0 : ℝ) 1 :=
    ⟨weighted.βdagger_mem.1.le.trans hb.1.le, hb.2⟩
  have hstationary : 0 < weightedStationaryGradient p rho b :=
    weighted.gradient_pos_of_mem_Ioc hb
  by_cases hgap : 0 ≤ p.stationaryStock b - D₀
  · simpa only [abs_of_nonneg hgap] using
      cancellingHoldAction_le model hrho hcoop hbclosed hstationary
        hgap (le_refl (p.stationaryStock b - D₀))
  · have hgapNeg : p.stationaryStock b - D₀ < 0 := lt_of_not_ge hgap
    let A := 2 * p.c * (1 - p.c * b) - rho
    have hA₀ : 0 ≤ A := by
      simpa only [A] using
        weighted_stock_coefficient_nonnegative model hcoop hbclosed
    have hAlag : A * (p.stationaryStock b - D₀) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hA₀ hgapNeg.le
    have hid := neg_civicWeightedGradient_eq_barrier_add_lag p rho b D₀
    have hnegative : -civicWeightedGradient p rho b D₀ < 0 := by
      simp only [weightedBarrierIntegrand, stationaryStockLag] at hid
      dsimp only [A] at hAlag
      linarith
    have hgradient₀ : 0 < cancellingHoldGradient p rho b D₀ 0 := by
      simp only [cancellingHoldGradient, cancellingHoldStockPath_zero]
      linarith
    have hexists : ∃ n, 0 < cancellingHoldGradient p rho b D₀ n :=
      ⟨0, hgradient₀⟩
    have hstop : cancellingHoldStop p rho b D₀ = 0 := by
      classical
      rw [cancellingHoldStop, firstPositiveIndex, dif_pos hexists]
      exact (Nat.find_eq_zero hexists).2 hgradient₀
    rw [hstop]
    simp only [controlAction, Finset.range_zero, Finset.sum_empty, mul_zero]
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg p.c))
        (sq_nonneg |p.stationaryStock b - D₀|))
      model.lambda₀_pos.le

/-- Quantitative version of the appended Exit continuation: if the stock
lag at the above-saddle endpoint is at most `B`, the extra action is bounded
by the same quadratic geometric-series price as the isolated hold. -/
theorem exists_exitAction_le_prefix_add_quadraticLag
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p)
    {rho b D₀ B : ℝ} (hrho : 0 ≤ rho)
    (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    {N : ℕ} (u : Fin N → ℝ)
    (hend : finiteControlledOrbit p rho u N = (b, D₀))
    (hb : b ∈ Ioc weighted.βdagger 1)
    (hD₀ : D₀ ∈ Icc p.I (p.I / p.lambda₀))
    (hgapNonneg : 0 ≤ p.stationaryStock b - D₀)
    (hgapLe : p.stationaryStock b - D₀ ≤ B) :
    ∃ e ∈ quasipotentialActionSet p rho,
      e ≤ gaussianVectorAction u + 2 * p.c ^ 2 * B ^ 2 / p.lambda₀ := by
  let H := controlAction (cancellingHoldControl p rho b D₀)
    (cancellingHoldStop p rho b D₀)
  refine ⟨gaussianVectorAction u + H, ?_, ?_⟩
  · simpa only [H] using
      append_cancellingHoldAction_mem_quasipotentialActionSet
        model ss hrhoCure hcoop weighted u hend hb hD₀
  · have hbclosed : b ∈ Icc (0 : ℝ) 1 :=
      ⟨weighted.βdagger_mem.1.le.trans hb.1.le, hb.2⟩
    have hstationary : 0 < weightedStationaryGradient p rho b :=
      weighted.gradient_pos_of_mem_Ioc hb
    have hhold := cancellingHoldAction_le model hrho hcoop hbclosed
      hstationary hgapNonneg hgapLe
    dsimp only [H] at hhold ⊢
    linarith

/-- Sign-free Exit continuation.  Its price is the square of the absolute
stationary-stock lag at the above-saddle endpoint. -/
theorem exists_exitAction_le_prefix_add_absLag_sq
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p)
    {rho b D₀ : ℝ} (hrho : 0 ≤ rho)
    (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    {N : ℕ} (u : Fin N → ℝ)
    (hend : finiteControlledOrbit p rho u N = (b, D₀))
    (hb : b ∈ Ioc weighted.βdagger 1)
    (hD₀ : D₀ ∈ Icc p.I (p.I / p.lambda₀)) :
    ∃ e ∈ quasipotentialActionSet p rho,
      e ≤ gaussianVectorAction u +
        2 * p.c ^ 2 * |p.stationaryStock b - D₀| ^ 2 / p.lambda₀ := by
  let H := controlAction (cancellingHoldControl p rho b D₀)
    (cancellingHoldStop p rho b D₀)
  refine ⟨gaussianVectorAction u + H, ?_, ?_⟩
  · simpa only [H] using
      append_cancellingHoldAction_mem_quasipotentialActionSet
        model ss hrhoCure hcoop weighted u hend hb hD₀
  · have hhold := cancellingHoldAction_le_abs_lag
      model hrho hcoop weighted hb (D₀ := D₀)
    dsimp only [H] at hhold ⊢
    linarith

/-- Complete one-climb continuation from an arbitrary finite prefix.  Starting
from any prefix endpoint below the weighted saddle, append the natural
margin climb and then the sign-free cancelling hold.  The resulting finite
history exits the calibrated basin, and its extra price is the local
barrier-plus-quadratic expression proved above. -/
theorem exists_exitAction_le_prefix_add_oneClimb
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p)
    {rho epsilon L : ℝ} (hrho : 0 ≤ rho)
    (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    {N : ℕ} (u : Fin N → ℝ) {x₀ : LoopState}
    (hend : finiteControlledOrbit p rho u N = x₀)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hstart : x₀.1 ≤ weighted.βdagger) (hepsilon : 0 < epsilon)
    (hroom : p.α * (passageGradientBound p + epsilon) ≤
      1 - weighted.βdagger) :
    let T := marginClimbStopFrom p rho epsilon weighted.βdagger x₀
    let A := (marginClimbPathFrom p rho epsilon x₀ T).1 - x₀.1
    let R := |stationaryStockLag p x₀| +
      driftStationaryStockLipschitzBound p * A
    let H := L * (weighted.βdagger - x₀.1) + epsilon
    ∃ e ∈ quasipotentialActionSet p rho,
      e ≤ gaussianVectorAction u +
        (2 / p.α) *
          (∫ z in x₀.1..weighted.βdagger,
            weightedBarrierIntegrand p rho z) +
        2 * L * H * A +
        (4 * p.c * (1 + p.α * L) / p.lambda₀) *
          (H * R + 2 * p.c * R ^ 2) +
        (epsilon / (2 * p.α)) * A +
        2 * p.c ^ 2 * R ^ 2 / p.lambda₀ := by
  let T := marginClimbStopFrom p rho epsilon weighted.βdagger x₀
  let y := marginClimbPathFrom p rho epsilon x₀ T
  let A := y.1 - x₀.1
  let R := |stationaryStockLag p x₀| +
    driftStationaryStockLipschitzBound p * A
  let H := L * (weighted.βdagger - x₀.1) + epsilon
  let v : Fin T → ℝ := fun i ↦
    marginClimbControlSequenceFrom p rho epsilon x₀ i
  let w : Fin (N + T) → ℝ := Fin.append u v
  have hendpoint : finiteControlledOrbit p rho w (N + T) = y := by
    rw [← finiteControlledOrbitFrom_calibratedPoint]
    rw [show w = Fin.append u v from rfl,
      finiteControlledOrbitFrom_append_right p rho
        (calibratedPoint p) u v le_rfl]
    rw [finiteControlledOrbitFrom_calibratedPoint, hend]
    simpa only [v, y, T] using
      finiteControlledOrbitFrom_marginClimb_eq
        (p := p) (rho := rho) (epsilon := epsilon)
          (target := weighted.βdagger) (x₀ := x₀) le_rfl
  have hyBox : y ∈ absorbingBox p := by
    simpa only [y, T] using
      (marginClimbPathFrom_isControlled p rho epsilon x₀).mem_absorbingBox
        model hx₀ T
  have hyAbove : weighted.βdagger < y.1 := by
    simpa only [y, T] using
      marginClimbStopFrom_crosses
        model hx₀.1 hstart weighted.βdagger_mem.2 hepsilon
  have hyPolicy : y.1 ∈ Ioc weighted.βdagger 1 :=
    ⟨hyAbove, hyBox.1.2⟩
  obtain ⟨e, heMem, heBound⟩ :=
    exists_exitAction_le_prefix_add_absLag_sq
      model ss hrho hrhoCure hcoop weighted w hendpoint
        hyPolicy hyBox.2
  have hwAction : gaussianVectorAction w =
      gaussianVectorAction u +
        controlAction (marginClimbControlSequenceFrom p rho epsilon x₀) T := by
    rw [show w = Fin.append u v from rfl, gaussianVectorAction_append]
    congr 1
    simpa only [v] using
      gaussianVectorAction_restrict
        (marginClimbControlSequenceFrom p rho epsilon x₀) T
  have hclimb := marginClimbPathFrom_action_le_integral_add_quadratic
    model hrho hcoop weighted hL hx₀ hstart hepsilon hroom
  have hmono : Monotone
      (fun n ↦ (marginClimbPathFrom p rho epsilon x₀ n).1) :=
    monotone_marginClimbPolicyFrom model rho epsilon hx₀.1 hepsilon.le
  have hA₀ : 0 ≤ A := by
    dsimp only [A, y]
    simpa only [marginClimbPathFrom_zero] using
      sub_nonneg.mpr (hmono (Nat.zero_le T))
  have hR₀ : 0 ≤ R := by
    dsimp only [R]
    exact add_nonneg (abs_nonneg _)
      (mul_nonneg (driftStationaryStockLipschitzBound_pos model).le hA₀)
  have hlag := marginClimbPathFrom_abs_lag_le_initial_add_advance
    model (rho := rho) hx₀.1 hepsilon.le T
  have hlagR : |stationaryStockLag p y| ≤ R := by
    simpa only [y, R, A, marginClimbPathFrom_zero] using hlag
  have hlagSq : |stationaryStockLag p y| ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) hR₀).2 hlagR
  have hholdScale₀ : 0 ≤ 2 * p.c ^ 2 / p.lambda₀ :=
    div_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg p.c)) model.lambda₀_pos.le
  have hhold : 2 * p.c ^ 2 * |stationaryStockLag p y| ^ 2 /
      p.lambda₀ ≤ 2 * p.c ^ 2 * R ^ 2 / p.lambda₀ := by
    have hscaled := mul_le_mul_of_nonneg_left hlagSq hholdScale₀
    calc
      2 * p.c ^ 2 * |stationaryStockLag p y| ^ 2 / p.lambda₀ =
          (2 * p.c ^ 2 / p.lambda₀) *
            |stationaryStockLag p y| ^ 2 := by ring
      _ ≤ (2 * p.c ^ 2 / p.lambda₀) * R ^ 2 := hscaled
      _ = 2 * p.c ^ 2 * R ^ 2 / p.lambda₀ := by ring
  refine ⟨e, heMem, ?_⟩
  rw [hwAction] at heBound
  have heBound' : e ≤ gaussianVectorAction u +
      controlAction (marginClimbControlSequenceFrom p rho epsilon x₀) T +
        2 * p.c ^ 2 * |stationaryStockLag p y| ^ 2 / p.lambda₀ := by
    simpa only [y, T, stationaryStockLag, marginClimbPathFrom] using heBound
  have hclimb' :
      controlAction (marginClimbControlSequenceFrom p rho epsilon x₀) T ≤
        (2 / p.α) *
            (∫ z in x₀.1..weighted.βdagger,
              weightedBarrierIntegrand p rho z) +
          2 * L * H * A +
          (4 * p.c * (1 + p.α * L) / p.lambda₀) *
            (H * R + 2 * p.c * R ^ 2) +
          (epsilon / (2 * p.α)) * A := by
    simpa only [T, A, R, H, y] using hclimb
  have hfinal : e ≤ gaussianVectorAction u +
      (2 / p.α) *
          (∫ z in x₀.1..weighted.βdagger,
            weightedBarrierIntegrand p rho z) +
        2 * L * H * A +
        (4 * p.c * (1 + p.α * L) / p.lambda₀) *
          (H * R + 2 * p.c * R ^ 2) +
        (epsilon / (2 * p.α)) * A +
        2 * p.c ^ 2 * R ^ 2 / p.lambda₀ := by
    linarith
  simpa only [T, A, R, H, y] using hfinal

/-! ## Coupled barrier/mesh ledger -/

/-- Finite control action is monotone in its horizon. -/
theorem controlAction_mono {u : ℕ → ℝ} {m n : ℕ} (hmn : m ≤ n) :
    controlAction u m ≤ controlAction u n := by
  unfold controlAction
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
    fun i _hi _him ↦ sq_nonneg (u i)

/-- A longer horizon pays a prefix and the prefix's next control summand. -/
theorem controlAction_add_next_le {u : ℕ → ℝ} {n N : ℕ} (hn : n < N) :
    controlAction u n + (u n) ^ 2 / 2 ≤ controlAction u N := by
  have hsucc : n + 1 ≤ N := Nat.succ_le_iff.mpr hn
  have heq : controlAction u (n + 1) =
      controlAction u n + (u n) ^ 2 / 2 := by
    simp only [controlAction, Finset.sum_range_succ]
    ring
  rw [← heq]
  exact controlAction_mono hsucc

/-- Optimal scalar coefficient for keeping the barrier work and Lipschitz
mesh error coupled in a single advancing cell. -/
def coupledCellFactor (t : ℝ) : ℝ :=
  if t ≤ 1 then 2 - t else 1 / t

/-- On the small-mesh branch, the coupled refund coefficient is exactly
`2 / alpha - L`. -/
theorem coupledCellFactor_div_eq_two_div_sub
    {alpha L : ℝ} (halpha : 0 < alpha) (hsmall : alpha * L ≤ 1) :
    coupledCellFactor (alpha * L) / alpha = 2 / alpha - L := by
  simp only [coupledCellFactor, if_pos hsmall]
  field_simp [halpha.ne']

/-- The coupled cell factor is positive for every nonnegative mesh
parameter. -/
theorem coupledCellFactor_pos (t : ℝ) :
    0 < coupledCellFactor t := by
  rw [coupledCellFactor]
  split_ifs with h
  · linarith
  · have htOne : 1 < t := lt_of_not_ge h
    exact one_div_pos.mpr (zero_lt_one.trans htOne)

/-- The coupled cell factor strictly improves the coefficient used by the
separated barrier/mesh estimate whenever the mesh parameter is positive. -/
theorem correctedCellFactor_lt_coupledCellFactor
    {t : ℝ} (ht : 0 < t) :
    2 / (1 + 2 * t) < coupledCellFactor t := by
  have hden : 0 < 1 + 2 * t := by positivity
  rw [coupledCellFactor]
  split_ifs with h
  · have htOne : t ≤ 1 := h
    apply (div_lt_iff₀ hden).2
    have hprod : 0 < t * (3 - 2 * t) :=
      mul_pos ht (by linarith)
    nlinarith
  · have htOne : 1 < t := lt_of_not_ge h
    have htpos : 0 < t := htOne.trans' zero_lt_one
    rw [div_lt_div_iff₀ hden htpos]
    linarith

/-- Scalar heart of the coupled cell estimate.  For `t = alpha L`, the
quantity in parentheses is the left barrier rectangle plus its quadratic
Lipschitz error after dividing by `alpha`. -/
theorem coupledCellFactor_mul_le_half_sq
    {t a d u : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hu : a + d ≤ u) :
    coupledCellFactor t * (a * d + (t / 2) * d ^ 2) ≤ u ^ 2 / 2 := by
  have hsum : 0 ≤ a + d := add_nonneg ha hd
  have huNonneg : 0 ≤ u := hsum.trans hu
  have hsquare : (a + d) ^ 2 ≤ u ^ 2 :=
    (sq_le_sq₀ hsum huNonneg).2 hu
  rw [coupledCellFactor]
  split_ifs with h
  · have hcore := sq_nonneg (a - (1 - t) * d)
    nlinarith
  · have htOne : 1 < t := lt_of_not_ge h
    have htpos : 0 < t := zero_lt_one.trans htOne
    have hnonneg : 0 ≤ (t / 2) * a ^ 2 + (t - 1) * a * d := by
      exact add_nonneg
        (mul_nonneg (div_nonneg htpos.le (by norm_num)) (sq_nonneg a))
        (mul_nonneg (mul_nonneg (sub_nonneg.mpr htOne.le) ha) hd)
    have hscaled :
        a * d + (t / 2) * d ^ 2 ≤ t * ((a + d) ^ 2 / 2) := by
      nlinarith
    have hdiv :
        (1 / t) * (a * d + (t / 2) * d ^ 2) ≤ (a + d) ^ 2 / 2 := by
      rw [one_div, inv_mul_eq_div]
      exact (div_le_iff₀ htpos).2 (by simpa only [mul_comm] using hscaled)
    exact hdiv.trans (by nlinarith)

/-- On the small-mesh branch, the coupled cell ledger leaves an exact square
of slack.  This residual pays for a selected cell which overleaps the local
saddle window. -/
theorem coupledCellFactor_mul_add_residual_le_half_sq
    {t a d u : ℝ} (ht : t ≤ 1) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hu : a + d ≤ u) :
    coupledCellFactor t * (a * d + (t / 2) * d ^ 2) +
        (a - (1 - t) * d) ^ 2 / 2 ≤ u ^ 2 / 2 := by
  have hsum : 0 ≤ a + d := add_nonneg ha hd
  have huNonneg : 0 ≤ u := hsum.trans hu
  have hsquare : (a + d) ^ 2 ≤ u ^ 2 :=
    (sq_le_sq₀ hsum huNonneg).2 hu
  simp only [coupledCellFactor, if_pos ht]
  nlinarith only [hsquare]

/-! ## Deficit-refined localized ledger -/

/-- The complete non-barrier burden of an advancing stopped-maximum cell.
The first term prices stock deficit at the old level; the second prices a
retreat of the current policy below that level. -/
def passageCellBurden
    (p : LoopParams) (rho b beta D : ℝ) : ℝ :=
  (2 * p.c * (1 - p.c * b) - rho) *
      (p.stationaryStock b - D) +
    (1 / p.α - 2 * p.c ^ 2 * D) * (b - beta)

/-- Exact square-root residual left by the small-mesh coupled ledger in one
advancing cell. -/
def passageCellResidual
    (p : LoopParams) (rho L b b' beta D : ℝ) : ℝ :=
  weightedBarrierIntegrand p rho b + passageCellBurden p rho b beta D -
    (1 - p.α * L) * ((b' - b) / p.α)

/-- A strengthened small-step inequality leaves half of the inverse-rate
coefficient available to price retreat. -/
theorem half_inv_le_retreatCoefficient_of_four_alpha_c_sq_I_le_lambda
    {p : LoopParams} (model : DriftModelAssumptions p)
    {D : ℝ} (hfour : 4 * p.α * p.c ^ 2 * p.I ≤ p.lambda₀)
    (hD : D ≤ p.I / p.lambda₀) :
    1 / (2 * p.α) ≤ 1 / p.α - 2 * p.c ^ 2 * D := by
  have hscale : 0 ≤ 4 * p.α * p.c ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) (sq_nonneg p.c)
  have hDscaled :
      4 * p.α * p.c ^ 2 * D ≤
        4 * p.α * p.c ^ 2 * (p.I / p.lambda₀) :=
    mul_le_mul_of_nonneg_left hD hscale
  have hceiling :
      4 * p.α * p.c ^ 2 * (p.I / p.lambda₀) ≤ 1 := by
    calc
      4 * p.α * p.c ^ 2 * (p.I / p.lambda₀) =
          (4 * p.α * p.c ^ 2 * p.I) / p.lambda₀ := by ring
      _ ≤ 1 := (div_le_iff₀ model.lambda₀_pos).2 (by
        simpa only [one_mul] using hfour)
  have hfourD : 4 * p.α * p.c ^ 2 * D ≤ 1 :=
    hDscaled.trans hceiling
  rw [le_sub_iff_add_le]
  apply (le_div_iff₀ model.α_pos).2
  have hinv : (1 / (2 * p.α)) * p.α = 1 / 2 := by
    field_simp [model.α_pos.ne']
  rw [add_mul, hinv]
  nlinarith

/-- Paper II, Proposition `prop:passage`, exact advancing-cell budget.  If
the current policy has retreated below its stopped running maximum, the
control must also repay that retreat; the cell burden carries the term
explicitly. -/
theorem IsControlledCivicWeightedPathFrom.control_ge_flooredBarrier_burden_add_advance
    {p : LoopParams} {rho floor : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p)
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hfloor : floor ∈ Icc (0 : ℝ) weighted.βdagger) {n : ℕ}
    (hadvance :
      flooredCappedPolicyRunningMax floor weighted.βdagger x n <
        flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1)) :
    weightedBarrierIntegrand p rho
        (flooredCappedPolicyRunningMax floor weighted.βdagger x n) +
      passageCellBurden p rho
        (flooredCappedPolicyRunningMax floor weighted.βdagger x n)
        (x n).1 (x n).2 +
      (flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1) -
        flooredCappedPolicyRunningMax floor weighted.βdagger x n) / p.α ≤
      u n := by
  let b := flooredCappedPolicyRunningMax floor weighted.βdagger x n
  let b' := flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1)
  let beta := (x n).1
  let D := (x n).2
  let A := 2 * p.c * (1 - p.c * b) - rho
  obtain ⟨_hold, _hbetaB, hnewPolicy⟩ :=
    flooredCappedRunningMax_advance_structure hadvance
  have hbsegment := path.flooredCappedRunningMax_mem
    weighted hx₀.1 hfloor n
  have hbmem : b ∈ Icc (0 : ℝ) 1 :=
    ⟨hfloor.1.trans hbsegment.1,
      hbsegment.2.trans weighted.βdagger_mem.2.le⟩
  have hbnonneg : 0 ≤ b := hbmem.1
  have hb'pos : 0 < b' := hbnonneg.trans_lt hadvance
  have hxnextPos : 0 < (x (n + 1)).1 := hb'pos.trans_le hnewPolicy
  have hxnext : (x (n + 1)).1 = LoopParams.clipUnit
      (beta + p.α * (civicWeightedGradient p rho beta D + u n)) := by
    have hstep := congrArg Prod.fst (path.step n)
    simpa only [controlledCivicWeightedStep] using hstep
  have hinput : b' ≤ beta + p.α *
      (civicWeightedGradient p rho beta D + u n) := by
    calc
      b' ≤ (x (n + 1)).1 := hnewPolicy
      _ = LoopParams.clipUnit
          (beta + p.α * (civicWeightedGradient p rho beta D + u n)) := hxnext
      _ ≤ beta + p.α * (civicWeightedGradient p rho beta D + u n) :=
        clipUnit_le_input_of_pos (by rwa [← hxnext])
  have hgradientEq : civicWeightedGradient p rho beta D =
      weightedStationaryGradient p rho b -
        A * (p.stationaryStock b - D) +
          2 * p.c ^ 2 * D * (b - beta) := by
    rw [← civicWeightedGradient_stationary_eq_weightedStationaryGradient rho hbmem]
    simp only [civicWeightedGradient, LoopParams.gradU]
    dsimp only [A]
    ring
  have hinputSlack :
      0 ≤ p.α * (civicWeightedGradient p rho beta D + u n) -
        (b' - beta) := by
    linarith
  have hslackIdentity :
      p.α * u n -
          (p.α * (weightedBarrierIntegrand p rho b +
            A * (p.stationaryStock b - D)) + (b' - b)) =
        (p.α * (civicWeightedGradient p rho beta D + u n) -
          (b' - beta)) +
          (1 - 2 * p.α * p.c ^ 2 * D) * (b - beta) := by
    rw [hgradientEq]
    simp only [weightedBarrierIntegrand]
    ring
  have hdivide : p.α * ((b' - b) / p.α) = b' - b := by
    field_simp [model.α_pos.ne']
  have hinv : p.α * (1 / p.α - 2 * p.c ^ 2 * D) =
      1 - 2 * p.α * p.c ^ 2 * D := by
    field_simp [model.α_pos.ne']
  simp only [passageCellBurden]
  dsimp only [b, b', beta, D, A] at hinputSlack hslackIdentity hdivide hinv ⊢
  nlinarith [model.α_pos]

/-- Under `(SS)`, both parts of the complete advancing-cell burden are
nonnegative. -/
theorem IsControlledCivicWeightedPathFrom.passageCellBurden_nonneg_of_advance
    {p : LoopParams} {rho floor : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hfloor : floor ∈ Icc (0 : ℝ) weighted.βdagger)
    (hstart : x₀.1 ≤ floor)
    (hstock₀ : x₀.2 ≤ p.stationaryStock floor) {n : ℕ}
    (hadvance :
      flooredCappedPolicyRunningMax floor weighted.βdagger x n <
        flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1)) :
    0 ≤ passageCellBurden p rho
      (flooredCappedPolicyRunningMax floor weighted.βdagger x n)
      (x n).1 (x n).2 := by
  let b := flooredCappedPolicyRunningMax floor weighted.βdagger x n
  let beta := (x n).1
  let D := (x n).2
  obtain ⟨hold, hbetaB, _hnewPolicy⟩ :=
    flooredCappedRunningMax_advance_structure hadvance
  have hfloorUnit : floor ∈ Icc (0 : ℝ) 1 :=
    ⟨hfloor.1, hfloor.2.trans weighted.βdagger_mem.2.le⟩
  have hbsegment := path.flooredCappedRunningMax_mem
    weighted hx₀.1 hfloor n
  have hbmem : b ∈ Icc (0 : ℝ) 1 :=
    ⟨hfloor.1.trans hbsegment.1,
      hbsegment.2.trans weighted.βdagger_mem.2.le⟩
  have hstock := path.stock_le_stationary_flooredRunningMax
    model ss hx₀ hfloorUnit hstart hstock₀ n
  rw [← hold] at hstock
  have htheta : 0 ≤ p.stationaryStock b - D := by
    simpa only [b, D] using sub_nonneg.mpr hstock
  have hA : 0 ≤ 2 * p.c * (1 - p.c * b) - rho :=
    weighted_stock_coefficient_nonnegative model hcoop hbmem
  have hsmall := two_alpha_c_sq_stationaryStock_le_one model ss hbmem
  have hscale : 0 ≤ 2 * p.α * p.c ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) (sq_nonneg p.c)
  have hsmallD : 2 * p.α * p.c ^ 2 * D ≤ 1 :=
    (mul_le_mul_of_nonneg_left hstock hscale).trans hsmall
  have hdip : 0 ≤ b - beta := sub_nonneg.mpr hbetaB
  have hdipProduct :
      0 ≤ (1 - 2 * p.α * p.c ^ 2 * D) * (b - beta) :=
    mul_nonneg (sub_nonneg.mpr hsmallD) hdip
  have hdipScaled :
      0 ≤ (1 / p.α - 2 * p.c ^ 2 * D) * (b - beta) := by
    have hrewrite :
        (1 / p.α - 2 * p.c ^ 2 * D) * (b - beta) =
          ((1 - 2 * p.α * p.c ^ 2 * D) * (b - beta)) / p.α := by
      field_simp [model.α_pos.ne']
    rw [hrewrite]
    exact div_nonneg hdipProduct model.α_pos.le
  simp only [passageCellBurden]
  dsimp only [b, beta, D] at htheta hA hdipScaled ⊢
  exact add_nonneg (mul_nonneg hA htheta) hdipScaled

/-- With half-step room, the complete burden quantitatively controls both
the old-level stock deficit and the retreat depth. -/
theorem IsControlledCivicWeightedPathFrom.deficit_add_halfRetreat_le_passageCellBurden
    {p : LoopParams} {rho floor : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hfloor : floor ∈ Icc (0 : ℝ) weighted.βdagger)
    (hstart : x₀.1 ≤ floor)
    (hstock₀ : x₀.2 ≤ p.stationaryStock floor)
    (hfour : 4 * p.α * p.c ^ 2 * p.I ≤ p.lambda₀) {n : ℕ}
    (hadvance :
      flooredCappedPolicyRunningMax floor weighted.βdagger x n <
        flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1)) :
    (2 * p.c * (1 - p.c * weighted.βdagger) - rho) *
          (p.stationaryStock
              (flooredCappedPolicyRunningMax floor weighted.βdagger x n) -
            (x n).2) +
        (1 / (2 * p.α)) *
          (flooredCappedPolicyRunningMax floor weighted.βdagger x n -
            (x n).1) ≤
      passageCellBurden p rho
        (flooredCappedPolicyRunningMax floor weighted.βdagger x n)
        (x n).1 (x n).2 := by
  let b := flooredCappedPolicyRunningMax floor weighted.βdagger x n
  let beta := (x n).1
  let D := (x n).2
  obtain ⟨hold, hbetaB, _hnewPolicy⟩ :=
    flooredCappedRunningMax_advance_structure hadvance
  have hfloorUnit : floor ∈ Icc (0 : ℝ) 1 :=
    ⟨hfloor.1, hfloor.2.trans weighted.βdagger_mem.2.le⟩
  have hbsegment := path.flooredCappedRunningMax_mem
    weighted hx₀.1 hfloor n
  have hbmem : b ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨hfloor.1.trans hbsegment.1, hbsegment.2⟩
  have hbUnit : b ∈ Icc (0 : ℝ) 1 :=
    ⟨hbmem.1, hbmem.2.trans weighted.βdagger_mem.2.le⟩
  have hstock := path.stock_le_stationary_flooredRunningMax
    model ss hx₀ hfloorUnit hstart hstock₀ n
  rw [← hold] at hstock
  have htheta : 0 ≤ p.stationaryStock b - D := by
    simpa only [b, D] using sub_nonneg.mpr hstock
  have hDceiling : D ≤ p.I / p.lambda₀ :=
    hstock.trans (stationaryStock_mem_stockInterval model hbUnit).2
  have hcoefficient :
      2 * p.c * (1 - p.c * weighted.βdagger) - rho ≤
        2 * p.c * (1 - p.c * b) - rho := by
    have hproduct : 0 ≤ 2 * p.c ^ 2 * (weighted.βdagger - b) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg p.c))
        (sub_nonneg.mpr hbmem.2)
    nlinarith
  have hfirst := mul_le_mul_of_nonneg_right hcoefficient htheta
  have hdip : 0 ≤ b - beta := sub_nonneg.mpr hbetaB
  have hretreat :=
    half_inv_le_retreatCoefficient_of_four_alpha_c_sq_I_le_lambda
      model hfour hDceiling
  have hsecond := mul_le_mul_of_nonneg_right hretreat hdip
  simp only [passageCellBurden]
  dsimp only [b, beta, D] at hfirst hsecond ⊢
  linarith

/-- Paper II, Proposition `prop:passage`, level-budget step.  On an advance
of the floored stopped maximum, control pays not only the stationary barrier
and the policy increment but also the exact stock deficit at the old level.
The usual dip term from a temporarily lower current policy is absorbed by
`(SS)`. -/
theorem IsControlledCivicWeightedPathFrom.control_ge_flooredBarrier_deficit_add_advance
    {p : LoopParams} {rho floor : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (_hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hfloor : floor ∈ Icc (0 : ℝ) weighted.βdagger)
    (hstart : x₀.1 ≤ floor)
    (hstock₀ : x₀.2 ≤ p.stationaryStock floor) {n : ℕ}
    (hadvance :
      flooredCappedPolicyRunningMax floor weighted.βdagger x n <
        flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1)) :
    weightedBarrierIntegrand p rho
        (flooredCappedPolicyRunningMax floor weighted.βdagger x n) +
      (2 * p.c *
          (1 - p.c *
            flooredCappedPolicyRunningMax floor weighted.βdagger x n) - rho) *
        (p.stationaryStock
            (flooredCappedPolicyRunningMax floor weighted.βdagger x n) -
          (x n).2) +
    (flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1) -
        flooredCappedPolicyRunningMax floor weighted.βdagger x n) / p.α ≤
      u n := by
  let b := flooredCappedPolicyRunningMax floor weighted.βdagger x n
  let beta := (x n).1
  let D := (x n).2
  obtain ⟨hold, hbetaB, _hnewPolicy⟩ :=
    flooredCappedRunningMax_advance_structure hadvance
  have hfloorUnit : floor ∈ Icc (0 : ℝ) 1 :=
    ⟨hfloor.1, hfloor.2.trans weighted.βdagger_mem.2.le⟩
  have hbsegment := path.flooredCappedRunningMax_mem
    weighted hx₀.1 hfloor n
  have hbmem : b ∈ Icc (0 : ℝ) 1 :=
    ⟨hfloor.1.trans hbsegment.1,
      hbsegment.2.trans weighted.βdagger_mem.2.le⟩
  have hstock := path.stock_le_stationary_flooredRunningMax
    model ss hx₀ hfloorUnit hstart hstock₀ n
  rw [← hold] at hstock
  have hsmall := two_alpha_c_sq_stationaryStock_le_one model ss hbmem
  have hscale : 0 ≤ 2 * p.α * p.c ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) (sq_nonneg p.c)
  have hsmallD : 2 * p.α * p.c ^ 2 * D ≤ 1 :=
    (mul_le_mul_of_nonneg_left hstock hscale).trans hsmall
  have hdip : 0 ≤ b - beta := sub_nonneg.mpr hbetaB
  have hdipProduct :
      0 ≤ (1 - 2 * p.α * p.c ^ 2 * D) * (b - beta) :=
    mul_nonneg (sub_nonneg.mpr hsmallD) hdip
  have hstrong := path.control_ge_flooredBarrier_burden_add_advance
    model weighted hx₀ hfloor hadvance
  have hdipScaled :
      0 ≤ (1 / p.α - 2 * p.c ^ 2 * D) * (b - beta) := by
    have hrewrite :
        (1 / p.α - 2 * p.c ^ 2 * D) * (b - beta) =
          ((1 - 2 * p.α * p.c ^ 2 * D) * (b - beta)) / p.α := by
      field_simp [model.α_pos.ne']
    rw [hrewrite]
    exact div_nonneg hdipProduct model.α_pos.le
  simp only [passageCellBurden] at hstrong
  dsimp only [b, beta, D] at hstrong hdipScaled ⊢
  linarith

/-- Paper II, Proposition `prop:passage`, burden-aware one-cell budget.  It
retains both the old-level stock deficit and the current-policy retreat that
the truncation state must control. -/
theorem IsControlledCivicWeightedPathFrom.floored_coupled_burden_cell_le_half_control_sq
    {p : LoopParams} {rho floor L : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hfloor : floor ∈ Icc (0 : ℝ) weighted.βdagger)
    (hstart : x₀.1 ≤ floor)
    (hstock₀ : x₀.2 ≤ p.stationaryStock floor) (n : ℕ) :
    (coupledCellFactor (p.α * L) / p.α) *
        ((∫ z in
            flooredCappedPolicyRunningMax floor weighted.βdagger x n..
            flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1),
            weightedBarrierIntegrand p rho z) +
          passageCellBurden p rho
              (flooredCappedPolicyRunningMax floor weighted.βdagger x n)
              (x n).1 (x n).2 *
            (flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1) -
              flooredCappedPolicyRunningMax floor weighted.βdagger x n)) ≤
      (u n) ^ 2 / 2 := by
  let b := flooredCappedPolicyRunningMax floor weighted.βdagger x n
  let b' := flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1)
  let q := passageCellBurden p rho b (x n).1 (x n).2
  let a := weightedBarrierIntegrand p rho b + q
  let d := (b' - b) / p.α
  let t := p.α * L
  have hbsegment := path.flooredCappedRunningMax_mem
    weighted hx₀.1 hfloor n
  have hb'segment := path.flooredCappedRunningMax_mem
    weighted hx₀.1 hfloor (n + 1)
  have hbmem : b ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨hfloor.1.trans hbsegment.1, hbsegment.2⟩
  have hb'mem : b' ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨hfloor.1.trans hb'segment.1, hb'segment.2⟩
  have hmono : b ≤ b' :=
    monotone_flooredCappedPolicyRunningMax
      floor weighted.βdagger x n.le_succ
  rcases hmono.lt_or_eq with hadvance | heq
  · have hq : 0 ≤ q := by
      simpa only [q, b] using
        path.passageCellBurden_nonneg_of_advance
          model ss hcoop weighted hx₀ hfloor hstart hstock₀ hadvance
    have hbarrier : 0 < weightedBarrierIntegrand p rho b :=
      weighted.barrier_pos_before hbmem
        (hadvance.trans_le (min_le_left _ _))
    have ha : 0 ≤ a := by
      dsimp only [a]
      exact add_nonneg hbarrier.le hq
    have hd : 0 ≤ d :=
      div_nonneg (sub_nonneg.mpr hmono) model.α_pos.le
    have hu := path.control_ge_flooredBarrier_burden_add_advance
      model weighted hx₀ hfloor hadvance
    have hu' : a + d ≤ u n := by
      simpa only [a, d, q, b, b'] using hu
    have hcell := integral_le_left_rectangle_add_lipschitz
      (continuousOn_weightedBarrierIntegrand model rho weighted) hL
      hbmem hb'mem hmono
    have hcellTotal :
        (∫ z in b..b', weightedBarrierIntegrand p rho z) +
            q * (b' - b) ≤
          p.α * (a * d + (t / 2) * d ^ 2) := by
      calc
        (∫ z in b..b', weightedBarrierIntegrand p rho z) +
              q * (b' - b) ≤
            (weightedBarrierIntegrand p rho b * (b' - b) +
              (L / 2) * (b' - b) ^ 2) + q * (b' - b) :=
          add_le_add_left hcell _
        _ = p.α * (a * d + (t / 2) * d ^ 2) := by
          dsimp only [a, d, t]
          field_simp [model.α_pos.ne']
          ring
    have hfactor : 0 < coupledCellFactor t := coupledCellFactor_pos t
    have hscale : 0 ≤ coupledCellFactor t / p.α :=
      (div_pos hfactor model.α_pos).le
    have hscaled := mul_le_mul_of_nonneg_left hcellTotal hscale
    have hscaledEq :
        (coupledCellFactor t / p.α) *
            (p.α * (a * d + (t / 2) * d ^ 2)) =
          coupledCellFactor t * (a * d + (t / 2) * d ^ 2) := by
      field_simp [model.α_pos.ne']
    rw [hscaledEq] at hscaled
    have hcore := coupledCellFactor_mul_le_half_sq
      (t := t) (u := u n) ha hd hu'
    exact hscaled.trans hcore
  · have heqRaw :
        flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1) =
          flooredCappedPolicyRunningMax floor weighted.βdagger x n := by
      simpa only [b, b'] using heq.symm
    rw [heqRaw, intervalIntegral.integral_same, sub_self, mul_zero, add_zero]
    simpa only [mul_zero] using
      (div_nonneg (sq_nonneg (u n)) (by norm_num : (0 : ℝ) ≤ 2))

/-- Strengthened advancing-cell ledger on the small-mesh branch.  In
addition to the barrier and complete burden, it retains the exact residual
square which is discarded by the ordinary coupled estimate. -/
theorem IsControlledCivicWeightedPathFrom.floored_coupled_burden_cell_add_residual_le
    {p : LoopParams} {rho floor L : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hfloor : floor ∈ Icc (0 : ℝ) weighted.βdagger)
    (hstart : x₀.1 ≤ floor)
    (hstock₀ : x₀.2 ≤ p.stationaryStock floor) {n : ℕ}
    (hsmall : p.α * L ≤ 1)
    (hadvance :
      flooredCappedPolicyRunningMax floor weighted.βdagger x n <
        flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1)) :
    (coupledCellFactor (p.α * L) / p.α) *
        ((∫ z in
            flooredCappedPolicyRunningMax floor weighted.βdagger x n..
            flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1),
            weightedBarrierIntegrand p rho z) +
          passageCellBurden p rho
              (flooredCappedPolicyRunningMax floor weighted.βdagger x n)
              (x n).1 (x n).2 *
            (flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1) -
              flooredCappedPolicyRunningMax floor weighted.βdagger x n)) +
      passageCellResidual p rho L
          (flooredCappedPolicyRunningMax floor weighted.βdagger x n)
          (flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1))
          (x n).1 (x n).2 ^ 2 / 2 ≤
        (u n) ^ 2 / 2 := by
  let b := flooredCappedPolicyRunningMax floor weighted.βdagger x n
  let b' := flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1)
  let q := passageCellBurden p rho b (x n).1 (x n).2
  let a := weightedBarrierIntegrand p rho b + q
  let d := (b' - b) / p.α
  let t := p.α * L
  have hbsegment := path.flooredCappedRunningMax_mem
    weighted hx₀.1 hfloor n
  have hb'segment := path.flooredCappedRunningMax_mem
    weighted hx₀.1 hfloor (n + 1)
  have hbmem : b ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨hfloor.1.trans hbsegment.1, hbsegment.2⟩
  have hb'mem : b' ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨hfloor.1.trans hb'segment.1, hb'segment.2⟩
  have hmono : b ≤ b' := hadvance.le
  have hq : 0 ≤ q := by
    simpa only [q, b] using
      path.passageCellBurden_nonneg_of_advance
        model ss hcoop weighted hx₀ hfloor hstart hstock₀ hadvance
  have hbarrier : 0 < weightedBarrierIntegrand p rho b :=
    weighted.barrier_pos_before hbmem
      (hadvance.trans_le (min_le_left _ _))
  have ha : 0 ≤ a := by
    dsimp only [a]
    exact add_nonneg hbarrier.le hq
  have hd : 0 ≤ d :=
    div_nonneg (sub_nonneg.mpr hmono) model.α_pos.le
  have hu := path.control_ge_flooredBarrier_burden_add_advance
    model weighted hx₀ hfloor hadvance
  have hu' : a + d ≤ u n := by
    simpa only [a, d, q, b, b'] using hu
  have hcell := integral_le_left_rectangle_add_lipschitz
    (continuousOn_weightedBarrierIntegrand model rho weighted) hL
    hbmem hb'mem hmono
  have hcellTotal :
      (∫ z in b..b', weightedBarrierIntegrand p rho z) +
          q * (b' - b) ≤
        p.α * (a * d + (t / 2) * d ^ 2) := by
    calc
      (∫ z in b..b', weightedBarrierIntegrand p rho z) +
            q * (b' - b) ≤
          (weightedBarrierIntegrand p rho b * (b' - b) +
            (L / 2) * (b' - b) ^ 2) + q * (b' - b) :=
        add_le_add_left hcell _
      _ = p.α * (a * d + (t / 2) * d ^ 2) := by
        dsimp only [a, d, t]
        field_simp [model.α_pos.ne']
        ring
  have hscale : 0 ≤ coupledCellFactor t / p.α :=
    (div_pos (coupledCellFactor_pos t) model.α_pos).le
  have hscaled := mul_le_mul_of_nonneg_left hcellTotal hscale
  have hscaledEq :
      (coupledCellFactor t / p.α) *
          (p.α * (a * d + (t / 2) * d ^ 2)) =
        coupledCellFactor t * (a * d + (t / 2) * d ^ 2) := by
    field_simp [model.α_pos.ne']
  rw [hscaledEq] at hscaled
  have hcore := coupledCellFactor_mul_add_residual_le_half_sq
    (t := t) (u := u n) (by simpa only [t] using hsmall) ha hd hu'
  have hsum := add_le_add hscaled
    (le_refl ((a - (1 - t) * d) ^ 2 / 2))
  have hresult :
      (coupledCellFactor t / p.α) *
          ((∫ z in b..b', weightedBarrierIntegrand p rho z) +
            q * (b' - b)) +
        (a - (1 - t) * d) ^ 2 / 2 ≤ (u n) ^ 2 / 2 :=
    hsum.trans hcore
  simpa only [b, b', q, a, d, t, passageCellResidual] using hresult

/-- Paper II, Proposition `prop:passage`, one-cell level budget.  The
coupled coefficient simultaneously pays the barrier integral, its Lipschitz
mesh correction, and the stock-deficit charge. -/
theorem IsControlledCivicWeightedPathFrom.floored_coupled_deficit_cell_le_half_control_sq
    {p : LoopParams} {rho floor L : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hfloor : floor ∈ Icc (0 : ℝ) weighted.βdagger)
    (hstart : x₀.1 ≤ floor)
    (hstock₀ : x₀.2 ≤ p.stationaryStock floor) (n : ℕ) :
    (coupledCellFactor (p.α * L) / p.α) *
        ((∫ z in
            flooredCappedPolicyRunningMax floor weighted.βdagger x n..
            flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1),
            weightedBarrierIntegrand p rho z) +
          (2 * p.c *
              (1 - p.c *
                flooredCappedPolicyRunningMax floor weighted.βdagger x n) - rho) *
            (p.stationaryStock
                (flooredCappedPolicyRunningMax floor weighted.βdagger x n) -
              (x n).2) *
            (flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1) -
              flooredCappedPolicyRunningMax floor weighted.βdagger x n)) ≤
      (u n) ^ 2 / 2 := by
  let b := flooredCappedPolicyRunningMax floor weighted.βdagger x n
  let b' := flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1)
  let A := 2 * p.c * (1 - p.c * b) - rho
  let theta := p.stationaryStock b - (x n).2
  let a := weightedBarrierIntegrand p rho b + A * theta
  let d := (b' - b) / p.α
  let t := p.α * L
  have hbsegment := path.flooredCappedRunningMax_mem
    weighted hx₀.1 hfloor n
  have hb'segment := path.flooredCappedRunningMax_mem
    weighted hx₀.1 hfloor (n + 1)
  have hbmem : b ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨hfloor.1.trans hbsegment.1, hbsegment.2⟩
  have hb'mem : b' ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨hfloor.1.trans hb'segment.1, hb'segment.2⟩
  have hmono : b ≤ b' :=
    monotone_flooredCappedPolicyRunningMax
      floor weighted.βdagger x n.le_succ
  rcases hmono.lt_or_eq with hadvance | heq
  · obtain ⟨hold, _hbetaB, _hnewPolicy⟩ :=
      flooredCappedRunningMax_advance_structure hadvance
    have hfloorUnit : floor ∈ Icc (0 : ℝ) 1 :=
      ⟨hfloor.1, hfloor.2.trans weighted.βdagger_mem.2.le⟩
    have hstock := path.stock_le_stationary_flooredRunningMax
      model ss hx₀ hfloorUnit hstart hstock₀ n
    rw [← hold] at hstock
    have htheta : 0 ≤ theta := by
      simpa only [theta] using sub_nonneg.mpr hstock
    have hbUnit : b ∈ Icc (0 : ℝ) 1 :=
      ⟨hbmem.1, hbmem.2.trans weighted.βdagger_mem.2.le⟩
    have hA : 0 ≤ A := by
      simpa only [A] using
        weighted_stock_coefficient_nonnegative model hcoop hbUnit
    have hbarrier : 0 < weightedBarrierIntegrand p rho b :=
      weighted.barrier_pos_before hbmem
        (hadvance.trans_le (min_le_left _ _))
    have ha : 0 ≤ a := by
      dsimp only [a]
      exact add_nonneg hbarrier.le (mul_nonneg hA htheta)
    have hd : 0 ≤ d :=
      div_nonneg (sub_nonneg.mpr hmono) model.α_pos.le
    have hu := path.control_ge_flooredBarrier_deficit_add_advance
      model ss hcoop weighted hx₀ hfloor hstart hstock₀ hadvance
    have hu' : a + d ≤ u n := by
      simpa only [a, d, A, theta, b, b'] using hu
    have hcell := integral_le_left_rectangle_add_lipschitz
      (continuousOn_weightedBarrierIntegrand model rho weighted) hL
      hbmem hb'mem hmono
    have hcellTotal :
        (∫ z in b..b', weightedBarrierIntegrand p rho z) +
            A * theta * (b' - b) ≤
          p.α * (a * d + (t / 2) * d ^ 2) := by
      calc
        (∫ z in b..b', weightedBarrierIntegrand p rho z) +
              A * theta * (b' - b) ≤
            (weightedBarrierIntegrand p rho b * (b' - b) +
              (L / 2) * (b' - b) ^ 2) +
                A * theta * (b' - b) := add_le_add_left hcell _
        _ = p.α * (a * d + (t / 2) * d ^ 2) := by
          dsimp only [a, d, t]
          field_simp [model.α_pos.ne']
          ring
    have hfactor : 0 < coupledCellFactor t := coupledCellFactor_pos t
    have hscale : 0 ≤ coupledCellFactor t / p.α :=
      (div_pos hfactor model.α_pos).le
    have hscaled := mul_le_mul_of_nonneg_left hcellTotal hscale
    have hscaledEq :
        (coupledCellFactor t / p.α) *
            (p.α * (a * d + (t / 2) * d ^ 2)) =
          coupledCellFactor t * (a * d + (t / 2) * d ^ 2) := by
      field_simp [model.α_pos.ne']
    rw [hscaledEq] at hscaled
    have hcore := coupledCellFactor_mul_le_half_sq
      (t := t) (u := u n) ha hd hu'
    exact hscaled.trans hcore
  · have heqRaw :
        flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1) =
          flooredCappedPolicyRunningMax floor weighted.βdagger x n := by
        simpa only [b, b'] using heq.symm
    rw [heqRaw, intervalIntegral.integral_same, sub_self, mul_zero, add_zero]
    simpa only [mul_zero] using
      (div_nonneg (sq_nonneg (u n)) (by norm_num : (0 : ℝ) ≤ 2))

/-- The policy-level mass of complete advancing-cell burden. -/
def flooredCappedBurdenMass
    (p : LoopParams) (rho floor cap : ℝ) (x : ℕ → LoopState) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    passageCellBurden p rho
        (flooredCappedPolicyRunningMax floor cap x n) (x n).1 (x n).2 *
      (flooredCappedPolicyRunningMax floor cap x (n + 1) -
        flooredCappedPolicyRunningMax floor cap x n)

/-- The policy-level mass of stock deficit carried by the cells of a floored
stopped-maximum partition. -/
def flooredCappedDeficitMass
    (p : LoopParams) (floor cap : ℝ) (x : ℕ → LoopState) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    (p.stationaryStock (flooredCappedPolicyRunningMax floor cap x n) -
        (x n).2) *
      (flooredCappedPolicyRunningMax floor cap x (n + 1) -
        flooredCappedPolicyRunningMax floor cap x n)

/-- The same deficit mass weighted by the exact stock coefficient in the
civic-weighted gradient. -/
def flooredCappedDeficitCharge
    (p : LoopParams) (rho floor cap : ℝ) (x : ℕ → LoopState) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    (2 * p.c *
        (1 - p.c * flooredCappedPolicyRunningMax floor cap x n) - rho) *
      (p.stationaryStock (flooredCappedPolicyRunningMax floor cap x n) -
        (x n).2) *
      (flooredCappedPolicyRunningMax floor cap x (n + 1) -
        flooredCappedPolicyRunningMax floor cap x n)

/-- Paper II, Proposition `prop:passage`, complete localized level budget.
The action gap above the coupled barrier pays the burden mass, including all
retreat corrections. -/
theorem IsControlledCivicWeightedPathFrom.floored_coupled_barrier_add_burden_le_action
    {p : LoopParams} {rho floor L : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hfloor : floor ∈ Icc (0 : ℝ) weighted.βdagger)
    (hstart : x₀.1 ≤ floor)
    (hstock₀ : x₀.2 ≤ p.stationaryStock floor) {N : ℕ}
    (hcross : weighted.βdagger ≤ policyRunningMax x N) :
    (coupledCellFactor (p.α * L) / p.α) *
        ((∫ z in floor..weighted.βdagger,
            weightedBarrierIntegrand p rho z) +
          flooredCappedBurdenMass
            p rho floor weighted.βdagger x N) ≤
      controlAction u N := by
  let b : ℕ → ℝ := fun n ↦
    flooredCappedPolicyRunningMax floor weighted.βdagger x n
  let f := weightedBarrierIntegrand p rho
  let q : ℕ → ℝ := fun n ↦
    passageCellBurden p rho (b n) (x n).1 (x n).2 *
      (b (n + 1) - b n)
  have hbsegment : ∀ n, b n ∈ Icc floor weighted.βdagger :=
    fun n ↦ path.flooredCappedRunningMax_mem weighted hx₀.1 hfloor n
  have hbmem : ∀ n, b n ∈ Icc (0 : ℝ) weighted.βdagger :=
    fun n ↦ ⟨hfloor.1.trans (hbsegment n).1, (hbsegment n).2⟩
  have hbmono : ∀ n, b n ≤ b (n + 1) := fun n ↦
    monotone_flooredCappedPolicyRunningMax
      floor weighted.βdagger x n.le_succ
  have hcellInt : ∀ n < N, IntervalIntegrable f MeasureTheory.volume
      (b n) (b (n + 1)) := by
    intro n _hn
    have hsubset : [[b n, b (n + 1)]] ⊆
        Icc (0 : ℝ) weighted.βdagger := by
      rw [uIcc_of_le (hbmono n)]
      intro z hz
      exact ⟨(hbmem n).1.trans hz.1,
        hz.2.trans (hbmem (n + 1)).2⟩
    exact ((continuousOn_weightedBarrierIntegrand model rho weighted).mono
      hsubset).intervalIntegrable
  have hadjacent :
      ∑ n ∈ Finset.range N, ∫ z in b n..b (n + 1), f z =
        ∫ z in b 0..b N, f z :=
    intervalIntegral.sum_integral_adjacent_intervals hcellInt
  have hbegin : b 0 = floor :=
    path.flooredCappedRunningMax_zero weighted hfloor.2 hstart
  have hend : b N = weighted.βdagger :=
    flooredCappedRunningMax_eq_target hcross
  have hdecompose :
      (∫ z in floor..weighted.βdagger, f z) +
          flooredCappedBurdenMass
            p rho floor weighted.βdagger x N =
        ∑ n ∈ Finset.range N,
          ((∫ z in b n..b (n + 1), f z) + q n) := by
    rw [Finset.sum_add_distrib, hadjacent, hbegin, hend]
    rfl
  have hsum :
      ∑ n ∈ Finset.range N,
          (coupledCellFactor (p.α * L) / p.α) *
            ((∫ z in b n..b (n + 1), f z) + q n) ≤
        ∑ n ∈ Finset.range N, (u n) ^ 2 / 2 := by
    exact Finset.sum_le_sum fun n _hn ↦ by
      simpa only [b, f, q] using
        path.floored_coupled_burden_cell_le_half_control_sq
          model ss hcoop weighted hL hx₀ hfloor hstart hstock₀ n
  calc
    (coupledCellFactor (p.α * L) / p.α) *
        ((∫ z in floor..weighted.βdagger,
            weightedBarrierIntegrand p rho z) +
          flooredCappedBurdenMass
            p rho floor weighted.βdagger x N) =
        ∑ n ∈ Finset.range N,
          (coupledCellFactor (p.α * L) / p.α) *
            ((∫ z in b n..b (n + 1), f z) + q n) := by
      rw [show weightedBarrierIntegrand p rho = f from rfl,
        hdecompose, Finset.mul_sum]
    _ ≤ ∑ n ∈ Finset.range N, (u n) ^ 2 / 2 := hsum
    _ = controlAction u N := by
      simp only [controlAction, div_eq_mul_inv, Finset.mul_sum]
      ring_nf

/-- Paper II, Proposition `prop:passage`, localized level budget.  Summing
the refined cells prices the complete barrier interval and the complete
coefficient-weighted deficit mass without double counting either term. -/
theorem IsControlledCivicWeightedPathFrom.floored_coupled_barrier_add_deficit_le_action
    {p : LoopParams} {rho floor L : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hfloor : floor ∈ Icc (0 : ℝ) weighted.βdagger)
    (hstart : x₀.1 ≤ floor)
    (hstock₀ : x₀.2 ≤ p.stationaryStock floor) {N : ℕ}
    (hcross : weighted.βdagger ≤ policyRunningMax x N) :
    (coupledCellFactor (p.α * L) / p.α) *
        ((∫ z in floor..weighted.βdagger,
            weightedBarrierIntegrand p rho z) +
          flooredCappedDeficitCharge
            p rho floor weighted.βdagger x N) ≤
      controlAction u N := by
  let b : ℕ → ℝ := fun n ↦
    flooredCappedPolicyRunningMax floor weighted.βdagger x n
  let f := weightedBarrierIntegrand p rho
  let q : ℕ → ℝ := fun n ↦
    (2 * p.c * (1 - p.c * b n) - rho) *
      (p.stationaryStock (b n) - (x n).2) * (b (n + 1) - b n)
  have hbsegment : ∀ n, b n ∈ Icc floor weighted.βdagger :=
    fun n ↦ path.flooredCappedRunningMax_mem weighted hx₀.1 hfloor n
  have hbmem : ∀ n, b n ∈ Icc (0 : ℝ) weighted.βdagger :=
    fun n ↦ ⟨hfloor.1.trans (hbsegment n).1, (hbsegment n).2⟩
  have hbmono : ∀ n, b n ≤ b (n + 1) := fun n ↦
    monotone_flooredCappedPolicyRunningMax
      floor weighted.βdagger x n.le_succ
  have hcellInt : ∀ n < N, IntervalIntegrable f MeasureTheory.volume
      (b n) (b (n + 1)) := by
    intro n _hn
    have hsubset : [[b n, b (n + 1)]] ⊆
        Icc (0 : ℝ) weighted.βdagger := by
      rw [uIcc_of_le (hbmono n)]
      intro z hz
      exact ⟨(hbmem n).1.trans hz.1,
        hz.2.trans (hbmem (n + 1)).2⟩
    exact ((continuousOn_weightedBarrierIntegrand model rho weighted).mono
      hsubset).intervalIntegrable
  have hadjacent :
      ∑ n ∈ Finset.range N, ∫ z in b n..b (n + 1), f z =
        ∫ z in b 0..b N, f z :=
    intervalIntegral.sum_integral_adjacent_intervals hcellInt
  have hbegin : b 0 = floor :=
    path.flooredCappedRunningMax_zero weighted hfloor.2 hstart
  have hend : b N = weighted.βdagger :=
    flooredCappedRunningMax_eq_target hcross
  have hdecompose :
      (∫ z in floor..weighted.βdagger, f z) +
          flooredCappedDeficitCharge
            p rho floor weighted.βdagger x N =
        ∑ n ∈ Finset.range N,
          ((∫ z in b n..b (n + 1), f z) + q n) := by
    rw [Finset.sum_add_distrib, hadjacent, hbegin, hend]
    rfl
  have hsum :
      ∑ n ∈ Finset.range N,
          (coupledCellFactor (p.α * L) / p.α) *
            ((∫ z in b n..b (n + 1), f z) + q n) ≤
        ∑ n ∈ Finset.range N, (u n) ^ 2 / 2 := by
    exact Finset.sum_le_sum fun n _hn ↦ by
      simpa only [b, f, q] using
        path.floored_coupled_deficit_cell_le_half_control_sq
          model ss hcoop weighted hL hx₀ hfloor hstart hstock₀ n
  calc
    (coupledCellFactor (p.α * L) / p.α) *
        ((∫ z in floor..weighted.βdagger,
            weightedBarrierIntegrand p rho z) +
          flooredCappedDeficitCharge
            p rho floor weighted.βdagger x N) =
        ∑ n ∈ Finset.range N,
          (coupledCellFactor (p.α * L) / p.α) *
            ((∫ z in b n..b (n + 1), f z) + q n) := by
      rw [show weightedBarrierIntegrand p rho = f from rfl,
        hdecompose, Finset.mul_sum]
    _ ≤ ∑ n ∈ Finset.range N, (u n) ^ 2 / 2 := hsum
    _ = controlAction u N := by
      simp only [controlAction, div_eq_mul_inv, Finset.mul_sum]
      ring_nf

/-- The minimum stock coefficient on the saddle segment.  Since the
coefficient decreases with policy, its minimum is attained at the saddle. -/
def saddleStockCoefficient
    (p : LoopParams) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) : ℝ :=
  2 * p.c * (1 - p.c * weighted.βdagger) - rho

/-- Paper II, Proposition `prop:passage`: the minimum stock coefficient is
strictly positive.  At the saddle its product with positive stationary stock
equals the positive primitive loss `v`. -/
theorem saddleStockCoefficient_pos
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho : ℝ} (weighted : WeightedThresholdAssumption p rho) :
    0 < saddleStockCoefficient p weighted := by
  have hbUnit : weighted.βdagger ∈ Icc (0 : ℝ) 1 :=
    ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩
  have hstockPos : 0 < p.stationaryStock weighted.βdagger :=
    model.I_pos.trans_le (stationaryStock_mem_stockInterval model hbUnit).1
  have hroot : civicWeightedGradient p rho weighted.βdagger
      (p.stationaryStock weighted.βdagger) = 0 := by
    rw [civicWeightedGradient_stationary_eq_weightedStationaryGradient rho hbUnit]
    exact weighted.gradient_zero
  simp only [civicWeightedGradient, LoopParams.gradU] at hroot
  by_contra hnot
  have hcoefficient : saddleStockCoefficient p weighted ≤ 0 :=
    not_lt.mp hnot
  have hproduct : saddleStockCoefficient p weighted *
      p.stationaryStock weighted.βdagger ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hcoefficient hstockPos.le
  simp only [saddleStockCoefficient] at hproduct
  nlinarith [model.v_pos]

/-- The saddle coefficient is a lower bound for the stock coefficient at
every level below the saddle. -/
theorem saddleStockCoefficient_le
    {p : LoopParams} (_model : DriftModelAssumptions p)
    {rho b : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (hb : b ∈ Icc (0 : ℝ) weighted.βdagger) :
    saddleStockCoefficient p weighted ≤
      2 * p.c * (1 - p.c * b) - rho := by
  have hproduct : 0 ≤ 2 * p.c ^ 2 * (weighted.βdagger - b) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg p.c))
      (sub_nonneg.mpr hb.2)
  simp only [saddleStockCoefficient]
  nlinarith

/-- Burden-aware truncation estimate for an actual new-maximum step.  The
selected burden controls both the old-level deficit and any preceding policy
retreat; only the realized advance beyond the old level remains explicit. -/
theorem IsControlledCivicWeightedPath.stationaryStockLag_succ_le_burden_add_advance
    {p : LoopParams} {rho : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPath p rho u x)
    (hfour : 4 * p.α * p.c ^ 2 * p.I ≤ p.lambda₀) {n : ℕ}
    (hadvance :
      flooredCappedPolicyRunningMax 0 weighted.βdagger x n <
        flooredCappedPolicyRunningMax 0 weighted.βdagger x (n + 1)) :
    stationaryStockLag p (x (n + 1)) ≤
      (1 / saddleStockCoefficient p weighted +
          2 * p.α * passageRetreatTransportSlope p) *
        passageCellBurden p rho
          (flooredCappedPolicyRunningMax 0 weighted.βdagger x n)
          (x n).1 (x n).2 +
      driftStationaryStockLipschitzBound p *
        ((x (n + 1)).1 -
          flooredCappedPolicyRunningMax 0 weighted.βdagger x n) := by
  let b := flooredCappedPolicyRunningMax 0 weighted.βdagger x n
  let beta := (x n).1
  let beta' := (x (n + 1)).1
  let D := (x n).2
  let theta := p.stationaryStock b - D
  let q := passageCellBurden p rho b beta D
  obtain ⟨hold, hbetaB, hnewPolicy⟩ :=
    flooredCappedRunningMax_advance_structure hadvance
  have hp₁mem : calibratedPoint p ∈ absorbingBox p :=
    ⟨by simp [calibratedPoint],
      stationaryStock_mem_stockInterval model (by norm_num)⟩
  have hfloor : (0 : ℝ) ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨le_rfl, weighted.βdagger_mem.1.le⟩
  have hfloorUnit : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hstart : (calibratedPoint p).1 ≤ (0 : ℝ) := by
    change (0 : ℝ) ≤ 0
    exact le_rfl
  have hstock₀ : (calibratedPoint p).2 ≤ p.stationaryStock 0 := by
    change p.stationaryStock 0 ≤ p.stationaryStock 0
    exact le_rfl
  have hbsegment := path.toFrom.flooredCappedRunningMax_mem
    weighted hp₁mem.1 hfloor n
  have hbmem : b ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨hfloor.1.trans hbsegment.1, hbsegment.2⟩
  have hbUnit : b ∈ Icc (0 : ℝ) 1 :=
    ⟨hbmem.1, hbmem.2.trans weighted.βdagger_mem.2.le⟩
  have hstock := path.toFrom.stock_le_stationary_flooredRunningMax
    model ss hp₁mem hfloorUnit hstart hstock₀ n
  rw [← hold] at hstock
  have htheta : 0 ≤ theta := by
    simpa only [theta, b, D] using sub_nonneg.mpr hstock
  have hdip : 0 ≤ b - beta := by
    simpa only [b, beta] using sub_nonneg.mpr hbetaB
  have hbnext : b ≤ beta' := by
    dsimp only [b, beta']
    exact hadvance.le.trans hnewPolicy
  have htransport := path.stationaryStockLag_succ_le_oldLevel_add_retreat
    model n hbUnit hbetaB hbnext hstock
  have hlower :=
    path.toFrom.deficit_add_halfRetreat_le_passageCellBurden
      model ss weighted hp₁mem hfloor hstart hstock₀ hfour hadvance
  change saddleStockCoefficient p weighted * theta +
      (1 / (2 * p.α)) * (b - beta) ≤ q at hlower
  have hq : 0 ≤ q := by
    simpa only [q, b, beta, D] using
      path.toFrom.passageCellBurden_nonneg_of_advance
        model ss hcoop weighted hp₁mem hfloor hstart hstock₀ hadvance
  have hA : 0 < saddleStockCoefficient p weighted :=
    saddleStockCoefficient_pos model weighted
  have hretreatWeight : 0 ≤ 1 / (2 * p.α) :=
    (one_div_pos.mpr (mul_pos two_pos model.α_pos)).le
  have hthetaWeighted : saddleStockCoefficient p weighted * theta ≤ q := by
    have hsecond : 0 ≤ (1 / (2 * p.α)) * (b - beta) :=
      mul_nonneg hretreatWeight hdip
    linarith
  have hthetaLe : theta ≤ q / saddleStockCoefficient p weighted := by
    apply (le_div_iff₀ hA).2
    simpa only [mul_comm] using hthetaWeighted
  have hdipWeighted : (1 / (2 * p.α)) * (b - beta) ≤ q := by
    have hfirst : 0 ≤ saddleStockCoefficient p weighted * theta :=
      mul_nonneg (saddleStockCoefficient_pos model weighted).le htheta
    linarith
  have htwoAlpha : 0 < 2 * p.α := mul_pos two_pos model.α_pos
  have hdipDiv : (b - beta) / (2 * p.α) ≤ q := by
    calc
      (b - beta) / (2 * p.α) =
          (1 / (2 * p.α)) * (b - beta) := by ring
      _ ≤ q := hdipWeighted
  have hdipLe : b - beta ≤ (2 * p.α) * q := by
    simpa only [mul_comm] using (div_le_iff₀ htwoAlpha).mp hdipDiv
  have hR : 0 ≤ passageRetreatTransportSlope p := by
    simp only [passageRetreatTransportSlope]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) model.η_pos.le)
        (sub_nonneg.mpr model.lambda₀_lt_one.le))
      (div_nonneg model.I_pos.le model.lambda₀_pos.le)
  have hRdip := mul_le_mul_of_nonneg_left hdipLe hR
  calc
    stationaryStockLag p (x (n + 1)) ≤
        (p.stationaryStock
              (flooredCappedPolicyRunningMax 0 weighted.βdagger x n) -
            (x n).2) +
          passageRetreatTransportSlope p *
            (flooredCappedPolicyRunningMax 0 weighted.βdagger x n -
              (x n).1) +
          driftStationaryStockLipschitzBound p *
            ((x (n + 1)).1 -
              flooredCappedPolicyRunningMax 0 weighted.βdagger x n) :=
      by simpa only [b, beta, beta', D, theta] using htransport
    _ ≤ q / saddleStockCoefficient p weighted +
          passageRetreatTransportSlope p *
            ((2 * p.α) * q) +
          driftStationaryStockLipschitzBound p *
            ((x (n + 1)).1 -
              flooredCappedPolicyRunningMax 0 weighted.βdagger x n) := by
      gcongr
    _ = (1 / saddleStockCoefficient p weighted +
            2 * p.α * passageRetreatTransportSlope p) * q +
          driftStationaryStockLipschitzBound p *
            ((x (n + 1)).1 -
              flooredCappedPolicyRunningMax 0 weighted.βdagger x n) := by
      ring

/-- At an advancing stopped-maximum cell, the retreat of the current policy
below the old maximum is at most `2 alpha` times the complete cell burden.
This is the second half of the truncate-before bridge. -/
theorem IsControlledCivicWeightedPath.retreat_le_two_alpha_mul_burden
    {p : LoopParams} {rho : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPath p rho u x)
    (hfour : 4 * p.α * p.c ^ 2 * p.I ≤ p.lambda₀) {n : ℕ}
    (hadvance :
      flooredCappedPolicyRunningMax 0 weighted.βdagger x n <
        flooredCappedPolicyRunningMax 0 weighted.βdagger x (n + 1)) :
    flooredCappedPolicyRunningMax 0 weighted.βdagger x n - (x n).1 ≤
      2 * p.α * passageCellBurden p rho
        (flooredCappedPolicyRunningMax 0 weighted.βdagger x n)
        (x n).1 (x n).2 := by
  let b := flooredCappedPolicyRunningMax 0 weighted.βdagger x n
  let beta := (x n).1
  let D := (x n).2
  let theta := p.stationaryStock b - D
  let q := passageCellBurden p rho b beta D
  obtain ⟨hold, hbetaB, _hnewPolicy⟩ :=
    flooredCappedRunningMax_advance_structure hadvance
  have hp₁mem : calibratedPoint p ∈ absorbingBox p :=
    ⟨by simp [calibratedPoint],
      stationaryStock_mem_stockInterval model (by norm_num)⟩
  have hfloor : (0 : ℝ) ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨le_rfl, weighted.βdagger_mem.1.le⟩
  have hfloorUnit : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hstart : (calibratedPoint p).1 ≤ (0 : ℝ) := by
    change (0 : ℝ) ≤ 0
    exact le_rfl
  have hstock₀ : (calibratedPoint p).2 ≤ p.stationaryStock 0 := by
    change p.stationaryStock 0 ≤ p.stationaryStock 0
    exact le_rfl
  have hstock := path.toFrom.stock_le_stationary_flooredRunningMax
    model ss hp₁mem hfloorUnit hstart hstock₀ n
  rw [← hold] at hstock
  have htheta : 0 ≤ theta := by
    simpa only [theta, b, D] using sub_nonneg.mpr hstock
  have hlower :=
    path.toFrom.deficit_add_halfRetreat_le_passageCellBurden
      model ss weighted hp₁mem hfloor hstart hstock₀ hfour hadvance
  change saddleStockCoefficient p weighted * theta +
      (1 / (2 * p.α)) * (b - beta) ≤ q at hlower
  have hfirst : 0 ≤ saddleStockCoefficient p weighted * theta :=
    mul_nonneg (saddleStockCoefficient_pos model weighted).le htheta
  have hweighted : (1 / (2 * p.α)) * (b - beta) ≤ q := by
    linarith
  have htwoAlpha : 0 < 2 * p.α := mul_pos two_pos model.α_pos
  have hdiv : (b - beta) / (2 * p.α) ≤ q := by
    calc
      (b - beta) / (2 * p.α) =
          (1 / (2 * p.α)) * (b - beta) := by ring
      _ ≤ q := hweighted
  have hretreat : b - beta ≤ (2 * p.α) * q := by
    simpa only [mul_comm] using (div_le_iff₀ htwoAlpha).mp hdiv
  simpa only [b, beta, q, D] using hretreat

/-- At the beginning of an advancing selected cell, the complete burden
controls the signed own-position lag.  This is the bridge needed to truncate
*before* that cell: both the old-level deficit and the preceding retreat are
paid by the discarded suffix. -/
theorem IsControlledCivicWeightedPath.abs_stationaryStockLag_le_burden
    {p : LoopParams} {rho : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPath p rho u x)
    (hfour : 4 * p.α * p.c ^ 2 * p.I ≤ p.lambda₀) {n : ℕ}
    (hadvance :
      flooredCappedPolicyRunningMax 0 weighted.βdagger x n <
        flooredCappedPolicyRunningMax 0 weighted.βdagger x (n + 1)) :
    |stationaryStockLag p (x n)| ≤
      (1 / saddleStockCoefficient p weighted +
          2 * p.α * driftStationaryStockLipschitzBound p) *
        passageCellBurden p rho
          (flooredCappedPolicyRunningMax 0 weighted.βdagger x n)
          (x n).1 (x n).2 := by
  let b := flooredCappedPolicyRunningMax 0 weighted.βdagger x n
  let beta := (x n).1
  let D := (x n).2
  let theta := p.stationaryStock b - D
  let q := passageCellBurden p rho b beta D
  obtain ⟨hold, hbetaB, _hnewPolicy⟩ :=
    flooredCappedRunningMax_advance_structure hadvance
  have hp₁mem : calibratedPoint p ∈ absorbingBox p :=
    ⟨by simp [calibratedPoint],
      stationaryStock_mem_stockInterval model (by norm_num)⟩
  have hfloor : (0 : ℝ) ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨le_rfl, weighted.βdagger_mem.1.le⟩
  have hfloorUnit : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hstart : (calibratedPoint p).1 ≤ (0 : ℝ) := by
    change (0 : ℝ) ≤ 0
    exact le_rfl
  have hstock₀ : (calibratedPoint p).2 ≤ p.stationaryStock 0 := by
    change p.stationaryStock 0 ≤ p.stationaryStock 0
    exact le_rfl
  have hbsegment := path.toFrom.flooredCappedRunningMax_mem
    weighted hp₁mem.1 hfloor n
  have hbmem : b ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨hfloor.1.trans hbsegment.1, hbsegment.2⟩
  have hbUnit : b ∈ Icc (0 : ℝ) 1 :=
    ⟨hbmem.1, hbmem.2.trans weighted.βdagger_mem.2.le⟩
  have hbetaUnit : beta ∈ Icc (0 : ℝ) 1 := by
    simpa only [beta] using path.policy_mem n
  have hstock := path.toFrom.stock_le_stationary_flooredRunningMax
    model ss hp₁mem hfloorUnit hstart hstock₀ n
  rw [← hold] at hstock
  have htheta : 0 ≤ theta := by
    simpa only [theta, b, D] using sub_nonneg.mpr hstock
  have hdip : 0 ≤ b - beta := sub_nonneg.mpr hbetaB
  have hlower := path.toFrom.deficit_add_halfRetreat_le_passageCellBurden
    model ss weighted hp₁mem hfloor hstart hstock₀ hfour hadvance
  change saddleStockCoefficient p weighted * theta +
      (1 / (2 * p.α)) * (b - beta) ≤ q at hlower
  have hq : 0 ≤ q := by
    simpa only [q, b, beta, D] using
      path.toFrom.passageCellBurden_nonneg_of_advance
        model ss hcoop weighted hp₁mem hfloor hstart hstock₀ hadvance
  have hA : 0 < saddleStockCoefficient p weighted :=
    saddleStockCoefficient_pos model weighted
  have hretreatWeight : 0 ≤ 1 / (2 * p.α) :=
    (one_div_pos.mpr (mul_pos two_pos model.α_pos)).le
  have hthetaWeighted : saddleStockCoefficient p weighted * theta ≤ q := by
    have hsecond : 0 ≤ (1 / (2 * p.α)) * (b - beta) :=
      mul_nonneg hretreatWeight hdip
    linarith
  have hthetaLe : theta ≤ q / saddleStockCoefficient p weighted := by
    apply (le_div_iff₀ hA).2
    simpa only [mul_comm] using hthetaWeighted
  have hdipWeighted : (1 / (2 * p.α)) * (b - beta) ≤ q := by
    have hfirst : 0 ≤ saddleStockCoefficient p weighted * theta :=
      mul_nonneg hA.le htheta
    linarith
  have htwoAlpha : 0 < 2 * p.α := mul_pos two_pos model.α_pos
  have hdipDiv : (b - beta) / (2 * p.α) ≤ q := by
    calc
      (b - beta) / (2 * p.α) =
          (1 / (2 * p.α)) * (b - beta) := by ring
      _ ≤ q := hdipWeighted
  have hdipLe : b - beta ≤ (2 * p.α) * q := by
    simpa only [mul_comm] using (div_le_iff₀ htwoAlpha).mp hdipDiv
  have hchar₀ : 0 ≤ p.stationaryStock b - p.stationaryStock beta :=
    sub_nonneg.mpr <| (stationaryStock_strictMonoOn model).monotoneOn
      hbetaUnit hbUnit hbetaB
  have hchar := stationaryStock_sub_le_driftLipschitz
    model hbetaUnit hbUnit hbetaB
  have hown : stationaryStockLag p (x n) =
      theta - (p.stationaryStock b - p.stationaryStock beta) := by
    simp only [stationaryStockLag, theta, beta, D]
    ring
  have habs : |stationaryStockLag p (x n)| ≤
      theta + (p.stationaryStock b - p.stationaryStock beta) := by
    rw [hown, abs_le]
    constructor <;> linarith
  have hK₀ : 0 ≤ driftStationaryStockLipschitzBound p :=
    (driftStationaryStockLipschitzBound_pos model).le
  calc
    |stationaryStockLag p (x n)| ≤
        theta + (p.stationaryStock b - p.stationaryStock beta) := habs
    _ ≤ q / saddleStockCoefficient p weighted +
        driftStationaryStockLipschitzBound p * (b - beta) := by
      gcongr
    _ ≤ q / saddleStockCoefficient p weighted +
        driftStationaryStockLipschitzBound p * ((2 * p.α) * q) := by
      linarith [mul_le_mul_of_nonneg_left hdipLe hK₀]
    _ = (1 / saddleStockCoefficient p weighted +
          2 * p.α * driftStationaryStockLipschitzBound p) * q := by
      ring

/-- A rate-free coefficient bounding the non-integral price of the
truncate-before one-climb continuation. -/
def passageOneClimbQuadraticConstant
    (p : LoopParams) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (L : ℝ) : ℝ :=
  let P := passageGradientBound p
  let CA := P + 4
  let CH := 3 * L + 1
  let K := driftStationaryStockLipschitzBound p
  let B := 1 / saddleStockCoefficient p weighted + 2 * K
  let CR := B + K * CA
  let M := 4 * p.c * (1 + L) / p.lambda₀
  2 * (2 * L * CH * CA +
    M * (CH * CR + 2 * p.c * CR ^ 2) +
    CA / 2 + 2 * p.c ^ 2 * CR ^ 2 / p.lambda₀)

/-- The one-climb quadratic coefficient is strictly positive. -/
theorem passageOneClimbQuadraticConstant_pos
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho L : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    0 < passageOneClimbQuadraticConstant p weighted L := by
  let P := passageGradientBound p
  let CA := P + 4
  let CH := 3 * L + 1
  let K := driftStationaryStockLipschitzBound p
  let B := 1 / saddleStockCoefficient p weighted + 2 * K
  let CR := B + K * CA
  let M := 4 * p.c * (1 + L) / p.lambda₀
  have hP : 0 ≤ P := (passageGradientBound_pos model).le
  have hCA : 0 < CA := by dsimp only [CA]; linarith
  have hL₀ : 0 ≤ L := hL.nonneg
  have hCH : 0 ≤ CH := by dsimp only [CH]; positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact (driftStationaryStockLipschitzBound_pos model).le
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact add_nonneg
      (one_div_nonneg.mpr (saddleStockCoefficient_pos model weighted).le)
      (mul_nonneg (by norm_num) hK)
  have hCR : 0 ≤ CR := by dsimp only [CR]; positivity
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) model.c_pos.le)
        (by linarith)) model.lambda₀_pos.le
  have hfirst : 0 ≤ 2 * L * CH * CA :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hL₀) hCH) hCA.le
  have hsecond : 0 ≤ M * (CH * CR + 2 * p.c * CR ^ 2) := by
    exact mul_nonneg hM <| add_nonneg (mul_nonneg hCH hCR)
      (mul_nonneg (mul_nonneg (by norm_num) model.c_pos.le) (sq_nonneg CR))
  have hfourth : 0 ≤ 2 * p.c ^ 2 * CR ^ 2 / p.lambda₀ :=
    div_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg p.c)) (sq_nonneg CR))
      model.lambda₀_pos.le
  simp only [passageOneClimbQuadraticConstant]
  dsimp only [P, CA, CH, K, B, CR, M] at hfirst hsecond hfourth ⊢
  linarith

/-- Pure scalar estimate behind the local one-climb construction.  If the
starting saddle distance and signed lag are controlled by a window width
`w` and burden `q`, every non-integral term in the continuation price is
bounded by one fixed multiple of `w² + q²`. -/
theorem oneClimb_nonintegral_price_le_quadratic
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho L alpha w q d A R H : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (halpha : 0 < alpha) (halphaOne : alpha ≤ 1)
    (hw : 0 ≤ w) (hq : 0 ≤ q) (halphaW : alpha ≤ w)
    (hd₀ : 0 ≤ d) (hd : d ≤ w + 2 * alpha * q)
    (hA₀ : 0 ≤ A)
    (hA : A ≤ d + alpha * (passageGradientBound p + alpha * w))
    (hH : H = L * d + alpha * w)
    (hR₀ : 0 ≤ R)
    (hR : R ≤
      (1 / saddleStockCoefficient p weighted +
          2 * alpha * driftStationaryStockLipschitzBound p) * q +
        driftStationaryStockLipschitzBound p * A) :
    2 * L * H * A +
        (4 * p.c * (1 + alpha * L) / p.lambda₀) *
          (H * R + 2 * p.c * R ^ 2) +
        (w / 2) * A + 2 * p.c ^ 2 * R ^ 2 / p.lambda₀ ≤
      passageOneClimbQuadraticConstant p weighted L * (w ^ 2 + q ^ 2) := by
  let P := passageGradientBound p
  let CA := P + 4
  let CH := 3 * L + 1
  let K := driftStationaryStockLipschitzBound p
  let B := 1 / saddleStockCoefficient p weighted + 2 * K
  let CR := B + K * CA
  let M := 4 * p.c * (1 + L) / p.lambda₀
  let E := 2 * L * CH * CA +
    M * (CH * CR + 2 * p.c * CR ^ 2) +
    CA / 2 + 2 * p.c ^ 2 * CR ^ 2 / p.lambda₀
  let S := w + q
  have hP₀ : 0 ≤ P := (passageGradientBound_pos model).le
  have hCA₀ : 0 ≤ CA := by dsimp only [CA]; linarith
  have hL₀ : 0 ≤ L := hL.nonneg
  have hCH₀ : 0 ≤ CH := by dsimp only [CH]; positivity
  have hK₀ : 0 ≤ K := by
    dsimp only [K]
    exact (driftStationaryStockLipschitzBound_pos model).le
  have hB₀ : 0 ≤ B := by
    dsimp only [B]
    exact add_nonneg
      (one_div_nonneg.mpr (saddleStockCoefficient_pos model weighted).le)
      (mul_nonneg (by norm_num) hK₀)
  have hCR₀ : 0 ≤ CR := by dsimp only [CR]; positivity
  have hM₀ : 0 ≤ M := by
    dsimp only [M]
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) model.c_pos.le)
        (by linarith)) model.lambda₀_pos.le
  have hS₀ : 0 ≤ S := by dsimp only [S]; linarith
  have hE₀ : 0 ≤ E := by
    dsimp only [E]
    have hfirst : 0 ≤ 2 * L * CH * CA :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hL₀) hCH₀) hCA₀
    have hsecond : 0 ≤ M * (CH * CR + 2 * p.c * CR ^ 2) :=
      mul_nonneg hM₀ <| add_nonneg (mul_nonneg hCH₀ hCR₀)
        (mul_nonneg (mul_nonneg (by norm_num) model.c_pos.le) (sq_nonneg CR))
    have hthird : 0 ≤ CA / 2 := div_nonneg hCA₀ (by norm_num)
    have hfourth : 0 ≤ 2 * p.c ^ 2 * CR ^ 2 / p.lambda₀ :=
      div_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (sq_nonneg p.c)) (sq_nonneg CR))
        model.lambda₀_pos.le
    linarith only [hfirst, hsecond, hthird, hfourth]
  have halphaQ : alpha * q ≤ q :=
    mul_le_of_le_one_left hq halphaOne
  have hd' : d ≤ w + 2 * q := by linarith
  have halphaP : alpha * P ≤ w * P :=
    mul_le_mul_of_nonneg_right halphaW hP₀
  have halphaSq : alpha ^ 2 ≤ 1 := by
    have hprod := mul_nonneg halpha.le (sub_nonneg.mpr halphaOne)
    nlinarith
  have halphaSqW : alpha ^ 2 * w ≤ w := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right halphaSq hw
  have hmesh : alpha * (P + alpha * w) ≤ (P + 1) * w := by
    nlinarith
  have hAbase : A ≤ (P + 2) * w + 2 * q := by
    change A ≤ d + alpha * (P + alpha * w) at hA
    linarith
  have hAupper : A ≤ CA * S := by
    have htail : 0 ≤ 2 * w + (P + 2) * q := by positivity
    dsimp only [CA, S]
    nlinarith
  have halphaW' : alpha * w ≤ w :=
    mul_le_of_le_one_left hw halphaOne
  have hHupper : H ≤ CH * S := by
    have hLd := mul_le_mul_of_nonneg_left hd' hL₀
    have htail : 0 ≤ 2 * L * w + (L + 1) * q := by positivity
    rw [hH]
    dsimp only [CH, S]
    nlinarith
  have hH₀ : 0 ≤ H := by
    rw [hH]
    exact add_nonneg (mul_nonneg hL₀ hd₀)
      (mul_nonneg halpha.le hw)
  have hBalpha :
      1 / saddleStockCoefficient p weighted + 2 * alpha * K ≤ B := by
    have htwoK : 0 ≤ 2 * K := mul_nonneg (by norm_num) hK₀
    have hmul := mul_le_mul_of_nonneg_right halphaOne htwoK
    dsimp only [B]
    nlinarith
  have hBalpha₀ :
      0 ≤ 1 / saddleStockCoefficient p weighted + 2 * alpha * K := by
    exact add_nonneg
      (one_div_nonneg.mpr (saddleStockCoefficient_pos model weighted).le)
      (mul_nonneg (mul_nonneg (by norm_num) halpha.le) hK₀)
  have hRq :
      (1 / saddleStockCoefficient p weighted + 2 * alpha * K) * q ≤
        B * q := mul_le_mul_of_nonneg_right hBalpha hq
  have hKA : K * A ≤ K * (CA * S) :=
    mul_le_mul_of_nonneg_left hAupper hK₀
  have hRupper : R ≤ CR * S := by
    have hR' : R ≤
        (1 / saddleStockCoefficient p weighted + 2 * alpha * K) * q +
          K * A := by
      simpa only [K] using hR
    calc
      R ≤ _ := hR'
      _ ≤ B * q + K * (CA * S) := add_le_add hRq hKA
      _ ≤ B * S + K * (CA * S) := by
        have hqS : q ≤ S := by dsimp only [S]; linarith
        exact add_le_add (mul_le_mul_of_nonneg_left hqS hB₀) le_rfl
      _ = CR * S := by
        dsimp only [CR, S]
        ring
  have hHA : H * A ≤ CH * CA * S ^ 2 := by
    calc
      H * A ≤ (CH * S) * (CA * S) :=
        mul_le_mul hHupper hAupper hA₀
          (mul_nonneg hCH₀ hS₀)
      _ = CH * CA * S ^ 2 := by ring
  have hHR : H * R ≤ CH * CR * S ^ 2 := by
    calc
      H * R ≤ (CH * S) * (CR * S) :=
        mul_le_mul hHupper hRupper hR₀
          (mul_nonneg hCH₀ hS₀)
      _ = CH * CR * S ^ 2 := by ring
  have hRsq : R ^ 2 ≤ CR ^ 2 * S ^ 2 := by
    have hsquare := (sq_le_sq₀ hR₀
      (mul_nonneg hCR₀ hS₀)).2 hRupper
    simpa only [mul_pow] using hsquare
  have hAlphaL : alpha * L ≤ L :=
    mul_le_of_le_one_left hL₀ halphaOne
  have hcoeff : 4 * p.c * (1 + alpha * L) / p.lambda₀ ≤ M := by
    have hadd : 1 + alpha * L ≤ 1 + L := by linarith
    have hscale : 0 ≤ 4 * p.c :=
      mul_nonneg (by norm_num) model.c_pos.le
    have hmul := mul_le_mul_of_nonneg_left hadd hscale
    exact (div_le_div_iff_of_pos_right model.lambda₀_pos).2 <| by
      simpa only [M] using hmul
  have hcoeff₀ : 0 ≤ 4 * p.c * (1 + alpha * L) / p.lambda₀ := by
    have hone : 0 ≤ 1 + alpha * L := by positivity
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) model.c_pos.le) hone)
      model.lambda₀_pos.le
  have hinside : H * R + 2 * p.c * R ^ 2 ≤
      (CH * CR + 2 * p.c * CR ^ 2) * S ^ 2 := by
    have hsquareScaled : 2 * p.c * R ^ 2 ≤
        2 * p.c * (CR ^ 2 * S ^ 2) :=
      mul_le_mul_of_nonneg_left hRsq
        (mul_nonneg (by norm_num) model.c_pos.le)
    calc
      H * R + 2 * p.c * R ^ 2 ≤
          CH * CR * S ^ 2 + 2 * p.c * (CR ^ 2 * S ^ 2) :=
        add_le_add hHR hsquareScaled
      _ = (CH * CR + 2 * p.c * CR ^ 2) * S ^ 2 := by ring
  have hinside₀ : 0 ≤ H * R + 2 * p.c * R ^ 2 :=
    add_nonneg (mul_nonneg hH₀ hR₀)
      (mul_nonneg
        (mul_nonneg (by norm_num) model.c_pos.le) (sq_nonneg R))
  have hterm₁ : 2 * L * H * A ≤ 2 * L * CH * CA * S ^ 2 := by
    have htwoL : 0 ≤ 2 * L := mul_nonneg (by norm_num) hL₀
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hHA htwoL
  have hterm₂ :
      (4 * p.c * (1 + alpha * L) / p.lambda₀) *
          (H * R + 2 * p.c * R ^ 2) ≤
        M * (CH * CR + 2 * p.c * CR ^ 2) * S ^ 2 := by
    calc
      _ ≤ M * (H * R + 2 * p.c * R ^ 2) :=
        mul_le_mul_of_nonneg_right hcoeff hinside₀
      _ ≤ M * ((CH * CR + 2 * p.c * CR ^ 2) * S ^ 2) :=
        mul_le_mul_of_nonneg_left hinside hM₀
      _ = _ := by ring
  have hterm₃ : (w / 2) * A ≤ (CA / 2) * S ^ 2 := by
    have hwS : w ≤ S := by dsimp only [S]; linarith
    have hhalfW : w / 2 ≤ S / 2 :=
      (div_le_div_iff_of_pos_right two_pos).2 hwS
    calc
      (w / 2) * A ≤ (S / 2) * (CA * S) :=
        mul_le_mul hhalfW hAupper hA₀
          (div_nonneg hS₀ (by norm_num))
      _ = (CA / 2) * S ^ 2 := by ring
  have hterm₄ : 2 * p.c ^ 2 * R ^ 2 / p.lambda₀ ≤
      (2 * p.c ^ 2 * CR ^ 2 / p.lambda₀) * S ^ 2 := by
    have hscale : 0 ≤ 2 * p.c ^ 2 / p.lambda₀ :=
      div_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg p.c))
        model.lambda₀_pos.le
    have hscaled := mul_le_mul_of_nonneg_left hRsq hscale
    calc
      2 * p.c ^ 2 * R ^ 2 / p.lambda₀ =
          (2 * p.c ^ 2 / p.lambda₀) * R ^ 2 := by ring
      _ ≤ (2 * p.c ^ 2 / p.lambda₀) * (CR ^ 2 * S ^ 2) := hscaled
      _ = (2 * p.c ^ 2 * CR ^ 2 / p.lambda₀) * S ^ 2 := by ring
  have hsum :
      2 * L * H * A +
          (4 * p.c * (1 + alpha * L) / p.lambda₀) *
            (H * R + 2 * p.c * R ^ 2) +
          (w / 2) * A + 2 * p.c ^ 2 * R ^ 2 / p.lambda₀ ≤
        E * S ^ 2 := by
    dsimp only [E]
    linarith only [hterm₁, hterm₂, hterm₃, hterm₄]
  have hsumSq : S ^ 2 ≤ 2 * (w ^ 2 + q ^ 2) := by
    dsimp only [S]
    nlinarith only [sq_nonneg (w - q)]
  have hscaledSum := mul_le_mul_of_nonneg_left hsumSq hE₀
  calc
    _ ≤ E * S ^ 2 := hsum
    _ ≤ E * (2 * (w ^ 2 + q ^ 2)) := hscaledSum
    _ = passageOneClimbQuadraticConstant p weighted L *
        (w ^ 2 + q ^ 2) := by
      simp only [passageOneClimbQuadraticConstant]
      dsimp only [P, CA, CH, K, B, CR, M, E]
      ring

/-- A rate-free coefficient for the complete local truncate-before
construction.  Besides the non-integral one-climb price, it absorbs the
retreat re-climb and the difference between the natural `2 / alpha`
coefficient and the coupled suffix-refund coefficient. -/
def passageLocalOneClimbQuadraticConstant
    (p : LoopParams) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (L : ℝ) : ℝ :=
  2 * passageOneClimbQuadraticConstant p weighted L +
    14 * L + 2 * L ^ 2

/-- The complete local coefficient is independent of the operator rate in
the fixed-primitives family. -/
@[simp] theorem passageLocalOneClimbQuadraticConstant_withOperatorRate
    (p : LoopParams) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (L alpha : ℝ) :
    passageLocalOneClimbQuadraticConstant (withOperatorRate p alpha)
        (weighted.withOperatorRate alpha) L =
      passageLocalOneClimbQuadraticConstant p weighted L := by
  rfl

/-- The complete local one-climb coefficient is strictly positive. -/
theorem passageLocalOneClimbQuadraticConstant_pos
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho L : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    0 < passageLocalOneClimbQuadraticConstant p weighted L := by
  have hC := passageOneClimbQuadraticConstant_pos model weighted hL
  have hL₀ : 0 ≤ L := hL.nonneg
  simp only [passageLocalOneClimbQuadraticConstant]
  nlinarith only [hC, hL₀, sq_nonneg L]

/-- Scalar collection of the three quadratic remainders in the local
truncate-before construction. -/
theorem localOneClimbQuadratic_collect
    {C₀ L W D w q : ℝ} (hC₀ : 0 ≤ C₀) (hL : 0 ≤ L)
    (hW : W ^ 2 ≤ 2 * (D ^ 2 + w ^ 2)) :
    C₀ * (W ^ 2 + q ^ 2) +
        14 * L * (D ^ 2 + q ^ 2) +
        (3 * L ^ 2 / 2) * D ^ 2 ≤
      (2 * C₀ + 14 * L + 2 * L ^ 2) *
        (w ^ 2 + D ^ 2 + q ^ 2) := by
  have hWq : W ^ 2 + q ^ 2 ≤
      2 * (D ^ 2 + w ^ 2) + q ^ 2 := add_le_add hW le_rfl
  have hWqScaled : C₀ * (W ^ 2 + q ^ 2) ≤
      C₀ * (2 * (D ^ 2 + w ^ 2) + q ^ 2) :=
    mul_le_mul_of_nonneg_left hWq hC₀
  have hwTerm : 0 ≤ (14 * L + 2 * L ^ 2) * w ^ 2 :=
    mul_nonneg (by nlinarith only [hL, sq_nonneg L]) (sq_nonneg w)
  have hDTerm : 0 ≤ (L ^ 2 / 2) * D ^ 2 :=
    mul_nonneg (div_nonneg (sq_nonneg L) (by norm_num)) (sq_nonneg D)
  have hqTerm : 0 ≤ (C₀ + 2 * L ^ 2) * q ^ 2 :=
    mul_nonneg (add_nonneg hC₀ (mul_nonneg (by norm_num) (sq_nonneg L)))
      (sq_nonneg q)
  have hid :
      (2 * C₀ + 14 * L + 2 * L ^ 2) *
          (w ^ 2 + D ^ 2 + q ^ 2) =
        (C₀ * (2 * (D ^ 2 + w ^ 2) + q ^ 2) +
          14 * L * (D ^ 2 + q ^ 2) + (3 * L ^ 2 / 2) * D ^ 2) +
          (14 * L + 2 * L ^ 2) * w ^ 2 +
          (L ^ 2 / 2) * D ^ 2 + (C₀ + 2 * L ^ 2) * q ^ 2 := by
    ring
  rw [hid]
  linarith only [hWqScaled, hwTerm, hDTerm, hqTerm]

/-- Scalar overleap estimate.  If an advancing cell starts more than one
window width below the saddle, its advance and the exact coupled residual
control that distance. -/
theorem overleapingCell_saddleDistance_sq_le
    {alpha L D w q r e f : ℝ}
    (halpha : 0 < alpha) (halphaOne : alpha ≤ 1)
    (hL : 0 ≤ L) (hquarter : alpha * L ≤ 1 / 4)
    (hD : 0 ≤ D) (hw : 0 ≤ w) (hq : 0 ≤ q)
    (he : 0 ≤ e) (hfLe : f ≤ L * D)
    (hoverleap : D ≤ e + w)
    (hresidual : r = f + q - (1 - alpha * L) * (e / alpha)) :
    D ^ 2 ≤ 12 * w ^ 2 + 48 * q ^ 2 + 48 * alpha ^ 2 * r ^ 2 := by
  have hsum₀ : 0 ≤ L * D + q + |r| := by positivity
  have hinside : f + q - r ≤ L * D + q + |r| := by
    linarith [neg_le_abs r]
  have hfactorEq : (1 - alpha * L) * (e / alpha) = f + q - r := by
    linarith only [hresidual]
  have htransport : (1 - alpha * L) * e = alpha * (f + q - r) := by
    calc
      (1 - alpha * L) * e =
          alpha * ((1 - alpha * L) * (e / alpha)) := by
        field_simp [halpha.ne']
      _ = alpha * (f + q - r) := by rw [hfactorEq]
  have hinsideScaled := mul_le_mul_of_nonneg_left hinside halpha.le
  have hleft : (3 / 4 : ℝ) * e ≤ (1 - alpha * L) * e := by
    have hfactor : (3 / 4 : ℝ) ≤ 1 - alpha * L := by linarith
    exact mul_le_mul_of_nonneg_right hfactor he
  have hchain : (3 / 4 : ℝ) * e ≤
      alpha * (L * D + q + |r|) := by
    rw [htransport] at hleft
    exact hleft.trans hinsideScaled
  have heUpper : e ≤ 2 * alpha * (L * D + q + |r|) := by
    have hright₀ : 0 ≤ alpha * (L * D + q + |r|) :=
      mul_nonneg halpha.le hsum₀
    nlinarith only [hchain, hright₀]
  have hpre : D ≤ w + 2 * alpha * (L * D + q + |r|) := by
    linarith only [hoverleap, heUpper]
  have htwoFactor : 2 * alpha * L ≤ 1 / 2 := by
    nlinarith only [hquarter]
  have hLD : 2 * alpha * L * D ≤ (1 / 2 : ℝ) * D :=
    mul_le_mul_of_nonneg_right htwoFactor hD
  have hDlinear : D ≤ 2 * w + 4 * alpha * q + 4 * alpha * |r| := by
    nlinarith only [hpre, hLD]
  have hsumNonneg : 0 ≤ 2 * w + 4 * alpha * q + 4 * alpha * |r| := by
    positivity
  have hDsquare : D ^ 2 ≤
      (2 * w + 4 * alpha * q + 4 * alpha * |r|) ^ 2 :=
    (sq_le_sq₀ hD hsumNonneg).2 hDlinear
  let a := 2 * w
  let b := 4 * alpha * q
  let c := 4 * alpha * |r|
  have hthree : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    nlinarith only [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have hexpanded :
      (2 * w + 4 * alpha * q + 4 * alpha * |r|) ^ 2 ≤
        12 * w ^ 2 + 48 * alpha ^ 2 * q ^ 2 +
          48 * alpha ^ 2 * r ^ 2 := by
    dsimp only [a, b, c] at hthree
    have hrsq : |r| ^ 2 = r ^ 2 := sq_abs r
    nlinarith only [hthree, hrsq]
  have halphaSq : alpha ^ 2 ≤ 1 := by
    nlinarith only [halpha.le, halphaOne]
  have hqScaled : 48 * alpha ^ 2 * q ^ 2 ≤ 48 * q ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right halphaSq (sq_nonneg q)
    nlinarith only [hmul]
  linarith only [hDsquare, hexpanded, hqScaled]

/-- Local truncate-before surgery.  If an advancing cell begins at a state
whose retreat and signed stock lag are controlled by burden `q`, discard that
cell and its suffix, restart one natural margin climb, and exit.  The ideal
tail from the old stopped maximum is retained at exactly the coupled refund
coefficient; every other term is quadratic. -/
theorem exists_exitAction_le_prefix_add_tail_add_localQuadratic
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p)
    {rho L b w q : ℝ} (hrho : 0 ≤ rho)
    (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (halphaOne : p.α ≤ 1) (hsmall : p.α * L ≤ 1)
    (hb : b ∈ Icc (0 : ℝ) weighted.βdagger)
    (hw : p.α ≤ w) (hq : 0 ≤ q)
    {N : ℕ} (u : Fin N → ℝ) {x₀ : LoopState}
    (hend : finiteControlledOrbit p rho u N = x₀)
    (hx₀ : x₀ ∈ absorbingBox p) (hbetaB : x₀.1 ≤ b)
    (hretreat : b - x₀.1 ≤ 2 * p.α * q)
    (hlag : |stationaryStockLag p x₀| ≤
      (1 / saddleStockCoefficient p weighted +
          2 * p.α * driftStationaryStockLipschitzBound p) * q)
    (hroom : p.α *
        (passageGradientBound p +
          p.α * ((weighted.βdagger - b) + w)) ≤
      1 - weighted.βdagger) :
    ∃ e ∈ quasipotentialActionSet p rho,
      e ≤ gaussianVectorAction u +
        (coupledCellFactor (p.α * L) / p.α) *
          (∫ z in b..weighted.βdagger,
            weightedBarrierIntegrand p rho z) +
        passageLocalOneClimbQuadraticConstant p weighted L *
          (w ^ 2 + (weighted.βdagger - b) ^ 2 + q ^ 2) := by
  let beta := x₀.1
  let D := weighted.βdagger - b
  let W := D + w
  let epsilon := p.α * W
  let T := marginClimbStopFrom p rho epsilon weighted.βdagger x₀
  let y := marginClimbPathFrom p rho epsilon x₀ T
  let A := y.1 - x₀.1
  let R := |stationaryStockLag p x₀| +
    driftStationaryStockLipschitzBound p * A
  let H := L * (weighted.βdagger - x₀.1) + epsilon
  let C₀ := passageOneClimbQuadraticConstant p weighted L
  let C := passageLocalOneClimbQuadraticConstant p weighted L
  have hD₀ : 0 ≤ D := by dsimp only [D]; exact sub_nonneg.mpr hb.2
  have hw₀ : 0 ≤ w := model.α_pos.le.trans hw
  have hW₀ : 0 ≤ W := by dsimp only [W]; linarith
  have hWpos : 0 < W := by
    dsimp only [W]
    linarith [model.α_pos]
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    exact mul_pos model.α_pos hWpos
  have hbeta : beta ∈ Icc (0 : ℝ) weighted.βdagger := by
    refine ⟨?_, hbetaB.trans hb.2⟩
    dsimp only [beta]
    exact hx₀.1.1
  have hstart : x₀.1 ≤ weighted.βdagger := hbetaB.trans hb.2
  have hroom' : p.α * (passageGradientBound p + epsilon) ≤
      1 - weighted.βdagger := by
    simpa only [epsilon, W, D] using hroom
  obtain ⟨e, heMem, heBound⟩ :=
    exists_exitAction_le_prefix_add_oneClimb
      model ss hrho hrhoCure hcoop weighted hL u hend hx₀ hstart
        hepsilon hroom'
  have hmono : Monotone
      (fun n ↦ (marginClimbPathFrom p rho epsilon x₀ n).1) :=
    monotone_marginClimbPolicyFrom model rho epsilon hx₀.1 hepsilon.le
  have hA₀ : 0 ≤ A := by
    dsimp only [A, y]
    simpa only [marginClimbPathFrom_zero] using
      sub_nonneg.mpr (hmono (Nat.zero_le T))
  have hAupper : A ≤
      (weighted.βdagger - x₀.1) +
        p.α * (passageGradientBound p + p.α * W) := by
    have hadvance := marginClimbStopFrom_advance_le_distance_add_mesh
      model hrho hcoop hx₀ hstart weighted.βdagger_mem.2
        hepsilon hroom'
    simpa only [A, y, T, epsilon, W] using hadvance
  have hdistance : weighted.βdagger - x₀.1 ≤
      W + 2 * p.α * q := by
    have hdecomp : weighted.βdagger - x₀.1 =
        D + (b - x₀.1) := by
      dsimp only [D]
      ring
    rw [hdecomp]
    dsimp only [W]
    linarith
  have hR₀ : 0 ≤ R := by
    dsimp only [R]
    exact add_nonneg (abs_nonneg _)
      (mul_nonneg
        (driftStationaryStockLipschitzBound_pos model).le hA₀)
  have hRupper : R ≤
      (1 / saddleStockCoefficient p weighted +
          2 * p.α * driftStationaryStockLipschitzBound p) * q +
        driftStationaryStockLipschitzBound p * A := by
    dsimp only [R]
    exact add_le_add hlag le_rfl
  have hscalar := oneClimb_nonintegral_price_le_quadratic
    model weighted hL model.α_pos halphaOne hW₀ hq
      (show p.α ≤ W by dsimp only [W]; linarith)
      (sub_nonneg.mpr hstart) hdistance hA₀ hAupper
      (show H = L * (weighted.βdagger - x₀.1) + p.α * W by
        simp only [H, epsilon])
      hR₀ hRupper
  have heReduced : e ≤ gaussianVectorAction u +
      (2 / p.α) *
        (∫ z in x₀.1..weighted.βdagger,
          weightedBarrierIntegrand p rho z) +
      C₀ * (W ^ 2 + q ^ 2) := by
    have heBound' : e ≤ gaussianVectorAction u +
        (2 / p.α) *
          (∫ z in x₀.1..weighted.βdagger,
            weightedBarrierIntegrand p rho z) +
        2 * L * H * A +
        (4 * p.c * (1 + p.α * L) / p.lambda₀) *
          (H * R + 2 * p.c * R ^ 2) +
        (W / 2) * A + 2 * p.c ^ 2 * R ^ 2 / p.lambda₀ := by
      have hepsilonFactor : epsilon / (2 * p.α) = W / 2 := by
        dsimp only [epsilon]
        field_simp [model.α_pos.ne']
      simpa only [T, A, R, H, y, epsilon, W, hepsilonFactor] using heBound
    dsimp only [C₀] at hscalar ⊢
    linarith
  have hretreatScaled :
      (2 / p.α) *
          (∫ z in x₀.1..b, weightedBarrierIntegrand p rho z) ≤
        14 * L * (D ^ 2 + q ^ 2) := by
    have hdistanceD : weighted.βdagger - x₀.1 ≤
        D + 2 * p.α * q := by
      have hdecomp : weighted.βdagger - x₀.1 =
          D + (b - x₀.1) := by
        dsimp only [D]
        ring
      rw [hdecomp]
      linarith
    simpa only [D, beta] using
      scaled_weightedBarrierRetreatIntegral_le_quadratic
        model weighted hL model.α_pos halphaOne
          (beta := x₀.1) (b := b) (w := D) (q := q)
          hbeta hb hbetaB hD₀ hq hdistanceD hretreat
  let f := weightedBarrierIntegrand p rho
  have hcont : ContinuousOn f (Icc (0 : ℝ) weighted.βdagger) := by
    simpa only [f] using continuousOn_weightedBarrierIntegrand model rho weighted
  have htail :
      (∫ z in b..weighted.βdagger, weightedBarrierIntegrand p rho z) ≤
        (3 * L / 2) * D ^ 2 := by
    have hcell := integral_le_left_rectangle_add_lipschitz
      hcont hL hb ⟨weighted.βdagger_mem.1.le, le_rfl⟩ hb.2
    have hsaddle : f weighted.βdagger = 0 := by
      simp only [f, weightedBarrierIntegrand, weighted.gradient_zero, neg_zero]
    have hbarrier : 0 ≤ f b := by
      dsimp only [f]
      exact weighted.barrier_nonneg_before hb
    have hbound := hL.bound hb
      (show weighted.βdagger ∈ Icc (0 : ℝ) weighted.βdagger from
        ⟨weighted.βdagger_mem.1.le, le_rfl⟩)
    have hheight : f b ≤ L * D := by
      change |f b - f weighted.βdagger| ≤
        L * |b - weighted.βdagger| at hbound
      rw [hsaddle, sub_zero, abs_of_nonneg hbarrier,
        abs_of_nonpos (sub_nonpos.mpr hb.2)] at hbound
      dsimp only [D]
      linarith
    have hmul := mul_le_mul_of_nonneg_right hheight hD₀
    dsimp only [f, D] at hcell hmul ⊢
    nlinarith
  have hL₀ : 0 ≤ L := hL.nonneg
  have htailScaled :
      L * (∫ z in b..weighted.βdagger,
        weightedBarrierIntegrand p rho z) ≤
      (3 * L ^ 2 / 2) * D ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left htail hL₀
    calc
      L * (∫ z in b..weighted.βdagger,
          weightedBarrierIntegrand p rho z) ≤
          L * ((3 * L / 2) * D ^ 2) := hmul
      _ = (3 * L ^ 2 / 2) * D ^ 2 := by ring
  have hleftInt : IntervalIntegrable f MeasureTheory.volume x₀.1 b := by
    have hsubset : [[x₀.1, b]] ⊆ Icc (0 : ℝ) weighted.βdagger := by
      rw [uIcc_of_le hbetaB]
      intro z hz
      exact ⟨hbeta.1.trans hz.1, hz.2.trans hb.2⟩
    exact (hcont.mono hsubset).intervalIntegrable
  have hrightInt : IntervalIntegrable f MeasureTheory.volume b
      weighted.βdagger := by
    have hsubset : [[b, weighted.βdagger]] ⊆
        Icc (0 : ℝ) weighted.βdagger := by
      rw [uIcc_of_le hb.2]
      intro z hz
      exact ⟨hb.1.trans hz.1, hz.2⟩
    exact (hcont.mono hsubset).intervalIntegrable
  have hadd :
      (∫ z in x₀.1..b, f z) +
          (∫ z in b..weighted.βdagger, f z) =
        ∫ z in x₀.1..weighted.βdagger, f z :=
    intervalIntegral.integral_add_adjacent_intervals hleftInt hrightInt
  have hscaleEq := coupledCellFactor_div_eq_two_div_sub
    model.α_pos hsmall
  have hsplit :
      (2 / p.α) *
          (∫ z in x₀.1..weighted.βdagger, f z) =
        (2 / p.α) * (∫ z in x₀.1..b, f z) +
        (coupledCellFactor (p.α * L) / p.α) *
          (∫ z in b..weighted.βdagger, f z) +
        L * (∫ z in b..weighted.βdagger, f z) := by
    rw [← hadd, hscaleEq]
    ring
  have hC₀ : 0 ≤ C₀ :=
    (passageOneClimbQuadraticConstant_pos model weighted hL).le
  have hWsq : W ^ 2 ≤ 2 * (D ^ 2 + w ^ 2) := by
    dsimp only [W]
    nlinarith only [sq_nonneg (D - w)]
  have hlocal :
      C₀ * (W ^ 2 + q ^ 2) +
          14 * L * (D ^ 2 + q ^ 2) +
          (3 * L ^ 2 / 2) * D ^ 2 ≤
        C * (w ^ 2 + D ^ 2 + q ^ 2) := by
    have hCeq : C = 2 * C₀ + 14 * L + 2 * L ^ 2 := by
      rfl
    rw [hCeq]
    exact localOneClimbQuadratic_collect hC₀ hL₀ hWsq
  refine ⟨e, heMem, ?_⟩
  dsimp only [f] at hsplit
  rw [hsplit] at heReduced
  change e ≤ gaussianVectorAction u +
      (coupledCellFactor (p.α * L) / p.α) *
        (∫ z in b..weighted.βdagger,
          weightedBarrierIntegrand p rho z) +
      C * (w ^ 2 + D ^ 2 + q ^ 2)
  linarith only [heReduced, hretreatScaled, htailScaled, hlocal]

/-- The coefficient-weighted charge dominates the unweighted deficit mass
by the positive saddle coefficient. -/
theorem IsControlledCivicWeightedPathFrom.saddleCoefficient_mul_flooredDeficitMass_le_charge
    {p : LoopParams} {rho floor : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hfloor : floor ∈ Icc (0 : ℝ) weighted.βdagger)
    (hstart : x₀.1 ≤ floor)
    (hstock₀ : x₀.2 ≤ p.stationaryStock floor) (N : ℕ) :
    saddleStockCoefficient p weighted *
        flooredCappedDeficitMass p floor weighted.βdagger x N ≤
      flooredCappedDeficitCharge p rho floor weighted.βdagger x N := by
  let b : ℕ → ℝ := fun n ↦
    flooredCappedPolicyRunningMax floor weighted.βdagger x n
  have hfloorUnit : floor ∈ Icc (0 : ℝ) 1 :=
    ⟨hfloor.1, hfloor.2.trans weighted.βdagger_mem.2.le⟩
  rw [flooredCappedDeficitMass, flooredCappedDeficitCharge,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _hn
  have hmono : b n ≤ b (n + 1) :=
    monotone_flooredCappedPolicyRunningMax
      floor weighted.βdagger x n.le_succ
  rcases hmono.lt_or_eq with hadvance | heq
  · obtain ⟨hold, _hpolicy, _hnext⟩ :=
      flooredCappedRunningMax_advance_structure hadvance
    have hstock := path.stock_le_stationary_flooredRunningMax
      model ss hx₀ hfloorUnit hstart hstock₀ n
    have hlag : 0 ≤ p.stationaryStock (b n) - (x n).2 := by
      rw [show b n = flooredPolicyRunningMax floor x n from hold]
      exact sub_nonneg.mpr hstock
    have hbsegment := path.flooredCappedRunningMax_mem
      weighted hx₀.1 hfloor n
    have hbmem : b n ∈ Icc (0 : ℝ) weighted.βdagger :=
      ⟨hfloor.1.trans hbsegment.1, hbsegment.2⟩
    have hcoefficient := saddleStockCoefficient_le model weighted hbmem
    have hfirst := mul_le_mul_of_nonneg_right hcoefficient hlag
    have hdelta : 0 ≤ b (n + 1) - b n := sub_nonneg.mpr hmono
    have hsecond := mul_le_mul_of_nonneg_right hfirst hdelta
    simpa only [b, mul_assoc] using hsecond
  · have heqRaw :
        flooredCappedPolicyRunningMax floor weighted.βdagger x (n + 1) =
          flooredCappedPolicyRunningMax floor weighted.βdagger x n := by
      simpa only [b] using heq.symm
    rw [heqRaw, sub_self]
    norm_num

/-- Paper II, Proposition `prop:passage`, global burden budget for a crossing
path.  Its full deficit-plus-retreat mass is paid from the path-specific gap
above the coupled stationary barrier. -/
theorem IsControlledCivicWeightedPath.coupled_burdenMass_le_action_gap
    {p : LoopParams} {rho L : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPath p rho u x) {N : ℕ}
    (hcross : weighted.βdagger ≤ policyRunningMax x N) :
    (coupledCellFactor (p.α * L) / p.α) *
        flooredCappedBurdenMass p rho 0 weighted.βdagger x N ≤
      controlAction u N -
        (coupledCellFactor (p.α * L) / p.α) *
          weightedBarrierArea weighted := by
  let pathFrom := path.toFrom
  have hp₁mem : calibratedPoint p ∈ absorbingBox p :=
    ⟨by simp [calibratedPoint],
      stationaryStock_mem_stockInterval model (by norm_num)⟩
  have hfloor : (0 : ℝ) ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨le_rfl, weighted.βdagger_mem.1.le⟩
  have hstart : (calibratedPoint p).1 ≤ (0 : ℝ) := by
    change (0 : ℝ) ≤ 0
    exact le_rfl
  have hstock : (calibratedPoint p).2 ≤ p.stationaryStock 0 := by
    change p.stationaryStock 0 ≤ p.stationaryStock 0
    exact le_rfl
  have hledger := pathFrom.floored_coupled_barrier_add_burden_le_action
    model ss hcoop weighted hL hp₁mem hfloor hstart hstock hcross
  dsimp only [weightedBarrierArea] at hledger ⊢
  ring_nf at hledger ⊢
  linarith

/-- Paper II, Proposition `prop:passage`, global level budget for a crossing
path.  Its stock-deficit mass is paid entirely from the path-specific gap
above the coupled stationary barrier. -/
theorem IsControlledCivicWeightedPath.coupled_deficitMass_le_action_gap
    {p : LoopParams} {rho L : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPath p rho u x) {N : ℕ}
    (hcross : weighted.βdagger ≤ policyRunningMax x N) :
    (coupledCellFactor (p.α * L) / p.α) *
        saddleStockCoefficient p weighted *
          flooredCappedDeficitMass p 0 weighted.βdagger x N ≤
      controlAction u N -
        (coupledCellFactor (p.α * L) / p.α) *
          weightedBarrierArea weighted := by
  let pathFrom := path.toFrom
  have hp₁mem : calibratedPoint p ∈ absorbingBox p :=
    ⟨by simp [calibratedPoint],
      stationaryStock_mem_stockInterval model (by norm_num)⟩
  have hfloor : (0 : ℝ) ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨le_rfl, weighted.βdagger_mem.1.le⟩
  have hstart : (calibratedPoint p).1 ≤ (0 : ℝ) := by
    change (0 : ℝ) ≤ 0
    exact le_rfl
  have hstock : (calibratedPoint p).2 ≤ p.stationaryStock 0 := by
    change p.stationaryStock 0 ≤ p.stationaryStock 0
    exact le_rfl
  have hcharge := pathFrom.saddleCoefficient_mul_flooredDeficitMass_le_charge
    model ss weighted hp₁mem hfloor hstart hstock N
  have hledger := pathFrom.floored_coupled_barrier_add_deficit_le_action
    model ss hcoop weighted hL hp₁mem hfloor hstart hstock hcross
  let scale := coupledCellFactor (p.α * L) / p.α
  have hscale : 0 ≤ scale :=
    (div_pos (coupledCellFactor_pos (p.α * L)) model.α_pos).le
  have hscaled := mul_le_mul_of_nonneg_left hcharge hscale
  dsimp only [scale, weightedBarrierArea] at hscaled hledger ⊢
  ring_nf at hscaled hledger ⊢
  linarith

/-- A Lipschitz constant for the weighted barrier is necessarily strictly
positive: the barrier is positive at zero and vanishes at the saddle. -/
theorem lipschitzConstantOn_weightedBarrierIntegrand_pos
    {p : LoopParams} {rho L : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    0 < L := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨le_rfl, weighted.βdagger_mem.1.le⟩
  have hsaddle : weighted.βdagger ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨weighted.βdagger_mem.1.le, le_rfl⟩
  have hbound := hL.bound hzero hsaddle
  have hbarrierZero : 0 < weightedBarrierIntegrand p rho 0 := by
    simpa only [weightedBarrierIntegrand, neg_pos] using weighted.gradient_zero_neg
  have hbarrierSaddle :
      weightedBarrierIntegrand p rho weighted.βdagger = 0 := by
    simp only [weightedBarrierIntegrand, weighted.gradient_zero, neg_zero]
  rw [hbarrierSaddle, sub_zero, abs_of_pos hbarrierZero,
    zero_sub, abs_neg, abs_of_pos weighted.βdagger_mem.1] at hbound
  by_contra hnot
  have hzeroL : L = 0 := le_antisymm (not_lt.mp hnot) hL.nonneg
  rw [hzeroL, zero_mul] at hbound
  linarith

/-- One stopped-maximum cell pays the complete Lipschitz upper rectangle at
the improved coupled coefficient. -/
theorem IsControlledCivicWeightedPath.coupled_cell_integral_le_half_control_sq
    {p : LoopParams} {rho L : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPath p rho u x) (n : ℕ) :
    (coupledCellFactor (p.α * L) / p.α) *
        (∫ z in
          cappedPolicyRunningMax weighted.βdagger x n..
          cappedPolicyRunningMax weighted.βdagger x (n + 1),
          weightedBarrierIntegrand p rho z) ≤
      (u n) ^ 2 / 2 := by
  let b := cappedPolicyRunningMax weighted.βdagger x n
  let b' := cappedPolicyRunningMax weighted.βdagger x (n + 1)
  let a := weightedBarrierIntegrand p rho b
  let d := (b' - b) / p.α
  let t := p.α * L
  have hbmem := path.cappedRunningMax_mem weighted n
  have hb'mem := path.cappedRunningMax_mem weighted (n + 1)
  have hmono : b ≤ b' :=
    (monotone_cappedPolicyRunningMax weighted.βdagger x) n.le_succ
  have hfactor : 0 < coupledCellFactor t := coupledCellFactor_pos t
  have hscale : 0 ≤ coupledCellFactor t / p.α :=
    (div_pos hfactor model.α_pos).le
  have hcell := integral_le_left_rectangle_add_lipschitz
    (continuousOn_weightedBarrierIntegrand model rho weighted) hL
      hbmem hb'mem hmono
  have hcellRewritten :
      (∫ z in b..b', weightedBarrierIntegrand p rho z) ≤
        p.α * (a * d + (t / 2) * d ^ 2) := by
    calc
      (∫ z in b..b', weightedBarrierIntegrand p rho z) ≤
          a * (b' - b) + (L / 2) * (b' - b) ^ 2 := hcell
      _ = p.α * (a * d + (t / 2) * d ^ 2) := by
        dsimp only [a, d, t]
        field_simp [model.α_pos.ne']
  have hscaled := mul_le_mul_of_nonneg_left hcellRewritten hscale
  have hscaledEq :
      (coupledCellFactor t / p.α) *
          (p.α * (a * d + (t / 2) * d ^ 2)) =
        coupledCellFactor t * (a * d + (t / 2) * d ^ 2) := by
    field_simp [model.α_pos.ne']
  rw [hscaledEq] at hscaled
  rcases hmono.lt_or_eq with hadvance | heq
  · have hbBelow : b < weighted.βdagger :=
      hadvance.trans_le (min_le_left _ _)
    have ha : 0 ≤ a :=
      (weighted.barrier_pos_before hbmem hbBelow).le
    have hd : 0 ≤ d :=
      (div_nonneg (sub_nonneg.mpr hmono) model.α_pos.le)
    have hu := path.control_ge_barrier_add_advance
      model ss hcoop weighted hadvance
    have hcore := coupledCellFactor_mul_le_half_sq (t := t) ha hd hu
    exact hscaled.trans hcore
  · change (coupledCellFactor (p.α * L) / p.α) *
        (∫ z in b..b', weightedBarrierIntegrand p rho z) ≤
      (u n) ^ 2 / 2
    rw [← heq, intervalIntegral.integral_same, mul_zero]
    positivity

/-- Every finite prefix pays the coupled barrier up to its capped running
maximum. -/
theorem IsControlledCivicWeightedPath.coupled_action_lower_bound_to_cappedRunningMax
    {p : LoopParams} {rho L : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPath p rho u x) (N : ℕ) :
    (coupledCellFactor (p.α * L) / p.α) *
        (∫ z in (0 : ℝ)..cappedPolicyRunningMax weighted.βdagger x N,
          weightedBarrierIntegrand p rho z) ≤
      controlAction u N := by
  let b : ℕ → ℝ := fun n ↦ cappedPolicyRunningMax weighted.βdagger x n
  let f : ℝ → ℝ := weightedBarrierIntegrand p rho
  have hcont : ContinuousOn f (Icc (0 : ℝ) weighted.βdagger) :=
    continuousOn_weightedBarrierIntegrand model rho weighted
  have hbmem : ∀ n, b n ∈ Icc (0 : ℝ) weighted.βdagger :=
    fun n ↦ path.cappedRunningMax_mem weighted n
  have hbmono : ∀ n, b n ≤ b (n + 1) := fun n ↦
    (monotone_cappedPolicyRunningMax weighted.βdagger x) n.le_succ
  have hcellInt : ∀ n < N, IntervalIntegrable f MeasureTheory.volume
      (b n) (b (n + 1)) := by
    intro n _hn
    have hsubset : [[b n, b (n + 1)]] ⊆
        Icc (0 : ℝ) weighted.βdagger := by
      rw [uIcc_of_le (hbmono n)]
      intro z hz
      exact ⟨(hbmem n).1.trans hz.1, hz.2.trans (hbmem (n + 1)).2⟩
    exact (hcont.mono hsubset).intervalIntegrable
  have hadjacent :
      ∑ n ∈ Finset.range N, ∫ z in b n..b (n + 1), f z =
        ∫ z in b 0..b N, f z :=
    intervalIntegral.sum_integral_adjacent_intervals hcellInt
  have hstart : b 0 = 0 :=
    path.cappedRunningMax_zero weighted.βdagger_mem.1.le
  have hsum :
      ∑ n ∈ Finset.range N,
          (coupledCellFactor (p.α * L) / p.α) *
            (∫ z in b n..b (n + 1), f z) ≤
        ∑ n ∈ Finset.range N, (u n) ^ 2 / 2 := by
    apply Finset.sum_le_sum
    intro n _hn
    simpa only [b, f] using
      path.coupled_cell_integral_le_half_control_sq
        model ss hcoop weighted hL n
  calc
    (coupledCellFactor (p.α * L) / p.α) *
        (∫ z in (0 : ℝ)..cappedPolicyRunningMax weighted.βdagger x N,
          weightedBarrierIntegrand p rho z) =
        ∑ n ∈ Finset.range N,
          (coupledCellFactor (p.α * L) / p.α) *
            (∫ z in b n..b (n + 1), f z) := by
      rw [← Finset.mul_sum, hadjacent, hstart]
    _ ≤ ∑ n ∈ Finset.range N, (u n) ^ 2 / 2 := hsum
    _ = controlAction u N := by
      simp only [controlAction, div_eq_mul_inv, Finset.mul_sum]
      ring_nf

/-- A Lipschitz weighted barrier has a quadratic tail at its saddle root. -/
theorem weightedBarrierTail_le_three_halves_lipschitz
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho L b : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (hb : b ∈ Icc (0 : ℝ) weighted.βdagger) :
    (∫ z in b..weighted.βdagger, weightedBarrierIntegrand p rho z) ≤
      (3 * L / 2) * (weighted.βdagger - b) ^ 2 := by
  let f := weightedBarrierIntegrand p rho
  have hcont := continuousOn_weightedBarrierIntegrand model rho weighted
  have hcell := integral_le_left_rectangle_add_lipschitz
    hcont hL hb ⟨weighted.βdagger_mem.1.le, le_rfl⟩ hb.2
  have hsaddle : f weighted.βdagger = 0 := by
    simp only [f, weightedBarrierIntegrand, weighted.gradient_zero, neg_zero]
  have hbarrier : 0 ≤ f b := by
    dsimp only [f]
    exact weighted.barrier_nonneg_before hb
  have hbound := hL.bound hb
    (show weighted.βdagger ∈ Icc (0 : ℝ) weighted.βdagger from
      ⟨weighted.βdagger_mem.1.le, le_rfl⟩)
  have hheight : f b ≤ L * (weighted.βdagger - b) := by
    rw [show weightedBarrierIntegrand p rho b = f b from rfl,
      show weightedBarrierIntegrand p rho weighted.βdagger =
        f weighted.βdagger from rfl,
      hsaddle, sub_zero, abs_of_nonneg hbarrier,
      abs_of_nonpos (sub_nonpos.mpr hb.2)] at hbound
    linarith
  have hwidth : 0 ≤ weighted.βdagger - b := sub_nonneg.mpr hb.2
  have hmul := mul_le_mul_of_nonneg_right hheight hwidth
  dsimp only [f] at hcell hmul ⊢
  nlinarith

/-- Paper II, Proposition `prop:passage`, refined top-window step bound.
The squared advance of any selected cell is paid by the total action gap plus
the coupled barrier tail above its old level. -/
theorem IsControlledCivicWeightedPath.cappedAdvance_sq_le_actionGap_add_barrierTail
    {p : LoopParams} {rho L : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPath p rho u x) {n N : ℕ}
    (hn : n < N)
    (hadvance : cappedPolicyRunningMax weighted.βdagger x n <
      cappedPolicyRunningMax weighted.βdagger x (n + 1)) :
    (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
        cappedPolicyRunningMax weighted.βdagger x n) ^ 2 /
          (2 * p.α ^ 2) ≤
      controlAction u N -
          (2 / (p.α * (1 + 2 * p.α * L))) *
            weightedBarrierArea weighted +
        (coupledCellFactor (p.α * L) / p.α) *
          (∫ z in cappedPolicyRunningMax weighted.βdagger x n..
              weighted.βdagger,
            weightedBarrierIntegrand p rho z) := by
  let b := cappedPolicyRunningMax weighted.βdagger x n
  let b' := cappedPolicyRunningMax weighted.βdagger x (n + 1)
  let e := b' - b
  let f := weightedBarrierIntegrand p rho
  let scale := coupledCellFactor (p.α * L) / p.α
  have hbmem := path.cappedRunningMax_mem weighted n
  have hb'mem := path.cappedRunningMax_mem weighted (n + 1)
  have he : 0 < e := by simpa only [e, b, b'] using sub_pos.mpr hadvance
  have heRate : 0 ≤ e / p.α :=
    div_nonneg he.le model.α_pos.le
  have hbarrier : 0 ≤ f b := by
    dsimp only [f]
    exact weighted.barrier_nonneg_before hbmem
  have hu := path.control_ge_barrier_add_advance
    model ss hcoop weighted hadvance
  have huRate : e / p.α ≤ u n := by
    dsimp only [e, b, b']
    dsimp only [f] at hbarrier
    linarith
  have huNonneg : 0 ≤ u n := heRate.trans huRate
  have hsquare : (e / p.α) ^ 2 ≤ (u n) ^ 2 :=
    (sq_le_sq₀ heRate huNonneg).2 huRate
  have hstep : e ^ 2 / (2 * p.α ^ 2) ≤ (u n) ^ 2 / 2 := by
    have hsquare' : e ^ 2 / p.α ^ 2 ≤ (u n) ^ 2 := by
      simpa only [div_pow] using hsquare
    calc
      e ^ 2 / (2 * p.α ^ 2) = (e ^ 2 / p.α ^ 2) / 2 := by ring
      _ ≤ (u n) ^ 2 / 2 :=
        (div_le_div_iff_of_pos_right two_pos).2 hsquare'
  have hprefix := path.coupled_action_lower_bound_to_cappedRunningMax
    model ss hcoop weighted hL n
  have htotal := controlAction_add_next_le (u := u) hn
  have hpaid :
      scale * (∫ z in (0 : ℝ)..b, f z) +
          e ^ 2 / (2 * p.α ^ 2) ≤ controlAction u N := by
    have hsum :
        scale * (∫ z in (0 : ℝ)..b, f z) +
            e ^ 2 / (2 * p.α ^ 2) ≤
          controlAction u n + (u n) ^ 2 / 2 := by
      exact add_le_add (by simpa only [scale, b, f] using hprefix) hstep
    exact hsum.trans htotal
  have hcont : ContinuousOn f (Icc (0 : ℝ) weighted.βdagger) :=
    continuousOn_weightedBarrierIntegrand model rho weighted
  have hleftSubset : [[(0 : ℝ), b]] ⊆ Icc (0 : ℝ) weighted.βdagger := by
    rw [uIcc_of_le hbmem.1]
    intro z hz
    exact ⟨hz.1, hz.2.trans hbmem.2⟩
  have hrightSubset : [[b, weighted.βdagger]] ⊆
      Icc (0 : ℝ) weighted.βdagger := by
    rw [uIcc_of_le hbmem.2]
    intro z hz
    exact ⟨hbmem.1.trans hz.1, hz.2⟩
  have hleftInt : IntervalIntegrable f MeasureTheory.volume 0 b :=
    (hcont.mono hleftSubset).intervalIntegrable
  have hrightInt : IntervalIntegrable f MeasureTheory.volume b
      weighted.βdagger :=
    (hcont.mono hrightSubset).intervalIntegrable
  have hadd :
      (∫ z in (0 : ℝ)..b, f z) +
          (∫ z in b..weighted.βdagger, f z) =
        ∫ z in (0 : ℝ)..weighted.βdagger, f z :=
    intervalIntegral.integral_add_adjacent_intervals hleftInt hrightInt
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨le_rfl, weighted.βdagger_mem.1.le⟩
  have hsaddle : weighted.βdagger ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨weighted.βdagger_mem.1.le, le_rfl⟩
  have hLbound := hL.bound hzero hsaddle
  have hbarrierZero : 0 < weightedBarrierIntegrand p rho 0 := by
    simpa only [weightedBarrierIntegrand, neg_pos] using weighted.gradient_zero_neg
  have hbarrierSaddle :
      weightedBarrierIntegrand p rho weighted.βdagger = 0 := by
    simp only [weightedBarrierIntegrand, weighted.gradient_zero, neg_zero]
  rw [hbarrierSaddle, sub_zero, abs_of_pos hbarrierZero,
    zero_sub, abs_neg, abs_of_pos weighted.βdagger_mem.1] at hLbound
  have hLpos : 0 < L := by
    by_contra hnot
    have hzeroL : L = 0 := le_antisymm (not_lt.mp hnot) hL.nonneg
    rw [hzeroL, zero_mul] at hLbound
    linarith
  let t := p.α * L
  have htpos : 0 < t := by
    dsimp only [t]
    exact mul_pos model.α_pos hLpos
  have hden : 0 < 1 + 2 * t := by positivity
  have hfactor : 2 / (1 + 2 * t) < coupledCellFactor t :=
    correctedCellFactor_lt_coupledCellFactor htpos
  have hdiv :
      (2 / (1 + 2 * t)) / p.α ≤ coupledCellFactor t / p.α := by
    have hinv : 0 < 1 / p.α := one_div_pos.mpr model.α_pos
    have hdivStrict :
        (2 / (1 + 2 * t)) / p.α < coupledCellFactor t / p.α := by
      simpa only [div_eq_mul_inv, one_mul] using
        (mul_lt_mul_of_pos_right hfactor hinv)
    exact hdivStrict.le
  have hcoefficient :
      2 / (p.α * (1 + 2 * p.α * L)) ≤ scale := by
    calc
      2 / (p.α * (1 + 2 * p.α * L)) =
          (2 / (1 + 2 * t)) / p.α := by
        dsimp only [t]
        field_simp [model.α_pos.ne', hden.ne']
      _ ≤ coupledCellFactor t / p.α := hdiv
      _ = scale := by rfl
  have hfull := mul_le_mul_of_nonneg_right hcoefficient
    (weightedBarrierArea_pos model weighted).le
  have hfull' :
      (2 / (p.α * (1 + 2 * p.α * L))) *
          weightedBarrierArea weighted ≤
        scale * ((∫ z in (0 : ℝ)..b, f z) +
          ∫ z in b..weighted.βdagger, f z) := by
    dsimp only [weightedBarrierArea, scale, f] at hfull ⊢
    rw [hadd]
    exact hfull
  dsimp only [e, b, b', f, scale] at hpaid hfull' ⊢
  linarith

/-- Quadratic-tail form of the refined top-window step bound. -/
theorem IsControlledCivicWeightedPath.cappedAdvance_sq_le_actionGap_add_quadraticTail
    {p : LoopParams} {rho L : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPath p rho u x) {n N : ℕ}
    (hn : n < N)
    (hadvance : cappedPolicyRunningMax weighted.βdagger x n <
      cappedPolicyRunningMax weighted.βdagger x (n + 1)) :
    (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
        cappedPolicyRunningMax weighted.βdagger x n) ^ 2 /
          (2 * p.α ^ 2) ≤
      controlAction u N -
          (2 / (p.α * (1 + 2 * p.α * L))) *
            weightedBarrierArea weighted +
        (coupledCellFactor (p.α * L) / p.α) *
          ((3 * L / 2) *
            (weighted.βdagger -
              cappedPolicyRunningMax weighted.βdagger x n) ^ 2) := by
  have hmain := path.cappedAdvance_sq_le_actionGap_add_barrierTail
    model ss hcoop weighted hL hn hadvance
  have hbmem := path.cappedRunningMax_mem weighted n
  have htail := weightedBarrierTail_le_three_halves_lipschitz
    model weighted hL hbmem
  have hscale : 0 ≤ coupledCellFactor (p.α * L) / p.α :=
    (div_pos (coupledCellFactor_pos (p.α * L)) model.α_pos).le
  have hscaled := mul_le_mul_of_nonneg_left htail hscale
  linarith

/-- Every finite crossing control pays the full barrier at the coupled
coefficient. -/
theorem IsControlledCivicWeightedPath.coupled_action_lower_bound_of_crossing
    {p : LoopParams} {rho L : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPath p rho u x) {N : ℕ}
    (hcross : weighted.βdagger ≤ policyRunningMax x N) :
    (coupledCellFactor (p.α * L) / p.α) *
        (∫ z in (0 : ℝ)..weighted.βdagger,
          weightedBarrierIntegrand p rho z) ≤
      controlAction u N := by
  let b : ℕ → ℝ := fun n ↦ cappedPolicyRunningMax weighted.βdagger x n
  let f : ℝ → ℝ := weightedBarrierIntegrand p rho
  have hcont : ContinuousOn f (Icc (0 : ℝ) weighted.βdagger) :=
    continuousOn_weightedBarrierIntegrand model rho weighted
  have hbmem : ∀ n, b n ∈ Icc (0 : ℝ) weighted.βdagger :=
    fun n ↦ path.cappedRunningMax_mem weighted n
  have hbmono : ∀ n, b n ≤ b (n + 1) := fun n ↦
    (monotone_cappedPolicyRunningMax weighted.βdagger x) n.le_succ
  have hcellInt : ∀ n < N, IntervalIntegrable f MeasureTheory.volume
      (b n) (b (n + 1)) := by
    intro n _hn
    have hsubset : [[b n, b (n + 1)]] ⊆
        Icc (0 : ℝ) weighted.βdagger := by
      rw [uIcc_of_le (hbmono n)]
      intro z hz
      exact ⟨(hbmem n).1.trans hz.1, hz.2.trans (hbmem (n + 1)).2⟩
    exact (hcont.mono hsubset).intervalIntegrable
  have hadjacent :
      ∑ n ∈ Finset.range N, ∫ z in b n..b (n + 1), f z =
        ∫ z in b 0..b N, f z :=
    intervalIntegral.sum_integral_adjacent_intervals hcellInt
  have hstart : b 0 = 0 :=
    path.cappedRunningMax_zero weighted.βdagger_mem.1.le
  have hend : b N = weighted.βdagger :=
    cappedRunningMax_eq_target hcross
  have hsum :
      ∑ n ∈ Finset.range N,
          (coupledCellFactor (p.α * L) / p.α) *
            (∫ z in b n..b (n + 1), f z) ≤
        ∑ n ∈ Finset.range N, (u n) ^ 2 / 2 := by
    apply Finset.sum_le_sum
    intro n _hn
    simpa only [b, f] using
      path.coupled_cell_integral_le_half_control_sq
        model ss hcoop weighted hL n
  calc
    (coupledCellFactor (p.α * L) / p.α) *
        (∫ z in (0 : ℝ)..weighted.βdagger, f z) =
        ∑ n ∈ Finset.range N,
          (coupledCellFactor (p.α * L) / p.α) *
            (∫ z in b n..b (n + 1), f z) := by
      rw [← Finset.mul_sum, hadjacent, hstart, hend]
    _ ≤ ∑ n ∈ Finset.range N, (u n) ^ 2 / 2 := hsum
    _ = controlAction u N := by
      simp only [controlAction, div_eq_mul_inv, Finset.mul_sum]
      ring_nf

/-- The coupled pathwise bound passes to the crossing quasipotential. -/
theorem coupledBarrier_le_civicCrossingQuasipotential
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho L : ℝ}
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    (coupledCellFactor (p.α * L) / p.α) *
        weightedBarrierArea weighted ≤
      civicCrossingQuasipotential weighted := by
  change _ ≤ sInf (crossingActionSet weighted)
  apply le_csInf (crossingActionSet_nonempty model weighted)
  rintro a ⟨T, u, hcross, rfl⟩
  have path := finiteControlledOrbit_isControlled p rho u
  have haction := path.coupled_action_lower_bound_of_crossing
    model ss hcoop weighted hL hcross
  rwa [controlAction_extendFiniteControl] at haction

/-! ## What the fixed-parameter existential statement entails -/

/-- The coupled coefficient is strictly above the corrected coefficient in
`prop:qpbounds`, and the barrier area is strictly positive. -/
theorem correctedBarrier_lt_coupledBarrier
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho L : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    (2 / (p.α * (1 + 2 * p.α * L))) * weightedBarrierArea weighted <
      (coupledCellFactor (p.α * L) / p.α) *
        weightedBarrierArea weighted := by
  let t := p.α * L
  have hLpos := lipschitzConstantOn_weightedBarrierIntegrand_pos weighted hL
  have htpos : 0 < t := by
    dsimp only [t]
    exact mul_pos model.α_pos hLpos
  have hden : 0 < 1 + 2 * t := by positivity
  have hfactor : 2 / (1 + 2 * t) < coupledCellFactor t :=
    correctedCellFactor_lt_coupledCellFactor htpos
  have hdiv :
      (2 / (1 + 2 * t)) / p.α < coupledCellFactor t / p.α :=
    by
      have hinv : 0 < 1 / p.α := one_div_pos.mpr model.α_pos
      simpa only [div_eq_mul_inv, one_mul] using
        (mul_lt_mul_of_pos_right hfactor hinv)
  have harea := weightedBarrierArea_pos model weighted
  calc
    (2 / (p.α * (1 + 2 * p.α * L))) *
        weightedBarrierArea weighted =
        ((2 / (1 + 2 * t)) / p.α) * weightedBarrierArea weighted := by
      dsimp only [t]
      field_simp [model.α_pos.ne', hden.ne']
    _ < (coupledCellFactor t / p.α) * weightedBarrierArea weighted :=
      mul_lt_mul_of_pos_right hdiv harea
    _ = (coupledCellFactor (p.α * L) / p.α) *
        weightedBarrierArea weighted := by rfl

/-- Consequently the corrected lower bracket lies strictly below the actual
crossing quasipotential. -/
theorem correctedBarrier_lt_civicCrossingQuasipotential
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho L : ℝ}
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    (2 / (p.α * (1 + 2 * p.α * L))) *
        weightedBarrierArea weighted <
      civicCrossingQuasipotential weighted :=
  (correctedBarrier_lt_coupledBarrier model weighted hL).trans_le
    (coupledBarrier_le_civicCrossingQuasipotential
      model ss hcoop weighted hL)

/-- Paper II, Proposition `prop:passage`, level budget in the paper's
normalization.  The complete deficit mass of any crossing path is paid from its own
action gap above `V_-`; this is the quantitative input to the Selection step. -/
theorem IsControlledCivicWeightedPath.corrected_deficitMass_le_action_gap
    {p : LoopParams} {rho L : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPath p rho u x) {N : ℕ}
    (hcross : weighted.βdagger ≤ policyRunningMax x N) :
    (coupledCellFactor (p.α * L) / p.α) *
        saddleStockCoefficient p weighted *
          flooredCappedDeficitMass p 0 weighted.βdagger x N ≤
      controlAction u N -
        (2 / (p.α * (1 + 2 * p.α * L))) *
          weightedBarrierArea weighted := by
  have hmass := path.coupled_deficitMass_le_action_gap
    model ss hcoop weighted hL hcross
  have hbarrier := correctedBarrier_lt_coupledBarrier model weighted hL
  linarith

/-- The paper-normalized action gap also pays the complete
deficit-plus-retreat burden mass. -/
theorem IsControlledCivicWeightedPath.corrected_burdenMass_le_action_gap
    {p : LoopParams} {rho L : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPath p rho u x) {N : ℕ}
    (hcross : weighted.βdagger ≤ policyRunningMax x N) :
    (coupledCellFactor (p.α * L) / p.α) *
        flooredCappedBurdenMass p rho 0 weighted.βdagger x N ≤
      controlAction u N -
        (2 / (p.α * (1 + 2 * p.α * L))) *
          weightedBarrierArea weighted := by
  have hmass := path.coupled_burdenMass_le_action_gap
    model ss hcoop weighted hL hcross
  have hbarrier := correctedBarrier_lt_coupledBarrier model weighted hL
  linarith

/-! ## Finite-partition selection -/

/-- One cell of the stopped-maximum partition, retaining only its policy
width and the stock deficit charged on that width. -/
structure PassageSelectionCell where
  width : ℝ
  deficit : ℝ

/-- Total policy width of a finite selection ledger. -/
@[simp]
def passageSelectionWidth : List PassageSelectionCell → ℝ
  | [] => 0
  | cell :: cells => cell.width + passageSelectionWidth cells

/-- Total deficit mass of a finite selection ledger. -/
@[simp]
def passageSelectionMass : List PassageSelectionCell → ℝ
  | [] => 0
  | cell :: cells =>
      cell.deficit * cell.width + passageSelectionMass cells

/-- A dominated cell is a positive-width cell whose squared deficit is paid
by the deficit mass in its own suffix. -/
@[simp]
def HasDominatedPassageCell
    (a : ℝ) : List PassageSelectionCell → Prop
  | [] => False
  | cell :: cells =>
      (0 < cell.width ∧
        cell.deficit ^ 2 ≤
          a * passageSelectionMass (cell :: cells)) ∨
        HasDominatedPassageCell a cells

/-- Nonnegative cells have nonnegative total width. -/
theorem passageSelectionWidth_nonneg
    {cells : List PassageSelectionCell}
    (hnonneg : cells.Forall fun cell ↦
      0 ≤ cell.width ∧ 0 ≤ cell.deficit) :
    0 ≤ passageSelectionWidth cells := by
  induction cells with
  | nil =>
      simp only [passageSelectionWidth]
      exact le_rfl
  | cons cell cells ih =>
      simp only [List.forall_cons] at hnonneg
      simp only [passageSelectionWidth]
      exact add_nonneg hnonneg.1.1 (ih hnonneg.2)

/-- Nonnegative cells have nonnegative total deficit mass. -/
theorem passageSelectionMass_nonneg
    {cells : List PassageSelectionCell}
    (hnonneg : cells.Forall fun cell ↦
      0 ≤ cell.width ∧ 0 ≤ cell.deficit) :
    0 ≤ passageSelectionMass cells := by
  induction cells with
  | nil =>
      simp only [passageSelectionMass]
      exact le_rfl
  | cons cell cells ih =>
      simp only [List.forall_cons] at hnonneg
      simp only [passageSelectionMass]
      exact add_nonneg (mul_nonneg hnonneg.1.2 hnonneg.1.1)
        (ih hnonneg.2)

/-- Scalar square-root estimate behind the discrete Selection argument.  If
the head deficit is too large to be dominated by its suffix mass, that cell's
width consumes a corresponding drop in the square root of suffix mass. -/
theorem passageSelectionCell_sqrt_width_le
    {a d theta tailMass : ℝ}
    (ha : 0 < a) (hd : 0 < d) (htheta : 0 ≤ theta)
    (htail : 0 ≤ tailMass)
    (hfail : a * (theta * d + tailMass) < theta ^ 2) :
    Real.sqrt a * d ≤
      2 * (Real.sqrt (theta * d + tailMass) - Real.sqrt tailMass) := by
  let totalMass := theta * d + tailMass
  have hthetaPos : 0 < theta := by
    have hleft : 0 ≤ a * totalMass := by
      apply mul_nonneg ha.le
      dsimp only [totalMass]
      exact add_nonneg (mul_nonneg htheta hd.le) htail
    dsimp only [totalMass] at hfail hleft
    nlinarith [sq_nonneg theta]
  have htotal : 0 < totalMass := by
    dsimp only [totalMass]
    exact add_pos_of_pos_of_nonneg (mul_pos hthetaPos hd) htail
  have htailLe : tailMass ≤ totalMass := by
    dsimp only [totalMass]
    exact le_add_of_nonneg_left (mul_nonneg htheta hd.le)
  have hsqrtTailLe : Real.sqrt tailMass ≤ Real.sqrt totalMass :=
    Real.sqrt_le_sqrt htailLe
  have hsqrtProductLt : Real.sqrt a * Real.sqrt totalMass < theta := by
    rw [← Real.sqrt_mul ha.le]
    rw [← Real.sqrt_sq htheta]
    exact Real.sqrt_lt_sqrt (mul_nonneg ha.le htotal.le) (by
      simpa only [totalMass] using hfail)
  have hsqrtA : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hsumLt : Real.sqrt a *
      (Real.sqrt totalMass + Real.sqrt tailMass) < 2 * theta := by
    have hsecond := mul_le_mul_of_nonneg_left hsqrtTailLe hsqrtA
    nlinarith
  have hsumPos :
      0 < Real.sqrt totalMass + Real.sqrt tailMass :=
    add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 htotal)
      (Real.sqrt_nonneg tailMass)
  have hsqrtIdentity :
      (Real.sqrt totalMass - Real.sqrt tailMass) *
          (Real.sqrt totalMass + Real.sqrt tailMass) = theta * d := by
    have htotalSq := Real.sq_sqrt htotal.le
    have htailSq := Real.sq_sqrt htail
    dsimp only [totalMass] at htotalSq ⊢
    nlinarith
  have hmul :
      (Real.sqrt a * d) *
          (Real.sqrt totalMass + Real.sqrt tailMass) ≤
        (2 * (Real.sqrt totalMass - Real.sqrt tailMass)) *
          (Real.sqrt totalMass + Real.sqrt tailMass) := by
    calc
      (Real.sqrt a * d) *
          (Real.sqrt totalMass + Real.sqrt tailMass) =
          (Real.sqrt a *
            (Real.sqrt totalMass + Real.sqrt tailMass)) * d := by ring
      _ ≤ (2 * theta) * d :=
        mul_le_mul_of_nonneg_right hsumLt.le hd.le
      _ = (2 * (Real.sqrt totalMass - Real.sqrt tailMass)) *
          (Real.sqrt totalMass + Real.sqrt tailMass) := by
        calc
          (2 * theta) * d = 2 * (theta * d) := by ring
          _ = 2 * ((Real.sqrt totalMass - Real.sqrt tailMass) *
              (Real.sqrt totalMass + Real.sqrt tailMass)) := by
            rw [hsqrtIdentity]
          _ = _ := by ring
  exact le_of_mul_le_mul_right hmul hsumPos

/-- If no cell is dominated, the total width is at most twice the square
root of total deficit mass divided by the square root of the comparison
coefficient.  This is the finite, exact counterpart of integrating
`(sqrt T)'`. -/
theorem sqrt_mul_passageSelectionWidth_le_of_not_dominated
    {a : ℝ} {cells : List PassageSelectionCell}
    (ha : 0 < a)
    (hnonneg : cells.Forall fun cell ↦
      0 ≤ cell.width ∧ 0 ≤ cell.deficit)
    (hnot : ¬HasDominatedPassageCell a cells) :
    Real.sqrt a * passageSelectionWidth cells ≤
      2 * Real.sqrt (passageSelectionMass cells) := by
  induction cells with
  | nil =>
      simp only [passageSelectionWidth, passageSelectionMass, Real.sqrt_zero,
        mul_zero]
      exact le_rfl
  | cons cell cells ih =>
      simp only [List.forall_cons] at hnonneg
      have hnotHead : ¬(0 < cell.width ∧
          cell.deficit ^ 2 ≤
            a * passageSelectionMass (cell :: cells)) := by
        intro hhead
        exact hnot (by
          simp only [HasDominatedPassageCell]
          exact Or.inl hhead)
      have hnotTail : ¬HasDominatedPassageCell a cells := by
        intro htail
        exact hnot (by
          simp only [HasDominatedPassageCell]
          exact Or.inr htail)
      have htailBound := ih hnonneg.2 hnotTail
      by_cases hwidth : cell.width = 0
      · simp only [passageSelectionWidth, passageSelectionMass, hwidth,
          mul_zero, zero_add]
        exact htailBound
      · have hwidthPos : 0 < cell.width :=
          lt_of_le_of_ne hnonneg.1.1 (Ne.symm hwidth)
        have hfail :
            a * passageSelectionMass (cell :: cells) < cell.deficit ^ 2 :=
          lt_of_not_ge fun hle ↦ hnotHead ⟨hwidthPos, hle⟩
        have hcellBound := passageSelectionCell_sqrt_width_le
          ha hwidthPos hnonneg.1.2
            (passageSelectionMass_nonneg hnonneg.2)
            (by simpa only [passageSelectionMass] using hfail)
        simp only [passageSelectionWidth, passageSelectionMass]
        calc
          Real.sqrt a * (cell.width + passageSelectionWidth cells) =
              Real.sqrt a * cell.width +
                Real.sqrt a * passageSelectionWidth cells := by ring
          _ ≤ 2 * (Real.sqrt
                (cell.deficit * cell.width + passageSelectionMass cells) -
                  Real.sqrt (passageSelectionMass cells)) +
              2 * Real.sqrt (passageSelectionMass cells) :=
            add_le_add hcellBound htailBound
          _ = 2 * Real.sqrt
              (cell.deficit * cell.width + passageSelectionMass cells) := by ring

/-- Paper II, Proposition `prop:passage`, Selection step on a finite stopped-
maximum partition.  If total deficit mass is below `a W²/4`, some positive-
width cell has squared deficit controlled by its own suffix refund. -/
theorem exists_dominatedPassageCell_of_mass_lt
    {a : ℝ} {cells : List PassageSelectionCell}
    (ha : 0 < a)
    (hnonneg : cells.Forall fun cell ↦
      0 ≤ cell.width ∧ 0 ≤ cell.deficit)
    (hwidth : 0 < passageSelectionWidth cells)
    (hmass : passageSelectionMass cells <
      a * passageSelectionWidth cells ^ 2 / 4) :
    HasDominatedPassageCell a cells := by
  by_contra hnot
  have hbound := sqrt_mul_passageSelectionWidth_le_of_not_dominated
    ha hnonneg hnot
  have hmassNonneg := passageSelectionMass_nonneg hnonneg
  have hleftNonneg :
      0 ≤ Real.sqrt a * passageSelectionWidth cells :=
    mul_nonneg (Real.sqrt_nonneg a) hwidth.le
  have hrightNonneg :
      0 ≤ 2 * Real.sqrt (passageSelectionMass cells) :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hsquare := (sq_le_sq₀ hleftNonneg hrightNonneg).2 hbound
  have hsqrtA := Real.sq_sqrt ha.le
  have hsqrtMass := Real.sq_sqrt hmassNonneg
  nlinarith

/-- A dominated-cell witness carries an explicit list index and its literal
suffix.  This form is used to recover the corresponding control time. -/
theorem HasDominatedPassageCell.exists_index
    {a : ℝ} {cells : List PassageSelectionCell}
    (hdominated : HasDominatedPassageCell a cells) :
    ∃ (k : ℕ) (hk : k < cells.length),
      0 < (cells[k]).width ∧
        (cells[k]).deficit ^ 2 ≤
          a * passageSelectionMass (cells.drop k) := by
  induction cells with
  | nil => simp only [HasDominatedPassageCell] at hdominated
  | cons cell cells ih =>
      simp only [HasDominatedPassageCell] at hdominated
      rcases hdominated with hhead | htail
      · refine ⟨0, by simp only [List.length_cons]; omega, ?_, ?_⟩
        · simpa only [List.getElem_cons_zero] using hhead.1
        · simpa only [List.getElem_cons_zero, List.drop_zero] using hhead.2
      · obtain ⟨k, hk, hwidth, hbound⟩ := ih htail
        refine ⟨k + 1, by simp only [List.length_cons]; omega, ?_, ?_⟩
        · simpa only [List.getElem_cons_succ] using hwidth
        · simpa only [List.getElem_cons_succ, List.drop_succ_cons] using hbound

/-- Summing widths of a function-generated cell list is the corresponding
finite sum. -/
theorem passageSelectionWidth_ofFn
    {N : ℕ} (cells : Fin N → PassageSelectionCell) :
    passageSelectionWidth (List.ofFn cells) = ∑ n, (cells n).width := by
  induction N with
  | zero => simp only [List.ofFn_zero, passageSelectionWidth, Finset.univ_eq_empty,
      Finset.sum_empty]
  | succ N ih =>
      rw [List.ofFn_succ]
      simp only [passageSelectionWidth, Fin.sum_univ_succ]
      rw [ih]

/-- Summing masses of a function-generated cell list is the corresponding
finite sum. -/
theorem passageSelectionMass_ofFn
    {N : ℕ} (cells : Fin N → PassageSelectionCell) :
    passageSelectionMass (List.ofFn cells) =
      ∑ n, (cells n).deficit * (cells n).width := by
  induction N with
  | zero => simp only [List.ofFn_zero, passageSelectionMass, Finset.univ_eq_empty,
      Finset.sum_empty]
  | succ N ih =>
      rw [List.ofFn_succ]
      simp only [passageSelectionMass, Fin.sum_univ_succ]
      rw [ih]

/-- Projection of a real level onto a closed policy window. -/
def passageWindowClamp (lo hi z : ℝ) : ℝ :=
  min hi (max lo z)

/-- Window projection is monotone. -/
theorem monotone_passageWindowClamp (lo hi : ℝ) :
    Monotone (passageWindowClamp lo hi) := by
  intro x y hxy
  exact min_le_min_left hi (max_le_max_left lo hxy)

/-- A level below the window projects to its lower endpoint. -/
theorem passageWindowClamp_eq_lo
    {lo hi z : ℝ} (hlohi : lo ≤ hi) (hz : z ≤ lo) :
    passageWindowClamp lo hi z = lo := by
  simp only [passageWindowClamp, max_eq_left hz, min_eq_right hlohi]

/-- A level above the window projects to its upper endpoint. -/
theorem passageWindowClamp_eq_hi
    {lo hi z : ℝ} (hlohi : lo ≤ hi) (hz : hi ≤ z) :
    passageWindowClamp lo hi z = hi := by
  have hloz : lo ≤ z := hlohi.trans hz
  simp only [passageWindowClamp, max_eq_right hloz, min_eq_left hz]

/-- Window projection is one-Lipschitz on an ordered pair. -/
theorem passageWindowClamp_sub_le
    {lo hi x y : ℝ} (hxy : x ≤ y) :
    passageWindowClamp lo hi y - passageWindowClamp lo hi x ≤ y - x := by
  have hmax : |max lo y - max lo x| ≤ |y - x| := by
    simpa only [max_comm] using abs_max_sub_max_le_abs y x lo
  have hmin :
      |min hi (max lo y) - min hi (max lo x)| ≤
        |max lo y - max lo x| := by
    calc
      |min hi (max lo y) - min hi (max lo x)| ≤
          max |hi - hi| |max lo y - max lo x| :=
        abs_min_sub_min_le_max hi (max lo y) hi (max lo x)
      _ = |max lo y - max lo x| := by
        simp only [sub_self, abs_zero, max_eq_right, abs_nonneg]
  have habs :
      |passageWindowClamp lo hi y - passageWindowClamp lo hi x| ≤
        |y - x| := by
    simp only [passageWindowClamp]
    exact hmin.trans hmax
  have hclamp : passageWindowClamp lo hi x ≤ passageWindowClamp lo hi y :=
    monotone_passageWindowClamp lo hi hxy
  rw [abs_of_nonneg (sub_nonneg.mpr hclamp),
    abs_of_nonneg (sub_nonneg.mpr hxy)] at habs
  exact habs

/-- A strict increase of the clipped coordinate straddles the window: the
old point is below the upper endpoint and the new point is above the lower
endpoint. -/
theorem passageWindowClamp_strict_sub_order
    {lo hi x y : ℝ} (hlohi : lo ≤ hi)
    (hstrict : 0 < passageWindowClamp lo hi y -
      passageWindowClamp lo hi x) :
    x < hi ∧ lo < y := by
  constructor
  · by_contra hnot
    have hhiX : hi ≤ x := le_of_not_gt hnot
    have hhiY : hi ≤ y := by
      by_contra hnotY
      have hyhi : y < hi := lt_of_not_ge hnotY
      have hclampY : passageWindowClamp lo hi y ≤ hi := min_le_left _ _
      have hclampX : passageWindowClamp lo hi x = hi :=
        passageWindowClamp_eq_hi hlohi hhiX
      rw [hclampX] at hstrict
      linarith
    rw [passageWindowClamp_eq_hi hlohi hhiX,
      passageWindowClamp_eq_hi hlohi hhiY, sub_self] at hstrict
    exact (lt_irrefl 0 hstrict).elim
  · by_contra hnot
    have hyLo : y ≤ lo := le_of_not_gt hnot
    have hxLo : x ≤ lo := by
      by_contra hnotX
      have hloX : lo < x := lt_of_not_ge hnotX
      have hclampX : lo ≤ passageWindowClamp lo hi x := by
        simp only [passageWindowClamp]
        exact le_min hlohi (le_max_left lo x)
      have hclampY : passageWindowClamp lo hi y = lo :=
        passageWindowClamp_eq_lo hlohi hyLo
      rw [hclampY] at hstrict
      linarith
    rw [passageWindowClamp_eq_lo hlohi hyLo,
      passageWindowClamp_eq_lo hlohi hxLo, sub_self] at hstrict
    exact (lt_irrefl 0 hstrict).elim

/-- The middle-window cells cut from a crossing path's stopped-maximum
partition.  Deficits are truncated at zero only to make zero-width cells
harmless; every positive-width cell is an actual advancing cell and hence has
nonnegative untruncated deficit. -/
def passageWindowCells
    (p : LoopParams) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    (x : ℕ → LoopState) (lo hi : ℝ) (N : ℕ) :
    List PassageSelectionCell :=
  List.ofFn fun n : Fin N ↦
    let b := flooredCappedPolicyRunningMax 0 weighted.βdagger x n
    let b' := flooredCappedPolicyRunningMax 0 weighted.βdagger x (n + 1)
    { width := passageWindowClamp lo hi b' - passageWindowClamp lo hi b
      deficit := max (p.stationaryStock b - (x n).2) 0 }

/-- Every path window cell has nonnegative width and deficit. -/
theorem passageWindowCells_nonnegative
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    (x : ℕ → LoopState) {lo hi : ℝ} (N : ℕ) :
    (passageWindowCells p weighted x lo hi N).Forall fun cell ↦
      0 ≤ cell.width ∧ 0 ≤ cell.deficit := by
  rw [List.forall_iff_forall_mem]
  unfold passageWindowCells
  rw [List.forall_mem_ofFn_iff]
  intro n
  let b := flooredCappedPolicyRunningMax 0 weighted.βdagger x n
  let b' := flooredCappedPolicyRunningMax 0 weighted.βdagger x (n + 1)
  have hmono : b ≤ b' :=
    monotone_flooredCappedPolicyRunningMax
      0 weighted.βdagger x (Nat.le_succ (n : ℕ))
  change 0 ≤ passageWindowClamp lo hi b' - passageWindowClamp lo hi b ∧
    0 ≤ max (p.stationaryStock b - (x n).2) 0
  exact ⟨sub_nonneg.mpr (monotone_passageWindowClamp lo hi hmono),
    le_max_right _ _⟩

/-- A crossing path's clipped middle-window cells have exactly the geometric
width of that window. -/
theorem IsControlledCivicWeightedPath.passageWindowCells_width
    {p : LoopParams} {rho lo hi : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPath p rho u x)
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi)
    (hhi : hi ≤ weighted.βdagger) {N : ℕ}
    (hcross : weighted.βdagger ≤ policyRunningMax x N) :
    passageSelectionWidth (passageWindowCells p weighted x lo hi N) =
      hi - lo := by
  let b : ℕ → ℝ := fun n ↦
    flooredCappedPolicyRunningMax 0 weighted.βdagger x n
  let z : ℕ → ℝ := fun n ↦ passageWindowClamp lo hi (b n)
  have hfloor : (0 : ℝ) ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨le_rfl, weighted.βdagger_mem.1.le⟩
  have hstart : (calibratedPoint p).1 ≤ (0 : ℝ) := by
    change (0 : ℝ) ≤ 0
    exact le_rfl
  have hbzero : b 0 = 0 :=
    path.toFrom.flooredCappedRunningMax_zero weighted hfloor.2 hstart
  have hbN : b N = weighted.βdagger :=
    flooredCappedRunningMax_eq_target hcross
  have hz0 : z 0 = lo := by
    dsimp only [z]
    rw [passageWindowClamp_eq_lo hlohi (by simpa only [b, hbzero] using hlo)]
  have hzN : z N = hi := by
    dsimp only [z]
    rw [passageWindowClamp_eq_hi hlohi (by simpa only [b, hbN] using hhi)]
  rw [passageWindowCells, passageSelectionWidth_ofFn]
  have htel := Finset.sum_range_sub z N
  rw [hz0, hzN] at htel
  rw [← Fin.sum_univ_eq_sum_range] at htel
  simpa only [z, b] using htel

/-- The clipped window mass is no larger than the complete deficit mass in
the stopped-maximum ledger. -/
theorem IsControlledCivicWeightedPath.passageWindowCells_mass_le
    {p : LoopParams} {rho lo hi : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPath p rho u x) (N : ℕ) :
    passageSelectionMass (passageWindowCells p weighted x lo hi N) ≤
      flooredCappedDeficitMass p 0 weighted.βdagger x N := by
  let b : ℕ → ℝ := fun n ↦
    flooredCappedPolicyRunningMax 0 weighted.βdagger x n
  have hp₁mem : calibratedPoint p ∈ absorbingBox p :=
    ⟨by simp [calibratedPoint],
      stationaryStock_mem_stockInterval model (by norm_num)⟩
  have hfloor : (0 : ℝ) ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨le_rfl, weighted.βdagger_mem.1.le⟩
  have hfloorUnit : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hstart : (calibratedPoint p).1 ≤ (0 : ℝ) := by
    change (0 : ℝ) ≤ 0
    exact le_rfl
  have hstock₀ : (calibratedPoint p).2 ≤ p.stationaryStock 0 := by
    change p.stationaryStock 0 ≤ p.stationaryStock 0
    exact le_rfl
  rw [passageWindowCells, passageSelectionMass_ofFn,
    flooredCappedDeficitMass]
  conv_rhs => rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_le_sum
  intro n _hn
  have hmono : b n ≤ b (n + 1) :=
    monotone_flooredCappedPolicyRunningMax
      0 weighted.βdagger x (Nat.le_succ (n : ℕ))
  rcases hmono.lt_or_eq with hadvance | heq
  · obtain ⟨hold, _hpolicy, _hnext⟩ :=
      flooredCappedRunningMax_advance_structure hadvance
    have hstock := path.toFrom.stock_le_stationary_flooredRunningMax
      model ss hp₁mem hfloorUnit hstart hstock₀ n
    have hlag : 0 ≤ p.stationaryStock (b n) - (x n).2 := by
      rw [show b n = flooredPolicyRunningMax 0 x n from hold]
      exact sub_nonneg.mpr hstock
    have hclampDelta :
        passageWindowClamp lo hi (b (n + 1)) -
            passageWindowClamp lo hi (b n) ≤ b (n + 1) - b n :=
      passageWindowClamp_sub_le hmono
    have hclampNonneg : 0 ≤
        passageWindowClamp lo hi (b (n + 1)) -
          passageWindowClamp lo hi (b n) :=
      sub_nonneg.mpr (monotone_passageWindowClamp lo hi hmono)
    have hmul := mul_le_mul_of_nonneg_left hclampDelta hlag
    simpa only [b, max_eq_left hlag, mul_comm] using hmul
  · have heqRaw :
        flooredCappedPolicyRunningMax 0 weighted.βdagger x (n + 1) =
          flooredCappedPolicyRunningMax 0 weighted.βdagger x n := by
      simpa only [b] using heq.symm
    rw [heqRaw, sub_self]
    norm_num

/-- Paper II, Proposition `prop:passage`, discrete Selection step for an
actual crossing path.  A sufficiently small global deficit budget produces
a dominated positive-width cell inside any prescribed middle window. -/
theorem IsControlledCivicWeightedPath.hasDominatedPassageWindowCell
    {p : LoopParams} {rho lo hi a : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPath p rho u x)
    (ha : 0 < a) (hlo : 0 ≤ lo) (hlohi : lo < hi)
    (hhi : hi ≤ weighted.βdagger) {N : ℕ}
    (hcross : weighted.βdagger ≤ policyRunningMax x N)
    (hbudget : flooredCappedDeficitMass p 0 weighted.βdagger x N <
      a * (hi - lo) ^ 2 / 4) :
    HasDominatedPassageCell a
      (passageWindowCells p weighted x lo hi N) := by
  let cells := passageWindowCells p weighted x lo hi N
  have hnonneg := passageWindowCells_nonnegative
    weighted x (lo := lo) (hi := hi) N
  have hwidthEq := path.passageWindowCells_width
    weighted hlo hlohi.le hhi hcross
  have hwidth : 0 < passageSelectionWidth cells := by
    simpa only [cells, hwidthEq] using sub_pos.mpr hlohi
  have hmassLe := path.passageWindowCells_mass_le
    model ss weighted (lo := lo) (hi := hi) N
  apply exists_dominatedPassageCell_of_mass_lt ha hnonneg hwidth
  rw [hwidthEq]
  exact hmassLe.trans_lt hbudget

/-- Paper II, Proposition `prop:passage`, Selection step in action-gap form.
The refined ledger converts a sufficiently small path-specific gap above
`V_-` directly into a dominated cell in the chosen top window. -/
theorem IsControlledCivicWeightedPath.hasDominatedPassageWindowCell_of_actionGap_lt
    {p : LoopParams} {rho L lo hi a : ℝ}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPath p rho u x)
    (ha : 0 < a) (hlo : 0 ≤ lo) (hlohi : lo < hi)
    (hhi : hi ≤ weighted.βdagger) {N : ℕ}
    (hcross : weighted.βdagger ≤ policyRunningMax x N)
    (hgap :
      controlAction u N -
          (2 / (p.α * (1 + 2 * p.α * L))) *
            weightedBarrierArea weighted <
        ((coupledCellFactor (p.α * L) / p.α) *
          saddleStockCoefficient p weighted) *
          (a * (hi - lo) ^ 2 / 4)) :
    HasDominatedPassageCell a
      (passageWindowCells p weighted x lo hi N) := by
  let coefficient :=
    (coupledCellFactor (p.α * L) / p.α) *
      saddleStockCoefficient p weighted
  have hcoefficient : 0 < coefficient :=
    mul_pos
      (div_pos (coupledCellFactor_pos (p.α * L)) model.α_pos)
      (saddleStockCoefficient_pos model weighted)
  have hmassScaled := path.corrected_deficitMass_le_action_gap
    model ss hcoop weighted hL hcross
  have hmassStrict : coefficient *
      flooredCappedDeficitMass p 0 weighted.βdagger x N <
        coefficient * (a * (hi - lo) ^ 2 / 4) := by
    dsimp only [coefficient] at hmassScaled hgap ⊢
    exact hmassScaled.trans_lt hgap
  have hmass : flooredCappedDeficitMass p 0 weighted.βdagger x N <
      a * (hi - lo) ^ 2 / 4 :=
    (mul_lt_mul_iff_right₀ hcoefficient).mp hmassStrict
  exact path.hasDominatedPassageWindowCell
    model ss weighted ha hlo hlohi hhi hcross hmass

/-- A dominated window-cell witness yields an actual advancing control step,
with the untruncated own-level deficit controlled by the literal suffix mass
of the clipped partition. -/
theorem IsControlledCivicWeightedPath.exists_dominatedPassageWindowStep
    {p : LoopParams} {rho lo hi a : ℝ}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPath p rho u x) {N : ℕ}
    (hdominated : HasDominatedPassageCell a
      (passageWindowCells p weighted x lo hi N)) :
    ∃ n < N,
      flooredCappedPolicyRunningMax 0 weighted.βdagger x n <
          flooredCappedPolicyRunningMax 0 weighted.βdagger x (n + 1) ∧
        0 < passageWindowClamp lo hi
              (flooredCappedPolicyRunningMax 0 weighted.βdagger x (n + 1)) -
            passageWindowClamp lo hi
              (flooredCappedPolicyRunningMax 0 weighted.βdagger x n) ∧
        (p.stationaryStock
              (flooredCappedPolicyRunningMax 0 weighted.βdagger x n) -
            (x n).2) ^ 2 ≤
          a * passageSelectionMass
            ((passageWindowCells p weighted x lo hi N).drop n) := by
  let cells := passageWindowCells p weighted x lo hi N
  obtain ⟨n, hn, hwidth, hbound⟩ := hdominated.exists_index
  have hlength : cells.length = N := by
    simp only [cells, passageWindowCells, List.length_ofFn]
  have hnN : n < N := by
    rw [← hlength]
    exact hn
  let b : ℕ → ℝ := fun k ↦
    flooredCappedPolicyRunningMax 0 weighted.βdagger x k
  have hwidth' :
      0 < passageWindowClamp lo hi (b (n + 1)) -
        passageWindowClamp lo hi (b n) := by
    simpa only [cells, passageWindowCells, List.getElem_ofFn, b] using hwidth
  have hmono : b n ≤ b (n + 1) :=
    monotone_flooredCappedPolicyRunningMax
      0 weighted.βdagger x n.le_succ
  have hadvance : b n < b (n + 1) := by
    rcases hmono.lt_or_eq with hlt | heq
    · exact hlt
    · rw [← heq, sub_self] at hwidth'
      exact (lt_irrefl 0 hwidth').elim
  obtain ⟨hold, _hpolicy, _hnext⟩ :=
    flooredCappedRunningMax_advance_structure hadvance
  have hp₁mem : calibratedPoint p ∈ absorbingBox p :=
    ⟨by simp [calibratedPoint],
      stationaryStock_mem_stockInterval model (by norm_num)⟩
  have hfloorUnit : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hstart : (calibratedPoint p).1 ≤ (0 : ℝ) := by
    change (0 : ℝ) ≤ 0
    exact le_rfl
  have hstock₀ : (calibratedPoint p).2 ≤ p.stationaryStock 0 := by
    change p.stationaryStock 0 ≤ p.stationaryStock 0
    exact le_rfl
  have hstock := path.toFrom.stock_le_stationary_flooredRunningMax
    model ss hp₁mem hfloorUnit hstart hstock₀ n
  have hlag : 0 ≤ p.stationaryStock (b n) - (x n).2 := by
    rw [show b n = flooredPolicyRunningMax 0 x n from hold]
    exact sub_nonneg.mpr hstock
  have hbound' :
      (max (p.stationaryStock (b n) - (x n).2) 0) ^ 2 ≤
        a * passageSelectionMass (cells.drop n) := by
    simpa only [cells, passageWindowCells, List.getElem_ofFn, b] using hbound
  rw [max_eq_left hlag] at hbound'
  refine ⟨n, hnN, ?_, hwidth', ?_⟩
  · simpa only [b] using hadvance
  · simpa only [b, cells] using hbound'

/-! ## Burden-aware finite selection -/

/-- Window cells carrying the complete deficit-plus-retreat burden. -/
def passageBurdenWindowCells
    (p : LoopParams) (rho : ℝ)
    (weighted : WeightedThresholdAssumption p rho)
    (x : ℕ → LoopState) (lo hi : ℝ) (N : ℕ) :
    List PassageSelectionCell :=
  List.ofFn fun n : Fin N ↦
    let b := flooredCappedPolicyRunningMax 0 weighted.βdagger x n
    let b' := flooredCappedPolicyRunningMax 0 weighted.βdagger x (n + 1)
    { width := passageWindowClamp lo hi b' - passageWindowClamp lo hi b
      deficit := max (passageCellBurden p rho b (x n).1 (x n).2) 0 }

/-- Every burden-window cell is componentwise nonnegative. -/
theorem passageBurdenWindowCells_nonnegative
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    (x : ℕ → LoopState) {lo hi : ℝ} (N : ℕ) :
    (passageBurdenWindowCells p rho weighted x lo hi N).Forall fun cell ↦
      0 ≤ cell.width ∧ 0 ≤ cell.deficit := by
  rw [List.forall_iff_forall_mem]
  unfold passageBurdenWindowCells
  rw [List.forall_mem_ofFn_iff]
  intro n
  let b := flooredCappedPolicyRunningMax 0 weighted.βdagger x n
  let b' := flooredCappedPolicyRunningMax 0 weighted.βdagger x (n + 1)
  have hmono : b ≤ b' :=
    monotone_flooredCappedPolicyRunningMax
      0 weighted.βdagger x (Nat.le_succ (n : ℕ))
  change 0 ≤ passageWindowClamp lo hi b' - passageWindowClamp lo hi b ∧
    0 ≤ max (passageCellBurden p rho b (x n).1 (x n).2) 0
  exact ⟨sub_nonneg.mpr (monotone_passageWindowClamp lo hi hmono),
    le_max_right _ _⟩

/-- Burden cells retain exactly the geometric width of the selected window. -/
theorem IsControlledCivicWeightedPath.passageBurdenWindowCells_width
    {p : LoopParams} {rho lo hi : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPath p rho u x)
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi)
    (hhi : hi ≤ weighted.βdagger) {N : ℕ}
    (hcross : weighted.βdagger ≤ policyRunningMax x N) :
    passageSelectionWidth
        (passageBurdenWindowCells p rho weighted x lo hi N) =
      hi - lo := by
  let b : ℕ → ℝ := fun n ↦
    flooredCappedPolicyRunningMax 0 weighted.βdagger x n
  let z : ℕ → ℝ := fun n ↦ passageWindowClamp lo hi (b n)
  have hfloor : (0 : ℝ) ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨le_rfl, weighted.βdagger_mem.1.le⟩
  have hstart : (calibratedPoint p).1 ≤ (0 : ℝ) := by
    change (0 : ℝ) ≤ 0
    exact le_rfl
  have hbzero : b 0 = 0 :=
    path.toFrom.flooredCappedRunningMax_zero weighted hfloor.2 hstart
  have hbN : b N = weighted.βdagger :=
    flooredCappedRunningMax_eq_target hcross
  have hz0 : z 0 = lo := by
    dsimp only [z]
    rw [passageWindowClamp_eq_lo hlohi (by simpa only [b, hbzero] using hlo)]
  have hzN : z N = hi := by
    dsimp only [z]
    rw [passageWindowClamp_eq_hi hlohi (by simpa only [b, hbN] using hhi)]
  rw [passageBurdenWindowCells, passageSelectionWidth_ofFn]
  have htel := Finset.sum_range_sub z N
  rw [hz0, hzN] at htel
  rw [← Fin.sum_univ_eq_sum_range] at htel
  simpa only [z, b] using htel

/-- The clipped burden-window mass is no larger than the full burden ledger. -/
theorem IsControlledCivicWeightedPath.passageBurdenWindowCells_mass_le
    {p : LoopParams} {rho lo hi : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPath p rho u x) (N : ℕ) :
    passageSelectionMass
        (passageBurdenWindowCells p rho weighted x lo hi N) ≤
      flooredCappedBurdenMass p rho 0 weighted.βdagger x N := by
  let b : ℕ → ℝ := fun n ↦
    flooredCappedPolicyRunningMax 0 weighted.βdagger x n
  have hp₁mem : calibratedPoint p ∈ absorbingBox p :=
    ⟨by simp [calibratedPoint],
      stationaryStock_mem_stockInterval model (by norm_num)⟩
  have hfloor : (0 : ℝ) ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨le_rfl, weighted.βdagger_mem.1.le⟩
  have hstart : (calibratedPoint p).1 ≤ (0 : ℝ) := by
    change (0 : ℝ) ≤ 0
    exact le_rfl
  have hstock₀ : (calibratedPoint p).2 ≤ p.stationaryStock 0 := by
    change p.stationaryStock 0 ≤ p.stationaryStock 0
    exact le_rfl
  rw [passageBurdenWindowCells, passageSelectionMass_ofFn,
    flooredCappedBurdenMass]
  conv_rhs => rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_le_sum
  intro n _hn
  have hmono : b n ≤ b (n + 1) :=
    monotone_flooredCappedPolicyRunningMax
      0 weighted.βdagger x (Nat.le_succ (n : ℕ))
  rcases hmono.lt_or_eq with hadvance | heq
  · have hburden := path.toFrom.passageCellBurden_nonneg_of_advance
      model ss hcoop weighted hp₁mem hfloor hstart hstock₀ hadvance
    have hclampDelta :
        passageWindowClamp lo hi (b (n + 1)) -
            passageWindowClamp lo hi (b n) ≤ b (n + 1) - b n :=
      passageWindowClamp_sub_le hmono
    have hmul := mul_le_mul_of_nonneg_left hclampDelta hburden
    simpa only [b, max_eq_left hburden, mul_comm] using hmul
  · have heqRaw :
        flooredCappedPolicyRunningMax 0 weighted.βdagger x (n + 1) =
          flooredCappedPolicyRunningMax 0 weighted.βdagger x n := by
      simpa only [b] using heq.symm
    rw [heqRaw, sub_self]
    norm_num

/-- The literal suffix selected by the burden-aware cell argument is paid
by the controls which remain after the truncation time.  The selected cell
itself is retained in the suffix mass here; callers may subtract its clipped
width explicitly.  This descending finite proof is the refund ledger needed
by the saddle surgery and avoids any appeal to an integral profile. -/
theorem IsControlledCivicWeightedPath.passageBurdenWindowSuffix_refund
    {p : LoopParams} {rho L lo hi : ℝ}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPath p rho u x)
    {start N : ℕ} (hstartN : start ≤ N)
    (hcross : weighted.βdagger ≤ policyRunningMax x N) :
    (coupledCellFactor (p.α * L) / p.α) *
        ((∫ z in
            flooredCappedPolicyRunningMax 0 weighted.βdagger x start..
              weighted.βdagger,
            weightedBarrierIntegrand p rho z) +
          passageSelectionMass
            ((passageBurdenWindowCells p rho weighted x lo hi N).drop start)) ≤
      controlAction u N - controlAction u start := by
  let cells := passageBurdenWindowCells p rho weighted x lo hi N
  let b : ℕ → ℝ := fun n ↦
    flooredCappedPolicyRunningMax 0 weighted.βdagger x n
  let f := weightedBarrierIntegrand p rho
  let scale := coupledCellFactor (p.α * L) / p.α
  have hp₁mem : calibratedPoint p ∈ absorbingBox p :=
    ⟨by simp [calibratedPoint],
      stationaryStock_mem_stockInterval model (by norm_num)⟩
  have hfloor : (0 : ℝ) ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨le_rfl, weighted.βdagger_mem.1.le⟩
  have hstart : (calibratedPoint p).1 ≤ (0 : ℝ) := by
    change (0 : ℝ) ≤ 0
    exact le_rfl
  have hstock₀ : (calibratedPoint p).2 ≤ p.stationaryStock 0 := by
    change p.stationaryStock 0 ≤ p.stationaryStock 0
    exact le_rfl
  have hbsegment : ∀ n, b n ∈ Icc (0 : ℝ) weighted.βdagger := by
    intro n
    simpa only [b] using path.toFrom.flooredCappedRunningMax_mem
      weighted hp₁mem.1 hfloor n
  have hbmono : ∀ n, b n ≤ b (n + 1) := fun n ↦
    monotone_flooredCappedPolicyRunningMax
      0 weighted.βdagger x n.le_succ
  have hend : b N = weighted.βdagger := by
    simpa only [b] using flooredCappedRunningMax_eq_target hcross
  have hscale : 0 ≤ scale :=
    (div_pos (coupledCellFactor_pos (p.α * L)) model.α_pos).le
  induction hstartN using Nat.decreasingInduction with
  | self =>
      have hlength : cells.length = N := by
        simp only [cells, passageBurdenWindowCells, List.length_ofFn]
      have hdrop : cells.drop N = [] :=
        List.drop_eq_nil_of_le (by omega)
      rw [show flooredCappedPolicyRunningMax 0 weighted.βdagger x N =
          weighted.βdagger by simpa only [b] using hend,
        intervalIntegral.integral_same, hdrop]
      simp only [passageSelectionMass, add_zero, mul_zero, sub_self]
      exact le_rfl
  | of_succ n hn ih =>
      have hnCells : n < cells.length := by
        simpa only [cells, passageBurdenWindowCells, List.length_ofFn] using hn
      have hcons : cells[n] :: cells.drop (n + 1) = cells.drop n :=
        List.cons_getElem_drop_succ (h := hnCells)
      let q := passageCellBurden p rho (b n) (x n).1 (x n).2 *
        (b (n + 1) - b n)
      have hcellMass : cells[n].deficit * cells[n].width ≤ q := by
        have hmono := hbmono n
        rcases hmono.lt_or_eq with hadvance | heq
        · have hburden := path.toFrom.passageCellBurden_nonneg_of_advance
            model ss hcoop weighted hp₁mem hfloor hstart hstock₀
              (by simpa only [b] using hadvance)
          have hclampDelta :
              passageWindowClamp lo hi (b (n + 1)) -
                  passageWindowClamp lo hi (b n) ≤ b (n + 1) - b n :=
            passageWindowClamp_sub_le hmono
          have hmul := mul_le_mul_of_nonneg_left hclampDelta hburden
          simpa only [cells, passageBurdenWindowCells, List.getElem_ofFn,
            b, q, max_eq_left hburden, mul_comm] using hmul
        · have heq' : b (n + 1) = b n := heq.symm
          simp only [cells, passageBurdenWindowCells, List.getElem_ofFn,
            b, q, heq', sub_self, mul_zero, le_refl]
      have hcellLedger :
          scale *
              ((∫ z in b n..b (n + 1), f z) + q) ≤
            (u n) ^ 2 / 2 := by
        simpa only [scale, b, f, q] using
          path.toFrom.floored_coupled_burden_cell_le_half_control_sq
            model ss hcoop weighted hL hp₁mem hfloor hstart hstock₀ n
      have hleftInt : IntervalIntegrable f MeasureTheory.volume
          (b n) (b (n + 1)) := by
        have hsubset : [[b n, b (n + 1)]] ⊆
            Icc (0 : ℝ) weighted.βdagger := by
          rw [uIcc_of_le (hbmono n)]
          intro z hz
          exact ⟨(hbsegment n).1.trans hz.1,
            hz.2.trans (hbsegment (n + 1)).2⟩
        exact ((continuousOn_weightedBarrierIntegrand model rho weighted).mono
          hsubset).intervalIntegrable
      have hrightInt : IntervalIntegrable f MeasureTheory.volume
          (b (n + 1)) weighted.βdagger := by
        have hsubset : [[b (n + 1), weighted.βdagger]] ⊆
            Icc (0 : ℝ) weighted.βdagger := by
          rw [uIcc_of_le (hbsegment (n + 1)).2]
          intro z hz
          exact ⟨(hbsegment (n + 1)).1.trans hz.1, hz.2⟩
        exact ((continuousOn_weightedBarrierIntegrand model rho weighted).mono
          hsubset).intervalIntegrable
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        hleftInt hrightInt
      have hinside :
          (∫ z in b n..weighted.βdagger, f z) +
              passageSelectionMass (cells.drop n) ≤
            ((∫ z in b n..b (n + 1), f z) + q) +
              ((∫ z in b (n + 1)..weighted.βdagger, f z) +
                passageSelectionMass (cells.drop (n + 1))) := by
        rw [← hcons]
        simp only [passageSelectionMass]
        linarith
      have hinsideScaled := mul_le_mul_of_nonneg_left hinside hscale
      have hsum :
          scale *
              ((∫ z in b n..weighted.βdagger, f z) +
                passageSelectionMass (cells.drop n)) ≤
            (u n) ^ 2 / 2 +
              (controlAction u N - controlAction u (n + 1)) := by
        calc
          _ ≤ scale *
              (((∫ z in b n..b (n + 1), f z) + q) +
                ((∫ z in b (n + 1)..weighted.βdagger, f z) +
                  passageSelectionMass (cells.drop (n + 1)))) := hinsideScaled
          _ = scale * ((∫ z in b n..b (n + 1), f z) + q) +
              scale * ((∫ z in b (n + 1)..weighted.βdagger, f z) +
                passageSelectionMass (cells.drop (n + 1))) := by ring
          _ ≤ (u n) ^ 2 / 2 +
              (controlAction u N - controlAction u (n + 1)) :=
            add_le_add hcellLedger (by simpa only [b, f, scale, cells] using ih)
      have hactionSucc : controlAction u (n + 1) =
          controlAction u n + (u n) ^ 2 / 2 := by
        simp only [controlAction, Finset.sum_range_succ]
        ring
      have hresult :
        scale *
            ((∫ z in b n..weighted.βdagger, f z) +
              passageSelectionMass (cells.drop n)) ≤
          controlAction u N - controlAction u n := by
        rw [hactionSucc] at hsum
        linarith
      simpa only [b, f, scale, cells] using hresult

/-- Selected-cell suffix refund with the exact small-mesh residual retained.
The ordinary suffix lemma pays the ideal saddle tail and burden mass; this
version additionally exposes the square which pays for a cell that overleaps
the localization window. -/
theorem IsControlledCivicWeightedPath.passageBurdenWindowSuffix_refund_add_residual
    {p : LoopParams} {rho L lo hi : ℝ}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPath p rho u x)
    {n N : ℕ} (hn : n < N)
    (hcross : weighted.βdagger ≤ policyRunningMax x N)
    (hsmall : p.α * L ≤ 1)
    (hadvance :
      flooredCappedPolicyRunningMax 0 weighted.βdagger x n <
        flooredCappedPolicyRunningMax 0 weighted.βdagger x (n + 1)) :
    (coupledCellFactor (p.α * L) / p.α) *
        ((∫ z in
            flooredCappedPolicyRunningMax 0 weighted.βdagger x n..
              weighted.βdagger,
            weightedBarrierIntegrand p rho z) +
          passageSelectionMass
            ((passageBurdenWindowCells p rho weighted x lo hi N).drop n)) +
      passageCellResidual p rho L
          (flooredCappedPolicyRunningMax 0 weighted.βdagger x n)
          (flooredCappedPolicyRunningMax 0 weighted.βdagger x (n + 1))
          (x n).1 (x n).2 ^ 2 / 2 ≤
        controlAction u N - controlAction u n := by
  let cells := passageBurdenWindowCells p rho weighted x lo hi N
  let b : ℕ → ℝ := fun k ↦
    flooredCappedPolicyRunningMax 0 weighted.βdagger x k
  let f := weightedBarrierIntegrand p rho
  let scale := coupledCellFactor (p.α * L) / p.α
  let burden := passageCellBurden p rho (b n) (x n).1 (x n).2
  let charge := burden * (b (n + 1) - b n)
  let residual := passageCellResidual p rho L
    (b n) (b (n + 1)) (x n).1 (x n).2
  have hp₁mem : calibratedPoint p ∈ absorbingBox p :=
    ⟨by simp [calibratedPoint],
      stationaryStock_mem_stockInterval model (by norm_num)⟩
  have hfloor : (0 : ℝ) ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨le_rfl, weighted.βdagger_mem.1.le⟩
  have hstart : (calibratedPoint p).1 ≤ (0 : ℝ) := by
    change (0 : ℝ) ≤ 0
    exact le_rfl
  have hstock₀ : (calibratedPoint p).2 ≤ p.stationaryStock 0 := by
    change p.stationaryStock 0 ≤ p.stationaryStock 0
    exact le_rfl
  have hbsegment : ∀ k, b k ∈ Icc (0 : ℝ) weighted.βdagger := by
    intro k
    simpa only [b] using path.toFrom.flooredCappedRunningMax_mem
      weighted hp₁mem.1 hfloor k
  have hmono : b n ≤ b (n + 1) := hadvance.le
  have hscale : 0 ≤ scale :=
    (div_pos (coupledCellFactor_pos (p.α * L)) model.α_pos).le
  have hlength : cells.length = N := by
    simp only [cells, passageBurdenWindowCells, List.length_ofFn]
  have hnCells : n < cells.length := by simpa only [hlength] using hn
  have hcons : cells[n] :: cells.drop (n + 1) = cells.drop n :=
    List.cons_getElem_drop_succ (h := hnCells)
  have hburden : 0 ≤ burden := by
    simpa only [burden, b] using
      path.toFrom.passageCellBurden_nonneg_of_advance
        model ss hcoop weighted hp₁mem hfloor hstart hstock₀ hadvance
  have hcellMass : cells[n].deficit * cells[n].width ≤ charge := by
    have hclampDelta :
        passageWindowClamp lo hi (b (n + 1)) -
            passageWindowClamp lo hi (b n) ≤ b (n + 1) - b n :=
      passageWindowClamp_sub_le hmono
    have hmul := mul_le_mul_of_nonneg_left hclampDelta hburden
    simpa only [cells, passageBurdenWindowCells, List.getElem_ofFn,
      b, burden, charge, max_eq_left hburden, mul_comm] using hmul
  have hcellLedger :
      scale * ((∫ z in b n..b (n + 1), f z) + charge) +
          residual ^ 2 / 2 ≤ (u n) ^ 2 / 2 := by
    simpa only [scale, b, f, burden, charge, residual] using
      path.toFrom.floored_coupled_burden_cell_add_residual_le
        model ss hcoop weighted hL hp₁mem hfloor hstart hstock₀
          hsmall hadvance
  have hsuffix :
      scale * ((∫ z in b (n + 1)..weighted.βdagger, f z) +
          passageSelectionMass (cells.drop (n + 1))) ≤
        controlAction u N - controlAction u (n + 1) := by
    simpa only [scale, b, f, cells] using
      path.passageBurdenWindowSuffix_refund
        model ss hcoop weighted hL (Nat.succ_le_of_lt hn) hcross
  have hleftInt : IntervalIntegrable f MeasureTheory.volume
      (b n) (b (n + 1)) := by
    have hsubset : [[b n, b (n + 1)]] ⊆
        Icc (0 : ℝ) weighted.βdagger := by
      rw [uIcc_of_le hmono]
      intro z hz
      exact ⟨(hbsegment n).1.trans hz.1,
        hz.2.trans (hbsegment (n + 1)).2⟩
    exact ((continuousOn_weightedBarrierIntegrand model rho weighted).mono
      hsubset).intervalIntegrable
  have hrightInt : IntervalIntegrable f MeasureTheory.volume
      (b (n + 1)) weighted.βdagger := by
    have hsubset : [[b (n + 1), weighted.βdagger]] ⊆
        Icc (0 : ℝ) weighted.βdagger := by
      rw [uIcc_of_le (hbsegment (n + 1)).2]
      intro z hz
      exact ⟨(hbsegment (n + 1)).1.trans hz.1, hz.2⟩
    exact ((continuousOn_weightedBarrierIntegrand model rho weighted).mono
      hsubset).intervalIntegrable
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    hleftInt hrightInt
  have hinside :
      (∫ z in b n..weighted.βdagger, f z) +
          passageSelectionMass (cells.drop n) ≤
        ((∫ z in b n..b (n + 1), f z) + charge) +
          ((∫ z in b (n + 1)..weighted.βdagger, f z) +
            passageSelectionMass (cells.drop (n + 1))) := by
    rw [← hcons]
    simp only [passageSelectionMass]
    linarith
  have hinsideScaled := mul_le_mul_of_nonneg_left hinside hscale
  have hsum :
      scale * ((∫ z in b n..weighted.βdagger, f z) +
          passageSelectionMass (cells.drop n)) + residual ^ 2 / 2 ≤
        (u n) ^ 2 / 2 +
          (controlAction u N - controlAction u (n + 1)) := by
    calc
      _ ≤ scale *
            (((∫ z in b n..b (n + 1), f z) + charge) +
              ((∫ z in b (n + 1)..weighted.βdagger, f z) +
                passageSelectionMass (cells.drop (n + 1)))) +
          residual ^ 2 / 2 := add_le_add hinsideScaled le_rfl
      _ = (scale * ((∫ z in b n..b (n + 1), f z) + charge) +
            residual ^ 2 / 2) +
          scale * ((∫ z in b (n + 1)..weighted.βdagger, f z) +
            passageSelectionMass (cells.drop (n + 1))) := by ring
      _ ≤ (u n) ^ 2 / 2 +
          (controlAction u N - controlAction u (n + 1)) :=
        add_le_add hcellLedger hsuffix
  have hactionSucc : controlAction u (n + 1) =
      controlAction u n + (u n) ^ 2 / 2 := by
    simp only [controlAction, Finset.sum_range_succ]
    ring
  rw [hactionSucc] at hsum
  have hresult :
      scale * ((∫ z in b n..weighted.βdagger, f z) +
          passageSelectionMass (cells.drop n)) + residual ^ 2 / 2 ≤
        controlAction u N - controlAction u n := by
    linarith
  simpa only [scale, b, f, cells, residual] using hresult

/-- A dominated cell in the terminal saddle window yields a complete basin
exit after truncating immediately before that cell.  Normal cells are already
within one window width; overleaping cells are paid by the exact residual
square retained above. -/
theorem IsControlledCivicWeightedPath.exists_exitAction_le_action_add_selectedWindowQuadratic
    {p : LoopParams} {rho L : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hrho : 0 ≤ rho) (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPath p rho u x)
    {w a : ℝ} {n N : ℕ}
    (halphaOne : p.α ≤ 1) (hquarter : p.α * L ≤ 1 / 4)
    (hfour : 4 * p.α * p.c ^ 2 * p.I ≤ p.lambda₀)
    (hwAlpha : p.α ≤ w) (hwSaddle : w ≤ weighted.βdagger)
    (hroom : p.α * (passageGradientBound p + 2 * p.α) ≤
      1 - weighted.βdagger)
    (hn : n < N) (hcross : weighted.βdagger ≤ policyRunningMax x N)
    (hadvance :
      flooredCappedPolicyRunningMax 0 weighted.βdagger x n <
        flooredCappedPolicyRunningMax 0 weighted.βdagger x (n + 1))
    (hwindow : 0 <
      passageWindowClamp (weighted.βdagger - w) weighted.βdagger
          (flooredCappedPolicyRunningMax 0 weighted.βdagger x (n + 1)) -
        passageWindowClamp (weighted.βdagger - w) weighted.βdagger
          (flooredCappedPolicyRunningMax 0 weighted.βdagger x n))
    (hqSq :
      (passageCellBurden p rho
          (flooredCappedPolicyRunningMax 0 weighted.βdagger x n)
          (x n).1 (x n).2) ^ 2 ≤
        a * passageSelectionMass
          ((passageBurdenWindowCells p rho weighted x
            (weighted.βdagger - w) weighted.βdagger N).drop n))
    (hburdenAbsorb :
      49 * passageLocalOneClimbQuadraticConstant p weighted L * a ≤
        (coupledCellFactor (p.α * L) / p.α) / 4)
    (hresidualAbsorb :
      192 * passageLocalOneClimbQuadraticConstant p weighted L * p.α ^ 2 ≤ 1) :
    ∃ e ∈ quasipotentialActionSet p rho,
      e ≤ controlAction u N +
        13 * passageLocalOneClimbQuadraticConstant p weighted L * w ^ 2 := by
  let b := flooredCappedPolicyRunningMax 0 weighted.βdagger x n
  let b' := flooredCappedPolicyRunningMax 0 weighted.βdagger x (n + 1)
  let q := passageCellBurden p rho b (x n).1 (x n).2
  let D := weighted.βdagger - b
  let step := b' - b
  let residual := passageCellResidual p rho L b b' (x n).1 (x n).2
  let cells := passageBurdenWindowCells p rho weighted x
    (weighted.βdagger - w) weighted.βdagger N
  let mass := passageSelectionMass (cells.drop n)
  let scale := coupledCellFactor (p.α * L) / p.α
  let C := passageLocalOneClimbQuadraticConstant p weighted L
  have hw₀ : 0 ≤ w := model.α_pos.le.trans hwAlpha
  have hlohi : weighted.βdagger - w ≤ weighted.βdagger := by linarith
  have horder := passageWindowClamp_strict_sub_order hlohi hwindow
  have hbBelow : b < weighted.βdagger := by simpa only [b] using horder.1
  have hb'Above : weighted.βdagger - w < b' := by
    simpa only [b'] using horder.2
  have hbmem : b ∈ Icc (0 : ℝ) weighted.βdagger := by
    simpa only [b] using path.toFrom.flooredCappedRunningMax_mem
      weighted (show (calibratedPoint p).1 ∈ Icc (0 : ℝ) 1 by
        simp [calibratedPoint])
      (show (0 : ℝ) ∈ Icc (0 : ℝ) weighted.βdagger from
        ⟨le_rfl, weighted.βdagger_mem.1.le⟩) n
  have hD₀ : 0 ≤ D := by dsimp only [D]; exact sub_nonneg.mpr hbmem.2
  have hstep₀ : 0 ≤ step := by dsimp only [step]; exact sub_nonneg.mpr hadvance.le
  have hq₀ : 0 ≤ q := by
    have hp₁mem : calibratedPoint p ∈ absorbingBox p :=
      ⟨by simp [calibratedPoint],
        stationaryStock_mem_stockInterval model (by norm_num)⟩
    simpa only [q, b] using
      path.toFrom.passageCellBurden_nonneg_of_advance
        model ss hcoop weighted hp₁mem
          (show (0 : ℝ) ∈ Icc (0 : ℝ) weighted.βdagger from
            ⟨le_rfl, weighted.βdagger_mem.1.le⟩)
          (show (calibratedPoint p).1 ≤ (0 : ℝ) by
            simp [calibratedPoint])
          (show (calibratedPoint p).2 ≤ p.stationaryStock 0 by
            rfl) hadvance
  have hsmall : p.α * L ≤ 1 := by linarith
  obtain ⟨_hold, hbetaB, _hnew⟩ :=
    flooredCappedRunningMax_advance_structure hadvance
  have hretreat := path.retreat_le_two_alpha_mul_burden
    model ss weighted hfour hadvance
  have hlag := path.abs_stationaryStockLag_le_burden
    model ss hcoop weighted hfour hadvance
  let v : Fin n → ℝ := fun i ↦ u i
  have hvEnd : finiteControlledOrbit p rho v n = x n := by
    simpa only [v] using finiteControlledOrbit_restrict_eq path le_rfl
  have hx : x n ∈ absorbingBox p := path.mem_absorbingBox model n
  have hDw : D + w ≤ 2 := by
    have hDOne : D ≤ 1 := by
      dsimp only [D]
      linarith [hbmem.1, weighted.βdagger_mem.2.le]
    have hwOne : w ≤ 1 := hwSaddle.trans weighted.βdagger_mem.2.le
    linarith
  have hlocalRoom : p.α *
      (passageGradientBound p + p.α * (D + w)) ≤
        1 - weighted.βdagger := by
    have hinner : p.α * (D + w) ≤ 2 * p.α := by
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left hDw model.α_pos.le
    have houter : p.α *
        (passageGradientBound p + p.α * (D + w)) ≤
          p.α * (passageGradientBound p + 2 * p.α) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hinner) model.α_pos.le
    exact houter.trans hroom
  obtain ⟨exitCost, hexitMem, hexitLocal⟩ :=
    exists_exitAction_le_prefix_add_tail_add_localQuadratic
      model ss hrho hrhoCure hcoop weighted hL halphaOne hsmall hbmem
        hwAlpha hq₀ v hvEnd hx hbetaB
        (by simpa only [b, q] using hretreat)
        (by simpa only [q] using hlag)
        (by simpa only [D] using hlocalRoom)
  have hvAction : gaussianVectorAction v = controlAction u n := by
    simpa only [v] using gaussianVectorAction_restrict u n
  rw [hvAction] at hexitLocal
  have hrefund := path.passageBurdenWindowSuffix_refund_add_residual
    model ss hcoop weighted hL hn hcross hsmall hadvance
      (lo := weighted.βdagger - w) (hi := weighted.βdagger)
  have hrefund' :
      scale * ((∫ z in b..weighted.βdagger,
          weightedBarrierIntegrand p rho z) + mass) +
        residual ^ 2 / 2 ≤ controlAction u N - controlAction u n := by
    simpa only [scale, b, mass, cells, residual] using hrefund
  have hmass₀ : 0 ≤ mass := by
    dsimp only [mass, cells]
    apply passageSelectionMass_nonneg
    have hnonneg := passageBurdenWindowCells_nonnegative weighted x
      (lo := weighted.βdagger - w) (hi := weighted.βdagger) N
    rw [List.forall_iff_forall_mem] at hnonneg ⊢
    intro cell hcell
    exact hnonneg cell (List.mem_of_mem_drop hcell)
  have hscale₀ : 0 ≤ scale := by
    dsimp only [scale]
    exact (div_pos (coupledCellFactor_pos (p.α * L)) model.α_pos).le
  have hC₀ : 0 ≤ C := by
    dsimp only [C]
    exact (passageLocalOneClimbQuadraticConstant_pos model weighted hL).le
  have hDsq : D ^ 2 ≤
      12 * w ^ 2 + 48 * q ^ 2 + 48 * p.α ^ 2 * residual ^ 2 := by
    by_cases hnormal : weighted.βdagger - w ≤ b
    · have hDle : D ≤ w := by dsimp only [D]; linarith
      have hDsqW := (sq_le_sq₀ hD₀ hw₀).2 hDle
      have htail₀ : 0 ≤
          11 * w ^ 2 + 48 * q ^ 2 + 48 * p.α ^ 2 * residual ^ 2 := by
        positivity
      linarith
    · have hover : D ≤ step + w := by
        have hbelow : b < weighted.βdagger - w := lt_of_not_ge hnormal
        dsimp only [D, step]
        linarith
      have hbarrier₀ : 0 ≤ weightedBarrierIntegrand p rho b :=
        weighted.barrier_nonneg_before hbmem
      have hbarrierLe := weightedBarrierIntegrand_le_lipschitz_saddle_distance
        weighted hL hbmem
      exact overleapingCell_saddleDistance_sq_le
        model.α_pos halphaOne hL.nonneg hquarter hD₀ hw₀ hq₀
          hstep₀ hbarrierLe hover (by
            simp only [residual, passageCellResidual, q, step])
  have hquadShape :
      C * (w ^ 2 + D ^ 2 + q ^ 2) ≤
        13 * C * w ^ 2 + 49 * C * q ^ 2 +
          48 * C * p.α ^ 2 * residual ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hDsq hC₀
    nlinarith only [hscaled]
  have hqSq' : q ^ 2 ≤ a * mass := by
    simpa only [q, mass, cells, b] using hqSq
  have hqPay : 49 * C * q ^ 2 ≤ scale * mass / 4 := by
    have hcoef₀ : 0 ≤ 49 * C := mul_nonneg (by norm_num) hC₀
    have hfirst := mul_le_mul_of_nonneg_left hqSq' hcoef₀
    have hsecond := mul_le_mul_of_nonneg_right
      (by simpa only [C, scale] using hburdenAbsorb) hmass₀
    nlinarith only [hfirst, hsecond]
  have hrPay : 48 * C * p.α ^ 2 * residual ^ 2 ≤ residual ^ 2 / 4 := by
    have hrsq₀ : 0 ≤ residual ^ 2 / 4 :=
      div_nonneg (sq_nonneg residual) (by norm_num)
    have hmul := mul_le_mul_of_nonneg_right
      (by simpa only [C] using hresidualAbsorb) hrsq₀
    nlinarith only [hmul]
  have hquad :
      C * (w ^ 2 + D ^ 2 + q ^ 2) ≤
        13 * C * w ^ 2 + scale * mass / 4 + residual ^ 2 / 4 := by
    linarith only [hquadShape, hqPay, hrPay]
  have hcharge :
      scale * (∫ z in b..weighted.βdagger,
          weightedBarrierIntegrand p rho z) +
          scale * mass / 4 + residual ^ 2 / 4 ≤
        controlAction u N - controlAction u n := by
    have hmassScaled : 0 ≤ scale * mass := mul_nonneg hscale₀ hmass₀
    have hrsq₀ : 0 ≤ residual ^ 2 := sq_nonneg residual
    nlinarith only [hrefund', hmassScaled, hrsq₀]
  refine ⟨exitCost, hexitMem, ?_⟩
  change exitCost ≤ controlAction u N + 13 * C * w ^ 2
  dsimp only [C, D] at hexitLocal ⊢
  linarith only [hexitLocal, hquad, hcharge]

/-- A sufficiently small complete burden budget selects a positive-width
cell whose squared burden is dominated by its own suffix refund. -/
theorem IsControlledCivicWeightedPath.hasDominatedPassageBurdenWindowCell
    {p : LoopParams} {rho lo hi a : ℝ} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPath p rho u x)
    (ha : 0 < a) (hlo : 0 ≤ lo) (hlohi : lo < hi)
    (hhi : hi ≤ weighted.βdagger) {N : ℕ}
    (hcross : weighted.βdagger ≤ policyRunningMax x N)
    (hbudget : flooredCappedBurdenMass p rho 0 weighted.βdagger x N <
      a * (hi - lo) ^ 2 / 4) :
    HasDominatedPassageCell a
      (passageBurdenWindowCells p rho weighted x lo hi N) := by
  let cells := passageBurdenWindowCells p rho weighted x lo hi N
  have hnonneg := passageBurdenWindowCells_nonnegative
    weighted x (lo := lo) (hi := hi) N
  have hwidthEq := path.passageBurdenWindowCells_width
    weighted hlo hlohi.le hhi hcross
  have hwidth : 0 < passageSelectionWidth cells := by
    simpa only [cells, hwidthEq] using sub_pos.mpr hlohi
  have hmassLe := path.passageBurdenWindowCells_mass_le
    model ss hcoop weighted (lo := lo) (hi := hi) N
  apply exists_dominatedPassageCell_of_mass_lt ha hnonneg hwidth
  rw [hwidthEq]
  exact hmassLe.trans_lt hbudget

/-- Action-gap form of burden-aware Selection. -/
theorem IsControlledCivicWeightedPath.hasDominatedPassageBurdenWindowCell_of_actionGap_lt
    {p : LoopParams} {rho L lo hi a : ℝ}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPath p rho u x)
    (ha : 0 < a) (hlo : 0 ≤ lo) (hlohi : lo < hi)
    (hhi : hi ≤ weighted.βdagger) {N : ℕ}
    (hcross : weighted.βdagger ≤ policyRunningMax x N)
    (hgap :
      controlAction u N -
          (2 / (p.α * (1 + 2 * p.α * L))) *
            weightedBarrierArea weighted <
        (coupledCellFactor (p.α * L) / p.α) *
          (a * (hi - lo) ^ 2 / 4)) :
    HasDominatedPassageCell a
      (passageBurdenWindowCells p rho weighted x lo hi N) := by
  let coefficient := coupledCellFactor (p.α * L) / p.α
  have hcoefficient : 0 < coefficient :=
    div_pos (coupledCellFactor_pos (p.α * L)) model.α_pos
  have hmassScaled := path.corrected_burdenMass_le_action_gap
    model ss hcoop weighted hL hcross
  have hmassStrict : coefficient *
      flooredCappedBurdenMass p rho 0 weighted.βdagger x N <
        coefficient * (a * (hi - lo) ^ 2 / 4) := by
    dsimp only [coefficient] at hmassScaled hgap ⊢
    exact hmassScaled.trans_lt hgap
  have hmass : flooredCappedBurdenMass p rho 0 weighted.βdagger x N <
      a * (hi - lo) ^ 2 / 4 :=
    (mul_lt_mul_iff_right₀ hcoefficient).mp hmassStrict
  exact path.hasDominatedPassageBurdenWindowCell
    model ss hcoop weighted ha hlo hlohi hhi hcross hmass

/-- A dominated burden cell yields the corresponding actual advancing step. -/
theorem IsControlledCivicWeightedPath.exists_dominatedPassageBurdenWindowStep
    {p : LoopParams} {rho lo hi a : ℝ}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPath p rho u x) {N : ℕ}
    (hdominated : HasDominatedPassageCell a
      (passageBurdenWindowCells p rho weighted x lo hi N)) :
    ∃ n < N,
      flooredCappedPolicyRunningMax 0 weighted.βdagger x n <
          flooredCappedPolicyRunningMax 0 weighted.βdagger x (n + 1) ∧
        0 < passageWindowClamp lo hi
              (flooredCappedPolicyRunningMax 0 weighted.βdagger x (n + 1)) -
            passageWindowClamp lo hi
              (flooredCappedPolicyRunningMax 0 weighted.βdagger x n) ∧
        (passageCellBurden p rho
            (flooredCappedPolicyRunningMax 0 weighted.βdagger x n)
            (x n).1 (x n).2) ^ 2 ≤
          a * passageSelectionMass
            ((passageBurdenWindowCells p rho weighted x lo hi N).drop n) := by
  let cells := passageBurdenWindowCells p rho weighted x lo hi N
  obtain ⟨n, hn, hwidth, hbound⟩ := hdominated.exists_index
  have hlength : cells.length = N := by
    simp only [cells, passageBurdenWindowCells, List.length_ofFn]
  have hnN : n < N := by
    rw [← hlength]
    exact hn
  let b : ℕ → ℝ := fun k ↦
    flooredCappedPolicyRunningMax 0 weighted.βdagger x k
  have hwidth' :
      0 < passageWindowClamp lo hi (b (n + 1)) -
        passageWindowClamp lo hi (b n) := by
    simpa only [cells, passageBurdenWindowCells, List.getElem_ofFn, b] using hwidth
  have hmono : b n ≤ b (n + 1) :=
    monotone_flooredCappedPolicyRunningMax
      0 weighted.βdagger x n.le_succ
  have hadvance : b n < b (n + 1) := by
    rcases hmono.lt_or_eq with hlt | heq
    · exact hlt
    · rw [← heq, sub_self] at hwidth'
      exact (lt_irrefl 0 hwidth').elim
  have hp₁mem : calibratedPoint p ∈ absorbingBox p :=
    ⟨by simp [calibratedPoint],
      stationaryStock_mem_stockInterval model (by norm_num)⟩
  have hfloor : (0 : ℝ) ∈ Icc (0 : ℝ) weighted.βdagger :=
    ⟨le_rfl, weighted.βdagger_mem.1.le⟩
  have hstart : (calibratedPoint p).1 ≤ (0 : ℝ) := by
    change (0 : ℝ) ≤ 0
    exact le_rfl
  have hstock₀ : (calibratedPoint p).2 ≤ p.stationaryStock 0 := by
    change p.stationaryStock 0 ≤ p.stationaryStock 0
    exact le_rfl
  have hburden := path.toFrom.passageCellBurden_nonneg_of_advance
    model ss hcoop weighted hp₁mem hfloor hstart hstock₀ hadvance
  have hbound' :
      (max (passageCellBurden p rho (b n) (x n).1 (x n).2) 0) ^ 2 ≤
        a * passageSelectionMass (cells.drop n) := by
    simpa only [cells, passageBurdenWindowCells, List.getElem_ofFn, b] using hbound
  rw [max_eq_left hburden] at hbound'
  refine ⟨n, hnN, ?_, hwidth', ?_⟩
  · simpa only [b] using hadvance
  · simpa only [b, cells] using hbound'

/-- Pure order algebra behind any fixed-parameter existential passage bound.
Once a strict intermediate lower bound `S` is known, every upper bracket can
be rewritten with an arbitrary positive scale. -/
theorem exists_scaled_gap_constant
    {B S X V U scale : ℝ}
    (hBS : B < S) (hSX : S ≤ X) (hXV : X ≤ V) (hVU : V ≤ U)
    (hscale : 0 < scale) :
    ∃ C : ℝ, 0 ≤ C ∧ V ≤ X + C * (X - B) * scale := by
  let denom := (S - B) * scale
  let C := (U - B) / denom
  have hSBpos : 0 < S - B := sub_pos.mpr hBS
  have hdenomPos : 0 < denom := by
    dsimp only [denom]
    exact mul_pos hSBpos hscale
  have hUBnonneg : 0 ≤ U - B := by linarith
  have hCnonneg : 0 ≤ C := by
    dsimp only [C]
    exact div_nonneg hUBnonneg hdenomPos.le
  refine ⟨C, hCnonneg, ?_⟩
  have hidentity : C * (S - B) * scale = U - B := by
    dsimp only [C, denom]
    field_simp [hSBpos.ne', hscale.ne']
  have hgap : S - B ≤ X - B := by linarith
  have hfirst : C * (S - B) ≤ C * (X - B) :=
    mul_le_mul_of_nonneg_left hgap hCnonneg
  have hmono : C * (S - B) * scale ≤ C * (X - B) * scale :=
    mul_le_mul_of_nonneg_right hfirst hscale.le
  linarith

/-- Positive logarithmic weight used by the derivation in the independent
passage report.  Unlike the paper's raw `1 + log (1/alpha)`, this never
vanishes or changes sign. -/
def passageLogWeight (alpha : ℝ) : ℝ :=
  1 + max (Real.log (1 / alpha)) 0

/-- Paper II, Proposition `prop:passage`: the sign-safe logarithmic weight is
strictly positive at every adaptation rate. -/
theorem passageLogWeight_pos (alpha : ℝ) : 0 < passageLogWeight alpha := by
  have hmax : 0 ≤ max (Real.log (1 / alpha)) 0 := le_max_right _ _
  simp only [passageLogWeight]
  linarith

/-- The raw logarithmic multiplier printed in `prop:passage` vanishes at the
perfectly positive adaptation rate `alpha = exp 1`. -/
theorem rawPassageLogFactor_exp_one :
    1 + Real.log (1 / Real.exp 1) = 0 := by
  rw [one_div, ← Real.exp_neg, Real.log_exp]
  norm_num

/-! ## The fixed-primitives family -/

/-- The literal logarithmic factor in the proposition.  It is
positive throughout the proposition's restricted family `0 < alpha ≤ 1`. -/
def passageLogFactor (alpha : ℝ) : ℝ :=
  1 + Real.log (1 / alpha)

/-- On `(0, 1]` the logarithmic factor is positive; it vanishes at `α = e`
and is negative beyond, so the restriction is substantive. -/
theorem passageLogFactor_pos_of_pos_of_le_one
    {alpha : ℝ} (halpha : 0 < alpha) (halphaOne : alpha ≤ 1) :
    0 < passageLogFactor alpha := by
  have honeDiv : (1 : ℝ) ≤ 1 / alpha := by
    exact (le_div_iff₀ halpha).2 (by simpa using halphaOne)
  have hlog : 0 ≤ Real.log (1 / alpha) := Real.log_nonneg honeDiv
  simp only [passageLogFactor]
  linarith

/-- On the small-rate interval, the printed logarithmic factor is at least
one. -/
theorem one_le_passageLogFactor_of_pos_of_le_one
    {alpha : ℝ} (halpha : 0 < alpha) (halphaOne : alpha ≤ 1) :
    1 ≤ passageLogFactor alpha := by
  have honeDiv : (1 : ℝ) ≤ 1 / alpha := by
    exact (le_div_iff₀ halpha).2 (by simpa using halphaOne)
  have hlog : 0 ≤ Real.log (1 / alpha) := Real.log_nonneg honeDiv
  simp only [passageLogFactor]
  linarith

/-- The corrected lower barrier `V_-` along the family varying only the
operator rate.  The barrier area, saddle, and Lipschitz constant are all
rate-free. -/
def passageLowerBarrierAtRate
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (L alpha : ℝ) : ℝ :=
  (2 / (alpha * (1 + 2 * alpha * L))) * weightedBarrierArea weighted

/-- Under the quarter-mesh restriction, the coupled ledger exceeds the
corrected lower barrier by at least `L` times the barrier area. -/
theorem passageLowerBarrier_add_L_area_le_coupledBarrier
    {p : LoopParams} {rho alpha L : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    (halpha : 0 < alpha) (hL : 0 ≤ L)
    (hquarter : alpha * L ≤ 1 / 4) :
    passageLowerBarrierAtRate weighted L alpha +
        L * weightedBarrierArea weighted ≤
      (coupledCellFactor (alpha * L) / alpha) *
        weightedBarrierArea weighted := by
  have hsmall : alpha * L ≤ 1 := by linarith
  have hden : 0 < 1 + 2 * alpha * L := by positivity
  have hcoefficient :
      2 / (alpha * (1 + 2 * alpha * L)) + L ≤
        coupledCellFactor (alpha * L) / alpha := by
    rw [coupledCellFactor_div_eq_two_div_sub halpha hsmall]
    have hid :
        (2 / alpha - L) -
            (2 / (alpha * (1 + 2 * alpha * L)) + L) =
          2 * L * (1 - 2 * alpha * L) /
            (1 + 2 * alpha * L) := by
      field_simp [halpha.ne', hden.ne']
      ring
    have hnumerator : 0 ≤ 2 * L * (1 - 2 * alpha * L) := by
      have : 0 ≤ 1 - 2 * alpha * L := by linarith
      positivity
    have hdiff : 0 ≤ (2 / alpha - L) -
        (2 / (alpha * (1 + 2 * alpha * L)) + L) := by
      rw [hid]
      exact div_nonneg hnumerator hden.le
    linarith only [hdiff]
  have harea : 0 ≤ weightedBarrierArea weighted := by
    simp only [weightedBarrierArea]
    exact intervalIntegral.integral_nonneg weighted.βdagger_mem.1.le
      (fun beta _hbeta ↦ weighted.barrier_nonneg_before
        (show beta ∈ Icc (0 : ℝ) weighted.βdagger from _hbeta))
  have hscaled := mul_le_mul_of_nonneg_right hcoefficient harea
  simp only [passageLowerBarrierAtRate]
  nlinarith only [hscaled]

/-- The explicit positive ceiling used to instantiate the paper's
existential `alpha_0`.  Its second branch guarantees `(SS)` and its third
branch makes the stationary-characteristic dominance ratio strictly less
than one.  `driftStationaryStockLipschitzBound` is a proved rate-free upper
bound for the paper's `L* = max D*'`. -/
def saddlePassageAlphaCeiling
    (p : LoopParams) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) : ℝ :=
  min 1 <| min
    (p.lambda₀ / (4 * p.c ^ 2 * p.I))
    ((1 - p.s weighted.βdagger) /
      (4 * p.c * driftStationaryStockLipschitzBound p))

/-- The canonical passage-rate ceiling is strictly positive. -/
theorem saddlePassageAlphaCeiling_pos
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho : ℝ} (weighted : WeightedThresholdAssumption p rho) :
    0 < saddlePassageAlphaCeiling p weighted := by
  have hdenSS : 0 < 4 * p.c ^ 2 * p.I :=
    mul_pos (mul_pos (by norm_num) (sq_pos_of_pos model.c_pos)) model.I_pos
  have hSS : 0 < p.lambda₀ / (4 * p.c ^ 2 * p.I) :=
    div_pos model.lambda₀_pos hdenSS
  have hs := driftStockMultiplier_nonneg_le model
    (show weighted.βdagger ∈ Icc (0 : ℝ) 1 from
      ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩)
  have hgap : 0 < 1 - p.s weighted.βdagger := by
    linarith [model.lambda₀_pos]
  have hK : 0 < driftStationaryStockLipschitzBound p :=
    driftStationaryStockLipschitzBound_pos model
  have hdenSlope :
      0 < 4 * p.c * driftStationaryStockLipschitzBound p :=
    mul_pos (mul_pos (by norm_num) model.c_pos) hK
  have hSlope : 0 < (1 - p.s weighted.βdagger) /
      (4 * p.c * driftStationaryStockLipschitzBound p) :=
    div_pos hgap hdenSlope
  simp only [saddlePassageAlphaCeiling, lt_min_iff]
  exact ⟨zero_lt_one, hSS, hSlope⟩

/-- The canonical ceiling lies in the paper's interval `(0, 1]`. -/
theorem saddlePassageAlphaCeiling_mem_Ioc
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho : ℝ} (weighted : WeightedThresholdAssumption p rho) :
    saddlePassageAlphaCeiling p weighted ∈ Ioc (0 : ℝ) 1 :=
  ⟨saddlePassageAlphaCeiling_pos model weighted,
    min_le_left _ _⟩

/-- Every positive rate below the canonical ceiling satisfies Paper II's
small-step condition without assuming that the reference rate itself does. -/
theorem smallStepAssumption_withOperatorRate_of_le_passageCeiling
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho alpha : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (_halpha : 0 ≤ alpha)
    (halphaLe : alpha ≤ saddlePassageAlphaCeiling p weighted) :
    SmallStepAssumption (withOperatorRate p alpha) := by
  have hceiling : saddlePassageAlphaCeiling p weighted ≤
      p.lambda₀ / (4 * p.c ^ 2 * p.I) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have halphaSS : alpha ≤ p.lambda₀ / (4 * p.c ^ 2 * p.I) :=
    halphaLe.trans hceiling
  have hden : 0 < 4 * p.c ^ 2 * p.I :=
    mul_pos (mul_pos (by norm_num) (sq_pos_of_pos model.c_pos)) model.I_pos
  have hmul : alpha * (4 * p.c ^ 2 * p.I) ≤ p.lambda₀ :=
    (le_div_iff₀ hden).1 halphaSS
  constructor
  simp only [withOperatorRate_alpha, withOperatorRate_c,
    withOperatorRate_I, withOperatorRate_lambda₀]
  nlinarith [model.lambda₀_pos]

/-- The strengthened ceiling leaves half of the `(SS)` dip coefficient in
reserve for the burden-aware truncation argument. -/
theorem four_alpha_c_sq_I_le_lambda_of_le_passageCeiling
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho alpha : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (halphaLe : alpha ≤ saddlePassageAlphaCeiling p weighted) :
    4 * alpha * p.c ^ 2 * p.I ≤ p.lambda₀ := by
  have hceiling : saddlePassageAlphaCeiling p weighted ≤
      p.lambda₀ / (4 * p.c ^ 2 * p.I) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have halphaSS : alpha ≤ p.lambda₀ / (4 * p.c ^ 2 * p.I) :=
    halphaLe.trans hceiling
  have hden : 0 < 4 * p.c ^ 2 * p.I :=
    mul_pos (mul_pos (by norm_num) (sq_pos_of_pos model.c_pos)) model.I_pos
  have hmul : alpha * (4 * p.c ^ 2 * p.I) ≤ p.lambda₀ :=
    (le_div_iff₀ hden).1 halphaSS
  nlinarith

/-- The explicit upper strategy estimate remains available below the
canonical ceiling even when the original parameter record itself does not
satisfy `(SS)`: use the ceiling rate as the reference member of the
fixed-primitives family. -/
theorem upwardStrategyCostAtRate_upper_bound_of_le_passageCeiling
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho L alpha : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (halpha : 0 < alpha)
    (halphaLe : alpha ≤ saddlePassageAlphaCeiling p weighted)
    (halphaOne : alpha ≤ 1)
    (hroom : alpha * (p.v + alpha) ≤ 1 - weighted.βdagger) :
    upwardStrategyCostAtRate weighted alpha ≤
      (2 / alpha) * weightedBarrierArea weighted +
        smallRateStrategyRemainderBound p L := by
  let alphaZero := saddlePassageAlphaCeiling p weighted
  let qZero := withOperatorRate p alphaZero
  let modelZero : DriftModelAssumptions qZero :=
    model.withOperatorRate (saddlePassageAlphaCeiling_pos model weighted)
  let ssZero : SmallStepAssumption qZero :=
    smallStepAssumption_withOperatorRate_of_le_passageCeiling
      model weighted
        (saddlePassageAlphaCeiling_pos model weighted).le le_rfl
  let weightedZero : WeightedThresholdAssumption qZero rho :=
    weighted.withOperatorRate alphaZero
  have hLZero : IsLipschitzConstantOn
      (weightedBarrierIntegrand qZero rho) L
        0 weightedZero.βdagger := by
    change IsLipschitzConstantOn
      (weightedBarrierIntegrand (withOperatorRate p alphaZero) rho) L
        0 weighted.βdagger
    have hfun :
        weightedBarrierIntegrand (withOperatorRate p alphaZero) rho =
          weightedBarrierIntegrand p rho := by
      funext beta
      exact withOperatorRate_weightedBarrierIntegrand p alphaZero rho beta
    rw [hfun]
    exact hL
  have hupper := upwardStrategyCostAtRate_upper_bound
    modelZero ssZero hrho (by simpa only [qZero, withOperatorRate_c] using hcoop)
      weightedZero hLZero halpha (by
        change alpha ≤ alphaZero
        exact halphaLe)
      halphaOne (by
        simpa only [qZero, weightedZero, withOperatorRate_v,
          WeightedThresholdAssumption.withOperatorRate_βdagger] using hroom)
  have hweighted : weightedZero.withOperatorRate alpha =
      weighted.withOperatorRate alpha := by
    rfl
  change upwardStrategyCost (weightedZero.withOperatorRate alpha) ≤
    (2 / alpha) * weightedBarrierArea weightedZero +
      smallRateStrategyRemainderBound qZero L at hupper
  rw [hweighted, weightedBarrierArea_withOperatorRate] at hupper
  simp only [qZero,
    smallRateStrategyRemainderBound, withOperatorRate_v,
    withOperatorRate_c, withOperatorRate_lambda₀,
    driftStationaryStockLipschitzBound_withOperatorRate] at hupper
  change upwardStrategyCost (weighted.withOperatorRate alpha) ≤
    (2 / alpha) * weightedBarrierArea weighted +
      smallRateStrategyRemainderBound p L
  convert hupper using 1
  · rfl
  · simp only [smallRateStrategyRemainderBound]

/-- At every rate below the strengthened ceiling, at least half of the
inverse-rate retreat coefficient remains after the stock coupling. -/
theorem half_inv_le_passageRetreatCoefficient
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho alpha D : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (halpha : 0 < alpha)
    (halphaLe : alpha ≤ saddlePassageAlphaCeiling p weighted)
    (hD : D ≤ p.I / p.lambda₀) :
    1 / (2 * alpha) ≤ 1 / alpha - 2 * p.c ^ 2 * D := by
  have hfour := four_alpha_c_sq_I_le_lambda_of_le_passageCeiling
    model weighted halphaLe
  have hscale : 0 ≤ 4 * alpha * p.c ^ 2 := by positivity
  have hDscaled :
      4 * alpha * p.c ^ 2 * D ≤
        4 * alpha * p.c ^ 2 * (p.I / p.lambda₀) :=
    mul_le_mul_of_nonneg_left hD hscale
  have hceiling :
      4 * alpha * p.c ^ 2 * (p.I / p.lambda₀) ≤ 1 := by
    calc
      4 * alpha * p.c ^ 2 * (p.I / p.lambda₀) =
          (4 * alpha * p.c ^ 2 * p.I) / p.lambda₀ := by ring
      _ ≤ 1 := (div_le_iff₀ model.lambda₀_pos).2 (by
        simpa only [one_mul] using hfour)
  have hfourD : 4 * alpha * p.c ^ 2 * D ≤ 1 :=
    hDscaled.trans hceiling
  rw [le_sub_iff_add_le]
  apply (le_div_iff₀ halpha).2
  have hinv : (1 / (2 * alpha)) * alpha = 1 / 2 := by
    field_simp [halpha.ne']
  rw [add_mul, hinv]
  nlinarith

/-- The canonical ceiling enforces the strict dominance ratio printed in
the proposition. -/
theorem saddlePassageAlphaCeiling_dominance
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho : ℝ} (weighted : WeightedThresholdAssumption p rho) :
    2 * p.c * saddlePassageAlphaCeiling p weighted *
        driftStationaryStockLipschitzBound p <
      1 - p.s weighted.βdagger := by
  let K := driftStationaryStockLipschitzBound p
  let gap := 1 - p.s weighted.βdagger
  have hK : 0 < K := by
    simpa only [K] using driftStationaryStockLipschitzBound_pos model
  have hcK : 0 < 4 * p.c * K :=
    mul_pos (mul_pos (by norm_num) model.c_pos) hK
  have hle : saddlePassageAlphaCeiling p weighted ≤ gap / (4 * p.c * K) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hmul : saddlePassageAlphaCeiling p weighted * (4 * p.c * K) ≤ gap :=
    (le_div_iff₀ hcK).1 hle
  have hgap : 0 < gap := by
    have hs := driftStockMultiplier_nonneg_le model
      (show weighted.βdagger ∈ Icc (0 : ℝ) 1 from
        ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩)
    dsimp only [gap]
    linarith [model.lambda₀_pos]
  dsimp only [K, gap] at hmul hgap ⊢
  nlinarith

/-! ## Uniform constants for the finite surgery -/

/-- A uniform positive floor for every crossing action's excess over the
corrected barrier on the quarter-mesh interval. -/
def passageSurgeryGapLower
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (L : ℝ) : ℝ :=
  L * weightedBarrierArea weighted

/-- A rate-free upper bound for the excess of every crossing action admitted
by the surgery predicate. -/
def passageSurgeryGapUpper
    (p : LoopParams) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (L : ℝ) : ℝ :=
  4 * L * weightedBarrierArea weighted +
    smallRateStrategyRemainderBound p L + 1

/-- A rate-free multiplier making the terminal Selection window wide enough
while retaining a positive lower endpoint. -/
def passageSurgeryWindowMultiplier
    (p : LoopParams) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (L : ℝ) : ℝ :=
  let C := passageLocalOneClimbQuadraticConstant p weighted L
  let G := passageSurgeryGapLower weighted L
  1 + (784 * C + 1) / G

/-- The final uniform coefficient produced by the truncate-before surgery.
The logarithmic factor is retained in the proposition, although the proved
local overhead is already quadratic without it. -/
def passageSurgeryErrorConstant
    (p : LoopParams) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (L : ℝ) : ℝ :=
  13 * passageLocalOneClimbQuadraticConstant p weighted L *
    passageSurgeryWindowMultiplier p weighted L ^ 2 *
      passageSurgeryGapUpper p weighted L

/-- The construction ceiling simultaneously enforces the quarter-mesh
branch, residual absorption, terminal-window geometry, and room for the
one-climb continuation. -/
def passageSurgeryAlphaCeiling
    (p : LoopParams) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (L : ℝ) : ℝ :=
  let C := passageLocalOneClimbQuadraticConstant p weighted L
  let W := passageSurgeryWindowMultiplier p weighted L
  let G := passageSurgeryGapUpper p weighted L
  min (saddlePassageAlphaCeiling p weighted) <| min (1 / (4 * L)) <|
    min (1 / (192 * C)) <| min
      (weighted.βdagger / (W * G))
      ((1 - weighted.βdagger) / (passageGradientBound p + 2))

/-- The lower gap constant is strictly positive. -/
theorem passageSurgeryGapLower_pos
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho L : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    0 < passageSurgeryGapLower weighted L := by
  simp only [passageSurgeryGapLower]
  exact mul_pos
    (lipschitzConstantOn_weightedBarrierIntegrand_pos weighted hL)
    (weightedBarrierArea_pos model weighted)

/-- The admitted-action upper gap constant is strictly positive. -/
theorem passageSurgeryGapUpper_pos
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho L : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    0 < passageSurgeryGapUpper p weighted L := by
  have hrem := smallRateStrategyRemainderBound_nonneg model hL.nonneg
  have harea := (weightedBarrierArea_pos model weighted).le
  have hfirst : 0 ≤ 4 * L * weightedBarrierArea weighted :=
    mul_nonneg (mul_nonneg (by norm_num) hL.nonneg) harea
  simp only [passageSurgeryGapUpper]
  linarith only [hfirst, hrem]

/-- The Selection-window multiplier is greater than one. -/
theorem one_lt_passageSurgeryWindowMultiplier
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho L : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    1 < passageSurgeryWindowMultiplier p weighted L := by
  have hC := passageLocalOneClimbQuadraticConstant_pos model weighted hL
  have hG := passageSurgeryGapLower_pos model weighted hL
  simp only [passageSurgeryWindowMultiplier]
  have : 0 < (784 * passageLocalOneClimbQuadraticConstant p weighted L + 1) /
      passageSurgeryGapLower weighted L := by positivity
  linarith

/-- The final uniform error coefficient is nonnegative (indeed positive). -/
theorem passageSurgeryErrorConstant_pos
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho L : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    0 < passageSurgeryErrorConstant p weighted L := by
  simp only [passageSurgeryErrorConstant]
  exact mul_pos
    (mul_pos
      (mul_pos (by norm_num)
        (passageLocalOneClimbQuadraticConstant_pos model weighted hL))
      (sq_pos_of_pos
        (zero_lt_one.trans
          (one_lt_passageSurgeryWindowMultiplier model weighted hL))))
    (passageSurgeryGapUpper_pos model weighted hL)

/-- The construction ceiling is strictly positive. -/
theorem passageSurgeryAlphaCeiling_pos
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho L : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    0 < passageSurgeryAlphaCeiling p weighted L := by
  let C := passageLocalOneClimbQuadraticConstant p weighted L
  let W := passageSurgeryWindowMultiplier p weighted L
  let G := passageSurgeryGapUpper p weighted L
  have hLpos := lipschitzConstantOn_weightedBarrierIntegrand_pos weighted hL
  have hC : 0 < C := by
    simpa only [C] using
      passageLocalOneClimbQuadraticConstant_pos model weighted hL
  have hW : 0 < W := by
    simpa only [W] using
      (zero_lt_one.trans
        (one_lt_passageSurgeryWindowMultiplier model weighted hL))
  have hG : 0 < G := by
    simpa only [G] using passageSurgeryGapUpper_pos model weighted hL
  have hP : 0 < passageGradientBound p + 2 := by
    linarith [passageGradientBound_pos model]
  simp only [passageSurgeryAlphaCeiling, lt_min_iff]
  exact ⟨saddlePassageAlphaCeiling_pos model weighted,
    one_div_pos.mpr (mul_pos (by norm_num) hLpos),
    one_div_pos.mpr (mul_pos (by norm_num) hC),
    div_pos weighted.βdagger_mem.1 (mul_pos hW hG),
    div_pos (sub_pos.mpr weighted.βdagger_mem.2) hP⟩

/-- Every construction rate is below the canonical ceiling. -/
theorem passageSurgeryAlphaCeiling_le_canonical
    (p : LoopParams) {rho L : ℝ}
    (weighted : WeightedThresholdAssumption p rho) :
    passageSurgeryAlphaCeiling p weighted L ≤
      saddlePassageAlphaCeiling p weighted := by
  simp only [passageSurgeryAlphaCeiling]
  exact min_le_left _ _

/-- The construction ceiling lies in `(0,1]`. -/
theorem passageSurgeryAlphaCeiling_mem_Ioc
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho L : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    passageSurgeryAlphaCeiling p weighted L ∈ Ioc (0 : ℝ) 1 :=
  ⟨passageSurgeryAlphaCeiling_pos model weighted hL,
    (passageSurgeryAlphaCeiling_le_canonical p weighted).trans
      (saddlePassageAlphaCeiling_mem_Ioc model weighted).2⟩

/-- All four noncanonical rate restrictions can be recovered from the
construction ceiling. -/
theorem passageSurgeryAlphaCeiling_aux_bounds
    (p : LoopParams) {rho L : ℝ}
    (weighted : WeightedThresholdAssumption p rho) :
    passageSurgeryAlphaCeiling p weighted L ≤ 1 / (4 * L) ∧
    passageSurgeryAlphaCeiling p weighted L ≤
      1 / (192 * passageLocalOneClimbQuadraticConstant p weighted L) ∧
    passageSurgeryAlphaCeiling p weighted L ≤
      weighted.βdagger /
        (passageSurgeryWindowMultiplier p weighted L *
          passageSurgeryGapUpper p weighted L) ∧
    passageSurgeryAlphaCeiling p weighted L ≤
      (1 - weighted.βdagger) / (passageGradientBound p + 2) := by
  simp only [passageSurgeryAlphaCeiling]
  refine ⟨(min_le_right _ _).trans (min_le_left _ _), ?_⟩
  refine ⟨(min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)), ?_⟩
  refine ⟨(min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))), ?_⟩
  exact (min_le_right _ _).trans
    ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))

/-- The smaller construction ceiling retains the paper's strict
stationary-characteristic dominance condition. -/
theorem passageSurgeryAlphaCeiling_dominance
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho L : ℝ} (weighted : WeightedThresholdAssumption p rho) :
    2 * p.c * passageSurgeryAlphaCeiling p weighted L *
        driftStationaryStockLipschitzBound p <
      1 - p.s weighted.βdagger := by
  have hcoef : 0 ≤ 2 * p.c * driftStationaryStockLipschitzBound p := by
    exact mul_nonneg (mul_nonneg (by norm_num) model.c_pos.le)
      (driftStationaryStockLipschitzBound_pos model).le
  have hle := mul_le_mul_of_nonneg_right
    (passageSurgeryAlphaCeiling_le_canonical p (L := L) weighted) hcoef
  have hcanonical := saddlePassageAlphaCeiling_dominance model weighted
  have hle' :
      2 * p.c * passageSurgeryAlphaCeiling p weighted L *
          driftStationaryStockLipschitzBound p ≤
        2 * p.c * saddlePassageAlphaCeiling p weighted *
          driftStationaryStockLipschitzBound p := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hle
  exact hle'.trans_lt hcanonical

/-- The explicit upper strategy's leading coefficient exceeds the corrected
barrier coefficient by at most `4 L`. -/
theorem two_div_area_le_passageLowerBarrier_add_four_L_area
    {p : LoopParams} {rho alpha L : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    (halpha : 0 < alpha) (hL : 0 ≤ L) :
    (2 / alpha) * weightedBarrierArea weighted ≤
      passageLowerBarrierAtRate weighted L alpha +
        4 * L * weightedBarrierArea weighted := by
  have ht : 0 ≤ alpha * L := mul_nonneg halpha.le hL
  have hden : 0 < 1 + 2 * alpha * L := by positivity
  have hid :
      2 / alpha - 2 / (alpha * (1 + 2 * alpha * L)) =
        4 * L / (1 + 2 * alpha * L) := by
    field_simp [halpha.ne', hden.ne']
    ring
  have hfrac : 4 * L / (1 + 2 * alpha * L) ≤ 4 * L := by
    apply (div_le_iff₀ hden).2
    nlinarith only [hL, ht]
  have hcoefficient :
      2 / alpha ≤ 2 / (alpha * (1 + 2 * alpha * L)) + 4 * L := by
    linarith only [hid, hfrac]
  have harea : 0 ≤ weightedBarrierArea weighted := by
    simp only [weightedBarrierArea]
    exact intervalIntegral.integral_nonneg weighted.βdagger_mem.1.le
      (fun beta hbeta ↦ weighted.barrier_nonneg_before hbeta)
  have hscaled := mul_le_mul_of_nonneg_right hcoefficient harea
  simp only [passageLowerBarrierAtRate]
  nlinarith only [hscaled]

/-- Scalar Selection budget used by the uniform construction.  A gap `Y`
above its positive rate-free floor is paid by the window
`W * alpha * Y`; the two coupled coefficients supply the inverse powers of
`alpha`. -/
theorem passageSurgery_selection_gap_lt
    {alpha L C G W Y : ℝ}
    (halpha : 0 < alpha) (hsmall : alpha * L ≤ 1)
    (hC : 0 < C) (hG : 0 < G) (hGY : G ≤ Y)
    (hW : W = 1 + (784 * C + 1) / G) :
    Y < (coupledCellFactor (alpha * L) / alpha) *
      (((coupledCellFactor (alpha * L) / alpha) / (196 * C)) *
        (W * alpha * Y) ^ 2 / 4) := by
  let scale := coupledCellFactor (alpha * L) / alpha
  have hscale : 0 < scale := by
    dsimp only [scale]
    exact div_pos (coupledCellFactor_pos (alpha * L)) halpha
  have hscaleEq : scale = 2 / alpha - L := by
    dsimp only [scale]
    exact coupledCellFactor_div_eq_two_div_sub halpha hsmall
  have hscaleAlpha : 1 ≤ scale * alpha := by
    rw [hscaleEq]
    have hid : (2 / alpha - L) * alpha = 2 - alpha * L := by
      field_simp [halpha.ne']
    rw [hid]
    linarith
  have hscaleAlphaSq : 1 ≤ (scale * alpha) ^ 2 := by
    nlinarith only [hscaleAlpha]
  have hWone : 1 < W := by
    rw [hW]
    have : 0 < (784 * C + 1) / G := by positivity
    linarith
  have hWG : 784 * C < W * G := by
    rw [hW]
    have hcancel : ((784 * C + 1) / G) * G = 784 * C + 1 := by
      field_simp [hG.ne']
    rw [add_mul, one_mul, hcancel]
    linarith only [hG]
  have hWY : W * G ≤ W * Y :=
    mul_le_mul_of_nonneg_left hGY (zero_lt_one.trans hWone).le
  have hkey : 784 * C < W ^ 2 * Y := by
    have hfirst : 784 * C < W * Y := hWG.trans_le hWY
    have hWYpos : 0 < W * Y := by
      exact mul_pos (zero_lt_one.trans hWone) (hG.trans_le hGY)
    have hsecond : W * Y ≤ W * (W * Y) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hWone.le hWYpos.le
    have hrewrite : W * (W * Y) = W ^ 2 * Y := by ring
    rw [hrewrite] at hsecond
    exact hfirst.trans_le hsecond
  have hYpos : 0 < Y := hG.trans_le hGY
  have hmulY := mul_lt_mul_of_pos_right hkey hYpos
  have hscalePay : W ^ 2 * Y ^ 2 ≤
      (scale * alpha) ^ 2 * (W ^ 2 * Y ^ 2) := by
    have hnonneg : 0 ≤ W ^ 2 * Y ^ 2 := by positivity
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hscaleAlphaSq hnonneg
  have hcore : 784 * C * Y <
      (scale * alpha) ^ 2 * (W ^ 2 * Y ^ 2) := by
    have hrewrite : W ^ 2 * Y * Y = W ^ 2 * Y ^ 2 := by ring
    rw [hrewrite] at hmulY
    exact hmulY.trans_le hscalePay
  have hden : 0 < 784 * C := mul_pos (by norm_num) hC
  have hquotient :
      Y < (scale * alpha) ^ 2 * (W ^ 2 * Y ^ 2) / (784 * C) :=
    (lt_div_iff₀ hden).2 (by
      simpa only [mul_comm] using hcore)
  have hid :
      scale * ((scale / (196 * C)) * (W * alpha * Y) ^ 2 / 4) =
        (scale * alpha) ^ 2 * (W ^ 2 * Y ^ 2) / (784 * C) := by
    field_simp [hC.ne']
    ring
  dsimp only [scale] at hid ⊢
  rw [hid]
  exact hquotient

/-- The finite-path construction isolated by the proof.  It asks
for one constant, independent of the replacement rate, which turns every
`nu`-near-minimal finite crossing below the explicit two-phase cost plus one
into a basin exit after charging the printed quadratic/logarithmic overhead
with the same `nu` tolerance.  The extra ceiling removes arbitrary,
highly-nonminimal crossings that the paper never uses; the variational
reduction obtains it by choosing its approximation tolerance at most one. -/
def HasUniformSaddlePassageSurgery
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    (L alphaZero C : ℝ) : Prop :=
  ∀ ⦃alpha nu a : ℝ⦄, 0 < alpha → alpha ≤ alphaZero →
    0 < nu →
    a ∈ crossingActionSet (weighted.withOperatorRate alpha) →
    a ≤ civicCrossingQuasipotentialAtRate weighted alpha + nu →
    a ≤ upwardStrategyCostAtRate weighted alpha + 1 →
    ∃ e ∈ quasipotentialActionSet (withOperatorRate p alpha) rho,
      e ≤ a + C * alpha ^ 2 *
        (civicCrossingQuasipotentialAtRate weighted alpha -
            passageLowerBarrierAtRate weighted L alpha + nu) *
          passageLogFactor alpha

/-- The burden-aware truncate-before construction supplies the uniform
finite-path surgery.  The selected cell itself is discarded; its whole
suffix refund pays one natural margin climb and an exact sign-free exit
hold.  The resulting local error is `O(w^2)`, so the printed logarithmic
factor is used only through its lower bound by one. -/
theorem hasUniformSaddlePassageSurgery_oneClimb
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho L : ℝ} (hrho : 0 ≤ rho) (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    HasUniformSaddlePassageSurgery weighted L
      (passageSurgeryAlphaCeiling p weighted L)
      (passageSurgeryErrorConstant p weighted L) := by
  intro alpha nu action halpha halphaLe hnu haMem hnear hactionCeiling
  let q := withOperatorRate p alpha
  let modelq : DriftModelAssumptions q := model.withOperatorRate halpha
  let weightedq : WeightedThresholdAssumption q rho :=
    weighted.withOperatorRate alpha
  have halphaCanonical : alpha ≤ saddlePassageAlphaCeiling p weighted :=
    halphaLe.trans
      (passageSurgeryAlphaCeiling_le_canonical p (L := L) weighted)
  let ssq : SmallStepAssumption q :=
    smallStepAssumption_withOperatorRate_of_le_passageCeiling
      model weighted halpha.le halphaCanonical
  have hLq : IsLipschitzConstantOn
      (weightedBarrierIntegrand q rho) L 0 weightedq.βdagger := by
    change IsLipschitzConstantOn
      (weightedBarrierIntegrand (withOperatorRate p alpha) rho) L
        0 weighted.βdagger
    have hfun : weightedBarrierIntegrand (withOperatorRate p alpha) rho =
        weightedBarrierIntegrand p rho := by
      funext beta
      exact withOperatorRate_weightedBarrierIntegrand p alpha rho beta
    rw [hfun]
    exact hL
  let B := passageLowerBarrierAtRate weighted L alpha
  let scale := coupledCellFactor (alpha * L) / alpha
  let C := passageLocalOneClimbQuadraticConstant p weighted L
  let Glo := passageSurgeryGapLower weighted L
  let Ghi := passageSurgeryGapUpper p weighted L
  let W := passageSurgeryWindowMultiplier p weighted L
  let Y := action - B
  let w := W * alpha * Y
  let selection := scale / (196 * C)
  have hLpos := lipschitzConstantOn_weightedBarrierIntegrand_pos weighted hL
  have hC : 0 < C := by
    simpa only [C] using
      passageLocalOneClimbQuadraticConstant_pos model weighted hL
  have hGlo : 0 < Glo := by
    simpa only [Glo] using passageSurgeryGapLower_pos model weighted hL
  have hGhi : 0 < Ghi := by
    simpa only [Ghi] using passageSurgeryGapUpper_pos model weighted hL
  have hWone : 1 < W := by
    simpa only [W] using
      one_lt_passageSurgeryWindowMultiplier model weighted hL
  have halphaOne : alpha ≤ 1 :=
    halphaLe.trans (passageSurgeryAlphaCeiling_mem_Ioc model weighted hL).2
  have haux := passageSurgeryAlphaCeiling_aux_bounds p (L := L) weighted
  have halphaQuarterCeiling : alpha ≤ 1 / (4 * L) :=
    halphaLe.trans haux.1
  have hquarter : alpha * L ≤ 1 / 4 := by
    have hden : 0 < 4 * L := mul_pos (by norm_num) hLpos
    have hmul := (le_div_iff₀ hden).1 halphaQuarterCeiling
    nlinarith only [hmul]
  have hsmall : alpha * L ≤ 1 := by linarith
  have halphaResidualCeiling : alpha ≤ 1 / (192 * C) := by
    simpa only [C] using halphaLe.trans haux.2.1
  have hresidualAbsorb : 192 * C * alpha ^ 2 ≤ 1 := by
    have hden : 0 < 192 * C := mul_pos (by norm_num) hC
    have hlinear := (le_div_iff₀ hden).1 halphaResidualCeiling
    have hsquare : alpha ^ 2 ≤ alpha := by nlinarith only [halpha, halphaOne]
    have hscaled := mul_le_mul_of_nonneg_left hsquare hden.le
    nlinarith only [hlinear, hscaled]
  have halphaGeometryCeiling :
      alpha ≤ weighted.βdagger / (W * Ghi) := by
    simpa only [W, Ghi] using halphaLe.trans haux.2.2.1
  have hgeometry : alpha * W * Ghi ≤ weighted.βdagger := by
    have hden : 0 < W * Ghi :=
      mul_pos (zero_lt_one.trans hWone) hGhi
    have hmul := (le_div_iff₀ hden).1 halphaGeometryCeiling
    nlinarith only [hmul]
  have halphaRoomCeiling :
      alpha ≤ (1 - weighted.βdagger) /
        (passageGradientBound p + 2) := by
    simpa only using halphaLe.trans haux.2.2.2
  have hP : 0 < passageGradientBound p + 2 := by
    linarith [passageGradientBound_pos model]
  have hroomWide : alpha * (passageGradientBound p + 2) ≤
      1 - weighted.βdagger :=
    (le_div_iff₀ hP).1 halphaRoomCeiling
  have hroom : alpha * (passageGradientBound p + 2 * alpha) ≤
      1 - weighted.βdagger := by
    have hinner : passageGradientBound p + 2 * alpha ≤
        passageGradientBound p + 2 := by linarith
    exact (mul_le_mul_of_nonneg_left hinner halpha.le).trans hroomWide
  have hupperRoom : alpha * (p.v + alpha) ≤
      1 - weighted.βdagger := by
    have hprimitive : p.v + alpha ≤
        passageGradientBound p + 2 * alpha := by
      have hterm : 0 ≤ 2 * p.c * (p.I / p.lambda₀) := by
        exact mul_nonneg (mul_nonneg (by norm_num) model.c_pos.le)
          (div_nonneg model.I_pos.le model.lambda₀_pos.le)
      simp only [passageGradientBound]
      linarith
    exact (mul_le_mul_of_nonneg_left hprimitive halpha.le).trans hroom
  have hfour : 4 * alpha * p.c ^ 2 * p.I ≤ p.lambda₀ :=
    four_alpha_c_sq_I_le_lambda_of_le_passageCeiling
      model weighted halphaCanonical
  obtain ⟨N, uFin, hcross, haEq⟩ := haMem
  let u := extendFiniteControl uFin
  let x := finiteControlledOrbit q rho uFin
  let path : IsControlledCivicWeightedPath q rho u x :=
    finiteControlledOrbit_isControlled q rho uFin
  have hactionEq : controlAction u N = gaussianVectorAction uFin := by
    simpa only [u] using controlAction_extendFiniteControl uFin
  have hactionDef : action = gaussianVectorAction uFin := haEq
  have hcross' : weightedq.βdagger ≤ policyRunningMax x N := by
    simpa only [weightedq, x] using hcross
  have hlowerCoupled := path.coupled_action_lower_bound_of_crossing
    modelq ssq (by simpa only [q, withOperatorRate_c] using hcoop)
      weightedq hLq hcross'
  rw [hactionEq, ← hactionDef] at hlowerCoupled
  have hseparation := passageLowerBarrier_add_L_area_le_coupledBarrier
    weighted halpha hL.nonneg hquarter
  have hseparation' : B + Glo ≤
      scale * weightedBarrierArea weighted := by
    simpa only [B, Glo, scale, passageSurgeryGapLower] using hseparation
  have hlowerCoupled' :
      scale * weightedBarrierArea weighted ≤ action := by
    change (coupledCellFactor (q.α * L) / q.α) *
      weightedBarrierArea weightedq ≤ action at hlowerCoupled
    rw [weightedBarrierArea_withOperatorRate] at hlowerCoupled
    simpa only [q, scale, withOperatorRate_alpha] using hlowerCoupled
  have hGloY : Glo ≤ Y := by
    dsimp only [Y]
    linarith only [hseparation', hlowerCoupled']
  have hYpos : 0 < Y := hGlo.trans_le hGloY
  have hstrategyUpper :=
    upwardStrategyCostAtRate_upper_bound_of_le_passageCeiling
      model hrho hcoop weighted hL halpha halphaCanonical halphaOne hupperRoom
  have hleading :=
    two_div_area_le_passageLowerBarrier_add_four_L_area
      weighted halpha hL.nonneg
  have hYGhi : Y ≤ Ghi := by
    dsimp only [Y, B, Ghi, passageSurgeryGapUpper]
    linarith only [hactionCeiling, hstrategyUpper, hleading]
  have hWdef : W = 1 + (784 * C + 1) / Glo := by
    rfl
  have hselectionGap : Y < scale * (selection * w ^ 2 / 4) := by
    simpa only [selection, w] using
      passageSurgery_selection_gap_lt halpha hsmall hC hGlo hGloY hWdef
  have hWGloOne : 1 < W * Glo := by
    rw [hWdef]
    have hcancel : ((784 * C + 1) / Glo) * Glo = 784 * C + 1 := by
      field_simp [hGlo.ne']
    rw [add_mul, one_mul, hcancel]
    nlinarith only [hGlo, hC]
  have hWYOne : 1 ≤ W * Y := by
    have hmono := mul_le_mul_of_nonneg_left hGloY
      (zero_lt_one.trans hWone).le
    exact hWGloOne.le.trans hmono
  have hwAlpha : alpha ≤ w := by
    dsimp only [w]
    have hscaled := mul_le_mul_of_nonneg_left hWYOne halpha.le
    nlinarith only [hscaled]
  have hwPos : 0 < w := halpha.trans_le hwAlpha
  have hwSaddle : w ≤ weighted.βdagger := by
    have hWYUpper := mul_le_mul_of_nonneg_left hYGhi
      (zero_lt_one.trans hWone).le
    have hscaled := mul_le_mul_of_nonneg_left hWYUpper halpha.le
    dsimp only [w]
    nlinarith only [hscaled, hgeometry]
  have hlo : 0 ≤ weightedq.βdagger - w := by
    simpa only [weightedq,
      WeightedThresholdAssumption.withOperatorRate_βdagger] using
      sub_nonneg.mpr hwSaddle
  have hlohi : weightedq.βdagger - w < weightedq.βdagger := by
    linarith only [hwPos]
  have hselectionPos : 0 < selection := by
    dsimp only [selection, scale]
    exact div_pos
      (div_pos (coupledCellFactor_pos (alpha * L)) halpha)
      (mul_pos (by norm_num) hC)
  have hgapForSelection :
      controlAction u N -
          (2 / (q.α * (1 + 2 * q.α * L))) *
            weightedBarrierArea weightedq <
        (coupledCellFactor (q.α * L) / q.α) *
          (selection *
            (weightedq.βdagger -
              (weightedq.βdagger - w)) ^ 2 / 4) := by
    rw [hactionEq, ← hactionDef]
    simpa only [q, weightedq, B, Y, scale, passageLowerBarrierAtRate,
      withOperatorRate_alpha,
      WeightedThresholdAssumption.withOperatorRate_βdagger,
      weightedBarrierArea_withOperatorRate, sub_sub_cancel] using hselectionGap
  have hdominated :=
    path.hasDominatedPassageBurdenWindowCell_of_actionGap_lt
      modelq ssq (by simpa only [q, withOperatorRate_c] using hcoop)
      weightedq hLq hselectionPos hlo hlohi le_rfl hcross' hgapForSelection
  obtain ⟨n, hn, hadvance, hwindow, hburden⟩ :=
    path.exists_dominatedPassageBurdenWindowStep
      modelq ssq (by simpa only [q, withOperatorRate_c] using hcoop)
        weightedq hdominated
  have hburdenAbsorb :
      49 * passageLocalOneClimbQuadraticConstant q weightedq L * selection ≤
        (coupledCellFactor (q.α * L) / q.α) / 4 := by
    have heq : 49 * C * selection = scale / 4 := by
      dsimp only [selection]
      field_simp [hC.ne']
      ring
    simpa only [q, weightedq, C, scale,
      passageLocalOneClimbQuadraticConstant_withOperatorRate,
      withOperatorRate_alpha] using heq.le
  have hresidualAbsorbQ :
      192 * passageLocalOneClimbQuadraticConstant q weightedq L * q.α ^ 2 ≤ 1 := by
    simpa only [q, weightedq,
      passageLocalOneClimbQuadraticConstant_withOperatorRate,
      withOperatorRate_alpha, C] using hresidualAbsorb
  obtain ⟨exitCost, hexitMem, hexitBound⟩ :=
    path.exists_exitAction_le_action_add_selectedWindowQuadratic
      modelq ssq hrho (by simpa only [q, withOperatorRate_cureThreshold] using hrhoCure)
        (by simpa only [q, withOperatorRate_c] using hcoop)
        weightedq hLq halphaOne hquarter
        (by simpa only [q, withOperatorRate_alpha, withOperatorRate_c,
          withOperatorRate_I, withOperatorRate_lambda₀] using hfour)
        hwAlpha (by simpa only [weightedq,
          WeightedThresholdAssumption.withOperatorRate_βdagger] using hwSaddle)
        (by
          change alpha * (passageGradientBound p + 2 * alpha) ≤
            1 - weighted.βdagger
          exact hroom)
        hn hcross' hadvance hwindow hburden hburdenAbsorb hresidualAbsorbQ
  have hexitBound' : exitCost ≤ action + 13 * C * w ^ 2 := by
    rw [hactionEq, ← hactionDef] at hexitBound
    simpa only [q, weightedq, C,
      passageLocalOneClimbQuadraticConstant_withOperatorRate] using hexitBound
  have hYGap : Y ≤
      civicCrossingQuasipotentialAtRate weighted alpha - B + nu := by
    dsimp only [Y]
    linarith only [hnear]
  have hGapPos : 0 <
      civicCrossingQuasipotentialAtRate weighted alpha - B + nu :=
    hYpos.trans_le hYGap
  have hYsq : Y ^ 2 ≤ Ghi *
      (civicCrossingQuasipotentialAtRate weighted alpha - B + nu) := by
    have hmul := mul_le_mul hYGhi hYGap hYpos.le hGhi.le
    nlinarith only [hmul]
  have hlog := one_le_passageLogFactor_of_pos_of_le_one halpha halphaOne
  have hoverhead : 13 * C * w ^ 2 ≤
      passageSurgeryErrorConstant p weighted L * alpha ^ 2 *
        (civicCrossingQuasipotentialAtRate weighted alpha - B + nu) *
          passageLogFactor alpha := by
    let Gap := civicCrossingQuasipotentialAtRate weighted alpha - B + nu
    have hcoef : 0 ≤ 13 * C * W ^ 2 * alpha ^ 2 := by positivity
    have hsquarePay := mul_le_mul_of_nonneg_left hYsq hcoef
    have hpreLog : 13 * C * W ^ 2 * alpha ^ 2 * Y ^ 2 ≤
        13 * C * W ^ 2 * Ghi * alpha ^ 2 * Gap := by
      dsimp only [Gap] at hsquarePay ⊢
      nlinarith only [hsquarePay]
    have hlogPay :
        13 * C * W ^ 2 * Ghi * alpha ^ 2 * Gap ≤
          13 * C * W ^ 2 * Ghi * alpha ^ 2 * Gap *
            passageLogFactor alpha := by
      have hnonneg : 0 ≤ 13 * C * W ^ 2 * Ghi * alpha ^ 2 * Gap := by
        dsimp only [Gap]
        positivity
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hlog hnonneg
    calc
      13 * C * w ^ 2 = 13 * C * W ^ 2 * alpha ^ 2 * Y ^ 2 := by
        dsimp only [w]
        ring
      _ ≤ 13 * C * W ^ 2 * Ghi * alpha ^ 2 * Gap := hpreLog
      _ ≤ 13 * C * W ^ 2 * Ghi * alpha ^ 2 * Gap *
          passageLogFactor alpha := hlogPay
      _ = passageSurgeryErrorConstant p weighted L * alpha ^ 2 *
          (civicCrossingQuasipotentialAtRate weighted alpha - B + nu) *
            passageLogFactor alpha := by
        dsimp only [passageSurgeryErrorConstant, C, W, Ghi, B, Gap]
  refine ⟨exitCost, ?_, hexitBound'.trans (add_le_add_right hoverhead action)⟩
  simpa only [q] using hexitMem

/-- Variational reduction for the `prop:passage`: a uniform
finite-path surgery implies the claimed uniform quasipotential inequality.
No compactness or continuity of either infimum is assumed; both infima are
approximated from above and the tolerance is sent to zero explicitly. -/
theorem quantitativeSaddlePassage_uniform_of_surgery
    {p : LoopParams} (model : DriftModelAssumptions p)
    (threshold : ThresholdAssumption p)
    {rho L C alphaZero : ℝ}
    (hrho : 0 ≤ rho) (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (_hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (hC : 0 ≤ C)
    (halphaZero : alphaZero ∈ Ioc (0 : ℝ) 1)
    (halphaZeroCanonical : alphaZero ≤ saddlePassageAlphaCeiling p weighted)
    (hdominance :
      2 * p.c * alphaZero * driftStationaryStockLipschitzBound p <
        1 - p.s weighted.βdagger)
    (surgery : HasUniformSaddlePassageSurgery weighted L alphaZero C) :
    ∃ alphaZero ∈ Ioc (0 : ℝ) 1,
      2 * p.c * alphaZero * driftStationaryStockLipschitzBound p <
        1 - p.s weighted.βdagger ∧
      ∀ ⦃alpha : ℝ⦄, 0 < alpha → alpha ≤ alphaZero →
        civicCrossingQuasipotentialAtRate weighted alpha ≤
            civicQuasipotentialAtRate p rho alpha ∧
          civicQuasipotentialAtRate p rho alpha ≤
            civicCrossingQuasipotentialAtRate weighted alpha +
              C * alpha ^ 2 *
                (civicCrossingQuasipotentialAtRate weighted alpha -
                  passageLowerBarrierAtRate weighted L alpha) *
                passageLogFactor alpha := by
  refine ⟨alphaZero, halphaZero, hdominance, ?_⟩
  intro alpha halpha halphaLe
  let q := withOperatorRate p alpha
  let modelq : DriftModelAssumptions q := model.withOperatorRate halpha
  let ssq : SmallStepAssumption q :=
    smallStepAssumption_withOperatorRate_of_le_passageCeiling
      model weighted halpha.le (halphaLe.trans halphaZeroCanonical)
  let thresholdq : ThresholdAssumption q := threshold.withOperatorRate alpha
  let weightedq : WeightedThresholdAssumption q rho :=
    weighted.withOperatorRate alpha
  have hcrossExit : civicCrossingQuasipotentialAtRate weighted alpha ≤
      civicQuasipotentialAtRate p rho alpha := by
    simpa only [civicCrossingQuasipotentialAtRate,
      civicQuasipotentialAtRate, q, weightedq] using
      civicCrossingQuasipotential_le_civicQuasipotential
        modelq ssq thresholdq hrho (by simpa [q] using hrhoCure)
          (by simpa [q] using hcoop) weightedq
  refine ⟨hcrossExit, ?_⟩
  let X := civicCrossingQuasipotentialAtRate weighted alpha
  let V := civicQuasipotentialAtRate p rho alpha
  let B := passageLowerBarrierAtRate weighted L alpha
  let k := C * alpha ^ 2 * passageLogFactor alpha
  have halphaOne : alpha ≤ 1 :=
    halphaLe.trans halphaZero.2
  have hlog : 0 < passageLogFactor alpha :=
    passageLogFactor_pos_of_pos_of_le_one halpha halphaOne
  have hk : 0 ≤ k := by
    dsimp only [k]
    positivity
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  let delta := min 1 (epsilon / (1 + k))
  have hden : 0 < 1 + k := by linarith
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min zero_lt_one (div_pos hepsilon hden)
  have hdeltaOne : delta ≤ 1 := by
    dsimp only [delta]
    exact min_le_left _ _
  have hdeltaScaled : delta * (1 + k) ≤ epsilon := by
    have hle : delta ≤ epsilon / (1 + k) := by
      dsimp only [delta]
      exact min_le_right _ _
    exact (le_div_iff₀ hden).1 hle
  obtain ⟨T, u, hcross, haction⟩ :=
    exists_crossing_control_lt_quasipotential_add
      modelq weightedq hdelta
  let a := gaussianVectorAction u
  have haMem : a ∈ crossingActionSet weightedq :=
    ⟨T, u, hcross, rfl⟩
  have haLt : a < X + delta := by
    simpa only [a, X, civicCrossingQuasipotentialAtRate, weightedq] using haction
  have hVupper : V ≤ upwardStrategyCostAtRate weighted alpha := by
    simpa only [V, civicQuasipotentialAtRate, q, weightedq,
      upwardStrategyCostAtRate] using
      civicQuasipotential_le_upwardStrategyCost modelq ssq
        (by simpa [q] using hrhoCure) (by simpa [q] using hcoop) weightedq
  have haCeiling : a ≤ upwardStrategyCostAtRate weighted alpha + 1 := by
    linarith only [haLt, hcrossExit, hVupper, hdeltaOne]
  obtain ⟨e, heMem, heBound⟩ :=
    surgery halpha halphaLe hdelta haMem (by
      simpa only [a, X, weightedq] using haLt.le) haCeiling
  have hVle : V ≤ e := by
    change sInf (quasipotentialActionSet q rho) ≤ e
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro z ⟨N, v, x, _path, _hexit, rfl⟩
      exact controlAction_nonneg v N
    · simpa only [q] using heMem
  have heBound' : e ≤ a + k * (X - B + delta) := by
    change e ≤ a + C * alpha ^ 2 *
      (X - B + delta) * passageLogFactor alpha at heBound
    dsimp only [k]
    ring_nf at heBound ⊢
    exact heBound
  calc
    V ≤ e := hVle
    _ ≤ a + k * (X - B + delta) := heBound'
    _ ≤ (X + delta) + k * (X - B + delta) :=
      add_le_add haLt.le le_rfl
    _ ≤ X + k * (X - B) + epsilon := by
      have hid : (X + delta) + k * (X - B + delta) =
          X + k * (X - B) + delta * (1 + k) := by ring
      rw [hid]
      linarith only [hdeltaScaled]
    _ = civicCrossingQuasipotentialAtRate weighted alpha +
          C * alpha ^ 2 *
            (civicCrossingQuasipotentialAtRate weighted alpha -
              passageLowerBarrierAtRate weighted L alpha) *
            passageLogFactor alpha + epsilon := by
      dsimp only [X, B, k]
      ring

/-- Paper II, Proposition `prop:passage` in `civic_drift.tex`: holding all
primitives except the adaptation rate fixed, the crossing and basin-exit
quasipotentials differ by at most the stated uniform
`alpha^2 * gap * (1 + log (1 / alpha))` allowance for all sufficiently
small positive rates. -/
theorem quantitativeSaddlePassage_uniform
    {p : LoopParams} (model : DriftModelAssumptions p)
    (threshold : ThresholdAssumption p)
    {rho L : ℝ} (hrho : 0 ≤ rho) (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    ∃ alphaZero ∈ Ioc (0 : ℝ) 1,
      2 * p.c * alphaZero * driftStationaryStockLipschitzBound p <
        1 - p.s weighted.βdagger ∧
      ∀ ⦃alpha : ℝ⦄, 0 < alpha → alpha ≤ alphaZero →
        civicCrossingQuasipotentialAtRate weighted alpha ≤
            civicQuasipotentialAtRate p rho alpha ∧
          civicQuasipotentialAtRate p rho alpha ≤
            civicCrossingQuasipotentialAtRate weighted alpha +
              passageSurgeryErrorConstant p weighted L * alpha ^ 2 *
                (civicCrossingQuasipotentialAtRate weighted alpha -
                  passageLowerBarrierAtRate weighted L alpha) *
                passageLogFactor alpha := by
  exact quantitativeSaddlePassage_uniform_of_surgery
    model threshold hrho hrhoCure hcoop weighted hL
      (passageSurgeryErrorConstant_pos model weighted hL).le
      (passageSurgeryAlphaCeiling_mem_Ioc model weighted hL)
      (passageSurgeryAlphaCeiling_le_canonical p (L := L) weighted)
      (passageSurgeryAlphaCeiling_dominance model (L := L) weighted)
      (hasUniformSaddlePassageSurgery_oneClimb
        model hrho hrhoCure hcoop weighted hL)

/-- The literal fixed-parameter passage inequality with a sign-safe `log₊`
factor.  This is an order-theoretic consequence of the strict coupled ledger
and the upper strategy; it does not claim the uniform-in-rate constant of
`quantitativeSaddlePassage_uniform`. -/
theorem quantitativeSaddlePassage_logPlus
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho L : ℝ} (hrho : 0 ≤ rho) (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    ∃ C : ℝ, 0 ≤ C ∧
      civicCrossingQuasipotential weighted ≤ civicQuasipotential p rho ∧
      civicQuasipotential p rho ≤
        civicCrossingQuasipotential weighted +
          C * p.α ^ 2 *
            (civicCrossingQuasipotential weighted -
              (2 / (p.α * (1 + 2 * p.α * L))) *
                weightedBarrierArea weighted) *
            passageLogWeight p.α := by
  let B := (2 / (p.α * (1 + 2 * p.α * L))) *
    weightedBarrierArea weighted
  let S := (coupledCellFactor (p.α * L) / p.α) *
    weightedBarrierArea weighted
  let X := civicCrossingQuasipotential weighted
  let V := civicQuasipotential p rho
  let U := upwardStrategyCost weighted
  have hBS : B < S := by
    simpa only [B, S] using correctedBarrier_lt_coupledBarrier model weighted hL
  have hSX : S ≤ X := by
    simpa only [S, X] using
      coupledBarrier_le_civicCrossingQuasipotential
        model ss hcoop weighted hL
  have hXV : X ≤ V := by
    simpa only [X, V] using
      civicCrossingQuasipotential_le_civicQuasipotential
        model ss threshold hrho hrhoCure hcoop weighted
  have hVU : V ≤ U := by
    simpa only [V, U] using
      civicQuasipotential_le_upwardStrategyCost
        model ss hrhoCure hcoop weighted
  have hscale : 0 < p.α ^ 2 * passageLogWeight p.α :=
    mul_pos (sq_pos_of_pos model.α_pos) (passageLogWeight_pos p.α)
  obtain ⟨C, hC, hbound⟩ :=
    exists_scaled_gap_constant hBS hSX hXV hVU hscale
  refine ⟨C, hC, hXV, ?_⟩
  dsimp only [B, X, V] at hbound ⊢
  convert hbound using 1
  ring

/-- With an explicit positivity hypothesis on the raw logarithmic factor,
the fixed-parameter inequality follows by the same order argument.  The
factor's positivity is a genuine hypothesis at rates above `1/e`; the
uniform small-rate result is `quantitativeSaddlePassage_uniform`. -/
theorem quantitativeSaddlePassage_of_logFactor_pos
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho L : ℝ} (hrho : 0 ≤ rho) (hrhoCure : rho < cureThreshold p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (hlog : 0 < 1 + Real.log (1 / p.α)) :
    ∃ C : ℝ, 0 ≤ C ∧
      civicCrossingQuasipotential weighted ≤ civicQuasipotential p rho ∧
      civicQuasipotential p rho ≤
        civicCrossingQuasipotential weighted +
          C * p.α ^ 2 *
            (civicCrossingQuasipotential weighted -
              (2 / (p.α * (1 + 2 * p.α * L))) *
                weightedBarrierArea weighted) *
            (1 + Real.log (1 / p.α)) := by
  let B := (2 / (p.α * (1 + 2 * p.α * L))) *
    weightedBarrierArea weighted
  let S := (coupledCellFactor (p.α * L) / p.α) *
    weightedBarrierArea weighted
  let X := civicCrossingQuasipotential weighted
  let V := civicQuasipotential p rho
  let U := upwardStrategyCost weighted
  have hBS : B < S := by
    simpa only [B, S] using correctedBarrier_lt_coupledBarrier model weighted hL
  have hSX : S ≤ X := by
    simpa only [S, X] using
      coupledBarrier_le_civicCrossingQuasipotential
        model ss hcoop weighted hL
  have hXV : X ≤ V := by
    simpa only [X, V] using
      civicCrossingQuasipotential_le_civicQuasipotential
        model ss threshold hrho hrhoCure hcoop weighted
  have hVU : V ≤ U := by
    simpa only [V, U] using
      civicQuasipotential_le_upwardStrategyCost
        model ss hrhoCure hcoop weighted
  have hscale : 0 < p.α ^ 2 * (1 + Real.log (1 / p.α)) :=
    mul_pos (sq_pos_of_pos model.α_pos) hlog
  obtain ⟨C, hC, hbound⟩ :=
    exists_scaled_gap_constant hBS hSX hXV hVU hscale
  refine ⟨C, hC, hXV, ?_⟩
  dsimp only [B, X, V] at hbound ⊢
  convert hbound using 1
  ring

#print axioms IsControlledCivicWeightedPath.abs_stationaryStockLag_le_burden
#print axioms IsControlledCivicWeightedPath.exists_exitAction_le_action_add_selectedWindowQuadratic
#print axioms IsControlledCivicWeightedPath.passageBurdenWindowSuffix_refund
#print axioms IsControlledCivicWeightedPath.passageBurdenWindowSuffix_refund_add_residual
#print axioms IsControlledCivicWeightedPath.retreat_le_two_alpha_mul_burden
#print axioms IsControlledCivicWeightedPathFrom.floored_coupled_burden_cell_add_residual_le
#print axioms IsControlledCivicWeightedPathFrom.stationaryStockLag_succ
#print axioms abs_civicWeightedGradient_le_barrier_add_abs_lag
#print axioms abs_civicWeightedGradient_le_passageGradientBound
#print axioms append_cancellingHoldAction_mem_quasipotentialActionSet
#print axioms cancellingHoldAction_le_abs_lag
#print axioms coupledCellFactor_div_eq_two_div_sub
#print axioms coupledCellFactor_mul_add_residual_le_half_sq
#print axioms exists_exitAction_le_prefix_add_absLag_sq
#print axioms exists_exitAction_le_prefix_add_oneClimb
#print axioms exists_exitAction_le_prefix_add_quadraticLag
#print axioms exists_exitAction_le_prefix_add_tail_add_localQuadratic
#print axioms finiteControlledOrbitFrom_cancellingHoldStop_exits
#print axioms finiteControlledOrbitFrom_cancellingHold_eq
#print axioms finiteControlledOrbitFrom_marginClimb_eq
#print axioms hasUniformSaddlePassageSurgery_oneClimb
#print axioms localOneClimbQuadratic_collect
#print axioms marginClimbPathFrom_abs_lag_le
#print axioms marginClimbPathFrom_abs_lag_le_initial_add_advance
#print axioms marginClimbPathFrom_abs_lag_succ_le
#print axioms marginClimbPathFrom_abs_lag_succ_le_increment
#print axioms marginClimbPathFrom_abs_lag_work_le
#print axioms marginClimbPathFrom_abs_lag_work_le_quadratic
#print axioms marginClimbPathFrom_action_eq
#print axioms marginClimbPathFrom_action_le_integral_add_quadratic
#print axioms marginClimbPathFrom_action_summand_eq
#print axioms marginClimbPathFrom_barrier_work_le
#print axioms marginClimbPathFrom_before_stop_increment_bounds
#print axioms marginClimbPathFrom_before_stop_step_data
#print axioms marginClimbPathFrom_eventually_crosses
#print axioms marginClimbPathFrom_isControlled
#print axioms marginClimbPathFrom_lambda_mul_sum_abs_lag_le
#print axioms marginClimbPathFrom_le_target_before_stop
#print axioms marginClimbPathFrom_stationaryStockLag_succ
#print axioms marginClimbPathFrom_step_sq_sum_le
#print axioms marginClimbPathFrom_succ
#print axioms marginClimbPathFrom_sum_abs_lag_sq_le
#print axioms marginClimbPathFrom_zero
#print axioms marginClimbStopFrom_advance_le_distance_add_mesh
#print axioms marginClimbStopFrom_crosses
#print axioms marginClimbStopFrom_mul_margin_le_advance
#print axioms marginClimb_net_gradient_eq_abs
#print axioms max_neg_civicWeightedGradient_le_barrier_add_abs_lag
#print axioms monotone_marginClimbPolicyFrom
#print axioms oneClimb_nonintegral_price_le_quadratic
#print axioms one_le_passageLogFactor_of_pos_of_le_one
#print axioms one_lt_passageSurgeryWindowMultiplier
#print axioms overleapingCell_saddleDistance_sq_le
#print axioms passageGradientBound_pos
#print axioms passageLocalOneClimbQuadraticConstant_pos
#print axioms passageLocalOneClimbQuadraticConstant_withOperatorRate
#print axioms passageLowerBarrier_add_L_area_le_coupledBarrier
#print axioms passageOneClimbQuadraticConstant_pos
#print axioms passageSurgeryAlphaCeiling_aux_bounds
#print axioms passageSurgeryAlphaCeiling_dominance
#print axioms passageSurgeryAlphaCeiling_le_canonical
#print axioms passageSurgeryAlphaCeiling_mem_Ioc
#print axioms passageSurgeryAlphaCeiling_pos
#print axioms passageSurgeryErrorConstant_pos
#print axioms passageSurgeryGapLower_pos
#print axioms passageSurgeryGapUpper_pos
#print axioms passageSurgery_selection_gap_lt
#print axioms passageWindowClamp_strict_sub_order
#print axioms quantitativeSaddlePassage_uniform
#print axioms scaled_weightedBarrierRetreatIntegral_le_quadratic
#print axioms signedHoldAction_le_rent_add_transient
#print axioms signedHoldControl_eq_barrier_add_geometric
#print axioms signedHoldPath_step
#print axioms two_div_area_le_passageLowerBarrier_add_four_L_area
#print axioms upwardStrategyCostAtRate_upper_bound_of_le_passageCeiling
#print axioms weightedBarrierIntegrand_le_lipschitz_saddle_distance
#print axioms stationaryStock_sub_stockStep
#print axioms stationaryStock_sub_stockStep_at_oldLevel
#print axioms stationaryStockLag_controlledCivicWeightedStep
#print axioms IsControlledCivicWeightedPath.stationaryStockLag_succ
#print axioms IsControlledCivicWeightedPath.stationaryStockLag_succ_at_oldLevel
#print axioms IsControlledCivicWeightedPath.stationaryStockLag_succ_le_oldLevel_add_retreat
#print axioms cancellingHoldGradient_nonpos_of_before_saddle
#print axioms cancellingHoldPath_step_of_before_saddle
#print axioms cancellingHoldControl_eq_barrier_add_geometric
#print axioms cancellingHoldAction_eq_before_saddle
#print axioms cancellingHoldAction_at_saddle_eq_price_sub_tail
#print axioms tendsto_cancellingHoldAction_at_saddle
#print axioms cancellingHoldAction_le_rent_add_transient
#print axioms controlAction_mono
#print axioms controlAction_add_next_le
#print axioms coupledCellFactor_pos
#print axioms correctedCellFactor_lt_coupledCellFactor
#print axioms coupledCellFactor_mul_le_half_sq
#print axioms half_inv_le_retreatCoefficient_of_four_alpha_c_sq_I_le_lambda
#print axioms IsControlledCivicWeightedPathFrom.control_ge_flooredBarrier_burden_add_advance
#print axioms IsControlledCivicWeightedPathFrom.passageCellBurden_nonneg_of_advance
#print axioms IsControlledCivicWeightedPathFrom.deficit_add_halfRetreat_le_passageCellBurden
#print axioms IsControlledCivicWeightedPathFrom.control_ge_flooredBarrier_deficit_add_advance
#print axioms IsControlledCivicWeightedPathFrom.floored_coupled_burden_cell_le_half_control_sq
#print axioms IsControlledCivicWeightedPathFrom.floored_coupled_deficit_cell_le_half_control_sq
#print axioms IsControlledCivicWeightedPathFrom.floored_coupled_barrier_add_burden_le_action
#print axioms IsControlledCivicWeightedPathFrom.floored_coupled_barrier_add_deficit_le_action
#print axioms saddleStockCoefficient_pos
#print axioms saddleStockCoefficient_le
#print axioms IsControlledCivicWeightedPath.stationaryStockLag_succ_le_burden_add_advance
#print axioms IsControlledCivicWeightedPathFrom.saddleCoefficient_mul_flooredDeficitMass_le_charge
#print axioms IsControlledCivicWeightedPath.coupled_burdenMass_le_action_gap
#print axioms IsControlledCivicWeightedPath.coupled_deficitMass_le_action_gap
#print axioms lipschitzConstantOn_weightedBarrierIntegrand_pos
#print axioms IsControlledCivicWeightedPath.coupled_cell_integral_le_half_control_sq
#print axioms IsControlledCivicWeightedPath.coupled_action_lower_bound_to_cappedRunningMax
#print axioms weightedBarrierTail_le_three_halves_lipschitz
#print axioms IsControlledCivicWeightedPath.cappedAdvance_sq_le_actionGap_add_barrierTail
#print axioms IsControlledCivicWeightedPath.cappedAdvance_sq_le_actionGap_add_quadraticTail
#print axioms IsControlledCivicWeightedPath.coupled_action_lower_bound_of_crossing
#print axioms coupledBarrier_le_civicCrossingQuasipotential
#print axioms correctedBarrier_lt_coupledBarrier
#print axioms correctedBarrier_lt_civicCrossingQuasipotential
#print axioms IsControlledCivicWeightedPath.corrected_deficitMass_le_action_gap
#print axioms IsControlledCivicWeightedPath.corrected_burdenMass_le_action_gap
#print axioms passageSelectionWidth_nonneg
#print axioms passageSelectionMass_nonneg
#print axioms passageSelectionCell_sqrt_width_le
#print axioms sqrt_mul_passageSelectionWidth_le_of_not_dominated
#print axioms exists_dominatedPassageCell_of_mass_lt
#print axioms HasDominatedPassageCell.exists_index
#print axioms passageSelectionWidth_ofFn
#print axioms passageSelectionMass_ofFn
#print axioms monotone_passageWindowClamp
#print axioms passageWindowClamp_eq_lo
#print axioms passageWindowClamp_eq_hi
#print axioms passageWindowClamp_sub_le
#print axioms passageWindowCells_nonnegative
#print axioms IsControlledCivicWeightedPath.passageWindowCells_width
#print axioms IsControlledCivicWeightedPath.passageWindowCells_mass_le
#print axioms IsControlledCivicWeightedPath.hasDominatedPassageWindowCell
#print axioms IsControlledCivicWeightedPath.hasDominatedPassageWindowCell_of_actionGap_lt
#print axioms IsControlledCivicWeightedPath.exists_dominatedPassageWindowStep
#print axioms passageBurdenWindowCells_nonnegative
#print axioms IsControlledCivicWeightedPath.passageBurdenWindowCells_width
#print axioms IsControlledCivicWeightedPath.passageBurdenWindowCells_mass_le
#print axioms IsControlledCivicWeightedPath.hasDominatedPassageBurdenWindowCell
#print axioms IsControlledCivicWeightedPath.hasDominatedPassageBurdenWindowCell_of_actionGap_lt
#print axioms IsControlledCivicWeightedPath.exists_dominatedPassageBurdenWindowStep
#print axioms exists_scaled_gap_constant
#print axioms passageLogWeight_pos
#print axioms rawPassageLogFactor_exp_one
#print axioms passageLogFactor_pos_of_pos_of_le_one
#print axioms saddlePassageAlphaCeiling_pos
#print axioms saddlePassageAlphaCeiling_mem_Ioc
#print axioms smallStepAssumption_withOperatorRate_of_le_passageCeiling
#print axioms four_alpha_c_sq_I_le_lambda_of_le_passageCeiling
#print axioms half_inv_le_passageRetreatCoefficient
#print axioms saddlePassageAlphaCeiling_dominance
#print axioms quantitativeSaddlePassage_uniform_of_surgery
#print axioms quantitativeSaddlePassage_logPlus
#print axioms quantitativeSaddlePassage_of_logFactor_pos

end

end CivicAlignment.PaperII
