/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.JumpLimit
import CivicAlignment.PaperII.Root
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Paper III: burn decomposition for the jump map

This file proves the exact infinite telescoping identity in `prop:burn` on
orbits for which the projection is inactive.  It also records an exact
rational counterexample to the proposition's global strict-monotonicity claim:
two distinct admissible initial excesses can both clip to policy one on their
first step, after which both policy paths are identically one.
-/

namespace CivicAlignment.PaperIII

open Filter Function Set Topology

noncomputable section

/-! ## Raw jump orbits and the exact telescope -/

/-- The unprojected jump orbit used whenever every raw policy input stays in `[0,1]`. -/
def rawJumpOrbit (p : LoopParams) (x₀ : LoopState) (n : ℕ) : LoopState :=
  ((jumpMap p)^[n]) x₀

/-- Every step of the infinite raw jump orbit remains in the policy interval. -/
def JumpOrbitNeverClips (p : LoopParams) (x₀ : LoopState) : Prop :=
  ∀ n : ℕ,
    (rawJumpOrbit p x₀ n).1 +
        jumpGain p (rawJumpOrbit p x₀ n).1 * (rawJumpOrbit p x₀ n).2 ∈
      Icc (0 : ℝ) 1

/-- The raw jump orbit satisfies its defining one-step recursion. -/
theorem rawJumpOrbit_succ (p : LoopParams) (x₀ : LoopState) (n : ℕ) :
    rawJumpOrbit p x₀ (n + 1) = jumpMap p (rawJumpOrbit p x₀ n) := by
  simp only [rawJumpOrbit, Function.iterate_succ_apply']

/-- A globally unclipped raw orbit agrees with the projected jump orbit at every time. -/
theorem projectedJumpOrbit_eq_rawJumpOrbit_of_neverClips
    {p : LoopParams} {x₀ : LoopState} (hnever : JumpOrbitNeverClips p x₀) (n : ℕ) :
    ((projectedJumpMap p)^[n]) x₀ = rawJumpOrbit p x₀ n := by
  rw [rawJumpOrbit]
  apply projectedJumpMap_iterate_eq_jumpMap_iterate
  intro k _hk
  exact hnever k

/-- The raw policy coordinate obeys the displayed affine jump equation. -/
theorem rawJumpOrbit_policy_succ (p : LoopParams) (x₀ : LoopState) (n : ℕ) :
    (rawJumpOrbit p x₀ (n + 1)).1 =
      (rawJumpOrbit p x₀ n).1 +
        jumpGain p (rawJumpOrbit p x₀ n).1 * (rawJumpOrbit p x₀ n).2 := by
  rw [rawJumpOrbit_succ]
  rfl

/-- The raw excess coordinate is multiplied by `σ(β)` at every jump. -/
theorem rawJumpOrbit_excess_succ (p : LoopParams) (x₀ : LoopState) (n : ℕ) :
    (rawJumpOrbit p x₀ (n + 1)).2 =
      jumpPersistence p (rawJumpOrbit p x₀ n).1 * (rawJumpOrbit p x₀ n).2 := by
  rw [rawJumpOrbit_succ]
  rfl

/-- On the policy interval, the jump gain `A(β)` is strictly positive. -/
theorem jumpGain_pos_of_mem {p : LoopParams} (model : LoopModelAssumptions p)
    {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 < jumpGain p β := by
  have hfactor : 0 < 1 - p.c * β := by
    have hmul : p.c * β ≤ p.c := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hβ.2 model.c_pos.le
    linarith [model.c_lt_one]
  simp only [jumpGain]
  exact mul_pos (mul_pos (by norm_num) model.c_pos) hfactor

/-- The jump persistence is uniformly bounded by `1-λ₀+g<1`. -/
theorem jumpPersistence_nonneg_le_uniform {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 ≤ jumpPersistence p β ∧
      jumpPersistence p β ≤ 1 - p.lambda₀ + p.g ∧
      1 - p.lambda₀ + p.g < 1 := by
  have hs := stockMultiplier_nonneg_le model hβ
  simp only [jumpPersistence]
  constructor
  · exact add_nonneg hs.1 model.g_nonneg
  constructor
  · linarith [hs.2]
  · linarith

/-- Persistence is strictly positive on the policy interval under the standing model. -/
theorem jumpPersistence_pos_of_mem {p : LoopParams}
    (model : LoopModelAssumptions p) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 < jumpPersistence p β := by
  have hresidual_le_one : 1 - β ≤ 1 := by linarith [hβ.1]
  have hscaled_le_eta : p.η * (1 - β) ≤ p.η := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hresidual_le_one model.η_pos.le
  have hinner : 0 < 1 - p.η * (1 - β) := by
    linarith [model.η_lt_one]
  have hs : 0 < p.s β := by
    simp only [LoopParams.s]
    exact mul_pos (sub_pos.mpr model.lambda₀_lt_one) (sq_pos_of_pos hinner)
  simp only [jumpPersistence]
  linarith [model.g_nonneg]

/-- The affine gain `A(β)` strictly decreases with policy on `[0,1]`. -/
theorem jumpGain_strictAntiOn {p : LoopParams} (model : LoopModelAssumptions p) :
    StrictAntiOn (jumpGain p) (Icc (0 : ℝ) 1) := by
  intro β₁ _hβ₁ β₂ _hβ₂ hlt
  have hcSquare : 0 < p.c ^ 2 := sq_pos_of_pos model.c_pos
  have hproduct : 0 < 2 * p.c ^ 2 * (β₂ - β₁) := by positivity
  simp only [jumpGain]
  nlinarith

/-- A never-clipped raw orbit remains in the policy interval. -/
theorem rawJumpOrbit_policy_mem {p : LoopParams} {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hnever : JumpOrbitNeverClips p x₀) :
    ∀ n : ℕ, (rawJumpOrbit p x₀ n).1 ∈ Icc (0 : ℝ) 1 := by
  intro n
  cases n with
  | zero => simpa only [rawJumpOrbit, Function.iterate_zero_apply] using hx₀
  | succ n =>
      simpa only [Nat.succ_eq_add_one, rawJumpOrbit_policy_succ] using hnever n

/-- Nonnegative initial excess remains nonnegative along a raw jump orbit. -/
theorem rawJumpOrbit_excess_nonneg {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hE₀ : 0 ≤ x₀.2)
    (hnever : JumpOrbitNeverClips p x₀) :
    ∀ n : ℕ, 0 ≤ (rawJumpOrbit p x₀ n).2 := by
  intro n
  induction n with
  | zero => simpa only [rawJumpOrbit, Function.iterate_zero_apply] using hE₀
  | succ n ih =>
      rw [rawJumpOrbit_excess_succ]
      exact mul_nonneg
        (jumpPersistence_nonneg_le_uniform model hgain
          (rawJumpOrbit_policy_mem hx₀ hnever n)).1 ih

/-- Strictly positive initial excess remains strictly positive. -/
theorem rawJumpOrbit_excess_pos {p : LoopParams} (model : LoopModelAssumptions p)
    {x₀ : LoopState} (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hE₀ : 0 < x₀.2)
    (hnever : JumpOrbitNeverClips p x₀) :
    ∀ n : ℕ, 0 < (rawJumpOrbit p x₀ n).2 := by
  intro n
  induction n with
  | zero => simpa only [rawJumpOrbit, Function.iterate_zero_apply] using hE₀
  | succ n ih =>
      rw [rawJumpOrbit_excess_succ]
      exact mul_pos
        (jumpPersistence_pos_of_mem model (rawJumpOrbit_policy_mem hx₀ hnever n)) ih

/-- A positive, never-clipped jump orbit raises policy strictly at every step. -/
theorem rawJumpOrbit_policy_lt_succ {p : LoopParams} (model : LoopModelAssumptions p)
    {x₀ : LoopState} (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hE₀ : 0 < x₀.2)
    (hnever : JumpOrbitNeverClips p x₀) (n : ℕ) :
    (rawJumpOrbit p x₀ n).1 < (rawJumpOrbit p x₀ (n + 1)).1 := by
  rw [rawJumpOrbit_policy_succ]
  exact lt_add_of_pos_right _
    (mul_pos
      (jumpGain_pos_of_mem model (rawJumpOrbit_policy_mem hx₀ hnever n))
      (rawJumpOrbit_excess_pos model hx₀ hE₀ hnever n))

/--
The jump sizes `hₜ=A(βₜ)Eₜ` are strictly decreasing on every positive,
never-clipped orbit.  This is the first assertion of `prop:burn`(iii), proved
without assuming that the orbit is the critical one.
-/
theorem rawJumpOrbit_jumpSize_strictlyDecreases {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {x₀ : LoopState} (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hE₀ : 0 < x₀.2)
    (hnever : JumpOrbitNeverClips p x₀) (n : ℕ) :
    jumpGain p (rawJumpOrbit p x₀ (n + 1)).1 *
        (rawJumpOrbit p x₀ (n + 1)).2 <
      jumpGain p (rawJumpOrbit p x₀ n).1 * (rawJumpOrbit p x₀ n).2 := by
  have hβn := rawJumpOrbit_policy_mem hx₀ hnever n
  have hβnext := rawJumpOrbit_policy_mem hx₀ hnever (n + 1)
  have hpolicy := rawJumpOrbit_policy_lt_succ model hx₀ hE₀ hnever n
  have hAdec := jumpGain_strictAntiOn model hβn hβnext hpolicy
  have hEn := rawJumpOrbit_excess_pos model hx₀ hE₀ hnever n
  have hpersistence := jumpPersistence_nonneg_le_uniform model hgain hβn
  have hpersistence_lt_one :
      jumpPersistence p (rawJumpOrbit p x₀ n).1 < 1 :=
    hpersistence.2.1.trans_lt hpersistence.2.2
  have hEdec : (rawJumpOrbit p x₀ (n + 1)).2 < (rawJumpOrbit p x₀ n).2 := by
    rw [rawJumpOrbit_excess_succ]
    exact mul_lt_of_lt_one_left hEn hpersistence_lt_one
  exact (mul_lt_mul_of_pos_left hEdec (jumpGain_pos_of_mem model hβnext)).trans
    (mul_lt_mul_of_pos_right hAdec hEn)

/-- Excess on a never-clipped orbit is bounded by the uniform geometric envelope. -/
theorem rawJumpOrbit_excess_le_geometric {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {x₀ : LoopState} (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hE₀ : 0 ≤ x₀.2)
    (hnever : JumpOrbitNeverClips p x₀) :
    ∀ n : ℕ,
      (rawJumpOrbit p x₀ n).2 ≤ x₀.2 * (1 - p.lambda₀ + p.g) ^ n := by
  have hq : 0 ≤ 1 - p.lambda₀ + p.g :=
    add_nonneg (sub_nonneg.mpr model.lambda₀_lt_one.le) model.g_nonneg
  have hEnonneg := rawJumpOrbit_excess_nonneg model hgain hx₀ hE₀ hnever
  intro n
  induction n with
  | zero => simp [rawJumpOrbit]
  | succ n ih =>
      rw [rawJumpOrbit_excess_succ, pow_succ]
      have hpersistence := jumpPersistence_nonneg_le_uniform model hgain
        (rawJumpOrbit_policy_mem hx₀ hnever n)
      calc
        jumpPersistence p (rawJumpOrbit p x₀ n).1 * (rawJumpOrbit p x₀ n).2 ≤
            (1 - p.lambda₀ + p.g) * (rawJumpOrbit p x₀ n).2 :=
          mul_le_mul_of_nonneg_right hpersistence.2.1 (hEnonneg n)
        _ ≤ (1 - p.lambda₀ + p.g) *
            (x₀.2 * (1 - p.lambda₀ + p.g) ^ n) :=
          mul_le_mul_of_nonneg_left ih hq
        _ = x₀.2 * ((1 - p.lambda₀ + p.g) ^ n *
            (1 - p.lambda₀ + p.g)) := by ring

/-- The excess coordinate of a never-clipped jump orbit converges to zero. -/
theorem rawJumpOrbit_excess_tendsto_zero {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {x₀ : LoopState} (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hE₀ : 0 ≤ x₀.2)
    (hnever : JumpOrbitNeverClips p x₀) :
    Tendsto (fun n : ℕ ↦ (rawJumpOrbit p x₀ n).2) atTop (nhds 0) := by
  have hq_nonneg : 0 ≤ 1 - p.lambda₀ + p.g :=
    add_nonneg (sub_nonneg.mpr model.lambda₀_lt_one.le) model.g_nonneg
  have hq_lt : 1 - p.lambda₀ + p.g < 1 := by linarith
  have hbound := rawJumpOrbit_excess_le_geometric model hgain hx₀ hE₀ hnever
  have hupper : Tendsto
      (fun n : ℕ ↦ x₀.2 * (1 - p.lambda₀ + p.g) ^ n) atTop (nhds 0) := by
    simpa only [mul_comm, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt).mul_const x₀.2
  exact squeeze_zero
    (rawJumpOrbit_excess_nonneg model hgain hx₀ hE₀ hnever) hbound hupper

/-- One burn summand is exactly the loss of rescaled excess during that step. -/
theorem jumpBurnTerm_eq_excess_sub_next {p : LoopParams}
    (model : LoopModelAssumptions p) {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hnever : JumpOrbitNeverClips p x₀)
    (n : ℕ) :
    jumpBurnRate p (rawJumpOrbit p x₀ n).1 *
        ((rawJumpOrbit p x₀ (n + 1)).1 - (rawJumpOrbit p x₀ n).1) =
      (rawJumpOrbit p x₀ n).2 - (rawJumpOrbit p x₀ (n + 1)).2 := by
  rw [rawJumpOrbit_succ]
  have hA := jumpGain_pos_of_mem model (rawJumpOrbit_policy_mem hx₀ hnever n)
  have hchange := jumpMap_excess_change_eq_neg_burnRate_mul_policy_change
    (p := p) (x := rawJumpOrbit p x₀ n) hA.ne'
  linarith

/-- Every burn summand is nonnegative. -/
theorem jumpBurnTerm_nonneg {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hE₀ : 0 ≤ x₀.2)
    (hnever : JumpOrbitNeverClips p x₀) (n : ℕ) :
    0 ≤ jumpBurnRate p (rawJumpOrbit p x₀ n).1 *
      ((rawJumpOrbit p x₀ (n + 1)).1 - (rawJumpOrbit p x₀ n).1) := by
  rw [jumpBurnTerm_eq_excess_sub_next model hx₀ hnever]
  rw [rawJumpOrbit_excess_succ]
  have hpersistence := jumpPersistence_nonneg_le_uniform model hgain
    (rawJumpOrbit_policy_mem hx₀ hnever n)
  have hE := rawJumpOrbit_excess_nonneg model hgain hx₀ hE₀ hnever n
  have hle_one : jumpPersistence p (rawJumpOrbit p x₀ n).1 ≤ 1 :=
    hpersistence.2.1.trans hpersistence.2.2.le
  exact sub_nonneg.mpr (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hle_one hE)

/-- The finite burn sum telescopes to initial excess minus current excess. -/
theorem sum_jumpBurnTerm_eq_excess_sub {p : LoopParams}
    (model : LoopModelAssumptions p) {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hnever : JumpOrbitNeverClips p x₀)
    (N : ℕ) :
    ∑ n ∈ Finset.range N,
        jumpBurnRate p (rawJumpOrbit p x₀ n).1 *
          ((rawJumpOrbit p x₀ (n + 1)).1 - (rawJumpOrbit p x₀ n).1) =
      x₀.2 - (rawJumpOrbit p x₀ N).2 := by
  induction N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, rawJumpOrbit,
      Function.iterate_zero_apply, sub_self]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih,
        jumpBurnTerm_eq_excess_sub_next model hx₀ hnever]
      ring

/--
Paper III, Proposition 7.4 (`prop:burn`), clause (i),
`civic_loops.tex:550`: on every globally unclipped admissible jump orbit, the
left-endpoint burn terms have sum exactly equal to the initial rescaled excess.
-/
theorem burnDecomposition_exactTelescope {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {β₀ excess₀ : ℝ} (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1)
    (hexcess₀ : excess₀ ∈ Ico (0 : ℝ) (1 / (2 * p.c ^ 2)))
    (hnever : JumpOrbitNeverClips p (β₀, excess₀)) :
    HasSum
      (fun n : ℕ ↦
        jumpBurnRate p (rawJumpOrbit p (β₀, excess₀) n).1 *
          ((rawJumpOrbit p (β₀, excess₀) (n + 1)).1 -
            (rawJumpOrbit p (β₀, excess₀) n).1))
      excess₀ := by
  let term : ℕ → ℝ := fun n ↦
    jumpBurnRate p (rawJumpOrbit p (β₀, excess₀) n).1 *
      ((rawJumpOrbit p (β₀, excess₀) (n + 1)).1 -
        (rawJumpOrbit p (β₀, excess₀) n).1)
  have hterm_nonneg : ∀ n, 0 ≤ term n := by
    intro n
    exact jumpBurnTerm_nonneg model hgain hβ₀ hexcess₀.1 hnever n
  apply (hasSum_iff_tendsto_nat_of_nonneg hterm_nonneg excess₀).2
  have hexcess_tendsto := rawJumpOrbit_excess_tendsto_zero
    model hgain hβ₀ hexcess₀.1 hnever
  have htelescope : ∀ N : ℕ,
      ∑ n ∈ Finset.range N, term n =
        excess₀ - (rawJumpOrbit p (β₀, excess₀) N).2 := by
    intro N
    exact sum_jumpBurnTerm_eq_excess_sub model hβ₀ hnever N
  have hlimit : Tendsto
      (fun N : ℕ ↦ excess₀ - (rawJumpOrbit p (β₀, excess₀) N).2)
      atTop (nhds excess₀) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hexcess_tendsto
  exact hlimit.congr' (Eventually.of_forall fun N ↦ (htelescope N).symm)

/-- The paper's displayed `tsum` equality follows from the stronger `HasSum` result. -/
theorem tsum_jumpBurnTerm_eq_initialExcess {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {β₀ excess₀ : ℝ} (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1)
    (hexcess₀ : excess₀ ∈ Ico (0 : ℝ) (1 / (2 * p.c ^ 2)))
    (hnever : JumpOrbitNeverClips p (β₀, excess₀)) :
    ∑' n : ℕ,
        jumpBurnRate p (rawJumpOrbit p (β₀, excess₀) n).1 *
          ((rawJumpOrbit p (β₀, excess₀) (n + 1)).1 -
            (rawJumpOrbit p (β₀, excess₀) n).1) =
      excess₀ :=
  (burnDecomposition_exactTelescope model hgain hβ₀ hexcess₀ hnever).tsum_eq

/-! ## Exact clipping counterexample to clause (ii) -/

/-- Exact rational parameters from the rate-separation benchmark. -/
def burnClippingParams : LoopParams where
  η := 1 / 2
  lambda₀ := 1 / 50
  I := 1 / 50
  v := 1 / 10
  c := 9 / 10
  α := 1 / 10
  g := 0

/-- The clipping counterexample satisfies every standing primitive restriction. -/
theorem burnClipping_model : LoopModelAssumptions burnClippingParams := by
  constructor <;> norm_num [burnClippingParams]

/-- The same parameters satisfy the Paper II specialization used to construct the saddle. -/
theorem burnClipping_driftModel :
    PaperII.DriftModelAssumptions burnClippingParams := by
  constructor <;> norm_num [burnClippingParams]

/-- The benchmark stationary gradient is negative at the calibrated endpoint. -/
theorem burnClipping_G_zero_neg : burnClippingParams.G 0 < 0 := by
  norm_num [burnClippingParams, LoopParams.G, LoopParams.stationaryStock,
    LoopParams.s]

/-- The benchmark stationary gradient is positive at the captured endpoint. -/
theorem burnClipping_G_one_pos : 0 < burnClippingParams.G 1 := by
  norm_num [burnClippingParams, LoopParams.G, LoopParams.stationaryStock,
    LoopParams.s]

/-- The exact benchmark therefore has the oriented interior saddle assumed in the section. -/
theorem burnClipping_hasThreshold :
    Nonempty (PaperII.ThresholdAssumption burnClippingParams) :=
  PaperII.thresholdAutomatic burnClipping_driftModel
    burnClipping_G_zero_neg burnClipping_G_one_pos

/-- Its content gain is below the stock divergence ceiling. -/
theorem burnClipping_gain_lt_lambda :
    burnClippingParams.g < burnClippingParams.lambda₀ := by
  norm_num [burnClippingParams]

/-- Once policy is one and excess is nonnegative, the projected jump remains at policy one. -/
theorem projectedJumpMap_preserves_policy_one {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {x : LoopState} (hpolicy : x.1 = 1) (hexcess : 0 ≤ x.2) :
    (projectedJumpMap p x).1 = 1 ∧ 0 ≤ (projectedJumpMap p x).2 := by
  have hβ : x.1 ∈ Icc (0 : ℝ) 1 := by simpa only [hpolicy] using (right_mem_Icc.mpr zero_le_one)
  have hA : 0 ≤ jumpGain p x.1 := (jumpGain_pos_of_mem model hβ).le
  have hinput : 1 ≤ x.1 + jumpGain p x.1 * x.2 := by
    rw [hpolicy] at hA ⊢
    exact le_add_of_nonneg_right (mul_nonneg hA hexcess)
  constructor
  · simp only [projectedJumpMap]
    exact clipUnit_eq_one_of_le hinput
  · simp only [projectedJumpMap]
    exact mul_nonneg
      (jumpPersistence_nonneg_le_uniform model hgain hβ).1 hexcess

/-- A projected orbit starting at policy one stays there forever. -/
theorem projectedJumpOrbit_policy_one {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {excess : ℝ} (hexcess : 0 ≤ excess) (n : ℕ) :
    (((projectedJumpMap p)^[n]) ((1 : ℝ), excess)).1 = 1 ∧
      0 ≤ (((projectedJumpMap p)^[n]) ((1 : ℝ), excess)).2 := by
  induction n with
  | zero => exact ⟨rfl, hexcess⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact projectedJumpMap_preserves_policy_one model hgain ih.1 ih.2

/-- The lower of two distinct admissible excesses clips to one on its first step. -/
theorem burnClipping_first_lower :
    projectedJumpMap burnClippingParams ((0 : ℝ), (3 / 5 : ℝ)) =
      ((1 : ℝ), (147 / 1000 : ℝ)) := by
  norm_num [projectedJumpMap, jumpGain, jumpPersistence, burnClippingParams,
    LoopParams.s, LoopParams.clipUnit, Set.coe_projIcc]

/-- The higher admissible excess also clips to one on its first step. -/
theorem burnClipping_first_upper :
    projectedJumpMap burnClippingParams ((0 : ℝ), (61 / 100 : ℝ)) =
      ((1 : ℝ), (2989 / 20000 : ℝ)) := by
  norm_num [projectedJumpMap, jumpGain, jumpPersistence, burnClippingParams,
    LoopParams.s, LoopParams.clipUnit, Set.coe_projIcc]

/-- The lower clipping orbit has policy one at every positive time. -/
theorem burnClipping_lower_policy_succ (n : ℕ) :
    (((projectedJumpMap burnClippingParams)^[n + 1])
        ((0 : ℝ), (3 / 5 : ℝ))).1 = 1 := by
  rw [Function.iterate_succ_apply, burnClipping_first_lower]
  exact (projectedJumpOrbit_policy_one burnClipping_model
    burnClipping_gain_lt_lambda (by norm_num) n).1

/-- The higher clipping orbit has policy one at every positive time. -/
theorem burnClipping_upper_policy_succ (n : ℕ) :
    (((projectedJumpMap burnClippingParams)^[n + 1])
        ((0 : ℝ), (61 / 100 : ℝ))).1 = 1 := by
  rw [Function.iterate_succ_apply, burnClipping_first_upper]
  exact (projectedJumpOrbit_policy_one burnClipping_model
    burnClipping_gain_lt_lambda (by norm_num) n).1

/-- The lower clipping orbit's policy converges to one. -/
theorem burnClipping_lower_policy_tendsto :
    Tendsto
      (fun n : ℕ ↦
        (((projectedJumpMap burnClippingParams)^[n])
          ((0 : ℝ), (3 / 5 : ℝ))).1)
      atTop (nhds 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  cases n with
  | zero => omega
  | succ n => simpa only [Nat.succ_eq_add_one] using (burnClipping_lower_policy_succ n).symm

/-- The higher clipping orbit's policy also converges to one. -/
theorem burnClipping_upper_policy_tendsto :
    Tendsto
      (fun n : ℕ ↦
        (((projectedJumpMap burnClippingParams)^[n])
          ((0 : ℝ), (61 / 100 : ℝ))).1)
      atTop (nhds 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  cases n with
  | zero => omega
  | succ n => simpa only [Nat.succ_eq_add_one] using (burnClipping_upper_policy_succ n).symm

/-- Both counterexample excesses lie in the proposition's stated half-open interval. -/
theorem burnClipping_excesses_admissible :
    (3 / 5 : ℝ) ∈ Ico 0 (1 / (2 * burnClippingParams.c ^ 2)) ∧
      (61 / 100 : ℝ) ∈ Ico 0 (1 / (2 * burnClippingParams.c ^ 2)) ∧
      (3 / 5 : ℝ) < 61 / 100 := by
  norm_num [burnClippingParams]

/--
Paper III, Proposition 7.4 (`prop:burn`), clause (ii),
`civic_loops.tex:550`: the asserted strict monotonicity on the full admissible
interval is false for the projected jump map.  Any function assigning the
actual policy limits to all admissible initial excesses takes the same value
at the two distinct exact-rational excesses above, so it cannot be strictly
increasing there.
-/
theorem burnPolicyLimit_not_strictOn_admissibleInterval
    (limitPolicy : ℝ → ℝ)
    (hlimit : ∀ excess ∈ Ico (0 : ℝ)
        (1 / (2 * burnClippingParams.c ^ 2)),
      Tendsto
        (fun n : ℕ ↦
          (((projectedJumpMap burnClippingParams)^[n]) ((0 : ℝ), excess)).1)
        atTop (nhds (limitPolicy excess))) :
    ¬ StrictMonoOn limitPolicy
      (Ico (0 : ℝ) (1 / (2 * burnClippingParams.c ^ 2))) := by
  intro hstrict
  have hadmissible := burnClipping_excesses_admissible
  have hlower : limitPolicy (3 / 5 : ℝ) = 1 :=
    tendsto_nhds_unique (hlimit (3 / 5) hadmissible.1)
      burnClipping_lower_policy_tendsto
  have hupper : limitPolicy (61 / 100 : ℝ) = 1 :=
    tendsto_nhds_unique (hlimit (61 / 100) hadmissible.2.1)
      burnClipping_upper_policy_tendsto
  have hlt := hstrict hadmissible.1 hadmissible.2.1 hadmissible.2.2
  rw [hlower, hupper] at hlt
  exact lt_irrefl 1 hlt

#print axioms rawJumpOrbit_succ
#print axioms projectedJumpOrbit_eq_rawJumpOrbit_of_neverClips
#print axioms rawJumpOrbit_policy_succ
#print axioms rawJumpOrbit_excess_succ
#print axioms jumpGain_pos_of_mem
#print axioms jumpPersistence_nonneg_le_uniform
#print axioms jumpPersistence_pos_of_mem
#print axioms jumpGain_strictAntiOn
#print axioms rawJumpOrbit_policy_mem
#print axioms rawJumpOrbit_excess_nonneg
#print axioms rawJumpOrbit_excess_pos
#print axioms rawJumpOrbit_policy_lt_succ
#print axioms rawJumpOrbit_jumpSize_strictlyDecreases
#print axioms rawJumpOrbit_excess_le_geometric
#print axioms rawJumpOrbit_excess_tendsto_zero
#print axioms jumpBurnTerm_eq_excess_sub_next
#print axioms jumpBurnTerm_nonneg
#print axioms sum_jumpBurnTerm_eq_excess_sub
#print axioms burnDecomposition_exactTelescope
#print axioms tsum_jumpBurnTerm_eq_initialExcess
#print axioms burnClipping_model
#print axioms burnClipping_driftModel
#print axioms burnClipping_G_zero_neg
#print axioms burnClipping_G_one_pos
#print axioms burnClipping_hasThreshold
#print axioms burnClipping_gain_lt_lambda
#print axioms projectedJumpMap_preserves_policy_one
#print axioms projectedJumpOrbit_policy_one
#print axioms burnClipping_first_lower
#print axioms burnClipping_first_upper
#print axioms burnClipping_lower_policy_succ
#print axioms burnClipping_upper_policy_succ
#print axioms burnClipping_lower_policy_tendsto
#print axioms burnClipping_upper_policy_tendsto
#print axioms burnClipping_excesses_admissible
#print axioms burnPolicyLimit_not_strictOn_admissibleInterval

end

end CivicAlignment.PaperIII
