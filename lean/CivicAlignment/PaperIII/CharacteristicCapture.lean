/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.ClassificationConvergence

/-!
# Paper III: capture above the saddle characteristic

This file formalizes `lem:charcap`.  The proof first handles the compact
cooperative box by comparison with the monotone orbit started on the
stationary characteristic.  A separate argument treats stocks above the box,
so the theorem retains the paper's unrestricted upper-stock quantifier.
-/

namespace CivicAlignment.PaperIII

open Filter Function Set Topology

noncomputable section

/-! ## Canonical full-loop orbits -/

/-- The canonical orbit of the simultaneous Paper III loop. -/
def fullLoopOrbit (p : LoopParams) (x₀ : LoopState) (n : ℕ) : LoopState :=
  (p.loopMap^[n]) x₀

@[simp]
theorem fullLoopOrbit_zero (p : LoopParams) (x₀ : LoopState) :
    fullLoopOrbit p x₀ 0 = x₀ := by
  simp [fullLoopOrbit]

@[simp]
theorem fullLoopOrbit_succ (p : LoopParams) (x₀ : LoopState) (n : ℕ) :
    fullLoopOrbit p x₀ (n + 1) = p.loopMap (fullLoopOrbit p x₀ n) := by
  simp [fullLoopOrbit, Function.iterate_succ_apply']

/-- The canonical full-loop orbit satisfies the simultaneous recursion. -/
theorem fullLoopOrbit_isOrbit (p : LoopParams) (x₀ : LoopState) :
    IsLoopOrbit p (fullLoopOrbit p x₀) := by
  intro n
  exact fullLoopOrbit_succ p x₀ n

/-- Restarting at an iterate gives the corresponding shifted orbit. -/
theorem fullLoopOrbit_from_iterate (p : LoopParams) (x₀ : LoopState) (n k : ℕ) :
    fullLoopOrbit p (fullLoopOrbit p x₀ n) k = fullLoopOrbit p x₀ (k + n) := by
  simp only [fullLoopOrbit, Function.iterate_add_apply]

/-- Deleting a finite prefix does not change convergence of a canonical orbit. -/
theorem fullLoopOrbit_tendsto_iff_tail (p : LoopParams) (x₀ q : LoopState) (n : ℕ) :
    Tendsto (fullLoopOrbit p (fullLoopOrbit p x₀ n)) atTop (𝓝 q) ↔
      Tendsto (fullLoopOrbit p x₀) atTop (𝓝 q) := by
  have hfun : fullLoopOrbit p (fullLoopOrbit p x₀ n) =
      fun k ↦ fullLoopOrbit p x₀ (k + n) := by
    funext k
    exact fullLoopOrbit_from_iterate p x₀ n k
  rw [hfun]
  exact tendsto_add_atTop_iff_nat n

/-! ## Characteristic geometry -/

/-- The stationary stock is at least one period's exogenous injection. -/
theorem injection_le_stationaryStock {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    p.I ≤ p.stationaryStock β := by
  have hden : 0 < 1 - p.s β - p.g := zoneDenominator_pos model hgain hβ
  have hs := stockMultiplier_nonneg_le model hβ
  have hden_le : 1 - p.s β - p.g ≤ 1 := by
    linarith [hs.1, model.g_nonneg]
  simp only [LoopParams.stationaryStock]
  apply (le_div_iff₀ hden).2
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hden_le model.I_pos.le

/-- At full capture the stationary characteristic reaches the policy-free ceiling. -/
theorem stationaryStock_one_eq_stockCeiling (p : LoopParams) :
    p.stationaryStock 1 = stockCeiling p := by
  simp only [LoopParams.stationaryStock, stockCeiling, LoopParams.s, sub_self,
    mul_zero, sub_zero, one_pow]
  ring

/-- A point on the stationary characteristic belongs to the invariant box `B`. -/
theorem characteristicState_mem_classificationBox {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    (β, p.stationaryStock β) ∈ classificationBox p := by
  exact ⟨hβ, injection_le_stationaryStock model hgain hβ,
    stationaryStock_le_policyFreeBound model hgain hβ⟩

/-- The loop map preserves order between two canonical orbits in `B`. -/
theorem fullLoopOrbit_le_of_le_in_classificationBox {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (ss : StrictStepSize p) {x₀ y₀ : LoopState}
    (hx₀ : x₀ ∈ classificationBox p) (hy₀ : y₀ ∈ classificationBox p)
    (hxy : x₀ ≤ y₀) :
    ∀ n, fullLoopOrbit p x₀ n ≤ fullLoopOrbit p y₀ n := by
  have hxmem := orbit_mem_classificationBox model hgain
    (ss.toCooperativeCeiling model hgain) (fullLoopOrbit_isOrbit p x₀) hx₀
  have hymem := orbit_mem_classificationBox model hgain
    (ss.toCooperativeCeiling model hgain) (fullLoopOrbit_isOrbit p y₀) hy₀
  intro n
  induction n with
  | zero => simpa using hxy
  | succ n ih =>
      rw [fullLoopOrbit_succ, fullLoopOrbit_succ]
      exact classificationLoopMap_monotoneOn model hgain
        (ss.toCooperativeCeiling model hgain).diagonal_nonneg (hxmem n) (hymem n) ih

/-! ## Capture from the cooperative box -/

/--
Above the saddle, a point on the stationary characteristic takes a
componentwise nondecreasing first step.
-/
theorem characteristicState_le_step {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (threshold : PaperII.ThresholdAssumption p) {β : ℝ}
    (hβ : β ∈ Ioc threshold.βdagger 1) :
    (β, p.stationaryStock β) ≤ p.loopMap (β, p.stationaryStock β) := by
  have hunit : β ∈ Icc (0 : ℝ) 1 :=
    ⟨threshold.βdagger_mem.1.le.trans hβ.1.le, hβ.2⟩
  have hG : 0 < p.G β := by
    by_cases hone : β = 1
    · simpa only [hone] using threshold.G_one_pos
    · have hβint : β ∈ Ioo (0 : ℝ) 1 :=
        ⟨threshold.βdagger_mem.1.trans hβ.1, lt_of_le_of_ne hβ.2 hone⟩
      exact threshold.G_pos_after β hβint hβ.1
  constructor
  · simp only [LoopParams.loopMap, LoopParams.deferenceStep,
      gradU_stationaryStock_eq_G]
    calc
      β = LoopParams.clipUnit β := (clipUnit_eq_self hunit).symm
      _ ≤ LoopParams.clipUnit (β + p.α * p.G β) :=
        LoopParams.monotone_clipUnit (by nlinarith [model.α_pos, hG])
  · simp only [LoopParams.loopMap]
    exact (loopStationaryStock_fixed model hgain hunit).ge

/-- The characteristic orbit above the saddle converges to the captured corner. -/
theorem characteristicOrbit_tendsto_captured {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (ss : StrictStepSize p) (threshold : PaperII.ThresholdAssumption p)
    {β : ℝ} (hβ : β ∈ Ioc threshold.βdagger 1) :
    Tendsto (fullLoopOrbit p (β, p.stationaryStock β)) atTop
      (𝓝 (1, p.stationaryStock 1)) := by
  let x₀ : LoopState := (β, p.stationaryStock β)
  let x := fullLoopOrbit p x₀
  have hunit : β ∈ Icc (0 : ℝ) 1 :=
    ⟨threshold.βdagger_mem.1.le.trans hβ.1.le, hβ.2⟩
  have hx₀ : x₀ ∈ classificationBox p :=
    characteristicState_mem_classificationBox model hgain hunit
  have htraj : IsLoopOrbit p x := fullLoopOrbit_isOrbit p x₀
  have hstep : x 0 ≤ x 1 := by
    simpa only [x, x₀, fullLoopOrbit_zero, fullLoopOrbit_succ] using
      characteristicState_le_step model hgain threshold hβ
  obtain ⟨q, hq, hlim, hequilibrium⟩ :=
    comparableStep_convergesToFixedPoint model hgain (ss.toCooperativeCeiling model hgain) htraj hx₀
      (t := 0) (Or.inl (by simpa using hstep))
  have hxmem := orbit_mem_classificationBox model hgain
      (ss.toCooperativeCeiling model hgain) htraj hx₀
  have hmono : Monotone x := by
    simpa only [Nat.add_zero] using
      orbit_tail_monotone_of_le model hgain
      
        (ss.toCooperativeCeiling model hgain) htraj hxmem (t := 0) hstep
  have hβlower : ∀ n, β ≤ (x n).1 := by
    intro n
    have := (hmono (Nat.zero_le n)).1
    simpa only [x, x₀, fullLoopOrbit_zero] using this
  have hqβge : β ≤ q.1 :=
    isClosed_Ici.mem_of_tendsto ((continuous_fst.tendsto q).comp hlim)
      (Eventually.of_forall hβlower)
  rcases (loopEquilibrium_iff_stationary_sign_catalogue model hgain q.1 q.2).1
      hequilibrium with hcalibrated | hinterior | hcaptured
  · rcases hcalibrated with ⟨hqzero, -, -⟩
    have hβpos : 0 < β := threshold.βdagger_mem.1.trans hβ.1
    rw [hqzero] at hqβge
    linarith
  · rcases hinterior with ⟨hqint, -, hqG⟩
    have hqabove : threshold.βdagger < q.1 := hβ.1.trans_le hqβge
    have hqGpos := threshold.G_pos_after q.1 hqint hqabove
    linarith
  · rcases hcaptured with ⟨hqone, hqstock, -⟩
    have hqeq : q = (1, p.stationaryStock 1) := Prod.ext hqone hqstock
    simpa only [x, x₀, hqeq] using hlim

/-- Any state in `B` that dominates an above-saddle characteristic point is captured. -/
theorem tendsto_captured_of_dominates_characteristic {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (ss : StrictStepSize p) (threshold : PaperII.ThresholdAssumption p)
    {b : ℝ} (hb : b ∈ Ioc threshold.βdagger 1) {x₀ : LoopState}
    (hx₀ : x₀ ∈ classificationBox p)
    (hdom : (b, p.stationaryStock b) ≤ x₀) :
    Tendsto (fullLoopOrbit p x₀) atTop (𝓝 (1, p.stationaryStock 1)) := by
  have hbunit : b ∈ Icc (0 : ℝ) 1 :=
    ⟨threshold.βdagger_mem.1.le.trans hb.1.le, hb.2⟩
  have hy₀ := characteristicState_mem_classificationBox model hgain hbunit
  have horder := fullLoopOrbit_le_of_le_in_classificationBox model hgain ss hy₀ hx₀ hdom
  have hylimit := characteristicOrbit_tendsto_captured model hgain ss threshold hb
  have hxmem := orbit_mem_classificationBox model hgain
    (ss.toCooperativeCeiling model hgain) (fullLoopOrbit_isOrbit p x₀) hx₀
  have hupper : ∀ n, fullLoopOrbit p x₀ n ≤ (1, p.stationaryStock 1) := by
    intro n
    exact ⟨(hxmem n).1.2, by
      rw [stationaryStock_one_eq_stockCeiling]
      exact (hxmem n).2.2⟩
  have hβlimit : Tendsto (fun n ↦ (fullLoopOrbit p x₀ n).1) atTop (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      ((continuous_fst.tendsto (1, p.stationaryStock 1)).comp hylimit)
      tendsto_const_nhds (fun n ↦ (horder n).1) (fun n ↦ (hupper n).1)
  have hDlimit : Tendsto (fun n ↦ (fullLoopOrbit p x₀ n).2) atTop
      (𝓝 (p.stationaryStock 1)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      ((continuous_snd.tendsto (1, p.stationaryStock 1)).comp hylimit)
      tendsto_const_nhds (fun n ↦ (horder n).2) (fun n ↦ (hupper n).2)
  exact (Prod.tendsto_iff _ _).2 ⟨hβlimit, hDlimit⟩

/-- The characteristic-capture claim restricted to the original invariant box. -/
theorem characteristicCapture_in_classificationBox {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (ss : StrictStepSize p) (threshold : PaperII.ThresholdAssumption p)
    {β D : ℝ} (hβ : β ∈ Ioc threshold.βdagger 1)
    (hcharacteristic : p.stationaryStock β ≤ D) (hD : D ≤ stockCeiling p) :
    Tendsto (fullLoopOrbit p (β, D)) atTop (𝓝 (1, p.stationaryStock 1)) := by
  have hunit : β ∈ Icc (0 : ℝ) 1 :=
    ⟨threshold.βdagger_mem.1.le.trans hβ.1.le, hβ.2⟩
  have hx₀ : (β, D) ∈ classificationBox p := ⟨hunit,
    (injection_le_stationaryStock model hgain hunit).trans hcharacteristic, hD⟩
  exact tendsto_captured_of_dominates_characteristic model hgain ss threshold hβ hx₀
    ⟨le_rfl, hcharacteristic⟩

/-! ## Stocks above the invariant box -/

/-- The stock multiplier, including content gain, is strictly positive on the policy interval. -/
theorem stockMultiplier_add_gain_pos {p : LoopParams}
    (model : LoopModelAssumptions p) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 < p.s β + p.g := by
  have hbase : 0 < p.s 0 + p.g := stockDiagonalLower_pos model
  have hs : p.s 0 ≤ p.s β :=
    (stockMultiplier_strictMonoOn model).monotoneOn
      (left_mem_Icc.mpr zero_le_one) hβ hβ.1
  linarith

/-- Above the captured stock ceiling, every policy has gradient larger than `G(1)`. -/
theorem capturedGradient_lt_gradU_of_stockCeiling_lt {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {β D : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) (hD : stockCeiling p < D) :
    p.G 1 < p.gradU β D := by
  have hgap : 0 < p.lambda₀ - p.g := sub_pos.mpr hgain
  have hceiling : 0 < stockCeiling p := div_pos model.I_pos hgap
  have hresidual : 1 - p.c ≤ 1 - p.c * β := by
    nlinarith [hβ.2, model.c_pos]
  have hcoefficient : 0 < 2 * p.c * (1 - p.c) := by
    exact mul_pos (mul_pos two_pos model.c_pos) (sub_pos.mpr model.c_lt_one)
  have hfirst : 2 * p.c * (1 - p.c) * stockCeiling p <
      2 * p.c * (1 - p.c) * D :=
    mul_lt_mul_of_pos_left hD hcoefficient
  have hsecond : 2 * p.c * (1 - p.c) * D ≤
      2 * p.c * (1 - p.c * β) * D := by
    have hDpos : 0 < D := hceiling.trans hD
    have hcoefficients : 2 * p.c * (1 - p.c) ≤
        2 * p.c * (1 - p.c * β) :=
      mul_le_mul_of_nonneg_left hresidual
        (mul_nonneg (by norm_num) model.c_pos.le)
    exact mul_le_mul_of_nonneg_right hcoefficients hDpos.le
  rw [← gradU_stationaryStock_eq_G p 1, stationaryStock_one_eq_stockCeiling]
  simp only [LoopParams.gradU]
  linarith

/-- While stock is above the captured ceiling, the projected policy step cannot decrease. -/
theorem policy_le_step_of_stockCeiling_lt {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (threshold : PaperII.ThresholdAssumption p) {β D : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) (hD : stockCeiling p < D) :
    β ≤ p.deferenceStep β D := by
  have hgrad : 0 < p.gradU β D :=
    threshold.G_one_pos.trans (capturedGradient_lt_gradU_of_stockCeiling_lt
      model hgain hβ hD)
  simp only [LoopParams.deferenceStep]
  calc
    β = LoopParams.clipUnit β := (clipUnit_eq_self hβ).symm
    _ ≤ LoopParams.clipUnit (β + p.α * p.gradU β D) :=
      LoopParams.monotone_clipUnit (by nlinarith [model.α_pos, hgrad])

/--
If a nonnegative-stock orbit never crosses the captured ceiling from above,
then it converges to the captured corner directly: the stock excess contracts
to zero while the policy has a fixed positive increment until it clips at one.
-/
theorem tendsto_captured_of_always_above_stockCeiling {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (threshold : PaperII.ThresholdAssumption p) {x₀ : LoopState}
    (hβ₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hD₀ : 0 ≤ x₀.2)
    (habove : ∀ n, stockCeiling p < (fullLoopOrbit p x₀ n).2) :
    Tendsto (fullLoopOrbit p x₀) atTop (𝓝 (1, p.stationaryStock 1)) := by
  let x := fullLoopOrbit p x₀
  have htraj : IsLoopOrbit p x := fullLoopOrbit_isOrbit p x₀
  have hβmem : ∀ n, (x n).1 ∈ Icc (0 : ℝ) 1 := policy_mem_unit htraj hβ₀
  have hstockNonneg : ∀ n, 0 ≤ (x n).2 := stock_nonneg model htraj hβ₀ hD₀
  let δ : ℝ := p.α * p.G 1
  have hδ : 0 < δ := mul_pos model.α_pos threshold.G_one_pos
  have hresidual : ∀ n, 0 ≤ 1 - (x n).1 := fun n ↦ sub_nonneg.mpr (hβmem n).2
  have hdescent : ∀ n, δ ≤ 1 - (x n).1 →
      1 - (x (n + 1)).1 ≤ (1 - (x n).1) - δ := by
    intro n hn
    have hgrad := capturedGradient_lt_gradU_of_stockCeiling_lt model hgain
      (hβmem n) (habove n)
    have hscaled : δ < p.α * p.gradU (x n).1 (x n).2 := by
      exact mul_lt_mul_of_pos_left hgrad model.α_pos
    have htarget : (x n).1 + δ ∈ Icc (0 : ℝ) 1 := by
      constructor
      · nlinarith [(hβmem n).1, hδ]
      · linarith
    have hpolicy : (x n).1 + δ ≤ (x (n + 1)).1 := by
      rw [htraj n]
      simp only [LoopParams.loopMap, LoopParams.deferenceStep]
      calc
        (x n).1 + δ = LoopParams.clipUnit ((x n).1 + δ) :=
          (clipUnit_eq_self htarget).symm
        _ ≤ LoopParams.clipUnit
            ((x n).1 + p.α * p.gradU (x n).1 (x n).2) :=
          LoopParams.monotone_clipUnit (by linarith)
    linarith
  obtain ⟨n, hn⟩ := exists_lt_of_uniform_descent hresidual hδ hdescent
  have hβone : (x (n + 1)).1 = 1 := by
    have hgrad := capturedGradient_lt_gradU_of_stockCeiling_lt model hgain
      (hβmem n) (habove n)
    have hscaled : δ < p.α * p.gradU (x n).1 (x n).2 :=
      mul_lt_mul_of_pos_left hgrad model.α_pos
    have hraw : 1 ≤ (x n).1 + p.α * p.gradU (x n).1 (x n).2 := by
      nlinarith
    rw [htraj n]
    simp only [LoopParams.loopMap, LoopParams.deferenceStep]
    exact (PaperII.clipUnit_eq_one_iff _).2 hraw
  have hpolicyStep : ∀ k, (x k).1 ≤ (x (k + 1)).1 := by
    intro k
    rw [htraj k]
    exact policy_le_step_of_stockCeiling_lt model hgain threshold (hβmem k) (habove k)
  have hβtail : ∀ j, (x (n + 1 + j)).1 = 1 := by
    intro j
    induction j with
    | zero => simpa using hβone
    | succ j ih =>
        have hle : (x (n + 1 + j)).1 ≤ (x (n + 1 + (j + 1))).1 := by
          simpa only [Nat.add_assoc] using hpolicyStep (n + 1 + j)
        have hupper := (hβmem (n + 1 + (j + 1))).2
        rw [ih] at hle
        linarith
  have hβeventual : ∀ k, n + 1 ≤ k → (x k).1 = 1 := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact hβtail j
  have hβlimit : Tendsto (fun k ↦ (x k).1) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    exact Filter.eventually_atTop.2 ⟨n + 1, fun k hk ↦ (hβeventual k hk).symm⟩
  let a : ℝ := 1 - p.lambda₀ + p.g
  have ha_nonneg : 0 ≤ a := by
    dsimp only [a]
    linarith [model.lambda₀_lt_one, model.g_nonneg]
  have ha_lt_one : a < 1 := by
    dsimp only [a]
    linarith
  have hdecay := excess_le_geometric model hgain htraj hβ₀ hD₀
  have hdecay' : ∀ k, (x k).2 - stockCeiling p ≤
      a ^ k * (x₀.2 - stockCeiling p) := by
    intro k
    simpa only [x, a, fullLoopOrbit_zero] using hdecay k
  have hupperLimit : Tendsto
      (fun k : ℕ ↦ a ^ k * (x₀.2 - stockCeiling p)) atTop (𝓝 0) := by
    simpa only [a, zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one ha_nonneg ha_lt_one).mul_const
        (x₀.2 - stockCeiling p)
  have hexcessLimit : Tendsto (fun k ↦ (x k).2 - stockCeiling p) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupperLimit
      (fun k ↦ sub_nonneg.mpr (habove k).le) hdecay'
  have hstockLimit : Tendsto (fun k ↦ (x k).2) atTop (𝓝 (stockCeiling p)) := by
    simpa only [sub_add_cancel, zero_add] using hexcessLimit.add_const (stockCeiling p)
  rw [stationaryStock_one_eq_stockCeiling]
  exact (Prod.tendsto_iff _ _).2 ⟨hβlimit, hstockLimit⟩

/--
Paper III, Lemma 7.3 (`lem:charcap`), civic_loops.tex:543.

In a bistable loop satisfying `(SS_g)`, every policy strictly above the saddle
and every stock on or above that policy's stationary characteristic converges
to the captured corner.  No upper bound on the initial stock is assumed.
-/
theorem characteristicCapture {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (ss : StrictStepSize p) (threshold : PaperII.ThresholdAssumption p)
    {β D : ℝ} (hβ : β ∈ Ioc threshold.βdagger 1)
    (hcharacteristic : p.stationaryStock β ≤ D) :
    Tendsto (fullLoopOrbit p (β, D)) atTop (𝓝 (1, p.stationaryStock 1)) := by
  let x₀ : LoopState := (β, D)
  let x := fullLoopOrbit p x₀
  have hunit : β ∈ Icc (0 : ℝ) 1 :=
    ⟨threshold.βdagger_mem.1.le.trans hβ.1.le, hβ.2⟩
  have hDpos : 0 < D :=
    (div_pos model.I_pos (zoneDenominator_pos model hgain hunit)).trans_le hcharacteristic
  have htraj : IsLoopOrbit p x := fullLoopOrbit_isOrbit p x₀
  have hβmem : ∀ n, (x n).1 ∈ Icc (0 : ℝ) 1 := policy_mem_unit htraj hunit
  by_cases hDupper : D ≤ stockCeiling p
  · exact characteristicCapture_in_classificationBox model hgain ss threshold hβ
      hcharacteristic hDupper
  · have hDabove : stockCeiling p < D := lt_of_not_ge hDupper
    by_cases hentry : ∃ n, (x n).2 ≤ stockCeiling p
    · let T : ℕ := Nat.find hentry
      have hTupper : (x T).2 ≤ stockCeiling p := Nat.find_spec hentry
      have hTpos : 0 < T := by
        by_contra hnot
        have hTzero : T = 0 := Nat.eq_zero_of_not_pos hnot
        rw [hTzero] at hTupper
        simp only [x, x₀, fullLoopOrbit_zero] at hTupper
        linarith
      let k : ℕ := T - 1
      have hTk : T = k + 1 := by
        dsimp only [k]
        omega
      have hkT : k < T := by omega
      have hDk : stockCeiling p < (x k).2 := by
        exact lt_of_not_ge (Nat.find_min hentry hkT)
      have hβlower : ∀ j, j ≤ k → β ≤ (x j).1 := by
        intro j hj
        induction j with
        | zero => exact le_rfl
        | succ j ih =>
            have hjT : j < T := by omega
            have hDj : stockCeiling p < (x j).2 :=
              lt_of_not_ge (Nat.find_min hentry hjT)
            have hstep := policy_le_step_of_stockCeiling_lt model hgain threshold
              (hβmem j) hDj
            have hnext : (x j).1 ≤ (x (j + 1)).1 := by
              rw [htraj j]
              exact hstep
            exact (ih (by omega)).trans hnext
      let b : ℝ := (x k).1
      have hb : b ∈ Ioc threshold.βdagger 1 := by
        refine ⟨hβ.1.trans_le (hβlower k le_rfl), (hβmem k).2⟩
      have hbunit : b ∈ Icc (0 : ℝ) 1 := hβmem k
      have hpolicyDom : b ≤ (x T).1 := by
        rw [hTk, htraj k]
        exact policy_le_step_of_stockCeiling_lt model hgain threshold hbunit hDk
      have hDchar_lt : p.stationaryStock b < (x k).2 := by
        have hcharUpper := stationaryStock_le_policyFreeBound model hgain hbunit
        exact hcharUpper.trans_lt hDk
      have hstockDom : p.stationaryStock b ≤ (x T).2 := by
        apply LT.lt.le
        calc
          p.stationaryStock b = p.stockStep b (p.stationaryStock b) :=
            (loopStationaryStock_fixed model hgain hbunit).symm
          _ < p.stockStep b (x k).2 := by
            simp only [LoopParams.stockStep]
            simpa only [add_comm] using add_lt_add_right
              (mul_lt_mul_of_pos_left hDchar_lt
                (stockMultiplier_add_gain_pos model hbunit)) p.I
          _ = (x T).2 := by
            rw [hTk, htraj k]
            rfl
      have hxT : x T ∈ classificationBox p := by
        refine ⟨hβmem T, ?_, hTupper⟩
        rw [hTk]
        exact injection_le_stock_succ model htraj hunit hDpos.le k
      have htail := tendsto_captured_of_dominates_characteristic model hgain ss
        threshold hb hxT ⟨hpolicyDom, hstockDom⟩
      apply (fullLoopOrbit_tendsto_iff_tail p x₀ (1, p.stationaryStock 1) T).1
      simpa only [x] using htail
    · have habove : ∀ n, stockCeiling p < (x n).2 := by
        intro n
        exact lt_of_not_ge fun hn ↦ hentry ⟨n, hn⟩
      exact tendsto_captured_of_always_above_stockCeiling model hgain threshold
        hunit hDpos.le habove

#print axioms fullLoopOrbit_zero
#print axioms fullLoopOrbit_succ
#print axioms fullLoopOrbit_isOrbit
#print axioms fullLoopOrbit_from_iterate
#print axioms fullLoopOrbit_tendsto_iff_tail
#print axioms injection_le_stationaryStock
#print axioms stationaryStock_one_eq_stockCeiling
#print axioms characteristicState_mem_classificationBox
#print axioms fullLoopOrbit_le_of_le_in_classificationBox
#print axioms characteristicState_le_step
#print axioms characteristicOrbit_tendsto_captured
#print axioms tendsto_captured_of_dominates_characteristic
#print axioms characteristicCapture_in_classificationBox
#print axioms stockMultiplier_add_gain_pos
#print axioms capturedGradient_lt_gradU_of_stockCeiling_lt
#print axioms policy_le_step_of_stockCeiling_lt
#print axioms tendsto_captured_of_always_above_stockCeiling
#print axioms characteristicCapture

end

end CivicAlignment.PaperIII
