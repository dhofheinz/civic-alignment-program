/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.CharacteristicCapture
import CivicAlignment.PaperIII.JumpLimit

/-!
# Paper III: the sub-saddle transient trap

This file formalizes `lem:trap`.  The proof uses a one-sided excess estimate:
upward policy motion lowers the moving-characteristic correction, while a
downward policy move is uniformly bounded by the harm coefficient `v`.  This
keeps the estimate valid even when the initial stock lies below its stationary
characteristic.
-/

namespace CivicAlignment.PaperIII

open Filter Function Set Topology

noncomputable section

/-! ## Uniform constants below the saddle -/

/-- The right endpoint `β† - ρ/2` of the interval used in `lem:trap`. -/
def subSaddleEndpoint {p : LoopParams}
    (threshold : PaperII.ThresholdAssumption p) (ρ : ℝ) : ℝ :=
  threshold.βdagger - ρ / 2

/-- The largest stationary gradient on `[0, β† - ρ/2]`. -/
def subSaddleGradientMaximum {p : LoopParams}
    (threshold : PaperII.ThresholdAssumption p) (ρ : ℝ) : ℝ :=
  sSup (p.G '' Icc (0 : ℝ) (subSaddleEndpoint threshold ρ))

/-- The positive sub-saddle gradient margin `m`. -/
def subSaddleMargin {p : LoopParams}
    (threshold : PaperII.ThresholdAssumption p) (ρ : ℝ) : ℝ :=
  -subSaddleGradientMaximum threshold ρ

/-- A global Lipschitz bound for the stationary-stock characteristic on `[0,1]`. -/
def stationaryStockLipschitzBound (p : LoopParams) : ℝ :=
  2 * p.η * (1 - p.lambda₀) * p.I / (p.lambda₀ - p.g) ^ 2

/-- The policy-free excess allowance `ε*` from `lem:trap`. -/
def subSaddleExcessAllowance (p : LoopParams) (ρ : ℝ) : ℝ :=
  ρ * (p.lambda₀ - p.g) / (16 * p.c)

/--
An explicit small-step ceiling for the sub-saddle trap.  Its first term implies
strict `(SS_g)`; its second makes the moving-characteristic error floor at most
`m/(16c)`.
-/
def subSaddleAlphaCeiling {p : LoopParams}
    (threshold : PaperII.ThresholdAssumption p) (ρ : ℝ) : ℝ :=
  min ((p.lambda₀ - p.g) / (4 * p.c ^ 2 * p.I))
    (subSaddleMargin threshold ρ * (p.lambda₀ - p.g) /
      (16 * p.c * stationaryStockLipschitzBound p * p.v))

/-- The sub-saddle interval is nonempty and lies strictly below the saddle. -/
theorem subSaddleEndpoint_mem {p : LoopParams}
    (threshold : PaperII.ThresholdAssumption p) {ρ : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) threshold.βdagger) :
    subSaddleEndpoint threshold ρ ∈ Ioo (0 : ℝ) threshold.βdagger := by
  rcases hρ with ⟨hρpos, hρlt⟩
  simp only [subSaddleEndpoint]
  constructor <;> nlinarith

/-- The maximum defining `m` is attained. -/
theorem subSaddleGradientMaximum_isGreatest {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (threshold : PaperII.ThresholdAssumption p) {ρ : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) threshold.βdagger) :
    IsGreatest
      (p.G '' Icc (0 : ℝ) (subSaddleEndpoint threshold ρ))
      (subSaddleGradientMaximum threshold ρ) := by
  have hend := subSaddleEndpoint_mem threshold hρ
  have hcont : ContinuousOn p.G
      (Icc (0 : ℝ) (subSaddleEndpoint threshold ρ)) := by
    intro β hβ
    have hunit : β ∈ Icc (0 : ℝ) 1 :=
      ⟨hβ.1, hβ.2.trans (hend.2.le.trans threshold.βdagger_mem.2.le)⟩
    exact (p.hasDerivAt_G β (zoneDenominator_pos model hgain hunit).ne').continuousAt
      |>.continuousWithinAt
  exact (isCompact_Icc.image_of_continuousOn hcont).isGreatest_sSup
    ⟨p.G 0, ⟨0, ⟨le_rfl, hend.1.le⟩, rfl⟩⟩

/-- The maximum definition gives the uniform negative-gradient margin. -/
theorem G_le_neg_subSaddleMargin {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (threshold : PaperII.ThresholdAssumption p) {ρ β : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) threshold.βdagger)
    (hβ : β ∈ Icc (0 : ℝ) (subSaddleEndpoint threshold ρ)) :
    p.G β ≤ -subSaddleMargin threshold ρ := by
  have hmax := (subSaddleGradientMaximum_isGreatest model hgain threshold hρ).2
    ⟨β, hβ, rfl⟩
  simpa only [subSaddleMargin, neg_neg] using hmax

/-- The compact sub-saddle gradient margin is strictly positive. -/
theorem subSaddleMargin_pos {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (threshold : PaperII.ThresholdAssumption p) {ρ : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) threshold.βdagger) :
    0 < subSaddleMargin threshold ρ := by
  have hgreatest := subSaddleGradientMaximum_isGreatest model hgain threshold hρ
  rcases hgreatest.1 with ⟨β, hβ, hvalue⟩
  have hend := subSaddleEndpoint_mem threshold hρ
  have hβlt : β < threshold.βdagger := hβ.2.trans_lt hend.2
  have hGneg : p.G β < 0 := by
    by_cases hzero : β = 0
    · simpa only [hzero] using threshold.G_zero_neg
    · have hβint : β ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne hβ.1 (Ne.symm hzero),
          hβlt.trans threshold.βdagger_mem.2⟩
      exact threshold.G_neg_before β hβint hβlt
  simp only [subSaddleMargin]
  rw [← hvalue]
  exact neg_pos.mpr hGneg

/-- The explicit stationary-characteristic Lipschitz constant is positive. -/
theorem stationaryStockLipschitzBound_pos {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀) :
    0 < stationaryStockLipschitzBound p := by
  simp only [stationaryStockLipschitzBound]
  apply div_pos
  · exact mul_pos
      (mul_pos (mul_pos (by norm_num) model.η_pos) (sub_pos.mpr model.lambda₀_lt_one))
      model.I_pos
  · exact sq_pos_of_pos (sub_pos.mpr hgain)

/-- The policy-free excess allowance is positive. -/
theorem subSaddleExcessAllowance_pos {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀) {ρ : ℝ}
    (hρ : 0 < ρ) : 0 < subSaddleExcessAllowance p ρ := by
  simp only [subSaddleExcessAllowance]
  exact div_pos (mul_pos hρ (sub_pos.mpr hgain)) (mul_pos (by norm_num) model.c_pos)

/-- The displayed small-step ceiling is genuinely positive. -/
theorem subSaddleAlphaCeiling_pos {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (threshold : PaperII.ThresholdAssumption p) {ρ : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) threshold.βdagger) :
    0 < subSaddleAlphaCeiling threshold ρ := by
  have hm := subSaddleMargin_pos model hgain threshold hρ
  have hL := stationaryStockLipschitzBound_pos model hgain
  simp only [subSaddleAlphaCeiling, lt_min_iff]
  constructor
  · exact div_pos (sub_pos.mpr hgain)
      (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos model.c_pos)) model.I_pos)
  · exact div_pos (mul_pos hm (sub_pos.mpr hgain))
      (mul_pos (mul_pos (mul_pos (by norm_num) model.c_pos) hL) model.v_pos)

/-! ## One-step estimates -/

/-- With content gain below grounding, the stationary characteristic is increasing on `[0,1]`. -/
theorem stationaryStock_monoOn {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀) :
    MonotoneOn p.stationaryStock (Icc (0 : ℝ) 1) := by
  intro β₁ hβ₁ β₂ hβ₂ hβ
  have hs := (stockMultiplier_strictMonoOn model).monotoneOn hβ₁ hβ₂ hβ
  have hden₁ := zoneDenominator_pos model hgain hβ₁
  have hden₂ := zoneDenominator_pos model hgain hβ₂
  simp only [LoopParams.stationaryStock]
  exact (div_le_div_iff₀ hden₁ hden₂).2 (by nlinarith [model.I_pos])

/-- The explicit global bound controls every stationary-stock increment on `[0,1]`. -/
theorem stationaryStock_sub_le_lipschitz {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {β₁ β₂ : ℝ} (hβ₁ : β₁ ∈ Icc (0 : ℝ) 1)
    (hβ₂ : β₂ ∈ Icc (0 : ℝ) 1) (hβ : β₁ ≤ β₂) :
    p.stationaryStock β₂ - p.stationaryStock β₁ ≤
      stationaryStockLipschitzBound p * (β₂ - β₁) := by
  let d₁ := 1 - p.s β₁ - p.g
  let d₂ := 1 - p.s β₂ - p.g
  let gap := p.lambda₀ - p.g
  let k := 2 * p.η * (1 - p.lambda₀)
  have hd₁ : 0 < d₁ := zoneDenominator_pos model hgain hβ₁
  have hd₂ : 0 < d₂ := zoneDenominator_pos model hgain hβ₂
  have hgap : 0 < gap := sub_pos.mpr hgain
  have hsdiff := stockMultiplier_sub_le model hβ₁ hβ₂ hβ
  have hgapd₁ : gap ≤ d₁ := by
    dsimp only [gap, d₁]
    linarith [(stockMultiplier_nonneg_le model hβ₁).2]
  have hgapd₂ : gap ≤ d₂ := by
    dsimp only [gap, d₂]
    linarith [(stockMultiplier_nonneg_le model hβ₂).2]
  have hden : gap ^ 2 ≤ d₁ * d₂ := by
    nlinarith [mul_le_mul hgapd₁ hgapd₂ hgap.le hd₁.le]
  have hk_nonneg : 0 ≤ k := by
    dsimp only [k]
    exact mul_nonneg
      (mul_nonneg (by norm_num) model.η_pos.le)
      (sub_nonneg.mpr model.lambda₀_lt_one.le)
  have hdelta : 0 ≤ β₂ - β₁ := sub_nonneg.mpr hβ
  have hnum : p.I * (p.s β₂ - p.s β₁) ≤ p.I * (k * (β₂ - β₁)) := by
    exact mul_le_mul_of_nonneg_left (by simpa only [k] using hsdiff) model.I_pos.le
  have hupper_nonneg : 0 ≤ p.I * (k * (β₂ - β₁)) :=
    mul_nonneg model.I_pos.le (mul_nonneg hk_nonneg hdelta)
  have hfrac :
      p.I * (p.s β₂ - p.s β₁) / (d₁ * d₂) ≤
        p.I * (k * (β₂ - β₁)) / gap ^ 2 :=
    div_le_div₀ hupper_nonneg hnum (sq_pos_of_pos hgap) hden
  have hid : p.stationaryStock β₂ - p.stationaryStock β₁ =
      p.I * (p.s β₂ - p.s β₁) / (d₁ * d₂) := by
    simp only [LoopParams.stationaryStock]
    rw [div_sub_div p.I p.I hd₂.ne' hd₁.ne']
    dsimp only [d₁, d₂]
    ring
  rw [hid]
  calc
    _ ≤ p.I * (k * (β₂ - β₁)) / gap ^ 2 := hfrac
    _ = stationaryStockLipschitzBound p * (β₂ - β₁) := by
      simp only [stationaryStockLipschitzBound]
      dsimp only [k, gap]
      ring

/-- The instantaneous gradient is stationary gradient plus stock excess times `A(β)`. -/
theorem gradU_eq_G_add_jumpGain_mul_excess (p : LoopParams) (β D : ℝ) :
    p.gradU β D = p.G β + jumpGain p β * (D - p.stationaryStock β) := by
  simp only [LoopParams.gradU, LoopParams.G, LoopParams.stationaryStock, jumpGain]
  ring

/-- On the policy interval, `A(β)` lies in `[0,2c]`. -/
theorem jumpGain_nonneg_le {p : LoopParams} (model : LoopModelAssumptions p)
    {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 ≤ jumpGain p β ∧ jumpGain p β ≤ 2 * p.c := by
  have hresidual_nonneg : 0 ≤ 1 - p.c * β := by
    nlinarith [mul_le_mul_of_nonneg_left hβ.2 model.c_pos.le, model.c_lt_one]
  have hresidual_le : 1 - p.c * β ≤ 1 := by
    nlinarith [mul_nonneg model.c_pos.le hβ.1]
  simp only [jumpGain]
  constructor
  · exact mul_nonneg (mul_nonneg (by norm_num) model.c_pos.le) hresidual_nonneg
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hresidual_le
      (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) model.c_pos.le)

/-- Nonnegative stock prevents the raw gradient from falling below `-v`. -/
theorem neg_v_le_gradU {p : LoopParams} (model : LoopModelAssumptions p)
    {β D : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) (hD : 0 ≤ D) :
    -p.v ≤ p.gradU β D := by
  have hA := (jumpGain_nonneg_le model hβ).1
  simp only [LoopParams.gradU, jumpGain] at hA ⊢
  nlinarith [mul_nonneg hA hD]

/-- A positive projected value cannot exceed its unprojected input: `lem:clip`(ii),
the projection is inactive or clips downward off the upper face. -/
theorem clipUnit_le_input_of_pos_trap {z : ℝ}
    (hpos : 0 < LoopParams.clipUnit z) :
    LoopParams.clipUnit z ≤ z := by
  simp only [clipUnit_eq_clipTo] at hpos ⊢
  exact clipTo_le_input hpos

/-- Projection cannot move policy downward by more than `αv` at nonnegative stock. -/
theorem policy_sub_deferenceStep_le {p : LoopParams}
    (model : LoopModelAssumptions p) {β D : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) (hD : 0 ≤ D) :
    β - p.deferenceStep β D ≤ p.α * p.v := by
  have hgrad := neg_v_le_gradU model hβ hD
  by_cases htarget : 0 ≤ β - p.α * p.v
  · have htargetMem : β - p.α * p.v ∈ Icc (0 : ℝ) 1 :=
      ⟨htarget, by nlinarith [hβ.2, model.α_pos, model.v_pos]⟩
    have hinput : β - p.α * p.v ≤ β + p.α * p.gradU β D := by
      nlinarith [mul_le_mul_of_nonneg_left hgrad model.α_pos.le]
    have hclip := LoopParams.monotone_clipUnit hinput
    rw [clipUnit_eq_self htargetMem] at hclip
    simp only [LoopParams.deferenceStep]
    linarith
  · have hβsmall : β < p.α * p.v := by linarith
    have hstep_nonneg := (LoopParams.clipUnit_mem
      (β + p.α * p.gradU β D)).1
    simp only [LoopParams.deferenceStep]
    linarith

/-- A nonpositive raw gradient cannot increase projected policy. -/
theorem deferenceStep_le_of_grad_nonpos {p : LoopParams} {β D : ℝ}
    (hα : 0 ≤ p.α) (hβ : β ∈ Icc (0 : ℝ) 1)
    (hgrad : p.gradU β D ≤ 0) :
    p.deferenceStep β D ≤ β := by
  have hinput : β + p.α * p.gradU β D ≤ β := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hα hgrad]
  have hclip := LoopParams.monotone_clipUnit hinput
  rw [clipUnit_eq_self hβ] at hclip
  simpa only [LoopParams.deferenceStep] using hclip

/-- If the stationary gradient is nonpositive, upward policy motion is paid
for by positive excess. -/
theorem policy_ascent_le_excess {p : LoopParams}
    (model : LoopModelAssumptions p) {β D : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) (hG : p.G β ≤ 0) :
    p.deferenceStep β D - β ≤
      2 * p.c * p.α * max (D - p.stationaryStock β) 0 := by
  let E := D - p.stationaryStock β
  have hA := jumpGain_nonneg_le model hβ
  by_cases hup : β < p.deferenceStep β D
  · have hclipPos : 0 < p.deferenceStep β D := hβ.1.trans_lt hup
    have hraw : p.deferenceStep β D ≤ β + p.α * p.gradU β D := by
      simp only [LoopParams.deferenceStep]
      exact clipUnit_le_input_of_pos_trap
        (by simpa only [LoopParams.deferenceStep] using hclipPos)
    have hE : E ≤ max E 0 := le_max_left _ _
    have hgrad : p.gradU β D ≤ jumpGain p β * max E 0 := by
      rw [gradU_eq_G_add_jumpGain_mul_excess]
      have hmul := mul_le_mul_of_nonneg_left hE hA.1
      linarith
    have hscaled := mul_le_mul_of_nonneg_left hgrad model.α_pos.le
    have hgainBound := mul_le_mul_of_nonneg_right hA.2 (le_max_right E 0)
    have hgainScaled := mul_le_mul_of_nonneg_left hgainBound model.α_pos.le
    change p.deferenceStep β D - β ≤ 2 * p.c * p.α * max E 0
    nlinarith
  · have hnonpos : p.deferenceStep β D - β ≤ 0 := sub_nonpos.mpr (not_lt.mp hup)
    have hrhs : 0 ≤ 2 * p.c * p.α * max E 0 :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) model.c_pos.le) model.α_pos.le)
        (le_max_right E 0)
    exact hnonpos.trans hrhs

/-- Stock excess above the moving stationary characteristic. -/
def orbitExcess (p : LoopParams) (x₀ : LoopState) (n : ℕ) : ℝ :=
  (fullLoopOrbit p x₀ n).2 - p.stationaryStock (fullLoopOrbit p x₀ n).1

/-- Uniform affine contraction factor for positive stock excess. -/
def subSaddleContraction (p : LoopParams) : ℝ :=
  1 - p.lambda₀ + p.g

/-- Stationary error floor in the one-sided excess estimate. -/
def subSaddleErrorFloor (p : LoopParams) : ℝ :=
  p.α * stationaryStockLipschitzBound p * p.v / (p.lambda₀ - p.g)

/-- Geometric envelope for all cumulative upward policy motion. -/
def subSaddleAscentEnvelope (p : LoopParams) (x₀ : LoopState) : ℝ :=
  (8 * p.c / 3) * p.α * max (orbitExcess p x₀ 0) 0 / (p.lambda₀ - p.g)

/-- The excess obeys the exact moving-characteristic recursion. -/
theorem orbitExcess_succ {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {x₀ : LoopState} {n : ℕ}
    (hβ : (fullLoopOrbit p x₀ n).1 ∈ Icc (0 : ℝ) 1) :
    orbitExcess p x₀ (n + 1) =
      (p.s (fullLoopOrbit p x₀ n).1 + p.g) * orbitExcess p x₀ n +
        p.stationaryStock (fullLoopOrbit p x₀ n).1 -
          p.stationaryStock (fullLoopOrbit p x₀ (n + 1)).1 := by
  let β := (fullLoopOrbit p x₀ n).1
  have hfixed := loopStationaryStock_fixed model hgain hβ
  simp only [orbitExcess, fullLoopOrbit_succ, LoopParams.loopMap,
    LoopParams.stockStep]
  simp only [LoopParams.stockStep] at hfixed
  linarith

/-- One-step positive-excess estimate, valid on the entire sub-saddle interval. -/
theorem orbitExcess_posPart_succ_le {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {x₀ : LoopState} {n : ℕ} {b : ℝ}
    (hβ : (fullLoopOrbit p x₀ n).1 ∈ Icc (0 : ℝ) b)
    (hβnext : (fullLoopOrbit p x₀ (n + 1)).1 ∈ Icc (0 : ℝ) b)
    (hb : b ≤ 1) (hD : 0 ≤ (fullLoopOrbit p x₀ n).2) :
    max (orbitExcess p x₀ (n + 1)) 0 ≤
      (1 - p.lambda₀ + p.g) * max (orbitExcess p x₀ n) 0 +
        p.α * stationaryStockLipschitzBound p * p.v := by
  let β := (fullLoopOrbit p x₀ n).1
  let β' := (fullLoopOrbit p x₀ (n + 1)).1
  let E := orbitExcess p x₀ n
  let q := 1 - p.lambda₀ + p.g
  let L := stationaryStockLipschitzBound p
  have hβunit : β ∈ Icc (0 : ℝ) 1 := ⟨hβ.1, hβ.2.trans hb⟩
  have hβnextUnit : β' ∈ Icc (0 : ℝ) 1 := ⟨hβnext.1, hβnext.2.trans hb⟩
  have hmult := stockMultiplier_nonneg_le model hβunit
  have hcoeff_nonneg : 0 ≤ p.s β + p.g := add_nonneg hmult.1 model.g_nonneg
  have hcoeff_le : p.s β + p.g ≤ q := by
    dsimp only [q]
    linarith
  have hq_nonneg : 0 ≤ q := by
    dsimp only [q]
    linarith [model.lambda₀_lt_one, model.g_nonneg]
  have hEmax : E ≤ max E 0 := le_max_left _ _
  have hstockTerm :
      p.stationaryStock β - p.stationaryStock β' ≤ p.α * L * p.v := by
    by_cases hup : β ≤ β'
    · have hmono := stationaryStock_monoOn model hgain hβunit hβnextUnit hup
      have hnonpos : p.stationaryStock β - p.stationaryStock β' ≤ 0 :=
        sub_nonpos.mpr hmono
      have hrhs : 0 ≤ p.α * L * p.v := by
        have hL := stationaryStockLipschitzBound_pos model hgain
        exact mul_nonneg (mul_nonneg model.α_pos.le hL.le) model.v_pos.le
      exact hnonpos.trans hrhs
    · have hdown : β' ≤ β := (not_le.mp hup).le
      have hlip := stationaryStock_sub_le_lipschitz model hgain
        hβnextUnit hβunit hdown
      have hmove := policy_sub_deferenceStep_le model hβunit hD
      have hβeq : β' = p.deferenceStep β (fullLoopOrbit p x₀ n).2 := by
        simp only [β', β, fullLoopOrbit_succ, LoopParams.loopMap]
      rw [← hβeq] at hmove
      have hLnonneg := (stationaryStockLipschitzBound_pos model hgain).le
      have hscaled := mul_le_mul_of_nonneg_left hmove hLnonneg
      dsimp only [L]
      nlinarith
  have hmain : orbitExcess p x₀ (n + 1) ≤
      q * max E 0 + p.α * L * p.v := by
    rw [orbitExcess_succ model hgain hβunit]
    have hfirst : (p.s β + p.g) * E ≤ q * max E 0 :=
      (mul_le_mul_of_nonneg_left hEmax hcoeff_nonneg).trans
        (mul_le_mul_of_nonneg_right hcoeff_le (le_max_right E 0))
    dsimp only [β, β', E, q, L] at hfirst hstockTerm ⊢
    linarith
  have hrhs_nonneg : 0 ≤ q * max E 0 + p.α * L * p.v := by
    have hL := stationaryStockLipschitzBound_pos model hgain
    exact add_nonneg (mul_nonneg hq_nonneg (le_max_right E 0))
      (mul_nonneg (mul_nonneg model.α_pos.le hL.le) model.v_pos.le)
  apply max_le
  · simpa only [q, E, L] using hmain
  · simpa only [q, E, L] using hrhs_nonneg

/-! ## Consequences of the explicit step ceiling -/

/-- The first part of `α₀` implies strict `(SS_g)`. -/
theorem strictStepSize_of_le_subSaddleAlphaCeiling {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (threshold : PaperII.ThresholdAssumption p) {ρ : ℝ}
    (hα : p.α ≤ subSaddleAlphaCeiling threshold ρ) :
    StrictStepSize p := by
  have hden : 0 < 4 * p.c ^ 2 * p.I :=
    mul_pos (mul_pos (by norm_num) (sq_pos_of_pos model.c_pos)) model.I_pos
  have hbound : p.α ≤ (p.lambda₀ - p.g) / (4 * p.c ^ 2 * p.I) :=
    hα.trans (min_le_left _ _)
  have hcross := (le_div_iff₀ hden).mp hbound
  constructor
  nlinarith [sub_pos.mpr hgain]

/-- The second part of `α₀` controls the excess recursion's stationary error floor. -/
theorem subSaddleErrorFloor_le {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (threshold : PaperII.ThresholdAssumption p) {ρ : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) threshold.βdagger)
    (hα : p.α ≤ subSaddleAlphaCeiling threshold ρ) :
    p.α * stationaryStockLipschitzBound p * p.v / (p.lambda₀ - p.g) ≤
      subSaddleMargin threshold ρ / (16 * p.c) := by
  have hm := subSaddleMargin_pos model hgain threshold hρ
  have hL := stationaryStockLipschitzBound_pos model hgain
  have hgap : 0 < p.lambda₀ - p.g := sub_pos.mpr hgain
  have hc16 : 0 < 16 * p.c := mul_pos (by norm_num) model.c_pos
  have hden : 0 < 16 * p.c * stationaryStockLipschitzBound p * p.v := by
    exact mul_pos (mul_pos hc16 hL) model.v_pos
  have hbound : p.α ≤
      subSaddleMargin threshold ρ * (p.lambda₀ - p.g) /
        (16 * p.c * stationaryStockLipschitzBound p * p.v) :=
    hα.trans (min_le_right _ _)
  have hcross := (le_div_iff₀ hden).mp hbound
  apply (div_le_div_iff₀ hgap hc16).2
  nlinarith

/-- The initial allowance budgets at most `ρ/6` of total upward policy motion. -/
theorem subSaddleAscentBudget {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {ρ E : ℝ}
    (hE : p.α * max E 0 ≤ subSaddleExcessAllowance p ρ) :
    (8 * p.c / 3) * p.α * max E 0 / (p.lambda₀ - p.g) ≤ ρ / 6 := by
  have hgap : 0 < p.lambda₀ - p.g := sub_pos.mpr hgain
  have hc16 : 0 < 16 * p.c := mul_pos (by norm_num) model.c_pos
  have hE' : p.α * max E 0 ≤
      ρ * (p.lambda₀ - p.g) / (16 * p.c) := by
    simpa only [subSaddleExcessAllowance] using hE
  have hcross := (le_div_iff₀ hc16).mp hE'
  apply (div_le_iff₀ hgap).2
  nlinarith

/-! ## Coupled transient bounds -/

set_option maxHeartbeats 1000000 in
-- The coupled nonlinear induction requires more normalization than the default budget permits.
/--
The policy ascent and positive stock excess satisfy simultaneous geometric
bounds.  In particular, the total possible ascent is finite even for an
initial stock below the stationary characteristic.
-/
theorem subSaddleOrbit_bounds {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (threshold : PaperII.ThresholdAssumption p) {ρ β₀ D₀ : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) threshold.βdagger)
    (hα : p.α ≤ subSaddleAlphaCeiling threshold ρ)
    (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1)
    (hbelow : β₀ ≤ threshold.βdagger - ρ)
    (hD₀ : 0 ≤ D₀)
    (hscaled : p.α * (D₀ - p.stationaryStock β₀) ≤
      subSaddleExcessAllowance p ρ) :
    let x₀ : LoopState := (β₀, D₀)
    ∀ n,
      (fullLoopOrbit p x₀ n).1 ≤
          β₀ + subSaddleAscentEnvelope p x₀ *
            (1 - subSaddleContraction p ^ n) ∧
        max (orbitExcess p x₀ n) 0 ≤
          subSaddleContraction p ^ n * max (orbitExcess p x₀ 0) 0 +
            subSaddleErrorFloor p := by
  dsimp only
  let x₀ : LoopState := (β₀, D₀)
  let q := subSaddleContraction p
  let gap := p.lambda₀ - p.g
  let m := subSaddleMargin threshold ρ
  let L := stationaryStockLipschitzBound p
  let e₀ := max (orbitExcess p x₀ 0) 0
  let r := subSaddleErrorFloor p
  let B := subSaddleAscentEnvelope p x₀
  have hgap : 0 < gap := sub_pos.mpr hgain
  have hq_nonneg : 0 ≤ q := by
    dsimp only [q, subSaddleContraction]
    linarith [model.lambda₀_lt_one, model.g_nonneg]
  have hq_lt : q < 1 := by
    dsimp only [q, subSaddleContraction]
    linarith
  have hm : 0 < m := by
    dsimp only [m]
    exact subSaddleMargin_pos model hgain threshold hρ
  have hL : 0 < L := by
    dsimp only [L]
    exact stationaryStockLipschitzBound_pos model hgain
  have hr_nonneg : 0 ≤ r := by
    dsimp only [r, subSaddleErrorFloor]
    exact div_nonneg
      (mul_nonneg (mul_nonneg model.α_pos.le hL.le) model.v_pos.le) hgap.le
  have hr_small : r ≤ m / (16 * p.c) := by
    dsimp only [r, m, L, subSaddleErrorFloor]
    exact subSaddleErrorFloor_le model hgain threshold hρ hα
  have htraj := fullLoopOrbit_isOrbit p x₀
  have hβmem : ∀ n, (fullLoopOrbit p x₀ n).1 ∈ Icc (0 : ℝ) 1 := by
    apply policy_mem_unit htraj
    simpa only [x₀, fullLoopOrbit_zero] using hβ₀
  have hDnonneg : ∀ n, 0 ≤ (fullLoopOrbit p x₀ n).2 := by
    apply stock_nonneg model htraj
    · simpa only [x₀, fullLoopOrbit_zero] using hβ₀
    · simpa only [x₀, fullLoopOrbit_zero] using hD₀
  have hallowance_pos := subSaddleExcessAllowance_pos model hgain hρ.1
  have he₀scaled : p.α * e₀ ≤ subSaddleExcessAllowance p ρ := by
    have hEzero : orbitExcess p x₀ 0 = D₀ - p.stationaryStock β₀ := by
      simp only [orbitExcess, x₀, fullLoopOrbit_zero]
    by_cases hE : orbitExcess p x₀ 0 ≤ 0
    · simp only [e₀, max_eq_right hE, mul_zero]
      exact hallowance_pos.le
    · simp only [e₀, max_eq_left (le_of_not_ge hE), hEzero]
      exact hscaled
  have hB_budget : B ≤ ρ / 6 := by
    dsimp only [B, subSaddleAscentEnvelope, e₀]
    exact subSaddleAscentBudget model hgain he₀scaled
  have hB_nonneg : 0 ≤ B := by
    dsimp only [B, subSaddleAscentEnvelope]
    have h8c : 0 ≤ 8 * p.c / 3 :=
      div_nonneg (mul_nonneg (by norm_num) model.c_pos.le) (by norm_num)
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg h8c model.α_pos.le)
        (le_max_right (orbitExcess p x₀ 0) 0)) hgap.le
  have hend := subSaddleEndpoint_mem threshold hρ
  have hend_le_one : subSaddleEndpoint threshold ρ ≤ 1 :=
    hend.2.le.trans threshold.βdagger_mem.2.le
  have hgap_eq : gap = 1 - q := by
    dsimp only [gap, q, subSaddleContraction]
    ring
  have hB_gap : B * gap = (8 * p.c / 3) * p.α * e₀ := by
    dsimp only [B, subSaddleAscentEnvelope, e₀, gap]
    exact div_mul_cancel₀ _ hgap.ne'
  have hstepIdentity : ∀ n,
      B * (1 - q ^ (n + 1)) =
        B * (1 - q ^ n) + (8 * p.c / 3) * p.α * q ^ n * e₀ := by
    intro n
    calc
      B * (1 - q ^ (n + 1)) =
          B * (1 - q ^ n) + (B * gap) * q ^ n := by
            rw [pow_succ, hgap_eq]
            ring
      _ = B * (1 - q ^ n) + (8 * p.c / 3) * p.α * q ^ n * e₀ := by
            rw [hB_gap]
            ring
  have hr_gap : r * gap = p.α * L * p.v := by
    dsimp only [r, subSaddleErrorFloor, L, gap]
    exact div_mul_cancel₀ _ hgap.ne'
  have hfloorIdentity :
      q * r + p.α * L * p.v = r := by
    rw [← hr_gap, hgap_eq]
    ring
  intro n
  induction n with
  | zero =>
      constructor
      · simp only [fullLoopOrbit_zero, pow_zero, sub_self, mul_zero, add_zero]
        exact le_rfl
      · simp only [pow_zero, one_mul]
        exact le_add_of_nonneg_right hr_nonneg
  | succ n ih =>
      have hpow_nonneg : 0 ≤ q ^ n := pow_nonneg hq_nonneg n
      have hpow_le_one : q ^ n ≤ 1 := pow_le_one₀ hq_nonneg hq_lt.le
      have hfactor : 0 ≤ 1 - q ^ n := sub_nonneg.mpr hpow_le_one
      have hpartial : B * (1 - q ^ n) ≤ ρ / 6 := by
        have hfactor_le_one : 1 - q ^ n ≤ 1 := by linarith
        exact (mul_le_of_le_one_right hB_nonneg hfactor_le_one).trans hB_budget
      have hβupper : (fullLoopOrbit p x₀ n).1 ≤ subSaddleEndpoint threshold ρ := by
        calc
          (fullLoopOrbit p x₀ n).1 ≤ β₀ + B * (1 - q ^ n) := ih.1
          _ ≤ threshold.βdagger - ρ + ρ / 6 := add_le_add hbelow hpartial
          _ ≤ subSaddleEndpoint threshold ρ := by
            simp only [subSaddleEndpoint]
            nlinarith [hρ.1]
      have hβinterval : (fullLoopOrbit p x₀ n).1 ∈
          Icc (0 : ℝ) (subSaddleEndpoint threshold ρ) :=
        ⟨(hβmem n).1, hβupper⟩
      have hGmargin := G_le_neg_subSaddleMargin model hgain threshold hρ hβinterval
      have hGnonpos : p.G (fullLoopOrbit p x₀ n).1 ≤ 0 :=
        hGmargin.trans (neg_nonpos.mpr hm.le)
      have hqterm_nonneg : 0 ≤ q ^ n * e₀ :=
        mul_nonneg hpow_nonneg (le_max_right _ _)
      have hascent :
          (fullLoopOrbit p x₀ (n + 1)).1 - (fullLoopOrbit p x₀ n).1 ≤
            (8 * p.c / 3) * p.α * q ^ n * e₀ := by
        have hbase := policy_ascent_le_excess model
          (β := (fullLoopOrbit p x₀ n).1)
          (D := (fullLoopOrbit p x₀ n).2) (hβmem n) hGnonpos
        have hbase' :
            p.deferenceStep (fullLoopOrbit p x₀ n).1 (fullLoopOrbit p x₀ n).2 -
                (fullLoopOrbit p x₀ n).1 ≤
              2 * p.c * p.α * max (orbitExcess p x₀ n) 0 := by
          simpa only [orbitExcess] using hbase
        rw [fullLoopOrbit_succ]
        simp only [LoopParams.loopMap]
        by_cases hsmall : max (orbitExcess p x₀ n) 0 ≤ m / (4 * p.c)
        · have hA := jumpGain_nonneg_le model (hβmem n)
          have hE := le_max_left (orbitExcess p x₀ n) 0
          have hAE : jumpGain p (fullLoopOrbit p x₀ n).1 * orbitExcess p x₀ n ≤
              2 * p.c * (m / (4 * p.c)) := by
            have hmul₁ := mul_le_mul_of_nonneg_left hE hA.1
            have hmul₂ := mul_le_mul_of_nonneg_right hA.2
              (le_max_right (orbitExcess p x₀ n) 0)
            have hc : 0 < p.c := model.c_pos
            nlinarith
          have hhalf : 2 * p.c * (m / (4 * p.c)) = m / 2 := by
            field_simp [model.c_pos.ne']
            ring
          rw [hhalf] at hAE
          simp only [orbitExcess] at hAE
          have hgrad : p.gradU (fullLoopOrbit p x₀ n).1
              (fullLoopOrbit p x₀ n).2 ≤ 0 := by
            rw [gradU_eq_G_add_jumpGain_mul_excess]
            nlinarith
          have hdown := deferenceStep_le_of_grad_nonpos model.α_pos.le
            (hβmem n) hgrad
          have hzero : 0 ≤ (8 * p.c / 3) * p.α * q ^ n * e₀ := by
            exact mul_nonneg
              (mul_nonneg
                (mul_nonneg
                  (div_nonneg (mul_nonneg (by norm_num) model.c_pos.le) (by norm_num))
                  model.α_pos.le)
                hpow_nonneg)
              (le_max_right _ _)
          exact (sub_nonpos.mpr hdown).trans hzero
        · have hhigh : m / (4 * p.c) < max (orbitExcess p x₀ n) 0 :=
            lt_of_not_ge hsmall
          have heBound : max (orbitExcess p x₀ n) 0 ≤ q ^ n * e₀ + r := by
            simpa only [q, subSaddleContraction, e₀, r, subSaddleErrorFloor] using ih.2
          have hqlarge : 3 * r ≤ q ^ n * e₀ := by
            have hc16 : 0 < 16 * p.c := mul_pos (by norm_num) model.c_pos
            have hc4 : 0 < 4 * p.c := mul_pos (by norm_num) model.c_pos
            have hrCross := (le_div_iff₀ hc16).mp hr_small
            have hhighCross := (div_lt_iff₀ hc4).mp hhigh
            have heCross := mul_le_mul_of_nonneg_left heBound hc4.le
            nlinarith
          have hfourthirds : max (orbitExcess p x₀ n) 0 ≤
              (4 / 3 : ℝ) * (q ^ n * e₀) := by
            nlinarith [heBound]
          have hscaledUp := mul_le_mul_of_nonneg_left hfourthirds
            (mul_nonneg
              (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) model.c_pos.le)
              model.α_pos.le)
          calc
            p.deferenceStep (fullLoopOrbit p x₀ n).1
                  (fullLoopOrbit p x₀ n).2 - (fullLoopOrbit p x₀ n).1 ≤
                2 * p.c * p.α * max (orbitExcess p x₀ n) 0 := hbase'
            _ ≤ 2 * p.c * p.α * ((4 / 3 : ℝ) * (q ^ n * e₀)) := hscaledUp
            _ = (8 * p.c / 3) * p.α * q ^ n * e₀ := by ring
      have hβnextBound : (fullLoopOrbit p x₀ (n + 1)).1 ≤
          β₀ + B * (1 - q ^ (n + 1)) := by
        rw [hstepIdentity n]
        linarith
      have hpow_next_nonneg : 0 ≤ q ^ (n + 1) := pow_nonneg hq_nonneg _
      have hpow_next_le_one : q ^ (n + 1) ≤ 1 := pow_le_one₀ hq_nonneg hq_lt.le
      have hpartialNext : B * (1 - q ^ (n + 1)) ≤ ρ / 6 := by
        have hfactor_le_one : 1 - q ^ (n + 1) ≤ 1 := by
          linarith [hpow_next_nonneg]
        exact (mul_le_of_le_one_right hB_nonneg hfactor_le_one).trans hB_budget
      have hβnextUpper : (fullLoopOrbit p x₀ (n + 1)).1 ≤
          subSaddleEndpoint threshold ρ := by
        calc
          _ ≤ β₀ + B * (1 - q ^ (n + 1)) := hβnextBound
          _ ≤ threshold.βdagger - ρ + ρ / 6 := add_le_add hbelow hpartialNext
          _ ≤ subSaddleEndpoint threshold ρ := by
            simp only [subSaddleEndpoint]
            nlinarith [hρ.1]
      have hβnextInterval : (fullLoopOrbit p x₀ (n + 1)).1 ∈
          Icc (0 : ℝ) (subSaddleEndpoint threshold ρ) :=
        ⟨(hβmem (n + 1)).1, hβnextUpper⟩
      have hexcessStep := orbitExcess_posPart_succ_le model hgain hβinterval
        hβnextInterval hend_le_one (hDnonneg n)
      have hcontract := mul_le_mul_of_nonneg_left ih.2 hq_nonneg
      constructor
      · simpa only [q, B] using hβnextBound
      · calc
          max (orbitExcess p x₀ (n + 1)) 0 ≤
              q * max (orbitExcess p x₀ n) 0 + p.α * L * p.v := by
                simpa only [q, subSaddleContraction, L] using hexcessStep
          _ ≤ q * (q ^ n * e₀ + r) + p.α * L * p.v := by
                nlinarith
          _ = q ^ (n + 1) * e₀ + r := by
                calc
                  q * (q ^ n * e₀ + r) + p.α * L * p.v =
                      q ^ (n + 1) * e₀ + (q * r + p.α * L * p.v) := by
                        rw [pow_succ]
                        ring
                  _ = q ^ (n + 1) * e₀ + r := by rw [hfloorIdentity]
          _ = subSaddleContraction p ^ (n + 1) *
                max (orbitExcess p x₀ 0) 0 + subSaddleErrorFloor p := by
                rfl

/-- The transient budget keeps every policy iterate below `β† - ρ/2`. -/
theorem subSaddleOrbit_stays_below {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (threshold : PaperII.ThresholdAssumption p) {ρ β₀ D₀ : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) threshold.βdagger)
    (hα : p.α ≤ subSaddleAlphaCeiling threshold ρ)
    (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1)
    (hbelow : β₀ ≤ threshold.βdagger - ρ)
    (hD₀ : 0 ≤ D₀)
    (hscaled : p.α * (D₀ - p.stationaryStock β₀) ≤
      subSaddleExcessAllowance p ρ) :
    ∀ n, (fullLoopOrbit p (β₀, D₀) n).1 ≤ subSaddleEndpoint threshold ρ := by
  let x₀ : LoopState := (β₀, D₀)
  have hbounds := subSaddleOrbit_bounds model hgain threshold hρ hα hβ₀ hbelow hD₀ hscaled
  have hallowance_pos := subSaddleExcessAllowance_pos model hgain hρ.1
  have he₀scaled : p.α * max (orbitExcess p x₀ 0) 0 ≤
      subSaddleExcessAllowance p ρ := by
    have hEzero : orbitExcess p x₀ 0 = D₀ - p.stationaryStock β₀ := by
      simp only [orbitExcess, x₀, fullLoopOrbit_zero]
    by_cases hE : orbitExcess p x₀ 0 ≤ 0
    · simp only [max_eq_right hE, mul_zero]
      exact hallowance_pos.le
    · rw [max_eq_left (le_of_not_ge hE), hEzero]
      exact hscaled
  have hbudget : subSaddleAscentEnvelope p x₀ ≤ ρ / 6 := by
    simpa only [subSaddleAscentEnvelope] using
      (subSaddleAscentBudget model hgain he₀scaled)
  have hq_nonneg : 0 ≤ subSaddleContraction p := by
    simp only [subSaddleContraction]
    linarith [model.lambda₀_lt_one, model.g_nonneg]
  have hq_lt : subSaddleContraction p < 1 := by
    simp only [subSaddleContraction]
    linarith
  have hB_nonneg : 0 ≤ subSaddleAscentEnvelope p x₀ := by
    simp only [subSaddleAscentEnvelope]
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (div_nonneg (mul_nonneg (by norm_num) model.c_pos.le) (by norm_num))
          model.α_pos.le)
        (le_max_right _ _)) (sub_pos.mpr hgain).le
  intro n
  have hpow_nonneg : 0 ≤ subSaddleContraction p ^ n := pow_nonneg hq_nonneg n
  have hpow_le : subSaddleContraction p ^ n ≤ 1 :=
    pow_le_one₀ hq_nonneg hq_lt.le
  have hpartial : subSaddleAscentEnvelope p x₀ *
      (1 - subSaddleContraction p ^ n) ≤ ρ / 6 := by
    have hfactor : 1 - subSaddleContraction p ^ n ≤ 1 := by linarith
    exact (mul_le_of_le_one_right hB_nonneg hfactor).trans hbudget
  calc
    (fullLoopOrbit p (β₀, D₀) n).1 ≤
        β₀ + subSaddleAscentEnvelope p x₀ *
          (1 - subSaddleContraction p ^ n) := (hbounds n).1
    _ ≤ threshold.βdagger - ρ + ρ / 6 := add_le_add hbelow hpartial
    _ ≤ subSaddleEndpoint threshold ρ := by
      simp only [subSaddleEndpoint]
      nlinarith [hρ.1]

/-- Positive excess becomes uniformly too small to overcome the sub-saddle margin. -/
theorem subSaddleOrbit_eventually_grad_le {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (threshold : PaperII.ThresholdAssumption p) {ρ β₀ D₀ : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) threshold.βdagger)
    (hα : p.α ≤ subSaddleAlphaCeiling threshold ρ)
    (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1)
    (hbelow : β₀ ≤ threshold.βdagger - ρ)
    (hD₀ : 0 ≤ D₀)
    (hscaled : p.α * (D₀ - p.stationaryStock β₀) ≤
      subSaddleExcessAllowance p ρ) :
    ∃ N, ∀ n, N ≤ n →
      p.gradU (fullLoopOrbit p (β₀, D₀) n).1
          (fullLoopOrbit p (β₀, D₀) n).2 ≤
        -subSaddleMargin threshold ρ / 2 := by
  let x₀ : LoopState := (β₀, D₀)
  let q := subSaddleContraction p
  let e₀ := max (orbitExcess p x₀ 0) 0
  let r := subSaddleErrorFloor p
  let m := subSaddleMargin threshold ρ
  have hq_nonneg : 0 ≤ q := by
    dsimp only [q, subSaddleContraction]
    linarith [model.lambda₀_lt_one, model.g_nonneg]
  have hq_lt : q < 1 := by
    dsimp only [q, subSaddleContraction]
    linarith
  have hm : 0 < m := by
    dsimp only [m]
    exact subSaddleMargin_pos model hgain threshold hρ
  have hr_small : r ≤ m / (16 * p.c) := by
    dsimp only [r, m, subSaddleErrorFloor]
    exact subSaddleErrorFloor_le model hgain threshold hρ hα
  have hbounds := subSaddleOrbit_bounds model hgain threshold hρ hα hβ₀ hbelow hD₀ hscaled
  have hbelowAll := subSaddleOrbit_stays_below model hgain threshold hρ hα hβ₀
    hbelow hD₀ hscaled
  have htraj := fullLoopOrbit_isOrbit p x₀
  have hβmem : ∀ n, (fullLoopOrbit p x₀ n).1 ∈ Icc (0 : ℝ) 1 := by
    apply policy_mem_unit htraj
    simpa only [x₀, fullLoopOrbit_zero] using hβ₀
  have hpow : Tendsto (fun n : ℕ ↦ q ^ n * e₀) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt).mul_const e₀
  have hcutoff : 0 < m / (16 * p.c) :=
    div_pos hm (mul_pos (by norm_num) model.c_pos)
  have heventually : ∀ᶠ n in atTop, q ^ n * e₀ < m / (16 * p.c) :=
    (tendsto_order.1 hpow).2 _ hcutoff
  obtain ⟨N, hN⟩ := eventually_atTop.1 heventually
  refine ⟨N, ?_⟩
  intro n hn
  have hqsmall := hN n hn
  have hEbound : max (orbitExcess p x₀ n) 0 ≤ q ^ n * e₀ + r := by
    simpa only [q, subSaddleContraction, e₀, r, subSaddleErrorFloor] using (hbounds n).2
  have hEsmall : max (orbitExcess p x₀ n) 0 ≤ m / (8 * p.c) := by
    have hc16 : 0 < 16 * p.c := mul_pos (by norm_num) model.c_pos
    have hc8 : 0 < 8 * p.c := mul_pos (by norm_num) model.c_pos
    have hqCross := (lt_div_iff₀ hc16).mp hqsmall
    have hrCross := (le_div_iff₀ hc16).mp hr_small
    have heCross := mul_le_mul_of_nonneg_left hEbound hc16.le
    apply (le_div_iff₀ hc8).2
    nlinarith
  have hβinterval : (fullLoopOrbit p x₀ n).1 ∈
      Icc (0 : ℝ) (subSaddleEndpoint threshold ρ) :=
    ⟨(hβmem n).1, by simpa only [x₀] using hbelowAll n⟩
  have hG := G_le_neg_subSaddleMargin model hgain threshold hρ hβinterval
  have hA := jumpGain_nonneg_le model (hβmem n)
  have hE := le_max_left (orbitExcess p x₀ n) 0
  have hAE : jumpGain p (fullLoopOrbit p x₀ n).1 * orbitExcess p x₀ n ≤ m / 4 := by
    have hmul₁ := mul_le_mul_of_nonneg_left hE hA.1
    have hmul₂ := mul_le_mul_of_nonneg_right hA.2
      (le_max_right (orbitExcess p x₀ n) 0)
    have hscaledE : 2 * p.c * max (orbitExcess p x₀ n) 0 ≤
        2 * p.c * (m / (8 * p.c)) :=
      mul_le_mul_of_nonneg_left hEsmall
        (mul_nonneg (by norm_num) model.c_pos.le)
    have hidentity : 2 * p.c * (m / (8 * p.c)) = m / 4 := by
      field_simp [model.c_pos.ne']
      ring
    exact hmul₁.trans (hmul₂.trans (hscaledE.trans_eq hidentity))
  simp only [x₀, m, orbitExcess] at hG hAE hm ⊢
  rw [gradU_eq_G_add_jumpGain_mul_excess]
  exact (add_le_add hG hAE).trans (by nlinarith [hm])

/-! ## Finite-time calibration and convergence -/

/-- An eventually uniform negative gradient forces finite-time policy calibration. -/
theorem tendsto_calibrated_of_eventually_grad_le {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {x₀ : LoopState} (hβ₀ : x₀.1 ∈ Icc (0 : ℝ) 1)
    {ε : ℝ} (hε : 0 < ε)
    (heventual : ∃ N, ∀ n, N ≤ n →
      p.gradU (fullLoopOrbit p x₀ n).1 (fullLoopOrbit p x₀ n).2 ≤ -ε) :
    Tendsto (fullLoopOrbit p x₀) atTop (𝓝 (0, p.stationaryStock 0)) := by
  let x := fullLoopOrbit p x₀
  have htraj : IsLoopOrbit p x := fullLoopOrbit_isOrbit p x₀
  have hβmem : ∀ n, (x n).1 ∈ Icc (0 : ℝ) 1 := policy_mem_unit htraj hβ₀
  obtain ⟨N, hgradient⟩ := heventual
  let δ := p.α * ε
  have hδ : 0 < δ := mul_pos model.α_pos hε
  let u : ℕ → ℝ := fun k ↦ (x (N + k)).1
  have hu_nonneg : ∀ k, 0 ≤ u k := fun k ↦ (hβmem (N + k)).1
  have hdescent : ∀ k, δ ≤ u k → u (k + 1) ≤ u k - δ := by
    intro k hk
    have hgrad := hgradient (N + k) (Nat.le_add_right N k)
    have htarget : u k - δ ∈ Icc (0 : ℝ) 1 := by
      constructor
      · linarith
      · have huupper := (hβmem (N + k)).2
        dsimp only [u]
        linarith [hδ]
    have hraw : (x (N + k)).1 + p.α * p.gradU (x (N + k)).1 (x (N + k)).2 ≤
        u k - δ := by
      dsimp only [u, δ]
      have hscaled := mul_le_mul_of_nonneg_left hgrad model.α_pos.le
      nlinarith
    have hclip := LoopParams.monotone_clipUnit hraw
    rw [clipUnit_eq_self htarget] at hclip
    have hnext : (x ((N + k) + 1)).1 ≤ u k - δ := by
      rw [htraj (N + k)]
      simpa only [LoopParams.loopMap, LoopParams.deferenceStep] using hclip
    dsimp only [u]
    simpa only [Nat.add_assoc] using hnext
  obtain ⟨k, hk⟩ := exists_lt_of_uniform_descent hu_nonneg hδ
    (ε := δ) hdescent
  have hgradk := hgradient (N + k) (Nat.le_add_right N k)
  have hrawk : (x (N + k)).1 + p.α * p.gradU (x (N + k)).1 (x (N + k)).2 ≤ 0 := by
    have hscaled := mul_le_mul_of_nonneg_left hgradk model.α_pos.le
    dsimp only [u, δ] at hk
    nlinarith
  let T := N + k + 1
  have hβT : (x T).1 = 0 := by
    dsimp only [T]
    rw [htraj (N + k)]
    simp only [LoopParams.loopMap, LoopParams.deferenceStep]
    exact (PaperII.clipUnit_eq_zero_iff _).2 hrawk
  have hβtail : ∀ j, (x (T + j)).1 = 0 := by
    intro j
    induction j with
    | zero => simpa using hβT
    | succ j ih =>
        have hindex : N ≤ T + j := by
          dsimp only [T]
          omega
        have hgrad := hgradient (T + j) hindex
        have hraw : (x (T + j)).1 +
            p.α * p.gradU (x (T + j)).1 (x (T + j)).2 ≤ 0 := by
          rw [ih]
          have hgrad' : p.gradU (x (T + j)).1 (x (T + j)).2 ≤ -ε := by
            simpa only [x] using hgrad
          rw [ih] at hgrad'
          have hscaled := mul_le_mul_of_nonneg_left hgrad' model.α_pos.le
          nlinarith [hε, model.α_pos]
        have hstep : (x ((T + j) + 1)).1 = 0 := by
          rw [htraj (T + j)]
          simp only [LoopParams.loopMap, LoopParams.deferenceStep]
          exact (PaperII.clipUnit_eq_zero_iff _).2 hraw
        simpa only [Nat.add_assoc] using hstep
  let a := p.s 0 + p.g
  have ha_nonneg : 0 ≤ a := by
    dsimp only [a]
    exact add_nonneg
      (stockMultiplier_nonneg_le model (β := 0) (by norm_num)).1 model.g_nonneg
  have ha_lt : a < 1 := by
    dsimp only [a]
    linarith [(stockMultiplier_nonneg_le model (β := 0) (by norm_num)).2]
  have hstockTail : ∀ j,
      (x (T + j)).2 = arithGeom a p.I (x T).2 j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have hstep : (x ((T + j) + 1)).2 =
            (p.s (x (T + j)).1 + p.g) * (x (T + j)).2 + p.I := by
          rw [htraj (T + j)]
          rfl
        rw [hβtail j, ih] at hstep
        rw [arithGeom_succ]
        dsimp only [a]
        simpa only [Nat.add_assoc] using hstep
  have hlimitEq : p.I / (1 - a) = p.stationaryStock 0 := by
    simp only [a, LoopParams.stationaryStock]
    ring
  have hstockLimit : Tendsto (fun j ↦ (x (T + j)).2) atTop
      (𝓝 (p.stationaryStock 0)) := by
    have harith : Tendsto (arithGeom a p.I (x T).2) atTop
        (𝓝 (p.I / (1 - a))) :=
      tendsto_arithGeom_nhds_of_lt_one ha_nonneg ha_lt
    rw [hlimitEq] at harith
    apply harith.congr'
    exact Eventually.of_forall fun j ↦ (hstockTail j).symm
  have hpolicyLimit : Tendsto (fun j ↦ (x (T + j)).1) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall fun j ↦ (hβtail j).symm
  have htailLimit : Tendsto (fun j ↦ x (T + j)) atTop
      (𝓝 (0, p.stationaryStock 0)) :=
    (Prod.tendsto_iff _ _).2 ⟨hpolicyLimit, hstockLimit⟩
  apply (tendsto_add_atTop_iff_nat T).1
  simpa only [x, Nat.add_comm] using htailLimit

/--
Paper III, Lemma 7.5 (`lem:trap`), `civic_loops.tex:577`.

Fix `ρ ∈ (0,β†)`.  The explicit positive ceiling
`subSaddleAlphaCeiling threshold ρ` depends only on the model constants and
`ρ`.  At every positive adaptation rate below that ceiling, a state starting
at least `ρ` below the saddle and satisfying the paper's rescaled-excess bound
converges to the calibrated corner.
-/
theorem subSaddleTrap {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (threshold : PaperII.ThresholdAssumption p) {ρ β D : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) threshold.βdagger)
    (hα : p.α ≤ subSaddleAlphaCeiling threshold ρ)
    (hβ : β ∈ Icc (0 : ℝ) 1)
    (hbelow : β ≤ threshold.βdagger - ρ)
    (hD : 0 ≤ D)
    (hscaled : p.α * (D - p.stationaryStock β) ≤
      subSaddleExcessAllowance p ρ) :
    Tendsto (fullLoopOrbit p (β, D)) atTop
      (𝓝 (0, p.stationaryStock 0)) := by
  have hm := subSaddleMargin_pos model hgain threshold hρ
  have heventual := subSaddleOrbit_eventually_grad_le model hgain threshold hρ hα
    hβ hbelow hD hscaled
  have heventual' : ∃ N, ∀ n, N ≤ n →
      p.gradU (fullLoopOrbit p (β, D) n).1 (fullLoopOrbit p (β, D) n).2 ≤
        -(subSaddleMargin threshold ρ / 2) := by
    rcases heventual with ⟨N, hN⟩
    exact ⟨N, fun n hn ↦ by simpa only [neg_div] using hN n hn⟩
  exact tendsto_calibrated_of_eventually_grad_le model hgain hβ
    (ε := subSaddleMargin threshold ρ / 2) (by linarith) heventual'

#print axioms subSaddleEndpoint_mem
#print axioms subSaddleGradientMaximum_isGreatest
#print axioms G_le_neg_subSaddleMargin
#print axioms subSaddleMargin_pos
#print axioms stationaryStockLipschitzBound_pos
#print axioms subSaddleExcessAllowance_pos
#print axioms subSaddleAlphaCeiling_pos
#print axioms stationaryStock_monoOn
#print axioms stationaryStock_sub_le_lipschitz
#print axioms gradU_eq_G_add_jumpGain_mul_excess
#print axioms jumpGain_nonneg_le
#print axioms neg_v_le_gradU
#print axioms clipUnit_le_input_of_pos_trap
#print axioms policy_sub_deferenceStep_le
#print axioms deferenceStep_le_of_grad_nonpos
#print axioms policy_ascent_le_excess
#print axioms orbitExcess_succ
#print axioms orbitExcess_posPart_succ_le
#print axioms strictStepSize_of_le_subSaddleAlphaCeiling
#print axioms subSaddleErrorFloor_le
#print axioms subSaddleAscentBudget
#print axioms subSaddleOrbit_bounds
#print axioms subSaddleOrbit_stays_below
#print axioms subSaddleOrbit_eventually_grad_le
#print axioms tendsto_calibrated_of_eventually_grad_le
#print axioms subSaddleTrap

end

end CivicAlignment.PaperIII
