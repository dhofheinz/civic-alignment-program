/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.NonlinearRobustness

/-!
# Paper II: a grounded nonlinear square-root stock law

The ungrounded recursion `(m(β) √D + j)²` has no finite captured
equilibrium when `m(1) = 1` and `j > 0`.  This file studies the grounded
replacement

`m(β) = √(1 - λ₀) (1 - η(1 - β))`,

whose full-deference multiplier is strictly below one.  The registered
characteristic is therefore finite at both endpoints.
-/

namespace CivicAlignment.PaperII

open Filter Function Set Topology

noncomputable section

/-- Primitive restrictions used by the grounded square-root stock family. -/
structure GroundedSqrtPrimitiveAssumptions (p : LoopParams) (j : ℝ) : Prop where
  η_pos : 0 < p.η
  η_lt_one : p.η < 1
  lambda₀_pos : 0 < p.lambda₀
  lambda₀_lt_one : p.lambda₀ < 1
  injection_pos : 0 < j
  c_pos : 0 < p.c
  c_lt_one : p.c < 1
  α_pos : 0 < p.α

/-- Grounded persistence at full deference. -/
def groundedSqrtPersistence (p : LoopParams) : ℝ :=
  √(1 - p.lambda₀)

/-- Policy-dependent persistence in deviation rather than squared deviation. -/
def groundedSqrtMultiplier (p : LoopParams) (β : ℝ) : ℝ :=
  groundedSqrtPersistence p * (1 - p.η * (1 - β))

/-- The genuinely nonlinear stock recursion. -/
def groundedSqrtStockStep (p : LoopParams) (j β D : ℝ) : ℝ :=
  (groundedSqrtMultiplier p β * √D + j) ^ 2

/-- Its finite stationary characteristic. -/
def groundedSqrtCharacteristic (p : LoopParams) (j β : ℝ) : ℝ :=
  (j / (1 - groundedSqrtMultiplier p β)) ^ 2

/-- The largest characteristic value, attained at full deference. -/
def groundedSqrtStockUpper (p : LoopParams) (j : ℝ) : ℝ :=
  (j / (1 - groundedSqrtPersistence p)) ^ 2

theorem groundedSqrtPersistence_pos_lt_one
    {p : LoopParams} {j : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j) :
    0 < groundedSqrtPersistence p ∧ groundedSqrtPersistence p < 1 := by
  have hbase : 0 ≤ 1 - p.lambda₀ :=
    sub_nonneg.mpr primitive.lambda₀_lt_one.le
  have hsquare : (groundedSqrtPersistence p) ^ 2 = 1 - p.lambda₀ := by
    simpa only [groundedSqrtPersistence] using Real.sq_sqrt hbase
  have hnonneg : 0 ≤ groundedSqrtPersistence p := by
    exact Real.sqrt_nonneg _
  constructor
  · exact Real.sqrt_pos.2 (sub_pos.mpr primitive.lambda₀_lt_one)
  · nlinarith [primitive.lambda₀_pos]

/-- The grounded multiplier is uniformly positive and strictly below one on
the registered policy interval. -/
theorem groundedSqrtMultiplier_pos_le
    {p : LoopParams} {j β : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 < groundedSqrtMultiplier p β ∧
      groundedSqrtMultiplier p β ≤ groundedSqrtPersistence p := by
  have hr := groundedSqrtPersistence_pos_lt_one primitive
  have hresidual_nonneg : 0 ≤ 1 - β := sub_nonneg.mpr hβ.2
  have hresidual_le_one : 1 - β ≤ 1 := by linarith [hβ.1]
  have hinner_pos : 0 < 1 - p.η * (1 - β) := by
    have hmul : p.η * (1 - β) ≤ p.η := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hresidual_le_one primitive.η_pos.le
    linarith [primitive.η_lt_one]
  have hinner_le : 1 - p.η * (1 - β) ≤ 1 :=
    sub_le_self _ (mul_nonneg primitive.η_pos.le hresidual_nonneg)
  constructor
  · exact mul_pos hr.1 hinner_pos
  · simp only [groundedSqrtMultiplier]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hinner_le hr.1.le

theorem groundedSqrtMultiplier_lt_one
    {p : LoopParams} {j β : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    (hβ : β ∈ Icc (0 : ℝ) 1) :
    groundedSqrtMultiplier p β < 1 :=
  (groundedSqrtMultiplier_pos_le primitive hβ).2.trans_lt
    (groundedSqrtPersistence_pos_lt_one primitive).2

/-- Exact policy increment of the grounded multiplier. -/
theorem groundedSqrtMultiplier_sub
    (p : LoopParams) (β₁ β₂ : ℝ) :
    groundedSqrtMultiplier p β₂ - groundedSqrtMultiplier p β₁ =
      groundedSqrtPersistence p * p.η * (β₂ - β₁) := by
  simp only [groundedSqrtMultiplier]
  ring

/-- The grounded multiplier is strictly increasing on `[0,1]`. -/
theorem groundedSqrtMultiplier_strictMonoOn
    {p : LoopParams} {j : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j) :
    StrictMonoOn (groundedSqrtMultiplier p) (Icc (0 : ℝ) 1) := by
  intro β₁ _hβ₁ β₂ _hβ₂ hβ
  apply sub_pos.mp
  rw [groundedSqrtMultiplier_sub]
  exact mul_pos (mul_pos
    (groundedSqrtPersistence_pos_lt_one primitive).1 primitive.η_pos)
    (sub_pos.mpr hβ)

/-- The characteristic denominator is uniformly positive. -/
theorem groundedSqrtCharacteristicDenominator_pos
    {p : LoopParams} {j β : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 < 1 - groundedSqrtMultiplier p β :=
  sub_pos.mpr (groundedSqrtMultiplier_lt_one primitive hβ)

/-- The characteristic stays inside the finite registered stock interval. -/
theorem groundedSqrtCharacteristic_mem
    {p : LoopParams} {j β : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    (hβ : β ∈ Icc (0 : ℝ) 1) :
    groundedSqrtCharacteristic p j β ∈
      Icc (j ^ 2) (groundedSqrtStockUpper p j) := by
  have hm := groundedSqrtMultiplier_pos_le primitive hβ
  have hr := groundedSqrtPersistence_pos_lt_one primitive
  have hden : 0 < 1 - groundedSqrtMultiplier p β :=
    groundedSqrtCharacteristicDenominator_pos primitive hβ
  have hrden : 0 < 1 - groundedSqrtPersistence p := sub_pos.mpr hr.2
  have hquotPos : 0 < j / (1 - groundedSqrtMultiplier p β) :=
    div_pos primitive.injection_pos hden
  have hupperPos : 0 < j / (1 - groundedSqrtPersistence p) :=
    div_pos primitive.injection_pos hrden
  have hlowerQuot : j ≤ j / (1 - groundedSqrtMultiplier p β) := by
    rw [le_div_iff₀ hden]
    nlinarith [primitive.injection_pos, hm.1]
  have hupperQuot : j / (1 - groundedSqrtMultiplier p β) ≤
      j / (1 - groundedSqrtPersistence p) := by
    exact (div_le_div_iff₀ hden hrden).2 <| by
      nlinarith [primitive.injection_pos, hm.2]
  constructor
  · simp only [groundedSqrtCharacteristic]
    exact (sq_le_sq₀ primitive.injection_pos.le hquotPos.le).2 hlowerQuot
  · simp only [groundedSqrtCharacteristic, groundedSqrtStockUpper]
    exact (sq_le_sq₀ hquotPos.le hupperPos.le).2 hupperQuot

/-- The characteristic is strictly increasing. -/
theorem groundedSqrtCharacteristic_strictMonoOn
    {p : LoopParams} {j : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j) :
    StrictMonoOn (groundedSqrtCharacteristic p j) (Icc (0 : ℝ) 1) := by
  intro β₁ hβ₁ β₂ hβ₂ hβ
  have hm := groundedSqrtMultiplier_strictMonoOn primitive hβ₁ hβ₂ hβ
  have hden₁ := groundedSqrtCharacteristicDenominator_pos primitive hβ₁
  have hden₂ := groundedSqrtCharacteristicDenominator_pos primitive hβ₂
  have hquot : j / (1 - groundedSqrtMultiplier p β₁) <
      j / (1 - groundedSqrtMultiplier p β₂) := by
    exact (div_lt_div_iff₀ hden₁ hden₂).2 <| by
      nlinarith [primitive.injection_pos]
  have hq₁ : 0 ≤ j / (1 - groundedSqrtMultiplier p β₁) :=
    (div_pos primitive.injection_pos hden₁).le
  have hq₂ : 0 ≤ j / (1 - groundedSqrtMultiplier p β₂) :=
    (div_pos primitive.injection_pos hden₂).le
  simp only [groundedSqrtCharacteristic]
  exact (sq_lt_sq₀ hq₁ hq₂).2 hquot

/-- The registered characteristic is an exact fixed stock for every policy
in `[0,1]`. -/
theorem groundedSqrtCharacteristic_fixed
    {p : LoopParams} {j β : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    (hβ : β ∈ Icc (0 : ℝ) 1) :
    groundedSqrtStockStep p j β (groundedSqrtCharacteristic p j β) =
      groundedSqrtCharacteristic p j β := by
  have hden : 0 < 1 - groundedSqrtMultiplier p β :=
    groundedSqrtCharacteristicDenominator_pos primitive hβ
  have hquot : 0 ≤ j / (1 - groundedSqrtMultiplier p β) :=
    (div_pos primitive.injection_pos hden).le
  have hsqrt : √(groundedSqrtCharacteristic p j β) =
      j / (1 - groundedSqrtMultiplier p β) := by
    simp only [groundedSqrtCharacteristic, Real.sqrt_sq hquot]
  have hidentity : groundedSqrtMultiplier p β *
        (j / (1 - groundedSqrtMultiplier p β)) + j =
      j / (1 - groundedSqrtMultiplier p β) := by
    field_simp [hden.ne']
    ring
  rw [groundedSqrtStockStep, hsqrt, hidentity]
  rfl

/-- In particular, the grounded full-deference characteristic is finite and
is exactly the registered stock ceiling. -/
theorem groundedSqrtCharacteristic_one
    (p : LoopParams) (j : ℝ) :
    groundedSqrtCharacteristic p j 1 = groundedSqrtStockUpper p j := by
  simp only [groundedSqrtCharacteristic, groundedSqrtStockUpper,
    groundedSqrtMultiplier]
  ring_nf

/-- The grounded nonlinear law packaged for the abstract robustness theorem. -/
def groundedSqrtStockLaw
    (p : LoopParams) (j : ℝ)
    (primitive : GroundedSqrtPrimitiveAssumptions p j) : NonlinearStockLaw where
  step := groundedSqrtStockStep p j
  characteristic := groundedSqrtCharacteristic p j
  stockLower := j ^ 2
  stockUpper := groundedSqrtStockUpper p j
  stockLower_le_stockUpper :=
    (groundedSqrtCharacteristic_mem primitive (show (1 : ℝ) ∈ Icc 0 1 by
      norm_num)).1.trans_eq (groundedSqrtCharacteristic_one p j)

@[simp] theorem groundedSqrtStockLaw_step
    {p : LoopParams} {j : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j) (β D : ℝ) :
    (groundedSqrtStockLaw p j primitive).step β D =
      groundedSqrtStockStep p j β D := rfl

@[simp] theorem groundedSqrtStockLaw_characteristic
    {p : LoopParams} {j : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j) (β : ℝ) :
    (groundedSqrtStockLaw p j primitive).characteristic β =
      groundedSqrtCharacteristic p j β := rfl

theorem sqrt_groundedSqrtStockUpper
    {p : LoopParams} {j : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j) :
    √(groundedSqrtStockUpper p j) =
      j / (1 - groundedSqrtPersistence p) := by
  have hden : 0 < 1 - groundedSqrtPersistence p :=
    sub_pos.mpr (groundedSqrtPersistence_pos_lt_one primitive).2
  simp only [groundedSqrtStockUpper,
    Real.sqrt_sq (div_pos primitive.injection_pos hden).le]

/-- The nonlinear stock coordinate maps its registered interval into itself. -/
theorem groundedSqrtStockStep_mem
    {p : LoopParams} {j β D : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    (hβ : β ∈ Icc (0 : ℝ) 1)
    (hD : D ∈ Icc (j ^ 2) (groundedSqrtStockUpper p j)) :
    groundedSqrtStockStep p j β D ∈
      Icc (j ^ 2) (groundedSqrtStockUpper p j) := by
  have hm := groundedSqrtMultiplier_pos_le primitive hβ
  have hr := groundedSqrtPersistence_pos_lt_one primitive
  have hden : 0 < 1 - groundedSqrtPersistence p := sub_pos.mpr hr.2
  let Q : ℝ := j / (1 - groundedSqrtPersistence p)
  have hQpos : 0 < Q := div_pos primitive.injection_pos hden
  have hDnonneg : 0 ≤ D := by
    exact (sq_nonneg j).trans hD.1
  have hrootUpper : √D ≤ Q := by
    calc
      √D ≤ √(groundedSqrtStockUpper p j) := Real.sqrt_le_sqrt hD.2
      _ = Q := by simpa only [Q] using sqrt_groundedSqrtStockUpper primitive
  have hinsideLower : j ≤ groundedSqrtMultiplier p β * √D + j := by
    exact le_add_of_nonneg_left
      (mul_nonneg hm.1.le (Real.sqrt_nonneg D))
  have hmulUpper : groundedSqrtMultiplier p β * √D ≤
      groundedSqrtPersistence p * Q :=
    mul_le_mul hm.2 hrootUpper (Real.sqrt_nonneg D) hr.1.le
  have hrootIdentity : groundedSqrtPersistence p * Q + j = Q := by
    dsimp only [Q]
    field_simp [hden.ne']
    ring
  have hinsideUpper : groundedSqrtMultiplier p β * √D + j ≤ Q := by
    calc
      groundedSqrtMultiplier p β * √D + j ≤
          groundedSqrtPersistence p * Q + j := by
        simpa only [add_comm] using add_le_add_right hmulUpper j
      _ = Q := hrootIdentity
  have hinsideNonneg : 0 ≤ groundedSqrtMultiplier p β * √D + j :=
    primitive.injection_pos.le.trans hinsideLower
  constructor
  · simp only [groundedSqrtStockStep]
    exact (sq_le_sq₀ primitive.injection_pos.le hinsideNonneg).2 hinsideLower
  · simp only [groundedSqrtStockStep, groundedSqrtStockUpper]
    exact (sq_le_sq₀ hinsideNonneg hQpos.le).2 hinsideUpper

/-- The full nonlinear loop maps the registered compact rectangle into
itself. -/
theorem groundedSqrtInvariantBox
    {p : LoopParams} {j : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j) :
    MapsTo (nonlinearLoopMap p (groundedSqrtStockLaw p j primitive))
      (nonlinearLoopBox (groundedSqrtStockLaw p j primitive))
      (nonlinearLoopBox (groundedSqrtStockLaw p j primitive)) := by
  intro x hx
  exact ⟨LoopParams.clipUnit_mem _, groundedSqrtStockStep_mem primitive hx.1 hx.2⟩

/-- The grounded nonlinear loop is continuous on the whole plane. -/
theorem continuous_groundedSqrtLoopMap
    (p : LoopParams) (j : ℝ)
    (primitive : GroundedSqrtPrimitiveAssumptions p j) :
    Continuous (nonlinearLoopMap p (groundedSqrtStockLaw p j primitive)) := by
  unfold nonlinearLoopMap LoopParams.deferenceStep LoopParams.gradU
    groundedSqrtStockLaw groundedSqrtStockStep groundedSqrtMultiplier
    groundedSqrtPersistence LoopParams.clipUnit
  fun_prop

/-- The quantitative ceiling condition needed for policy cooperativity. -/
structure GroundedSqrtSmallStepAssumption
    (p : LoopParams) (j : ℝ) : Prop where
  bound : 2 * p.α * p.c ^ 2 * groundedSqrtStockUpper p j ≤ 1

theorem groundedSqrt_unclipped_mono_policy
    {p : LoopParams} {j β₁ β₂ D : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    (small : GroundedSqrtSmallStepAssumption p j)
    (hβ : β₁ ≤ β₂)
    (hD : D ∈ Icc (j ^ 2) (groundedSqrtStockUpper p j)) :
    unclippedDeferenceInput p β₁ D ≤
      unclippedDeferenceInput p β₂ D := by
  have hk : 0 ≤ 2 * p.α * p.c ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) primitive.α_pos.le) (sq_nonneg p.c)
  have hkD : 2 * p.α * p.c ^ 2 * D ≤
      2 * p.α * p.c ^ 2 * groundedSqrtStockUpper p j :=
    mul_le_mul_of_nonneg_left hD.2 hk
  have hcoefficient : 0 ≤ 1 - 2 * p.α * p.c ^ 2 * D := by
    linarith [small.bound]
  have hdelta : 0 ≤ β₂ - β₁ := sub_nonneg.mpr hβ
  have hproduct := mul_nonneg hdelta hcoefficient
  simp only [unclippedDeferenceInput, LoopParams.gradU]
  nlinarith

theorem groundedSqrt_unclipped_mono_stock
    {p : LoopParams} {j β D₁ D₂ : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    (hβ : β ∈ Icc (0 : ℝ) 1) (hD : D₁ ≤ D₂) :
    unclippedDeferenceInput p β D₁ ≤
      unclippedDeferenceInput p β D₂ := by
  have hcβ : p.c * β ≤ p.c := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hβ.2 primitive.c_pos.le
  have hresidual : 0 ≤ 1 - p.c * β := by
    linarith [primitive.c_lt_one]
  have hcoefficient : 0 ≤ p.α * (2 * p.c * (1 - p.c * β)) :=
    mul_nonneg primitive.α_pos.le
      (mul_nonneg (mul_nonneg (by norm_num) primitive.c_pos.le) hresidual)
  have hproduct := mul_nonneg hcoefficient (sub_nonneg.mpr hD)
  simp only [unclippedDeferenceInput, LoopParams.gradU]
  nlinarith

/-- The nonlinear stock step is nondecreasing jointly in policy and stock on
the registered rectangle. -/
theorem groundedSqrtStockStep_mono
    {p : LoopParams} {j β₁ β₂ D₁ D₂ : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    (hβ₁ : β₁ ∈ Icc (0 : ℝ) 1)
    (hβ₂ : β₂ ∈ Icc (0 : ℝ) 1)
    (hβ : β₁ ≤ β₂) (hD : D₁ ≤ D₂) :
    groundedSqrtStockStep p j β₁ D₁ ≤
      groundedSqrtStockStep p j β₂ D₂ := by
  have hm₁ := groundedSqrtMultiplier_pos_le primitive hβ₁
  have hm₂ := groundedSqrtMultiplier_pos_le primitive hβ₂
  have hm : groundedSqrtMultiplier p β₁ ≤ groundedSqrtMultiplier p β₂ :=
    (groundedSqrtMultiplier_strictMonoOn primitive).monotoneOn hβ₁ hβ₂ hβ
  have hroot : √D₁ ≤ √D₂ := Real.sqrt_le_sqrt hD
  have hmul : groundedSqrtMultiplier p β₁ * √D₁ ≤
      groundedSqrtMultiplier p β₂ * √D₂ :=
    mul_le_mul hm hroot (Real.sqrt_nonneg D₁) hm₂.1.le
  have hinside : groundedSqrtMultiplier p β₁ * √D₁ + j ≤
      groundedSqrtMultiplier p β₂ * √D₂ + j :=
    by simpa only [add_comm] using add_le_add_right hmul j
  have hleftNonneg : 0 ≤ groundedSqrtMultiplier p β₁ * √D₁ + j :=
    add_nonneg (mul_nonneg hm₁.1.le (Real.sqrt_nonneg D₁))
      primitive.injection_pos.le
  have hrightNonneg : 0 ≤ groundedSqrtMultiplier p β₂ * √D₂ + j :=
    add_nonneg (mul_nonneg hm₂.1.le (Real.sqrt_nonneg D₂))
      primitive.injection_pos.le
  simp only [groundedSqrtStockStep]
  exact (sq_le_sq₀ hleftNonneg hrightNonneg).2 hinside

/-- The grounded nonlinear loop is cooperative on its invariant rectangle. -/
theorem groundedSqrtLoopMap_monotoneOn
    {p : LoopParams} {j : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    (small : GroundedSqrtSmallStepAssumption p j) :
    MonotoneOn (nonlinearLoopMap p (groundedSqrtStockLaw p j primitive))
      (nonlinearLoopBox (groundedSqrtStockLaw p j primitive)) := by
  intro x hx y hy hxy
  have hpolicyPolicy := groundedSqrt_unclipped_mono_policy primitive small
    hxy.1 hx.2
  have hpolicyStock := groundedSqrt_unclipped_mono_stock primitive hy.1 hxy.2
  have hpolicy : p.deferenceStep x.1 x.2 ≤ p.deferenceStep y.1 y.2 := by
    exact LoopParams.monotone_clipUnit (hpolicyPolicy.trans hpolicyStock)
  have hstock := groundedSqrtStockStep_mono primitive hx.1 hy.1
    hxy.1 hxy.2
  exact ⟨hpolicy, hstock⟩

/-- The grounded family supplies the abstract theorem's core hypotheses once
the explicit nonlinear small-step ceiling is imposed. -/
theorem groundedSqrtNonlinearCore
    {p : LoopParams} {j : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    (small : GroundedSqrtSmallStepAssumption p j) :
    NonlinearLoopCoreAssumptions p (groundedSqrtStockLaw p j primitive) :=
  ⟨groundedSqrtInvariantBox primitive,
    continuous_groundedSqrtLoopMap p j primitive,
    groundedSqrtLoopMap_monotoneOn primitive small⟩

/-! ## Quantitative orientation bounds -/

/-- Uniform policy diagonal for the grounded nonlinear rectangle. -/
def groundedPolicyDiagonalLower (p : LoopParams) (j : ℝ) : ℝ :=
  1 - 2 * p.α * p.c ^ 2 * groundedSqrtStockUpper p j

/-- Uniform stock-to-policy cross response. -/
def groundedPolicyStockUpper (p : LoopParams) : ℝ :=
  2 * p.α * p.c

/-- The positive square-root ceiling used in the nonlinear stock estimate. -/
def groundedSqrtStockRootUpper (p : LoopParams) (j : ℝ) : ℝ :=
  j / (1 - groundedSqrtPersistence p)

/-- Uniform policy-to-stock response for the grounded square-root law. -/
def groundedStockPolicyUpper (p : LoopParams) (j : ℝ) : ℝ :=
  2 * groundedSqrtPersistence p * p.η * groundedSqrtStockRootUpper p j *
    (groundedSqrtPersistence p * groundedSqrtStockRootUpper p j + j)

/-- Uniform positive stock diagonal for the grounded square-root law. -/
def groundedStockDiagonalLower (p : LoopParams) : ℝ :=
  (groundedSqrtMultiplier p 0) ^ 2

/-- The new nonlinear orientation condition.  Its first field is the exact
cooperativity ceiling; its second is strict diagonal-product dominance for
the explicit uniform constants above. -/
structure GroundedSqrtConvergentStepAssumption
    (p : LoopParams) (j : ℝ) : Prop where
  smallStep : GroundedSqrtSmallStepAssumption p j
  crossProduct_lt :
    groundedPolicyStockUpper p * groundedStockPolicyUpper p j <
      groundedPolicyDiagonalLower p j * groundedStockDiagonalLower p

theorem groundedPolicyStockUpper_pos
    {p : LoopParams} {j : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j) :
    0 < groundedPolicyStockUpper p := by
  simp only [groundedPolicyStockUpper]
  exact mul_pos (mul_pos two_pos primitive.α_pos) primitive.c_pos

theorem groundedStockDiagonalLower_pos
    {p : LoopParams} {j : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j) :
    0 < groundedStockDiagonalLower p := by
  simp only [groundedStockDiagonalLower]
  exact sq_pos_of_pos
    (groundedSqrtMultiplier_pos_le primitive (by norm_num)).1

/-- Lower policy-input estimate for a southeast increment on the nonlinear
rectangle. -/
theorem groundedSoutheast_policy_lower
    {p : LoopParams} {j : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    {x y : LoopState}
    (hx : x ∈ nonlinearLoopBox (groundedSqrtStockLaw p j primitive))
    (hy : y ∈ nonlinearLoopBox (groundedSqrtStockLaw p j primitive))
    (hβ : x.1 ≤ y.1) (hD : y.2 ≤ x.2) :
    groundedPolicyDiagonalLower p j * (y.1 - x.1) -
        groundedPolicyStockUpper p * (x.2 - y.2) ≤
      unclippedDeferenceInput p y.1 y.2 -
        unclippedDeferenceInput p x.1 x.2 := by
  have hk : 0 ≤ 2 * p.α * p.c ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) primitive.α_pos.le) (sq_nonneg p.c)
  have hyUpper : y.2 ≤ groundedSqrtStockUpper p j := hy.2.2
  have ha : groundedPolicyDiagonalLower p j ≤
      1 - 2 * p.α * p.c ^ 2 * y.2 := by
    simp only [groundedPolicyDiagonalLower]
    have := mul_le_mul_of_nonneg_left hyUpper hk
    linarith
  have hb : 2 * p.α * p.c * (1 - p.c * x.1) ≤
      groundedPolicyStockUpper p := by
    have hcx : 0 ≤ p.c * x.1 := mul_nonneg primitive.c_pos.le hx.1.1
    have hcoef : 0 ≤ 2 * p.α * p.c :=
      mul_nonneg (mul_nonneg (by norm_num) primitive.α_pos.le)
        primitive.c_pos.le
    simp only [groundedPolicyStockUpper]
    nlinarith [mul_le_mul_of_nonneg_left
      (show 1 - p.c * x.1 ≤ 1 by linarith) hcoef]
  have hap := mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hβ)
  have hbq := mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr hD)
  simp only [unclippedDeferenceInput, LoopParams.gradU]
  nlinarith

/-- Upper policy-input estimate for a northwest increment on the nonlinear
rectangle. -/
theorem groundedNorthwest_policy_upper
    {p : LoopParams} {j : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    {x y : LoopState}
    (hx : x ∈ nonlinearLoopBox (groundedSqrtStockLaw p j primitive))
    (hy : y ∈ nonlinearLoopBox (groundedSqrtStockLaw p j primitive))
    (hβ : y.1 ≤ x.1) (hD : x.2 ≤ y.2) :
    unclippedDeferenceInput p y.1 y.2 -
        unclippedDeferenceInput p x.1 x.2 ≤
      -groundedPolicyDiagonalLower p j * (x.1 - y.1) +
        groundedPolicyStockUpper p * (y.2 - x.2) := by
  have hk : 0 ≤ 2 * p.α * p.c ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) primitive.α_pos.le) (sq_nonneg p.c)
  have hyUpper : y.2 ≤ groundedSqrtStockUpper p j := hy.2.2
  have ha : groundedPolicyDiagonalLower p j ≤
      1 - 2 * p.α * p.c ^ 2 * y.2 := by
    simp only [groundedPolicyDiagonalLower]
    have := mul_le_mul_of_nonneg_left hyUpper hk
    linarith
  have hb : 2 * p.α * p.c * (1 - p.c * x.1) ≤
      groundedPolicyStockUpper p := by
    have hcx : 0 ≤ p.c * x.1 := mul_nonneg primitive.c_pos.le hx.1.1
    have hcoef : 0 ≤ 2 * p.α * p.c :=
      mul_nonneg (mul_nonneg (by norm_num) primitive.α_pos.le)
        primitive.c_pos.le
    simp only [groundedPolicyStockUpper]
    nlinarith [mul_le_mul_of_nonneg_left
      (show 1 - p.c * x.1 ≤ 1 by linarith) hcoef]
  have hap := mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hβ)
  have hbq := mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr hD)
  simp only [unclippedDeferenceInput, LoopParams.gradU]
  nlinarith

/-- Exact stock difference when only policy changes. -/
theorem groundedSqrtStockStep_policy_difference
    (p : LoopParams) (j β₁ β₂ D : ℝ) :
    groundedSqrtStockStep p j β₂ D - groundedSqrtStockStep p j β₁ D =
      (groundedSqrtMultiplier p β₂ - groundedSqrtMultiplier p β₁) * √D *
        ((groundedSqrtMultiplier p β₂ + groundedSqrtMultiplier p β₁) *
          √D + 2 * j) := by
  simp only [groundedSqrtStockStep]
  ring

/-- Exact stock difference when only the prior stock changes. -/
theorem groundedSqrtStockStep_stock_difference
    (p : LoopParams) (j β D₁ D₂ : ℝ)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) :
    groundedSqrtStockStep p j β D₂ - groundedSqrtStockStep p j β D₁ =
      (groundedSqrtMultiplier p β) ^ 2 * (D₂ - D₁) +
        2 * groundedSqrtMultiplier p β * j * (√D₂ - √D₁) := by
  have hsqrt₁ := Real.sq_sqrt hD₁
  have hsqrt₂ := Real.sq_sqrt hD₂
  simp only [groundedSqrtStockStep]
  nlinarith

/-- Uniform upper bound on the nonlinear stock change due to policy alone. -/
theorem groundedSqrtStockStep_policy_difference_upper
    {p : LoopParams} {j β₁ β₂ D : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    (hβ₁ : β₁ ∈ Icc (0 : ℝ) 1)
    (hβ₂ : β₂ ∈ Icc (0 : ℝ) 1)
    (hβ : β₁ ≤ β₂)
    (hD : D ∈ Icc (j ^ 2) (groundedSqrtStockUpper p j)) :
    groundedSqrtStockStep p j β₂ D - groundedSqrtStockStep p j β₁ D ≤
      groundedStockPolicyUpper p j * (β₂ - β₁) := by
  let r := groundedSqrtPersistence p
  let Q := groundedSqrtStockRootUpper p j
  let m₁ := groundedSqrtMultiplier p β₁
  let m₂ := groundedSqrtMultiplier p β₂
  have hr := groundedSqrtPersistence_pos_lt_one primitive
  have hm₁ := groundedSqrtMultiplier_pos_le primitive hβ₁
  have hm₂ := groundedSqrtMultiplier_pos_le primitive hβ₂
  have hQpos : 0 < Q := by
    dsimp only [Q, groundedSqrtStockRootUpper]
    exact div_pos primitive.injection_pos (sub_pos.mpr hr.2)
  have hDnonneg : 0 ≤ D := (sq_nonneg j).trans hD.1
  have hroot : √D ≤ Q := by
    calc
      √D ≤ √(groundedSqrtStockUpper p j) := Real.sqrt_le_sqrt hD.2
      _ = Q := by
        simpa only [Q, groundedSqrtStockRootUpper] using
          sqrt_groundedSqrtStockUpper primitive
  have hdelta : 0 ≤ β₂ - β₁ := sub_nonneg.mpr hβ
  have hrnonneg : 0 ≤ r := by
    dsimp only [r]
    exact hr.1.le
  have hA : m₂ - m₁ = r * p.η * (β₂ - β₁) := by
    simpa only [m₁, m₂, r] using groundedSqrtMultiplier_sub p β₁ β₂
  have hAnonneg : 0 ≤ m₂ - m₁ := by
    rw [hA]
    exact mul_nonneg (mul_nonneg hrnonneg primitive.η_pos.le) hdelta
  have hsum : m₂ + m₁ ≤ 2 * r := by
    dsimp only [m₁, m₂, r]
    linarith [hm₁.2, hm₂.2]
  have hsumNonneg : 0 ≤ m₂ + m₁ := by
    dsimp only [m₁, m₂]
    linarith [hm₁.1, hm₂.1]
  have hsumRoot : (m₂ + m₁) * √D ≤ 2 * r * Q :=
    mul_le_mul hsum hroot (Real.sqrt_nonneg D)
      (mul_nonneg (by norm_num) hrnonneg)
  have hbracket : (m₂ + m₁) * √D + 2 * j ≤
      2 * r * Q + 2 * j := by
    simpa only [add_comm] using add_le_add_right hsumRoot (2 * j)
  have hbracketNonneg : 0 ≤ (m₂ + m₁) * √D + 2 * j :=
    add_nonneg (mul_nonneg hsumNonneg (Real.sqrt_nonneg D))
      (mul_nonneg (by norm_num) primitive.injection_pos.le)
  have hbracketUpperNonneg : 0 ≤ 2 * r * Q + 2 * j :=
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hrnonneg) hQpos.le)
      (mul_nonneg (by norm_num) primitive.injection_pos.le)
  have hAroot : (m₂ - m₁) * √D ≤ (m₂ - m₁) * Q :=
    mul_le_mul_of_nonneg_left hroot hAnonneg
  have hproduct :
      (m₂ - m₁) * √D * ((m₂ + m₁) * √D + 2 * j) ≤
        (m₂ - m₁) * Q * (2 * r * Q + 2 * j) :=
    mul_le_mul hAroot hbracket hbracketNonneg
      (mul_nonneg hAnonneg hQpos.le)
  rw [groundedSqrtStockStep_policy_difference]
  calc
    (m₂ - m₁) * √D * ((m₂ + m₁) * √D + 2 * j) ≤
        (m₂ - m₁) * Q * (2 * r * Q + 2 * j) := hproduct
    _ = groundedStockPolicyUpper p j * (β₂ - β₁) := by
      rw [hA]
      change (r * p.η * (β₂ - β₁)) * Q * (2 * r * Q + 2 * j) =
        (2 * r * p.η * Q * (r * Q + j)) * (β₂ - β₁)
      ring

/-- Uniform positive diagonal response to stock alone. -/
theorem groundedSqrtStockStep_stock_difference_lower
    {p : LoopParams} {j β D₁ D₂ : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    (hβ : β ∈ Icc (0 : ℝ) 1)
    (hD₁ : D₁ ∈ Icc (j ^ 2) (groundedSqrtStockUpper p j))
    (hD₂ : D₂ ∈ Icc (j ^ 2) (groundedSqrtStockUpper p j))
    (hD : D₁ ≤ D₂) :
    groundedStockDiagonalLower p * (D₂ - D₁) ≤
      groundedSqrtStockStep p j β D₂ - groundedSqrtStockStep p j β D₁ := by
  have hD₁nonneg : 0 ≤ D₁ := (sq_nonneg j).trans hD₁.1
  have hD₂nonneg : 0 ≤ D₂ := (sq_nonneg j).trans hD₂.1
  have hroot : √D₁ ≤ √D₂ := Real.sqrt_le_sqrt hD
  have hm := groundedSqrtMultiplier_pos_le primitive hβ
  have hm₀ := groundedSqrtMultiplier_pos_le primitive (show (0 : ℝ) ∈ Icc 0 1 by
    norm_num)
  have hm₀le : groundedSqrtMultiplier p 0 ≤ groundedSqrtMultiplier p β :=
    (groundedSqrtMultiplier_strictMonoOn primitive).monotoneOn
      (by norm_num) hβ hβ.1
  have hsq : (groundedSqrtMultiplier p 0) ^ 2 ≤
      (groundedSqrtMultiplier p β) ^ 2 :=
    (sq_le_sq₀ hm₀.1.le hm.1.le).2 hm₀le
  have hdiag := mul_le_mul_of_nonneg_right hsq (sub_nonneg.mpr hD)
  have hextra : 0 ≤ 2 * groundedSqrtMultiplier p β * j * (√D₂ - √D₁) := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hm.1.le) primitive.injection_pos.le)
      (sub_nonneg.mpr hroot)
  rw [groundedSqrtStockStep_stock_difference p j β D₁ D₂
    hD₁nonneg hD₂nonneg]
  simp only [groundedStockDiagonalLower]
  linarith

/-- Upper nonlinear stock estimate for a southeast increment. -/
theorem groundedSoutheast_stock_upper
    {p : LoopParams} {j : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    {x y : LoopState}
    (hx : x ∈ nonlinearLoopBox (groundedSqrtStockLaw p j primitive))
    (hy : y ∈ nonlinearLoopBox (groundedSqrtStockLaw p j primitive))
    (hβ : x.1 ≤ y.1) (hD : y.2 ≤ x.2) :
    groundedSqrtStockStep p j y.1 y.2 - groundedSqrtStockStep p j x.1 x.2 ≤
      groundedStockPolicyUpper p j * (y.1 - x.1) -
        groundedStockDiagonalLower p * (x.2 - y.2) := by
  have hpolicy := groundedSqrtStockStep_policy_difference_upper primitive
    hx.1 hy.1 hβ hy.2
  have hdiagonal := groundedSqrtStockStep_stock_difference_lower primitive
    hx.1 hy.2 hx.2 hD
  linarith

/-- Lower nonlinear stock estimate for a northwest increment. -/
theorem groundedNorthwest_stock_lower
    {p : LoopParams} {j : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    {x y : LoopState}
    (hx : x ∈ nonlinearLoopBox (groundedSqrtStockLaw p j primitive))
    (hy : y ∈ nonlinearLoopBox (groundedSqrtStockLaw p j primitive))
    (hβ : y.1 ≤ x.1) (hD : x.2 ≤ y.2) :
    -groundedStockPolicyUpper p j * (x.1 - y.1) +
        groundedStockDiagonalLower p * (y.2 - x.2) ≤
      groundedSqrtStockStep p j y.1 y.2 - groundedSqrtStockStep p j x.1 x.2 := by
  have hpolicy := groundedSqrtStockStep_policy_difference_upper primitive
    hy.1 hx.1 hβ hx.2
  have hdiagonal := groundedSqrtStockStep_stock_difference_lower primitive
    hy.1 hx.2 hy.2 hD
  linarith

/-- The grounded family supplies all four abstract cross bounds from the
explicit nonlinear orientation inequality. -/
def groundedSqrtNonlinearCrossBounds
    {p : LoopParams} {j : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    (convergent : GroundedSqrtConvergentStepAssumption p j) :
    NonlinearCrossBounds p (groundedSqrtStockLaw p j primitive) where
  policyDiagonalLower := groundedPolicyDiagonalLower p j
  policyStockUpper := groundedPolicyStockUpper p
  stockPolicyUpper := groundedStockPolicyUpper p j
  stockDiagonalLower := groundedStockDiagonalLower p
  policyStockUpper_pos := groundedPolicyStockUpper_pos primitive
  stockDiagonalLower_pos := groundedStockDiagonalLower_pos primitive
  crossProduct_lt := convergent.crossProduct_lt
  southeast_policy_lower := by
    intro x y hx hy hβ hD
    exact groundedSoutheast_policy_lower primitive hx hy hβ hD
  southeast_stock_upper := by
    intro x y hx hy hβ hD
    exact groundedSoutheast_stock_upper primitive hx hy hβ hD
  northwest_policy_upper := by
    intro x y hx hy hβ hD
    exact groundedNorthwest_policy_upper primitive hx hy hβ hD
  northwest_stock_lower := by
    intro x y hx hy hβ hD
    exact groundedNorthwest_stock_lower primitive hx hy hβ hD

/-! ## Algebraic equilibrium catalogue -/

/-- Satisfaction gradient restricted to the grounded nonlinear
characteristic. -/
def groundedSqrtReducedGradient (p : LoopParams) (j β : ℝ) : ℝ :=
  p.gradU β (groundedSqrtCharacteristic p j β)

/-- Oriented unique crossing for the grounded nonlinear characteristic.  This
is algebraic fixed-point information, not a convergence or basin assumption. -/
structure GroundedSqrtThresholdAssumption
    (p : LoopParams) (j : ℝ) where
  βdagger : ℝ
  βdagger_mem : βdagger ∈ Ioo (0 : ℝ) 1
  reduced_zero : groundedSqrtReducedGradient p j βdagger = 0
  reduced_zero_neg : groundedSqrtReducedGradient p j 0 < 0
  reduced_one_pos : 0 < groundedSqrtReducedGradient p j 1
  reduced_neg_before : ∀ β ∈ Ioo (0 : ℝ) 1, β < βdagger →
    groundedSqrtReducedGradient p j β < 0
  reduced_pos_after : ∀ β ∈ Ioo (0 : ℝ) 1, βdagger < β →
    0 < groundedSqrtReducedGradient p j β

/-- Inside the registered rectangle, the nonlinear stock fixed-point equation
has the registered characteristic as its unique solution. -/
theorem groundedSqrtStock_fixed_iff_characteristic
    {p : LoopParams} {j β D : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    (hβ : β ∈ Icc (0 : ℝ) 1)
    (hD : D ∈ Icc (j ^ 2) (groundedSqrtStockUpper p j)) :
    groundedSqrtStockStep p j β D = D ↔
      D = groundedSqrtCharacteristic p j β := by
  constructor
  · intro hfixed
    have hm := groundedSqrtMultiplier_pos_le primitive hβ
    have hden : 0 < 1 - groundedSqrtMultiplier p β :=
      groundedSqrtCharacteristicDenominator_pos primitive hβ
    have hDnonneg : 0 ≤ D := (sq_nonneg j).trans hD.1
    have hinsidePos : 0 < groundedSqrtMultiplier p β * √D + j :=
      add_pos_of_nonneg_of_pos
        (mul_nonneg hm.1.le (Real.sqrt_nonneg D)) primitive.injection_pos
    have hrootEquation : √D = groundedSqrtMultiplier p β * √D + j := by
      calc
        √D = √(groundedSqrtStockStep p j β D) := by rw [hfixed]
        _ = groundedSqrtMultiplier p β * √D + j := by
          simp only [groundedSqrtStockStep, Real.sqrt_sq_eq_abs,
            abs_of_pos hinsidePos]
    have hroot : √D = j / (1 - groundedSqrtMultiplier p β) := by
      apply (eq_div_iff hden.ne').2
      nlinarith [hrootEquation]
    rw [← Real.sq_sqrt hDnonneg, hroot]
    rfl
  · rintro rfl
    exact groundedSqrtCharacteristic_fixed primitive hβ

theorem groundedSqrt_calibrated_fixed
    {p : LoopParams} {j : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    (threshold : GroundedSqrtThresholdAssumption p j) :
    IsNonlinearLoopEquilibrium p (groundedSqrtStockLaw p j primitive)
      (0, groundedSqrtCharacteristic p j 0) := by
  change (p.deferenceStep 0 (groundedSqrtCharacteristic p j 0),
      groundedSqrtStockStep p j 0 (groundedSqrtCharacteristic p j 0)) =
    (0, groundedSqrtCharacteristic p j 0)
  apply Prod.ext
  · simp only [LoopParams.deferenceStep]
    rw [clipUnit_eq_zero_iff]
    have hnegative : p.α * p.gradU 0 (groundedSqrtCharacteristic p j 0) < 0 :=
      mul_neg_of_pos_of_neg primitive.α_pos threshold.reduced_zero_neg
    simpa only [groundedSqrtReducedGradient, zero_add] using hnegative.le
  · exact groundedSqrtCharacteristic_fixed primitive (by norm_num)

theorem groundedSqrt_saddle_fixed
    {p : LoopParams} {j : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    (threshold : GroundedSqrtThresholdAssumption p j) :
    IsNonlinearLoopEquilibrium p (groundedSqrtStockLaw p j primitive)
      (threshold.βdagger,
        groundedSqrtCharacteristic p j threshold.βdagger) := by
  have hβ : threshold.βdagger ∈ Icc (0 : ℝ) 1 :=
    ⟨threshold.βdagger_mem.1.le, threshold.βdagger_mem.2.le⟩
  change (p.deferenceStep threshold.βdagger
      (groundedSqrtCharacteristic p j threshold.βdagger),
      groundedSqrtStockStep p j threshold.βdagger
        (groundedSqrtCharacteristic p j threshold.βdagger)) =
    (threshold.βdagger,
      groundedSqrtCharacteristic p j threshold.βdagger)
  apply Prod.ext
  · have hgrad : p.gradU threshold.βdagger
        (groundedSqrtCharacteristic p j threshold.βdagger) = 0 := by
      simpa only [groundedSqrtReducedGradient] using threshold.reduced_zero
    simp only [LoopParams.deferenceStep, hgrad, mul_zero, add_zero]
    exact clipUnit_eq_self hβ
  · exact groundedSqrtCharacteristic_fixed primitive hβ

theorem groundedSqrt_captured_fixed
    {p : LoopParams} {j : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    (threshold : GroundedSqrtThresholdAssumption p j) :
    IsNonlinearLoopEquilibrium p (groundedSqrtStockLaw p j primitive)
      (1, groundedSqrtCharacteristic p j 1) := by
  change (p.deferenceStep 1 (groundedSqrtCharacteristic p j 1),
      groundedSqrtStockStep p j 1 (groundedSqrtCharacteristic p j 1)) =
    (1, groundedSqrtCharacteristic p j 1)
  apply Prod.ext
  · simp only [LoopParams.deferenceStep]
    rw [clipUnit_eq_one_iff]
    have hpositive : 0 < p.α * p.gradU 1 (groundedSqrtCharacteristic p j 1) :=
      mul_pos primitive.α_pos threshold.reduced_one_pos
    simpa only [groundedSqrtReducedGradient] using
      (show (1 : ℝ) ≤ 1 + p.α * p.gradU 1
        (groundedSqrtCharacteristic p j 1) by linarith)
  · exact groundedSqrtCharacteristic_fixed primitive (by norm_num)

/-- The grounded nonlinear loop has exactly its two endpoint equilibria and
the oriented interior crossing inside the registered rectangle. -/
theorem groundedSqrtEquilibrium_iff_three_points
    {p : LoopParams} {j β D : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    (threshold : GroundedSqrtThresholdAssumption p j)
    (hmem : (β, D) ∈ nonlinearLoopBox (groundedSqrtStockLaw p j primitive)) :
    IsNonlinearLoopEquilibrium p (groundedSqrtStockLaw p j primitive) (β, D) ↔
      (β = 0 ∧ D = groundedSqrtCharacteristic p j 0) ∨
      (β = threshold.βdagger ∧
        D = groundedSqrtCharacteristic p j threshold.βdagger) ∨
      (β = 1 ∧ D = groundedSqrtCharacteristic p j 1) := by
  constructor
  · intro hequilibrium
    change (p.deferenceStep β D, groundedSqrtStockStep p j β D) = (β, D) at hequilibrium
    have hpolicy := congrArg Prod.fst hequilibrium
    have hstock := congrArg Prod.snd hequilibrium
    simp only at hpolicy hstock
    have hDchar : D = groundedSqrtCharacteristic p j β :=
      (groundedSqrtStock_fixed_iff_characteristic primitive hmem.1 hmem.2).1 hstock
    by_cases hzero : β = 0
    · exact Or.inl ⟨hzero, hzero ▸ hDchar⟩
    by_cases hone : β = 1
    · exact Or.inr (Or.inr ⟨hone, hone ▸ hDchar⟩)
    have hβint : β ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hmem.1.1 (Ne.symm hzero),
        lt_of_le_of_ne hmem.1.2 hone⟩
    have hinput : β + p.α * p.gradU β D = β := by
      exact (clipUnit_eq_interior_iff hβint).1 <| by
        simpa only [LoopParams.deferenceStep] using hpolicy
    have hgrad : p.gradU β D = 0 := by
      nlinarith [primitive.α_pos]
    have hreduced : groundedSqrtReducedGradient p j β = 0 := by
      simp only [groundedSqrtReducedGradient, ← hDchar]
      exact hgrad
    have hdagger : β = threshold.βdagger := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hbefore | hafter
      · have := threshold.reduced_neg_before β hβint hbefore
        linarith
      · have := threshold.reduced_pos_after β hβint hafter
        linarith
    exact Or.inr (Or.inl ⟨hdagger, hdagger ▸ hDchar⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact groundedSqrt_calibrated_fixed primitive threshold
    · exact groundedSqrt_saddle_fixed primitive threshold
    · exact groundedSqrt_captured_fixed primitive threshold

/-- Concrete algebraic catalogue for the grounded nonlinear family. -/
def groundedSqrtEquilibriumCatalogue
    {p : LoopParams} {j : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    (threshold : GroundedSqrtThresholdAssumption p j) :
    NonlinearEquilibriumCatalogue p (groundedSqrtStockLaw p j primitive) where
  βdagger := threshold.βdagger
  βdagger_mem := threshold.βdagger_mem
  calibrated_mem := by
    change (0, groundedSqrtCharacteristic p j 0) ∈
      nonlinearLoopBox (groundedSqrtStockLaw p j primitive)
    exact ⟨by norm_num, groundedSqrtCharacteristic_mem primitive (by norm_num)⟩
  saddle_mem := by
    have hβ : threshold.βdagger ∈ Icc (0 : ℝ) 1 :=
      ⟨threshold.βdagger_mem.1.le, threshold.βdagger_mem.2.le⟩
    exact ⟨hβ, groundedSqrtCharacteristic_mem primitive hβ⟩
  captured_mem := by
    change (1, groundedSqrtCharacteristic p j 1) ∈
      nonlinearLoopBox (groundedSqrtStockLaw p j primitive)
    exact ⟨by norm_num, groundedSqrtCharacteristic_mem primitive (by norm_num)⟩
  exactly_three := by
    rintro ⟨β, D⟩ hmem
    simpa only [nonlinearCalibratedPoint, nonlinearSaddlePoint,
      nonlinearCapturedPoint, groundedSqrtStockLaw_characteristic,
      Prod.mk.injEq] using
      groundedSqrtEquilibrium_iff_three_points primitive threshold hmem
  characteristic_strictMono := groundedSqrtCharacteristic_strictMonoOn primitive

/-- Full global-bistability theorem for the grounded nonlinear square-root
stock law.  Every new assumption is explicit: primitive grounding, the
quantitative orientation bound, and the oriented algebraic crossing. -/
theorem groundedSqrt_global_bistability
    {p : LoopParams} {j : ℝ}
    (primitive : GroundedSqrtPrimitiveAssumptions p j)
    (convergent : GroundedSqrtConvergentStepAssumption p j)
    (threshold : GroundedSqrtThresholdAssumption p j) :
    NonlinearGlobalBistabilityConclusions p
      (groundedSqrtStockLaw p j primitive)
      (groundedSqrtEquilibriumCatalogue primitive threshold) :=
  nonlinear_global_bistability
    (groundedSqrtNonlinearCore primitive convergent.smallStep)
    (groundedSqrtNonlinearCrossBounds primitive convergent)
    (groundedSqrtEquilibriumCatalogue primitive threshold)

#print axioms groundedSqrtCharacteristic_fixed
#print axioms groundedSqrtCharacteristic_strictMonoOn
#print axioms groundedSqrtInvariantBox
#print axioms groundedSqrtNonlinearCore
#print axioms groundedSqrtNonlinearCrossBounds
#print axioms groundedSqrtStock_fixed_iff_characteristic
#print axioms groundedSqrtEquilibrium_iff_three_points
#print axioms groundedSqrt_global_bistability

end


end CivicAlignment.PaperII
