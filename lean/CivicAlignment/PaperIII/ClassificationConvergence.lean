/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.Convergence
import CivicAlignment.PaperIII.Classification

/-!
# Paper III: global convergence under `(SS_g^+)`

This file ports the self-contained quadrant argument from Paper II to the
content-gain loop.  It proves convergence for every orbit starting in the
paper's invariant box `B`; it does not invoke the inapplicable Smith theorem.
-/

namespace CivicAlignment.PaperIII

open Filter Function Set Topology

noncomputable section

/-! ## Invariant box, convergent step, and uniform coefficients -/

/-- Paper III's original invariant box `B`. -/
def classificationBox (p : LoopParams) : Set LoopState :=
  Icc (0 : ℝ) 1 ×ˢ Icc p.I (stockCeiling p)

/-- Denominator of the displayed `(SS_g^+)` threshold. -/
def convergentStepDenominator (p : LoopParams) : ℝ :=
  2 * p.c * p.I *
    (p.c * (p.s 0 + p.g) + 2 * p.η * (1 - p.lambda₀))

/-- Paper III, Assumption `(SS_g^+)`, `civic_loops.tex:123`. -/
structure ConvergentStepAssumption (p : LoopParams) : Prop where
  bound : p.α <
    (p.lambda₀ - p.g) * (p.s 0 + p.g) / convergentStepDenominator p

def policyDiagonalLower (p : LoopParams) : ℝ :=
  1 - 2 * p.α * p.c ^ 2 * stockCeiling p

def policyStockUpper (p : LoopParams) : ℝ :=
  2 * p.α * p.c

def stockPolicyUpper (p : LoopParams) : ℝ :=
  2 * p.η * (1 - p.lambda₀) * stockCeiling p

def stockDiagonalLower (p : LoopParams) : ℝ :=
  p.s 0 + p.g

/-! ### Ceiling-parameterized box and extrema

The convergence argument below uses the box ceiling only through the bound
`D ≤ M` and the two extrema it determines.  Parameterizing the ceiling lets the
same argument run on the `ε`-inflated box of `InflatedBox.lean`, which is what
extends `thm:classify` from `B` to arbitrary nonnegative stock. -/

/-- Paper III's invariant box with a general upper face. -/
def boxAt (p : LoopParams) (M : ℝ) : Set LoopState :=
  Icc (0 : ℝ) 1 ×ˢ Icc p.I M

/-- Ceiling-parameterized diagonal entry of the policy row. -/
def policyDiagonalLowerAt (p : LoopParams) (M : ℝ) : ℝ :=
  1 - 2 * p.α * p.c ^ 2 * M

/-- Ceiling-parameterized off-diagonal entry of the stock row. -/
def stockPolicyUpperAt (p : LoopParams) (M : ℝ) : ℝ :=
  2 * p.η * (1 - p.lambda₀) * M

@[simp] theorem boxAt_stockCeiling (p : LoopParams) :
    boxAt p (stockCeiling p) = classificationBox p := rfl

@[simp] theorem policyDiagonalLowerAt_stockCeiling (p : LoopParams) :
    policyDiagonalLowerAt p (stockCeiling p) = policyDiagonalLower p := rfl

@[simp] theorem stockPolicyUpperAt_stockCeiling (p : LoopParams) :
    stockPolicyUpperAt p (stockCeiling p) = stockPolicyUpper p := rfl

/--
Everything the convergence argument needs of a candidate ceiling: it dominates
the stationary ceiling (so the box is invariant), it keeps the policy diagonal
positive (cooperativity), and it carries strict diagonal-product dominance.
-/
structure CooperativeCeiling (p : LoopParams) (M : ℝ) : Prop where
  ceiling_le : stockCeiling p ≤ M
  diagonal_nonneg : 0 ≤ policyDiagonalLowerAt p M

/-- The comparable-step principle needs only cooperativity, so `StrictStepSize`
suffices at the printed ceiling: no orientation, injectivity, or dominance. -/
theorem StrictStepSize.toCooperativeCeiling {p : LoopParams}
    (_model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (ss : StrictStepSize p) : CooperativeCeiling p (stockCeiling p) := by
  have hgap := sub_pos.mpr hgain
  refine ⟨le_rfl, ?_⟩
  have hratio : 2 * p.α * p.c ^ 2 * stockCeiling p < 1 := by
    simp only [stockCeiling]
    rw [show 2 * p.α * p.c ^ 2 * (p.I / (p.lambda₀ - p.g)) =
      (2 * p.α * p.c ^ 2 * p.I) / (p.lambda₀ - p.g) by ring]
    exact (div_lt_one hgap).2 ss.bound
  simp only [policyDiagonalLowerAt]
  linarith

/-- Cooperativity plus strict diagonal-product dominance: what the
quadrant-exclusion half of `thm:classify` needs. -/
structure CeilingAssumption (p : LoopParams) (M : ℝ) : Prop extends
    CooperativeCeiling p M where
  dominance : policyStockUpper p * stockPolicyUpperAt p M <
    policyDiagonalLowerAt p M * stockDiagonalLower p

/-- Paper III, `thm:classify`, invariance of the original box `B`,
`civic_loops.tex:143--145`. -/
theorem boxAt_invariant {p : LoopParams} {M : ℝ}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀) (hM : stockCeiling p ≤ M) :
    MapsTo p.loopMap (boxAt p M) (boxAt p M) := by
  intro x hx
  have hβ := hx.1
  have hD := hx.2
  have hs := stockMultiplier_nonneg_le model hβ
  have hDnonneg : 0 ≤ x.2 := model.I_pos.le.trans hD.1
  have hmult_nonneg : 0 ≤ p.s x.1 + p.g := add_nonneg hs.1 model.g_nonneg
  have hmult_upper : p.s x.1 + p.g ≤ 1 - p.lambda₀ + p.g := by linarith
  have hgap : 0 < p.lambda₀ - p.g := sub_pos.mpr hgain
  have hR : stockCeiling p * (p.lambda₀ - p.g) = p.I := by
    rw [stockCeiling]; field_simp
  refine ⟨LoopParams.clipUnit_mem _, ?_, ?_⟩
  · simp only [LoopParams.loopMap, LoopParams.stockStep]
    exact le_add_of_nonneg_left (mul_nonneg hmult_nonneg hDnonneg)
  · simp only [LoopParams.loopMap, LoopParams.stockStep]
    have hproduct : (p.s x.1 + p.g) * x.2 ≤ (1 - p.lambda₀ + p.g) * M :=
      mul_le_mul hmult_upper hD.2 hDnonneg
        (by linarith [model.lambda₀_lt_one, model.g_nonneg])
    have hIle : p.I ≤ M * (p.lambda₀ - p.g) := by nlinarith [hM, hgap, hR]
    linarith

theorem classificationBox_invariant {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀) :
    MapsTo p.loopMap (classificationBox p) (classificationBox p) := by
  intro x hx
  have hβ := hx.1
  have hD := hx.2
  have hs := stockMultiplier_nonneg_le model hβ
  have hDnonneg : 0 ≤ x.2 := model.I_pos.le.trans hD.1
  have hmult_nonneg : 0 ≤ p.s x.1 + p.g := add_nonneg hs.1 model.g_nonneg
  have hmult_upper : p.s x.1 + p.g ≤ 1 - p.lambda₀ + p.g := by linarith
  have hgap : 0 < p.lambda₀ - p.g := sub_pos.mpr hgain
  have hceiling : (1 - p.lambda₀ + p.g) * stockCeiling p + p.I =
      stockCeiling p := by
    simp only [stockCeiling]
    field_simp [hgap.ne']
    ring
  refine ⟨LoopParams.clipUnit_mem _, ?_, ?_⟩
  · simp only [LoopParams.loopMap, LoopParams.stockStep]
    exact le_add_of_nonneg_left (mul_nonneg hmult_nonneg hDnonneg)
  · simp only [LoopParams.loopMap, LoopParams.stockStep]
    have hproduct : (p.s x.1 + p.g) * x.2 ≤
        (1 - p.lambda₀ + p.g) * stockCeiling p :=
      mul_le_mul hmult_upper hD.2 hDnonneg
        (by linarith [model.lambda₀_lt_one, model.g_nonneg])
    linarith

/-- Positivity of the least stock diagonal used by `(SS_g^+)`;
auxiliary to `thm:classify`, `civic_loops.tex:134--179`. -/
theorem stockDiagonalLower_pos {p : LoopParams}
    (model : LoopModelAssumptions p) : 0 < stockDiagonalLower p := by
  have hs0 : 0 < p.s 0 := by
    simp only [LoopParams.s, sub_zero, mul_one]
    exact mul_pos (sub_pos.mpr model.lambda₀_lt_one)
      (sq_pos_of_pos (sub_pos.mpr model.η_lt_one))
  simp only [stockDiagonalLower]
  linarith [model.g_nonneg]

/-- Positivity of Paper III's displayed convergent-step denominator;
auxiliary to `thm:classify`, `civic_loops.tex:130--179`. -/
theorem convergentStepDenominator_pos {p : LoopParams}
    (model : LoopModelAssumptions p) : 0 < convergentStepDenominator p := by
  have hd := stockDiagonalLower_pos model
  have htail : 0 < 2 * p.η * (1 - p.lambda₀) :=
    mul_pos (mul_pos two_pos model.η_pos) (sub_pos.mpr model.lambda₀_lt_one)
  have hbracket :
      0 < p.c * (p.s 0 + p.g) + 2 * p.η * (1 - p.lambda₀) :=
    add_pos_of_pos_of_nonneg (mul_pos model.c_pos hd) htail.le
  simp only [convergentStepDenominator]
  exact mul_pos (mul_pos (mul_pos two_pos model.c_pos) model.I_pos) hbracket

/-- `(SS_g^+)` implies the strict cooperative step bound `(SS_g)`;
auxiliary to `thm:classify`, `civic_loops.tex:130--174`. -/
theorem ConvergentStepAssumption.toStrictStepSize {p : LoopParams}
    (model : LoopModelAssumptions p) (_hgain : p.g < p.lambda₀)
    (ssplus : ConvergentStepAssumption p) : StrictStepSize p := by
  have hd := stockDiagonalLower_pos model
  have hden := convergentStepDenominator_pos model
  have hbound : p.α * convergentStepDenominator p <
      (p.lambda₀ - p.g) * (p.s 0 + p.g) :=
    (lt_div_iff₀ hden).mp ssplus.bound
  have htail : 0 < 2 * p.η * (1 - p.lambda₀) :=
    mul_pos (mul_pos two_pos model.η_pos) (sub_pos.mpr model.lambda₀_lt_one)
  have hbase : 0 < 2 * p.c * p.I := mul_pos (mul_pos two_pos model.c_pos) model.I_pos
  have hdenCore : 2 * p.c * p.I * (p.c * (p.s 0 + p.g)) <
      convergentStepDenominator p := by
    simp only [convergentStepDenominator]
    exact mul_lt_mul_of_pos_left (lt_add_of_pos_right _ htail) hbase
  have hcore :
      (2 * p.α * p.c ^ 2 * p.I) * (p.s 0 + p.g) <
        (p.lambda₀ - p.g) * (p.s 0 + p.g) := by
    calc
      (2 * p.α * p.c ^ 2 * p.I) * (p.s 0 + p.g) =
          p.α * (2 * p.c * p.I * (p.c * (p.s 0 + p.g))) := by ring
      _ < p.α * convergentStepDenominator p :=
        mul_lt_mul_of_pos_left hdenCore model.α_pos
      _ < (p.lambda₀ - p.g) * (p.s 0 + p.g) := hbound
  exact ⟨(mul_lt_mul_iff_left₀ hd).mp hcore⟩

/-- `(SS_g^+)` leaves a strictly positive uniform policy diagonal;
auxiliary to `thm:classify`, `civic_loops.tex:134--179`. -/
theorem ConvergentStepAssumption.policyDiagonalLower_pos {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (ssplus : ConvergentStepAssumption p) : 0 < policyDiagonalLower p := by
  have hgap := sub_pos.mpr hgain
  have hsmall := ssplus.toStrictStepSize model hgain
  have hratio : 2 * p.α * p.c ^ 2 * stockCeiling p < 1 := by
    simp only [stockCeiling]
    rw [show 2 * p.α * p.c ^ 2 * (p.I / (p.lambda₀ - p.g)) =
      (2 * p.α * p.c ^ 2 * p.I) / (p.lambda₀ - p.g) by ring]
    exact (div_lt_one hgap).2 hsmall.bound
  simpa only [policyDiagonalLower] using sub_pos.mpr hratio

/-- Positivity of the uniform stock-to-policy cross bound;
auxiliary to `thm:classify`, `civic_loops.tex:134--179`. -/
theorem policyStockUpper_pos {p : LoopParams} (model : LoopModelAssumptions p) :
    0 < policyStockUpper p := by
  simp only [policyStockUpper]
  exact mul_pos (mul_pos two_pos model.α_pos) model.c_pos

/-- The literal `(SS_g^+)` bound gives strict diagonal-product dominance;
auxiliary to `thm:classify`, `civic_loops.tex:134--179`. -/
theorem ConvergentStepAssumption.crossProduct_lt_diagonalProduct {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (ssplus : ConvergentStepAssumption p) :
    policyStockUpper p * stockPolicyUpper p <
      policyDiagonalLower p * stockDiagonalLower p := by
  have hgap := sub_pos.mpr hgain
  have hden := convergentStepDenominator_pos model
  have hbound : p.α * convergentStepDenominator p <
      (p.lambda₀ - p.g) * (p.s 0 + p.g) :=
    (lt_div_iff₀ hden).mp ssplus.bound
  simp only [convergentStepDenominator] at hbound
  have hscaled :
      (p.lambda₀ - p.g) * (policyStockUpper p * stockPolicyUpper p) <
        (p.lambda₀ - p.g) *
          (policyDiagonalLower p * stockDiagonalLower p) := by
    have hleft :
        (p.lambda₀ - p.g) * (policyStockUpper p * stockPolicyUpper p) =
          4 * p.α * p.c * p.η * (1 - p.lambda₀) * p.I := by
      simp only [policyStockUpper, stockPolicyUpper, stockCeiling]
      field_simp [hgap.ne']
      ring
    have hright :
        (p.lambda₀ - p.g) *
            (policyDiagonalLower p * stockDiagonalLower p) =
          (p.lambda₀ - p.g - 2 * p.α * p.c ^ 2 * p.I) *
            (p.s 0 + p.g) := by
      simp only [policyDiagonalLower, stockDiagonalLower, stockCeiling]
      field_simp [hgap.ne']
    rw [hleft, hright]
    nlinarith [hbound]
  exact (mul_lt_mul_iff_right₀ hgap).mp hscaled

/-- The printed ceiling satisfies every requirement, so `(SS_g^+)` is the case
`M = stockCeiling p` of the parameterized development below. -/
theorem ConvergentStepAssumption.toCeilingAssumption {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (ssplus : ConvergentStepAssumption p) :
    CeilingAssumption p (stockCeiling p) :=
  ⟨⟨le_rfl, (ssplus.policyDiagonalLower_pos model hgain).le⟩,
    ssplus.crossProduct_lt_diagonalProduct model hgain⟩

/-! ## Order preservation and difference estimates on `B` -/

/-- Sharp stock-multiplier difference bound on the policy interval;
auxiliary to `thm:classify`, `civic_loops.tex:146--159`. -/
theorem stockMultiplier_sub_le {p : LoopParams} (model : LoopModelAssumptions p)
    {β₁ β₂ : ℝ} (hβ₁ : β₁ ∈ Icc (0 : ℝ) 1) (hβ₂ : β₂ ∈ Icc (0 : ℝ) 1)
    (hβ : β₁ ≤ β₂) :
    p.s β₂ - p.s β₁ ≤
      2 * p.η * (1 - p.lambda₀) * (β₂ - β₁) := by
  let r₁ := 1 - p.η * (1 - β₁)
  let r₂ := 1 - p.η * (1 - β₂)
  have hr₁_nonneg : 0 ≤ r₁ := by
    dsimp only [r₁]
    have hresidual : 1 - β₁ ≤ 1 := by linarith [hβ₁.1]
    have := mul_le_mul_of_nonneg_left hresidual model.η_pos.le
    nlinarith [model.η_lt_one.le]
  have hr₂_nonneg : 0 ≤ r₂ := by
    dsimp only [r₂]
    have hresidual : 1 - β₂ ≤ 1 := by linarith [hβ₂.1]
    have := mul_le_mul_of_nonneg_left hresidual model.η_pos.le
    nlinarith [model.η_lt_one.le]
  have hr₁_le : r₁ ≤ 1 := by
    dsimp only [r₁]
    exact sub_le_self _ (mul_nonneg model.η_pos.le (sub_nonneg.mpr hβ₁.2))
  have hr₂_le : r₂ ≤ 1 := by
    dsimp only [r₂]
    exact sub_le_self _ (mul_nonneg model.η_pos.le (sub_nonneg.mpr hβ₂.2))
  have hdiff : r₂ - r₁ = p.η * (β₂ - β₁) := by
    dsimp only [r₁, r₂]
    ring
  have hsum : r₂ + r₁ ≤ 2 := by linarith
  have hfactor : r₂ ^ 2 - r₁ ^ 2 = (r₂ - r₁) * (r₂ + r₁) := by ring
  have hdelta_nonneg : 0 ≤ p.η * (β₂ - β₁) :=
    mul_nonneg model.η_pos.le (sub_nonneg.mpr hβ)
  calc
    p.s β₂ - p.s β₁ = (1 - p.lambda₀) * (r₂ ^ 2 - r₁ ^ 2) := by
      simp only [LoopParams.s]
      dsimp only [r₁, r₂]
      ring
    _ = (1 - p.lambda₀) * (p.η * (β₂ - β₁) * (r₂ + r₁)) := by
      rw [hfactor, hdiff]
    _ ≤ (1 - p.lambda₀) * (p.η * (β₂ - β₁) * 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsum hdelta_nonneg)
        (sub_nonneg.mpr model.lambda₀_lt_one.le)
    _ = 2 * p.η * (1 - p.lambda₀) * (β₂ - β₁) := by ring

/-- Paper III, `thm:classify`, cooperativity of the loop map on `B`,
`civic_loops.tex:146--159`. -/
theorem classificationLoopMap_monotoneOn {p : LoopParams} {M : ℝ}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hdiagM : 0 ≤ policyDiagonalLowerAt p M) :
    MonotoneOn p.loopMap (boxAt p M) := by
  intro x hx y hy hxy
  have hk : 0 ≤ 2 * p.α * p.c ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) (sq_nonneg p.c)
  have hgap := sub_pos.mpr hgain
  have hratio : 2 * p.α * p.c ^ 2 * M ≤ 1 := by
    simpa only [policyDiagonalLowerAt, sub_nonneg] using hdiagM
  have hdiag : 0 ≤ 1 - 2 * p.α * p.c ^ 2 * x.2 := by
    have := mul_le_mul_of_nonneg_left hx.2.2 hk
    linarith
  have hpolicyPolicy :
      PaperII.unclippedDeferenceInput p x.1 x.2 ≤
        PaperII.unclippedDeferenceInput p y.1 x.2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hxy.1) hdiag
    simp only [PaperII.unclippedDeferenceInput, LoopParams.gradU]
    nlinarith
  have hresidual : 0 ≤ 1 - p.c * y.1 := by
    have := mul_le_mul_of_nonneg_left hy.1.2 model.c_pos.le
    nlinarith [model.c_lt_one]
  have hpolicyStock :
      PaperII.unclippedDeferenceInput p y.1 x.2 ≤
        PaperII.unclippedDeferenceInput p y.1 y.2 := by
    have hcoef : 0 ≤ p.α * (2 * p.c * (1 - p.c * y.1)) :=
      mul_nonneg model.α_pos.le
        (mul_nonneg (mul_nonneg (by norm_num) model.c_pos.le) hresidual)
    simp only [PaperII.unclippedDeferenceInput, LoopParams.gradU]
    nlinarith [mul_nonneg hcoef (sub_nonneg.mpr hxy.2)]
  have hpolicy : p.deferenceStep x.1 x.2 ≤ p.deferenceStep y.1 y.2 :=
    LoopParams.monotone_clipUnit (hpolicyPolicy.trans hpolicyStock)
  have hsorder : p.s x.1 ≤ p.s y.1 :=
    (stockMultiplier_strictMonoOn model).monotoneOn hx.1 hy.1 hxy.1
  have hmultNonneg : 0 ≤ p.s y.1 + p.g :=
    add_nonneg (stockMultiplier_nonneg_le model hy.1).1 model.g_nonneg
  have hxDnonneg : 0 ≤ x.2 := model.I_pos.le.trans hx.2.1
  have hstockPolicy : (p.s x.1 + p.g) * x.2 ≤ (p.s y.1 + p.g) * x.2 :=
    mul_le_mul_of_nonneg_right (by linarith [hsorder]) hxDnonneg
  have hstockStock : (p.s y.1 + p.g) * x.2 ≤ (p.s y.1 + p.g) * y.2 :=
    mul_le_mul_of_nonneg_left hxy.2 hmultNonneg
  have hstock : p.stockStep x.1 x.2 ≤ p.stockStep y.1 y.2 := by
    simp only [LoopParams.stockStep]
    linarith [hstockPolicy.trans hstockStock]
  exact ⟨hpolicy, hstock⟩

/-- Policy-coordinate lower estimate for a southeast increment;
auxiliary to `thm:classify`, `civic_loops.tex:159--170`. -/
theorem southeast_unclipped_difference_lower {p : LoopParams} {M : ℝ}
    (model : LoopModelAssumptions p) {x y : LoopState}
    (hx : x ∈ boxAt p M) (hy : y ∈ boxAt p M)
    (hβ : x.1 ≤ y.1) (hD : y.2 ≤ x.2) :
    policyDiagonalLowerAt p M * (y.1 - x.1) -
        policyStockUpper p * (x.2 - y.2) ≤
      PaperII.unclippedDeferenceInput p y.1 y.2 -
        PaperII.unclippedDeferenceInput p x.1 x.2 := by
  have hk : 0 ≤ 2 * p.α * p.c ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) (sq_nonneg p.c)
  have ha : policyDiagonalLowerAt p M ≤ 1 - 2 * p.α * p.c ^ 2 * y.2 := by
    simp only [policyDiagonalLowerAt]
    have := mul_le_mul_of_nonneg_left hy.2.2 hk
    linarith
  have hb : 2 * p.α * p.c * (1 - p.c * x.1) ≤ policyStockUpper p := by
    have hcx : 0 ≤ p.c * x.1 := mul_nonneg model.c_pos.le hx.1.1
    have hcoef : 0 ≤ 2 * p.α * p.c :=
      mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) model.c_pos.le
    simp only [policyStockUpper]
    nlinarith [mul_le_mul_of_nonneg_left (show 1 - p.c * x.1 ≤ 1 by linarith) hcoef]
  have hap := mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hβ)
  have hbq := mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr hD)
  simp only [PaperII.unclippedDeferenceInput, LoopParams.gradU]
  nlinarith

/-- Stock-coordinate upper estimate for a southeast increment;
auxiliary to `thm:classify`, `civic_loops.tex:159--170`. -/
theorem southeast_stock_difference_upper {p : LoopParams} {M : ℝ}
    (model : LoopModelAssumptions p) {x y : LoopState}
    (hx : x ∈ boxAt p M) (hy : y ∈ boxAt p M)
    (hβ : x.1 ≤ y.1) (hD : y.2 ≤ x.2) :
    p.stockStep y.1 y.2 - p.stockStep x.1 x.2 ≤
      stockPolicyUpperAt p M * (y.1 - x.1) -
        stockDiagonalLower p * (x.2 - y.2) := by
  have hsmono : p.s x.1 ≤ p.s y.1 :=
    (stockMultiplier_strictMonoOn model).monotoneOn hx.1 hy.1 hβ
  have hsdiff_nonneg : 0 ≤ p.s y.1 - p.s x.1 := sub_nonneg.mpr hsmono
  have hslope := stockMultiplier_sub_le model hx.1 hy.1 hβ
  have hslope_nonneg :
      0 ≤ 2 * p.η * (1 - p.lambda₀) * (y.1 - x.1) :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) model.η_pos.le)
        (sub_nonneg.mpr model.lambda₀_lt_one.le))
      (sub_nonneg.mpr hβ)
  have hy_nonneg : 0 ≤ y.2 := model.I_pos.le.trans hy.2.1
  have hmul := mul_le_mul hslope hy.2.2 hy_nonneg hslope_nonneg
  have hstockPolicy :
      (p.s y.1 - p.s x.1) * y.2 ≤ stockPolicyUpperAt p M * (y.1 - x.1) := by
    simpa only [stockPolicyUpperAt] using (show
      (p.s y.1 - p.s x.1) * y.2 ≤
        2 * p.η * (1 - p.lambda₀) * M * (y.1 - x.1) by
      calc
        (p.s y.1 - p.s x.1) * y.2 ≤
            (2 * p.η * (1 - p.lambda₀) * (y.1 - x.1)) * M := hmul
        _ = 2 * p.η * (1 - p.lambda₀) * M *
              (y.1 - x.1) := by ring)
  have hs0 : p.s 0 + p.g ≤ p.s x.1 + p.g := by
    have := (stockMultiplier_strictMonoOn model).monotoneOn (by norm_num) hx.1 hx.1.1
    linarith
  have hstockDiagonal := mul_le_mul_of_nonneg_right hs0 (sub_nonneg.mpr hD)
  simp only [LoopParams.stockStep, stockDiagonalLower]
  nlinarith

/-- Policy-coordinate upper estimate for a northwest increment;
auxiliary to `thm:classify`, `civic_loops.tex:159--170`. -/
theorem northwest_unclipped_difference_upper {p : LoopParams} {M : ℝ}
    (model : LoopModelAssumptions p) {x y : LoopState}
    (hx : x ∈ boxAt p M) (hy : y ∈ boxAt p M)
    (hβ : y.1 ≤ x.1) (hD : x.2 ≤ y.2) :
    PaperII.unclippedDeferenceInput p y.1 y.2 -
        PaperII.unclippedDeferenceInput p x.1 x.2 ≤
      -policyDiagonalLowerAt p M * (x.1 - y.1) +
        policyStockUpper p * (y.2 - x.2) := by
  have hk : 0 ≤ 2 * p.α * p.c ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) (sq_nonneg p.c)
  have ha : policyDiagonalLowerAt p M ≤ 1 - 2 * p.α * p.c ^ 2 * y.2 := by
    simp only [policyDiagonalLowerAt]
    have := mul_le_mul_of_nonneg_left hy.2.2 hk
    linarith
  have hb : 2 * p.α * p.c * (1 - p.c * x.1) ≤ policyStockUpper p := by
    have hcx : 0 ≤ p.c * x.1 := mul_nonneg model.c_pos.le hx.1.1
    have hcoef : 0 ≤ 2 * p.α * p.c :=
      mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) model.c_pos.le
    simp only [policyStockUpper]
    nlinarith [mul_le_mul_of_nonneg_left (show 1 - p.c * x.1 ≤ 1 by linarith) hcoef]
  have hap := mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hβ)
  have hbq := mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr hD)
  simp only [PaperII.unclippedDeferenceInput, LoopParams.gradU]
  nlinarith

/-- Stock-coordinate lower estimate for a northwest increment;
auxiliary to `thm:classify`, `civic_loops.tex:159--170`. -/
theorem northwest_stock_difference_lower {p : LoopParams} {M : ℝ}
    (model : LoopModelAssumptions p) {x y : LoopState}
    (hx : x ∈ boxAt p M) (hy : y ∈ boxAt p M)
    (hβ : y.1 ≤ x.1) (hD : x.2 ≤ y.2) :
    -stockPolicyUpperAt p M * (x.1 - y.1) +
        stockDiagonalLower p * (y.2 - x.2) ≤
      p.stockStep y.1 y.2 - p.stockStep x.1 x.2 := by
  have hsmono : p.s y.1 ≤ p.s x.1 :=
    (stockMultiplier_strictMonoOn model).monotoneOn hy.1 hx.1 hβ
  have hsdiff_nonneg : 0 ≤ p.s x.1 - p.s y.1 := sub_nonneg.mpr hsmono
  have hslope := stockMultiplier_sub_le model hy.1 hx.1 hβ
  have hslope_nonneg :
      0 ≤ 2 * p.η * (1 - p.lambda₀) * (x.1 - y.1) :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) model.η_pos.le)
        (sub_nonneg.mpr model.lambda₀_lt_one.le))
      (sub_nonneg.mpr hβ)
  have hy_nonneg : 0 ≤ y.2 := model.I_pos.le.trans hy.2.1
  have hmul := mul_le_mul hslope hy.2.2 hy_nonneg hslope_nonneg
  have hstockPolicy :
      (p.s x.1 - p.s y.1) * y.2 ≤ stockPolicyUpperAt p M * (x.1 - y.1) := by
    simpa only [stockPolicyUpperAt] using (show
      (p.s x.1 - p.s y.1) * y.2 ≤
        2 * p.η * (1 - p.lambda₀) * M * (x.1 - y.1) by
      calc
        (p.s x.1 - p.s y.1) * y.2 ≤
            (2 * p.η * (1 - p.lambda₀) * (x.1 - y.1)) * M := hmul
        _ = 2 * p.η * (1 - p.lambda₀) * M *
              (x.1 - y.1) := by ring)
  have hs0 : p.s 0 + p.g ≤ p.s x.1 + p.g := by
    have := (stockMultiplier_strictMonoOn model).monotoneOn (by norm_num) hx.1 hx.1.1
    linarith
  have hstockDiagonal := mul_le_mul_of_nonneg_right hs0 (sub_nonneg.mpr hD)
  simp only [LoopParams.stockStep, stockDiagonalLower]
  nlinarith

/-- `(SS_g^+)` excludes a southeast step followed by a northwest step;
auxiliary to `thm:classify`, `civic_loops.tex:159--170`. -/
theorem no_southeast_to_northwest {p : LoopParams} {M : ℝ}
    (model : LoopModelAssumptions p) (_hgain : p.g < p.lambda₀)
    (hdom : policyStockUpper p * stockPolicyUpperAt p M <
      policyDiagonalLowerAt p M * stockDiagonalLower p) {x y : LoopState}
    (hx : x ∈ boxAt p M) (hy : y ∈ boxAt p M)
    (hxy : PaperII.Southeast x y) :
    ¬PaperII.Northwest (p.loopMap x) (p.loopMap y) := by
  intro hnext
  have hinput : PaperII.unclippedDeferenceInput p y.1 y.2 <
      PaperII.unclippedDeferenceInput p x.1 x.2 := by
    by_contra hnot
    have hmono := LoopParams.monotone_clipUnit (not_lt.mp hnot)
    have hpolicy : (p.loopMap x).1 ≤ (p.loopMap y).1 := by
      simpa only [LoopParams.loopMap, LoopParams.deferenceStep,
        PaperII.unclippedDeferenceInput] using hmono
    exact (not_lt_of_ge hpolicy) hnext.1
  have hpolicyBound := southeast_unclipped_difference_lower model hx hy
    hxy.1.le hxy.2.le
  have hpolicy : policyDiagonalLowerAt p M * (y.1 - x.1) <
      policyStockUpper p * (x.2 - y.2) := by nlinarith
  have hstockBound := southeast_stock_difference_upper model hx hy hxy.1.le hxy.2.le
  have hstock : stockDiagonalLower p * (x.2 - y.2) <
      stockPolicyUpperAt p M * (y.1 - x.1) := by
    have hnextStock : 0 < p.stockStep y.1 y.2 - p.stockStep x.1 x.2 := by
      simpa only [LoopParams.loopMap] using sub_pos.mpr hnext.2
    nlinarith
  exact PaperII.cross_inequalities_impossible (sub_pos.mpr hxy.1) (sub_pos.mpr hxy.2)
    (policyStockUpper_pos model) (stockDiagonalLower_pos model)
    hdom hpolicy hstock

/-- `(SS_g^+)` excludes a northwest step followed by a southeast step;
auxiliary to `thm:classify`, `civic_loops.tex:159--170`. -/
theorem no_northwest_to_southeast {p : LoopParams} {M : ℝ}
    (model : LoopModelAssumptions p) (_hgain : p.g < p.lambda₀)
    (hdom : policyStockUpper p * stockPolicyUpperAt p M <
      policyDiagonalLowerAt p M * stockDiagonalLower p) {x y : LoopState}
    (hx : x ∈ boxAt p M) (hy : y ∈ boxAt p M)
    (hxy : PaperII.Northwest x y) :
    ¬PaperII.Southeast (p.loopMap x) (p.loopMap y) := by
  intro hnext
  have hinput : PaperII.unclippedDeferenceInput p x.1 x.2 <
      PaperII.unclippedDeferenceInput p y.1 y.2 := by
    by_contra hnot
    have hmono := LoopParams.monotone_clipUnit (not_lt.mp hnot)
    have hpolicy : (p.loopMap y).1 ≤ (p.loopMap x).1 := by
      simpa only [LoopParams.loopMap, LoopParams.deferenceStep,
        PaperII.unclippedDeferenceInput] using hmono
    exact (not_lt_of_ge hpolicy) hnext.1
  have hpolicyBound := northwest_unclipped_difference_upper model hx hy
    hxy.1.le hxy.2.le
  have hpolicy : policyDiagonalLowerAt p M * (x.1 - y.1) <
      policyStockUpper p * (y.2 - x.2) := by nlinarith
  have hstockBound := northwest_stock_difference_lower model hx hy hxy.1.le hxy.2.le
  have hstock : stockDiagonalLower p * (y.2 - x.2) <
      stockPolicyUpperAt p M * (x.1 - y.1) := by
    have hnextStock : p.stockStep y.1 y.2 - p.stockStep x.1 x.2 < 0 := by
      simpa only [LoopParams.loopMap] using sub_neg.mpr hnext.2
    nlinarith
  exact PaperII.cross_inequalities_impossible (sub_pos.mpr hxy.1) (sub_pos.mpr hxy.2)
    (policyStockUpper_pos model) (stockDiagonalLower_pos model)
    hdom hpolicy hstock

/-! ## Orbit convergence -/

/-- An orbit starting in Paper III's box `B` remains there;
auxiliary to `thm:classify`, `civic_loops.tex:143--170`. -/
theorem orbit_mem_classificationBox {p : LoopParams} {M : ℝ}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hM : CooperativeCeiling p M) {x : ℕ → LoopState} (traj : IsLoopOrbit p x)
    (hx0 : x 0 ∈ boxAt p M) : ∀ n, x n ∈ boxAt p M := by
  intro n
  induction n with
  | zero => exact hx0
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by omega, traj n]
      exact boxAt_invariant model hgain hM.ceiling_le ih

/-- A componentwise increasing step propagates along a Paper III orbit;
the monotone-step clause of `thm:classify`, `civic_loops.tex:134--170`. -/
theorem orbit_tail_monotone_of_le {p : LoopParams} {M : ℝ}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hM : CooperativeCeiling p M) {x : ℕ → LoopState}
    (traj : IsLoopOrbit p x) (hmem : ∀ n, x n ∈ boxAt p M) {t : ℕ}
    (hstep : x t ≤ x (t + 1)) : Monotone (fun n ↦ x (n + t)) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => simpa [Nat.add_comm] using hstep
  | succ n ih =>
      have hmono := classificationLoopMap_monotoneOn model hgain hM.diagonal_nonneg
        (hmem (n + t)) (hmem (n + 1 + t)) ih
      calc
        x (Nat.succ n + t) = p.loopMap (x (n + t)) := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using traj (n + t)
        _ ≤ p.loopMap (x (n + 1 + t)) := hmono
        _ = x (Nat.succ n + 1 + t) := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using (traj (n + 1 + t)).symm

/-- A componentwise decreasing step propagates along a Paper III orbit;
the monotone-step clause of `thm:classify`, `civic_loops.tex:134--170`. -/
theorem orbit_tail_antitone_of_ge {p : LoopParams} {M : ℝ}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hM : CooperativeCeiling p M) {x : ℕ → LoopState}
    (traj : IsLoopOrbit p x) (hmem : ∀ n, x n ∈ boxAt p M) {t : ℕ}
    (hstep : x (t + 1) ≤ x t) : Antitone (fun n ↦ x (n + t)) := by
  apply antitone_nat_of_succ_le
  intro n
  induction n with
  | zero => simpa [Nat.add_comm] using hstep
  | succ n ih =>
      have hmono := classificationLoopMap_monotoneOn model hgain hM.diagonal_nonneg
        (hmem (n + 1 + t)) (hmem (n + t)) ih
      calc
        x (Nat.succ n + 1 + t) = p.loopMap (x (n + 1 + t)) := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using traj (n + 1 + t)
        _ ≤ p.loopMap (x (n + t)) := hmono
        _ = x (Nat.succ n + t) := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using (traj (n + t)).symm

/-- Every bounded componentwise monotone sequence in `B` converges in `B`;
auxiliary to `thm:classify`, `civic_loops.tex:134--170`. -/
theorem monotone_sequence_tendsto_in_classificationBox {p : LoopParams} {M : ℝ}
    {x : ℕ → LoopState} (hmono : Monotone x)
    (hmem : ∀ n, x n ∈ boxAt p M) :
    ∃ q ∈ boxAt p M, Tendsto x atTop (𝓝 q) := by
  have hβmono : Monotone (fun n ↦ (x n).1) := fun _ _ h ↦ (hmono h).1
  have hDmono : Monotone (fun n ↦ (x n).2) := fun _ _ h ↦ (hmono h).2
  have hβbdd : BddAbove (range fun n ↦ (x n).1) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; exact (hmem n).1.2⟩
  have hDbdd : BddAbove (range fun n ↦ (x n).2) :=
    ⟨M, by rintro _ ⟨n, rfl⟩; exact (hmem n).2.2⟩
  let q : LoopState := (⨆ n, (x n).1, ⨆ n, (x n).2)
  have hlim : Tendsto x atTop (𝓝 q) := (Prod.tendsto_iff x q).2 ⟨
    by simpa only [q] using tendsto_atTop_ciSup hβmono hβbdd,
    by simpa only [q] using tendsto_atTop_ciSup hDmono hDbdd⟩
  have hclosed : IsClosed (boxAt p M) := isClosed_Icc.prod isClosed_Icc
  exact ⟨q, hclosed.mem_of_tendsto hlim (Eventually.of_forall hmem), hlim⟩

/-- Every bounded componentwise antitone sequence in `B` converges in `B`;
auxiliary to `thm:classify`, `civic_loops.tex:134--170`. -/
theorem antitone_sequence_tendsto_in_classificationBox {p : LoopParams} {M : ℝ}
    {x : ℕ → LoopState} (hanti : Antitone x)
    (hmem : ∀ n, x n ∈ boxAt p M) :
    ∃ q ∈ boxAt p M, Tendsto x atTop (𝓝 q) := by
  have hβanti : Antitone (fun n ↦ (x n).1) := fun _ _ h ↦ (hanti h).1
  have hDanti : Antitone (fun n ↦ (x n).2) := fun _ _ h ↦ (hanti h).2
  have hβbdd : BddBelow (range fun n ↦ (x n).1) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact (hmem n).1.1⟩
  have hDbdd : BddBelow (range fun n ↦ (x n).2) :=
    ⟨p.I, by rintro _ ⟨n, rfl⟩; exact (hmem n).2.1⟩
  let q : LoopState := (⨅ n, (x n).1, ⨅ n, (x n).2)
  have hlim : Tendsto x atTop (𝓝 q) := (Prod.tendsto_iff x q).2 ⟨
    by simpa only [q] using tendsto_atTop_ciInf hβanti hβbdd,
    by simpa only [q] using tendsto_atTop_ciInf hDanti hDbdd⟩
  have hclosed : IsClosed (boxAt p M) := isClosed_Icc.prod isClosed_Icc
  exact ⟨q, hclosed.mem_of_tendsto hlim (Eventually.of_forall hmem), hlim⟩

/-- A convergent Paper III orbit can only converge to a fixed point;
auxiliary to `thm:classify`, `civic_loops.tex:134--170`. -/
theorem orbit_limit_is_equilibrium {p : LoopParams} {x : ℕ → LoopState}
    (traj : IsLoopOrbit p x) {q : LoopState} (hlim : Tendsto x atTop (𝓝 q)) :
    IsLoopEquilibrium p q.1 q.2 := by
  have hshift : Tendsto (fun n ↦ x (n + 1)) atTop (𝓝 q) :=
    (tendsto_add_atTop_iff_nat 1).2 hlim
  have hmapToQ : Tendsto (fun n ↦ p.loopMap (x n)) atTop (𝓝 q) := by
    apply hshift.congr'
    exact Eventually.of_forall fun n ↦ traj n
  have hmapToMap : Tendsto (fun n ↦ p.loopMap (x n)) atTop (𝓝 (p.loopMap q)) :=
    ((PaperII.continuous_loopMap p).tendsto q).comp hlim
  exact tendsto_nhds_unique hmapToMap hmapToQ

/-- Paper III, `thm:classify`, monotone-step principle. -/
theorem comparableStep_convergesToFixedPoint {p : LoopParams} {M : ℝ}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hM : CooperativeCeiling p M) {x : ℕ → LoopState} (traj : IsLoopOrbit p x)
    (hx0 : x 0 ∈ boxAt p M) {t : ℕ}
    (hcomparable : x t ≤ x (t + 1) ∨ x (t + 1) ≤ x t) :
    ∃ q ∈ boxAt p M,
      Tendsto x atTop (𝓝 q) ∧ IsLoopEquilibrium p q.1 q.2 := by
  have hmem := orbit_mem_classificationBox model hgain hM traj hx0
  rcases hcomparable with hstep | hstep
  · have hmono := orbit_tail_monotone_of_le model hgain hM traj hmem hstep
    obtain ⟨q, hq, hlim⟩ := monotone_sequence_tendsto_in_classificationBox hmono
      (fun n ↦ hmem (n + t))
    have hfull : Tendsto x atTop (𝓝 q) := (tendsto_add_atTop_iff_nat t).1 hlim
    exact ⟨q, hq, hfull, orbit_limit_is_equilibrium traj hfull⟩
  · have hanti := orbit_tail_antitone_of_ge model hgain hM traj hmem hstep
    obtain ⟨q, hq, hlim⟩ := antitone_sequence_tendsto_in_classificationBox hanti
      (fun n ↦ hmem (n + t))
    have hfull : Tendsto x atTop (𝓝 q) := (tendsto_add_atTop_iff_nat t).1 hlim
    exact ⟨q, hq, hfull, orbit_limit_is_equilibrium traj hfull⟩

/-- Orbit-level form of the southeast-to-northwest exclusion;
auxiliary to `thm:classify`, `civic_loops.tex:159--170`. -/
theorem orbit_no_southeast_to_northwest {p : LoopParams} {M : ℝ}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hM : CeilingAssumption p M) {x : ℕ → LoopState}
    (traj : IsLoopOrbit p x) (hmem : ∀ n, x n ∈ boxAt p M) {n : ℕ}
    (hstep : PaperII.Southeast (x n) (x (n + 1))) :
    ¬PaperII.Northwest (x (n + 1)) (x (n + 2)) := by
  have h := no_southeast_to_northwest model hgain hM.dominance (hmem n) (hmem (n + 1)) hstep
  simpa [show n + 2 = (n + 1) + 1 by omega, traj n, traj (n + 1)] using h

/-- Orbit-level form of the northwest-to-southeast exclusion;
auxiliary to `thm:classify`, `civic_loops.tex:159--170`. -/
theorem orbit_no_northwest_to_southeast {p : LoopParams} {M : ℝ}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hM : CeilingAssumption p M) {x : ℕ → LoopState}
    (traj : IsLoopOrbit p x) (hmem : ∀ n, x n ∈ boxAt p M) {n : ℕ}
    (hstep : PaperII.Northwest (x n) (x (n + 1))) :
    ¬PaperII.Southeast (x (n + 1)) (x (n + 2)) := by
  have h := no_northwest_to_southeast model hgain hM.dominance (hmem n) (hmem (n + 1)) hstep
  simpa [show n + 2 = (n + 1) + 1 by omega, traj n, traj (n + 1)] using h

/-- With no comparable step, one southeast step fixes every step's quadrant;
auxiliary to `thm:classify`, `civic_loops.tex:159--170`. -/
theorem orbit_southeast_of_no_comparable_step {p : LoopParams} {M : ℝ}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hM : CeilingAssumption p M) {x : ℕ → LoopState}
    (traj : IsLoopOrbit p x) (hmem : ∀ n, x n ∈ boxAt p M)
    (hnone : ∀ n, ¬(x n ≤ x (n + 1) ∨ x (n + 1) ≤ x n))
    (hfirst : PaperII.Southeast (x 0) (x 1)) :
    ∀ n, PaperII.Southeast (x n) (x (n + 1)) := by
  intro n
  induction n with
  | zero => simpa using hfirst
  | succ n ih =>
      rcases PaperII.southeast_or_northwest_of_not_comparable (hnone (n + 1)) with h | h
      · simpa [Nat.succ_eq_add_one] using h
      · exact (orbit_no_southeast_to_northwest model hgain hM traj hmem ih
          (by simpa [Nat.succ_eq_add_one] using h)).elim

/-- With no comparable step, one northwest step fixes every step's quadrant;
auxiliary to `thm:classify`, `civic_loops.tex:159--170`. -/
theorem orbit_northwest_of_no_comparable_step {p : LoopParams} {M : ℝ}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hM : CeilingAssumption p M) {x : ℕ → LoopState}
    (traj : IsLoopOrbit p x) (hmem : ∀ n, x n ∈ boxAt p M)
    (hnone : ∀ n, ¬(x n ≤ x (n + 1) ∨ x (n + 1) ≤ x n))
    (hfirst : PaperII.Northwest (x 0) (x 1)) :
    ∀ n, PaperII.Northwest (x n) (x (n + 1)) := by
  intro n
  induction n with
  | zero => simpa using hfirst
  | succ n ih =>
      rcases PaperII.southeast_or_northwest_of_not_comparable (hnone (n + 1)) with h | h
      · exact (orbit_no_northwest_to_southeast model hgain hM traj hmem ih
          (by simpa [Nat.succ_eq_add_one] using h)).elim
      · simpa [Nat.succ_eq_add_one] using h

/-- An all-southeast orbit converges in `B` by mixed coordinate monotonicity;
auxiliary to `thm:classify`, `civic_loops.tex:159--170`. -/
theorem southeast_orbit_tendsto_in_classificationBox {p : LoopParams} {M : ℝ}
    {x : ℕ → LoopState} (hmem : ∀ n, x n ∈ boxAt p M)
    (hstep : ∀ n, PaperII.Southeast (x n) (x (n + 1))) :
    ∃ q ∈ boxAt p M, Tendsto x atTop (𝓝 q) := by
  have hβmono : Monotone (fun n ↦ (x n).1) :=
    monotone_nat_of_le_succ fun n ↦ (hstep n).1.le
  have hDanti : Antitone (fun n ↦ (x n).2) :=
    antitone_nat_of_succ_le fun n ↦ (hstep n).2.le
  have hβbdd : BddAbove (range fun n ↦ (x n).1) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; exact (hmem n).1.2⟩
  have hDbdd : BddBelow (range fun n ↦ (x n).2) :=
    ⟨p.I, by rintro _ ⟨n, rfl⟩; exact (hmem n).2.1⟩
  let q : LoopState := (⨆ n, (x n).1, ⨅ n, (x n).2)
  have hlim : Tendsto x atTop (𝓝 q) := (Prod.tendsto_iff x q).2 ⟨
    by simpa only [q] using tendsto_atTop_ciSup hβmono hβbdd,
    by simpa only [q] using tendsto_atTop_ciInf hDanti hDbdd⟩
  have hclosed : IsClosed (boxAt p M) := isClosed_Icc.prod isClosed_Icc
  exact ⟨q, hclosed.mem_of_tendsto hlim (Eventually.of_forall hmem), hlim⟩

/-- An all-northwest orbit converges in `B` by mixed coordinate monotonicity;
auxiliary to `thm:classify`, `civic_loops.tex:159--170`. -/
theorem northwest_orbit_tendsto_in_classificationBox {p : LoopParams} {M : ℝ}
    {x : ℕ → LoopState} (hmem : ∀ n, x n ∈ boxAt p M)
    (hstep : ∀ n, PaperII.Northwest (x n) (x (n + 1))) :
    ∃ q ∈ boxAt p M, Tendsto x atTop (𝓝 q) := by
  have hβanti : Antitone (fun n ↦ (x n).1) :=
    antitone_nat_of_succ_le fun n ↦ (hstep n).1.le
  have hDmono : Monotone (fun n ↦ (x n).2) :=
    monotone_nat_of_le_succ fun n ↦ (hstep n).2.le
  have hβbdd : BddBelow (range fun n ↦ (x n).1) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact (hmem n).1.1⟩
  have hDbdd : BddAbove (range fun n ↦ (x n).2) :=
    ⟨M, by rintro _ ⟨n, rfl⟩; exact (hmem n).2.2⟩
  let q : LoopState := (⨅ n, (x n).1, ⨆ n, (x n).2)
  have hlim : Tendsto x atTop (𝓝 q) := (Prod.tendsto_iff x q).2 ⟨
    by simpa only [q] using tendsto_atTop_ciInf hβanti hβbdd,
    by simpa only [q] using tendsto_atTop_ciSup hDmono hDbdd⟩
  have hclosed : IsClosed (boxAt p M) := isClosed_Icc.prod isClosed_Icc
  exact ⟨q, hclosed.mem_of_tendsto hlim (Eventually.of_forall hmem), hlim⟩

/--
Paper III, Theorem 2.2 (`thm:classify`), global-convergence clause,
`civic_loops.tex:134`.

Every orbit starting in `B` converges to a fixed point under the displayed
`(SS_g^+)` bound.  This is the content-gain version of Paper II's self-contained
quadrant proof and has no imported convergence axiom.
-/
theorem classification_globalConvergence_of_convergentStep {p : LoopParams} {M : ℝ}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hM : CeilingAssumption p M) {x : ℕ → LoopState}
    (traj : IsLoopOrbit p x) (hx0 : x 0 ∈ boxAt p M) :
    ∃ q ∈ boxAt p M,
      Tendsto x atTop (𝓝 q) ∧ IsLoopEquilibrium p q.1 q.2 := by
  have hmem := orbit_mem_classificationBox model hgain hM.toCooperativeCeiling traj hx0
  by_cases hcomparable : ∃ t, x t ≤ x (t + 1) ∨ x (t + 1) ≤ x t
  · obtain ⟨t, ht⟩ := hcomparable
    exact comparableStep_convergesToFixedPoint model hgain hM.toCooperativeCeiling traj hx0 ht
  · have hnone : ∀ n, ¬(x n ≤ x (n + 1) ∨ x (n + 1) ≤ x n) := by
      intro n hn
      exact hcomparable ⟨n, hn⟩
    rcases PaperII.southeast_or_northwest_of_not_comparable (hnone 0) with
      hfirst | hfirst
    · have hall := orbit_southeast_of_no_comparable_step model hgain hM traj hmem hnone
        (by simpa using hfirst)
      obtain ⟨q, hq, hlim⟩ := southeast_orbit_tendsto_in_classificationBox hmem hall
      exact ⟨q, hq, hlim, orbit_limit_is_equilibrium traj hlim⟩
    · have hall := orbit_northwest_of_no_comparable_step model hgain hM traj hmem hnone
        (by simpa using hfirst)
      obtain ⟨q, hq, hlim⟩ := northwest_orbit_tendsto_in_classificationBox hmem hall
      exact ⟨q, hq, hlim, orbit_limit_is_equilibrium traj hlim⟩

/-! ## Exact fixed-point catalogue -/

/--
Paper III, Theorem 2.2 (`thm:classify`), fixed-point catalogue,
`civic_loops.tex:130--174`.

The projection contributes the two endpoint sign conditions; every interior
fixed point is exactly a zero of the stationary gradient `G`.
-/
theorem loopEquilibrium_iff_stationary_sign_catalogue {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀) (β D : ℝ) :
    IsLoopEquilibrium p β D ↔
      (β = 0 ∧ D = p.stationaryStock 0 ∧ p.G 0 ≤ 0) ∨
      (β ∈ Ioo (0 : ℝ) 1 ∧ D = p.stationaryStock β ∧ p.G β = 0) ∨
      (β = 1 ∧ D = p.stationaryStock 1 ∧ 0 ≤ p.G 1) := by
  constructor
  · intro hequilibrium
    have hpolicy := congrArg Prod.fst hequilibrium
    simp only [LoopParams.loopMap] at hpolicy
    have hβ : β ∈ Icc (0 : ℝ) 1 := by
      have hmem := LoopParams.clipUnit_mem (β + p.α * p.gradU β D)
      simp only [LoopParams.deferenceStep] at hpolicy
      rwa [hpolicy] at hmem
    have hD := equilibrium_stock_eq_stationary model hgain hβ hequilibrium
    by_cases hzero : β = 0
    · subst β
      refine Or.inl ⟨rfl, hD, ?_⟩
      have hinput : p.α * p.gradU 0 D ≤ 0 := by
        rw [← zero_add (p.α * p.gradU 0 D)]
        exact (PaperII.clipUnit_eq_zero_iff _).1 (by
          simpa only [LoopParams.deferenceStep] using hpolicy)
      have hgrad : p.gradU 0 D = p.G 0 := by
        rw [hD, gradU_stationaryStock_eq_G]
      nlinarith [model.α_pos]
    by_cases hone : β = 1
    · subst β
      refine Or.inr (Or.inr ⟨rfl, hD, ?_⟩)
      have hinput : 1 ≤ 1 + p.α * p.gradU 1 D :=
        (PaperII.clipUnit_eq_one_iff _).1 (by
          simpa only [LoopParams.deferenceStep] using hpolicy)
      have hgrad : p.gradU 1 D = p.G 1 := by
        rw [hD, gradU_stationaryStock_eq_G]
      nlinarith [model.α_pos]
    · have hβint : β ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne hβ.1 (Ne.symm hzero), lt_of_le_of_ne hβ.2 hone⟩
      have hinput : β + p.α * p.gradU β D = β :=
        (PaperII.clipUnit_eq_interior_iff hβint).1 (by
          simpa only [LoopParams.deferenceStep] using hpolicy)
      have hgrad : p.gradU β D = 0 := by
        nlinarith [model.α_pos]
      have hG : p.G β = 0 := by
        rw [← gradU_stationaryStock_eq_G, ← hD]
        exact hgrad
      exact Or.inr (Or.inl ⟨hβint, hD, hG⟩)
  · rintro (⟨rfl, rfl, hG⟩ | ⟨hβ, rfl, hG⟩ | ⟨rfl, rfl, hG⟩)
    · have hunit : (0 : ℝ) ∈ Icc 0 1 := by norm_num
      have hstock := loopStationaryStock_fixed model hgain hunit
      have hpolicy : p.deferenceStep 0 (p.stationaryStock 0) = 0 := by
        simp only [LoopParams.deferenceStep, gradU_stationaryStock_eq_G, zero_add]
        rw [PaperII.clipUnit_eq_zero_iff]
        exact mul_nonpos_of_nonneg_of_nonpos model.α_pos.le hG
      simp only [IsLoopEquilibrium, LoopParams.loopMap, hpolicy, hstock]
    · exact stationaryRoot_equilibrium model hgain ⟨hβ.1.le, hβ.2.le⟩ hG
    · have hunit : (1 : ℝ) ∈ Icc 0 1 := by norm_num
      have hstock := loopStationaryStock_fixed model hgain hunit
      have hpolicy : p.deferenceStep 1 (p.stationaryStock 1) = 1 := by
        rw [LoopParams.deferenceStep, gradU_stationaryStock_eq_G,
          PaperII.clipUnit_eq_one_iff]
        nlinarith [mul_nonneg model.α_pos.le hG]
      simp only [IsLoopEquilibrium, LoopParams.loopMap, hpolicy, hstock]

#print axioms classificationBox_invariant
#print axioms stockDiagonalLower_pos
#print axioms convergentStepDenominator_pos
#print axioms ConvergentStepAssumption.toStrictStepSize
#print axioms ConvergentStepAssumption.policyDiagonalLower_pos
#print axioms policyStockUpper_pos
#print axioms ConvergentStepAssumption.crossProduct_lt_diagonalProduct
#print axioms stockMultiplier_sub_le
#print axioms classificationLoopMap_monotoneOn
#print axioms southeast_unclipped_difference_lower
#print axioms southeast_stock_difference_upper
#print axioms northwest_unclipped_difference_upper
#print axioms northwest_stock_difference_lower
#print axioms no_southeast_to_northwest
#print axioms no_northwest_to_southeast
#print axioms orbit_mem_classificationBox
#print axioms orbit_tail_monotone_of_le
#print axioms orbit_tail_antitone_of_ge
#print axioms monotone_sequence_tendsto_in_classificationBox
#print axioms antitone_sequence_tendsto_in_classificationBox
#print axioms orbit_limit_is_equilibrium
#print axioms comparableStep_convergesToFixedPoint
#print axioms orbit_no_southeast_to_northwest
#print axioms orbit_no_northwest_to_southeast
#print axioms orbit_southeast_of_no_comparable_step
#print axioms orbit_northwest_of_no_comparable_step
#print axioms southeast_orbit_tendsto_in_classificationBox
#print axioms northwest_orbit_tendsto_in_classificationBox
#print axioms classification_globalConvergence_of_convergentStep
#print axioms loopEquilibrium_iff_stationary_sign_catalogue

end

end CivicAlignment.PaperIII
