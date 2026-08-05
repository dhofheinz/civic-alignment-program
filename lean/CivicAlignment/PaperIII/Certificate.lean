/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.Basic
import CivicAlignment.ClippedStep
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Paper III: policy-free stock bounds and the knob-free certificate

This file isolates the certificate argument from the imported phase-portrait
theory.  Its stock bound quantifies over an arbitrary deference trajectory.
-/

namespace CivicAlignment.PaperIII

open Filter Set Topology

/-- The standing parameter restrictions in Paper III's loop-model paragraph. -/
structure LoopModelAssumptions (p : LoopParams) : Prop where
  η_pos : 0 < p.η
  η_lt_one : p.η < 1
  lambda₀_pos : 0 < p.lambda₀
  lambda₀_lt_one : p.lambda₀ < 1
  I_pos : 0 < p.I
  v_pos : 0 < p.v
  c_pos : 0 < p.c
  c_lt_one : p.c < 1
  α_pos : 0 < p.α
  g_nonneg : 0 ≤ p.g

/-- A pair of sequences obeys Paper III's stock law for every time step. -/
def IsStockTrajectory (p : LoopParams) (β D : ℕ → ℝ) : Prop :=
  ∀ t, D (t + 1) = p.stockStep (β t) (D t)

/-- On the policy interval, the endogenous persistence lies between zero and `1 - λ₀`. -/
theorem stockMultiplier_nonneg_le {p : LoopParams} (model : LoopModelAssumptions p)
    {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 ≤ p.s β ∧ p.s β ≤ 1 - p.lambda₀ := by
  have hη_nonneg : 0 ≤ p.η := model.η_pos.le
  have hresidual_nonneg : 0 ≤ 1 - β := sub_nonneg.mpr hβ.2
  have hresidual_le_one : 1 - β ≤ 1 := by linarith [hβ.1]
  have hproduct_nonneg : 0 ≤ p.η * (1 - β) := mul_nonneg hη_nonneg hresidual_nonneg
  have hproduct_le_eta : p.η * (1 - β) ≤ p.η := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hresidual_le_one hη_nonneg
  have hinner_nonneg : 0 ≤ 1 - p.η * (1 - β) := by
    linarith [model.η_lt_one.le]
  have hinner_le_one : 1 - p.η * (1 - β) ≤ 1 := by linarith
  have hsquare_le : (1 - p.η * (1 - β)) ^ 2 ≤ (1 : ℝ) ^ 2 :=
    (sq_le_sq₀ hinner_nonneg zero_le_one).2 hinner_le_one
  have hgrounding_nonneg : 0 ≤ 1 - p.lambda₀ := sub_nonneg.mpr model.lambda₀_lt_one.le
  constructor
  · simp only [LoopParams.s]
    exact mul_nonneg hgrounding_nonneg (sq_nonneg _)
  · simp only [LoopParams.s]
    simpa only [one_pow, mul_one] using
      mul_le_mul_of_nonneg_left hsquare_le hgrounding_nonneg

/-- The endogenous stock multiplier is strictly increasing on the policy interval. -/
theorem stockMultiplier_strictMonoOn {p : LoopParams} (model : LoopModelAssumptions p) :
    StrictMonoOn p.s (Icc (0 : ℝ) 1) := by
  intro β1 hβ1 β2 hβ2 hβ
  have hinner1_nonneg : 0 ≤ 1 - p.η * (1 - β1) := by
    have hresidual : 1 - β1 ≤ 1 := by linarith [hβ1.1]
    have hproduct : p.η * (1 - β1) ≤ p.η := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hresidual model.η_pos.le
    linarith [model.η_lt_one.le]
  have hinner2_nonneg : 0 ≤ 1 - p.η * (1 - β2) := by
    have hresidual : 1 - β2 ≤ 1 := by linarith [hβ2.1]
    have hproduct : p.η * (1 - β2) ≤ p.η := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hresidual model.η_pos.le
    linarith [model.η_lt_one.le]
  have hinner : 1 - p.η * (1 - β1) < 1 - p.η * (1 - β2) := by
    nlinarith [mul_pos model.η_pos (sub_pos.mpr hβ)]
  have hsquare := (sq_lt_sq₀ hinner1_nonneg hinner2_nonneg).2 hinner
  simp only [LoopParams.s]
  exact mul_lt_mul_of_pos_left hsquare (sub_pos.mpr model.lambda₀_lt_one)

/-- Every valid stock path remains nonnegative when it starts nonnegative. -/
theorem stockTrajectory_nonnegative {p : LoopParams} (model : LoopModelAssumptions p)
    {β D : ℕ → ℝ} (hβ : ∀ t, β t ∈ Icc (0 : ℝ) 1)
    (hstock : IsStockTrajectory p β D) (hD0 : 0 ≤ D 0) :
    ∀ t, 0 ≤ D t := by
  intro t
  induction t with
  | zero => exact hD0
  | succ t ih =>
      rw [hstock t]
      simp only [LoopParams.stockStep]
      have hmultiplier := stockMultiplier_nonneg_le model (hβ t)
      exact add_nonneg (mul_nonneg (add_nonneg hmultiplier.1 model.g_nonneg) ih) model.I_pos.le

/-- An arbitrary policy path is dominated by the worst-case affine stock recursion. -/
theorem stockTrajectory_le_arithGeom {p : LoopParams} (model : LoopModelAssumptions p)
    {β D : ℕ → ℝ} (hβ : ∀ t, β t ∈ Icc (0 : ℝ) 1) (hstock : IsStockTrajectory p β D)
    (hD0 : 0 ≤ D 0) :
    ∀ t, D t ≤ arithGeom (1 - p.lambda₀ + p.g) p.I (D 0) t := by
  have hDnonneg := stockTrajectory_nonnegative model hβ hstock hD0
  have huniform_nonneg : 0 ≤ 1 - p.lambda₀ + p.g :=
    add_nonneg (sub_nonneg.mpr model.lambda₀_lt_one.le) model.g_nonneg
  intro t
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
      rw [hstock t, arithGeom_succ]
      simp only [LoopParams.stockStep]
      have hmultiplier := stockMultiplier_nonneg_le model (hβ t)
      have hcoefficient : p.s (β t) + p.g ≤ 1 - p.lambda₀ + p.g := by
        linarith [hmultiplier.2]
      simpa only [add_comm] using
        add_le_add_right (mul_le_mul hcoefficient ih (hDnonneg t) huniform_nonneg) p.I

/--
Paper III, Lemma 4.1 (`lem:bound`), civic_loops.tex:235: for every deference
trajectory, the stock has the stated uniform bound and limsup bound.
-/
theorem stock_upper_bound {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β D : ℕ → ℝ}
    (hβ : ∀ t, β t ∈ Icc (0 : ℝ) 1) (hstock : IsStockTrajectory p β D)
    (hD0 : 0 ≤ D 0) :
    (∀ t, D t ≤ max (D 0) (p.I / (p.lambda₀ - p.g))) ∧
      limsup D atTop ≤ p.I / (p.lambda₀ - p.g) := by
  have hgap : 0 < p.lambda₀ - p.g := sub_pos.mpr hgain
  have hDnonneg := stockTrajectory_nonnegative model hβ hstock hD0
  have huniform_nonneg : 0 ≤ 1 - p.lambda₀ + p.g :=
    add_nonneg (sub_nonneg.mpr model.lambda₀_lt_one.le) model.g_nonneg
  have huniform_lt_one : 1 - p.lambda₀ + p.g < 1 := by linarith
  have hpointwise : ∀ t, D t ≤ max (D 0) (p.I / (p.lambda₀ - p.g)) := by
    intro t
    induction t with
    | zero => exact le_max_left _ _
    | succ t ih =>
        rw [hstock t]
        simp only [LoopParams.stockStep]
        have hmultiplier := stockMultiplier_nonneg_le model (hβ t)
        have hcoefficient : p.s (β t) + p.g ≤ 1 - p.lambda₀ + p.g := by
          linarith [hmultiplier.2]
        have hstep := mul_le_mul hcoefficient ih (hDnonneg t) huniform_nonneg
        have hstationary_le : p.I / (p.lambda₀ - p.g) ≤
            max (D 0) (p.I / (p.lambda₀ - p.g)) := le_max_right _ _
        have hmass : p.I ≤ (p.lambda₀ - p.g) *
            max (D 0) (p.I / (p.lambda₀ - p.g)) :=
          by simpa only [mul_comm] using (div_le_iff₀ hgap).mp hstationary_le
        nlinarith
  have hcomparison := stockTrajectory_le_arithGeom model hβ hstock hD0
  have hlimit : Tendsto (arithGeom (1 - p.lambda₀ + p.g) p.I (D 0)) atTop
      (𝓝 (p.I / (p.lambda₀ - p.g))) := by
    have hdenominator : 1 - (1 - p.lambda₀ + p.g) = p.lambda₀ - p.g := by ring
    simpa only [hdenominator] using
      tendsto_affineRecursion (1 - p.lambda₀ + p.g) p.I (D 0)
        huniform_nonneg huniform_lt_one
  have hlimsup : limsup D atTop ≤ p.I / (p.lambda₀ - p.g) := by
    calc
      limsup D atTop ≤
          limsup (arithGeom (1 - p.lambda₀ + p.g) p.I (D 0)) atTop :=
        limsup_le_limsup (Eventually.of_forall hcomparison)
          (isCoboundedUnder_le_of_le atTop hDnonneg) hlimit.isBoundedUnder_le
      _ = p.I / (p.lambda₀ - p.g) := hlimit.limsup_eq
  exact ⟨hpointwise, hlimsup⟩

/-! ## Static certificate inequality -/

/-- Paper III, equation `eq:cert`: the knob-free certificate margin. -/
def certificateMargin (p : LoopParams) : ℝ :=
  p.v * (p.lambda₀ - p.g) - 2 * p.c * p.I

/-- At every policy, stationary stock is at most the policy-free stock ceiling. -/
theorem stationaryStock_le_policyFreeBound {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) :
    p.stationaryStock β ≤ p.I / (p.lambda₀ - p.g) := by
  have hgap : 0 < p.lambda₀ - p.g := sub_pos.mpr hgain
  have hmultiplier := stockMultiplier_nonneg_le model hβ
  have hdenominator : 0 < 1 - p.s β - p.g := by linarith [hmultiplier.2]
  have hdenominator_order : p.lambda₀ - p.g ≤ 1 - p.s β - p.g := by
    linarith [hmultiplier.2]
  simp only [LoopParams.stationaryStock]
  apply (div_le_div_iff₀ hdenominator hgap).2
  exact mul_le_mul_of_nonneg_left hdenominator_order model.I_pos.le

/--
The three-step inequality chain in Paper III's proof of `thm:cert`, stated for
every stock below the policy-free ceiling.
-/
theorem gradU_le_neg_certificate {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) (hcertificate : 0 ≤ certificateMargin p)
    {β D : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1)
    (hD : D ≤ p.I / (p.lambda₀ - p.g)) :
    p.gradU β D ≤ -p.v * p.c * β := by
  have hgap : 0 < p.lambda₀ - p.g := sub_pos.mpr hgain
  have hcβ_nonneg : 0 ≤ 1 - p.c * β := by
    have hproduct : p.c * β ≤ p.c := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hβ.2 model.c_pos.le
    linarith [model.c_lt_one.le]
  have hfactor_nonneg : 0 ≤ 2 * p.c * (1 - p.c * β) :=
    mul_nonneg (mul_nonneg (by norm_num) model.c_pos.le) hcβ_nonneg
  have hstockTerm := mul_le_mul_of_nonneg_left hD hfactor_nonneg
  have hratio : 2 * p.c * p.I / (p.lambda₀ - p.g) ≤ p.v := by
    apply (div_le_iff₀ hgap).2
    simp only [certificateMargin] at hcertificate
    nlinarith
  have hratioWeighted := mul_le_mul_of_nonneg_left hratio hcβ_nonneg
  have hstockTerm' : 2 * p.c * (1 - p.c * β) * D ≤
      (1 - p.c * β) * (2 * p.c * p.I / (p.lambda₀ - p.g)) := by
    calc
      2 * p.c * (1 - p.c * β) * D ≤
          2 * p.c * (1 - p.c * β) * (p.I / (p.lambda₀ - p.g)) := hstockTerm
      _ = (1 - p.c * β) * (2 * p.c * p.I / (p.lambda₀ - p.g)) := by ring
  calc
    p.gradU β D ≤
        -p.v + (1 - p.c * β) * (2 * p.c * p.I / (p.lambda₀ - p.g)) := by
      simp only [LoopParams.gradU]
      simpa only [add_comm] using add_le_add_left hstockTerm' (-p.v)
    _ ≤ -p.v + (1 - p.c * β) * p.v := by
      simpa only [add_comm] using add_le_add_left hratioWeighted (-p.v)
    _ = -p.v * p.c * β := by ring

/--
Paper III, Theorem 4.3 (`thm:cert`), civic_loops.tex:249, static clause:
`G_g(β) ≤ -vcβ`, strictly negative for every positive policy.
-/
theorem stationaryGradient_le_neg_certificate {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hcertificate : 0 ≤ certificateMargin p) {β : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) :
    p.G β ≤ -p.v * p.c * β := by
  have hstock := stationaryStock_le_policyFreeBound model hgain hβ
  have hgradient := gradU_le_neg_certificate model hgain hcertificate hβ hstock
  convert hgradient using 1
  simp only [LoopParams.G, LoopParams.gradU, LoopParams.stationaryStock]
  ring

/-- Under the certificate, the stationary gradient is strictly negative at every `β > 0`. -/
theorem stationaryGradient_neg_of_pos {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hcertificate : 0 ≤ certificateMargin p) {β : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) (hβpos : 0 < β) :
    p.G β < 0 := by
  have hbound := stationaryGradient_le_neg_certificate model hgain hcertificate hβ
  have hpositive : 0 < p.v * p.c * β := mul_pos (mul_pos model.v_pos model.c_pos) hβpos
  have hnegative : -p.v * p.c * β < 0 := by nlinarith
  exact hbound.trans_lt hnegative

/-! ## Strict-margin refinement

`civic_loops.tex:247` asserts that heavy-ball momentum enters Definition 1's
class because a uniformly one-signed gradient "under the certificate happens
after a transient", but does not derive it.  It does hold, for every *strict*
margin: the two results below give a gradient bound that is uniform on the whole
policy interval, including at `β = 0`, where the sharp-margin bound `-v c β`
degenerates.  Only the boundary `m = 0` is uncovered, and the safe-side decision
rule of `prop:safe` never certifies there. -/

/--
Under a strictly positive certificate margin the satisfaction gradient is bounded
away from zero uniformly on `β ∈ [0,1]`, not merely by `-v c β`.
-/
theorem gradU_le_neg_strictMargin {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) (hmargin : 0 < certificateMargin p)
    {β D : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1)
    (hD : D ≤ p.I / (p.lambda₀ - p.g)) :
    p.gradU β D ≤ -((1 - p.c) * (certificateMargin p / (p.lambda₀ - p.g))) := by
  have hgap : 0 < p.lambda₀ - p.g := sub_pos.mpr hgain
  have hgapne : p.lambda₀ - p.g ≠ 0 := ne_of_gt hgap
  have hr_pos : 0 < certificateMargin p / (p.lambda₀ - p.g) := div_pos hmargin hgap
  have hkey : 2 * p.c * (p.I / (p.lambda₀ - p.g))
      = p.v - certificateMargin p / (p.lambda₀ - p.g) := by
    simp only [certificateMargin]
    field_simp
    ring
  have hcβ_nonneg : 0 ≤ 1 - p.c * β := by
    nlinarith [hβ.1, hβ.2, model.c_pos, model.c_lt_one]
  have hcβ_ge : 1 - p.c ≤ 1 - p.c * β := by nlinarith [hβ.2, model.c_pos]
  have hfactor_nonneg : 0 ≤ 2 * p.c * (1 - p.c * β) :=
    mul_nonneg (mul_nonneg (by norm_num) model.c_pos.le) hcβ_nonneg
  have hstock : 2 * p.c * (1 - p.c * β) * D
      ≤ (1 - p.c * β) * (p.v - certificateMargin p / (p.lambda₀ - p.g)) := by
    calc
      2 * p.c * (1 - p.c * β) * D
          ≤ 2 * p.c * (1 - p.c * β) * (p.I / (p.lambda₀ - p.g)) :=
            mul_le_mul_of_nonneg_left hD hfactor_nonneg
      _ = (1 - p.c * β) * (2 * p.c * (p.I / (p.lambda₀ - p.g))) := by ring
      _ = (1 - p.c * β) * (p.v - certificateMargin p / (p.lambda₀ - p.g)) := by
            rw [hkey]
  simp only [LoopParams.gradU]
  nlinarith [hstock, hcβ_ge, hr_pos, model.v_pos, model.c_pos, hβ.1, hβ.2,
    mul_nonneg (mul_nonneg model.v_pos.le model.c_pos.le) hβ.1,
    mul_nonneg (mul_nonneg model.c_pos.le hr_pos.le) (sub_nonneg.mpr hβ.2)]

/--
Consequence of `gradU_le_neg_strictMargin`: below the stock ceiling a strict
margin makes the gradient uniformly one-signed, which is the tail hypothesis the
heavy-ball rule needs to satisfy Definition 1.
-/
theorem gradU_neg_strictMargin {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) (hmargin : 0 < certificateMargin p)
    {β D : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1)
    (hD : D ≤ p.I / (p.lambda₀ - p.g)) :
    p.gradU β D < 0 := by
  have hgap : 0 < p.lambda₀ - p.g := sub_pos.mpr hgain
  have hr_pos : 0 < certificateMargin p / (p.lambda₀ - p.g) := div_pos hmargin hgap
  have hc : 0 < 1 - p.c := sub_pos.mpr model.c_lt_one
  have := gradU_le_neg_strictMargin model hgain hmargin hβ hD
  nlinarith [mul_pos hc hr_pos]

/--
Paper III, Corollary 4.4 (`cor:strict`), civic_loops.tex:265: a strictly
positive certificate margin yields the paper's full three-link gradient
bound, uniformly over every policy and every stock below the policy-free
ceiling.
-/
theorem strictMarginCertificate {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) (hmargin : 0 < certificateMargin p) :
    ∀ β ∈ Icc (0 : ℝ) 1, ∀ D, D ≤ p.I / (p.lambda₀ - p.g) →
      p.gradU β D ≤
          -p.v * p.c * β -
            (1 - p.c * β) * (certificateMargin p / (p.lambda₀ - p.g)) ∧
      -p.v * p.c * β -
            (1 - p.c * β) * (certificateMargin p / (p.lambda₀ - p.g)) ≤
          -((1 - p.c) * (certificateMargin p / (p.lambda₀ - p.g))) ∧
      -((1 - p.c) * (certificateMargin p / (p.lambda₀ - p.g))) < 0 := by
  intro β hβ D hD
  have hgap : 0 < p.lambda₀ - p.g := sub_pos.mpr hgain
  have hr_pos : 0 < certificateMargin p / (p.lambda₀ - p.g) := div_pos hmargin hgap
  have hkey : 2 * p.c * (p.I / (p.lambda₀ - p.g)) =
      p.v - certificateMargin p / (p.lambda₀ - p.g) := by
    simp only [certificateMargin]
    field_simp
    ring
  have hcβ_nonneg : 0 ≤ 1 - p.c * β := by
    nlinarith [hβ.1, hβ.2, model.c_pos, model.c_lt_one]
  have hfactor_nonneg : 0 ≤ 2 * p.c * (1 - p.c * β) :=
    mul_nonneg (mul_nonneg (by norm_num) model.c_pos.le) hcβ_nonneg
  have hstock : 2 * p.c * (1 - p.c * β) * D ≤
      (1 - p.c * β) *
        (p.v - certificateMargin p / (p.lambda₀ - p.g)) := by
    calc
      2 * p.c * (1 - p.c * β) * D ≤
          2 * p.c * (1 - p.c * β) * (p.I / (p.lambda₀ - p.g)) :=
        mul_le_mul_of_nonneg_left hD hfactor_nonneg
      _ = (1 - p.c * β) * (2 * p.c * (p.I / (p.lambda₀ - p.g))) := by ring
      _ = (1 - p.c * β) *
          (p.v - certificateMargin p / (p.lambda₀ - p.g)) := by rw [hkey]
  have hrefined : p.gradU β D ≤
      -p.v * p.c * β -
        (1 - p.c * β) * (certificateMargin p / (p.lambda₀ - p.g)) := by
    simp only [LoopParams.gradU]
    nlinarith [hstock]
  have hmiddle : -p.v * p.c * β -
        (1 - p.c * β) * (certificateMargin p / (p.lambda₀ - p.g)) ≤
      -((1 - p.c) * (certificateMargin p / (p.lambda₀ - p.g))) := by
    have hcβ_ge : 1 - p.c ≤ 1 - p.c * β := by
      nlinarith [hβ.2, model.c_pos]
    have hvβ_nonneg : 0 ≤ p.v * p.c * β :=
      mul_nonneg (mul_nonneg model.v_pos.le model.c_pos.le) hβ.1
    nlinarith
  have hstrict : -((1 - p.c) *
      (certificateMargin p / (p.lambda₀ - p.g))) < 0 := by
    have hc_pos : 0 < 1 - p.c := sub_pos.mpr model.c_lt_one
    nlinarith [mul_pos hc_pos hr_pos]
  exact ⟨hrefined, hmiddle, hstrict⟩

/-! ## Elementary fixed-point catalogue used by the certificate -/

/-- A loop equilibrium is an actual fixed point of the simultaneous loop map. -/
def IsLoopEquilibrium (p : LoopParams) (β D : ℝ) : Prop :=
  p.loopMap (β, D) = (β, D)

/-- Projecting a value strictly below a positive point of `[0,1]` remains strictly below it:
`lem:clip`(i), order transfer at the lower face. -/
theorem clipUnit_lt_of_lt_of_pos {x β : ℝ} (hx : x < β) (hβpos : 0 < β)
    (_hβone : β ≤ 1) : LoopParams.clipUnit x < β := by
  simp only [clipUnit_eq_clipTo]
  exact clipTo_lt_of_lt hx hβpos

/-- Every loop fixed point has its stock on the stationary characteristic. -/
theorem equilibrium_stock_eq_stationary {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β D : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1)
    (hequilibrium : IsLoopEquilibrium p β D) :
    D = p.stationaryStock β := by
  have hstockFixed := congrArg Prod.snd hequilibrium
  simp only [LoopParams.loopMap] at hstockFixed
  have hmultiplier := stockMultiplier_nonneg_le model hβ
  have hdenominator : 1 - p.s β - p.g ≠ 0 := by
    have : 0 < 1 - p.s β - p.g := by linarith [hmultiplier.2]
    exact this.ne'
  simp only [LoopParams.stockStep] at hstockFixed
  simp only [LoopParams.stationaryStock]
  apply (eq_div_iff hdenominator).2
  nlinarith

/--
Paper III, Theorem 4.3 (`thm:cert`), elementary fixed-point clause: under the
certificate, the calibrated corner is the unique loop equilibrium.
-/
theorem calibratedCorner_unique_equilibrium {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hcertificate : 0 ≤ certificateMargin p) :
    IsLoopEquilibrium p 0 (p.stationaryStock 0) ∧
      ∀ ⦃β D : ℝ⦄, β ∈ Icc (0 : ℝ) 1 → IsLoopEquilibrium p β D →
        β = 0 ∧ D = p.stationaryStock 0 := by
  have hzero : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hmultiplierZero := stockMultiplier_nonneg_le model hzero
  have hdenominatorZero : 1 - p.s 0 - p.g ≠ 0 := by
    have : 0 < 1 - p.s 0 - p.g := by linarith [hmultiplierZero.2, hgain]
    exact this.ne'
  have hGzero := stationaryGradient_le_neg_certificate model hgain hcertificate hzero
  have hGzero' : p.G 0 ≤ 0 := by simpa using hGzero
  have hinputZero : p.α * p.G 0 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos model.α_pos.le hGzero'
  have hclipZero : p.deferenceStep 0 (p.stationaryStock 0) = 0 := by
    have hgrad : p.gradU 0 (p.stationaryStock 0) = p.G 0 := by
      simp only [LoopParams.gradU, LoopParams.G, LoopParams.stationaryStock]
      ring
    simp only [LoopParams.deferenceStep, hgrad, zero_add]
    exact clipUnit_eq_zero_of_le hinputZero
  have hstockZero : p.stockStep 0 (p.stationaryStock 0) = p.stationaryStock 0 := by
    simp only [LoopParams.stockStep, LoopParams.stationaryStock]
    field_simp [hdenominatorZero]
    ring
  constructor
  · simp only [IsLoopEquilibrium, LoopParams.loopMap, hclipZero, hstockZero]
  · intro β D hβ hequilibrium
    have hD := equilibrium_stock_eq_stationary model hgain hβ hequilibrium
    have hβFixed := congrArg Prod.fst hequilibrium
    simp only [LoopParams.loopMap] at hβFixed
    have hβzero : β = 0 := by
      by_contra hnot
      have hβpos : 0 < β := lt_of_le_of_ne hβ.1 (Ne.symm hnot)
      have hgradient : p.gradU β D = p.G β := by
        rw [hD]
        simp only [LoopParams.gradU, LoopParams.G, LoopParams.stationaryStock]
        ring
      have hGneg := stationaryGradient_neg_of_pos model hgain hcertificate hβ hβpos
      have hstepLt : β + p.α * p.gradU β D < β := by
        rw [hgradient]
        nlinarith [mul_neg_of_pos_of_neg model.α_pos hGneg]
      have hprojectedLt := clipUnit_lt_of_lt_of_pos hstepLt hβpos hβ.2
      simp only [LoopParams.deferenceStep] at hβFixed
      linarith
    subst β
    exact ⟨rfl, hD⟩

/-! ## Sign-consistent responsive rules -/

/--
Paper III, Definition 4.2 (`def:sign`), civic_loops.tex:243, expressed directly
as a property of the trajectory generated by an otherwise arbitrary rule.
-/
structure SignConsistentResponsive (p : LoopParams) (β D : ℕ → ℝ) : Prop where
  unit_interval : ∀ t, β t ∈ Icc (0 : ℝ) 1
  sign_consistent : ∀ t, p.gradU (β t) (D t) ≤ 0 → β (t + 1) ≤ β t
  responsive : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ t, p.gradU (β t) (D t) ≤ -ε → ε ≤ β t → δ ≤ β t - β (t + 1)

/-- Projection is the identity on its target interval: `lem:clip`(ii), inactive case. -/
theorem clipUnit_eq_self {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    LoopParams.clipUnit x = x :=
  clipUnit_eq_self' hx

/-- A trajectory generated by Paper III's projected-gradient rule. -/
def IsProjectedGradientTrajectory (p : LoopParams) (β D : ℕ → ℝ) : Prop :=
  ∀ t, β (t + 1) = p.deferenceStep (β t) (D t)

/-- The projected-gradient rule at every positive rate satisfies Definition 1. -/
theorem projectedGradient_signConsistentResponsive {p : LoopParams}
    (model : LoopModelAssumptions p) {β D : ℕ → ℝ}
    (hβ0 : β 0 ∈ Icc (0 : ℝ) 1) (hupdate : IsProjectedGradientTrajectory p β D) :
    SignConsistentResponsive p β D := by
  have hunit : ∀ t, β t ∈ Icc (0 : ℝ) 1 := by
    intro t
    induction t with
    | zero => exact hβ0
    | succ t =>
        rw [hupdate t]
        exact LoopParams.clipUnit_mem _
  refine ⟨hunit, ?_, ?_⟩
  · intro t hgradient
    rw [hupdate t]
    simp only [LoopParams.deferenceStep]
    have hinput : β t + p.α * p.gradU (β t) (D t) ≤ β t := by
      have := mul_nonpos_of_nonneg_of_nonpos model.α_pos.le hgradient
      linarith
    exact (LoopParams.monotone_clipUnit hinput).trans_eq (clipUnit_eq_self (hunit t))
  · intro ε hε
    let δ : ℝ := min (p.α * ε) ε
    have hδpos : 0 < δ := by
      dsimp only [δ]
      exact lt_min (mul_pos model.α_pos hε) hε
    refine ⟨δ, hδpos, ?_⟩
    intro t hgradient hβε
    have hδstep : δ ≤ p.α * ε := min_le_left _ _
    have hδβ : δ ≤ β t := (min_le_right _ _).trans hβε
    have htarget : β t - δ ∈ Icc (0 : ℝ) 1 := by
      constructor
      · linarith
      · linarith [(hunit t).2]
    have hscaled := mul_le_mul_of_nonneg_left hgradient model.α_pos.le
    have hinput : β t + p.α * p.gradU (β t) (D t) ≤ β t - δ := by
      nlinarith
    rw [hupdate t]
    simp only [LoopParams.deferenceStep]
    have hclip := LoopParams.monotone_clipUnit hinput
    rw [clipUnit_eq_self htarget] at hclip
    linarith

/-- The increment used by a fixed-step sign rule. -/
noncomputable def fixedSignIncrement (step gradient : ℝ) : ℝ :=
  if gradient < 0 then -step else if 0 < gradient then step else 0

/-- A trajectory generated by a projected fixed-step sign rule. -/
def IsFixedSignTrajectory (p : LoopParams) (step : ℝ) (β D : ℕ → ℝ) : Prop :=
  ∀ t, β (t + 1) = LoopParams.clipUnit
    (β t + fixedSignIncrement step (p.gradU (β t) (D t)))

/-- Every positive fixed-step sign rule satisfies Definition 1. -/
theorem fixedSign_signConsistentResponsive {p : LoopParams} {step : ℝ}
    (hstep : 0 < step) {β D : ℕ → ℝ} (hβ0 : β 0 ∈ Icc (0 : ℝ) 1)
    (hupdate : IsFixedSignTrajectory p step β D) :
    SignConsistentResponsive p β D := by
  have hunit : ∀ t, β t ∈ Icc (0 : ℝ) 1 := by
    intro t
    induction t with
    | zero => exact hβ0
    | succ t =>
        rw [hupdate t]
        exact LoopParams.clipUnit_mem _
  refine ⟨hunit, ?_, ?_⟩
  · intro t hgradient
    by_cases hnegative : p.gradU (β t) (D t) < 0
    · rw [hupdate t]
      simp only [fixedSignIncrement, if_pos hnegative]
      have hinput : β t - step ≤ β t := by linarith
      simpa only [sub_eq_add_neg] using
        (LoopParams.monotone_clipUnit hinput).trans_eq (clipUnit_eq_self (hunit t))
    · have hzero : p.gradU (β t) (D t) = 0 :=
        le_antisymm hgradient (not_lt.mp hnegative)
      rw [hupdate t]
      simp only [fixedSignIncrement, hzero, lt_self_iff_false, if_false, add_zero]
      exact (clipUnit_eq_self (hunit t)).le
  · intro ε hε
    let δ : ℝ := min step ε
    have hδpos : 0 < δ := by dsimp only [δ]; exact lt_min hstep hε
    refine ⟨δ, hδpos, ?_⟩
    intro t hgradient hβε
    have hnegative : p.gradU (β t) (D t) < 0 := by linarith
    have hδstep : δ ≤ step := min_le_left _ _
    have hδβ : δ ≤ β t := (min_le_right _ _).trans hβε
    have htarget : β t - δ ∈ Icc (0 : ℝ) 1 := by
      constructor
      · linarith
      · linarith [(hunit t).2]
    have hinput : β t - step ≤ β t - δ := by linarith
    rw [hupdate t]
    simp only [fixedSignIncrement, if_pos hnegative]
    have hclip := LoopParams.monotone_clipUnit hinput
    rw [clipUnit_eq_self htarget] at hclip
    have hclip' : LoopParams.clipUnit (β t + -step) ≤ β t - δ := by
      simpa only [sub_eq_add_neg] using hclip
    linarith

/--
A two-sided multiplicative sign update: negative gradients retain a fraction
`q` of current deference, while positive gradients close the same fraction of
the remaining distance to one.
-/
noncomputable def multiplicativeSignStep (q β gradient : ℝ) : ℝ :=
  if gradient ≤ 0 then q * β else β + q * (1 - β)

/-- A trajectory generated by a projected multiplicative sign rule. -/
def IsMultiplicativeSignTrajectory (p : LoopParams) (q : ℝ) (β D : ℕ → ℝ) : Prop :=
  ∀ t, β (t + 1) = LoopParams.clipUnit
    (multiplicativeSignStep q (β t) (p.gradU (β t) (D t)))

/-- Every multiplicative sign rule with retention in `(0,1)` satisfies Definition 1. -/
theorem multiplicativeSign_signConsistentResponsive {p : LoopParams} {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) {β D : ℕ → ℝ} (hβ0 : β 0 ∈ Icc (0 : ℝ) 1)
    (hupdate : IsMultiplicativeSignTrajectory p q β D) :
    SignConsistentResponsive p β D := by
  have hunit : ∀ t, β t ∈ Icc (0 : ℝ) 1 := by
    intro t
    induction t with
    | zero => exact hβ0
    | succ t =>
        rw [hupdate t]
        exact LoopParams.clipUnit_mem _
  have hretained : ∀ t, q * β t ∈ Icc (0 : ℝ) 1 := by
    intro t
    have hβt := hunit t
    constructor
    · exact mul_nonneg hq.1.le hβt.1
    · calc
        q * β t ≤ 1 * β t := mul_le_mul_of_nonneg_right hq.2.le hβt.1
        _ ≤ 1 := by simpa only [one_mul] using hβt.2
  refine ⟨hunit, ?_, ?_⟩
  · intro t hgradient
    rw [hupdate t]
    simp only [multiplicativeSignStep, if_pos hgradient, clipUnit_eq_self (hretained t)]
    have := mul_le_mul_of_nonneg_right hq.2.le (hunit t).1
    simpa only [one_mul] using this
  · intro ε hε
    let δ : ℝ := (1 - q) * ε
    have honeSub : 0 < 1 - q := sub_pos.mpr hq.2
    have hδpos : 0 < δ := mul_pos honeSub hε
    refine ⟨δ, hδpos, ?_⟩
    intro t hgradient hβε
    have hgradientNonpos : p.gradU (β t) (D t) ≤ 0 := by linarith
    rw [hupdate t]
    simp only [multiplicativeSignStep, if_pos hgradientNonpos,
      clipUnit_eq_self (hretained t)]
    have hscaled := mul_le_mul_of_nonneg_left hβε honeSub.le
    dsimp only [δ]
    nlinarith

/-- Definition 1 imposed only after a finite transient. -/
structure EventuallySignConsistentResponsive (p : LoopParams) (β D : ℕ → ℝ) : Prop where
  unit_interval : ∀ t, β t ∈ Icc (0 : ℝ) 1
  tail : ∃ T,
    (∀ t, T ≤ t → p.gradU (β t) (D t) ≤ 0 → β (t + 1) ≤ β t) ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ t, T ≤ t → p.gradU (β t) (D t) ≤ -ε → ε ≤ β t →
        δ ≤ β t - β (t + 1)

/-- The heavy-ball update used in the numerical battery. -/
def IsHeavyBallTrajectory (p : LoopParams) (momentumRetention : ℝ)
    (β D momentum : ℕ → ℝ) : Prop :=
  ∀ t,
    momentum (t + 1) = momentumRetention * momentum t + p.α * p.gradU (β t) (D t) ∧
    β (t + 1) = LoopParams.clipUnit (β t + momentum (t + 1))

/--
Heavy-ball momentum satisfies Definition 1 after a transient if the gradient
has a uniformly negative tail. This is the conditional momentum claim in
civic_loops.tex:247.
-/
theorem heavyBall_eventuallySignConsistentResponsive {p : LoopParams}
    (model : LoopModelAssumptions p) {momentumRetention : ℝ}
    (hretention : momentumRetention ∈ Icc (0 : ℝ) 1)
    {β D momentum : ℕ → ℝ} (hβ0 : β 0 ∈ Icc (0 : ℝ) 1)
    (hupdate : IsHeavyBallTrajectory p momentumRetention β D momentum)
    (hnegativeTail : ∃ T κ, 0 < κ ∧
      ∀ t, T ≤ t → p.gradU (β t) (D t) ≤ -κ) :
    EventuallySignConsistentResponsive p β D := by
  have hunit : ∀ t, β t ∈ Icc (0 : ℝ) 1 := by
    intro t
    induction t with
    | zero => exact hβ0
    | succ t =>
        rw [(hupdate t).2]
        exact LoopParams.clipUnit_mem _
  obtain ⟨T, κ, hκpos, hgradientTail⟩ := hnegativeTail
  have hdecrement : 0 < p.α * κ := mul_pos model.α_pos hκpos
  have hcross : ∃ n, momentum (T + n) ≤ 0 := by
    by_contra hnever
    push Not at hnever
    have hlinear : ∀ n, momentum (T + n) ≤
        momentum T - (n : ℝ) * (p.α * κ) := by
      intro n
      induction n with
      | zero =>
          simpa only [Nat.cast_zero, zero_mul, sub_zero, Nat.add_zero] using
            (le_refl (momentum T))
      | succ n ih =>
          have hmpos : 0 < momentum (T + n) := hnever n
          have hretained : momentumRetention * momentum (T + n) ≤
              momentum (T + n) := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hretention.2 hmpos.le
          have hgradient := hgradientTail (T + n) (by omega)
          have hscaled := mul_le_mul_of_nonneg_left hgradient model.α_pos.le
          have hrecurrence := (hupdate (T + n)).1
          have hnext : momentum (T + n + 1) ≤
              momentum (T + n) - p.α * κ := by
            rw [hrecurrence]
            linarith
          norm_num [Nat.cast_succ] at ⊢
          simpa only [Nat.add_assoc] using (show
            momentum (T + n + 1) ≤
              momentum T - ((n : ℝ) + 1) * (p.α * κ) by nlinarith)
    obtain ⟨n, hn⟩ := exists_nat_gt (momentum T / (p.α * κ))
    have hproduct : momentum T < (n : ℝ) * (p.α * κ) :=
      (div_lt_iff₀ hdecrement).mp hn
    nlinarith [hnever n, hlinear n]
  obtain ⟨n, hn⟩ := hcross
  let S : ℕ := T + n
  have hTS : T ≤ S := by dsimp only [S]; omega
  have hmS : momentum S ≤ 0 := by simpa only [S] using hn
  have hmnonposFrom : ∀ j, momentum (S + j) ≤ 0 := by
    intro j
    induction j with
    | zero => simpa only [Nat.add_zero] using hmS
    | succ j ih =>
        have hgradient := hgradientTail (S + j) (by omega)
        have hretained : momentumRetention * momentum (S + j) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hretention.1 ih
        have hscaled : p.α * p.gradU (β (S + j)) (D (S + j)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos model.α_pos.le (by linarith)
        have hrecurrence := (hupdate (S + j)).1
        have hnext : momentum (S + j + 1) ≤ 0 := by rw [hrecurrence]; linarith
        simpa only [Nat.add_assoc] using hnext
  have hmnonpos : ∀ t, S ≤ t → momentum t ≤ 0 := by
    intro t ht
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ht
    exact hmnonposFrom j
  refine ⟨hunit, S, ?_, ?_⟩
  · intro t ht hgradient
    have hmterm : momentumRetention * momentum t ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hretention.1 (hmnonpos t ht)
    have hgterm : p.α * p.gradU (β t) (D t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos model.α_pos.le hgradient
    have hmnext : momentum (t + 1) ≤ 0 := by rw [(hupdate t).1]; linarith
    rw [(hupdate t).2]
    have hinput : β t + momentum (t + 1) ≤ β t := by linarith
    exact (LoopParams.monotone_clipUnit hinput).trans_eq (clipUnit_eq_self (hunit t))
  · intro ε hε
    let δ : ℝ := min (p.α * ε) ε
    have hδpos : 0 < δ := by
      dsimp only [δ]
      exact lt_min (mul_pos model.α_pos hε) hε
    refine ⟨δ, hδpos, ?_⟩
    intro t ht hgradient hβε
    have hmterm : momentumRetention * momentum t ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hretention.1 (hmnonpos t ht)
    have hscaled := mul_le_mul_of_nonneg_left hgradient model.α_pos.le
    have hmnext : momentum (t + 1) ≤ -p.α * ε := by
      rw [(hupdate t).1]
      linarith
    have hδstep : δ ≤ p.α * ε := min_le_left _ _
    have hδβ : δ ≤ β t := (min_le_right _ _).trans hβε
    have htarget : β t - δ ∈ Icc (0 : ℝ) 1 := by
      constructor
      · linarith
      · linarith [(hunit t).2]
    have hinput : β t + momentum (t + 1) ≤ β t - δ := by linarith
    rw [(hupdate t).2]
    have hclip := LoopParams.monotone_clipUnit hinput
    rw [clipUnit_eq_self htarget] at hclip
    linarith

/-- The certificate inequality with an additive stock-ceiling error. -/
theorem gradU_le_neg_certificate_add_error {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hcertificate : 0 ≤ certificateMargin p) {β D δ : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) (hδ : 0 ≤ δ)
    (hD : D ≤ p.I / (p.lambda₀ - p.g) + δ) :
    p.gradU β D ≤ -p.v * p.c * β + 2 * p.c * δ := by
  have hgap : 0 < p.lambda₀ - p.g := sub_pos.mpr hgain
  have hcβ_nonneg : 0 ≤ 1 - p.c * β := by
    have hproduct : p.c * β ≤ p.c := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hβ.2 model.c_pos.le
    linarith [model.c_lt_one.le]
  have hcβ_le_one : 1 - p.c * β ≤ 1 := by
    have : 0 ≤ p.c * β := mul_nonneg model.c_pos.le hβ.1
    linarith
  have hfactor_nonneg : 0 ≤ 2 * p.c * (1 - p.c * β) :=
    mul_nonneg (mul_nonneg (by norm_num) model.c_pos.le) hcβ_nonneg
  have hstockTerm := mul_le_mul_of_nonneg_left hD hfactor_nonneg
  have hratio : 2 * p.c * p.I / (p.lambda₀ - p.g) ≤ p.v := by
    apply (div_le_iff₀ hgap).2
    simp only [certificateMargin] at hcertificate
    nlinarith
  have hratioWeighted := mul_le_mul_of_nonneg_left hratio hcβ_nonneg
  have herrorWeighted : 2 * p.c * (1 - p.c * β) * δ ≤ 2 * p.c * δ := by
    have := mul_le_mul_of_nonneg_right hcβ_le_one hδ
    nlinarith [model.c_pos]
  have hstockTerm' : 2 * p.c * (1 - p.c * β) * D ≤
      (1 - p.c * β) * (2 * p.c * p.I / (p.lambda₀ - p.g)) +
        2 * p.c * (1 - p.c * β) * δ := by
    calc
      2 * p.c * (1 - p.c * β) * D ≤
          2 * p.c * (1 - p.c * β) *
            (p.I / (p.lambda₀ - p.g) + δ) := hstockTerm
      _ = (1 - p.c * β) * (2 * p.c * p.I / (p.lambda₀ - p.g)) +
          2 * p.c * (1 - p.c * β) * δ := by ring
  have hcombined : 2 * p.c * (1 - p.c * β) * D ≤
      (1 - p.c * β) * p.v + 2 * p.c * δ :=
    hstockTerm'.trans (add_le_add hratioWeighted herrorWeighted)
  calc
    p.gradU β D ≤ -p.v + (1 - p.c * β) * p.v + 2 * p.c * δ := by
      simp only [LoopParams.gradU]
      linarith
    _ = -p.v * p.c * β + 2 * p.c * δ := by ring

/-- A nonnegative sequence with a fixed decrement above a threshold crosses that threshold. -/
theorem exists_lt_of_uniform_descent {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n)
    {ε δ : ℝ} (hδ : 0 < δ) (hstep : ∀ n, ε ≤ u n → u (n + 1) ≤ u n - δ) :
    ∃ n, u n < ε := by
  by_contra hnever
  push Not at hnever
  have hlinear : ∀ n, u n ≤ u 0 - (n : ℝ) * δ := by
    intro n
    induction n with
    | zero =>
        simpa only [Nat.cast_zero, zero_mul, sub_zero] using (le_refl (u 0))
    | succ n ih =>
        have hnext := hstep n (hnever n)
        norm_num [Nat.cast_succ] at ⊢
        nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt (u 0 / δ)
  have hproduct : u 0 < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hn
  nlinarith [hu n, hlinear n]

/-- A nonnegative sequence under a stable contraction and a vanishing error tends to zero. -/
theorem tendsto_zero_of_nonnegative_contraction {u r : ℕ → ℝ} {A : ℝ}
    (hA_nonneg : 0 ≤ A) (hA_lt_one : A < 1) (hu : ∀ n, 0 ≤ u n)
    (hstep : ∀ n, u (n + 1) ≤ A * u n + r n)
    (hr : Tendsto r atTop (nhds 0)) :
    Tendsto u atTop (nhds 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun n ↦ ha.trans_le (hu n)
  · intro ε hε
    let b : ℝ := (1 - A) * ε / 2
    have honeSub : 0 < 1 - A := sub_pos.mpr hA_lt_one
    have hb : 0 < b := div_pos (mul_pos honeSub hε) (by norm_num)
    have hrEventually : ∀ᶠ n in atTop, r n < b := (tendsto_order.1 hr).2 b hb
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hrEventually
    have hcomparison : ∀ n, u (N + n) ≤ arithGeom A b (u N) n := by
      intro n
      induction n with
      | zero => exact le_rfl
      | succ n ih =>
          calc
            u (N + (n + 1)) = u (N + n + 1) := by simp only [Nat.add_assoc]
            _ ≤ A * u (N + n) + r (N + n) := hstep (N + n)
            _ ≤ A * arithGeom A b (u N) n + b :=
              add_le_add (mul_le_mul_of_nonneg_left ih hA_nonneg)
                (hN (N + n) (by omega)).le
            _ = arithGeom A b (u N) (n + 1) := by rw [arithGeom_succ]
    have hlimitValue : b / (1 - A) = ε / 2 := by
      dsimp only [b]
      field_simp [honeSub.ne']
    have hlimit : Tendsto (arithGeom A b (u N)) atTop (nhds (ε / 2)) := by
      simpa only [hlimitValue] using
        tendsto_affineRecursion A b (u N) hA_nonneg hA_lt_one
    have hcomparisonEventually : ∀ᶠ n in atTop, arithGeom A b (u N) n < ε :=
      (tendsto_order.1 hlimit).2 ε (by linarith)
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hcomparisonEventually
    refine Filter.eventually_atTop.2 ⟨N + M, ?_⟩
    intro n hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    have huBound : u ((N + M) + j) ≤ arithGeom A b (u N) (M + j) := by
      simpa only [Nat.add_assoc] using hcomparison (M + j)
    exact huBound.trans_lt (hM (M + j) (Nat.le_add_right M j))

/--
Under a responsive certified rule, the stock enters its exact policy-free
ceiling in finite time.
-/
theorem stockTrajectory_eventually_le_policyFreeBound {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hcertificate : 0 ≤ certificateMargin p) {β D : ℕ → ℝ}
    (hstock : IsStockTrajectory p β D) (hD0 : 0 ≤ D 0)
    (rule : SignConsistentResponsive p β D) :
    ∃ T, ∀ t, T ≤ t → D t ≤ p.I / (p.lambda₀ - p.g) := by
  let a : ℝ := 1 - p.lambda₀ + p.g
  let L : ℝ := p.I / (p.lambda₀ - p.g)
  let q : ℝ := (1 - p.lambda₀) - p.s (1 / 2)
  let e : ℝ := min (p.v / 8) (q * L / 2)
  have hgap : 0 < p.lambda₀ - p.g := sub_pos.mpr hgain
  have ha_nonneg : 0 ≤ a := by
    dsimp only [a]
    exact add_nonneg (sub_nonneg.mpr model.lambda₀_lt_one.le) model.g_nonneg
  have ha_lt_one : a < 1 := by dsimp only [a]; linarith
  have hLpos : 0 < L := div_pos model.I_pos hgap
  have hhalf : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hsHalfLt := stockMultiplier_strictMonoOn model hhalf hone (by norm_num : (1 / 2 : ℝ) < 1)
  have hsOne : p.s 1 = 1 - p.lambda₀ := by
    simp only [LoopParams.s, sub_self, mul_zero, sub_zero, one_pow, mul_one]
  rw [hsOne] at hsHalfLt
  have hqpos : 0 < q := by dsimp only [q]; linarith
  have hepos : 0 < e := by
    dsimp only [e]
    exact lt_min (div_pos model.v_pos (by norm_num))
      (div_pos (mul_pos hqpos hLpos) (by norm_num))
  have hDnonneg := stockTrajectory_nonnegative model rule.unit_interval hstock hD0
  have hcomparison := stockTrajectory_le_arithGeom model rule.unit_interval hstock hD0
  have hlimit : Tendsto (arithGeom a p.I (D 0)) atTop (𝓝 L) := by
    have hdenominator : 1 - a = p.lambda₀ - p.g := by dsimp only [a]; ring
    dsimp only [L]
    simpa only [hdenominator] using tendsto_affineRecursion a p.I (D 0) ha_nonneg ha_lt_one
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlimit e hepos
  have hcomparisonUpper : ∀ t, N ≤ t → arithGeom a p.I (D 0) t < L + e := by
    intro t ht
    have habs := hN t ht
    rw [Real.dist_eq] at habs
    have hdiff : arithGeom a p.I (D 0) t - L < e :=
      (le_abs_self _).trans_lt habs
    linarith
  have hgradientHigh : ∀ t, N ≤ t → (1 / 2 : ℝ) ≤ β t →
      p.gradU (β t) (D t) ≤ -(p.v * p.c / 4) := by
    intro t ht hβhalf
    have hDt : D t ≤ L + e :=
      (hcomparison t).trans (hcomparisonUpper t ht).le
    have he_v : e ≤ p.v / 8 := by exact min_le_left _ _
    have he_vc : 2 * p.c * e ≤ p.v * p.c / 4 := by
      have hscaled : (2 * p.c) * e ≤ (2 * p.c) * (p.v / 8) :=
        mul_le_mul_of_nonneg_left he_v (mul_nonneg (by norm_num) model.c_pos.le)
      nlinarith
    have hβscaled : (p.v * p.c) * (1 / 2) ≤ (p.v * p.c) * β t :=
      mul_le_mul_of_nonneg_left hβhalf (mul_nonneg model.v_pos.le model.c_pos.le)
    have hnegative : -p.v * p.c * β t ≤ -(p.v * p.c / 2) := by
      nlinarith
    have hbound := gradU_le_neg_certificate_add_error model hgain hcertificate
      (rule.unit_interval t) hepos.le hDt
    exact hbound.trans (by nlinarith)
  let r : ℝ := min (p.v * p.c / 4) (1 / 2)
  have hrpos : 0 < r := by
    dsimp only [r]
    exact lt_min (div_pos (mul_pos model.v_pos model.c_pos) (by norm_num)) (by norm_num)
  have hrGradient : r ≤ p.v * p.c / 4 := min_le_left _ _
  have hrBeta : r ≤ (1 / 2 : ℝ) := min_le_right _ _
  obtain ⟨d, hdpos, hresponsive⟩ := rule.responsive r hrpos
  have hbelowHalf : ∃ n, β (N + n) < (1 / 2 : ℝ) := by
    apply exists_lt_of_uniform_descent (u := fun n => β (N + n))
    · intro n
      exact (rule.unit_interval (N + n)).1
    · exact hdpos
    · intro n hn
      have hgrad := hgradientHigh (N + n) (by omega) hn
      have hdec := hresponsive (N + n) (hgrad.trans (neg_le_neg hrGradient))
        (hrBeta.trans hn)
      have hstep : β (N + n + 1) ≤ β (N + n) - d := by linarith
      simpa only [Nat.add_assoc] using hstep
  obtain ⟨n, hn⟩ := hbelowHalf
  let t : ℕ := N + n
  have htN : N ≤ t := by dsimp only [t]; omega
  have hβt : β t ∈ Icc (0 : ℝ) 1 := rule.unit_interval t
  have hβtHalf : β t < (1 / 2 : ℝ) := by simpa only [t] using hn
  have hsβ_le : p.s (β t) ≤ p.s (1 / 2) :=
    (stockMultiplier_strictMonoOn model hβt hhalf hβtHalf).le
  have hcoefficient : p.s (β t) + p.g ≤ p.s (1 / 2) + p.g :=
    by simpa only [add_comm] using add_le_add_right hsβ_le p.g
  have hhalfCoefficient_nonneg : 0 ≤ p.s (1 / 2) + p.g :=
    add_nonneg (stockMultiplier_nonneg_le model hhalf).1 model.g_nonneg
  have hhalfCoefficient_le_one : p.s (1 / 2) + p.g ≤ 1 := by
    linarith [hsHalfLt, hgain]
  have hDt : D t ≤ L + e := (hcomparison t).trans (hcomparisonUpper t htN).le
  have hmul := mul_le_mul hcoefficient hDt (hDnonneg t) hhalfCoefficient_nonneg
  have hfixed : a * L + p.I = L := by
    dsimp only [a, L]
    field_simp [hgap.ne']
    ring
  have hdecomp : p.s (1 / 2) + p.g = a - q := by
    dsimp only [a, q]
    ring
  have he_qL : e ≤ q * L / 2 := min_le_right _ _
  have herror : (p.s (1 / 2) + p.g) * e ≤ e :=
    mul_le_of_le_one_left hepos.le hhalfCoefficient_le_one
  have hnext : D (t + 1) ≤ L := by
    rw [hstock t]
    simp only [LoopParams.stockStep]
    calc
      (p.s (β t) + p.g) * D t + p.I ≤
          (p.s (1 / 2) + p.g) * (L + e) + p.I := by
            simpa only [add_comm] using add_le_add_right hmul p.I
      _ ≤ L := by
        rw [hdecomp]
        nlinarith
  let S : ℕ := t + 1
  have hstay : ∀ k, D (S + k) ≤ L := by
    intro k
    induction k with
    | zero => simpa only [S, Nat.add_zero] using hnext
    | succ k ih =>
        have hmultiplier := stockMultiplier_nonneg_le model (rule.unit_interval (S + k))
        have hcoefficient' : p.s (β (S + k)) + p.g ≤ a := by
          dsimp only [a]
          linarith [hmultiplier.2]
        have hstep := mul_le_mul hcoefficient' ih (hDnonneg (S + k)) ha_nonneg
        calc
          D (S + (k + 1)) = D (S + k + 1) := by
            simp only [S, Nat.add_assoc]
          _ = (p.s (β (S + k)) + p.g) * D (S + k) + p.I := by
            rw [hstock (S + k)]
            rfl
          _ ≤ a * L + p.I := by
            simpa only [add_comm] using add_le_add_right hstep p.I
          _ = L := hfixed
  refine ⟨S, ?_⟩
  intro k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact hstay j

/-- Under the certificate, every sign-consistent responsive policy converges to zero. -/
theorem deference_tendsto_zero {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) (hcertificate : 0 ≤ certificateMargin p)
    {β D : ℕ → ℝ} (hstock : IsStockTrajectory p β D) (hD0 : 0 ≤ D 0)
    (rule : SignConsistentResponsive p β D) :
    Tendsto β atTop (nhds 0) := by
  obtain ⟨T, hT⟩ := stockTrajectory_eventually_le_policyFreeBound
    model hgain hcertificate hstock hD0 rule
  have hgradient : ∀ t, T ≤ t →
      p.gradU (β t) (D t) ≤ -p.v * p.c * β t := by
    intro t ht
    exact gradU_le_neg_certificate model hgain hcertificate
      (rule.unit_interval t) (hT t ht)
  have hstep : ∀ t, T ≤ t → β (t + 1) ≤ β t := by
    intro t ht
    apply rule.sign_consistent
    have hβnonneg := (rule.unit_interval t).1
    exact (hgradient t ht).trans (by
      have : 0 ≤ p.v * p.c * β t :=
        mul_nonneg (mul_nonneg model.v_pos.le model.c_pos.le) hβnonneg
      nlinarith)
  have hanti : Antitone (fun n ↦ β (T + n)) := by
    apply antitone_nat_of_succ_le
    intro n
    have := hstep (T + n) (by omega)
    simpa only [Nat.add_assoc] using this
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun n ↦ ha.trans_le (rule.unit_interval n).1
  · intro b hb
    let r : ℝ := min (p.v * p.c * b) b
    have hvcbpos : 0 < p.v * p.c * b :=
      mul_pos (mul_pos model.v_pos model.c_pos) hb
    have hrpos : 0 < r := by
      dsimp only [r]
      exact lt_min hvcbpos hb
    have hrGradient : r ≤ p.v * p.c * b := min_le_left _ _
    have hrBeta : r ≤ b := min_le_right _ _
    obtain ⟨d, hdpos, hresponsive⟩ := rule.responsive r hrpos
    have hbelow : ∃ n, β (T + n) < b := by
      apply exists_lt_of_uniform_descent (u := fun n ↦ β (T + n))
      · intro n
        exact (rule.unit_interval (T + n)).1
      · exact hdpos
      · intro n hn
        have hscaled : p.v * p.c * b ≤ p.v * p.c * β (T + n) :=
          mul_le_mul_of_nonneg_left hn (mul_nonneg model.v_pos.le model.c_pos.le)
        have hgrad : p.gradU (β (T + n)) (D (T + n)) ≤ -r :=
          (hgradient (T + n) (by omega)).trans (by nlinarith)
        have hdec := hresponsive (T + n) hgrad (hrBeta.trans hn)
        have hnext : β (T + n + 1) ≤ β (T + n) - d := by linarith
        simpa only [Nat.add_assoc] using hnext
    obtain ⟨n, hn⟩ := hbelow
    refine Filter.eventually_atTop.2 ⟨T + n, ?_⟩
    intro t ht
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ht
    have hle := hanti (Nat.le_add_right n j)
    have hle' : β ((T + n) + j) ≤ β (T + n) := by
      simpa only [Nat.add_assoc] using hle
    exact hle'.trans_lt hn

/-- If deference converges to zero, the stable stock recursion converges to calibrated stock. -/
theorem stock_tendsto_calibrated {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β D : ℕ → ℝ}
    (hstock : IsStockTrajectory p β D)
    (hβ : ∀ t, β t ∈ Icc (0 : ℝ) 1) (hβlimit : Tendsto β atTop (nhds 0)) :
    Tendsto D atTop (nhds (p.stationaryStock 0)) := by
  let A : ℝ := 1 - p.lambda₀ + p.g
  let L : ℝ := p.stationaryStock 0
  let u : ℕ → ℝ := fun t ↦ |D t - L|
  let r : ℕ → ℝ := fun t ↦
    |((p.s (β t) + p.g) - (p.s 0 + p.g)) * L|
  have hA_nonneg : 0 ≤ A := by
    dsimp only [A]
    exact add_nonneg (sub_nonneg.mpr model.lambda₀_lt_one.le) model.g_nonneg
  have hA_lt_one : A < 1 := by dsimp only [A]; linarith
  have hmultiplierZero := stockMultiplier_nonneg_le model (by norm_num : (0 : ℝ) ∈ Icc 0 1)
  have hdenominator : 0 < 1 - p.s 0 - p.g := by linarith [hmultiplierZero.2]
  have hfixed : (p.s 0 + p.g) * L + p.I = L := by
    dsimp only [L, LoopParams.stationaryStock]
    field_simp [hdenominator.ne']
    ring
  have hsLimit : Tendsto (fun t ↦ p.s (β t)) atTop (nhds (p.s 0)) :=
    (p.hasDerivAt_s 0).continuousAt.tendsto.comp hβlimit
  have hcoefficientLimit : Tendsto (fun t ↦ p.s (β t) + p.g) atTop
      (nhds (p.s 0 + p.g)) := hsLimit.add tendsto_const_nhds
  have hcoefficientConstant : Tendsto (fun _ : ℕ ↦ p.s 0 + p.g) atTop
      (nhds (p.s 0 + p.g)) := tendsto_const_nhds
  have herrorCoefficient : Tendsto
      (fun t ↦ (p.s (β t) + p.g) - (p.s 0 + p.g)) atTop (nhds 0) := by
    simpa only [sub_self] using hcoefficientLimit.sub hcoefficientConstant
  have hconstantLimit : Tendsto (fun _ : ℕ ↦ L) atTop (nhds L) := tendsto_const_nhds
  have hrLimit : Tendsto r atTop (nhds 0) := by
    have hproduct := herrorCoefficient.mul hconstantLimit
    have habsolute := hproduct.abs
    simpa only [r, zero_mul, abs_zero] using habsolute
  have huNonneg : ∀ t, 0 ≤ u t := fun t ↦ abs_nonneg _
  have huStep : ∀ t, u (t + 1) ≤ A * u t + r t := by
    intro t
    have hmultiplier := stockMultiplier_nonneg_le model (hβ t)
    have hcoefficientNonneg : 0 ≤ p.s (β t) + p.g :=
      add_nonneg hmultiplier.1 model.g_nonneg
    have hcoefficientLe : p.s (β t) + p.g ≤ A := by
      dsimp only [A]
      linarith [hmultiplier.2]
    have herrorIdentity : D (t + 1) - L =
        (p.s (β t) + p.g) * (D t - L) +
          ((p.s (β t) + p.g) - (p.s 0 + p.g)) * L := by
      rw [hstock t]
      simp only [LoopParams.stockStep]
      linear_combination hfixed
    dsimp only [u, r]
    rw [herrorIdentity]
    calc
      |(p.s (β t) + p.g) * (D t - L) +
          ((p.s (β t) + p.g) - (p.s 0 + p.g)) * L| ≤
          |(p.s (β t) + p.g) * (D t - L)| +
            |((p.s (β t) + p.g) - (p.s 0 + p.g)) * L| := abs_add_le _ _
      _ = (p.s (β t) + p.g) * |D t - L| +
            |((p.s (β t) + p.g) - (p.s 0 + p.g)) * L| := by
          rw [abs_mul, abs_of_nonneg hcoefficientNonneg]
      _ ≤ A * |D t - L| +
            |((p.s (β t) + p.g) - (p.s 0 + p.g)) * L| :=
          by
            exact add_le_add
              (mul_le_mul_of_nonneg_right hcoefficientLe (abs_nonneg _)) le_rfl
  have huLimit := tendsto_zero_of_nonnegative_contraction
    hA_nonneg hA_lt_one huNonneg huStep hrLimit
  apply tendsto_iff_dist_tendsto_zero.2
  simpa only [u, L, Real.dist_eq] using huLimit

/-- The certificate is unchanged if Definition 1 starts only after a finite transient. -/
theorem eventualRule_tendsto_calibrated {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hcertificate : 0 ≤ certificateMargin p) {β D : ℕ → ℝ}
    (hstock : IsStockTrajectory p β D) (hD0 : 0 ≤ D 0)
    (rule : EventuallySignConsistentResponsive p β D) :
    Tendsto β atTop (nhds 0) ∧
      Tendsto D atTop (nhds (p.stationaryStock 0)) := by
  obtain ⟨T, hsign, hresponsive⟩ := rule.tail
  let βTail : ℕ → ℝ := fun n ↦ β (n + T)
  let DTail : ℕ → ℝ := fun n ↦ D (n + T)
  have hstockTail : IsStockTrajectory p βTail DTail := by
    intro n
    dsimp only [βTail, DTail]
    have hstep := hstock (n + T)
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep
  have hDnonneg := stockTrajectory_nonnegative model rule.unit_interval hstock hD0
  have htailRule : SignConsistentResponsive p βTail DTail := by
    refine ⟨?_, ?_, ?_⟩
    · intro n
      exact rule.unit_interval (n + T)
    · intro n hgradient
      have htail := hsign (n + T) (by omega) hgradient
      dsimp only [βTail]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
    · intro ε hε
      obtain ⟨δ, hδpos, htail⟩ := hresponsive ε hε
      refine ⟨δ, hδpos, ?_⟩
      intro n hgradient hβε
      have hdecrement := htail (n + T) (by omega) hgradient hβε
      dsimp only [βTail]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hdecrement
  have hβTailLimit := deference_tendsto_zero model hgain hcertificate hstockTail
    (by simpa only [DTail, Nat.zero_add] using hDnonneg T) htailRule
  have hβlimit : Tendsto β atTop (nhds 0) := by
    apply (Filter.tendsto_add_atTop_iff_nat T).1
    simpa only [βTail] using hβTailLimit
  exact ⟨hβlimit,
    stock_tendsto_calibrated model hgain hstock rule.unit_interval hβlimit⟩

/--
Under the certificate, the battery's heavy-ball rule converges whenever its
gradient has a uniformly negative tail.
-/
theorem heavyBall_tendsto_calibrated {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (hcertificate : 0 ≤ certificateMargin p) {momentumRetention : ℝ}
    (hretention : momentumRetention ∈ Icc (0 : ℝ) 1)
    {β D momentum : ℕ → ℝ} (hβ0 : β 0 ∈ Icc (0 : ℝ) 1)
    (hstock : IsStockTrajectory p β D) (hD0 : 0 ≤ D 0)
    (hupdate : IsHeavyBallTrajectory p momentumRetention β D momentum)
    (hnegativeTail : ∃ T κ, 0 < κ ∧
      ∀ t, T ≤ t → p.gradU (β t) (D t) ≤ -κ) :
    Tendsto β atTop (nhds 0) ∧
      Tendsto D atTop (nhds (p.stationaryStock 0)) := by
  apply eventualRule_tendsto_calibrated model hgain hcertificate hstock hD0
  exact heavyBall_eventuallySignConsistentResponsive model hretention hβ0 hupdate hnegativeTail

/--
Paper III, Theorem 4.3 (`thm:cert`), civic_loops.tex:249: the certificate gives
the stationary-gradient bound, the unique calibrated equilibrium, and global
convergence for every sign-consistent responsive rule and admissible initial
condition.
-/
theorem knobFreeCertificate {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) (hcertificate : 0 ≤ certificateMargin p) :
    (∀ β ∈ Ioc (0 : ℝ) 1,
      p.G β ≤ -p.v * p.c * β ∧ -p.v * p.c * β < 0) ∧
    (IsLoopEquilibrium p 0 (p.stationaryStock 0) ∧
      ∀ {β D : ℝ}, β ∈ Icc (0 : ℝ) 1 → IsLoopEquilibrium p β D →
        β = 0 ∧ D = p.stationaryStock 0) ∧
    ∀ (β D : ℕ → ℝ), IsStockTrajectory p β D → 0 ≤ D 0 →
      SignConsistentResponsive p β D →
        Tendsto β atTop (nhds 0) ∧
          Tendsto D atTop (nhds (p.stationaryStock 0)) := by
  refine ⟨?_, calibratedCorner_unique_equilibrium model hgain hcertificate, ?_⟩
  · intro β hβ
    have hinterval : β ∈ Icc (0 : ℝ) 1 := ⟨hβ.1.le, hβ.2⟩
    refine ⟨stationaryGradient_le_neg_certificate model hgain hcertificate hinterval, ?_⟩
    have : 0 < p.v * p.c * β :=
      mul_pos (mul_pos model.v_pos model.c_pos) hβ.1
    nlinarith
  · intro β D hstock hD0 rule
    have hβlimit := deference_tendsto_zero model hgain hcertificate hstock hD0 rule
    exact ⟨hβlimit,
      stock_tendsto_calibrated model hgain hstock rule.unit_interval hβlimit⟩

#print axioms stockMultiplier_nonneg_le
#print axioms stockMultiplier_strictMonoOn
#print axioms stockTrajectory_nonnegative
#print axioms stockTrajectory_le_arithGeom
#print axioms stock_upper_bound
#print axioms stationaryStock_le_policyFreeBound
#print axioms gradU_le_neg_certificate
#print axioms stationaryGradient_le_neg_certificate
#print axioms stationaryGradient_neg_of_pos
#print axioms clipUnit_lt_of_lt_of_pos
#print axioms equilibrium_stock_eq_stationary
#print axioms calibratedCorner_unique_equilibrium
#print axioms clipUnit_eq_self
#print axioms projectedGradient_signConsistentResponsive
#print axioms fixedSign_signConsistentResponsive
#print axioms multiplicativeSign_signConsistentResponsive
#print axioms heavyBall_eventuallySignConsistentResponsive
#print axioms gradU_le_neg_certificate_add_error
#print axioms exists_lt_of_uniform_descent
#print axioms tendsto_zero_of_nonnegative_contraction
#print axioms stockTrajectory_eventually_le_policyFreeBound
#print axioms deference_tendsto_zero
#print axioms stock_tendsto_calibrated
#print axioms eventualRule_tendsto_calibrated
#print axioms heavyBall_tendsto_calibrated
#print axioms knobFreeCertificate
#print axioms gradU_le_neg_strictMargin
#print axioms gradU_neg_strictMargin
#print axioms strictMarginCertificate

end CivicAlignment.PaperIII
