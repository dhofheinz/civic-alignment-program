/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.Convergence
import CivicAlignment.PaperII.GlobalCure

/-!
# Paper II: the prevention--release--restoration price schedule

This file formalizes the full statement of `thm:hyst`.  It separates
the exact release threshold at the captured corner from the restoration price,
the maximum of the weighted crossing function on the stationary
characteristic.  It also supplies the weighted planar convergence argument
required by the theorem's restoration clause.
-/

namespace CivicAlignment.PaperII

open Filter Function Set Topology

noncomputable section

/-! ## The civic-weighted map and its equilibria -/

/-- The unprojected civic-weighted policy update. -/
def civicWeightedInput (p : LoopParams) (ρ β D : ℝ) : ℝ :=
  β + p.α * civicWeightedGradient p ρ β D

/-- One civic-weighted projected policy step. -/
def civicWeightedDeferenceStep (p : LoopParams) (ρ β D : ℝ) : ℝ :=
  LoopParams.clipUnit (civicWeightedInput p ρ β D)

/-- The simultaneous Paper II loop map with civic weight `ρ`. -/
def civicWeightedLoopMap (p : LoopParams) (ρ : ℝ) (x : LoopState) : LoopState :=
  (civicWeightedDeferenceStep p ρ x.1 x.2, p.stockStep x.1 x.2)

/-- A trajectory under a constant civic weight. -/
def IsCivicWeightedTrajectory (p : LoopParams) (ρ : ℝ)
    (x : ℕ → LoopState) : Prop :=
  ∀ n, x (n + 1) = civicWeightedLoopMap p ρ (x n)

/-- A trajectory under a possibly time-varying civic-weight schedule. -/
def IsCivicWeightedScheduleTrajectory (p : LoopParams) (ρ : ℕ → ℝ)
    (x : ℕ → LoopState) : Prop :=
  ∀ n, x (n + 1) = civicWeightedLoopMap p (ρ n) (x n)

/-- An actual fixed point of the constant-weight map. -/
def IsCivicWeightedEquilibrium (p : LoopParams) (ρ β D : ℝ) : Prop :=
  civicWeightedLoopMap p ρ (β, D) = (β, D)

/-- On the stationary characteristic, the weighted gradient is stock times
the distance from the crossing price. -/
theorem civicWeightedGradient_stationary_eq {p : LoopParams}
    (model : DriftModelAssumptions p) {ρ β : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) :
    civicWeightedGradient p ρ β (p.stationaryStock β) =
      p.stationaryStock β * (weightedCureThreshold p β - ρ) := by
  have hden : 1 - p.s β ≠ 0 := (one_sub_s_pos model hβ).ne'
  have hI : p.I ≠ 0 := model.I_pos.ne'
  simp only [civicWeightedGradient, LoopParams.gradU, weightedCureThreshold,
    LoopParams.stationaryStock, model.no_content_gain, sub_zero]
  field_simp [hden, hI]
  ring

/-- On the stationary characteristic, negativity of the weighted gradient is
equivalent to the civic weight lying above `Ψ`. -/
theorem civicWeightedGradient_stationary_neg_iff {p : LoopParams}
    (model : DriftModelAssumptions p) {ρ β : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) :
    civicWeightedGradient p ρ β (p.stationaryStock β) < 0 ↔
      weightedCureThreshold p β < ρ := by
  rw [civicWeightedGradient_stationary_eq model hβ]
  have hstock : 0 < p.stationaryStock β :=
    model.I_pos.trans_le (stationaryStock_mem_stockInterval model hβ).1
  calc
    p.stationaryStock β * (weightedCureThreshold p β - ρ) < 0 ↔
        p.stationaryStock β * (weightedCureThreshold p β - ρ) <
          p.stationaryStock β * 0 := by rw [mul_zero]
    _ ↔ weightedCureThreshold p β - ρ < 0 :=
      mul_lt_mul_iff_right₀ hstock
    _ ↔ weightedCureThreshold p β < ρ := sub_neg

/-- The weighted map leaves the paper's stock box invariant at every weight. -/
theorem civicWeightedInvariantBox {p : LoopParams}
    (model : DriftModelAssumptions p) (ρ : ℝ) :
    MapsTo (civicWeightedLoopMap p ρ) (absorbingBox p) (absorbingBox p) := by
  intro x hx
  have hstock := invariantBox model hx
  exact ⟨LoopParams.clipUnit_mem _, hstock.2⟩

/-- The weighted calibrated corner is fixed for every nonnegative civic weight. -/
theorem civicWeighted_calibrated_fixed {p : LoopParams}
    (model : DriftModelAssumptions p) (threshold : ThresholdAssumption p)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    IsCivicWeightedEquilibrium p ρ 0 (p.stationaryStock 0) := by
  have hβ : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hstock := stationaryStock_fixed model hβ
  have hgrad : civicWeightedGradient p ρ 0 (p.stationaryStock 0) < 0 := by
    exact (calibratedGradient_uniform_in_weight threshold hρ
      (show (0, p.stationaryStock 0) ∈ calibratedGradientNeighborhood p by
        change p.gradU 0 (p.stationaryStock 0) < p.G 0 / 2
        rw [← G_eq_gradU_stationary]
        linarith [threshold.G_zero_neg])
      (model.I_pos.le.trans (stationaryStock_mem_stockInterval model hβ).1)).2
  apply Prod.ext
  · simp only [civicWeightedLoopMap, civicWeightedDeferenceStep,
      civicWeightedInput]
    rw [clipUnit_eq_zero_iff]
    nlinarith [model.α_pos]
  · simpa only [civicWeightedLoopMap, Prod.snd] using hstock

/-- The captured corner is fixed exactly through the release threshold. -/
theorem civicWeighted_captured_fixed_iff {p : LoopParams}
    (model : DriftModelAssumptions p) (ρ : ℝ) :
    IsCivicWeightedEquilibrium p ρ 1 (p.stationaryStock 1) ↔
      ρ ≤ cureThreshold p := by
  have hβ : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  have hstock := stationaryStock_fixed model hβ
  have hstationary : p.stationaryStock 1 = p.I / p.lambda₀ := by
    simp [LoopParams.stationaryStock, LoopParams.s, model.no_content_gain]
  constructor
  · intro hfixed
    have hpolicy := congrArg Prod.fst hfixed
    simp only [civicWeightedLoopMap, civicWeightedDeferenceStep,
      civicWeightedInput] at hpolicy
    have hinput : 1 ≤ 1 + p.α * civicWeightedGradient p ρ 1
        (p.stationaryStock 1) := (clipUnit_eq_one_iff _).mp hpolicy
    have hgrad : 0 ≤ civicWeightedGradient p ρ 1 (p.stationaryStock 1) := by
      nlinarith [model.α_pos]
    exact (civicWeightedGradient_captured_nonneg_iff model ρ).mp
      (hstationary ▸ hgrad)
  · intro hρ
    have hgrad : 0 ≤ civicWeightedGradient p ρ 1 (p.I / p.lambda₀) :=
      (civicWeightedGradient_captured_nonneg_iff model ρ).2 hρ
    apply Prod.ext
    · simp only [civicWeightedLoopMap, civicWeightedDeferenceStep,
        civicWeightedInput]
      rw [clipUnit_eq_one_iff]
      rw [hstationary]
      nlinarith [model.α_pos]
    · simpa only [civicWeightedLoopMap, Prod.snd] using hstock

/-- At the release threshold the captured normal gradient vanishes exactly. -/
theorem civicWeightedGradient_captured_at_cure_eq_zero {p : LoopParams}
    (model : DriftModelAssumptions p) :
    civicWeightedGradient p (cureThreshold p) 1 (p.stationaryStock 1) = 0 := by
  rw [show p.stationaryStock 1 = p.I / p.lambda₀ by
    simp [LoopParams.stationaryStock, LoopParams.s, model.no_content_gain]]
  rw [civicWeightedGradient_captured_eq model]
  ring

/-- The release factorization written at the captured stationary stock. -/
theorem civicWeightedGradient_captured_stationary_eq {p : LoopParams}
    (model : DriftModelAssumptions p) (ρ : ℝ) :
    civicWeightedGradient p ρ 1 (p.stationaryStock 1) =
      (p.I / p.lambda₀) * (cureThreshold p - ρ) := by
  rw [show p.stationaryStock 1 = p.I / p.lambda₀ by
    simp [LoopParams.stationaryStock, LoopParams.s, model.no_content_gain]]
  exact civicWeightedGradient_captured_eq model ρ

/-! ## The restoration price -/

/-- The restoration price is the maximum of `Ψ` on the policy interval. -/
def restorationPrice (p : LoopParams) : ℝ :=
  sSup (weightedCureThreshold p '' Icc (0 : ℝ) 1)

/-- The weighted crossing function is continuous. -/
theorem continuous_weightedCureThreshold (p : LoopParams) :
    Continuous (weightedCureThreshold p) := by
  change Continuous (fun β : ℝ ↦
    2 * p.c * (1 - p.c * β) -
      p.v * (1 - (1 - p.lambda₀) * (1 - p.η * (1 - β)) ^ 2) / p.I)
  fun_prop

/-- The restoration price is attained and dominates every stationary crossing
price. -/
theorem restorationPrice_isGreatest (p : LoopParams) :
    IsGreatest (weightedCureThreshold p '' Icc (0 : ℝ) 1)
      (restorationPrice p) := by
  exact (isCompact_Icc.image (continuous_weightedCureThreshold p)).isGreatest_sSup
    ⟨weightedCureThreshold p 0, ⟨0, by norm_num, rfl⟩⟩

/-- A maximizer for the restoration price exists in `[0,1]`. -/
theorem exists_restorationPrice_maximizer (p : LoopParams) :
    ∃ β ∈ Icc (0 : ℝ) 1, weightedCureThreshold p β = restorationPrice p := by
  rcases (restorationPrice_isGreatest p).1 with ⟨β, hβ, hvalue⟩
  exact ⟨β, hβ, hvalue⟩

/-- Release never costs more than full restoration. -/
theorem cureThreshold_le_restorationPrice (p : LoopParams) :
    cureThreshold p ≤ restorationPrice p := by
  rw [← weightedCureThreshold_one (p := p)]
  exact (restorationPrice_isGreatest p).2 ⟨1, by norm_num, rfl⟩

/-- Above the restoration price, the stationary weighted gradient is strictly
negative at every policy. -/
theorem civicWeightedGradient_stationary_neg_of_restoration {p : LoopParams}
    (model : DriftModelAssumptions p) {ρ β : ℝ}
    (hρ : restorationPrice p < ρ) (hβ : β ∈ Icc (0 : ℝ) 1) :
    civicWeightedGradient p ρ β (p.stationaryStock β) < 0 := by
  rw [civicWeightedGradient_stationary_eq model hβ]
  have hstock : 0 < p.stationaryStock β :=
    model.I_pos.trans_le (stationaryStock_mem_stockInterval model hβ).1
  have hΨ : weightedCureThreshold p β ≤ restorationPrice p :=
    (restorationPrice_isGreatest p).2 ⟨β, hβ, rfl⟩
  exact mul_neg_of_pos_of_neg hstock (sub_neg.mpr (hΨ.trans_lt hρ))

/-- Between release and restoration, the weighted characteristic has an
interior crossing. -/
theorem exists_weightedCrossing_of_between {p : LoopParams}
    {ρ : ℝ} (hlow : cureThreshold p < ρ) (hhigh : ρ < restorationPrice p) :
    ∃ β ∈ Ioo (0 : ℝ) 1, weightedCureThreshold p β = ρ := by
  obtain ⟨βmax, hβmax, hmax⟩ := exists_restorationPrice_maximizer p
  have hmaxρ : ρ < weightedCureThreshold p βmax := by rw [hmax]; exact hhigh
  have honeρ : weightedCureThreshold p 1 < ρ := by
    rwa [weightedCureThreshold_one]
  have hβmax_lt : βmax < 1 := lt_of_le_of_ne hβmax.2 (by
    intro h
    subst βmax
    exact (not_lt_of_ge honeρ.le) hmaxρ)
  have hcont : ContinuousOn (weightedCureThreshold p) (Icc βmax 1) :=
    (continuous_weightedCureThreshold p).continuousOn
  obtain ⟨β, hβ, hvalue⟩ := intermediate_value_Icc' hβmax.2 hcont
    (show ρ ∈ Icc (weightedCureThreshold p 1)
      (weightedCureThreshold p βmax) from ⟨honeρ.le, hmaxρ.le⟩)
  refine ⟨β, ⟨?_, ?_⟩, hvalue⟩
  · have hβnonneg : 0 ≤ β := hβmax.1.trans hβ.1
    exact lt_of_le_of_ne hβnonneg (by
      intro hzero
      have hβzero : β = 0 := hzero.symm
      have hmaxzero : βmax = 0 := le_antisymm (hβzero ▸ hβ.1) hβmax.1
      subst β
      subst βmax
      linarith)
  · exact lt_of_le_of_ne hβ.2 (by
      intro hone
      have hβone : β = 1 := hone
      subst β
      linarith)

/-! ## The weighted fixed-point catalogue above restoration -/

/-- Every weighted fixed point has stock on the same stationary
characteristic as the unweighted loop. -/
theorem civicWeightedEquilibrium_stock_eq_stationary {p : LoopParams}
    (model : DriftModelAssumptions p) {ρ β D : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1)
    (heq : IsCivicWeightedEquilibrium p ρ β D) :
    D = p.stationaryStock β := by
  have hstock := congrArg Prod.snd heq
  simp only [civicWeightedLoopMap, LoopParams.stockStep,
    model.no_content_gain, add_zero] at hstock
  have hden : 1 - p.s β ≠ 0 := (one_sub_s_pos model hβ).ne'
  simp only [LoopParams.stationaryStock, model.no_content_gain, sub_zero]
  apply (eq_div_iff hden).2
  nlinarith

/-- Above the restoration price, the calibrated corner is the unique weighted
equilibrium. -/
theorem civicWeightedEquilibrium_eq_calibrated_of_restoration {p : LoopParams}
    (model : DriftModelAssumptions p) (_threshold : ThresholdAssumption p)
    {ρ β D : ℝ} (hρ : restorationPrice p < ρ)
    (heq : IsCivicWeightedEquilibrium p ρ β D) :
    (β, D) = calibratedPoint p := by
  have hpolicy := congrArg Prod.fst heq
  simp only [civicWeightedLoopMap, civicWeightedDeferenceStep,
    civicWeightedInput] at hpolicy
  have hβ : β ∈ Icc (0 : ℝ) 1 := by
    have hmem := LoopParams.clipUnit_mem
      (β + p.α * civicWeightedGradient p ρ β D)
    rwa [hpolicy] at hmem
  have hD := civicWeightedEquilibrium_stock_eq_stationary model hβ heq
  by_cases hzero : β = 0
  · exact Prod.ext hzero (by simpa only [calibratedPoint, hzero] using hD)
  by_cases hone : β = 1
  · have hfixed : IsCivicWeightedEquilibrium p ρ 1 (p.stationaryStock 1) := by
      simpa only [hone, hD] using heq
    have hρcure : ρ ≤ cureThreshold p :=
      (civicWeighted_captured_fixed_iff model ρ).mp hfixed
    have hcure := cureThreshold_le_restorationPrice p
    exact ((not_lt_of_ge (hρcure.trans hcure)) hρ).elim
  have hβint : β ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hβ.1 (Ne.symm hzero), lt_of_le_of_ne hβ.2 hone⟩
  have hinput : β + p.α * civicWeightedGradient p ρ β D = β :=
    (clipUnit_eq_interior_iff hβint).mp hpolicy
  have hgrad : civicWeightedGradient p ρ β D = 0 := by
    nlinarith [model.α_pos]
  have hgradStationary :
      civicWeightedGradient p ρ β (p.stationaryStock β) = 0 := by
    rwa [← hD]
  rw [civicWeightedGradient_stationary_eq model
    ⟨hβint.1.le, hβint.2.le⟩] at hgradStationary
  have hstock : 0 < p.stationaryStock β :=
    model.I_pos.trans_le
      (stationaryStock_mem_stockInterval model
        ⟨hβint.1.le, hβint.2.le⟩).1
  have hcross : weightedCureThreshold p β = ρ := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hgradStationary).resolve_left hstock.ne')
  have hle : weightedCureThreshold p β ≤ restorationPrice p :=
    (restorationPrice_isGreatest p).2
      ⟨β, ⟨hβint.1.le, hβint.2.le⟩, rfl⟩
  rw [hcross] at hle
  exact ((not_lt_of_ge hle) hρ).elim

/-- Above restoration, the calibrated corner exists and is the unique
weighted equilibrium. -/
theorem civicWeightedEquilibrium_iff_calibrated_of_restoration {p : LoopParams}
    (model : DriftModelAssumptions p) (threshold : ThresholdAssumption p)
    {ρ β D : ℝ} (hρ : restorationPrice p < ρ) :
    IsCivicWeightedEquilibrium p ρ β D ↔
      (β, D) = calibratedPoint p := by
  constructor
  · exact civicWeightedEquilibrium_eq_calibrated_of_restoration
      model threshold hρ
  · intro hpoint
    have hcoordinates : β = 0 ∧ D = p.stationaryStock 0 := by
      simpa only [calibratedPoint, Prod.mk.injEq] using hpoint
    rcases hcoordinates with ⟨rfl, rfl⟩
    have hρpos : 0 < ρ :=
      (cureThreshold_pos model threshold).trans_le
        ((cureThreshold_le_restorationPrice p).trans hρ.le)
    exact civicWeighted_calibrated_fixed model threshold hρpos.le

/-! ## Weighted cooperativity and convergent-step condition -/

/-- Maximum stock-to-policy response for the weighted map on `[0,1]`. -/
def weightedPolicyStockUpper (p : LoopParams) (ρ : ℝ) : ℝ :=
  p.α * (2 * p.c - ρ)

/-- Denominator in the weighted form of `(SS⁺)`.  Relative to the unweighted
bound, only the stock-to-policy off-diagonal maximum changes, from `2αc` to
`α(2c-ρ)`. -/
def weightedConvergentStepDenominator (p : LoopParams) (ρ : ℝ) : ℝ :=
  p.I * (2 * p.c ^ 2 * p.s 0 +
    (2 * p.c - ρ) * (2 * p.η * (1 - p.lambda₀)))

/-- Paper II, Theorem 3.15(iii), the weighted form of `(SS⁺)`. -/
structure WeightedConvergentStepAssumption (p : LoopParams) (ρ : ℝ) : Prop where
  bound : p.α < p.lambda₀ * p.s 0 /
    weightedConvergentStepDenominator p ρ

/-- In the cooperative window the weighted `(SS⁺)` denominator is positive. -/
theorem weightedConvergentStepDenominator_pos {p : LoopParams} {ρ : ℝ}
    (model : DriftModelAssumptions p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c)) :
    0 < weightedConvergentStepDenominator p ρ := by
  have hcoef : 0 < 2 * p.c - ρ := by
    have hc : 0 < 2 * p.c ^ 2 := mul_pos two_pos (sq_pos_of_pos model.c_pos)
    nlinarith
  have htail : 0 < 2 * p.η * (1 - p.lambda₀) :=
    mul_pos (mul_pos two_pos model.η_pos) (sub_pos.mpr model.lambda₀_lt_one)
  have hsecond : 0 < (2 * p.c - ρ) *
      (2 * p.η * (1 - p.lambda₀)) := mul_pos hcoef htail
  have hs0 : 0 ≤ p.s 0 :=
    (driftStockMultiplier_nonneg_le model (by norm_num)).1
  simp only [weightedConvergentStepDenominator]
  exact mul_pos model.I_pos
    (add_pos_of_nonneg_of_pos (mul_nonneg (by positivity) hs0) hsecond)

/-- Weighted `(SS⁺)` forces `s(0)>0`. -/
theorem WeightedConvergentStepAssumption.stockDiagonalLower_pos
    {p : LoopParams} {ρ : ℝ} (model : DriftModelAssumptions p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (ssplus : WeightedConvergentStepAssumption p ρ) :
    0 < stockDiagonalLower p := by
  have hden := weightedConvergentStepDenominator_pos model hcoop
  have hquot : 0 < p.lambda₀ * p.s 0 /
      weightedConvergentStepDenominator p ρ := model.α_pos.trans ssplus.bound
  have hnum : 0 < p.lambda₀ * p.s 0 := (div_pos_iff.mp hquot).elim
    (fun h ↦ h.1) (fun h ↦ (not_lt_of_ge hden.le h.2).elim)
  rcases mul_pos_iff.mp hnum with h | h
  · simpa only [stockDiagonalLower] using h.2
  · exact (not_lt_of_ge model.lambda₀_pos.le h.1).elim

/-- Weighted `(SS⁺)` implies the strict policy-diagonal bound `(SS)`. -/
theorem WeightedConvergentStepAssumption.toStrictSmallStep
    {p : LoopParams} {ρ : ℝ} (model : DriftModelAssumptions p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (ssplus : WeightedConvergentStepAssumption p ρ) :
    StrictSmallStepAssumption p := by
  have hden := weightedConvergentStepDenominator_pos model hcoop
  have hbound : p.α * weightedConvergentStepDenominator p ρ <
      p.lambda₀ * p.s 0 := (lt_div_iff₀ hden).mp ssplus.bound
  have hcoef : 0 < 2 * p.c - ρ := by
    have hc : 0 < 2 * p.c ^ 2 := mul_pos two_pos (sq_pos_of_pos model.c_pos)
    nlinarith
  have htail : 0 < (2 * p.c - ρ) *
      (2 * p.η * (1 - p.lambda₀)) :=
    mul_pos hcoef (mul_pos (mul_pos two_pos model.η_pos)
      (sub_pos.mpr model.lambda₀_lt_one))
  have hcoreDen : 2 * p.c ^ 2 * p.I * p.s 0 <
      weightedConvergentStepDenominator p ρ := by
    simp only [weightedConvergentStepDenominator]
    have hs0 : 0 ≤ p.s 0 :=
      (driftStockMultiplier_nonneg_le model (by norm_num)).1
    nlinarith [model.I_pos, htail]
  have hcore : (2 * p.α * p.c ^ 2 * p.I) * p.s 0 <
      p.lambda₀ * p.s 0 := by
    calc
      (2 * p.α * p.c ^ 2 * p.I) * p.s 0 =
          p.α * (2 * p.c ^ 2 * p.I * p.s 0) := by ring
      _ < p.α * weightedConvergentStepDenominator p ρ :=
        mul_lt_mul_of_pos_left hcoreDen model.α_pos
      _ < p.lambda₀ * p.s 0 := hbound
  have hs0 : 0 < p.s 0 := by
    simpa only [stockDiagonalLower] using
      ssplus.stockDiagonalLower_pos model hcoop
  exact ⟨(mul_lt_mul_iff_left₀ hs0).mp hcore⟩

/-- Weighted `(SS⁺)` leaves a positive policy diagonal. -/
theorem WeightedConvergentStepAssumption.policyDiagonalLower_pos
    {p : LoopParams} {ρ : ℝ} (model : DriftModelAssumptions p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (ssplus : WeightedConvergentStepAssumption p ρ) :
    0 < policyDiagonalLower p := by
  have hsmall := ssplus.toStrictSmallStep model hcoop
  have hratio : 2 * p.α * p.c ^ 2 * (p.I / p.lambda₀) < 1 := by
    rw [show 2 * p.α * p.c ^ 2 * (p.I / p.lambda₀) =
      (2 * p.α * p.c ^ 2 * p.I) / p.lambda₀ by ring]
    exact (div_lt_one model.lambda₀_pos).2 hsmall.bound
  simpa only [policyDiagonalLower] using sub_pos.mpr hratio

/-- The weighted stock-to-policy cross bound is positive in the cooperative
window. -/
theorem weightedPolicyStockUpper_pos {p : LoopParams} {ρ : ℝ}
    (model : DriftModelAssumptions p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c)) :
    0 < weightedPolicyStockUpper p ρ := by
  simp only [weightedPolicyStockUpper]
  apply mul_pos model.α_pos
  have hc : 0 < 2 * p.c ^ 2 := mul_pos two_pos (sq_pos_of_pos model.c_pos)
  nlinarith

/-- Weighted `(SS⁺)` is strict diagonal-product dominance over the two cross
effects. -/
theorem WeightedConvergentStepAssumption.crossProduct_lt_diagonalProduct
    {p : LoopParams} {ρ : ℝ} (model : DriftModelAssumptions p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (ssplus : WeightedConvergentStepAssumption p ρ) :
    weightedPolicyStockUpper p ρ * stockPolicyUpper p <
      policyDiagonalLower p * stockDiagonalLower p := by
  have hden := weightedConvergentStepDenominator_pos model hcoop
  have hbound : p.α * weightedConvergentStepDenominator p ρ <
      p.lambda₀ * p.s 0 := (lt_div_iff₀ hden).mp ssplus.bound
  have hscaled :
      p.lambda₀ * (weightedPolicyStockUpper p ρ * stockPolicyUpper p) <
        p.lambda₀ * (policyDiagonalLower p * stockDiagonalLower p) := by
    have hleft :
        p.lambda₀ * (weightedPolicyStockUpper p ρ * stockPolicyUpper p) =
          p.α * (2 * p.c - ρ) *
            (2 * p.η * (1 - p.lambda₀)) * p.I := by
      simp only [weightedPolicyStockUpper, stockPolicyUpper]
      field_simp [model.lambda₀_pos.ne']
    have hright :
        p.lambda₀ * (policyDiagonalLower p * stockDiagonalLower p) =
          (p.lambda₀ - 2 * p.α * p.c ^ 2 * p.I) * p.s 0 := by
      simp only [policyDiagonalLower, stockDiagonalLower]
      field_simp [model.lambda₀_pos.ne']
    rw [hleft, hright]
    simp only [weightedConvergentStepDenominator] at hbound
    nlinarith
  exact (mul_lt_mul_iff_right₀ model.lambda₀_pos).mp hscaled

/-- Throughout the cooperative window the weighted gradient coefficient on
stock is nonnegative. -/
theorem weighted_stock_coefficient_nonnegative {p : LoopParams} {ρ β : ℝ}
    (model : DriftModelAssumptions p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (hβ : β ∈ Icc (0 : ℝ) 1) :
    0 ≤ 2 * p.c * (1 - p.c * β) - ρ := by
  have hmul : p.c * β ≤ p.c := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hβ.2 model.c_pos.le
  nlinarith [model.c_pos, model.c_lt_one]

/-- The weighted policy input remains monotone in policy under `(SS)`. -/
theorem civicWeightedInput_mono_policy {p : LoopParams} {ρ β₁ β₂ D : ℝ}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hβ₁ : β₁ ∈ Icc (0 : ℝ) 1) (hβ₂ : β₂ ∈ Icc (0 : ℝ) 1)
    (hβ : β₁ ≤ β₂) (hD : D ∈ Icc p.I (p.I / p.lambda₀)) :
    civicWeightedInput p ρ β₁ D ≤ civicWeightedInput p ρ β₂ D := by
  have h := unclippedDeferenceInput_mono_policy model ss hβ₁ hβ₂ hβ hD
  simp only [civicWeightedInput, civicWeightedGradient,
    unclippedDeferenceInput] at h ⊢
  nlinarith

/-- In the cooperative window the weighted input is monotone in stock. -/
theorem civicWeightedInput_mono_stock {p : LoopParams} {ρ β D₁ D₂ : ℝ}
    (model : DriftModelAssumptions p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (hβ : β ∈ Icc (0 : ℝ) 1) (hD : D₁ ≤ D₂) :
    civicWeightedInput p ρ β D₁ ≤ civicWeightedInput p ρ β D₂ := by
  have hcoef := weighted_stock_coefficient_nonnegative model hcoop hβ
  have hscaled : 0 ≤ p.α *
      (2 * p.c * (1 - p.c * β) - ρ) :=
    mul_nonneg model.α_pos.le hcoef
  simp only [civicWeightedInput, civicWeightedGradient, LoopParams.gradU]
  nlinarith [mul_nonneg hscaled (sub_nonneg.mpr hD)]

/-- In the stated window the civic-weighted map is order-preserving on `B`. -/
theorem civicWeightedLoopMap_monotoneOn_box {p : LoopParams} {ρ : ℝ}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c)) :
    MonotoneOn (civicWeightedLoopMap p ρ) (absorbingBox p) := by
  intro x hx y hy hxy
  have hpolicy₁ := civicWeightedInput_mono_policy (ρ := ρ) model ss
    hx.1 hy.1 hxy.1 hx.2
  have hpolicy₂ := civicWeightedInput_mono_stock model hcoop hy.1 hxy.2
  have hpolicy : civicWeightedDeferenceStep p ρ x.1 x.2 ≤
      civicWeightedDeferenceStep p ρ y.1 y.2 := by
    exact LoopParams.monotone_clipUnit (hpolicy₁.trans hpolicy₂)
  have hstock := (loopMap_monotoneOn_box model ss hx hy hxy).2
  exact ⟨hpolicy, hstock⟩

/-- The civic-weighted loop map is continuous. -/
theorem continuous_civicWeightedLoopMap (p : LoopParams) (ρ : ℝ) :
    Continuous (civicWeightedLoopMap p ρ) := by
  unfold civicWeightedLoopMap civicWeightedDeferenceStep civicWeightedInput
    civicWeightedGradient LoopParams.gradU LoopParams.stockStep LoopParams.s
    LoopParams.clipUnit
  fun_prop

/-- A weighted trajectory starting in `B` remains there. -/
theorem civicWeightedTrajectory_mem_absorbingBox {p : LoopParams} {ρ : ℝ}
    (model : DriftModelAssumptions p) {x : ℕ → LoopState}
    (traj : IsCivicWeightedTrajectory p ρ x)
    (hx0 : x 0 ∈ absorbingBox p) :
    ∀ n, x n ∈ absorbingBox p := by
  intro n
  induction n with
  | zero => exact hx0
  | succ n ih =>
      rw [traj n]
      exact civicWeightedInvariantBox model ρ ih

/-! ## Weighted difference estimates -/

/-- Lower policy-input estimate for a weighted southeast increment. -/
theorem civicWeighted_southeast_input_difference_lower
    {p : LoopParams} {ρ : ℝ} (model : DriftModelAssumptions p)
    {x y : LoopState} (hx : x ∈ absorbingBox p) (hy : y ∈ absorbingBox p)
    (hβ : x.1 ≤ y.1) (hD : y.2 ≤ x.2) :
    policyDiagonalLower p * (y.1 - x.1) -
        weightedPolicyStockUpper p ρ * (x.2 - y.2) ≤
      civicWeightedInput p ρ y.1 y.2 - civicWeightedInput p ρ x.1 x.2 := by
  have hk : 0 ≤ 2 * p.α * p.c ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) (sq_nonneg p.c)
  have ha : policyDiagonalLower p ≤ 1 - 2 * p.α * p.c ^ 2 * y.2 := by
    simp only [policyDiagonalLower]
    have := mul_le_mul_of_nonneg_left hy.2.2 hk
    linarith
  have hb : p.α * (2 * p.c * (1 - p.c * x.1) - ρ) ≤
      weightedPolicyStockUpper p ρ := by
    simp only [weightedPolicyStockUpper]
    have hcx : 0 ≤ p.c ^ 2 * x.1 :=
      mul_nonneg (sq_nonneg p.c) hx.1.1
    nlinarith [model.α_pos]
  have hap := mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hβ)
  have hbq := mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr hD)
  simp only [civicWeightedInput, civicWeightedGradient, LoopParams.gradU]
  nlinarith

/-- Upper policy-input estimate for a weighted northwest increment. -/
theorem civicWeighted_northwest_input_difference_upper
    {p : LoopParams} {ρ : ℝ} (model : DriftModelAssumptions p)
    {x y : LoopState} (hx : x ∈ absorbingBox p) (hy : y ∈ absorbingBox p)
    (hβ : y.1 ≤ x.1) (hD : x.2 ≤ y.2) :
    civicWeightedInput p ρ y.1 y.2 - civicWeightedInput p ρ x.1 x.2 ≤
      -policyDiagonalLower p * (x.1 - y.1) +
        weightedPolicyStockUpper p ρ * (y.2 - x.2) := by
  have hk : 0 ≤ 2 * p.α * p.c ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) (sq_nonneg p.c)
  have ha : policyDiagonalLower p ≤ 1 - 2 * p.α * p.c ^ 2 * y.2 := by
    simp only [policyDiagonalLower]
    have := mul_le_mul_of_nonneg_left hy.2.2 hk
    linarith
  have hb : p.α * (2 * p.c * (1 - p.c * x.1) - ρ) ≤
      weightedPolicyStockUpper p ρ := by
    simp only [weightedPolicyStockUpper]
    have hcx : 0 ≤ p.c ^ 2 * x.1 :=
      mul_nonneg (sq_nonneg p.c) hx.1.1
    nlinarith [model.α_pos]
  have hap := mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hβ)
  have hbq := mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr hD)
  simp only [civicWeightedInput, civicWeightedGradient, LoopParams.gradU]
  nlinarith

/-! ## Comparable weighted steps -/

/-- A componentwise increasing weighted step propagates by cooperativity. -/
theorem civicWeightedTrajectory_tail_monotone_of_le
    {p : LoopParams} {ρ : ℝ} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    {x : ℕ → LoopState} (traj : IsCivicWeightedTrajectory p ρ x)
    (hmem : ∀ n, x n ∈ absorbingBox p) {t : ℕ}
    (hstep : x t ≤ x (t + 1)) :
    Monotone (fun n ↦ x (n + t)) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => simpa [Nat.add_comm] using hstep
  | succ n ih =>
      have hmono := civicWeightedLoopMap_monotoneOn_box model ss hcoop
        (hmem (n + t)) (hmem (n + 1 + t)) ih
      calc
        x (Nat.succ n + t) = civicWeightedLoopMap p ρ (x (n + t)) := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using traj (n + t)
        _ ≤ civicWeightedLoopMap p ρ (x (n + 1 + t)) := hmono
        _ = x (Nat.succ n + 1 + t) := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using (traj (n + 1 + t)).symm

/-- A componentwise decreasing weighted step propagates by cooperativity. -/
theorem civicWeightedTrajectory_tail_antitone_of_ge
    {p : LoopParams} {ρ : ℝ} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    {x : ℕ → LoopState} (traj : IsCivicWeightedTrajectory p ρ x)
    (hmem : ∀ n, x n ∈ absorbingBox p) {t : ℕ}
    (hstep : x (t + 1) ≤ x t) :
    Antitone (fun n ↦ x (n + t)) := by
  apply antitone_nat_of_succ_le
  intro n
  induction n with
  | zero => simpa [Nat.add_comm] using hstep
  | succ n ih =>
      have hmono := civicWeightedLoopMap_monotoneOn_box model ss hcoop
        (hmem (n + 1 + t)) (hmem (n + t)) ih
      calc
        x (Nat.succ n + 1 + t) = civicWeightedLoopMap p ρ (x (n + 1 + t)) := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using traj (n + 1 + t)
        _ ≤ civicWeightedLoopMap p ρ (x (n + t)) := hmono
        _ = x (Nat.succ n + t) := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using (traj (n + t)).symm

/-- A limit of a constant-weight trajectory is a weighted equilibrium. -/
theorem civicWeightedTrajectory_limit_is_equilibrium
    {p : LoopParams} {ρ : ℝ} {x : ℕ → LoopState}
    (traj : IsCivicWeightedTrajectory p ρ x) {q : LoopState}
    (hlim : Tendsto x atTop (𝓝 q)) :
    IsCivicWeightedEquilibrium p ρ q.1 q.2 := by
  have hshift : Tendsto (fun n ↦ x (n + 1)) atTop (𝓝 q) :=
    (tendsto_add_atTop_iff_nat 1).2 hlim
  have hmapToQ : Tendsto (fun n ↦ civicWeightedLoopMap p ρ (x n))
      atTop (𝓝 q) := by
    apply hshift.congr'
    exact Eventually.of_forall fun n ↦ traj n
  have hmapToMap : Tendsto (fun n ↦ civicWeightedLoopMap p ρ (x n))
      atTop (𝓝 (civicWeightedLoopMap p ρ q)) :=
    ((continuous_civicWeightedLoopMap p ρ).tendsto q).comp hlim
  exact tendsto_nhds_unique hmapToMap hmapToQ

/-- One comparable weighted step forces convergence to a weighted fixed point. -/
theorem civicWeightedComparableStep_convergesToFixedPoint
    {p : LoopParams} {ρ : ℝ} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    {x : ℕ → LoopState} (traj : IsCivicWeightedTrajectory p ρ x)
    (hx0 : x 0 ∈ absorbingBox p) {t : ℕ}
    (hcomparable : x t ≤ x (t + 1) ∨ x (t + 1) ≤ x t) :
    ∃ q ∈ absorbingBox p, Tendsto x atTop (𝓝 q) ∧
      IsCivicWeightedEquilibrium p ρ q.1 q.2 := by
  have hmem := civicWeightedTrajectory_mem_absorbingBox model traj hx0
  rcases hcomparable with hstep | hstep
  · have hmono := civicWeightedTrajectory_tail_monotone_of_le
      model ss hcoop traj hmem hstep
    obtain ⟨q, hq, htail⟩ := monotone_sequence_tendsto_in_absorbingBox hmono
      (fun n ↦ hmem (n + t))
    have hlim : Tendsto x atTop (𝓝 q) :=
      (tendsto_add_atTop_iff_nat t).1 htail
    exact ⟨q, hq, hlim,
      civicWeightedTrajectory_limit_is_equilibrium traj hlim⟩
  · have hanti := civicWeightedTrajectory_tail_antitone_of_ge
      model ss hcoop traj hmem hstep
    obtain ⟨q, hq, htail⟩ := antitone_sequence_tendsto_in_absorbingBox hanti
      (fun n ↦ hmem (n + t))
    have hlim : Tendsto x atTop (𝓝 q) :=
      (tendsto_add_atTop_iff_nat t).1 htail
    exact ⟨q, hq, hlim,
      civicWeightedTrajectory_limit_is_equilibrium traj hlim⟩

/-! ## Weighted exclusion of quadrant alternation -/

/-- A weighted southeast step cannot be followed by a northwest step. -/
theorem civicWeighted_no_southeast_to_northwest
    {p : LoopParams} {ρ : ℝ} (model : DriftModelAssumptions p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (ssplus : WeightedConvergentStepAssumption p ρ)
    {x y : LoopState} (hx : x ∈ absorbingBox p) (hy : y ∈ absorbingBox p)
    (hxy : Southeast x y) :
    ¬Northwest (civicWeightedLoopMap p ρ x)
      (civicWeightedLoopMap p ρ y) := by
  intro hnext
  have hinput : civicWeightedInput p ρ y.1 y.2 <
      civicWeightedInput p ρ x.1 x.2 := by
    by_contra hnot
    have hmono := LoopParams.monotone_clipUnit (not_lt.mp hnot)
    have hpolicy : (civicWeightedLoopMap p ρ x).1 ≤
        (civicWeightedLoopMap p ρ y).1 := by
      simpa only [civicWeightedLoopMap, civicWeightedDeferenceStep] using hmono
    exact (not_lt_of_ge hpolicy) hnext.1
  have hpolicyBound := civicWeighted_southeast_input_difference_lower (ρ := ρ)
    model hx hy hxy.1.le hxy.2.le
  have hpolicy : policyDiagonalLower p * (y.1 - x.1) <
      weightedPolicyStockUpper p ρ * (x.2 - y.2) := by
    nlinarith
  have hstockBound := southeast_stock_difference_upper model hx hy
    hxy.1.le hxy.2.le
  have hstock : stockDiagonalLower p * (x.2 - y.2) <
      stockPolicyUpper p * (y.1 - x.1) := by
    have hnextStock : 0 < p.stockStep y.1 y.2 - p.stockStep x.1 x.2 := by
      simpa only [civicWeightedLoopMap] using sub_pos.mpr hnext.2
    nlinarith
  exact cross_inequalities_impossible (sub_pos.mpr hxy.1)
    (sub_pos.mpr hxy.2) (weightedPolicyStockUpper_pos model hcoop)
    (ssplus.stockDiagonalLower_pos model hcoop)
    (ssplus.crossProduct_lt_diagonalProduct model hcoop) hpolicy hstock

/-- A weighted northwest step cannot be followed by a southeast step. -/
theorem civicWeighted_no_northwest_to_southeast
    {p : LoopParams} {ρ : ℝ} (model : DriftModelAssumptions p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (ssplus : WeightedConvergentStepAssumption p ρ)
    {x y : LoopState} (hx : x ∈ absorbingBox p) (hy : y ∈ absorbingBox p)
    (hxy : Northwest x y) :
    ¬Southeast (civicWeightedLoopMap p ρ x)
      (civicWeightedLoopMap p ρ y) := by
  intro hnext
  have hinput : civicWeightedInput p ρ x.1 x.2 <
      civicWeightedInput p ρ y.1 y.2 := by
    by_contra hnot
    have hmono := LoopParams.monotone_clipUnit (not_lt.mp hnot)
    have hpolicy : (civicWeightedLoopMap p ρ y).1 ≤
        (civicWeightedLoopMap p ρ x).1 := by
      simpa only [civicWeightedLoopMap, civicWeightedDeferenceStep] using hmono
    exact (not_lt_of_ge hpolicy) hnext.1
  have hpolicyBound := civicWeighted_northwest_input_difference_upper (ρ := ρ)
    model hx hy hxy.1.le hxy.2.le
  have hpolicy : policyDiagonalLower p * (x.1 - y.1) <
      weightedPolicyStockUpper p ρ * (y.2 - x.2) := by
    nlinarith
  have hstockBound := northwest_stock_difference_lower model hx hy
    hxy.1.le hxy.2.le
  have hstock : stockDiagonalLower p * (y.2 - x.2) <
      stockPolicyUpper p * (x.1 - y.1) := by
    have hnextStock : p.stockStep y.1 y.2 - p.stockStep x.1 x.2 < 0 := by
      simpa only [civicWeightedLoopMap] using sub_neg.mpr hnext.2
    nlinarith
  exact cross_inequalities_impossible (sub_pos.mpr hxy.1)
    (sub_pos.mpr hxy.2) (weightedPolicyStockUpper_pos model hcoop)
    (ssplus.stockDiagonalLower_pos model hcoop)
    (ssplus.crossProduct_lt_diagonalProduct model hcoop) hpolicy hstock

/-- Under weighted `(SS⁺)`, every trajectory in `B` converges to a weighted
fixed point. -/
theorem civicWeighted_globalConvergence_of_convergentStep
    {p : LoopParams} {ρ : ℝ} (model : DriftModelAssumptions p)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (ssplus : WeightedConvergentStepAssumption p ρ)
    {x : ℕ → LoopState} (traj : IsCivicWeightedTrajectory p ρ x)
    (hx0 : x 0 ∈ absorbingBox p) :
    ∃ q ∈ absorbingBox p, Tendsto x atTop (𝓝 q) ∧
      IsCivicWeightedEquilibrium p ρ q.1 q.2 := by
  have ss : SmallStepAssumption p :=
    (ssplus.toStrictSmallStep model hcoop).toSmallStep
  have hmem := civicWeightedTrajectory_mem_absorbingBox model traj hx0
  by_cases hcomparable : ∃ t, x t ≤ x (t + 1) ∨ x (t + 1) ≤ x t
  · obtain ⟨t, ht⟩ := hcomparable
    exact civicWeightedComparableStep_convergesToFixedPoint
      model ss hcoop traj hx0 ht
  · have hnone : ∀ n, ¬(x n ≤ x (n + 1) ∨ x (n + 1) ≤ x n) := by
      intro n hn
      exact hcomparable ⟨n, hn⟩
    have hpropagateSE : ∀ {n}, Southeast (x n) (x (n + 1)) →
        Southeast (x (n + 1)) (x (n + 2)) := by
      intro n hstep
      rcases southeast_or_northwest_of_not_comparable (hnone (n + 1)) with h | h
      · simpa [show n + 2 = (n + 1) + 1 by omega] using h
      · have hbad := civicWeighted_no_southeast_to_northwest model hcoop ssplus
          (hmem n) (hmem (n + 1)) hstep
        have : Northwest (civicWeightedLoopMap p ρ (x n))
            (civicWeightedLoopMap p ρ (x (n + 1))) := by
          simpa [traj n, traj (n + 1),
            show n + 2 = (n + 1) + 1 by omega] using h
        exact (hbad this).elim
    have hpropagateNW : ∀ {n}, Northwest (x n) (x (n + 1)) →
        Northwest (x (n + 1)) (x (n + 2)) := by
      intro n hstep
      rcases southeast_or_northwest_of_not_comparable (hnone (n + 1)) with h | h
      · have hbad := civicWeighted_no_northwest_to_southeast model hcoop ssplus
          (hmem n) (hmem (n + 1)) hstep
        have : Southeast (civicWeightedLoopMap p ρ (x n))
            (civicWeightedLoopMap p ρ (x (n + 1))) := by
          simpa [traj n, traj (n + 1),
            show n + 2 = (n + 1) + 1 by omega] using h
        exact (hbad this).elim
      · simpa [show n + 2 = (n + 1) + 1 by omega] using h
    rcases southeast_or_northwest_of_not_comparable (hnone 0) with hfirst | hfirst
    · have hall : ∀ n, Southeast (x n) (x (n + 1)) := by
        intro n
        induction n with
        | zero => simpa using hfirst
        | succ n ih => simpa [Nat.succ_eq_add_one] using hpropagateSE ih
      obtain ⟨q, hq, hlim⟩ :=
        southeast_trajectory_tendsto_in_absorbingBox hmem hall
      exact ⟨q, hq, hlim,
        civicWeightedTrajectory_limit_is_equilibrium traj hlim⟩
    · have hall : ∀ n, Northwest (x n) (x (n + 1)) := by
        intro n
        induction n with
        | zero => simpa using hfirst
        | succ n ih => simpa [Nat.succ_eq_add_one] using hpropagateNW ih
      obtain ⟨q, hq, hlim⟩ :=
        northwest_trajectory_tendsto_in_absorbingBox hmem hall
      exact ⟨q, hq, hlim,
        civicWeightedTrajectory_limit_is_equilibrium traj hlim⟩

/-- Above restoration, weighted `(SS⁺)` forces every orbit in `B` to the
unique calibrated equilibrium. -/
theorem civicWeighted_restoration_tendsto_calibrated
    {p : LoopParams} (model : DriftModelAssumptions p)
    (threshold : ThresholdAssumption p) {ρ : ℝ}
    (hrestore : restorationPrice p < ρ)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (ssplus : WeightedConvergentStepAssumption p ρ)
    {x : ℕ → LoopState} (traj : IsCivicWeightedTrajectory p ρ x)
    (hx0 : x 0 ∈ absorbingBox p) :
    Tendsto x atTop (𝓝 (calibratedPoint p)) := by
  obtain ⟨q, _hq, hlim, heq⟩ :=
    civicWeighted_globalConvergence_of_convergentStep
      model hcoop ssplus traj hx0
  have hq := civicWeightedEquilibrium_eq_calibrated_of_restoration
    model threshold hrestore heq
  have hq' : q = calibratedPoint p := by simpa using hq
  rwa [hq'] at hlim

/-! ## A uniform prevention neighborhood -/

/-- A policy level strictly between calibration and the unweighted threshold. -/
def calibratedUpperPolicy {p : LoopParams}
    (threshold : ThresholdAssumption p) : ℝ :=
  threshold.βdagger / 2

/-- The upper comparison state used by the uniform prevention trap. -/
def calibratedUpperState (p : LoopParams)
    (threshold : ThresholdAssumption p) : LoopState :=
  (calibratedUpperPolicy threshold,
    p.stationaryStock (calibratedUpperPolicy threshold))

/-- The order neighborhood below the upper comparison state. -/
def calibratedPreventionNeighborhood (p : LoopParams)
    (threshold : ThresholdAssumption p) : Set LoopState :=
  Iic (calibratedUpperState p threshold)

/-- The upper comparison policy lies strictly before the threshold. -/
theorem calibratedUpperPolicy_mem {p : LoopParams}
    (threshold : ThresholdAssumption p) :
    calibratedUpperPolicy threshold ∈ Ioo (0 : ℝ) threshold.βdagger := by
  simp only [calibratedUpperPolicy]
  constructor <;> nlinarith [threshold.βdagger_mem.1]

/-- The upper comparison state lies in `B`. -/
theorem calibratedUpperState_mem {p : LoopParams}
    (model : DriftModelAssumptions p) (threshold : ThresholdAssumption p) :
    calibratedUpperState p threshold ∈ absorbingBox p := by
  have hu := calibratedUpperPolicy_mem threshold
  have hβ : calibratedUpperPolicy threshold ∈ Icc (0 : ℝ) 1 :=
    ⟨hu.1.le, hu.2.trans threshold.βdagger_mem.2 |>.le⟩
  exact ⟨hβ, stationaryStock_mem_stockInterval model hβ⟩

/-- The unweighted upper comparison state steps componentwise downward. -/
theorem loopMap_calibratedUpperState_le {p : LoopParams}
    (model : DriftModelAssumptions p) (threshold : ThresholdAssumption p) :
    p.loopMap (calibratedUpperState p threshold) ≤
      calibratedUpperState p threshold := by
  let βu := calibratedUpperPolicy threshold
  have hu := calibratedUpperPolicy_mem threshold
  have hβ : βu ∈ Icc (0 : ℝ) 1 :=
    ⟨hu.1.le, hu.2.trans threshold.βdagger_mem.2 |>.le⟩
  have hG : p.G βu < 0 :=
    threshold.G_neg_before βu ⟨hu.1, hu.2.trans threshold.βdagger_mem.2⟩ hu.2
  have hgrad : p.gradU βu (p.stationaryStock βu) < 0 := by
    rw [← G_eq_gradU_stationary]
    exact hG
  have hinput : βu + p.α * p.gradU βu (p.stationaryStock βu) ≤ βu := by
    nlinarith [model.α_pos]
  have hpolicy : p.deferenceStep βu (p.stationaryStock βu) ≤ βu := by
    have hclip := LoopParams.monotone_clipUnit hinput
    rw [clipUnit_eq_self hβ] at hclip
    exact hclip
  have hstock := stationaryStock_fixed model hβ
  exact ⟨hpolicy, hstock.le⟩

/-- The unweighted orbit from the prevention ceiling. -/
def calibratedUpperOrbit (p : LoopParams)
    (threshold : ThresholdAssumption p) (n : ℕ) : LoopState :=
  (p.loopMap^[n]) (calibratedUpperState p threshold)

/-- The comparison orbit follows the unweighted loop. -/
theorem calibratedUpperOrbit_isTrajectory (p : LoopParams)
    (threshold : ThresholdAssumption p) :
    IsLoopTrajectory p (calibratedUpperOrbit p threshold) := by
  intro n
  simp only [calibratedUpperOrbit, Function.iterate_succ_apply']

/-- The unweighted comparison orbit converges to calibration under `(SS)`;
global `(SS⁺)` is not needed. -/
theorem calibratedUpperOrbit_tendsto {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (threshold : ThresholdAssumption p) :
    Tendsto (calibratedUpperOrbit p threshold) atTop
      (𝓝 (calibratedPoint p)) := by
  have traj := calibratedUpperOrbit_isTrajectory p threshold
  have hstart := calibratedUpperState_mem model threshold
  obtain ⟨q, _hq, hlim, heq⟩ := comparableStep_convergesToFixedPoint
    model ss traj hstart (t := 0)
      (Or.inr (by simpa only [calibratedUpperOrbit, Function.iterate_zero_apply,
        Function.iterate_one, Function.comp_apply, Nat.zero_add,
        Nat.add_zero] using loopMap_calibratedUpperState_le model threshold))
  have hmem := trajectory_mem_absorbingBox model traj hstart
  have hanti := trajectory_tail_antitone_of_ge model ss traj hmem
    (t := 0) (by
      change p.loopMap (calibratedUpperState p threshold) ≤
        calibratedUpperState p threshold
      exact loopMap_calibratedUpperState_le model threshold)
  have horbit_le : ∀ n,
      calibratedUpperOrbit p threshold n ≤ calibratedUpperState p threshold := by
    intro n
    have := hanti (Nat.zero_le n)
    simpa only [Nat.add_zero, calibratedUpperOrbit,
      Function.iterate_zero_apply] using this
  have hqle : q ≤ calibratedUpperState p threshold := by
    exact isClosed_Iic.mem_of_tendsto hlim
      (Eventually.of_forall horbit_le)
  rcases equilibrium_mem_bistable_catalogue model threshold heq with
      hq | hq | hq
  · have hq' : q = calibratedPoint p := hq
    rwa [hq'] at hlim
  · have hβbad : threshold.βdagger ≤ calibratedUpperPolicy threshold := by
      simpa only [hq, saddlePoint, calibratedUpperState] using hqle.1
    exact (not_le_of_gt (calibratedUpperPolicy_mem threshold).2 hβbad).elim
  · have hβbad : (1 : ℝ) ≤ calibratedUpperPolicy threshold := by
      simpa only [hq, capturedPoint, calibratedUpperState] using hqle.1
    have hu := calibratedUpperPolicy_mem threshold
    exact (not_le_of_gt (hu.2.trans threshold.βdagger_mem.2) hβbad).elim

/-- The prevention order set is a genuine neighborhood of the calibrated
corner, independent of the civic weight. -/
theorem calibratedPreventionNeighborhood_mem_nhds {p : LoopParams}
    (model : DriftModelAssumptions p) (threshold : ThresholdAssumption p) :
    calibratedPreventionNeighborhood p threshold ∈ 𝓝 (calibratedPoint p) := by
  let U : Set LoopState :=
    Iio (calibratedUpperPolicy threshold) ×ˢ
      Iio (p.stationaryStock (calibratedUpperPolicy threshold))
  have hpoint : calibratedPoint p ∈ U := by
    constructor
    · exact (calibratedUpperPolicy_mem threshold).1
    · exact stationaryStock_strictMonoOn model (by norm_num)
        ⟨(calibratedUpperPolicy_mem threshold).1.le,
          ((calibratedUpperPolicy_mem threshold).2.trans
            threshold.βdagger_mem.2).le⟩
        (calibratedUpperPolicy_mem threshold).1
  have hUnhds : U ∈ 𝓝 (calibratedPoint p) :=
    (isOpen_Iio.prod isOpen_Iio).mem_nhds hpoint
  apply mem_of_superset hUnhds
  intro x hx
  exact ⟨hx.1.le, hx.2.le⟩

/-- A nonnegative weight lowers the first coordinate relative to the
unweighted map and leaves the stock step unchanged. -/
theorem civicWeightedLoopMap_le_loopMap {p : LoopParams} {ρ : ℝ}
    (model : DriftModelAssumptions p) (hρ : 0 ≤ ρ)
    {x : LoopState} (hD : 0 ≤ x.2) :
    civicWeightedLoopMap p ρ x ≤ p.loopMap x := by
  have hgrad := civicWeightedGradient_le_unweighted p
    (β := x.1) (D := x.2) hρ hD
  have hinput : civicWeightedInput p ρ x.1 x.2 ≤
      unclippedDeferenceInput p x.1 x.2 := by
    simp only [civicWeightedInput, unclippedDeferenceInput]
    nlinarith [mul_le_mul_of_nonneg_left hgrad model.α_pos.le]
  exact ⟨LoopParams.monotone_clipUnit hinput, le_rfl⟩

/-- A scheduled weighted trajectory starting in `B` remains there. -/
theorem civicWeightedScheduleTrajectory_mem_absorbingBox {p : LoopParams}
    (model : DriftModelAssumptions p) {ρ : ℕ → ℝ} {x : ℕ → LoopState}
    (traj : IsCivicWeightedScheduleTrajectory p ρ x)
    (hx0 : x 0 ∈ absorbingBox p) :
    ∀ n, x n ∈ absorbingBox p := by
  intro n
  induction n with
  | zero => exact hx0
  | succ n ih =>
      rw [traj n]
      exact civicWeightedInvariantBox model (ρ n) ih

/-- Every nonnegative civic-weight schedule is dominated by the single
unweighted comparison orbit. -/
theorem civicWeightedSchedule_le_calibratedUpperOrbit {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (threshold : ThresholdAssumption p) {ρ : ℕ → ℝ} (hρ : ∀ n, 0 ≤ ρ n)
    {x : ℕ → LoopState} (traj : IsCivicWeightedScheduleTrajectory p ρ x)
    (hx0 : x 0 ∈ absorbingBox p)
    (hupper : x 0 ≤ calibratedUpperState p threshold) :
    ∀ n, x n ≤ calibratedUpperOrbit p threshold n := by
  have hxmem := civicWeightedScheduleTrajectory_mem_absorbingBox model traj hx0
  have hytraj := calibratedUpperOrbit_isTrajectory p threshold
  have hymem := trajectory_mem_absorbingBox model hytraj
    (calibratedUpperState_mem model threshold)
  intro n
  induction n with
  | zero => simpa only [calibratedUpperOrbit, Function.iterate_zero_apply] using hupper
  | succ n ih =>
      rw [traj n, hytraj n]
      exact (civicWeightedLoopMap_le_loopMap (p := p) model (hρ n)
        (model.I_pos.le.trans (hxmem n).2.1)).trans
          (loopMap_monotoneOn_box model ss (hxmem n) (hymem n) ih)

/-- The scalar lower comparison path beneath every scheduled stock orbit. -/
def calibratedLowerStockPath (p : LoopParams) (D₀ : ℝ) (n : ℕ) : ℝ :=
  arithGeom (p.s 0) p.I D₀ n

/-- The lower comparison path converges to calibrated stationary stock. -/
theorem calibratedLowerStockPath_tendsto {p : LoopParams}
    (model : DriftModelAssumptions p) (D₀ : ℝ) :
    Tendsto (calibratedLowerStockPath p D₀) atTop
      (𝓝 (p.stationaryStock 0)) := by
  have hs := driftStockMultiplier_nonneg_le model (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
  have hlim := tendsto_affineRecursion (p.s 0) p.I D₀ hs.1
    (hs.2.trans_lt (sub_lt_self 1 model.lambda₀_pos))
  change Tendsto (arithGeom (p.s 0) p.I D₀) atTop
    (𝓝 (p.stationaryStock 0))
  simpa only [LoopParams.stationaryStock, model.no_content_gain, sub_zero] using hlim

/-- The affine calibrated-stock path is below every scheduled stock orbit. -/
theorem calibratedLowerStockPath_le_schedule {p : LoopParams}
    (model : DriftModelAssumptions p) {ρ : ℕ → ℝ} {x : ℕ → LoopState}
    (traj : IsCivicWeightedScheduleTrajectory p ρ x)
    (hx0 : x 0 ∈ absorbingBox p) :
    ∀ n, calibratedLowerStockPath p (x 0).2 n ≤ (x n).2 := by
  have hxmem := civicWeightedScheduleTrajectory_mem_absorbingBox model traj hx0
  intro n
  induction n with
  | zero => simp [calibratedLowerStockPath]
  | succ n ih =>
      have hβmono : p.s 0 ≤ p.s (x n).1 :=
        (driftStockMultiplier_strictMonoOn model).monotoneOn
          (by norm_num) (hxmem n).1 (hxmem n).1.1
      have hs0 : 0 ≤ p.s 0 :=
        (driftStockMultiplier_nonneg_le model (by norm_num)).1
      have hxD : 0 ≤ (x n).2 := model.I_pos.le.trans (hxmem n).2.1
      have hfirst := mul_le_mul_of_nonneg_left ih hs0
      have hfirst' : p.s 0 * arithGeom (p.s 0) p.I (x 0).2 n ≤
          p.s 0 * (x n).2 := by
        simpa only [calibratedLowerStockPath] using hfirst
      have hsecond := mul_le_mul_of_nonneg_right hβmono hxD
      rw [calibratedLowerStockPath, arithGeom_succ, traj n]
      simp only [civicWeightedLoopMap, LoopParams.stockStep,
        model.no_content_gain, add_zero]
      linarith [hfirst']

/-- Paper II, Theorem 3.15(i): the same neighborhood is attracted to calibration
under every nonnegative, possibly time-varying civic-weight schedule. -/
theorem civicWeighted_prevention_uniform_attraction {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (threshold : ThresholdAssumption p) {ρ : ℕ → ℝ} (hρ : ∀ n, 0 ≤ ρ n)
    {x : ℕ → LoopState} (traj : IsCivicWeightedScheduleTrajectory p ρ x)
    (hx0 : x 0 ∈ absorbingBox p)
    (hnear : x 0 ∈ calibratedPreventionNeighborhood p threshold) :
    Tendsto x atTop (𝓝 (calibratedPoint p)) := by
  have hxmem := civicWeightedScheduleTrajectory_mem_absorbingBox model traj hx0
  have hupper := civicWeightedSchedule_le_calibratedUpperOrbit
    model ss threshold hρ traj hx0 hnear
  have hy := calibratedUpperOrbit_tendsto model ss threshold
  have hyβ : Tendsto (fun n ↦ (calibratedUpperOrbit p threshold n).1)
      atTop (𝓝 0) := (continuous_fst.tendsto _).comp hy
  have hxβ : Tendsto (fun n ↦ (x n).1) atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ (hxmem n).1.1) (fun n ↦ (hupper n).1) hyβ
  have hlower := calibratedLowerStockPath_tendsto model (x 0).2
  have hyD : Tendsto (fun n ↦ (calibratedUpperOrbit p threshold n).2)
      atTop (𝓝 (p.stationaryStock 0)) := (continuous_snd.tendsto _).comp hy
  have hxD : Tendsto (fun n ↦ (x n).2)
      atTop (𝓝 (p.stationaryStock 0)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hyD
      (calibratedLowerStockPath_le_schedule model traj hx0)
      (fun n ↦ (hupper n).2)
  exact (Prod.tendsto_iff _ _).2 ⟨hxβ, hxD⟩

/-- Once exactly calibrated, every nonnegative schedule keeps the trajectory
there at every subsequent time. -/
theorem civicWeightedSchedule_calibrated_persists {p : LoopParams}
    (model : DriftModelAssumptions p) (threshold : ThresholdAssumption p)
    {ρ : ℕ → ℝ} (hρ : ∀ n, 0 ≤ ρ n) {x : ℕ → LoopState}
    (traj : IsCivicWeightedScheduleTrajectory p ρ x)
    (hx0 : x 0 = calibratedPoint p) :
    ∀ n, x n = calibratedPoint p := by
  intro n
  induction n with
  | zero => exact hx0
  | succ n ih =>
      rw [traj n, ih]
      simpa only [IsCivicWeightedEquilibrium, calibratedPoint] using
        civicWeighted_calibrated_fixed model threshold (hρ n)

/-! ## Strict release: attraction below and outward motion above -/

/-- Below the release price there is a terminal policy interval on which the
stationary weighted gradient is uniformly positive in sign. -/
theorem exists_captured_lower_policy {p : LoopParams}
    (model : DriftModelAssumptions p) {ρ : ℝ}
    (hρ : ρ < cureThreshold p) :
    ∃ b ∈ Ioo (0 : ℝ) 1, ∀ β ∈ Icc b 1,
      0 < civicWeightedGradient p ρ β (p.stationaryStock β) := by
  let A : Set ℝ := {β | ρ < weightedCureThreshold p β}
  have hopen : IsOpen A :=
    isOpen_lt continuous_const (continuous_weightedCureThreshold p)
  have hone : (1 : ℝ) ∈ A := by
    change ρ < weightedCureThreshold p 1
    rwa [weightedCureThreshold_one]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 1 hone
  let δ : ℝ := min (ε / 2) (1 / 2)
  let b : ℝ := 1 - δ
  have hδpos : 0 < δ := by
    simp only [δ]
    exact lt_min (half_pos hε) (by norm_num)
  have hδle : δ ≤ 1 / 2 := by
    simp only [δ]
    exact min_le_right _ _
  have hδε : δ < ε := by
    have : ε / 2 < ε := by linarith
    exact (min_le_left (ε / 2) (1 / 2)).trans_lt this
  have hb : b ∈ Ioo (0 : ℝ) 1 := by
    simp only [b]
    constructor <;> linarith
  refine ⟨b, hb, ?_⟩
  intro β hβ
  have hdist : dist β 1 < ε := by
    have hgap : 1 - β ≤ δ := by
      dsimp only [b] at hβ
      linarith [hβ.1]
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hβ.2)]
    linarith [hgap, hδε]
  have hΨ : ρ < weightedCureThreshold p β := hball hdist
  rw [civicWeightedGradient_stationary_eq model
    ⟨hb.1.le.trans hβ.1, hβ.2⟩]
  have hstock : 0 < p.stationaryStock β :=
    model.I_pos.trans_le (stationaryStock_mem_stockInterval model
      ⟨hb.1.le.trans hβ.1, hβ.2⟩).1
  exact mul_pos hstock (sub_pos.mpr hΨ)

/-- A generic constant-weight orbit. -/
def civicWeightedOrbit (p : LoopParams) (ρ : ℝ) (x₀ : LoopState)
    (n : ℕ) : LoopState :=
  ((civicWeightedLoopMap p ρ)^[n]) x₀

/-- The generic weighted orbit is a trajectory. -/
theorem civicWeightedOrbit_isTrajectory (p : LoopParams) (ρ : ℝ)
    (x₀ : LoopState) :
    IsCivicWeightedTrajectory p ρ (civicWeightedOrbit p ρ x₀) := by
  intro n
  simp only [civicWeightedOrbit, Function.iterate_succ_apply']

/-- A point on the positive-gradient stationary characteristic steps upward. -/
theorem captured_lower_state_le_step {p : LoopParams} {ρ b : ℝ}
    (model : DriftModelAssumptions p) (hb : b ∈ Icc (0 : ℝ) 1)
    (hgrad : 0 < civicWeightedGradient p ρ b (p.stationaryStock b)) :
    (b, p.stationaryStock b) ≤
      civicWeightedLoopMap p ρ (b, p.stationaryStock b) := by
  have hstock := stationaryStock_fixed model hb
  have hinput : b ≤ civicWeightedInput p ρ b (p.stationaryStock b) := by
    simp only [civicWeightedInput]
    nlinarith [model.α_pos]
  have hpolicy := LoopParams.monotone_clipUnit hinput
  rw [clipUnit_eq_self hb] at hpolicy
  exact ⟨hpolicy, hstock.ge⟩

/-- If the stationary gradient is positive on a terminal interval, the orbit
from its lower characteristic point converges monotonically to capture. -/
theorem civicWeightedOrbit_lower_tendsto_captured {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    {ρ b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1)
    (hcoop : ρ ≤ 2 * p.c * (1 - p.c))
    (hpositive : ∀ β ∈ Icc b 1,
      0 < civicWeightedGradient p ρ β (p.stationaryStock β)) :
    Tendsto (civicWeightedOrbit p ρ (b, p.stationaryStock b)) atTop
      (𝓝 (capturedPoint p)) := by
  let x₀ : LoopState := (b, p.stationaryStock b)
  let x := civicWeightedOrbit p ρ x₀
  have hbclosed : b ∈ Icc (0 : ℝ) 1 := ⟨hb.1.le, hb.2.le⟩
  have hx0 : x₀ ∈ absorbingBox p :=
    ⟨hbclosed, stationaryStock_mem_stockInterval model hbclosed⟩
  have traj : IsCivicWeightedTrajectory p ρ x :=
    civicWeightedOrbit_isTrajectory p ρ x₀
  have hfirst : x 0 ≤ x 1 := by
    change x₀ ≤ civicWeightedLoopMap p ρ x₀
    exact captured_lower_state_le_step model hbclosed
      (hpositive b ⟨le_rfl, hb.2.le⟩)
  obtain ⟨q, _hq, hlim, heq⟩ :=
    civicWeightedComparableStep_convergesToFixedPoint
      model ss hcoop traj hx0 (t := 0) (Or.inl hfirst)
  have hmem := civicWeightedTrajectory_mem_absorbingBox model traj hx0
  have hmono := civicWeightedTrajectory_tail_monotone_of_le
    model ss hcoop traj hmem (t := 0) hfirst
  have hx0_le : x₀ ≤ q := by
    have hle : ∀ n, x₀ ≤ x n := by
      intro n
      have := hmono (Nat.zero_le n)
      simpa only [Nat.add_zero, x, civicWeightedOrbit,
        Function.iterate_zero_apply] using this
    exact isClosed_Ici.mem_of_tendsto hlim (Eventually.of_forall hle)
  have hpolicy := congrArg Prod.fst heq
  simp only [civicWeightedLoopMap, civicWeightedDeferenceStep,
    civicWeightedInput] at hpolicy
  have hqβ : q.1 ∈ Icc (0 : ℝ) 1 := (show q ∈ absorbingBox p from _hq).1
  have hqD := civicWeightedEquilibrium_stock_eq_stationary model hqβ heq
  by_cases hone : q.1 = 1
  · have hq : q = capturedPoint p := by
      apply Prod.ext
      · simpa only [capturedPoint] using hone
      · simpa only [capturedPoint, hone] using hqD
    rwa [hq] at hlim
  by_cases hzero : q.1 = 0
  · have hbad : b ≤ 0 := by simpa only [x₀, hzero] using hx0_le.1
    exact (not_le_of_gt hb.1 hbad).elim
  have hqint : q.1 ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hqβ.1 (Ne.symm hzero), lt_of_le_of_ne hqβ.2 hone⟩
  have hinput : q.1 + p.α * civicWeightedGradient p ρ q.1 q.2 = q.1 :=
    (clipUnit_eq_interior_iff hqint).mp hpolicy
  have hgrad : civicWeightedGradient p ρ q.1 q.2 = 0 := by
    nlinarith [model.α_pos]
  have hqLower : b ≤ q.1 := by simpa only [x₀] using hx0_le.1
  have hpos := hpositive q.1 ⟨hqLower, hqint.2.le⟩
  rw [← hqD] at hpos
  exact (ne_of_gt hpos hgrad).elim

/-- Strictly below release, the captured corner has a genuine attracting
neighborhood. -/
theorem civicWeighted_captured_local_attraction {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    {ρ : ℝ} (_hρnonneg : 0 ≤ ρ) (hρ : ρ < cureThreshold p) :
    ∃ N : Set LoopState,
      N ∈ 𝓝 (capturedPoint p) ∧
      ∀ {x : ℕ → LoopState}, IsCivicWeightedTrajectory p ρ x →
        x 0 ∈ absorbingBox p → x 0 ∈ N →
        Tendsto x atTop (𝓝 (capturedPoint p)) := by
  obtain ⟨b, hb, hpositive⟩ := exists_captured_lower_policy model hρ
  let lower : LoopState := (b, p.stationaryStock b)
  let N : Set LoopState := Ici lower
  have hstationaryOne : p.stationaryStock 1 = p.I / p.lambda₀ := by
    simp [LoopParams.stationaryStock, LoopParams.s, model.no_content_gain]
  have hlowerPolicy : lower.1 < (capturedPoint p).1 := by
    simpa only [lower, capturedPoint] using hb.2
  have hlowerStock : lower.2 < (capturedPoint p).2 := by
    simpa only [lower, capturedPoint] using
      stationaryStock_strictMonoOn model ⟨hb.1.le, hb.2.le⟩
        (by norm_num) hb.2
  have hNnhds : N ∈ 𝓝 (capturedPoint p) := by
    let U : Set LoopState := Ioi lower.1 ×ˢ Ioi lower.2
    have hpoint : capturedPoint p ∈ U := ⟨hlowerPolicy, hlowerStock⟩
    have hUnhds : U ∈ 𝓝 (capturedPoint p) :=
      (isOpen_Ioi.prod isOpen_Ioi).mem_nhds hpoint
    exact mem_of_superset hUnhds fun _ hx ↦ ⟨hx.1.le, hx.2.le⟩
  refine ⟨N, hNnhds, ?_⟩
  intro x traj hx0 hxN
  have hcure_lt_ceiling : cureThreshold p < 2 * p.c * (1 - p.c) := by
    simp only [cureThreshold]
    have hpos : 0 < p.v * p.lambda₀ / p.I :=
      div_pos (mul_pos model.v_pos model.lambda₀_pos) model.I_pos
    linarith
  have hcoop : ρ ≤ 2 * p.c * (1 - p.c) :=
    (hρ.trans hcure_lt_ceiling).le
  have hmono := civicWeightedLoopMap_monotoneOn_box model ss hcoop
  have hxmem := civicWeightedTrajectory_mem_absorbingBox model traj hx0
  let lowerOrbit := civicWeightedOrbit p ρ lower
  have hlowerTraj : IsCivicWeightedTrajectory p ρ lowerOrbit :=
    civicWeightedOrbit_isTrajectory p ρ lower
  have hlowerMem : ∀ n, lowerOrbit n ∈ absorbingBox p :=
    civicWeightedTrajectory_mem_absorbingBox model hlowerTraj
      ⟨⟨hb.1.le, hb.2.le⟩,
        stationaryStock_mem_stockInterval model ⟨hb.1.le, hb.2.le⟩⟩
  have hlower_le : ∀ n, lowerOrbit n ≤ x n := by
    intro n
    induction n with
    | zero =>
        change lower ≤ x 0
        exact hxN
    | succ n ih =>
        rw [hlowerTraj n, traj n]
        exact hmono (hlowerMem n) (hxmem n) ih
  have hp3mem : capturedPoint p ∈ absorbingBox p := by
    constructor
    · simp [capturedPoint]
    · simpa only [capturedPoint, hstationaryOne] using
        (stationaryStock_mem_stockInterval model
          (show (1 : ℝ) ∈ Icc 0 1 by norm_num))
  have hp3fixed : IsCivicWeightedEquilibrium p ρ 1 (p.stationaryStock 1) :=
    (civicWeighted_captured_fixed_iff model ρ).2 hρ.le
  have hx_le : ∀ n, x n ≤ capturedPoint p := by
    intro n
    induction n with
    | zero =>
        exact ⟨hx0.1.2, by
          simpa only [capturedPoint, hstationaryOne] using hx0.2.2⟩
    | succ n ih =>
        rw [traj n]
        have hstep := hmono (hxmem n) hp3mem ih
        simpa only [IsCivicWeightedEquilibrium, capturedPoint] using
          hstep.trans_eq hp3fixed
  have hlowerLim : Tendsto lowerOrbit atTop (𝓝 (capturedPoint p)) :=
    civicWeightedOrbit_lower_tendsto_captured model ss hb hcoop hpositive
  have hlowerPolicyLim :=
    (continuous_fst.tendsto (capturedPoint p)).comp hlowerLim
  have hlowerStockLim :=
    (continuous_snd.tendsto (capturedPoint p)).comp hlowerLim
  have hpolicyLim : Tendsto (fun n ↦ (x n).1) atTop
      (𝓝 (capturedPoint p).1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlowerPolicyLim
      tendsto_const_nhds (fun n ↦ (hlower_le n).1) (fun n ↦ (hx_le n).1)
  have hstockLim : Tendsto (fun n ↦ (x n).2) atTop
      (𝓝 (capturedPoint p).2) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlowerStockLim
      tendsto_const_nhds (fun n ↦ (hlower_le n).2) (fun n ↦ (hx_le n).2)
  exact (Prod.tendsto_iff x (capturedPoint p)).2 ⟨hpolicyLim, hstockLim⟩

/-- Strictly above release, the captured corner itself moves immediately in
the outward policy direction. -/
theorem civicWeighted_captured_step_policy_lt_one {p : LoopParams}
    (model : DriftModelAssumptions p) {ρ : ℝ}
    (hρ : cureThreshold p < ρ) :
    (civicWeightedLoopMap p ρ (capturedPoint p)).1 < 1 := by
  have hstationaryOne : p.stationaryStock 1 = p.I / p.lambda₀ := by
    simp [LoopParams.stationaryStock, LoopParams.s, model.no_content_gain]
  have hgrad : civicWeightedGradient p ρ 1 (p.stationaryStock 1) < 0 := by
    rw [hstationaryOne]
    exact (civicWeightedGradient_captured_neg_iff model ρ).2 hρ
  have hinput : civicWeightedInput p ρ 1 (p.stationaryStock 1) < 1 := by
    simp only [civicWeightedInput]
    nlinarith [model.α_pos]
  have hmem := LoopParams.clipUnit_mem
    (civicWeightedInput p ρ 1 (p.stationaryStock 1))
  have hne : LoopParams.clipUnit
      (civicWeightedInput p ρ 1 (p.stationaryStock 1)) ≠ 1 := by
    intro hone
    have := (clipUnit_eq_one_iff _).mp hone
    linarith
  simpa only [civicWeightedLoopMap, civicWeightedDeferenceStep,
    capturedPoint] using lt_of_le_of_ne hmem.2 hne

/-- The outward-gradient statement holds on a full neighborhood of capture:
every admissible point there takes a strictly lower policy step. -/
theorem civicWeighted_captured_outward_neighborhood {p : LoopParams}
    (model : DriftModelAssumptions p) {ρ : ℝ}
    (hρ : cureThreshold p < ρ) :
    ∃ N : Set LoopState, N ∈ 𝓝 (capturedPoint p) ∧
      ∀ x ∈ N, x ∈ absorbingBox p →
        (civicWeightedLoopMap p ρ x).1 < x.1 := by
  let N : Set LoopState :=
    {x | civicWeightedGradient p ρ x.1 x.2 < 0} ∩
      (Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))
  have hopen : IsOpen N := by
    apply IsOpen.inter
    · apply isOpen_lt
      · simp only [civicWeightedGradient, LoopParams.gradU]
        fun_prop
      · fun_prop
    · exact isOpen_Ioi.prod isOpen_univ
  have hp3 : capturedPoint p ∈ N := by
    constructor
    · have hstationaryOne : p.stationaryStock 1 = p.I / p.lambda₀ := by
        simp [LoopParams.stationaryStock, LoopParams.s, model.no_content_gain]
      change civicWeightedGradient p ρ 1 (p.stationaryStock 1) < 0
      rw [hstationaryOne]
      exact (civicWeightedGradient_captured_neg_iff model ρ).2 hρ
    · exact ⟨by simp [capturedPoint], mem_univ _⟩
  refine ⟨N, hopen.mem_nhds hp3, ?_⟩
  intro x hx _hxbox
  have hgrad : civicWeightedGradient p ρ x.1 x.2 < 0 := hx.1
  have hβpos : 0 < x.1 := hx.2.1
  have hinput : civicWeightedInput p ρ x.1 x.2 < x.1 := by
    simp only [civicWeightedInput]
    nlinarith [model.α_pos]
  by_cases hnonpos : civicWeightedInput p ρ x.1 x.2 ≤ 0
  · have hclip := (clipUnit_eq_zero_iff _).2 hnonpos
    simpa only [civicWeightedLoopMap, civicWeightedDeferenceStep, hclip] using hβpos
  · have hinputpos : 0 < civicWeightedInput p ρ x.1 x.2 := lt_of_not_ge hnonpos
    have hinputone : civicWeightedInput p ρ x.1 x.2 < 1 :=
      hinput.trans_le _hxbox.1.2
    have hclip := clipUnit_eq_self
      ⟨hinputpos.le, hinputone.le⟩
    simpa only [civicWeightedLoopMap, civicWeightedDeferenceStep, hclip] using hinput

/-! ## Price coincidence and the descending-crossing spectrum -/

/-- Release and restoration coincide exactly when the weighted crossing
function attains its maximum at the captured endpoint. -/
theorem restorationPrice_eq_cureThreshold_iff (p : LoopParams) :
    restorationPrice p = cureThreshold p ↔
      ∀ β ∈ Icc (0 : ℝ) 1,
        weightedCureThreshold p β ≤ weightedCureThreshold p 1 := by
  constructor
  · intro hprices β hβ
    rw [weightedCureThreshold_one, ← hprices]
    exact (restorationPrice_isGreatest p).2 ⟨β, hβ, rfl⟩
  · intro hmax
    apply le_antisymm
    · obtain ⟨β, hβ, hβmax⟩ := exists_restorationPrice_maximizer p
      rw [← hβmax, ← weightedCureThreshold_one]
      exact hmax β hβ
    · exact cureThreshold_le_restorationPrice p

/-- `CureDominance` is sufficient for release and restoration to coincide. -/
theorem restorationPrice_eq_cureThreshold_of_cureDominance {p : LoopParams}
    (model : DriftModelAssumptions p) (dom : CureDominance p) :
    restorationPrice p = cureThreshold p := by
  apply (restorationPrice_eq_cureThreshold_iff p).2
  intro β hβ
  rw [weightedCureThreshold_one]
  exact weightedCureThreshold_le_cureThreshold model dom hβ

/-- If release and restoration coincide, the cooperative restoration window
has strictly positive width. -/
theorem restorationPrice_lt_cooperativityCeiling_of_eq {p : LoopParams}
    (model : DriftModelAssumptions p)
    (hprices : restorationPrice p = cureThreshold p) :
    restorationPrice p < 2 * p.c * (1 - p.c) := by
  rw [hprices, cureThreshold]
  have hpositive : 0 < p.v * p.lambda₀ / p.I :=
    div_pos (mul_pos model.v_pos model.lambda₀_pos) model.I_pos
  linarith

/-- Under the paper's threshold hypothesis, late restoration has a strictly
positive price relative to prevention. -/
theorem restorationPrice_pos {p : LoopParams}
    (model : DriftModelAssumptions p) (threshold : ThresholdAssumption p) :
    0 < restorationPrice p :=
  (cureThreshold_pos model threshold).trans_le
    (cureThreshold_le_restorationPrice p)

/-- The algebraic derivative of the weighted crossing function `Ψ`. -/
def weightedCureThresholdSlope (p : LoopParams) (β : ℝ) : ℝ :=
  -2 * p.c ^ 2 + p.v * p.sSlope β / p.I

/-- The named slope is the derivative of the weighted crossing function. -/
theorem hasDerivAt_weightedCureThreshold (p : LoopParams) (β : ℝ) :
    HasDerivAt (fun x : ℝ ↦ weightedCureThreshold p x)
      (weightedCureThresholdSlope p β) β := by
  have hlinear : HasDerivAt (fun x : ℝ ↦ 2 * p.c * (1 - p.c * x))
      (-2 * p.c ^ 2) β := by
    exact ((((hasDerivAt_id β).const_mul p.c).const_sub (1 : ℝ)).const_mul
      (2 * p.c)).congr_deriv (by ring)
  have hresidual : HasDerivAt (fun x : ℝ ↦ 1 - p.s x)
      (-p.sSlope β) β := by
    exact ((p.hasDerivAt_s β).const_sub (1 : ℝ)).congr_deriv (by ring)
  have hpenalty : HasDerivAt
      (fun x : ℝ ↦ p.v * (1 - p.s x) / p.I)
      (-p.v * p.sSlope β / p.I) β := by
    exact ((hresidual.const_mul p.v).div_const p.I).congr_deriv (by ring)
  change HasDerivAt
    (fun x : ℝ ↦ 2 * p.c * (1 - p.c * x) -
      p.v * (1 - p.s x) / p.I)
    (-2 * p.c ^ 2 + p.v * p.sSlope β / p.I) β
  exact (hlinear.sub hpenalty).congr_deriv (by ring)

/-- The Jacobian of the unclipped civic-weighted map at an interior state. -/
def weightedInteriorLoopJacobian (p : LoopParams) (ρ β D : ℝ) : LoopJacobian where
  a := 1 - 2 * p.α * p.c ^ 2 * D
  b := p.α * (2 * p.c * (1 - p.c * β) - ρ)
  cJ := p.sSlope β * D
  d := p.s β

/-- Both explicit real roots lie strictly inside the unit circle. -/
def LoopJacobian.IsLinearlyStable (J : LoopJacobian) : Prop :=
  |J.largerEigenvalue| < 1 ∧ |J.smallerEigenvalue| < 1

/-- A nonnegative planar Jacobian with `p(1)>0` and `d<1` is linearly stable.
The trace is nonnegative, so the smaller root cannot have larger magnitude
than the larger root. -/
theorem LoopJacobian.isLinearlyStable_of_nonnegative_of_charPoly_one_pos
    (J : LoopJacobian) (ha : 0 ≤ J.a) (hb : 0 ≤ J.b)
    (hcJ : 0 ≤ J.cJ) (hd : 0 ≤ J.d) (hdlt : J.d < 1)
    (hpoly : 0 < J.charPoly 1) : J.IsLinearlyStable := by
  have hdisc : 0 ≤ J.discriminant := J.discriminant_nonneg hb hcJ
  have hsmall : J.smallerEigenvalue < 1 :=
    J.smallerEigenvalue_lt_one hdlt (mul_nonneg hb hcJ)
  have hfactor := J.charPoly_eq_mul_eigenvalues hdisc 1
  rw [hfactor] at hpoly
  have hright : 0 < 1 - J.smallerEigenvalue := sub_pos.mpr hsmall
  have hleft : 0 < 1 - J.largerEigenvalue :=
    pos_of_mul_pos_left hpoly hright.le
  have hlarge : J.largerEigenvalue < 1 := sub_pos.mp hleft
  have horder := J.smallerEigenvalue_le_largerEigenvalue
  have hsum : J.smallerEigenvalue + J.largerEigenvalue = J.a + J.d := by
    simp only [LoopJacobian.smallerEigenvalue, LoopJacobian.largerEigenvalue,
      LoopJacobian.trace]
    ring
  have hsmallLower : (-1 : ℝ) < J.smallerEigenvalue := by
    have hsum_nonneg : 0 ≤ J.smallerEigenvalue + J.largerEigenvalue := by
      rw [hsum]
      positivity
    linarith
  have hlargeLower : (-1 : ℝ) < J.largerEigenvalue :=
    hsmallLower.trans_le horder
  exact ⟨(abs_lt.mpr ⟨hlargeLower, hlarge⟩),
    abs_lt.mpr ⟨hsmallLower, hsmall⟩⟩

/-- An interior solution of `Ψ(β)=ρ` is an actual fixed point of the
projected weighted map. -/
theorem civicWeighted_interior_crossing_fixed {p : LoopParams}
    (model : DriftModelAssumptions p) {ρ β : ℝ}
    (hβ : β ∈ Ioo (0 : ℝ) 1)
    (hcross : weightedCureThreshold p β = ρ) :
    IsCivicWeightedEquilibrium p ρ β (p.stationaryStock β) := by
  have hβclosed : β ∈ Icc (0 : ℝ) 1 := ⟨hβ.1.le, hβ.2.le⟩
  have hgradient :
      civicWeightedGradient p ρ β (p.stationaryStock β) = 0 := by
    rw [civicWeightedGradient_stationary_eq model hβclosed, hcross]
    ring
  have hstock := stationaryStock_fixed model hβclosed
  apply Prod.ext
  · simp only [civicWeightedLoopMap, civicWeightedDeferenceStep,
      civicWeightedInput, hgradient, mul_zero, add_zero]
    exact clipUnit_eq_self hβclosed
  · simpa only [civicWeightedLoopMap] using hstock

/-- At a weighted interior crossing all four Jacobian entries are
nonnegative, with strict off-diagonals. -/
theorem weightedCrossingJacobian_entry_bounds {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    {ρ β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1)
    (hcross : weightedCureThreshold p β = ρ) :
    let J := weightedInteriorLoopJacobian p ρ β (p.stationaryStock β)
    0 ≤ J.a ∧ J.a ≤ 1 ∧ 0 < J.b ∧ 0 < J.cJ ∧
      0 ≤ J.d ∧ J.d < 1 := by
  let D := p.stationaryStock β
  let J := weightedInteriorLoopJacobian p ρ β D
  have hβclosed : β ∈ Icc (0 : ℝ) 1 := ⟨hβ.1.le, hβ.2.le⟩
  have hD := stationaryStock_mem_stockInterval model hβclosed
  have hDpos : 0 < D := model.I_pos.trans_le hD.1
  have hcoefficient : 0 ≤ 2 * p.α * p.c ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) (sq_nonneg p.c)
  have hceiling : 2 * p.α * p.c ^ 2 * (p.I / p.lambda₀) ≤ 1 := by
    rw [show 2 * p.α * p.c ^ 2 * (p.I / p.lambda₀) =
      (2 * p.α * p.c ^ 2 * p.I) / p.lambda₀ by ring]
    exact (div_le_one model.lambda₀_pos).2 ss.bound
  have hscaled : 2 * p.α * p.c ^ 2 * D ≤ 1 :=
    (mul_le_mul_of_nonneg_left hD.2 hcoefficient).trans hceiling
  have ha₀ : 0 ≤ J.a := by
    change 0 ≤ 1 - 2 * p.α * p.c ^ 2 * D
    linarith
  have ha₁ : J.a ≤ 1 := by
    change 1 - 2 * p.α * p.c ^ 2 * D ≤ 1
    have : 0 ≤ 2 * p.α * p.c ^ 2 * D :=
      mul_nonneg hcoefficient hDpos.le
    linarith
  have hweighted : 2 * p.c * (1 - p.c * β) - ρ =
      p.v * (1 - p.s β) / p.I := by
    simp only [weightedCureThreshold] at hcross
    linarith
  have hb : 0 < J.b := by
    change 0 < p.α * (2 * p.c * (1 - p.c * β) - ρ)
    rw [hweighted]
    exact mul_pos model.α_pos
      (div_pos (mul_pos model.v_pos (one_sub_s_pos model hβclosed)) model.I_pos)
  have hcJ : 0 < J.cJ := by
    change 0 < p.sSlope β * D
    exact mul_pos (sSlope_pos model hβ) hDpos
  have hs := driftStockMultiplier_nonneg_le model hβclosed
  have hd₀ : 0 ≤ J.d := by simpa only [J, weightedInteriorLoopJacobian] using hs.1
  have hd₁ : J.d < 1 := by
    change p.s β < 1
    exact hs.2.trans_lt (sub_lt_self 1 model.lambda₀_pos)
  exact ⟨ha₀, ha₁, hb, hcJ, hd₀, hd₁⟩

/-- At a weighted crossing, the characteristic polynomial at one has sign
opposite to the orientation of `Ψ`. -/
theorem weightedCrossingJacobian_charPoly_one_eq_neg_slope
    {p : LoopParams} (model : DriftModelAssumptions p) {ρ β : ℝ}
    (hcross : weightedCureThreshold p β = ρ) :
    let D := p.stationaryStock β
    let J := weightedInteriorLoopJacobian p ρ β D
    J.charPoly 1 =
      -(p.α * D * (1 - p.s β)) * weightedCureThresholdSlope p β := by
  let D := p.stationaryStock β
  let J := weightedInteriorLoopJacobian p ρ β D
  have hweighted : 2 * p.c * (1 - p.c * β) - ρ =
      p.v * (1 - p.s β) / p.I := by
    simp only [weightedCureThreshold] at hcross
    linarith
  simp only [LoopJacobian.charPoly, LoopJacobian.trace, LoopJacobian.det,
    weightedInteriorLoopJacobian]
  rw [hweighted]
  simp only [weightedCureThresholdSlope]
  field_simp [model.I_pos.ne']
  ring

/-- Paper II, Theorem 3.15(iii): every transversal descending weighted crossing
is a linearly stable interior equilibrium. -/
theorem civicWeighted_descendingCrossing_linearlyStable {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    {ρ β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1)
    (hcross : weightedCureThreshold p β = ρ)
    (hdescending : weightedCureThresholdSlope p β < 0) :
    IsCivicWeightedEquilibrium p ρ β (p.stationaryStock β) ∧
      (weightedInteriorLoopJacobian p ρ β
        (p.stationaryStock β)).IsLinearlyStable := by
  let D := p.stationaryStock β
  let J := weightedInteriorLoopJacobian p ρ β D
  have hβclosed : β ∈ Icc (0 : ℝ) 1 := ⟨hβ.1.le, hβ.2.le⟩
  have hDpos : 0 < D := model.I_pos.trans_le
    (stationaryStock_mem_stockInterval model hβclosed).1
  have hwall : 0 < 1 - p.s β := one_sub_s_pos model hβclosed
  have hentries := weightedCrossingJacobian_entry_bounds model ss hβ hcross
  have hchar := weightedCrossingJacobian_charPoly_one_eq_neg_slope model hcross
  have hscale : 0 < p.α * D * (1 - p.s β) :=
    mul_pos (mul_pos model.α_pos hDpos) hwall
  have hpoly : 0 < J.charPoly 1 := by
    rw [hchar]
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos hscale) hdescending
  refine ⟨civicWeighted_interior_crossing_fixed model hβ hcross, ?_⟩
  exact J.isLinearlyStable_of_nonnegative_of_charPoly_one_pos
    hentries.1 hentries.2.2.1.le hentries.2.2.2.1.le
      hentries.2.2.2.2.1 hentries.2.2.2.2.2 hpoly

/-! ## Canonical theorem package -/

/-- The four clauses of the prevention--release--restoration price schedule,
kept as named fields so downstream audit results can depend on exactly the
part they use. -/
structure HysteresisPriceScheduleConclusions (p : LoopParams)
    (threshold : ThresholdAssumption p) : Prop where
  stationarySign : ∀ {ρ β : ℝ}, β ∈ Icc (0 : ℝ) 1 →
    (civicWeightedGradient p ρ β (p.stationaryStock β) < 0 ↔
      weightedCureThreshold p β < ρ)
  preventionNeighborhood : calibratedPreventionNeighborhood p threshold ∈
    𝓝 (calibratedPoint p)
  preventionAttraction : ∀ {ρ : ℕ → ℝ}, (∀ n, 0 ≤ ρ n) →
    ∀ {x : ℕ → LoopState}, IsCivicWeightedScheduleTrajectory p ρ x →
      x 0 ∈ absorbingBox p →
      x 0 ∈ calibratedPreventionNeighborhood p threshold →
      Tendsto x atTop (𝓝 (calibratedPoint p))
  preventionPersistence : ∀ {ρ : ℕ → ℝ}, (∀ n, 0 ≤ ρ n) →
    ∀ {x : ℕ → LoopState}, IsCivicWeightedScheduleTrajectory p ρ x →
      x 0 = calibratedPoint p → ∀ n, x n = calibratedPoint p
  releasePrice : weightedCureThreshold p 1 = cureThreshold p
  capturedStock : p.stationaryStock 1 = p.I / p.lambda₀
  releaseFactor : ∀ ρ,
    civicWeightedGradient p ρ 1 (p.stationaryStock 1) =
      (p.I / p.lambda₀) * (cureThreshold p - ρ)
  releaseFixed : ∀ ρ,
    IsCivicWeightedEquilibrium p ρ 1 (p.stationaryStock 1) ↔
      ρ ≤ cureThreshold p
  releaseAttraction : ∀ {ρ : ℝ}, 0 ≤ ρ → ρ < cureThreshold p →
    ∃ N : Set LoopState, N ∈ 𝓝 (capturedPoint p) ∧
      ∀ {x : ℕ → LoopState}, IsCivicWeightedTrajectory p ρ x →
        x 0 ∈ absorbingBox p → x 0 ∈ N →
        Tendsto x atTop (𝓝 (capturedPoint p))
  releaseOutward : ∀ {ρ : ℝ}, cureThreshold p < ρ →
    ∃ N : Set LoopState, N ∈ 𝓝 (capturedPoint p) ∧
      ∀ x ∈ N, x ∈ absorbingBox p →
        (civicWeightedLoopMap p ρ x).1 < x.1
  releaseEquality :
    civicWeightedGradient p (cureThreshold p) 1 (p.stationaryStock 1) = 0
  restorationMaximum :
    IsGreatest (weightedCureThreshold p '' Icc (0 : ℝ) 1)
      (restorationPrice p)
  release_le_restoration : cureThreshold p ≤ restorationPrice p
  restorationGradient : ∀ {ρ β : ℝ}, restorationPrice p < ρ →
    β ∈ Icc (0 : ℝ) 1 →
      civicWeightedGradient p ρ β (p.stationaryStock β) < 0
  restorationUnique : ∀ {ρ β D : ℝ}, restorationPrice p < ρ →
    (IsCivicWeightedEquilibrium p ρ β D ↔
      (β, D) = calibratedPoint p)
  restorationConvergence : ∀ {ρ : ℝ}, restorationPrice p < ρ →
    ρ ≤ 2 * p.c * (1 - p.c) →
    WeightedConvergentStepAssumption p ρ →
    ∀ {x : ℕ → LoopState}, IsCivicWeightedTrajectory p ρ x →
      x 0 ∈ absorbingBox p →
      Tendsto x atTop (𝓝 (calibratedPoint p))
  cooperativeCoefficient : ∀ {ρ β : ℝ},
    ρ ≤ 2 * p.c * (1 - p.c) → β ∈ Icc (0 : ℝ) 1 →
      0 ≤ 2 * p.c * (1 - p.c * β) - ρ
  bandCrossing : ∀ {ρ : ℝ}, cureThreshold p < ρ →
    ρ < restorationPrice p →
      ∃ β ∈ Ioo (0 : ℝ) 1, weightedCureThreshold p β = ρ
  descendingCrossingStable : ∀ {ρ β : ℝ}, β ∈ Ioo (0 : ℝ) 1 →
    weightedCureThreshold p β = ρ →
    weightedCureThresholdSlope p β < 0 →
      IsCivicWeightedEquilibrium p ρ β (p.stationaryStock β) ∧
        (weightedInteriorLoopJacobian p ρ β
          (p.stationaryStock β)).IsLinearlyStable
  priceCoincidence : restorationPrice p = cureThreshold p ↔
    ∀ β ∈ Icc (0 : ℝ) 1,
      weightedCureThreshold p β ≤ weightedCureThreshold p 1
  dominanceCoincidence : CureDominance p →
    restorationPrice p = cureThreshold p
  coincidenceWindow : restorationPrice p = cureThreshold p →
    restorationPrice p < 2 * p.c * (1 - p.c)
  lateInterventionPrice_pos : 0 < restorationPrice p

/-- Paper II, Theorem 3.15 (`thm:hyst`), `civic_drift.tex:296`.

The theorem separates the zero prevention price, the exact release
threshold at capture, and the maximum stationary restoration price. It also
contains the policy-schedule quantifiers, weighted `(SS⁺)` convergence, and
the descending-crossing spectrum rather than leaving those dynamics implicit.
-/
theorem hysteresisAsymmetry {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (threshold : ThresholdAssumption p) :
    HysteresisPriceScheduleConclusions p threshold := by
  refine {
    stationarySign := fun {ρ β} hβ ↦
      civicWeightedGradient_stationary_neg_iff model hβ
    preventionNeighborhood := calibratedPreventionNeighborhood_mem_nhds
      model threshold
    preventionAttraction := fun {ρ} hρ {x} traj hx₀ hnear ↦
      civicWeighted_prevention_uniform_attraction
        model ss threshold hρ traj hx₀ hnear
    preventionPersistence := fun {ρ} hρ {x} traj hx₀ ↦
      civicWeightedSchedule_calibrated_persists model threshold hρ traj hx₀
    releasePrice := weightedCureThreshold_one
    capturedStock := by
      simp [LoopParams.stationaryStock, LoopParams.s, model.no_content_gain]
    releaseFactor := civicWeightedGradient_captured_stationary_eq model
    releaseFixed := fun ρ ↦ civicWeighted_captured_fixed_iff model ρ
    releaseAttraction := fun {ρ} hρnonneg hρ ↦
      civicWeighted_captured_local_attraction model ss hρnonneg hρ
    releaseOutward := fun {ρ} hρ ↦
      civicWeighted_captured_outward_neighborhood model hρ
    releaseEquality := civicWeightedGradient_captured_at_cure_eq_zero model
    restorationMaximum := restorationPrice_isGreatest p
    release_le_restoration := cureThreshold_le_restorationPrice p
    restorationGradient := fun {ρ β} hρ hβ ↦
      civicWeightedGradient_stationary_neg_of_restoration model hρ hβ
    restorationUnique := fun {ρ β D} hρ ↦
      civicWeightedEquilibrium_iff_calibrated_of_restoration model threshold hρ
    restorationConvergence := fun {ρ} hrestore hcoop ssplus {x} traj hx₀ ↦
      civicWeighted_restoration_tendsto_calibrated
        model threshold hrestore hcoop ssplus traj hx₀
    cooperativeCoefficient := fun {ρ β} hcoop hβ ↦
      weighted_stock_coefficient_nonnegative model hcoop hβ
    bandCrossing := fun {ρ} hlow hhigh ↦
      exists_weightedCrossing_of_between hlow hhigh
    descendingCrossingStable := fun {ρ β} hβ hcross hslope ↦
      civicWeighted_descendingCrossing_linearlyStable
        model ss hβ hcross hslope
    priceCoincidence := restorationPrice_eq_cureThreshold_iff p
    dominanceCoincidence := restorationPrice_eq_cureThreshold_of_cureDominance model
    coincidenceWindow := restorationPrice_lt_cooperativityCeiling_of_eq model
    lateInterventionPrice_pos := restorationPrice_pos model threshold }

#print axioms civicWeightedGradient_stationary_eq
#print axioms civicWeightedGradient_stationary_neg_iff
#print axioms civicWeightedInvariantBox
#print axioms civicWeighted_calibrated_fixed
#print axioms civicWeighted_captured_fixed_iff
#print axioms civicWeightedGradient_captured_at_cure_eq_zero
#print axioms civicWeightedGradient_captured_stationary_eq
#print axioms continuous_weightedCureThreshold
#print axioms restorationPrice_isGreatest
#print axioms exists_restorationPrice_maximizer
#print axioms cureThreshold_le_restorationPrice
#print axioms civicWeightedGradient_stationary_neg_of_restoration
#print axioms exists_weightedCrossing_of_between
#print axioms civicWeightedEquilibrium_stock_eq_stationary
#print axioms civicWeightedEquilibrium_eq_calibrated_of_restoration
#print axioms civicWeightedEquilibrium_iff_calibrated_of_restoration
#print axioms weightedConvergentStepDenominator_pos
#print axioms WeightedConvergentStepAssumption.stockDiagonalLower_pos
#print axioms WeightedConvergentStepAssumption.toStrictSmallStep
#print axioms WeightedConvergentStepAssumption.policyDiagonalLower_pos
#print axioms weightedPolicyStockUpper_pos
#print axioms WeightedConvergentStepAssumption.crossProduct_lt_diagonalProduct
#print axioms weighted_stock_coefficient_nonnegative
#print axioms civicWeightedInput_mono_policy
#print axioms civicWeightedInput_mono_stock
#print axioms civicWeightedLoopMap_monotoneOn_box
#print axioms continuous_civicWeightedLoopMap
#print axioms civicWeightedTrajectory_mem_absorbingBox
#print axioms civicWeighted_southeast_input_difference_lower
#print axioms civicWeighted_northwest_input_difference_upper
#print axioms civicWeightedTrajectory_tail_monotone_of_le
#print axioms civicWeightedTrajectory_tail_antitone_of_ge
#print axioms civicWeightedTrajectory_limit_is_equilibrium
#print axioms civicWeightedComparableStep_convergesToFixedPoint
#print axioms civicWeighted_no_southeast_to_northwest
#print axioms civicWeighted_no_northwest_to_southeast
#print axioms civicWeighted_globalConvergence_of_convergentStep
#print axioms civicWeighted_restoration_tendsto_calibrated
#print axioms calibratedUpperPolicy_mem
#print axioms calibratedUpperState_mem
#print axioms loopMap_calibratedUpperState_le
#print axioms calibratedUpperOrbit_isTrajectory
#print axioms calibratedUpperOrbit_tendsto
#print axioms calibratedPreventionNeighborhood_mem_nhds
#print axioms civicWeightedLoopMap_le_loopMap
#print axioms civicWeightedScheduleTrajectory_mem_absorbingBox
#print axioms civicWeightedSchedule_le_calibratedUpperOrbit
#print axioms calibratedLowerStockPath_tendsto
#print axioms calibratedLowerStockPath_le_schedule
#print axioms civicWeighted_prevention_uniform_attraction
#print axioms civicWeightedSchedule_calibrated_persists
#print axioms exists_captured_lower_policy
#print axioms civicWeightedOrbit_isTrajectory
#print axioms captured_lower_state_le_step
#print axioms civicWeightedOrbit_lower_tendsto_captured
#print axioms civicWeighted_captured_local_attraction
#print axioms civicWeighted_captured_step_policy_lt_one
#print axioms civicWeighted_captured_outward_neighborhood
#print axioms restorationPrice_eq_cureThreshold_iff
#print axioms restorationPrice_eq_cureThreshold_of_cureDominance
#print axioms restorationPrice_lt_cooperativityCeiling_of_eq
#print axioms restorationPrice_pos
#print axioms hasDerivAt_weightedCureThreshold
#print axioms LoopJacobian.isLinearlyStable_of_nonnegative_of_charPoly_one_pos
#print axioms civicWeighted_interior_crossing_fixed
#print axioms weightedCrossingJacobian_entry_bounds
#print axioms weightedCrossingJacobian_charPoly_one_eq_neg_slope
#print axioms civicWeighted_descendingCrossing_linearlyStable
#print axioms hysteresisAsymmetry

end

end CivicAlignment.PaperII
