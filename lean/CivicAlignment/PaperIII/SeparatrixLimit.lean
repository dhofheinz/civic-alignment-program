/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.BurnMonotonicity
import CivicAlignment.PaperIII.Trap

/-!
# Paper III: the separatrix-scale limit

This file formalizes `prop:seplimit`.  The critical projected-jump excess is
the supremum of the admissible excesses whose policy limit stays below the
saddle.  Strict two-sided separation follows from the burn
trichotomy; continuity of the policy-limit function is not needed.  Fixed
finite transits then transfer to the full loop and enter the capture and
calibration regions supplied by `lem:charcap` and `lem:trap`.
-/

namespace CivicAlignment.PaperIII

open Filter Function Set Topology

noncomputable section

/-! ## Projected jump limits and the critical excess -/

/-- The policy limit of a projected jump orbit, represented as the supremum
of its monotone policy coordinates. -/
noncomputable def projectedJumpPolicyLimit
    (p : LoopParams) (β₀ E₀ : ℝ) : ℝ :=
  sSup (Set.range fun n : ℕ ↦ (projJumpOrbit p (β₀, E₀) n).1)

/-- The canonical projected policy orbit converges to
`projectedJumpPolicyLimit`. -/
theorem projJumpOrbit_policy_tendsto_limit {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {β₀ E₀ : ℝ} (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1) (hE₀ : 0 ≤ E₀) :
    Tendsto (fun n ↦ (projJumpOrbit p (β₀, E₀) n).1) atTop
      (nhds (projectedJumpPolicyLimit p β₀ E₀)) := by
  have hmono := projJumpOrbit_policy_monotone (x₀ := (β₀, E₀))
    model hgain hβ₀ hE₀
  have hbdd : BddAbove
      (Set.range fun n ↦ (projJumpOrbit p (β₀, E₀) n).1) :=
    ⟨1, by rintro y ⟨n, rfl⟩; exact (projJumpOrbit_policy_mem hβ₀ n).2⟩
  exact tendsto_atTop_ciSup hmono hbdd

/-- Zero initial excess leaves the projected jump state fixed. -/
theorem projJumpOrbit_zero_excess {p : LoopParams} {β₀ : ℝ}
    (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    projJumpOrbit p (β₀, 0) n = (β₀, 0) := by
  induction n with
  | zero => exact projJumpOrbit_zero p (β₀, 0)
  | succ n ih =>
      rw [projJumpOrbit_succ, ih]
      simp only [projectedJumpMap, mul_zero, add_zero]
      rw [clipUnit_eq_self hβ₀]

/-- The zero-excess policy limit is the initial policy. -/
theorem projectedJumpPolicyLimit_zero {p : LoopParams} {β₀ : ℝ}
    (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1) :
    projectedJumpPolicyLimit p β₀ 0 = β₀ := by
  simp only [projectedJumpPolicyLimit, projJumpOrbit_zero_excess hβ₀,
    Set.range_const, csSup_singleton]

/-- `JumpOrbitUniformlyBelow` is exactly admissibility plus a strict bound on
the canonical projected policy limit. -/
theorem jumpOrbitUniformlyBelow_iff {p : LoopParams} {βdagger β₀ E₀ : ℝ} :
    JumpOrbitUniformlyBelow p βdagger β₀ E₀ ↔
      0 ≤ E₀ ∧ 2 * p.c ^ 2 * E₀ < 1 ∧
        projectedJumpPolicyLimit p β₀ E₀ < βdagger := by
  simp only [JumpOrbitUniformlyBelow, projectedJumpPolicyLimit, projJumpOrbit]

/-- The paper's “saddle-bracketing transit” hypothesis: the starting policy
is below the saddle, while some admissible projected jump orbit has policy
limit strictly above it. -/
structure SaddleBracketingTransit
    (p : LoopParams) (threshold : PaperII.ThresholdAssumption p)
    (β₀ : ℝ) : Prop where
  policy_mem : β₀ ∈ Ico (0 : ℝ) threshold.βdagger
  exists_above : ∃ E₀ : ℝ,
    0 < E₀ ∧ 2 * p.c ^ 2 * E₀ < 1 ∧
      threshold.βdagger < projectedJumpPolicyLimit p β₀ E₀

/-- A saddle-bracketing transit places the critical jump excess inside the
admissible interval and gives strict policy separation on both sides.  This is
the precise fragment of `prop:burn`(ii) needed by `prop:seplimit`; it does not
assume continuity of the policy-limit function. -/
theorem jumpSeparatrixScale_twoSided {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (threshold : PaperII.ThresholdAssumption p) {β₀ : ℝ}
    (transit : SaddleBracketingTransit p threshold β₀) :
    let κ := jumpSeparatrixScale p threshold.βdagger β₀
    0 ≤ κ ∧ 2 * p.c ^ 2 * κ < 1 ∧
      (∀ E₀, 0 ≤ E₀ → E₀ < κ →
        projectedJumpPolicyLimit p β₀ E₀ < threshold.βdagger) ∧
      (∀ E₀, κ < E₀ → 2 * p.c ^ 2 * E₀ < 1 →
        threshold.βdagger < projectedJumpPolicyLimit p β₀ E₀) := by
  let S : Set ℝ :=
    {E₀ | JumpOrbitUniformlyBelow p threshold.βdagger β₀ E₀}
  let κ : ℝ := sSup S
  have hβ₀ : β₀ ∈ Icc (0 : ℝ) 1 :=
    ⟨transit.policy_mem.1, transit.policy_mem.2.le.trans threshold.βdagger_mem.2.le⟩
  have hzeroLimit : projectedJumpPolicyLimit p β₀ 0 = β₀ :=
    projectedJumpPolicyLimit_zero hβ₀
  have hzero : (0 : ℝ) ∈ S := by
    change JumpOrbitUniformlyBelow p threshold.βdagger β₀ 0
    rw [jumpOrbitUniformlyBelow_iff]
    exact ⟨le_rfl, by norm_num,
      by simpa only [hzeroLimit] using transit.policy_mem.2⟩
  have hSnonempty : S.Nonempty := ⟨0, hzero⟩
  obtain ⟨Ehi, hEhiPos, hEhiCap, hEhiAbove⟩ := transit.exists_above
  have hEhiLimit := projJumpOrbit_policy_tendsto_limit
    model hgain hβ₀ hEhiPos.le
  have hSupper : ∀ E ∈ S, E ≤ Ehi := by
    intro E hES
    change JumpOrbitUniformlyBelow p threshold.βdagger β₀ E at hES
    rw [jumpOrbitUniformlyBelow_iff] at hES
    rcases hES with ⟨hEnonneg, hEcap, hEbelow⟩
    by_contra hnot
    have hle : Ehi ≤ E := le_of_not_ge hnot
    have hELimit := projJumpOrbit_policy_tendsto_limit model hgain hβ₀ hEnonneg
    have hmono := projJumpOrbit_policy_limit_mono model hgain hβ₀ hEhiPos.le
      hEhiCap.le hle hEhiLimit hELimit
    linarith
  have hSbdd : BddAbove S := ⟨Ehi, hSupper⟩
  have hκNonneg : 0 ≤ κ := le_csSup hSbdd hzero
  have hκLe : κ ≤ Ehi := csSup_le hSnonempty hSupper
  have hcoefficient : 0 ≤ 2 * p.c ^ 2 := by positivity
  have hκCap : 2 * p.c ^ 2 * κ < 1 :=
    (mul_le_mul_of_nonneg_left hκLe hcoefficient).trans_lt hEhiCap
  have hbelow : ∀ E₀, 0 ≤ E₀ → E₀ < κ →
      projectedJumpPolicyLimit p β₀ E₀ < threshold.βdagger := by
    intro E₀ hE₀ hE₀κ
    obtain ⟨E, hES, hE₀E⟩ := exists_lt_of_lt_csSup hSnonempty hE₀κ
    change JumpOrbitUniformlyBelow p threshold.βdagger β₀ E at hES
    rw [jumpOrbitUniformlyBelow_iff] at hES
    rcases hES with ⟨hEnonneg, hEcap, hElimitBelow⟩
    have hE₀Cap : 2 * p.c ^ 2 * E₀ ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hE₀E.le hcoefficient
      linarith
    have hlimitE₀ := projJumpOrbit_policy_tendsto_limit model hgain hβ₀ hE₀
    have hlimitE := projJumpOrbit_policy_tendsto_limit model hgain hβ₀ hEnonneg
    have hmono := projJumpOrbit_policy_limit_mono model hgain hβ₀ hE₀
      hE₀Cap hE₀E.le hlimitE₀ hlimitE
    exact hmono.trans_lt hElimitBelow
  have habove : ∀ E₀, κ < E₀ → 2 * p.c ^ 2 * E₀ < 1 →
      threshold.βdagger < projectedJumpPolicyLimit p β₀ E₀ := by
    intro E₀ hκE₀ hE₀Cap
    have hE₀Pos : 0 < E₀ := hκNonneg.trans_lt hκE₀
    let L := projectedJumpPolicyLimit p β₀ E₀
    have hlimitE₀ : Tendsto (fun n ↦ (projJumpOrbit p (β₀, E₀) n).1)
        atTop (nhds L) := projJumpOrbit_policy_tendsto_limit
          model hgain hβ₀ hE₀Pos.le
    have hnotBelow : ¬ L < threshold.βdagger := by
      intro hLbelow
      have hmem : E₀ ∈ S := by
        change JumpOrbitUniformlyBelow p threshold.βdagger β₀ E₀
        rw [jumpOrbitUniformlyBelow_iff]
        exact ⟨hE₀Pos.le, hE₀Cap, hLbelow⟩
      exact (not_le_of_gt hκE₀) (le_csSup hSbdd hmem)
    have hsaddleLe : threshold.βdagger ≤ L := le_of_not_gt hnotBelow
    by_contra hnotAbove
    have hLe : L ≤ threshold.βdagger := le_of_not_gt hnotAbove
    have hLeq : L = threshold.βdagger := le_antisymm hLe hsaddleLe
    have hzeroTendsto : Tendsto
        (fun n ↦ (projJumpOrbit p (β₀, 0) n).1) atTop (nhds β₀) := by
      simpa only [projectedJumpPolicyLimit_zero hβ₀] using
        (projJumpOrbit_policy_tendsto_limit model hgain hβ₀ (le_refl 0))
    have hEunclipped : ProjOrbitUnclipped p (β₀, E₀) := by
      by_contra hclips
      have htri := burnPolicyLimit_trichotomy model hgain hβ₀ (le_refl 0)
        hE₀Pos hE₀Cap hzeroTendsto hlimitE₀
      have hLone : L = 1 := htri.2.2 hclips
      linarith [threshold.βdagger_mem.2]
    let Emid : ℝ := (κ + E₀) / 2
    have hκMid : κ < Emid := by dsimp only [Emid]; linarith
    have hmidE₀ : Emid < E₀ := by dsimp only [Emid]; linarith
    have hmidNonneg : 0 ≤ Emid := hκNonneg.trans hκMid.le
    have hmidCap : 2 * p.c ^ 2 * Emid < 1 := by
      exact (mul_lt_mul_of_pos_left hmidE₀
        (mul_pos two_pos (sq_pos_of_pos model.c_pos))).trans hE₀Cap
    let Lmid := projectedJumpPolicyLimit p β₀ Emid
    have hlimitMid : Tendsto (fun n ↦ (projJumpOrbit p (β₀, Emid) n).1)
        atTop (nhds Lmid) := projJumpOrbit_policy_tendsto_limit
          model hgain hβ₀ hmidNonneg
    have hmidNotBelow : ¬ Lmid < threshold.βdagger := by
      intro hmidBelow
      have hmem : Emid ∈ S := by
        change JumpOrbitUniformlyBelow p threshold.βdagger β₀ Emid
        rw [jumpOrbitUniformlyBelow_iff]
        exact ⟨hmidNonneg, hmidCap, hmidBelow⟩
      exact (not_le_of_gt hκMid) (le_csSup hSbdd hmem)
    have hsaddleLeMid : threshold.βdagger ≤ Lmid := le_of_not_gt hmidNotBelow
    have htri := burnPolicyLimit_trichotomy model hgain hβ₀ hmidNonneg
      hmidE₀ hE₀Cap hlimitMid hlimitE₀
    have hstrict : Lmid < L := (htri.2.1 hEunclipped).2
    rw [hLeq] at hstrict
    exact (not_lt_of_ge hsaddleLeMid) hstrict
  simpa only [jumpSeparatrixScale, S, κ] using
    ⟨hκNonneg, hκCap, hbelow, habove⟩

/-! ## Varying only the adaptation rate -/

/-- The primitive model assumptions are preserved when only the adaptation
rate is replaced by a positive value. -/
theorem LoopModelAssumptions.forAdaptationRate {p : LoopParams}
    (model : LoopModelAssumptions p) {α : ℝ} (hα : 0 < α) :
    LoopModelAssumptions (withAdaptationRate p α) where
  η_pos := by simpa [withAdaptationRate] using model.η_pos
  η_lt_one := by simpa [withAdaptationRate] using model.η_lt_one
  lambda₀_pos := by simpa [withAdaptationRate] using model.lambda₀_pos
  lambda₀_lt_one := by simpa [withAdaptationRate] using model.lambda₀_lt_one
  I_pos := by simpa [withAdaptationRate] using model.I_pos
  v_pos := by simpa [withAdaptationRate] using model.v_pos
  c_pos := by simpa [withAdaptationRate] using model.c_pos
  c_lt_one := by simpa [withAdaptationRate] using model.c_lt_one
  α_pos := by simpa [withAdaptationRate] using hα
  g_nonneg := by simpa [withAdaptationRate] using model.g_nonneg

/-- Auxiliary to Paper III, Proposition 7.6 (`prop:seplimit`): the stationary
gradient is independent of the adaptation rate. -/
@[simp]
theorem withAdaptationRate_G (p : LoopParams) (α β : ℝ) :
    (withAdaptationRate p α).G β = p.G β := rfl

/-- Auxiliary to Paper III, Proposition 7.6 (`prop:seplimit`): the stationary
gradient slope is independent of the adaptation rate. -/
@[simp]
theorem withAdaptationRate_GSlope (p : LoopParams) (α β : ℝ) :
    (withAdaptationRate p α).GSlope β = p.GSlope β := rfl

/-- Auxiliary to Paper III, Proposition 7.6 (`prop:seplimit`): transport the
paper's threshold bundle while varying only the adaptation rate. -/
def thresholdForAdaptationRate {p : LoopParams}
    (threshold : PaperII.ThresholdAssumption p) (α : ℝ) :
    PaperII.ThresholdAssumption (withAdaptationRate p α) where
  βdagger := threshold.βdagger
  βdagger_mem := threshold.βdagger_mem
  G_zero := by simpa only [withAdaptationRate_G] using threshold.G_zero
  G_zero_neg := by simpa only [withAdaptationRate_G] using threshold.G_zero_neg
  G_one_pos := by simpa only [withAdaptationRate_G] using threshold.G_one_pos
  G_neg_before := by simpa only [withAdaptationRate_G] using threshold.G_neg_before
  G_pos_after := by simpa only [withAdaptationRate_G] using threshold.G_pos_after
  GSlope_pos := by simpa only [withAdaptationRate_GSlope] using threshold.GSlope_pos

/-- Auxiliary to Paper III, Proposition 7.6 (`prop:seplimit`): transporting the
threshold bundle leaves its saddle coordinate unchanged. -/
@[simp]
theorem thresholdForAdaptationRate_beta {p : LoopParams}
    (threshold : PaperII.ThresholdAssumption p) (α : ℝ) :
    (thresholdForAdaptationRate threshold α).βdagger = threshold.βdagger := rfl

/-- Auxiliary to Paper III, Proposition 7.6 (`prop:seplimit`): stationary stock
is independent of the adaptation rate. -/
@[simp]
theorem withAdaptationRate_stationaryStock (p : LoopParams) (α β : ℝ) :
    (withAdaptationRate p α).stationaryStock β = p.stationaryStock β := rfl

/-- Auxiliary to Paper III, Proposition 7.6 (`prop:seplimit`): the sub-saddle
excess allowance is independent of the adaptation rate. -/
@[simp]
theorem withAdaptationRate_subSaddleExcessAllowance
    (p : LoopParams) (α ρ : ℝ) :
    subSaddleExcessAllowance (withAdaptationRate p α) ρ =
      subSaddleExcessAllowance p ρ := rfl

/-- Auxiliary to Paper III, Proposition 7.6 (`prop:seplimit`): transporting the
threshold bundle preserves the sub-saddle rate ceiling. -/
@[simp]
theorem withAdaptationRate_subSaddleAlphaCeiling {p : LoopParams}
    (threshold : PaperII.ThresholdAssumption p) (α ρ : ℝ) :
    subSaddleAlphaCeiling (thresholdForAdaptationRate threshold α) ρ =
      subSaddleAlphaCeiling threshold ρ := rfl

/-- A sufficiently small positive replacement rate satisfies strict `(SS_g)`. -/
theorem strictStepSize_forAdaptationRate {p : LoopParams} {α : ℝ}
    (hsmall : 2 * α * p.c ^ 2 * p.I < p.lambda₀ - p.g) :
    StrictStepSize (withAdaptationRate p α) := by
  constructor
  simpa only [withAdaptationRate] using hsmall

/-! ## Auxiliary projected-orbit estimates -/

/-- Positive projected excess remains strictly positive at every finite time. -/
theorem projJumpOrbit_excess_pos {p : LoopParams}
    (model : LoopModelAssumptions p) {x₀ : LoopState}
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (hE₀ : 0 < x₀.2) (n : ℕ) :
    0 < (projJumpOrbit p x₀ n).2 := by
  induction n with
  | zero => simpa only [projJumpOrbit_zero] using hE₀
  | succ n ih =>
      rw [projJumpOrbit_succ]
      exact mul_pos
        (jumpPersistence_pos_of_mem model (projJumpOrbit_policy_mem hx₀ n)) ih

/-- Projected excess converges geometrically to zero. -/
theorem projJumpOrbit_excess_tendsto_zero {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    {x₀ : LoopState} (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1)
    (hE₀ : 0 ≤ x₀.2) :
    Tendsto (fun n ↦ (projJumpOrbit p x₀ n).2) atTop (nhds 0) := by
  let q : ℝ := 1 - p.lambda₀ + p.g
  have hqNonneg : 0 ≤ q := by
    dsimp only [q]
    linarith [model.lambda₀_lt_one, model.g_nonneg]
  have hqLt : q < 1 := by dsimp only [q]; linarith
  have hupper : Tendsto (fun n : ℕ ↦ x₀.2 * q ^ n) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hqNonneg hqLt).const_mul x₀.2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n ↦ projJumpOrbit_excess_nonneg model hgain hx₀ hE₀ n)
    (fun n ↦ by simpa only [q] using
      projJumpOrbit_excess_le_geometric model hgain hx₀ hE₀ n)

/-- Every finite projected policy coordinate is at most its canonical limit. -/
theorem projJumpOrbit_policy_le_limit {p : LoopParams} {β₀ E₀ : ℝ}
    (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    (projJumpOrbit p (β₀, E₀) n).1 ≤
      projectedJumpPolicyLimit p β₀ E₀ := by
  apply le_csSup
  · exact ⟨1, by rintro y ⟨k, rfl⟩; exact (projJumpOrbit_policy_mem hβ₀ k).2⟩
  · exact ⟨n, rfl⟩

/-! ## Transferring finite projected transits to the full loop -/

/-- If the projected policy limit lies above the saddle, then at every
sufficiently small positive adaptation rate the corresponding full-loop state
is captured. -/
theorem eventually_fullLoop_capture_of_projectedLimit_above
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀)
    (threshold : PaperII.ThresholdAssumption p) {β₀ E₀ : ℝ}
    (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1) (hE₀ : 0 < E₀)
    (habove : threshold.βdagger < projectedJumpPolicyLimit p β₀ E₀) :
    ∀ᶠ α : ℝ in nhdsWithin 0 (Ioi 0),
      Tendsto
        (fullLoopOrbit (withAdaptationRate p α)
          (β₀, p.stationaryStock β₀ + E₀ / α)) atTop
        (nhds (1, p.stationaryStock 1)) := by
  have hpolicyLimit := projJumpOrbit_policy_tendsto_limit
    model hgain hβ₀ hE₀.le
  have heventuallyAbove := hpolicyLimit.eventually (Ioi_mem_nhds habove)
  obtain ⟨n, hn⟩ := (eventually_atTop.1 heventuallyAbove)
  have hβn : threshold.βdagger < (projJumpOrbit p (β₀, E₀) n).1 :=
    hn n le_rfl
  have hEn : 0 < (projJumpOrbit p (β₀, E₀) n).2 :=
    projJumpOrbit_excess_pos model hβ₀ hE₀ n
  have hrescaled := rescaledFullLoopOrbit_tendsto_projectedJumpOrbit
    model hgain (x := (β₀, E₀)) hβ₀ n
  have hpolicyRescaled : Tendsto
      (fun α : ℝ ↦ (rescaledFullLoopOrbit p α (β₀, E₀) n).1)
      (nhdsWithin 0 (Ioi 0))
      (nhds (projJumpOrbit p (β₀, E₀) n).1) :=
    (continuous_fst.tendsto _).comp hrescaled
  have hexcessRescaled : Tendsto
      (fun α : ℝ ↦ (rescaledFullLoopOrbit p α (β₀, E₀) n).2)
      (nhdsWithin 0 (Ioi 0))
      (nhds (projJumpOrbit p (β₀, E₀) n).2) :=
    (continuous_snd.tendsto _).comp hrescaled
  have heventuallyPolicy := hpolicyRescaled.eventually (Ioi_mem_nhds hβn)
  have heventuallyExcess := hexcessRescaled.eventually (Ioi_mem_nhds hEn)
  have hscaledStep : Tendsto (fun α : ℝ ↦ 2 * α * p.c ^ 2 * p.I)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hcontinuous : Continuous (fun α : ℝ ↦ 2 * α * p.c ^ 2 * p.I) := by
      fun_prop
    have hat : ContinuousAt (fun α : ℝ ↦ 2 * α * p.c ^ 2 * p.I) 0 :=
      hcontinuous.continuousAt
    have hfull : Tendsto (fun α : ℝ ↦ 2 * α * p.c ^ 2 * p.I)
        (nhds 0) (nhds 0) := by
      simpa only [ContinuousAt, mul_zero, zero_mul] using hat
    exact hfull.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have heventuallyStep := hscaledStep.eventually
    (Iio_mem_nhds (sub_pos.mpr hgain))
  filter_upwards [self_mem_nhdsWithin, heventuallyPolicy,
    heventuallyExcess, heventuallyStep] with α hα hβabove hEpositive hstep
  let q := withAdaptationRate p α
  let x₀ : LoopState := (β₀, p.stationaryStock β₀ + E₀ / α)
  let y : LoopState := fullLoopOrbit q x₀ n
  have modelq : LoopModelAssumptions q := by
    exact model.forAdaptationRate hα
  have hgainq : q.g < q.lambda₀ := by
    simpa only [q, withAdaptationRate] using hgain
  have ssq : StrictStepSize q := by
    exact strictStepSize_forAdaptationRate hstep
  let thresholdq : PaperII.ThresholdAssumption q :=
    thresholdForAdaptationRate threshold α
  have hβy : threshold.βdagger < y.1 := by
    simpa only [rescaledFullLoopOrbit, rescaleStockExcess, fullLoopOrbit,
      unscaleStockExcess, q, x₀, y] using hβabove
  have hscaledPositive : 0 < α * (y.2 - p.stationaryStock y.1) := by
    simpa only [rescaledFullLoopOrbit, rescaleStockExcess, fullLoopOrbit,
      unscaleStockExcess, q, x₀, y] using hEpositive
  have hcharacteristic : q.stationaryStock y.1 ≤ y.2 := by
    have hαpos : 0 < α := hα
    have hdiff : 0 < y.2 - p.stationaryStock y.1 := by
      rcases (mul_pos_iff.mp hscaledPositive) with hpos | hneg
      · exact hpos.2
      · exact (hneg.1.not_gt hαpos).elim
    have hp : p.stationaryStock y.1 < y.2 := sub_pos.mp hdiff
    simpa only [q, withAdaptationRate_stationaryStock] using hp.le
  have hβymem : y.1 ∈ Icc (0 : ℝ) 1 := by
    exact policy_mem_unit (fullLoopOrbit_isOrbit q x₀)
      (by simpa only [x₀, fullLoopOrbit_zero] using hβ₀) n
  have htail : Tendsto (fullLoopOrbit q y) atTop
      (nhds (1, q.stationaryStock 1)) := by
    apply characteristicCapture modelq hgainq ssq thresholdq
    · constructor
      · change threshold.βdagger < y.1
        exact hβy
      · exact hβymem.2
    · exact hcharacteristic
  have horbit : Tendsto (fullLoopOrbit q x₀) atTop
      (nhds (1, q.stationaryStock 1)) := by
    apply (fullLoopOrbit_tendsto_iff_tail q x₀ (1, q.stationaryStock 1) n).1
    simpa only [y] using htail
  simpa only [q, x₀, withAdaptationRate_stationaryStock] using horbit

/-- If the projected policy limit lies below the saddle, then at every
sufficiently small positive adaptation rate the corresponding full-loop state
calibrates. -/
theorem eventually_fullLoop_calibrate_of_projectedLimit_below
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀)
    (threshold : PaperII.ThresholdAssumption p) {β₀ E₀ : ℝ}
    (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1) (hE₀ : 0 < E₀)
    (hbelow : projectedJumpPolicyLimit p β₀ E₀ < threshold.βdagger) :
    ∀ᶠ α : ℝ in nhdsWithin 0 (Ioi 0),
      Tendsto
        (fullLoopOrbit (withAdaptationRate p α)
          (β₀, p.stationaryStock β₀ + E₀ / α)) atTop
        (nhds (0, p.stationaryStock 0)) := by
  let L := projectedJumpPolicyLimit p β₀ E₀
  let ρ := (threshold.βdagger - L) / 2
  have hβ₀leL : β₀ ≤ L := by
    have hle := projJumpOrbit_policy_le_limit (p := p) (E₀ := E₀) hβ₀ 0
    simpa only [projJumpOrbit_zero, L] using hle
  have hLnonneg : 0 ≤ L := hβ₀.1.trans hβ₀leL
  have hρpos : 0 < ρ := by
    dsimp only [ρ, L]
    linarith
  have hρlt : ρ < threshold.βdagger := by
    dsimp only [ρ]
    linarith [threshold.βdagger_mem.1, hLnonneg]
  have hρ : ρ ∈ Ioo (0 : ℝ) threshold.βdagger := ⟨hρpos, hρlt⟩
  have hallowPos : 0 < subSaddleExcessAllowance p ρ :=
    subSaddleExcessAllowance_pos model hgain hρpos
  have hexcessLimit := projJumpOrbit_excess_tendsto_zero
    model hgain (x₀ := (β₀, E₀)) hβ₀ hE₀.le
  have heventuallySmall := hexcessLimit.eventually
    (Iio_mem_nhds (half_pos hallowPos))
  obtain ⟨n, hn⟩ := eventually_atTop.1 heventuallySmall
  have hEnSmall : (projJumpOrbit p (β₀, E₀) n).2 <
      subSaddleExcessAllowance p ρ / 2 := hn n le_rfl
  have hβnLe : (projJumpOrbit p (β₀, E₀) n).1 ≤ L :=
    projJumpOrbit_policy_le_limit hβ₀ n
  have hβnMargin : (projJumpOrbit p (β₀, E₀) n).1 <
      threshold.βdagger - ρ := by
    dsimp only [ρ]
    linarith
  have hEnAllowance : (projJumpOrbit p (β₀, E₀) n).2 <
      subSaddleExcessAllowance p ρ := by
    linarith
  have hrescaled := rescaledFullLoopOrbit_tendsto_projectedJumpOrbit
    model hgain (x := (β₀, E₀)) hβ₀ n
  have hpolicyRescaled : Tendsto
      (fun α : ℝ ↦ (rescaledFullLoopOrbit p α (β₀, E₀) n).1)
      (nhdsWithin 0 (Ioi 0))
      (nhds (projJumpOrbit p (β₀, E₀) n).1) :=
    (continuous_fst.tendsto _).comp hrescaled
  have hexcessRescaled : Tendsto
      (fun α : ℝ ↦ (rescaledFullLoopOrbit p α (β₀, E₀) n).2)
      (nhdsWithin 0 (Ioi 0))
      (nhds (projJumpOrbit p (β₀, E₀) n).2) :=
    (continuous_snd.tendsto _).comp hrescaled
  have heventuallyPolicy := hpolicyRescaled.eventually
    (Iio_mem_nhds hβnMargin)
  have heventuallyExcess := hexcessRescaled.eventually
    (Iio_mem_nhds hEnAllowance)
  have hceilingPos := subSaddleAlphaCeiling_pos model hgain threshold hρ
  have hid : Tendsto (fun α : ℝ ↦ α) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have heventuallyCeiling := hid.eventually (Iio_mem_nhds hceilingPos)
  filter_upwards [self_mem_nhdsWithin, heventuallyPolicy,
    heventuallyExcess, heventuallyCeiling] with α hα hβbelow hEsmall hαsmall
  let q := withAdaptationRate p α
  let x₀ : LoopState := (β₀, p.stationaryStock β₀ + E₀ / α)
  let y : LoopState := fullLoopOrbit q x₀ n
  have modelq : LoopModelAssumptions q := model.forAdaptationRate hα
  have hgainq : q.g < q.lambda₀ := by
    simpa only [q, withAdaptationRate] using hgain
  let thresholdq : PaperII.ThresholdAssumption q :=
    thresholdForAdaptationRate threshold α
  have hβybelow : y.1 < threshold.βdagger - ρ := by
    simpa only [rescaledFullLoopOrbit, rescaleStockExcess, fullLoopOrbit,
      unscaleStockExcess, q, x₀, y] using hβbelow
  have hscaledY : α * (y.2 - p.stationaryStock y.1) <
      subSaddleExcessAllowance p ρ := by
    simpa only [rescaledFullLoopOrbit, rescaleStockExcess, fullLoopOrbit,
      unscaleStockExcess, q, x₀, y] using hEsmall
  have hβymem : y.1 ∈ Icc (0 : ℝ) 1 := by
    exact policy_mem_unit (fullLoopOrbit_isOrbit q x₀)
      (by simpa only [x₀, fullLoopOrbit_zero] using hβ₀) n
  have hD₀pos : 0 < x₀.2 := by
    have hstationary : 0 < p.stationaryStock β₀ :=
      div_pos model.I_pos (zoneDenominator_pos model hgain hβ₀)
    have hscaledInitial : 0 < E₀ / α := div_pos hE₀ hα
    simpa only [x₀] using add_pos hstationary hscaledInitial
  have hDy : 0 ≤ y.2 := by
    exact stock_nonneg modelq (fullLoopOrbit_isOrbit q x₀)
      (by simpa only [x₀, fullLoopOrbit_zero] using hβ₀)
      (by simpa only [x₀, fullLoopOrbit_zero] using hD₀pos.le) n
  have htail : Tendsto (fullLoopOrbit q y) atTop
      (nhds (0, q.stationaryStock 0)) := by
    apply subSaddleTrap modelq hgainq thresholdq
    · change ρ ∈ Ioo (0 : ℝ) threshold.βdagger
      exact hρ
    · change α ≤ subSaddleAlphaCeiling threshold ρ
      exact hαsmall.le
    · exact hβymem
    · change y.1 ≤ threshold.βdagger - ρ
      exact hβybelow.le
    · exact hDy
    · change α * (y.2 - p.stationaryStock y.1) ≤
        subSaddleExcessAllowance p ρ
      exact hscaledY.le
  have horbit : Tendsto (fullLoopOrbit q x₀) atTop
      (nhds (0, q.stationaryStock 0)) := by
    apply (fullLoopOrbit_tendsto_iff_tail q x₀ (0, q.stationaryStock 0) n).1
    simpa only [y] using htail
  simpa only [q, x₀, withAdaptationRate_stationaryStock] using horbit

/-! ## Captured-stock up-sets and their infimum -/

/-- At a fixed policy in the unit interval, one full-loop step is monotone in
the initial stock. -/
theorem loopMap_mono_same_policy {p : LoopParams}
    (model : LoopModelAssumptions p) {β D₁ D₂ : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) (hD : D₁ ≤ D₂) :
    p.loopMap (β, D₁) ≤ p.loopMap (β, D₂) := by
  have hA := (jumpGain_nonneg_le model hβ).1
  have hmul : jumpGain p β * D₁ ≤ jumpGain p β * D₂ :=
    mul_le_mul_of_nonneg_left hD hA
  have hgrad : p.gradU β D₁ ≤ p.gradU β D₂ := by
    simp only [LoopParams.gradU, jumpGain] at hmul ⊢
    linarith
  have hinput : β + p.α * p.gradU β D₁ ≤
      β + p.α * p.gradU β D₂ := by
    have := mul_le_mul_of_nonneg_left hgrad model.α_pos.le
    linarith
  have hpolicy : p.deferenceStep β D₁ ≤ p.deferenceStep β D₂ := by
    simp only [LoopParams.deferenceStep]
    exact LoopParams.monotone_clipUnit hinput
  have hmult : 0 ≤ p.s β + p.g :=
    add_nonneg (stockMultiplier_nonneg_le model hβ).1 model.g_nonneg
  have hstock : p.stockStep β D₁ ≤ p.stockStep β D₂ := by
    simp only [LoopParams.stockStep]
    simpa only [add_comm] using
      add_le_add_right (mul_le_mul_of_nonneg_left hD hmult) p.I
  exact ⟨hpolicy, hstock⟩

/-- Within the cooperative ceiling, increasing the initial stock at a fixed
policy increases every subsequent full-loop state.  A smaller nonnegative
stock may start below the box's lower face; after one step both compared
orbits are in the invariant ceiling box. -/
theorem fullLoopOrbit_mono_initialStock {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (ss : StrictStepSize p) {β D₁ D₂ : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) (hD₁ : 0 ≤ D₁) (hD : D₁ ≤ D₂)
    (hupper : (β, D₂) ∈ ceilingBox p) :
    ∀ n, fullLoopOrbit p (β, D₁) n ≤ fullLoopOrbit p (β, D₂) n := by
  let x₁ : LoopState := (β, D₁)
  let x₂ : LoopState := (β, D₂)
  let z₁ : LoopState := p.loopMap x₁
  let z₂ : LoopState := p.loopMap x₂
  have hfirst : z₁ ≤ z₂ := by
    simpa only [x₁, x₂, z₁, z₂] using loopMap_mono_same_policy model hβ hD
  have hinvariant := ceilingBox_invariant model hgain ss
  have hz₂mem : z₂ ∈ ceilingBox p := by
    exact hinvariant hupper
  have hz₁mem : z₁ ∈ ceilingBox p := by
    have hmult : 0 ≤ p.s β + p.g :=
      add_nonneg (stockMultiplier_nonneg_le model hβ).1 model.g_nonneg
    have hstockLower : p.I ≤ z₁.2 := by
      simp only [z₁, x₁, LoopParams.loopMap, LoopParams.stockStep]
      exact le_add_of_nonneg_left (mul_nonneg hmult hD₁)
    exact ⟨LoopParams.clipUnit_mem _, hstockLower,
      hfirst.2.trans hz₂mem.2.2⟩
  have hdenpos : 0 < 2 * p.α * p.c ^ 2 := twoAlphaCSq_pos model
  have hproduct : 2 * p.α * p.c ^ 2 * monotonicityCeiling p = 1 := by
    rw [monotonicityCeiling]
    simpa only [one_div] using mul_inv_cancel₀ hdenpos.ne'
  have hdiag : 0 ≤ policyDiagonalLowerAt p (monotonicityCeiling p) := by
    rw [policyDiagonalLowerAt, hproduct]
    norm_num
  have hmono : MonotoneOn p.loopMap (ceilingBox p) :=
    classificationLoopMap_monotoneOn model hgain hdiag
  have hz₁all : ∀ k, fullLoopOrbit p z₁ k ∈ ceilingBox p := by
    intro k
    induction k with
    | zero => simpa only [fullLoopOrbit_zero] using hz₁mem
    | succ k ih =>
        rw [fullLoopOrbit_succ]
        exact hinvariant ih
  have hz₂all : ∀ k, fullLoopOrbit p z₂ k ∈ ceilingBox p := by
    intro k
    induction k with
    | zero => simpa only [fullLoopOrbit_zero] using hz₂mem
    | succ k ih =>
        rw [fullLoopOrbit_succ]
        exact hinvariant ih
  have hshift : ∀ k, fullLoopOrbit p z₁ k ≤ fullLoopOrbit p z₂ k := by
    intro k
    induction k with
    | zero => simpa only [fullLoopOrbit_zero] using hfirst
    | succ k ih =>
        rw [fullLoopOrbit_succ, fullLoopOrbit_succ]
        exact hmono (hz₁all k) (hz₂all k) ih
  intro n
  cases n with
  | zero => simpa only [fullLoopOrbit_zero, Prod.le_def] using And.intro le_rfl hD
  | succ k =>
      simpa only [z₁, z₂, x₁, x₂, fullLoopOrbit,
        Function.iterate_succ_apply] using hshift k

/-- Nonnegative initial stocks whose full loop converges to the captured
corner. -/
def capturedInitialStockSet (p : LoopParams) (β₀ : ℝ) : Set ℝ :=
  {D | 0 ≤ D ∧ Tendsto (fullLoopOrbit p (β₀, D)) atTop
    (nhds (1, p.stationaryStock 1))}

/-- The stock separatrix `D_sep(α;β₀)`, defined as the infimum of captured
nonnegative initial stocks. -/
noncomputable def separatrixStock (p : LoopParams) (β₀ : ℝ) : ℝ :=
  sInf (capturedInitialStockSet p β₀)

/-- The captured-stock set is bounded below by zero. -/
theorem capturedInitialStockSet_bddBelow (p : LoopParams) (β₀ : ℝ) :
    BddBelow (capturedInitialStockSet p β₀) := by
  exact ⟨0, fun _ hD ↦ hD.1⟩

/-- Any exhibited captured stock bounds the separatrix from above. -/
theorem separatrixStock_le_of_captured {p : LoopParams} {β₀ D : ℝ}
    (hD : D ∈ capturedInitialStockSet p β₀) :
    separatrixStock p β₀ ≤ D := by
  exact csInf_le (capturedInitialStockSet_bddBelow p β₀) hD

/-- When some captured stock exists, the separatrix is nonnegative. -/
theorem separatrixStock_nonneg {p : LoopParams} {β₀ : ℝ}
    (hne : (capturedInitialStockSet p β₀).Nonempty) :
    0 ≤ separatrixStock p β₀ := by
  apply le_csInf hne
  intro D hD
  exact hD.1

/-- A calibrating stock inside the cooperative ceiling bounds the captured
up-set, hence bounds its infimum from below. -/
theorem calibratingStock_le_separatrixStock {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (ss : StrictStepSize p) {β₀ Dcal : ℝ}
    (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1)
    (hceiling : (β₀, Dcal) ∈ ceilingBox p)
    (hcal : Tendsto (fullLoopOrbit p (β₀, Dcal)) atTop
      (nhds (0, p.stationaryStock 0)))
    (hne : (capturedInitialStockSet p β₀).Nonempty) :
    Dcal ≤ separatrixStock p β₀ := by
  apply le_csInf hne
  intro D hDcaptured
  by_contra hnot
  have hDle : D ≤ Dcal := le_of_not_ge hnot
  have horder := fullLoopOrbit_mono_initialStock model hgain ss hβ₀
    hDcaptured.1 hDle hceiling
  have hcapturedPolicy : Tendsto
      (fun n ↦ (fullLoopOrbit p (β₀, D) n).1) atTop (nhds 1) :=
    (continuous_fst.tendsto _).comp hDcaptured.2
  have hcalPolicy : Tendsto
      (fun n ↦ (fullLoopOrbit p (β₀, Dcal) n).1) atTop (nhds 0) :=
    (continuous_fst.tendsto _).comp hcal
  have himpossible : (1 : ℝ) ≤ 0 :=
    le_of_tendsto_of_tendsto' hcapturedPolicy hcalPolicy
      (fun n ↦ (horder n).1)
  norm_num at himpossible

/-! ## The separatrix limit -/

/-- Paper III, Proposition 7.6 (`prop:seplimit`),
`civic_loops.tex:616`.

For fixed primitives and a saddle-bracketing projected transit, the captured
stock infimum has the critical inverse-rate scale.  The proof defines the
captured set directly, transfers strict projected transits at finite horizons,
and derives monotonicity of fate from cooperativity inside the explicit
ceiling; it does not import planar convergence. -/
theorem separatrixScaleLimit {p : LoopParams}
    (model : LoopModelAssumptions p) (hgain : p.g < p.lambda₀)
    (threshold : PaperII.ThresholdAssumption p) {β₀ : ℝ}
    (transit : SaddleBracketingTransit p threshold β₀) :
    Tendsto
      (fun α : ℝ ↦ α *
        (separatrixStock (withAdaptationRate p α) β₀ -
          p.stationaryStock β₀))
      (nhdsWithin 0 (Ioi 0))
      (nhds (jumpSeparatrixScale p threshold.βdagger β₀)) := by
  let κ := jumpSeparatrixScale p threshold.βdagger β₀
  change Tendsto
    (fun α : ℝ ↦ α *
      (separatrixStock (withAdaptationRate p α) β₀ -
        p.stationaryStock β₀))
    (nhdsWithin 0 (Ioi 0)) (nhds κ)
  have hβ₀ : β₀ ∈ Icc (0 : ℝ) 1 :=
    ⟨transit.policy_mem.1,
      transit.policy_mem.2.le.trans threshold.βdagger_mem.2.le⟩
  have htwo := jumpSeparatrixScale_twoSided model hgain threshold transit
  change 0 ≤ κ ∧ 2 * p.c ^ 2 * κ < 1 ∧
      (∀ E₀, 0 ≤ E₀ → E₀ < κ →
        projectedJumpPolicyLimit p β₀ E₀ < threshold.βdagger) ∧
      (∀ E₀, κ < E₀ → 2 * p.c ^ 2 * E₀ < 1 →
        threshold.βdagger < projectedJumpPolicyLimit p β₀ E₀) at htwo
  rcases htwo with ⟨hκnonneg, hκcap, hbelow, habove⟩
  obtain ⟨Ecap, hEcapPos, _hEcapAdmissible, hEcapAbove⟩ := transit.exists_above
  have hcaptureWitness :=
    eventually_fullLoop_capture_of_projectedLimit_above
      model hgain threshold hβ₀ hEcapPos hEcapAbove
  have hscaledStep : Tendsto (fun α : ℝ ↦ 2 * α * p.c ^ 2 * p.I)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hcontinuous : Continuous (fun α : ℝ ↦ 2 * α * p.c ^ 2 * p.I) := by
      fun_prop
    have hat : ContinuousAt (fun α : ℝ ↦ 2 * α * p.c ^ 2 * p.I) 0 :=
      hcontinuous.continuousAt
    have hfull : Tendsto (fun α : ℝ ↦ 2 * α * p.c ^ 2 * p.I)
        (nhds 0) (nhds 0) := by
      simpa only [ContinuousAt, mul_zero, zero_mul] using hat
    exact hfull.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have hstrictStep := hscaledStep.eventually
    (Iio_mem_nhds (sub_pos.mpr hgain))
  apply tendsto_order.2
  constructor
  · intro a ha
    by_cases hκzero : κ = 0
    · have hnegative : a < 0 := by simpa only [hκzero] using ha
      have hlinear : Tendsto
          (fun α : ℝ ↦ -α * p.stationaryStock β₀)
          (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
        have hcontinuous : Continuous
            (fun α : ℝ ↦ -α * p.stationaryStock β₀) := by fun_prop
        have hat : ContinuousAt
            (fun α : ℝ ↦ -α * p.stationaryStock β₀) 0 :=
          hcontinuous.continuousAt
        have hfull : Tendsto
            (fun α : ℝ ↦ -α * p.stationaryStock β₀)
            (nhds 0) (nhds 0) := by
          simpa only [ContinuousAt, neg_zero, zero_mul] using hat
        exact hfull.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      have heventuallyLower := hlinear.eventually (Ioi_mem_nhds hnegative)
      filter_upwards [self_mem_nhdsWithin, hcaptureWitness,
        heventuallyLower] with α hα hcaptured hlower
      let q := withAdaptationRate p α
      let Dcap := p.stationaryStock β₀ + Ecap / α
      have hDcapPos : 0 < Dcap := by
        have hstationary : 0 < p.stationaryStock β₀ :=
          div_pos model.I_pos (zoneDenominator_pos model hgain hβ₀)
        have hscaled : 0 < Ecap / α := div_pos hEcapPos hα
        exact add_pos hstationary hscaled
      have hDcapMem : Dcap ∈ capturedInitialStockSet q β₀ := by
        refine ⟨hDcapPos.le, ?_⟩
        simpa only [q, Dcap, withAdaptationRate_stationaryStock] using hcaptured
      have hne : (capturedInitialStockSet q β₀).Nonempty := ⟨Dcap, hDcapMem⟩
      have hsepNonneg : 0 ≤ separatrixStock q β₀ :=
        separatrixStock_nonneg hne
      have hαpos : 0 < α := hα
      have hscaledNonneg : 0 ≤ α * separatrixStock q β₀ :=
        mul_nonneg hαpos.le hsepNonneg
      change a < α *
        (separatrixStock q β₀ - p.stationaryStock β₀)
      nlinarith
    · have hκpos : 0 < κ := lt_of_le_of_ne hκnonneg (Ne.symm hκzero)
      let Eminus := (max a 0 + κ) / 2
      have hmaxLt : max a 0 < κ := max_lt ha hκpos
      have hEminusPos : 0 < Eminus := by
        dsimp only [Eminus]
        have hmaxNonneg : 0 ≤ max a 0 := le_max_right _ _
        linarith
      have haEminus : a < Eminus := by
        dsimp only [Eminus]
        have haMax : a ≤ max a 0 := le_max_left _ _
        linarith
      have hEminusκ : Eminus < κ := by
        dsimp only [Eminus]
        linarith
      have hlimitBelow := hbelow Eminus hEminusPos.le hEminusκ
      have hcalibrate :=
        eventually_fullLoop_calibrate_of_projectedLimit_below
          model hgain threshold hβ₀ hEminusPos hlimitBelow
      have hcoefficientPos : 0 < 2 * p.c ^ 2 :=
        mul_pos two_pos (sq_pos_of_pos model.c_pos)
      have hEminusCap : 2 * p.c ^ 2 * Eminus < 1 := by
        exact (mul_lt_mul_of_pos_left hEminusκ hcoefficientPos).trans hκcap
      have hceilingLimit : Tendsto
          (fun α : ℝ ↦ 2 * p.c ^ 2 *
            (Eminus + α * p.stationaryStock β₀))
          (nhdsWithin 0 (Ioi 0))
          (nhds (2 * p.c ^ 2 * Eminus)) := by
        have hcontinuous : Continuous
            (fun α : ℝ ↦ 2 * p.c ^ 2 *
              (Eminus + α * p.stationaryStock β₀)) := by fun_prop
        have hat : ContinuousAt
            (fun α : ℝ ↦ 2 * p.c ^ 2 *
              (Eminus + α * p.stationaryStock β₀)) 0 :=
          hcontinuous.continuousAt
        have hfull := hat
        simp only [ContinuousAt, zero_mul, add_zero] at hfull
        exact hfull.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      have hceilingEventually := hceilingLimit.eventually
        (Iio_mem_nhds hEminusCap)
      filter_upwards [self_mem_nhdsWithin, hcaptureWitness, hcalibrate,
        hstrictStep, hceilingEventually] with α hα hcaptured hcalibrated
          hstep hceilingScaled
      have hαpos : 0 < α := hα
      let q := withAdaptationRate p α
      let Dcap := p.stationaryStock β₀ + Ecap / α
      let Dminus := p.stationaryStock β₀ + Eminus / α
      have modelq : LoopModelAssumptions q := model.forAdaptationRate hα
      have hgainq : q.g < q.lambda₀ := by
        simpa only [q, withAdaptationRate] using hgain
      have ssq : StrictStepSize q := strictStepSize_forAdaptationRate hstep
      have hDcapPos : 0 < Dcap := by
        have hstationary : 0 < p.stationaryStock β₀ :=
          div_pos model.I_pos (zoneDenominator_pos model hgain hβ₀)
        exact add_pos hstationary (div_pos hEcapPos hαpos)
      have hDcapMem : Dcap ∈ capturedInitialStockSet q β₀ := by
        refine ⟨hDcapPos.le, ?_⟩
        simpa only [q, Dcap, withAdaptationRate_stationaryStock] using hcaptured
      have hne : (capturedInitialStockSet q β₀).Nonempty := ⟨Dcap, hDcapMem⟩
      have hDminusLower : p.I ≤ Dminus := by
        have hinjection := injection_le_stationaryStock model hgain hβ₀
        have hdivNonneg : 0 ≤ Eminus / α := (div_pos hEminusPos hαpos).le
        dsimp only [Dminus]
        linarith
      have hdenpos : 0 < 2 * α * p.c ^ 2 :=
        mul_pos (mul_pos two_pos hαpos) (sq_pos_of_pos model.c_pos)
      have hDminusUpper : Dminus ≤ monotonicityCeiling q := by
        have hstrict : Dminus < monotonicityCeiling q := by
          rw [monotonicityCeiling]
          change Dminus < 1 / (2 * α * p.c ^ 2)
          apply (lt_div_iff₀ hdenpos).2
          calc
            Dminus * (2 * α * p.c ^ 2) =
                2 * p.c ^ 2 *
                  (Eminus + α * p.stationaryStock β₀) := by
              dsimp only [Dminus]
              field_simp [hαpos.ne']
              ring
            _ < 1 := hceilingScaled
        exact hstrict.le
      have hDminusCeiling : (β₀, Dminus) ∈ ceilingBox q := by
        exact ⟨hβ₀, by simpa only [q, withAdaptationRate] using hDminusLower,
          hDminusUpper⟩
      have hcalibrated' : Tendsto (fullLoopOrbit q (β₀, Dminus)) atTop
          (nhds (0, q.stationaryStock 0)) := by
        simpa only [q, Dminus, withAdaptationRate_stationaryStock] using hcalibrated
      have hsepLower : Dminus ≤ separatrixStock q β₀ :=
        calibratingStock_le_separatrixStock modelq hgainq ssq hβ₀
          hDminusCeiling hcalibrated' hne
      have hscaledLower := mul_le_mul_of_nonneg_left
        (sub_le_sub_right hsepLower (p.stationaryStock β₀)) hαpos.le
      have hscaleIdentity :
          α * (Dminus - p.stationaryStock β₀) = Eminus := by
        dsimp only [Dminus]
        field_simp [hαpos.ne']
        ring
      change a < α *
        (separatrixStock q β₀ - p.stationaryStock β₀)
      calc
        a < Eminus := haEminus
        _ = α * (Dminus - p.stationaryStock β₀) := hscaleIdentity.symm
        _ ≤ α * (separatrixStock q β₀ - p.stationaryStock β₀) :=
          hscaledLower
  · intro b hb
    let A := 2 * p.c ^ 2
    have hApos : 0 < A := by
      dsimp only [A]
      exact mul_pos two_pos (sq_pos_of_pos model.c_pos)
    have hroom : 0 < 1 - A * κ := by
      dsimp only [A]
      linarith
    let δ := min ((b - κ) / 2) ((1 - A * κ) / (2 * A))
    have hδpos : 0 < δ := by
      dsimp only [δ]
      exact lt_min (half_pos (sub_pos.mpr hb))
        (div_pos hroom (mul_pos two_pos hApos))
    have hδb : δ ≤ (b - κ) / 2 := min_le_left _ _
    have hδroom : δ ≤ (1 - A * κ) / (2 * A) := min_le_right _ _
    let Eplus := κ + δ
    have hκEplus : κ < Eplus := by dsimp only [Eplus]; linarith
    have hEplusPos : 0 < Eplus := hκnonneg.trans_lt hκEplus
    have hEplusb : Eplus < b := by
      dsimp only [Eplus]
      linarith
    have hAδ : A * δ ≤ (1 - A * κ) / 2 := by
      calc
        A * δ ≤ A * ((1 - A * κ) / (2 * A)) :=
          mul_le_mul_of_nonneg_left hδroom hApos.le
        _ = (1 - A * κ) / 2 := by
          field_simp [hApos.ne']
    have hEplusCap : 2 * p.c ^ 2 * Eplus < 1 := by
      change A * Eplus < 1
      dsimp only [Eplus]
      nlinarith
    have hlimitAbove := habove Eplus hκEplus hEplusCap
    have hcapture := eventually_fullLoop_capture_of_projectedLimit_above
      model hgain threshold hβ₀ hEplusPos hlimitAbove
    filter_upwards [self_mem_nhdsWithin, hcapture] with α hα hcaptured
    have hαpos : 0 < α := hα
    let q := withAdaptationRate p α
    let Dplus := p.stationaryStock β₀ + Eplus / α
    have hDplusPos : 0 < Dplus := by
      have hstationary : 0 < p.stationaryStock β₀ :=
        div_pos model.I_pos (zoneDenominator_pos model hgain hβ₀)
      exact add_pos hstationary (div_pos hEplusPos hαpos)
    have hDplusMem : Dplus ∈ capturedInitialStockSet q β₀ := by
      refine ⟨hDplusPos.le, ?_⟩
      simpa only [q, Dplus, withAdaptationRate_stationaryStock] using hcaptured
    have hsepUpper : separatrixStock q β₀ ≤ Dplus :=
      separatrixStock_le_of_captured hDplusMem
    have hscaledUpper := mul_le_mul_of_nonneg_left
      (sub_le_sub_right hsepUpper (p.stationaryStock β₀)) hαpos.le
    have hscaleIdentity :
        α * (Dplus - p.stationaryStock β₀) = Eplus := by
      dsimp only [Dplus]
      field_simp [hαpos.ne']
      ring
    change α * (separatrixStock q β₀ - p.stationaryStock β₀) < b
    exact hscaledUpper.trans_lt (hscaleIdentity.trans_lt hEplusb)

#print axioms projJumpOrbit_policy_tendsto_limit
#print axioms projJumpOrbit_zero_excess
#print axioms projectedJumpPolicyLimit_zero
#print axioms jumpOrbitUniformlyBelow_iff
#print axioms jumpSeparatrixScale_twoSided
#print axioms LoopModelAssumptions.forAdaptationRate
#print axioms withAdaptationRate_G
#print axioms withAdaptationRate_GSlope
#print axioms thresholdForAdaptationRate_beta
#print axioms withAdaptationRate_stationaryStock
#print axioms withAdaptationRate_subSaddleExcessAllowance
#print axioms withAdaptationRate_subSaddleAlphaCeiling
#print axioms strictStepSize_forAdaptationRate
#print axioms projJumpOrbit_excess_pos
#print axioms projJumpOrbit_excess_tendsto_zero
#print axioms projJumpOrbit_policy_le_limit
#print axioms eventually_fullLoop_capture_of_projectedLimit_above
#print axioms eventually_fullLoop_calibrate_of_projectedLimit_below
#print axioms loopMap_mono_same_policy
#print axioms fullLoopOrbit_mono_initialStock
#print axioms capturedInitialStockSet_bddBelow
#print axioms separatrixStock_le_of_captured
#print axioms separatrixStock_nonneg
#print axioms calibratingStock_le_separatrixStock
#print axioms separatrixScaleLimit

end

end CivicAlignment.PaperIII
