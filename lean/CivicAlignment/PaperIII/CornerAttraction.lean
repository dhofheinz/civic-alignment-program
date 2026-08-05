/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.JumpLimit
import CivicAlignment.PaperIII.SaddleSpectrum

/-!
# Paper III: corners with strict gradient sign attract

`thm:classify`'s last clause says that a corner with strict stationary-gradient
sign is locally asymptotically stable.  Paper II's analogue is proved through
weighted-map machinery that does not carry the content gain `g`, so this file
gives the direct argument.

The captured corner is the informative case.  On the trapping set

  `{β₀ ≤ β ≤ 1} × {D*_g(β₀) ≤ D ≤ D*_g(1)}`

the stock lower bound is invariant, because the stock map is increasing in both
arguments and fixes `D*_g`; the gradient is therefore bounded below by
`-v + 2c(1-c) D*_g(β₀)`, which is positive once `β₀` is close enough to one; the
policy climbs by a fixed amount per step until it clips at one; and the stock
then follows a contracting affine recursion to `D*_g(1)`.  The calibrated corner
is the mirror image.
-/

namespace CivicAlignment.PaperIII

open Filter Set Topology

noncomputable section

variable {p : LoopParams}

/-! ## The captured corner -/

/-- Trapping set for the captured corner. -/
def capturedTrap (p : LoopParams) (β₀ : ℝ) : Set LoopState :=
  Icc β₀ 1 ×ˢ Icc (p.stationaryStock β₀) (p.stationaryStock 1)

/-- The uniform gradient floor available on the captured trapping set. -/
def capturedDrive (p : LoopParams) (β₀ : ℝ) : ℝ :=
  -p.v + 2 * p.c * (1 - p.c) * p.stationaryStock β₀

/-- On the trapping set the gradient is at least the floor. -/
theorem capturedTrap_gradU_ge (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β₀ : ℝ} (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1)
    {x : LoopState} (hx : x ∈ capturedTrap p β₀) :
    capturedDrive p β₀ ≤ p.gradU x.1 x.2 := by
  obtain ⟨⟨hβl, hβu⟩, hDl, _⟩ := hx
  have hcβ : 1 - p.c ≤ 1 - p.c * x.1 := by nlinarith [model.c_pos, hβu]
  have hDpos : 0 < p.stationaryStock β₀ :=
    div_pos model.I_pos (zoneDenominator_pos model hgain hβ₀)
  have h1 : (0 : ℝ) ≤ 1 - p.c * x.1 := by linarith [model.c_lt_one]
  simp only [LoopParams.gradU, capturedDrive]
  nlinarith [hcβ, hDl, model.c_pos, model.c_lt_one, hDpos, h1,
    mul_nonneg (mul_nonneg (by linarith [model.c_pos] : (0:ℝ) ≤ 2 * p.c) h1)
      (sub_nonneg.mpr hDl),
    mul_nonneg (by linarith [model.c_pos] : (0:ℝ) ≤ 2 * p.c)
      (mul_nonneg (sub_nonneg.mpr hcβ) hDpos.le)]

/-- The trapping set is forward invariant once the gradient floor is positive. -/
theorem capturedTrap_invariant (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β₀ : ℝ} (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1)
    (hdrive : 0 < capturedDrive p β₀) :
    MapsTo p.loopMap (capturedTrap p β₀) (capturedTrap p β₀) := by
  intro x hx
  obtain ⟨⟨hβl, hβu⟩, hDl, hDu⟩ := hx
  have hβmem : x.1 ∈ Icc (0 : ℝ) 1 := ⟨le_trans hβ₀.1 hβl, hβu⟩
  have hwallβ₀ : 1 - p.s β₀ - p.g ≠ 0 :=
    ne_of_gt (zoneDenominator_pos model hgain hβ₀)
  have hwall1 : 1 - p.s 1 - p.g ≠ 0 :=
    ne_of_gt (zoneDenominator_pos model hgain ⟨zero_le_one, le_rfl⟩)
  have hfix : ∀ b : ℝ, 1 - p.s b - p.g ≠ 0 →
      (p.s b + p.g) * p.stationaryStock b + p.I = p.stationaryStock b := by
    intro b hb
    simp only [LoopParams.stationaryStock]
    field_simp
    ring
  have hfix₀ := hfix β₀ hwallβ₀
  have hfix1 := hfix 1 hwall1
  have hsmono : p.s β₀ ≤ p.s x.1 :=
    (stockMultiplier_strictMonoOn model).monotoneOn hβ₀ hβmem hβl
  have hsmono1 : p.s x.1 ≤ p.s 1 :=
    (stockMultiplier_strictMonoOn model).monotoneOn hβmem ⟨zero_le_one, le_rfl⟩ hβu
  have hD0 : 0 ≤ x.2 :=
    le_trans (div_pos model.I_pos (zoneDenominator_pos model hgain hβ₀)).le hDl
  refine ⟨⟨?_, (LoopParams.clipUnit_mem _).2⟩, ?_, ?_⟩
  · -- the policy never falls back below `β₀`
    have hgrad := capturedTrap_gradU_ge model hgain hβ₀ (x := x) ⟨⟨hβl, hβu⟩, hDl, hDu⟩
    have hstep : x.1 ≤ x.1 + p.α * p.gradU x.1 x.2 := by
      have : 0 ≤ p.α * p.gradU x.1 x.2 :=
        mul_nonneg model.α_pos.le (by linarith)
      linarith
    calc β₀ ≤ x.1 := hβl
      _ = LoopParams.clipUnit x.1 := (clipUnit_eq_self' hβmem).symm
      _ ≤ _ := monotone_clipUnit' hstep
  · -- the stock stays above the characteristic at `β₀`
    change p.stationaryStock β₀ ≤ (p.s x.1 + p.g) * x.2 + p.I
    have : (p.s β₀ + p.g) * p.stationaryStock β₀ + p.I ≤ (p.s x.1 + p.g) * x.2 + p.I := by
      have hmul : (p.s β₀ + p.g) * p.stationaryStock β₀ ≤ (p.s x.1 + p.g) * x.2 :=
        mul_le_mul (by linarith) hDl
          (div_pos model.I_pos (zoneDenominator_pos model hgain hβ₀)).le
          (by linarith [(stockMultiplier_nonneg_le model hβmem).1, model.g_nonneg])
      linarith
    linarith [hfix₀, this]
  · -- and below the captured characteristic
    change (p.s x.1 + p.g) * x.2 + p.I ≤ p.stationaryStock 1
    have hmul : (p.s x.1 + p.g) * x.2 ≤ (p.s 1 + p.g) * p.stationaryStock 1 :=
      mul_le_mul (by linarith) hDu hD0
        (by linarith [(stockMultiplier_nonneg_le model ⟨zero_le_one, le_rfl⟩).1,
          model.g_nonneg])
    have : (p.s x.1 + p.g) * x.2 + p.I ≤ (p.s 1 + p.g) * p.stationaryStock 1 + p.I := by
      linarith
    linarith [hfix1, this]

/-- Under a positive gradient floor the policy reaches the captured face. -/
theorem capturedTrap_policy_eq_one (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β₀ : ℝ} (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1)
    (hdrive : 0 < capturedDrive p β₀) {x : ℕ → LoopState}
    (traj : IsLoopOrbit p x) (hx₀ : x 0 ∈ capturedTrap p β₀) :
    ∃ N : ℕ, ∀ n ≥ N, (x n).1 = 1 := by
  have hmem : ∀ n, x n ∈ capturedTrap p β₀ := by
    intro n
    induction n with
    | zero => exact hx₀
    | succ n ih => rw [traj n]; exact capturedTrap_invariant model hgain hβ₀ hdrive ih
  set δ : ℝ := p.α * capturedDrive p β₀ with hδdef
  have hδ : 0 < δ := mul_pos model.α_pos hdrive
  have hstep : ∀ n, min 1 ((x n).1 + δ) ≤ (x (n + 1)).1 := by
    intro n
    have hgrad := capturedTrap_gradU_ge model hgain hβ₀ (hmem n)
    have hβ : (x n).1 ∈ Icc (0 : ℝ) 1 := ⟨le_trans hβ₀.1 (hmem n).1.1, (hmem n).1.2⟩
    have hraw : (x n).1 + δ ≤ (x n).1 + p.α * p.gradU (x n).1 (x n).2 := by
      have := mul_le_mul_of_nonneg_left hgrad model.α_pos.le
      linarith
    rw [traj n]
    change min 1 ((x n).1 + δ) ≤ LoopParams.clipUnit _
    simp only [clipUnit_eq_clipTo, clipTo]
    exact le_trans (min_le_min le_rfl hraw) (le_max_right _ _)
  have hgrow : ∀ n : ℕ, min 1 ((x 0).1 + n * δ) ≤ (x n).1 := by
    intro n
    induction n with
    | zero => simpa only [Nat.cast_zero, zero_mul, add_zero] using min_le_right 1 (x 0).1
    | succ n ih =>
        refine le_trans ?_ (hstep n)
        refine le_min (min_le_left _ _) ?_
        push_cast
        rcases le_total ((x 0).1 + n * δ) 1 with hc | hc
        · rw [min_eq_right hc] at ih
          calc min 1 ((x 0).1 + ((n : ℝ) + 1) * δ) ≤ (x 0).1 + ((n : ℝ) + 1) * δ :=
                min_le_right _ _
            _ = ((x 0).1 + n * δ) + δ := by ring
            _ ≤ (x n).1 + δ := by linarith
        · rw [min_eq_left hc] at ih
          calc min 1 ((x 0).1 + ((n : ℝ) + 1) * δ) ≤ 1 := min_le_left _ _
            _ ≤ (x n).1 + δ := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((1 - (x 0).1) / δ)
  refine ⟨N, fun n hn => ?_⟩
  have hNn : ((N : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hn
  have hge : 1 ≤ (x 0).1 + n * δ := by
    have := (div_lt_iff₀ hδ).1 hN
    nlinarith [hδ.le]
  have := hgrow n
  rw [min_eq_left hge] at this
  exact le_antisymm (hmem n).1.2 this

/--
Paper III, `thm:classify`, captured-corner clause: with a positive gradient floor
the whole trapping set converges to the captured corner.  This is local
asymptotic stability in the form the zone structure uses.
-/
theorem capturedCorner_attraction (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β₀ : ℝ} (hβ₀ : β₀ ∈ Icc (0 : ℝ) 1)
    (hdrive : 0 < capturedDrive p β₀) {x : ℕ → LoopState}
    (traj : IsLoopOrbit p x) (hx₀ : x 0 ∈ capturedTrap p β₀) :
    Tendsto x atTop (𝓝 ((1 : ℝ), p.stationaryStock 1)) := by
  obtain ⟨T, hT⟩ := capturedTrap_policy_eq_one model hgain hβ₀ hdrive traj hx₀
  set a : ℝ := p.s 1 + p.g with hadef
  have ha_nonneg : 0 ≤ a :=
    add_nonneg (stockMultiplier_nonneg_le model ⟨zero_le_one, le_rfl⟩).1 model.g_nonneg
  have ha_lt : a < 1 := by
    have := (stockMultiplier_nonneg_le model (β := 1) ⟨zero_le_one, le_rfl⟩).2
    rw [hadef]; linarith
  have hβtail : ∀ j, (x (T + j)).1 = 1 := fun j => hT _ (by omega)
  have hstockTail : ∀ j, (x (T + j)).2 = arithGeom a p.I (x T).2 j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have hstep : (x ((T + j) + 1)).2 =
            (p.s (x (T + j)).1 + p.g) * (x (T + j)).2 + p.I := by
          rw [traj (T + j)]; rfl
        rw [hβtail j, ih] at hstep
        rw [arithGeom_succ]
        rw [hadef]
        simpa only [Nat.add_assoc] using hstep
  have hlimitEq : p.I / (1 - a) = p.stationaryStock 1 := by
    simp only [hadef, LoopParams.stationaryStock]
    ring
  have hstockLimit : Tendsto (fun j ↦ (x (T + j)).2) atTop
      (𝓝 (p.stationaryStock 1)) := by
    have harith : Tendsto (arithGeom a p.I (x T).2) atTop (𝓝 (p.I / (1 - a))) :=
      tendsto_arithGeom_nhds_of_lt_one ha_nonneg ha_lt
    rw [hlimitEq] at harith
    exact harith.congr' (Eventually.of_forall fun j ↦ (hstockTail j).symm)
  have hpolicyLimit : Tendsto (fun j ↦ (x (T + j)).1) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' (Eventually.of_forall fun j ↦ (hβtail j).symm)
  have htailLimit : Tendsto (fun j ↦ x (T + j)) atTop
      (𝓝 ((1 : ℝ), p.stationaryStock 1)) :=
    (Prod.tendsto_iff _ _).2 ⟨hpolicyLimit, hstockLimit⟩
  apply (tendsto_add_atTop_iff_nat T).1
  simpa only [Nat.add_comm] using htailLimit

/--
The gradient floor is available near the captured corner exactly when `G_g(1) > 0`:
`capturedDrive p 1 = G_g(1)`, and the floor is continuous in `β₀`, so zone (C)
supplies a nondegenerate trapping set.
-/
theorem capturedDrive_one (p : LoopParams) : capturedDrive p 1 = p.G 1 := by
  simp only [capturedDrive, LoopParams.G, LoopParams.stationaryStock]
  ring

/-- Zone-(C)-side existence: `G_g(1) > 0` supplies a nondegenerate captured
trap for Paper III, `thm:classify` and `thm:zones`. -/
theorem exists_capturedTrap_of_G_one_pos (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) (hG1 : 0 < p.G 1) :
    ∃ β₀ ∈ Ico (0 : ℝ) 1, 0 < capturedDrive p β₀ := by
  have hwall1 : 1 - p.s 1 - p.g ≠ 0 :=
    ne_of_gt (zoneDenominator_pos model hgain ⟨zero_le_one, le_rfl⟩)
  have hcont : ContinuousAt (capturedDrive p) 1 := by
    change ContinuousAt (fun b ↦ -p.v + 2 * p.c * (1 - p.c) * p.stationaryStock b) 1
    exact continuousAt_const.add
      (continuousAt_const.mul (continuousAt_stationaryStock_of_ne hwall1))
  have hpos : 0 < capturedDrive p 1 := by rw [capturedDrive_one]; exact hG1
  obtain ⟨ε, hε, hball⟩ :=
    Metric.eventually_nhds_iff.1 (hcont.eventually (lt_mem_nhds hpos))
  refine ⟨max 0 (1 - ε / 2), ⟨le_max_left _ _, ?_⟩, hball ?_⟩
  · rcases le_total (1 - ε / 2) 0 with h | h
    · rw [max_eq_left h]; norm_num
    · rw [max_eq_right h]; linarith
  · rw [Real.dist_eq, abs_of_nonpos (by
      rcases le_total (1 - ε / 2) 0 with h | h
      · rw [max_eq_left h]; norm_num
      · rw [max_eq_right h]; linarith)]
    rcases le_total (1 - ε / 2) 0 with h | h
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right h]; linarith

#print axioms capturedTrap_gradU_ge
#print axioms capturedTrap_invariant
#print axioms capturedTrap_policy_eq_one
#print axioms capturedCorner_attraction
#print axioms capturedDrive_one
#print axioms exists_capturedTrap_of_G_one_pos

/-! ## The calibrated corner -/

/-- Trapping set for the calibrated corner. -/
def calibratedTrap (p : LoopParams) (β₁ : ℝ) : Set LoopState :=
  Icc 0 β₁ ×ˢ Icc (p.stationaryStock 0) (p.stationaryStock β₁)

/-- The uniform gradient ceiling available on the calibrated trapping set. -/
def calibratedDrive (p : LoopParams) (β₁ : ℝ) : ℝ :=
  -p.v + 2 * p.c * p.stationaryStock β₁

/-- At the calibrated face, the trap's gradient ceiling is the stationary
gradient `G_g(0)`. -/
theorem calibratedDrive_zero (p : LoopParams) : calibratedDrive p 0 = p.G 0 := by
  simp only [calibratedDrive, LoopParams.G, LoopParams.stationaryStock]
  ring

/-- On the trapping set the gradient is at most the ceiling. -/
theorem calibratedTrap_gradU_le (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β₁ : ℝ} (hβ₁ : β₁ ∈ Icc (0 : ℝ) 1)
    {x : LoopState} (hx : x ∈ calibratedTrap p β₁) :
    p.gradU x.1 x.2 ≤ calibratedDrive p β₁ := by
  obtain ⟨⟨hβl, hβu⟩, hDl, hDu⟩ := hx
  have hD0 : 0 ≤ x.2 :=
    le_trans (div_pos model.I_pos
      (zoneDenominator_pos model hgain ⟨le_rfl, zero_le_one⟩)).le hDl
  have hcβ : 1 - p.c * x.1 ≤ 1 := by nlinarith [model.c_pos, hβl]
  have h1 : (0 : ℝ) ≤ 1 - p.c * x.1 := by
    nlinarith [model.c_pos, model.c_lt_one, hβu, hβ₁.2]
  simp only [LoopParams.gradU, calibratedDrive]
  nlinarith [hcβ, hDu, hD0, model.c_pos, h1,
    mul_nonneg (by linarith [model.c_pos] : (0:ℝ) ≤ 2 * p.c) (sub_nonneg.mpr hDu),
    mul_nonneg (by linarith [model.c_pos] : (0:ℝ) ≤ 2 * p.c)
      (mul_nonneg (sub_nonneg.mpr hcβ) hD0)]

/-- The calibrated trapping set is forward invariant under a negative ceiling. -/
theorem calibratedTrap_invariant (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β₁ : ℝ} (hβ₁ : β₁ ∈ Icc (0 : ℝ) 1)
    (hdrive : calibratedDrive p β₁ < 0) :
    MapsTo p.loopMap (calibratedTrap p β₁) (calibratedTrap p β₁) := by
  intro x hx
  obtain ⟨⟨hβl, hβu⟩, hDl, hDu⟩ := hx
  have hβmem : x.1 ∈ Icc (0 : ℝ) 1 := ⟨hβl, le_trans hβu hβ₁.2⟩
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hfix : ∀ b : ℝ, 1 - p.s b - p.g ≠ 0 →
      (p.s b + p.g) * p.stationaryStock b + p.I = p.stationaryStock b := by
    intro b hb
    simp only [LoopParams.stationaryStock]
    field_simp
    ring
  have hfix₀ := hfix 0 (ne_of_gt (zoneDenominator_pos model hgain hzero))
  have hfix₁ := hfix β₁ (ne_of_gt (zoneDenominator_pos model hgain hβ₁))
  have hsmono₀ : p.s 0 ≤ p.s x.1 :=
    (stockMultiplier_strictMonoOn model).monotoneOn hzero hβmem hβl
  have hsmono₁ : p.s x.1 ≤ p.s β₁ :=
    (stockMultiplier_strictMonoOn model).monotoneOn hβmem hβ₁ hβu
  have hD0 : 0 ≤ x.2 :=
    le_trans (div_pos model.I_pos (zoneDenominator_pos model hgain hzero)).le hDl
  refine ⟨⟨(LoopParams.clipUnit_mem _).1, ?_⟩, ?_, ?_⟩
  · -- the policy never climbs above `β₁`
    have hgrad := calibratedTrap_gradU_le model hgain hβ₁ (x := x) ⟨⟨hβl, hβu⟩, hDl, hDu⟩
    have hstep : x.1 + p.α * p.gradU x.1 x.2 ≤ x.1 := by
      have : p.α * p.gradU x.1 x.2 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos model.α_pos.le (by linarith)
      linarith
    calc LoopParams.clipUnit (x.1 + p.α * p.gradU x.1 x.2)
        ≤ LoopParams.clipUnit x.1 := monotone_clipUnit' hstep
      _ = x.1 := clipUnit_eq_self' hβmem
      _ ≤ β₁ := hβu
  · change p.stationaryStock 0 ≤ (p.s x.1 + p.g) * x.2 + p.I
    have hmul : (p.s 0 + p.g) * p.stationaryStock 0 ≤ (p.s x.1 + p.g) * x.2 :=
      mul_le_mul (by linarith) hDl
        (div_pos model.I_pos (zoneDenominator_pos model hgain hzero)).le
        (by linarith [(stockMultiplier_nonneg_le model hβmem).1, model.g_nonneg])
    linarith [hfix₀]
  · change (p.s x.1 + p.g) * x.2 + p.I ≤ p.stationaryStock β₁
    have hmul : (p.s x.1 + p.g) * x.2 ≤ (p.s β₁ + p.g) * p.stationaryStock β₁ :=
      mul_le_mul (by linarith) hDu hD0
        (by linarith [(stockMultiplier_nonneg_le model hβ₁).1, model.g_nonneg])
    linarith [hfix₁]

/-- Under a negative gradient ceiling the policy reaches the calibrated face. -/
theorem calibratedTrap_policy_eq_zero (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β₁ : ℝ} (hβ₁ : β₁ ∈ Icc (0 : ℝ) 1)
    (hdrive : calibratedDrive p β₁ < 0) {x : ℕ → LoopState}
    (traj : IsLoopOrbit p x) (hx₀ : x 0 ∈ calibratedTrap p β₁) :
    ∃ N : ℕ, ∀ n ≥ N, (x n).1 = 0 := by
  have hmem : ∀ n, x n ∈ calibratedTrap p β₁ := by
    intro n
    induction n with
    | zero => exact hx₀
    | succ n ih => rw [traj n]; exact calibratedTrap_invariant model hgain hβ₁ hdrive ih
  set δ : ℝ := p.α * (-calibratedDrive p β₁) with hδdef
  have hδ : 0 < δ := mul_pos model.α_pos (by linarith)
  have hstep : ∀ n, (x (n + 1)).1 ≤ max 0 ((x n).1 - δ) := by
    intro n
    have hgrad := calibratedTrap_gradU_le model hgain hβ₁ (hmem n)
    have hraw : (x n).1 + p.α * p.gradU (x n).1 (x n).2 ≤ (x n).1 - δ := by
      have := mul_le_mul_of_nonneg_left hgrad model.α_pos.le
      rw [hδdef]; linarith
    rw [traj n]
    change LoopParams.clipUnit _ ≤ max 0 ((x n).1 - δ)
    simp only [clipUnit_eq_clipTo, clipTo]
    exact max_le_max le_rfl (le_trans (min_le_right _ _) hraw)
  have hdecay : ∀ n : ℕ, (x n).1 ≤ max 0 ((x 0).1 - n * δ) := by
    intro n
    induction n with
    | zero =>
        simp only [Nat.cast_zero, zero_mul, sub_zero]
        exact le_max_right 0 (x 0).1
    | succ n ih =>
        refine le_trans (hstep n) ?_
        refine max_le (le_max_left _ _) ?_
        push_cast
        rcases le_total ((x 0).1 - n * δ) 0 with hc | hc
        · rw [max_eq_left hc] at ih
          calc (x n).1 - δ ≤ 0 - δ := by linarith
            _ ≤ max 0 ((x 0).1 - ((n : ℝ) + 1) * δ) := le_trans (by linarith) (le_max_left _ _)
        · rw [max_eq_right hc] at ih
          calc (x n).1 - δ ≤ ((x 0).1 - n * δ) - δ := by linarith
            _ = (x 0).1 - ((n : ℝ) + 1) * δ := by ring
            _ ≤ max 0 ((x 0).1 - ((n : ℝ) + 1) * δ) := le_max_right _ _
  obtain ⟨N, hN⟩ := exists_nat_gt ((x 0).1 / δ)
  refine ⟨N, fun n hn => ?_⟩
  have hNn : ((N : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hn
  have hle : (x 0).1 - n * δ ≤ 0 := by
    have := (div_lt_iff₀ hδ).1 hN
    nlinarith [hδ.le]
  have := hdecay n
  rw [max_eq_left hle] at this
  exact le_antisymm this (hmem n).1.1

/--
Paper III, `thm:classify`, calibrated-corner clause: the mirror of the captured
case.  With a negative gradient ceiling the whole trapping set converges to the
calibrated corner.
-/
theorem calibratedCorner_attraction (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) {β₁ : ℝ} (hβ₁ : β₁ ∈ Icc (0 : ℝ) 1)
    (hdrive : calibratedDrive p β₁ < 0) {x : ℕ → LoopState}
    (traj : IsLoopOrbit p x) (hx₀ : x 0 ∈ calibratedTrap p β₁) :
    Tendsto x atTop (𝓝 ((0 : ℝ), p.stationaryStock 0)) := by
  obtain ⟨T, hT⟩ := calibratedTrap_policy_eq_zero model hgain hβ₁ hdrive traj hx₀
  set a : ℝ := p.s 0 + p.g with hadef
  have ha_nonneg : 0 ≤ a :=
    add_nonneg (stockMultiplier_nonneg_le model ⟨le_rfl, zero_le_one⟩).1 model.g_nonneg
  have ha_lt : a < 1 := by
    have := (stockMultiplier_nonneg_le model (β := 0) ⟨le_rfl, zero_le_one⟩).2
    rw [hadef]; linarith
  have hβtail : ∀ j, (x (T + j)).1 = 0 := fun j => hT _ (by omega)
  have hstockTail : ∀ j, (x (T + j)).2 = arithGeom a p.I (x T).2 j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have hstep : (x ((T + j) + 1)).2 =
            (p.s (x (T + j)).1 + p.g) * (x (T + j)).2 + p.I := by
          rw [traj (T + j)]; rfl
        rw [hβtail j, ih] at hstep
        rw [arithGeom_succ, hadef]
        simpa only [Nat.add_assoc] using hstep
  have hlimitEq : p.I / (1 - a) = p.stationaryStock 0 := by
    simp only [hadef, LoopParams.stationaryStock]
    ring
  have hstockLimit : Tendsto (fun j ↦ (x (T + j)).2) atTop
      (𝓝 (p.stationaryStock 0)) := by
    have harith : Tendsto (arithGeom a p.I (x T).2) atTop (𝓝 (p.I / (1 - a))) :=
      tendsto_arithGeom_nhds_of_lt_one ha_nonneg ha_lt
    rw [hlimitEq] at harith
    exact harith.congr' (Eventually.of_forall fun j ↦ (hstockTail j).symm)
  have hpolicyLimit : Tendsto (fun j ↦ (x (T + j)).1) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (Eventually.of_forall fun j ↦ (hβtail j).symm)
  apply (tendsto_add_atTop_iff_nat T).1
  simpa only [Nat.add_comm] using
    (Prod.tendsto_iff _ _).2 ⟨hpolicyLimit, hstockLimit⟩

/-- Zone-(A)-side existence: `G_g(0) < 0` supplies a nondegenerate calibrated trap. -/
theorem exists_calibratedTrap_of_G_zero_neg (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀) (hG0 : p.G 0 < 0) :
    ∃ β₁ ∈ Ioc (0 : ℝ) 1, calibratedDrive p β₁ < 0 := by
  have hwall0 : 1 - p.s 0 - p.g ≠ 0 :=
    ne_of_gt (zoneDenominator_pos model hgain ⟨le_rfl, zero_le_one⟩)
  have hcont : ContinuousAt (calibratedDrive p) 0 := by
    change ContinuousAt (fun b ↦ -p.v + 2 * p.c * p.stationaryStock b) 0
    exact continuousAt_const.add
      (continuousAt_const.mul (continuousAt_stationaryStock_of_ne hwall0))
  have hneg : calibratedDrive p 0 < 0 := by rw [calibratedDrive_zero]; exact hG0
  obtain ⟨ε, hε, hball⟩ :=
    Metric.eventually_nhds_iff.1 (hcont.eventually (gt_mem_nhds hneg))
  refine ⟨min 1 (ε / 2), ⟨lt_min zero_lt_one (by linarith), min_le_left _ _⟩, hball ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_of_lt (lt_min zero_lt_one (by linarith)))]
  exact lt_of_le_of_lt (min_le_right _ _) (by linarith)

#print axioms calibratedTrap_gradU_le
#print axioms calibratedTrap_invariant
#print axioms calibratedTrap_policy_eq_zero
#print axioms calibratedCorner_attraction
#print axioms calibratedDrive_zero
#print axioms exists_calibratedTrap_of_G_zero_neg

end

end CivicAlignment.PaperIII
