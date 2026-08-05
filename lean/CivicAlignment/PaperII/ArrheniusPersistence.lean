/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.ArrheniusBlocks

/-!
# Paper II: quiet-block persistence accounting

Long pre-crossing excursions cannot be priced by adding the barrier ledger to
a lingering charge on the same time steps; the accounting uses disjoint
quiet blocks instead.  This file formalizes that combinatorial and
quadratic-action accounting before attaching it to the Gaussian length-class
sum.
-/

namespace CivicAlignment.PaperII

open Filter Function MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal

noncomputable section

/-! ## Block advances and the quiet/nonquiet partition -/

/-- Advance of a scalar record across block `j` of width `T`. -/
def blockAdvance (b : ℕ → ℝ) (T j : ℕ) : ℝ :=
  b ((j + 1) * T) - b (j * T)

/-- Blocks whose record advance is strictly below `gamma`. -/
def quietBlockSet (b : ℕ → ℝ) (T : ℕ) (gamma : ℝ) (k : ℕ) : Finset ℕ :=
  (Finset.range k).filter fun j ↦ blockAdvance b T j < gamma

/-- Complementary blocks whose record advance is at least `gamma`. -/
def nonquietBlockSet (b : ℕ → ℝ) (T : ℕ) (gamma : ℝ) (k : ℕ) : Finset ℕ :=
  (Finset.range k).filter fun j ↦ ¬blockAdvance b T j < gamma

/-- Every block is exactly quiet or nonquiet. -/
theorem quiet_card_add_nonquiet_card
    (b : ℕ → ℝ) (T : ℕ) (gamma : ℝ) (k : ℕ) :
    (quietBlockSet b T gamma k).card +
        (nonquietBlockSet b T gamma k).card = k := by
  simpa only [quietBlockSet, nonquietBlockSet, Finset.card_range] using
    Finset.card_filter_add_card_filter_not
      (s := Finset.range k)
      (p := fun j ↦ blockAdvance b T j < gamma)

/-- Block advances telescope across the regularly spaced endpoints. -/
theorem sum_blockAdvance_range (b : ℕ → ℝ) (T k : ℕ) :
    ∑ j ∈ Finset.range k, blockAdvance b T j =
      b (k * T) - b 0 := by
  let a : ℕ → ℝ := fun j ↦ b (j * T)
  have htel := Finset.sum_range_sub a k
  simpa only [blockAdvance, a, zero_mul] using htel

/-- A monotone record gives every block a nonnegative advance. -/
theorem blockAdvance_nonneg {b : ℕ → ℝ} (hb : Monotone b)
    (T j : ℕ) : 0 ≤ blockAdvance b T j := by
  apply sub_nonneg.mpr
  exact hb (Nat.mul_le_mul_right T j.le_succ)

/-- If the total record growth is at most `B`, the number of blocks advancing
by at least `gamma` pays at least `gamma` each. -/
theorem nonquiet_card_mul_le_totalGrowth
    {b : ℕ → ℝ} (hb : Monotone b)
    {T k : ℕ} {gamma B : ℝ} (_hgamma : 0 ≤ gamma)
    (hgrowth : b (k * T) - b 0 ≤ B) :
    ((nonquietBlockSet b T gamma k).card : ℝ) * gamma ≤ B := by
  let S := nonquietBlockSet b T gamma k
  have hsubset : S ⊆ Finset.range k := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hlarge : ∀ j ∈ S, gamma ≤ blockAdvance b T j := by
    intro j hj
    exact not_lt.mp (Finset.mem_filter.mp hj).2
  calc
    (S.card : ℝ) * gamma = ∑ _j ∈ S, gamma := by simp
    _ ≤ ∑ j ∈ S, blockAdvance b T j :=
      Finset.sum_le_sum fun j hj ↦ hlarge j hj
    _ ≤ ∑ j ∈ Finset.range k, blockAdvance b T j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun j _hj _hnot ↦ blockAdvance_nonneg hb T j)
    _ = b (k * T) - b 0 := sum_blockAdvance_range b T k
    _ ≤ B := hgrowth

/-- An explicit total-growth budget bounds the number of nonquiet blocks by a
natural number `K`. -/
theorem nonquiet_card_le
    {b : ℕ → ℝ} (hb : Monotone b)
    {T k K : ℕ} {gamma B : ℝ} (hgamma : 0 < gamma)
    (hgrowth : b (k * T) - b 0 ≤ B)
    (hbudget : B ≤ (K : ℝ) * gamma) :
    (nonquietBlockSet b T gamma k).card ≤ K := by
  have hmul := (nonquiet_card_mul_le_totalGrowth hb hgamma.le hgrowth).trans
    hbudget
  have hcast : ((nonquietBlockSet b T gamma k).card : ℝ) ≤ K := by
    nlinarith
  exact_mod_cast hcast

/-- Consequently at least `k-K` blocks are quiet. -/
theorem sub_le_quiet_card
    {b : ℕ → ℝ} {T k K : ℕ} {gamma : ℝ}
    (hnonquiet : (nonquietBlockSet b T gamma k).card ≤ K) :
    k - K ≤ (quietBlockSet b T gamma k).card := by
  have hpartition := quiet_card_add_nonquiet_card b T gamma k
  omega

/-! ## Disjoint quadratic action of blocks -/

/-- Quadratic action spent on block `j` of width `T`. -/
def controlBlockAction (u : ℕ → ℝ) (T j : ℕ) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ n ∈ Finset.Ico (j * T) ((j + 1) * T), (u n) ^ 2

/-- Quadratic action on the interval `[start, start + length)`. -/
def controlIntervalAction (u : ℕ → ℝ) (start length : ℕ) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ n ∈ Finset.Ico start (start + length), (u n) ^ 2

/-- A shifted finite control vector has exactly the corresponding interval
action in the infinite control history. -/
theorem gaussianVectorAction_shift_eq_controlIntervalAction
    (u : ℕ → ℝ) (start length : ℕ) :
    gaussianVectorAction (fun i : Fin length ↦ u (start + i)) =
      controlIntervalAction u start length := by
  unfold gaussianVectorAction controlIntervalAction
  rw [Fin.sum_univ_eq_sum_range
    (fun n ↦ (u (start + n)) ^ 2) length]
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]

/-- An interval contained in the initial horizon spends no more than the
total action through that horizon. -/
theorem controlIntervalAction_le_controlAction
    (u : ℕ → ℝ) (start length horizon : ℕ)
    (horizonBound : start + length ≤ horizon) :
    controlIntervalAction u start length ≤ controlAction u horizon := by
  unfold controlIntervalAction controlAction
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_Ico] at hn
    simp only [Finset.mem_range]
    exact hn.2.trans_le horizonBound
  · intro n _hn _hnot
    exact sq_nonneg (u n)

/-- Shifting an infinite control history turns its initial action into the
corresponding interval action of the original history. -/
theorem controlAction_shift_eq_controlIntervalAction
    (u : ℕ → ℝ) (start length : ℕ) :
    controlAction (fun n ↦ u (start + n)) length =
      controlIntervalAction u start length := by
  unfold controlAction controlIntervalAction
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]

/-- The interval action of the aligned `j`th block is the block action. -/
theorem controlIntervalAction_aligned_eq_controlBlockAction
    (u : ℕ → ℝ) (T j : ℕ) :
    controlIntervalAction u (j * T) T = controlBlockAction u T j := by
  unfold controlIntervalAction controlBlockAction
  rw [show (j + 1) * T = j * T + T by simp only [Nat.add_mul, one_mul]]

/-- Every block action is nonnegative. -/
theorem controlBlockAction_nonneg (u : ℕ → ℝ) (T j : ℕ) :
    0 ≤ controlBlockAction u T j := by
  unfold controlBlockAction
  positivity

/-- Summing disjoint consecutive block actions gives exactly the action
through the final block endpoint. -/
theorem sum_controlBlockAction_range
    (u : ℕ → ℝ) (T k : ℕ) :
    ∑ j ∈ Finset.range k, controlBlockAction u T j =
      controlAction u (k * T) := by
  induction k with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, zero_mul,
      controlAction, mul_zero]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [controlAction, controlBlockAction]
      rw [← mul_add]
      congr 1
      have hle : k * T ≤ (k + 1) * T :=
        Nat.mul_le_mul_right T k.le_succ
      exact Finset.sum_range_add_sum_Ico
        (fun n ↦ (u n) ^ 2) hle

/-- The sum of actions over any selected blocks is no larger than the total
action over all blocks. -/
theorem sum_controlBlockAction_subset_le
    (u : ℕ → ℝ) (T k : ℕ) {S : Finset ℕ}
    (hS : S ⊆ Finset.range k) :
    ∑ j ∈ S, controlBlockAction u T j ≤
      controlAction u (k * T) := by
  rw [← sum_controlBlockAction_range]
  exact Finset.sum_le_sum_of_subset_of_nonneg hS
    (fun j _hj _hnot ↦ controlBlockAction_nonneg u T j)

/-- If every quiet block pays at least `c0`, disjointness charges their count
without overlapping the barrier ledger. -/
theorem quiet_card_mul_le_controlAction
    {b : ℕ → ℝ} (u : ℕ → ℝ) {T k : ℕ} {gamma c0 : ℝ}
    (hcharge : ∀ j ∈ quietBlockSet b T gamma k,
      c0 ≤ controlBlockAction u T j) :
    ((quietBlockSet b T gamma k).card : ℝ) * c0 ≤
      controlAction u (k * T) := by
  let S := quietBlockSet b T gamma k
  have hsubset : S ⊆ Finset.range k := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  calc
    (S.card : ℝ) * c0 = ∑ _j ∈ S, c0 := by simp
    _ ≤ ∑ j ∈ S, controlBlockAction u T j :=
      Finset.sum_le_sum fun j hj ↦ hcharge j hj
    _ ≤ controlAction u (k * T) :=
      sum_controlBlockAction_subset_le u T k hsubset

/-- Combined quiet-block accounting: at most `K` nonquiet blocks and a charge
`c0` on every quiet block imply the long-excursion action
`(k-K)c0`. -/
theorem sub_mul_le_controlAction_of_quiet_charge
    {b : ℕ → ℝ} (u : ℕ → ℝ) {T k K : ℕ} {gamma c0 : ℝ}
    (hc0 : 0 ≤ c0)
    (hnonquiet : (nonquietBlockSet b T gamma k).card ≤ K)
    (hcharge : ∀ j ∈ quietBlockSet b T gamma k,
      c0 ≤ controlBlockAction u T j) :
    ((k - K : ℕ) : ℝ) * c0 ≤ controlAction u (k * T) := by
  have hcount := sub_le_quiet_card hnonquiet
  have hcast : ((k - K : ℕ) : ℝ) ≤
      (quietBlockSet b T gamma k).card := by exact_mod_cast hcount
  exact (mul_le_mul_of_nonneg_right hcast hc0).trans
    (quiet_card_mul_le_controlAction u hcharge)

/-! ## Spaced sliding windows -/

/-- A charged window of `length` steps starting at the beginning of aligned
block `j`, where the surrounding blocks have the possibly larger width
`stride`. -/
def controlSpacedWindowAction (u : ℕ → ℝ)
    (stride length j : ℕ) : ℝ :=
  controlIntervalAction u (j * stride) length

/-- A window no longer than its surrounding block spends no more action than
that block. -/
theorem controlSpacedWindowAction_le_controlBlockAction
    (u : ℕ → ℝ) {stride length j : ℕ} (hlength : length ≤ stride) :
    controlSpacedWindowAction u stride length j ≤
      controlBlockAction u stride j := by
  unfold controlSpacedWindowAction controlIntervalAction controlBlockAction
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_Ico] at hn ⊢
    constructor
    · exact hn.1
    · have hupper : j * stride + length ≤ (j + 1) * stride := by
        calc
          j * stride + length ≤ j * stride + stride :=
            Nat.add_le_add_left hlength _
          _ = (j + 1) * stride := by simp only [Nat.add_mul, one_mul]
      exact hn.2.trans_le hupper
  · intro n _hn _hnot
    exact sq_nonneg (u n)

/-- Any selected family of such aligned, spaced windows has total action no
larger than the action through the final surrounding block. -/
theorem sum_controlSpacedWindowAction_subset_le
    (u : ℕ → ℝ) {stride length k : ℕ} {S : Finset ℕ}
    (hlength : length ≤ stride) (hS : S ⊆ Finset.range k) :
    ∑ j ∈ S, controlSpacedWindowAction u stride length j ≤
      controlAction u (k * stride) := by
  calc
    ∑ j ∈ S, controlSpacedWindowAction u stride length j ≤
        ∑ j ∈ S, controlBlockAction u stride j := by
      exact Finset.sum_le_sum fun j _hj ↦
        controlSpacedWindowAction_le_controlBlockAction u hlength
    _ ≤ controlAction u (k * stride) :=
      sum_controlBlockAction_subset_le u stride k hS

/-- If each selected spaced window pays `c`, disjointness charges the number
of selected windows without double-counting any control coordinate. -/
theorem spacedWindow_card_mul_le_controlAction
    (u : ℕ → ℝ) {stride length k : ℕ} {S : Finset ℕ} {c : ℝ}
    (hlength : length ≤ stride) (hS : S ⊆ Finset.range k)
    (hcharge : ∀ j ∈ S, c ≤ controlSpacedWindowAction u stride length j) :
    (S.card : ℝ) * c ≤ controlAction u (k * stride) := by
  calc
    (S.card : ℝ) * c = ∑ _j ∈ S, c := by simp
    _ ≤ ∑ j ∈ S, controlSpacedWindowAction u stride length j :=
      Finset.sum_le_sum fun j hj ↦ hcharge j hj
    _ ≤ controlAction u (k * stride) :=
      sum_controlSpacedWindowAction_subset_le u hlength hS

/-! ## Model-specific source of a quiet-block charge -/

/-- The order-compatible home rectangle of radius `epsilon` lies in the
closed metric ball of the same radius around the calibrated corner. -/
theorem calibratedHomeRectangle_subset_closedBall
    (p : LoopParams) (epsilon : ℝ) :
    calibratedHomeRectangle p epsilon ⊆
      Metric.closedBall (calibratedPoint p) epsilon := by
  intro z hz
  rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff]
  constructor
  · rw [Real.dist_eq]
    simp only [calibratedPoint, sub_zero]
    rw [abs_of_nonneg hz.1.1]
    exact hz.1.2
  · rw [Real.dist_eq]
    change |z.2 - p.stationaryStock 0| ≤ epsilon
    have hnonneg : 0 ≤ z.2 - p.stationaryStock 0 := sub_nonneg.mpr hz.2.1
    rw [abs_of_nonneg hnonneg]
    linarith [hz.2.2]

/-- If an unforced endpoint is in an inner home ball while the controlled
endpoint remains outside a larger one, their mutual distance is at least the
gap between the radii. -/
theorem home_ball_gap_le_endpoint_dist
    {p : LoopParams} {inner outer : ℝ} {unforced controlled : LoopState}
    (hunforced : unforced ∈ Metric.closedBall (calibratedPoint p) inner)
    (hcontrolled : outer ≤ dist controlled (calibratedPoint p)) :
    outer - inner ≤ dist unforced controlled := by
  have hinner : dist unforced (calibratedPoint p) ≤ inner := hunforced
  have htriangle : dist controlled (calibratedPoint p) ≤
      dist controlled unforced + dist unforced (calibratedPoint p) :=
    dist_triangle controlled unforced (calibratedPoint p)
  rw [dist_comm controlled unforced] at htriangle
  linarith

/-- Compact-start funneling into an inner home ball turns avoidance of a
strictly larger home ball into a uniform positive action charge. -/
theorem exists_uniform_action_cost_of_avoiding_home
    (p : LoopParams) (rho : ℝ) {K : Set LoopState}
    (hK : IsCompact K) (N : ℕ) {inner outer : ℝ}
    (hgap : inner < outer)
    (hhome : ∀ x₀ ∈ K,
      finiteControlledOrbitFrom p rho x₀ (0 : Fin N → ℝ) N ∈
        Metric.closedBall (calibratedPoint p) inner) :
    ∃ c : ℝ, 0 < c ∧
      ∀ x₀ ∈ K, ∀ u : Fin N → ℝ,
        outer ≤ dist
          (finiteControlledOrbitFrom p rho x₀ u N)
          (calibratedPoint p) →
        c ≤ gaussianVectorAction u := by
  have hmargin : 0 < outer - inner := sub_pos.mpr hgap
  obtain ⟨c, hc, hcost⟩ :=
    exists_uniform_action_cost_of_endpoint_deviation
      p rho hK N hmargin
  refine ⟨c, hc, fun x₀ hx₀ u hout ↦ ?_⟩
  apply hcost x₀ hx₀ u
  exact home_ball_gap_le_endpoint_dist (hhome x₀ hx₀) hout

/-- The corrected R3 away-set charge.  Uniform funneling on the complete
pre-crossing region outside a full-state saddle ball turns failure to enter a
larger home ball into a fixed positive action cost. -/
theorem exists_awaySaddle_avoiding_home_action_cost
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho saddleRadius epsilon : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hsaddleRadius : 0 < saddleRadius) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ z ∈ weightedPreCrossingAwaySet weighted saddleRadius,
        ∀ u : Fin T → ℝ,
          2 * epsilon ≤
              dist (finiteControlledOrbitFrom p rho z u T)
                (calibratedPoint p) →
            c ≤ gaussianVectorAction u := by
  obtain ⟨T, hfunnel⟩ := exists_uniform_away_saddle_funnel_time
    model ss threshold hrho hcoop weighted hsaddleRadius hepsilon
  have hhome : ∀ z ∈ weightedPreCrossingAwaySet weighted saddleRadius,
      finiteControlledOrbitFrom p rho z (0 : Fin T → ℝ) T ∈
        Metric.closedBall (calibratedPoint p) epsilon := by
    intro z hz
    rw [finiteControlledOrbitFrom_zero_eq_civicWeightedOrbit]
    exact calibratedHomeRectangle_subset_closedBall p epsilon (hfunnel z hz)
  obtain ⟨c, hc, hcost⟩ := exists_uniform_action_cost_of_avoiding_home
    p rho (isCompact_weightedPreCrossingAwaySet weighted saddleRadius) T
      (by linarith : epsilon < 2 * epsilon) hhome
  exact ⟨T, c, hc, hcost⟩

/-- Sliding-window form of the away-set charge.  The window may start at any
time of an arbitrary controlled path; its action is the corresponding
half-open interval of the original control history. -/
theorem exists_awaySaddle_slidingWindow_action_cost
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho saddleRadius epsilon : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hsaddleRadius : 0 < saddleRadius) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ (z₀ : LoopState) (u : ℕ → ℝ) (x : ℕ → LoopState),
        IsControlledCivicWeightedPathFrom p rho z₀ u x →
          ∀ start : ℕ,
            x start ∈ weightedPreCrossingAwaySet weighted saddleRadius →
            2 * epsilon ≤ dist (x (start + T)) (calibratedPoint p) →
            c ≤ controlIntervalAction u start T := by
  obtain ⟨T, c, hc, hcost⟩ := exists_awaySaddle_avoiding_home_action_cost
    model ss threshold hrho hcoop weighted hsaddleRadius hepsilon
  refine ⟨T, c, hc, fun z₀ u x path start hstart hout ↦ ?_⟩
  have htail :
      finiteControlledOrbitFrom p rho (x start)
          (fun i : Fin T ↦ u (start + i)) T =
        x (start + T) :=
    finiteControlledOrbitFrom_restrict_eq (path.tail start) le_rfl
  have hpay : c ≤
      gaussianVectorAction (fun i : Fin T ↦ u (start + i)) := by
    apply hcost (x start) hstart
    rw [htail]
    exact hout
  calc
    c ≤ gaussianVectorAction (fun i : Fin T ↦ u (start + i)) := hpay
    _ = controlIntervalAction u start T :=
      gaussianVectorAction_shift_eq_controlIntervalAction u start T

/-- Disjoint-window consequence of the corrected R3 away-set charge.  Among
aligned windows separated by at least the funnel horizon, every selected
window that starts away from the saddle and still avoids the larger home ball
pays the same positive action cost, and those costs add without overlap. -/
theorem exists_awaySaddle_spacedWindow_action_bound
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho saddleRadius epsilon : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hsaddleRadius : 0 < saddleRadius) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ (z₀ : LoopState) (u : ℕ → ℝ) (x : ℕ → LoopState),
        IsControlledCivicWeightedPathFrom p rho z₀ u x →
          ∀ (stride k : ℕ) (S : Finset ℕ),
            T ≤ stride →
            S ⊆ Finset.range k →
            (∀ j ∈ S,
              x (j * stride) ∈
                weightedPreCrossingAwaySet weighted saddleRadius) →
            (∀ j ∈ S,
              2 * epsilon ≤
                dist (x (j * stride + T)) (calibratedPoint p)) →
            (S.card : ℝ) * c ≤ controlAction u (k * stride) := by
  obtain ⟨T, c, hc, hwindow⟩ :=
    exists_awaySaddle_slidingWindow_action_cost
      model ss threshold hrho hcoop weighted hsaddleRadius hepsilon
  refine ⟨T, c, hc, fun z₀ u x path stride k S hT hS haway hout ↦ ?_⟩
  apply spacedWindow_card_mul_le_controlAction u hT hS
  intro j hj
  unfold controlSpacedWindowAction
  exact hwindow z₀ u x path (j * stride)
    (haway j hj) (hout j hj)

/-- Starts dominated by a single sub-saddle point on the stationary
characteristic. -/
def characteristicFunnelStartSet (p : LoopParams) (b : ℝ) : Set LoopState :=
  absorbingBox p ∩ Set.Icc (calibratedPoint p) (b, p.stationaryStock b)

/-- The characteristic-funnel start set is compact. -/
theorem isCompact_characteristicFunnelStartSet (p : LoopParams) (b : ℝ) :
    IsCompact (characteristicFunnelStartSet p b) := by
  exact (isCompact_absorbingBox p).inter_right isClosed_Icc

/-- The case-B deterministic funnel supplies a positive quiet-block action
charge: a controlled block which avoids the doubled home ball must spend a
fixed amount of quadratic action, uniformly over the entire dominated
sub-saddle order rectangle. -/
theorem exists_characteristicFunnel_avoiding_home_action_cost
    {p : LoopParams} {rho b epsilon : ℝ}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (threshold : ThresholdAssumption p) (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hb : b ∈ Ioo (0 : ℝ) 1) (hbelow : b < weighted.βdagger)
    (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ x₀ ∈ characteristicFunnelStartSet p b,
        ∀ u : Fin N → ℝ,
          2 * epsilon ≤ dist
            (finiteControlledOrbitFrom p rho x₀ u N)
            (calibratedPoint p) →
          c ≤ gaussianVectorAction u := by
  obtain ⟨N, hfunnel⟩ :=
    exists_uniform_characteristic_funnel_time
      model ss threshold hrho hcoop weighted hb hbelow hepsilon
  have hhome : ∀ x₀ ∈ characteristicFunnelStartSet p b,
      finiteControlledOrbitFrom p rho x₀ (0 : Fin N → ℝ) N ∈
        Metric.closedBall (calibratedPoint p) epsilon := by
    intro x₀ hx₀
    have horbit :
        finiteControlledOrbitFrom p rho x₀ (0 : Fin N → ℝ) N =
          civicWeightedOrbit p rho x₀ N :=
      finiteControlledOrbitFrom_zero_eq_civicWeightedOrbit p rho x₀ N
    rw [horbit]
    apply calibratedHomeRectangle_subset_closedBall p epsilon
    exact hfunnel x₀ hx₀.1 hx₀.2.1 hx₀.2.2
  obtain ⟨c, hc, hcost⟩ :=
    exists_uniform_action_cost_of_avoiding_home
      p rho (isCompact_characteristicFunnelStartSet p b) N
        (by linarith : epsilon < 2 * epsilon) hhome
  exact ⟨N, c, hc, hcost⟩

/-- Uniform case-C reduction: between two sub-saddle policy levels `b<b'`,
elevated stock contracts into the characteristic-funnel start set at `b'`
within one common time, unless policy has already exceeded `b`. -/
theorem exists_caseC_to_characteristicFunnelStartSet_time
    {p : LoopParams} {b b' : ℝ}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hb : b ∈ Icc (0 : ℝ) 1) (hb' : b' ∈ Icc (0 : ℝ) 1)
    (hbb' : b < b') :
    ∃ N : ℕ, ∀ (rho : ℝ) (x₀ : LoopState) (u : ℕ → ℝ)
      (x : ℕ → LoopState),
      IsControlledCivicWeightedPathFrom p rho x₀ u x →
      x₀ ∈ absorbingBox p →
      calibratedPoint p ≤ x₀ →
      (∀ k ≤ N, (x k).1 ≤ b) →
      x N ∈ characteristicFunnelStartSet p b' := by
  have hstocklt : p.stationaryStock b < p.stationaryStock b' :=
    (stationaryStock_strictMonoOn model) hb hb' hbb'
  let epsilon : ℝ := p.stationaryStock b' - p.stationaryStock b
  have hepsilon : 0 < epsilon := sub_pos.mpr hstocklt
  obtain ⟨N, hcontract⟩ :=
    exists_uniform_stock_contraction_time model hb hepsilon
  refine ⟨N, fun rho x₀ u x path hx₀ hlower hpolicy ↦ ?_⟩
  have hstock : (x N).2 ≤ p.stationaryStock b' := by
    have hcontracted := hcontract rho x₀ u x path hx₀
      (fun k hk ↦ hpolicy k hk.le)
    dsimp only [epsilon] at hcontracted
    linarith
  have hpolicyN : (x N).1 ≤ b' :=
    (hpolicy N le_rfl).trans hbb'.le
  exact ⟨path.mem_absorbingBox model hx₀ N,
    path.calibratedPoint_le model ss hx₀ hlower N,
    hpolicyN, hstock⟩

/-- Combined case-C/case-B lingering charge.  Uniformly over the absorbing
box, a controlled path which stays below the lower sub-saddle level for the
whole block yet avoids the doubled home ball must spend a fixed positive
amount of action.  The first phase contracts elevated stock into the
`b'`-characteristic rectangle; the disjoint tail phase pays the funnel
deviation charge. -/
theorem exists_farPolicy_avoiding_home_action_cost
    {p : LoopParams} {rho b b' epsilon : ℝ}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (threshold : ThresholdAssumption p) (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hb : b ∈ Ioo (0 : ℝ) 1) (hb' : b' ∈ Ioo (0 : ℝ) 1)
    (hbb' : b < b') (hbelow : b' < weighted.βdagger)
    (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ (x₀ : LoopState) (u : ℕ → ℝ) (x : ℕ → LoopState),
        IsControlledCivicWeightedPathFrom p rho x₀ u x →
        x₀ ∈ absorbingBox p →
        calibratedPoint p ≤ x₀ →
        (∀ k ≤ T, (x k).1 ≤ b) →
        2 * epsilon ≤ dist (x T) (calibratedPoint p) →
        c ≤ controlAction u T := by
  obtain ⟨Ncontract, hcontract⟩ :=
    exists_caseC_to_characteristicFunnelStartSet_time model ss
      ⟨hb.1.le, hb.2.le⟩ ⟨hb'.1.le, hb'.2.le⟩ hbb'
  obtain ⟨Nfunnel, c, hc, hfunnel⟩ :=
    exists_characteristicFunnel_avoiding_home_action_cost
      model ss threshold hrho hcoop weighted hb' hbelow hepsilon
  refine ⟨Ncontract + Nfunnel, c, hc,
    fun x₀ u x path hx₀ hlower hpolicy hout ↦ ?_⟩
  have hmid : x Ncontract ∈ characteristicFunnelStartSet p b' :=
    hcontract rho x₀ u x path hx₀ hlower
      (fun k hk ↦ hpolicy k (hk.trans (Nat.le_add_right Ncontract Nfunnel)))
  have htailEq :
      finiteControlledOrbitFrom p rho (x Ncontract)
          (fun i : Fin Nfunnel ↦ u (Ncontract + i)) Nfunnel =
        x (Ncontract + Nfunnel) :=
    finiteControlledOrbitFrom_restrict_eq (path.tail Ncontract) le_rfl
  have htailCost : c ≤
      gaussianVectorAction
        (fun i : Fin Nfunnel ↦ u (Ncontract + i)) := by
    apply hfunnel (x Ncontract) hmid
    rw [htailEq]
    exact hout
  calc
    c ≤ gaussianVectorAction
        (fun i : Fin Nfunnel ↦ u (Ncontract + i)) := htailCost
    _ = controlIntervalAction u Ncontract Nfunnel :=
      gaussianVectorAction_shift_eq_controlIntervalAction
        u Ncontract Nfunnel
    _ ≤ controlAction u (Ncontract + Nfunnel) :=
      controlIntervalAction_le_controlAction
        u Ncontract Nfunnel (Ncontract + Nfunnel) le_rfl

/-- Aligned-block form of the combined far-policy lingering charge. -/
theorem exists_farPolicy_avoiding_home_block_action_cost
    {p : LoopParams} {rho b b' epsilon : ℝ}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (threshold : ThresholdAssumption p) (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hb : b ∈ Ioo (0 : ℝ) 1) (hb' : b' ∈ Ioo (0 : ℝ) 1)
    (hbb' : b < b') (hbelow : b' < weighted.βdagger)
    (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ (x₀ : LoopState) (u : ℕ → ℝ) (x : ℕ → LoopState),
        IsControlledCivicWeightedPathFrom p rho x₀ u x →
        x₀ ∈ absorbingBox p →
        calibratedPoint p ≤ x₀ →
        ∀ j : ℕ,
          (∀ n ≤ T, (x (j * T + n)).1 ≤ b) →
          2 * epsilon ≤ dist (x ((j + 1) * T)) (calibratedPoint p) →
          c ≤ controlBlockAction u T j := by
  obtain ⟨T, c, hc, hlocalCost⟩ :=
    exists_farPolicy_avoiding_home_action_cost
      model ss threshold hrho hcoop weighted hb hb' hbb' hbelow hepsilon
  refine ⟨T, c, hc, fun x₀ u x path hx₀ hlower j hpolicy hout ↦ ?_⟩
  let start := j * T
  have hxstart : x start ∈ absorbingBox p :=
    path.mem_absorbingBox model hx₀ start
  have hlowerStart : calibratedPoint p ≤ x start :=
    path.calibratedPoint_le model ss hx₀ hlower start
  have htime : start + T = (j + 1) * T := by
    dsimp only [start]
    simp only [Nat.add_mul, one_mul]
  have hcost : c ≤
      controlAction (fun n ↦ u (start + n)) T := by
    apply hlocalCost (x start) (fun n ↦ u (start + n))
      (fun n ↦ x (start + n)) (path.tail start)
      hxstart hlowerStart
    · intro n hn
      exact hpolicy n hn
    · simpa only [htime] using hout
  calc
    c ≤ controlAction (fun n ↦ u (start + n)) T := hcost
    _ = controlIntervalAction u start T :=
      controlAction_shift_eq_controlIntervalAction u start T
    _ = controlBlockAction u T j := by
      dsimp only [start]
      exact controlIntervalAction_aligned_eq_controlBlockAction u T j

/-- Conditional R2 lingering ledger for the actual civic-weighted path.
Once every quiet block is known to stay in the far-policy regime and avoid
home, the model-specific block charge and the running-maximum count combine
to give `(k-K)c` action on disjoint time steps.  The remaining block
dichotomy only has to establish the two displayed quiet-block premises. -/
theorem exists_quietBlock_lingering_action_bound
    {p : LoopParams} {rho b b' epsilon gamma : ℝ}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (threshold : ThresholdAssumption p) (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hb : b ∈ Ioo (0 : ℝ) 1) (hb' : b' ∈ Ioo (0 : ℝ) 1)
    (hbb' : b < b') (hbelow : b' < weighted.βdagger)
    (hepsilon : 0 < epsilon) (hgamma : 0 < gamma) :
    ∃ T : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ (K k : ℕ) (x₀ : LoopState) (u : ℕ → ℝ)
        (x : ℕ → LoopState),
        IsControlledCivicWeightedPathFrom p rho x₀ u x →
        x₀ ∈ absorbingBox p →
        calibratedPoint p ≤ x₀ →
        policyRunningMax x (k * T) ≤ weighted.βdagger →
        weighted.βdagger ≤ (K : ℝ) * gamma →
        (∀ j ∈ quietBlockSet (policyRunningMax x) T gamma k,
          ∀ n ≤ T, (x (j * T + n)).1 ≤ b) →
        (∀ j ∈ quietBlockSet (policyRunningMax x) T gamma k,
          2 * epsilon ≤
            dist (x ((j + 1) * T)) (calibratedPoint p)) →
        (((k - K : ℕ) : ℝ) * c ≤ controlAction u (k * T)) := by
  obtain ⟨T, c, hc, hblockCost⟩ :=
    exists_farPolicy_avoiding_home_block_action_cost
      model ss threshold hrho hcoop weighted hb hb' hbb' hbelow hepsilon
  refine ⟨T, c, hc,
    fun K k x₀ u x path hx₀ hlower hpreCross hbudget hfar hout ↦ ?_⟩
  have hmaxMono : Monotone (policyRunningMax x) :=
    monotone_runningMax fun n ↦ (x n).1
  have hmaxZero : 0 ≤ policyRunningMax x 0 := by
    simpa only [policyRunningMax, runningMax_zero, path.initial] using hx₀.1.1
  have hgrowth :
      policyRunningMax x (k * T) - policyRunningMax x 0 ≤
        weighted.βdagger := by
    linarith
  have hnonquiet :
      (nonquietBlockSet (policyRunningMax x) T gamma k).card ≤ K :=
    nonquiet_card_le hmaxMono hgamma hgrowth hbudget
  apply sub_mul_le_controlAction_of_quiet_charge
    (b := policyRunningMax x) u hc.le hnonquiet
  intro j hj
  exact hblockCost x₀ u x path hx₀ hlower j
    (hfar j hj) (hout j hj)

/-! ## Dimension-explicit Gaussian action tails -/

/-- One-coordinate exponential moment used to expose the dependence on the
length-class dimension. -/
def gaussianHalfSquareMgf (t : ℝ) : ℝ :=
  mgf (fun x : ℝ ↦ (1 / 2 : ℝ) * x ^ 2) (gaussianReal 0 1) t

/-- The finite-vector action MGF factors as the corresponding one-coordinate
MGF to the dimension. -/
theorem mgf_gaussianVectorAction_eq_pow (T : ℕ) (t : ℝ) :
    mgf gaussianVectorAction (standardGaussianVector T) t =
      gaussianHalfSquareMgf t ^ T := by
  unfold gaussianHalfSquareMgf
  unfold mgf standardGaussianVector
  have hfun : (fun xi : Fin T → ℝ ↦
      Real.exp (t * gaussianVectorAction xi)) =
      (fun xi : Fin T → ℝ ↦
        ∏ i, Real.exp (t * ((1 / 2 : ℝ) * (xi i) ^ 2))) := by
    funext xi
    simp only [gaussianVectorAction]
    have hsum : t * ((1 / 2 : ℝ) * ∑ i, (xi i) ^ 2) =
        ∑ i, t * ((1 / 2 : ℝ) * (xi i) ^ 2) := by
      simp only [Finset.mul_sum]
    rw [hsum]
    exact Real.exp_sum Finset.univ
      (fun i : Fin T ↦ t * ((1 / 2 : ℝ) * (xi i) ^ 2))
  rw [hfun]
  simpa only [Fintype.card_fin] using
    (MeasureTheory.integral_fintype_prod_eq_pow
      (ι := Fin T) (μ := gaussianReal 0 1)
      (fun x : ℝ ↦ Real.exp (t * ((1 / 2 : ℝ) * x ^ 2))))

/-- The one-coordinate MGF is strictly positive throughout the Chernoff
domain. -/
theorem gaussianHalfSquareMgf_pos {t : ℝ} (ht : t < 1) :
    0 < gaussianHalfSquareMgf t := by
  exact mgf_pos (integrable_exp_half_sq_standardGaussian ht)

/-- Quadratic action is a continuous function of a finite control vector. -/
theorem continuous_gaussianVectorAction (T : ℕ) :
    Continuous (gaussianVectorAction : (Fin T → ℝ) → ℝ) := by
  unfold gaussianVectorAction
  fun_prop

/-- A radial action-tail event in fixed Gaussian dimension. -/
def gaussianActionTailEvent (T : ℕ) (B : ℝ) : Set (Fin T → ℝ) :=
  {xi | B ≤ gaussianVectorAction xi}

/-- Its product-Gaussian probability. -/
def gaussianActionTailProbability (T : ℕ) (B : ℝ) : ℝ≥0∞ :=
  standardGaussianVector T (gaussianActionTailEvent T B)

/-- Radial action tails are Borel measurable. -/
theorem measurableSet_gaussianActionTailEvent (T : ℕ) (B : ℝ) :
    MeasurableSet (gaussianActionTailEvent T B) := by
  exact measurableSet_Ici.preimage
    (continuous_gaussianVectorAction T).measurable

/-- The event that the action of the first `T` coordinates of an infinite
Gaussian history is at least `B`. -/
def gaussianPrefixActionTailEvent (T : ℕ) (B : ℝ) : Set GaussianNoisePath :=
  gaussianPrefix T ⁻¹' gaussianActionTailEvent T B

/-- Prefix action-tail events are measurable on the infinite product space. -/
theorem measurableSet_gaussianPrefixActionTailEvent (T : ℕ) (B : ℝ) :
    MeasurableSet (gaussianPrefixActionTailEvent T B) := by
  exact (measurableSet_gaussianActionTailEvent T B).preimage
    (measurable_gaussianPrefix T)

/-- A prefix action tail under the canonical infinite Gaussian law has
exactly the corresponding finite-product probability. -/
theorem standardGaussianSequence_gaussianPrefixActionTailEvent
    (T : ℕ) (B : ℝ) :
    standardGaussianSequence (gaussianPrefixActionTailEvent T B) =
      gaussianActionTailProbability T B := by
  rw [gaussianPrefixActionTailEvent,
    ← Measure.map_apply (measurable_gaussianPrefix T)
      (measurableSet_gaussianActionTailEvent T B),
    standardGaussianSequence_map_prefix]
  rfl

/-- Chernoff bound with the dependence on dimension exposed as a power of the
one-coordinate MGF. -/
theorem gaussianActionTailProbability_le_chernoff
    (T : ℕ) {B t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    gaussianActionTailProbability T B ≤
      ENNReal.ofReal
        (Real.exp (-t * B) * gaussianHalfSquareMgf t ^ T) := by
  letI : IsProbabilityMeasure (standardGaussianVector T) := by
    unfold standardGaussianVector
    infer_instance
  have hchernoff :
      (standardGaussianVector T).real (gaussianActionTailEvent T B) ≤
        Real.exp (-t * B) *
          mgf gaussianVectorAction (standardGaussianVector T) t := by
    exact measure_ge_le_exp_mul_mgf B ht0
      (integrable_exp_gaussianVectorAction ht1)
  rw [mgf_gaussianVectorAction_eq_pow] at hchernoff
  have hnonneg : 0 ≤ Real.exp (-t * B) * gaussianHalfSquareMgf t ^ T :=
    mul_nonneg (Real.exp_pos _).le (pow_nonneg
      (gaussianHalfSquareMgf_pos ht1).le T)
  have hprob_ne_top : gaussianActionTailProbability T B ≠ ∞ := by
    exact measure_ne_top _ _
  apply (ENNReal.toReal_le_toReal hprob_ne_top (by simp)).1
  change (standardGaussianVector T).real
      (gaussianActionTailEvent T B) ≤ _
  rw [ENNReal.toReal_ofReal hnonneg]
  exact hchernoff

/-! ## The geometric long-length-class majorant -/

/-- Chernoff majorant for the length class indexed by `n`: every class keeps
the base crossing cost, each extra class pays `c0`, and the Gaussian
dimension is `(K+n+1)T`. -/
def lengthClassChernoffMajorant
    (C t base c0 sigma : ℝ) (T K n : ℕ) : ℝ :=
  Real.exp (-t * ((base + (n : ℝ) * c0) / sigma ^ 2)) *
    C ^ ((K + n + 1) * T)

/-- The union of prefix-action tails for all length classes beyond the
exceptional budget `K`.  Class `n` has `(K+n+1)T` Gaussian coordinates and
must pay at least `n c0 / sigma²`. -/
def longLengthClassActionEvent
    (T K : ℕ) (base c0 sigma : ℝ) : Set GaussianNoisePath :=
  ⋃ n : ℕ,
    gaussianPrefixActionTailEvent ((K + n + 1) * T)
      ((base + (n : ℝ) * c0) / sigma ^ 2)

/-- The long-length-class event is measurable. -/
theorem measurableSet_longLengthClassActionEvent
    (T K : ℕ) (base c0 sigma : ℝ) :
    MeasurableSet (longLengthClassActionEvent T K base c0 sigma) := by
  exact MeasurableSet.iUnion fun n ↦
    measurableSet_gaussianPrefixActionTailEvent ((K + n + 1) * T)
      ((base + (n : ℝ) * c0) / sigma ^ 2)

/-- Countable subadditivity and the fixed-dimensional Chernoff estimate give
the dimension-explicit majorant for the entire long-length-class event. -/
theorem standardGaussianSequence_longLengthClassActionEvent_le
    (T K : ℕ) (base c0 sigma : ℝ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    standardGaussianSequence
        (longLengthClassActionEvent T K base c0 sigma) ≤
      ∑' n : ℕ, ENNReal.ofReal
        (lengthClassChernoffMajorant
          (gaussianHalfSquareMgf t) t base c0 sigma T K n) := by
  calc
    standardGaussianSequence
        (longLengthClassActionEvent T K base c0 sigma) ≤
        ∑' n : ℕ, standardGaussianSequence
          (gaussianPrefixActionTailEvent ((K + n + 1) * T)
            ((base + (n : ℝ) * c0) / sigma ^ 2)) := by
      exact measure_iUnion_le _
    _ = ∑' n : ℕ, gaussianActionTailProbability ((K + n + 1) * T)
          ((base + (n : ℝ) * c0) / sigma ^ 2) := by
      congr 1
      funext n
      exact standardGaussianSequence_gaussianPrefixActionTailEvent _ _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal
          (lengthClassChernoffMajorant
            (gaussianHalfSquareMgf t) t base c0 sigma T K n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      simpa only [lengthClassChernoffMajorant] using
        gaussianActionTailProbability_le_chernoff ((K + n + 1) * T)
          (B := (base + (n : ℝ) * c0) / sigma ^ 2) ht0 ht1

/-- The length-class majorant is a fixed prefactor times a geometric ratio to
the class index. -/
theorem lengthClassChernoffMajorant_eq
    (C t base c0 sigma : ℝ) (T K n : ℕ) :
    lengthClassChernoffMajorant C t base c0 sigma T K n =
      (Real.exp (-t * (base / sigma ^ 2)) * C ^ ((K + 1) * T)) *
        (Real.exp (-t * (c0 / sigma ^ 2)) * C ^ T) ^ n := by
  have hexp : Real.exp (-t * ((base + (n : ℝ) * c0) / sigma ^ 2)) =
      Real.exp (-t * (base / sigma ^ 2)) *
        Real.exp (-t * (c0 / sigma ^ 2)) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hdim : (K + n + 1) * T = (K + 1) * T + n * T := by
    ring
  rw [lengthClassChernoffMajorant, hexp, hdim, pow_add, pow_mul, mul_pow]
  ring

/-- Every length-class majorant is nonnegative when the one-coordinate MGF
base is nonnegative. -/
theorem lengthClassChernoffMajorant_nonneg
    {C : ℝ} (hC : 0 ≤ C) (t base c0 sigma : ℝ) (T K n : ℕ) :
    0 ≤ lengthClassChernoffMajorant C t base c0 sigma T K n := by
  unfold lengthClassChernoffMajorant
  exact mul_nonneg (Real.exp_pos _).le (pow_nonneg hC _)

/-- Below the one-class ratio threshold, the real-valued length-class
majorant is summable. -/
theorem summable_lengthClassChernoffMajorant
    {C t base c0 sigma : ℝ} (T K : ℕ)
    (hC : 0 ≤ C)
    (hratio : Real.exp (-t * (c0 / sigma ^ 2)) * C ^ T < 1) :
    Summable
      (fun n : ℕ ↦ lengthClassChernoffMajorant
        C t base c0 sigma T K n) := by
  let q : ℝ := Real.exp (-t * (c0 / sigma ^ 2)) * C ^ T
  have hq0 : 0 ≤ q :=
    mul_nonneg (Real.exp_pos _).le (pow_nonneg hC T)
  have hsum : Summable
      (fun n : ℕ ↦
        (Real.exp (-t * (base / sigma ^ 2)) * C ^ ((K + 1) * T)) *
          q ^ n) :=
    (summable_geometric_of_lt_one hq0 hratio).mul_left _
  exact hsum.congr fun n ↦
    (lengthClassChernoffMajorant_eq C t base c0 sigma T K n).symm

/-- When the one-class ratio is below one, the entire long-length tail is an
explicit geometric series. -/
theorem tsum_lengthClassChernoffMajorant
    {C t base c0 sigma : ℝ} (T K : ℕ)
    (hC : 0 ≤ C)
    (hratio : Real.exp (-t * (c0 / sigma ^ 2)) * C ^ T < 1) :
    ∑' n : ℕ, lengthClassChernoffMajorant C t base c0 sigma T K n =
      (Real.exp (-t * (base / sigma ^ 2)) * C ^ ((K + 1) * T)) *
        (1 - Real.exp (-t * (c0 / sigma ^ 2)) * C ^ T)⁻¹ := by
  let q : ℝ := Real.exp (-t * (c0 / sigma ^ 2)) * C ^ T
  have hq0 : 0 ≤ q :=
    mul_nonneg (Real.exp_pos _).le (pow_nonneg hC T)
  rw [tsum_congr fun n ↦ lengthClassChernoffMajorant_eq
    C t base c0 sigma T K n]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hratio]

/-- The infinite union of long length classes has the closed geometric
Chernoff bound.  In particular, its Arrhenius exponent retains `base`; the
dimension growth contributes only the displayed finite prefactor and
geometric denominator. -/
theorem standardGaussianSequence_longLengthClassActionEvent_le_geometric
    (T K : ℕ) (base c0 sigma : ℝ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hratio : Real.exp (-t * (c0 / sigma ^ 2)) *
      gaussianHalfSquareMgf t ^ T < 1) :
    standardGaussianSequence
        (longLengthClassActionEvent T K base c0 sigma) ≤
      ENNReal.ofReal
        ((Real.exp (-t * (base / sigma ^ 2)) *
            gaussianHalfSquareMgf t ^ ((K + 1) * T)) *
          (1 - Real.exp (-t * (c0 / sigma ^ 2)) *
            gaussianHalfSquareMgf t ^ T)⁻¹) := by
  let C := gaussianHalfSquareMgf t
  have hC : 0 ≤ C := (gaussianHalfSquareMgf_pos ht1).le
  have hsum := summable_lengthClassChernoffMajorant
    (C := C) (t := t) (base := base) (c0 := c0) (sigma := sigma)
    T K hC hratio
  calc
    standardGaussianSequence
        (longLengthClassActionEvent T K base c0 sigma) ≤
        ∑' n : ℕ, ENNReal.ofReal
          (lengthClassChernoffMajorant C t base c0 sigma T K n) :=
      standardGaussianSequence_longLengthClassActionEvent_le
        T K base c0 sigma ht0 ht1
    _ = ENNReal.ofReal
          (∑' n : ℕ, lengthClassChernoffMajorant
            C t base c0 sigma T K n) := by
      rw [ENNReal.ofReal_tsum_of_nonneg
        (fun n ↦ lengthClassChernoffMajorant_nonneg hC t base c0 sigma T K n)
        hsum]
    _ = ENNReal.ofReal
          ((Real.exp (-t * (base / sigma ^ 2)) *
              C ^ ((K + 1) * T)) *
            (1 - Real.exp (-t * (c0 / sigma ^ 2)) * C ^ T)⁻¹) := by
      rw [tsum_lengthClassChernoffMajorant T K hC hratio]

/-- The elementary activated factor tends to zero as positive noise tends to
zero. -/
theorem tendsto_exp_neg_const_div_sq_nhdsGT_zero
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun sigma : ℝ ↦ Real.exp (-a / sigma ^ 2))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
  have hsquare : Tendsto (fun sigma : ℝ ↦ sigma ^ 2)
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhdsWithin 0 (Ioi (0 : ℝ))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hcont : ContinuousAt (fun sigma : ℝ ↦ sigma ^ 2) 0 := by
        fun_prop
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with sigma hsigma
      exact sq_pos_of_pos (by simpa only [mem_Ioi] using hsigma)
  have hinv : Tendsto (fun sigma : ℝ ↦ (sigma ^ 2)⁻¹)
      (nhdsWithin 0 (Ioi (0 : ℝ))) atTop :=
    tendsto_inv_nhdsGT_zero.comp hsquare
  have hscaled : Tendsto (fun sigma : ℝ ↦ a * (sigma ^ 2)⁻¹)
      (nhdsWithin 0 (Ioi (0 : ℝ))) atTop := by
    simpa only [mul_comm] using hinv.atTop_mul_const ha
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscaled
  apply hexp.congr'
  filter_upwards with sigma
  simp only [Function.comp_apply, div_eq_mul_inv]
  congr 1
  ring

/-- Hence, for positive Chernoff and quiet-block charges, the geometric
length-class ratio is eventually below one half. -/
theorem eventually_lengthClass_ratio_lt_half
    {C t c0 : ℝ} (_hC : 0 ≤ C) (ht : 0 < t) (hc0 : 0 < c0)
    (T : ℕ) :
    ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      Real.exp (-t * (c0 / sigma ^ 2)) * C ^ T < 1 / 2 := by
  have ha : 0 < t * c0 := mul_pos ht hc0
  have hbase := tendsto_exp_neg_const_div_sq_nhdsGT_zero ha
  have hratio : Tendsto
      (fun sigma : ℝ ↦
        Real.exp (-(t * c0) / sigma ^ 2) * C ^ T)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
    simpa using hbase.mul_const (C ^ T)
  have heventually := (tendsto_order.1 hratio).2 (1 / 2 : ℝ) (by norm_num)
  filter_upwards [heventually] with sigma hsigma
  rw [show -t * (c0 / sigma ^ 2) =
      -(t * c0) / sigma ^ 2 by ring]
  exact hsigma

/-- Pointwise finite-prefactor bound once the one-class ratio is below one
half. -/
theorem standardGaussianSequence_longLengthClassActionEvent_le_two
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (T K : ℕ) (base c0 sigma : ℝ)
    (hhalf : Real.exp (-t * (c0 / sigma ^ 2)) *
      gaussianHalfSquareMgf t ^ T < 1 / 2) :
    standardGaussianSequence
        (longLengthClassActionEvent T K base c0 sigma) ≤
      ENNReal.ofReal
        ((Real.exp (-t * (base / sigma ^ 2)) *
            gaussianHalfSquareMgf t ^ ((K + 1) * T)) * 2) := by
  let C := gaussianHalfSquareMgf t
  have hC : 0 ≤ C := (gaussianHalfSquareMgf_pos ht1).le
  let q : ℝ := Real.exp (-t * (c0 / sigma ^ 2)) * C ^ T
  have hq0 : 0 ≤ q :=
    mul_nonneg (Real.exp_pos _).le (pow_nonneg hC T)
  have hratio : q < 1 := hhalf.trans (by norm_num)
  have hden : 0 < 1 - q := sub_pos.mpr hratio
  have hinv : (1 - q)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_comm₀ hden (by norm_num : (0 : ℝ) < 2)]
    norm_num
    linarith
  have hpref :
      0 ≤ Real.exp (-t * (base / sigma ^ 2)) * C ^ ((K + 1) * T) :=
    mul_nonneg (Real.exp_pos _).le (pow_nonneg hC _)
  refine (standardGaussianSequence_longLengthClassActionEvent_le_geometric
    T K base c0 sigma ht0 ht1 hratio).trans ?_
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left hinv hpref

/-- Extended-real logarithmic rate of the union of long action length
classes. -/
def longLengthClassActionLogRate
    (T K : ℕ) (base c0 sigma : ℝ) : EReal :=
  (sigma ^ 2 : ℝ) *
    ENNReal.log
      (standardGaussianSequence
        (longLengthClassActionEvent T K base c0 sigma))

/-- Once the geometric ratio is below one half, taking logarithms leaves the
base action plus a finite dimension-dependent prefactor. -/
theorem longLengthClassActionLogRate_le_chernoff
    {t sigma : ℝ} (hsigma : sigma ≠ 0) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (T K : ℕ) (base c0 : ℝ)
    (hhalf : Real.exp (-t * (c0 / sigma ^ 2)) *
      gaussianHalfSquareMgf t ^ T < 1 / 2) :
    longLengthClassActionLogRate T K base c0 sigma ≤
      ((-t * base + sigma ^ 2 * Real.log
        (gaussianHalfSquareMgf t ^ ((K + 1) * T) * 2) : ℝ) : EReal) := by
  let C : ℝ := gaussianHalfSquareMgf t
  let D : ℝ := C ^ ((K + 1) * T) * 2
  have hCpos : 0 < C := gaussianHalfSquareMgf_pos ht1
  have hDpos : 0 < D := by
    dsimp only [D]
    exact mul_pos (pow_pos hCpos _) (by norm_num)
  have hprob :=
    standardGaussianSequence_longLengthClassActionEvent_le_two
      ht0 ht1 T K base c0 sigma hhalf
  have hprob' : standardGaussianSequence
      (longLengthClassActionEvent T K base c0 sigma) ≤
        ENNReal.ofReal (Real.exp (-t * (base / sigma ^ 2)) * D) := by
    simpa only [D, C, mul_assoc] using hprob
  have hlog :
      ENNReal.log
          (standardGaussianSequence
            (longLengthClassActionEvent T K base c0 sigma)) ≤
        ENNReal.log
          (ENNReal.ofReal (Real.exp (-t * (base / sigma ^ 2)) * D)) :=
    ENNReal.logOrderIso.monotone hprob'
  have hrhs :
      ENNReal.log
          (ENNReal.ofReal (Real.exp (-t * (base / sigma ^ 2)) * D)) =
        ((-t * (base / sigma ^ 2) + Real.log D : ℝ) : EReal) := by
    rw [ENNReal.log_ofReal_of_pos (mul_pos (Real.exp_pos _) hDpos)]
    norm_cast
    rw [Real.log_mul (Real.exp_pos _).ne' hDpos.ne', Real.log_exp]
  have hmul := mul_le_mul_of_nonneg_left hlog
    (show (0 : EReal) ≤ (sigma ^ 2 : ℝ) by
      exact_mod_cast sq_nonneg sigma)
  rw [hrhs] at hmul
  change longLengthClassActionLogRate T K base c0 sigma ≤
    ((sigma ^ 2 : ℝ) : EReal) *
      ((-t * (base / sigma ^ 2) + Real.log D : ℝ) : EReal) at hmul
  have heq : ((sigma ^ 2 : ℝ) : EReal) *
        ((-t * (base / sigma ^ 2) + Real.log D : ℝ) : EReal) =
      ((-t * base + sigma ^ 2 * Real.log D : ℝ) : EReal) := by
    norm_cast
    field_simp [hsigma]
  simpa only [C, D] using hmul.trans_eq heq

/-- At fixed positive Chernoff parameter, the long-class finite prefactor
vanishes at the small-noise logarithmic scale. -/
theorem limsup_longLengthClassActionLogRate_le_chernoffParameter
    {t c0 : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hc0 : 0 < c0)
    (T K : ℕ) (base : ℝ) :
    limsup (fun sigma : ℝ ↦
        longLengthClassActionLogRate T K base c0 sigma)
        (nhdsWithin 0 (Ioi (0 : ℝ))) ≤
      ((-t * base : ℝ) : EReal) := by
  let C : ℝ := Real.log
    (gaussianHalfSquareMgf t ^ ((K + 1) * T) * 2)
  have hmgfNonneg : 0 ≤ gaussianHalfSquareMgf t :=
    (gaussianHalfSquareMgf_pos ht1).le
  have hratio := eventually_lengthClass_ratio_lt_half
    hmgfNonneg ht0 hc0 T
  have hpointwise : ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      longLengthClassActionLogRate T K base c0 sigma ≤
        ((-t * base + sigma ^ 2 * C : ℝ) : EReal) := by
    filter_upwards [self_mem_nhdsWithin, hratio] with sigma hsigma hhalf
    simpa only [C] using longLengthClassActionLogRate_le_chernoff
      hsigma.ne' ht0.le ht1 T K base c0 hhalf
  have hreal : Tendsto (fun sigma : ℝ ↦ -t * base + sigma ^ 2 * C)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds (-t * base)) := by
    have hcont : ContinuousAt
        (fun sigma : ℝ ↦ -t * base + sigma ^ 2 * C) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hereal : Tendsto
      (fun sigma : ℝ ↦ ((-t * base + sigma ^ 2 * C : ℝ) : EReal))
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds (((-t * base : ℝ) : EReal))) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hreal
  exact (limsup_le_limsup hpointwise).trans_eq hereal.limsup_eq

/-- The countable union of all long length classes has logarithmic rate at
most minus its base action.  The growing Gaussian dimension is therefore a
prefactor effect, not a loss in the Arrhenius exponent. -/
theorem limsup_longLengthClassActionLogRate_le
    {c0 : ℝ} (hc0 : 0 < c0) (T K : ℕ) (base : ℝ) :
    limsup (fun sigma : ℝ ↦
        longLengthClassActionLogRate T K base c0 sigma)
        (nhdsWithin 0 (Ioi (0 : ℝ))) ≤
      ((-base : ℝ) : EReal) := by
  let R : EReal := limsup (fun sigma : ℝ ↦
    longLengthClassActionLogRate T K base c0 sigma)
    (nhdsWithin 0 (Ioi (0 : ℝ)))
  let t : ℕ → ℝ := fun n ↦ 1 - 1 / (n + 2 : ℝ)
  have hparameter : ∀ n, R ≤ ((-t n * base : ℝ) : EReal) := by
    intro n
    have hdenPos : 0 < (n + 2 : ℝ) := by positivity
    have hdenGtOne : (1 : ℝ) < n + 2 := by
      have hn : (0 : ℝ) ≤ n := by positivity
      linarith
    have ht0n : 0 < t n := by
      dsimp only [t]
      have hone : 1 / (n + 2 : ℝ) < 1 :=
        (div_lt_one hdenPos).2 hdenGtOne
      linarith
    have ht1n : t n < 1 := by
      dsimp only [t]
      have : 0 < 1 / (n + 2 : ℝ) := div_pos one_pos hdenPos
      linarith
    simpa only [R] using
      limsup_longLengthClassActionLogRate_le_chernoffParameter
        ht0n ht1n hc0 T K base
  have hinvBase : Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) atTop
      (nhds (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hinv : Tendsto (fun n : ℕ ↦ 1 / (n + 2 : ℝ)) atTop
      (nhds (0 : ℝ)) := by
    convert hinvBase.comp (tendsto_add_atTop_nat 1) using 1
    funext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  have htendsto : Tendsto t atTop (nhds (1 : ℝ)) := by
    simpa only [t, sub_zero] using tendsto_const_nhds.sub hinv
  have hreal : Tendsto (fun n ↦ -t n * base) atTop (nhds (-base)) := by
    simpa using htendsto.neg.mul_const base
  have hereal : Tendsto (fun n ↦ ((-t n * base : ℝ) : EReal)) atTop
      (nhds (((-base : ℝ) : EReal))) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hreal
  have hclosed : ((-base : ℝ) : EReal) ∈ Ici R :=
    isClosed_Ici.mem_of_tendsto hereal (Eventually.of_forall hparameter)
  simpa only [R, mem_Ici] using hclosed

/-- For small positive noise, the geometric denominator is uniformly at
most two.  This is the finite-prefactor form used in the persistence
estimate; the only `sigma⁻²` exponential left is the base crossing rate. -/
theorem eventually_standardGaussianSequence_longLengthClassActionEvent_le
    {t c0 : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hc0 : 0 < c0)
    (T K : ℕ) (base : ℝ) :
    ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      standardGaussianSequence
          (longLengthClassActionEvent T K base c0 sigma) ≤
        ENNReal.ofReal
          ((Real.exp (-t * (base / sigma ^ 2)) *
              gaussianHalfSquareMgf t ^ ((K + 1) * T)) * 2) := by
  let C := gaussianHalfSquareMgf t
  have hC : 0 ≤ C := (gaussianHalfSquareMgf_pos ht1).le
  have heventually := eventually_lengthClass_ratio_lt_half hC ht0 hc0 T
  filter_upwards [heventually] with sigma hhalf
  exact standardGaussianSequence_longLengthClassActionEvent_le_two
    ht0.le ht1 T K base c0 sigma hhalf

#print axioms quiet_card_add_nonquiet_card
#print axioms sum_blockAdvance_range
#print axioms blockAdvance_nonneg
#print axioms nonquiet_card_mul_le_totalGrowth
#print axioms nonquiet_card_le
#print axioms sub_le_quiet_card
#print axioms controlBlockAction_nonneg
#print axioms gaussianVectorAction_shift_eq_controlIntervalAction
#print axioms controlIntervalAction_le_controlAction
#print axioms controlAction_shift_eq_controlIntervalAction
#print axioms controlIntervalAction_aligned_eq_controlBlockAction
#print axioms sum_controlBlockAction_range
#print axioms sum_controlBlockAction_subset_le
#print axioms quiet_card_mul_le_controlAction
#print axioms sub_mul_le_controlAction_of_quiet_charge
#print axioms controlSpacedWindowAction_le_controlBlockAction
#print axioms sum_controlSpacedWindowAction_subset_le
#print axioms spacedWindow_card_mul_le_controlAction
#print axioms calibratedHomeRectangle_subset_closedBall
#print axioms home_ball_gap_le_endpoint_dist
#print axioms exists_uniform_action_cost_of_avoiding_home
#print axioms exists_awaySaddle_avoiding_home_action_cost
#print axioms exists_awaySaddle_slidingWindow_action_cost
#print axioms exists_awaySaddle_spacedWindow_action_bound
#print axioms isCompact_characteristicFunnelStartSet
#print axioms exists_characteristicFunnel_avoiding_home_action_cost
#print axioms exists_caseC_to_characteristicFunnelStartSet_time
#print axioms exists_farPolicy_avoiding_home_action_cost
#print axioms exists_farPolicy_avoiding_home_block_action_cost
#print axioms exists_quietBlock_lingering_action_bound
#print axioms mgf_gaussianVectorAction_eq_pow
#print axioms gaussianHalfSquareMgf_pos
#print axioms continuous_gaussianVectorAction
#print axioms measurableSet_gaussianActionTailEvent
#print axioms measurableSet_gaussianPrefixActionTailEvent
#print axioms standardGaussianSequence_gaussianPrefixActionTailEvent
#print axioms gaussianActionTailProbability_le_chernoff
#print axioms measurableSet_longLengthClassActionEvent
#print axioms standardGaussianSequence_longLengthClassActionEvent_le
#print axioms lengthClassChernoffMajorant_eq
#print axioms lengthClassChernoffMajorant_nonneg
#print axioms summable_lengthClassChernoffMajorant
#print axioms tsum_lengthClassChernoffMajorant
#print axioms standardGaussianSequence_longLengthClassActionEvent_le_geometric
#print axioms tendsto_exp_neg_const_div_sq_nhdsGT_zero
#print axioms eventually_lengthClass_ratio_lt_half
#print axioms standardGaussianSequence_longLengthClassActionEvent_le_two
#print axioms longLengthClassActionLogRate_le_chernoff
#print axioms limsup_longLengthClassActionLogRate_le_chernoffParameter
#print axioms limsup_longLengthClassActionLogRate_le
#print axioms eventually_standardGaussianSequence_longLengthClassActionEvent_le

end

end CivicAlignment.PaperII
