/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.Convergence

/-!
# Paper II: global bistability for nonlinear stock laws

This file leaves the affine theorem intact and isolates the dynamical
properties that its affine stock recursion supplies automatically.  A
nonlinear stock law receives its own compact rectangle, continuity and order
hypotheses, and four quantitative difference bounds.  Strict diagonal-product
dominance then rules out southeast/northwest alternation exactly as in the
affine proof.  No convergence, attraction, or basin conclusion is assumed.
-/

namespace CivicAlignment.PaperII

open Filter Function Set Topology

noncomputable section

/-- A scalar nonlinear stock law together with its registered characteristic
and compact stock interval. -/
structure NonlinearStockLaw where
  step : ℝ → ℝ → ℝ
  characteristic : ℝ → ℝ
  stockLower : ℝ
  stockUpper : ℝ
  stockLower_le_stockUpper : stockLower ≤ stockUpper

/-- The simultaneous policy/nonlinear-stock map. -/
def nonlinearLoopMap (p : LoopParams) (law : NonlinearStockLaw)
    (x : LoopState) : LoopState :=
  (p.deferenceStep x.1 x.2, law.step x.1 x.2)

/-- The registered compact rectangle for a nonlinear stock law. -/
def nonlinearLoopBox (law : NonlinearStockLaw) : Set LoopState :=
  Icc (0 : ℝ) 1 ×ˢ Icc law.stockLower law.stockUpper

/-- A trajectory of the simultaneous nonlinear loop. -/
def IsNonlinearLoopTrajectory (p : LoopParams) (law : NonlinearStockLaw)
    (x : ℕ → LoopState) : Prop :=
  ∀ n, x (n + 1) = nonlinearLoopMap p law (x n)

/-- A fixed point of the nonlinear simultaneous loop. -/
def IsNonlinearLoopEquilibrium (p : LoopParams) (law : NonlinearStockLaw)
    (x : LoopState) : Prop :=
  nonlinearLoopMap p law x = x

/-- The three registered equilibrium locations. -/
def nonlinearCalibratedPoint (law : NonlinearStockLaw) : LoopState :=
  (0, law.characteristic 0)

def nonlinearSaddlePoint (law : NonlinearStockLaw) (βdagger : ℝ) : LoopState :=
  (βdagger, law.characteristic βdagger)

def nonlinearCapturedPoint (law : NonlinearStockLaw) : LoopState :=
  (1, law.characteristic 1)

/-- Structural hypotheses independent of the global convergence conclusion. -/
structure NonlinearLoopCoreAssumptions
    (p : LoopParams) (law : NonlinearStockLaw) : Prop where
  mapsTo : MapsTo (nonlinearLoopMap p law)
    (nonlinearLoopBox law) (nonlinearLoopBox law)
  continuous : Continuous (nonlinearLoopMap p law)
  monotoneOn : MonotoneOn (nonlinearLoopMap p law) (nonlinearLoopBox law)

/-- Quantitative difference bounds replacing the four affine coefficients in
`(SS⁺)`.  Each bound is pointwise checkable on the registered rectangle. -/
structure NonlinearCrossBounds (p : LoopParams) (law : NonlinearStockLaw) where
  policyDiagonalLower : ℝ
  policyStockUpper : ℝ
  stockPolicyUpper : ℝ
  stockDiagonalLower : ℝ
  policyStockUpper_pos : 0 < policyStockUpper
  stockDiagonalLower_pos : 0 < stockDiagonalLower
  crossProduct_lt :
    policyStockUpper * stockPolicyUpper <
      policyDiagonalLower * stockDiagonalLower
  southeast_policy_lower : ∀ {x y : LoopState},
    x ∈ nonlinearLoopBox law → y ∈ nonlinearLoopBox law →
    x.1 ≤ y.1 → y.2 ≤ x.2 →
    policyDiagonalLower * (y.1 - x.1) -
        policyStockUpper * (x.2 - y.2) ≤
      unclippedDeferenceInput p y.1 y.2 -
        unclippedDeferenceInput p x.1 x.2
  southeast_stock_upper : ∀ {x y : LoopState},
    x ∈ nonlinearLoopBox law → y ∈ nonlinearLoopBox law →
    x.1 ≤ y.1 → y.2 ≤ x.2 →
    law.step y.1 y.2 - law.step x.1 x.2 ≤
      stockPolicyUpper * (y.1 - x.1) -
        stockDiagonalLower * (x.2 - y.2)
  northwest_policy_upper : ∀ {x y : LoopState},
    x ∈ nonlinearLoopBox law → y ∈ nonlinearLoopBox law →
    y.1 ≤ x.1 → x.2 ≤ y.2 →
    unclippedDeferenceInput p y.1 y.2 -
        unclippedDeferenceInput p x.1 x.2 ≤
      -policyDiagonalLower * (x.1 - y.1) +
        policyStockUpper * (y.2 - x.2)
  northwest_stock_lower : ∀ {x y : LoopState},
    x ∈ nonlinearLoopBox law → y ∈ nonlinearLoopBox law →
    y.1 ≤ x.1 → x.2 ≤ y.2 →
    -stockPolicyUpper * (x.1 - y.1) +
        stockDiagonalLower * (y.2 - x.2) ≤
      law.step y.1 y.2 - law.step x.1 x.2

/-- Algebraic equilibrium information, analogous to the affine paper's
oriented threshold assumption rather than a global dynamical conclusion. -/
structure NonlinearEquilibriumCatalogue
    (p : LoopParams) (law : NonlinearStockLaw) where
  βdagger : ℝ
  βdagger_mem : βdagger ∈ Ioo (0 : ℝ) 1
  calibrated_mem : nonlinearCalibratedPoint law ∈ nonlinearLoopBox law
  saddle_mem : nonlinearSaddlePoint law βdagger ∈ nonlinearLoopBox law
  captured_mem : nonlinearCapturedPoint law ∈ nonlinearLoopBox law
  exactly_three : ∀ q ∈ nonlinearLoopBox law,
    IsNonlinearLoopEquilibrium p law q ↔
      q = nonlinearCalibratedPoint law ∨
      q = nonlinearSaddlePoint law βdagger ∨
      q = nonlinearCapturedPoint law
  characteristic_strictMono : StrictMonoOn law.characteristic (Icc (0 : ℝ) 1)

/-- Every nonlinear trajectory starting in the registered rectangle stays
there. -/
theorem nonlinearTrajectory_mem_box
    {p : LoopParams} {law : NonlinearStockLaw}
    (core : NonlinearLoopCoreAssumptions p law)
    {x : ℕ → LoopState} (traj : IsNonlinearLoopTrajectory p law x)
    (hx0 : x 0 ∈ nonlinearLoopBox law) :
    ∀ n, x n ∈ nonlinearLoopBox law := by
  intro n
  induction n with
  | zero => exact hx0
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by omega, traj n]
      exact core.mapsTo ih

/-- A componentwise increasing nonlinear step propagates under cooperativity. -/
theorem nonlinearTrajectory_tail_monotone_of_le
    {p : LoopParams} {law : NonlinearStockLaw}
    (core : NonlinearLoopCoreAssumptions p law)
    {x : ℕ → LoopState} (traj : IsNonlinearLoopTrajectory p law x)
    (hmem : ∀ n, x n ∈ nonlinearLoopBox law) {t : ℕ}
    (hstep : x t ≤ x (t + 1)) :
    Monotone (fun n ↦ x (n + t)) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => simpa [Nat.add_comm] using hstep
  | succ n ih =>
      have hmono := core.monotoneOn
        (hmem (n + t)) (hmem (n + 1 + t)) ih
      calc
        x (Nat.succ n + t) = nonlinearLoopMap p law (x (n + t)) := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using traj (n + t)
        _ ≤ nonlinearLoopMap p law (x (n + 1 + t)) := hmono
        _ = x (Nat.succ n + 1 + t) := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using (traj (n + 1 + t)).symm

/-- A componentwise decreasing nonlinear step propagates under cooperativity. -/
theorem nonlinearTrajectory_tail_antitone_of_ge
    {p : LoopParams} {law : NonlinearStockLaw}
    (core : NonlinearLoopCoreAssumptions p law)
    {x : ℕ → LoopState} (traj : IsNonlinearLoopTrajectory p law x)
    (hmem : ∀ n, x n ∈ nonlinearLoopBox law) {t : ℕ}
    (hstep : x (t + 1) ≤ x t) :
    Antitone (fun n ↦ x (n + t)) := by
  apply antitone_nat_of_succ_le
  intro n
  induction n with
  | zero => simpa [Nat.add_comm] using hstep
  | succ n ih =>
      have hmono := core.monotoneOn
        (hmem (n + 1 + t)) (hmem (n + t)) ih
      calc
        x (Nat.succ n + 1 + t) =
            nonlinearLoopMap p law (x (n + 1 + t)) := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using traj (n + 1 + t)
        _ ≤ nonlinearLoopMap p law (x (n + t)) := hmono
        _ = x (Nat.succ n + t) := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using (traj (n + t)).symm

/-- A monotone sequence in the nonlinear rectangle converges in it. -/
theorem monotone_sequence_tendsto_in_nonlinearLoopBox
    {law : NonlinearStockLaw} {x : ℕ → LoopState}
    (hmono : Monotone x) (hmem : ∀ n, x n ∈ nonlinearLoopBox law) :
    ∃ q ∈ nonlinearLoopBox law, Tendsto x atTop (𝓝 q) := by
  have hβmono : Monotone (fun n ↦ (x n).1) := fun _ _ h ↦ (hmono h).1
  have hDmono : Monotone (fun n ↦ (x n).2) := fun _ _ h ↦ (hmono h).2
  have hβbdd : BddAbove (range fun n ↦ (x n).1) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; exact (hmem n).1.2⟩
  have hDbdd : BddAbove (range fun n ↦ (x n).2) :=
    ⟨law.stockUpper, by rintro _ ⟨n, rfl⟩; exact (hmem n).2.2⟩
  let q : LoopState := (⨆ n, (x n).1, ⨆ n, (x n).2)
  have hlim : Tendsto x atTop (𝓝 q) := (Prod.tendsto_iff x q).2 ⟨
    by simpa only [q] using tendsto_atTop_ciSup hβmono hβbdd,
    by simpa only [q] using tendsto_atTop_ciSup hDmono hDbdd⟩
  have hclosed : IsClosed (nonlinearLoopBox law) :=
    isClosed_Icc.prod isClosed_Icc
  exact ⟨q, hclosed.mem_of_tendsto hlim (Eventually.of_forall hmem), hlim⟩

/-- An antitone sequence in the nonlinear rectangle converges in it. -/
theorem antitone_sequence_tendsto_in_nonlinearLoopBox
    {law : NonlinearStockLaw} {x : ℕ → LoopState}
    (hanti : Antitone x) (hmem : ∀ n, x n ∈ nonlinearLoopBox law) :
    ∃ q ∈ nonlinearLoopBox law, Tendsto x atTop (𝓝 q) := by
  have hβanti : Antitone (fun n ↦ (x n).1) := fun _ _ h ↦ (hanti h).1
  have hDanti : Antitone (fun n ↦ (x n).2) := fun _ _ h ↦ (hanti h).2
  have hβbdd : BddBelow (range fun n ↦ (x n).1) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact (hmem n).1.1⟩
  have hDbdd : BddBelow (range fun n ↦ (x n).2) :=
    ⟨law.stockLower, by rintro _ ⟨n, rfl⟩; exact (hmem n).2.1⟩
  let q : LoopState := (⨅ n, (x n).1, ⨅ n, (x n).2)
  have hlim : Tendsto x atTop (𝓝 q) := (Prod.tendsto_iff x q).2 ⟨
    by simpa only [q] using tendsto_atTop_ciInf hβanti hβbdd,
    by simpa only [q] using tendsto_atTop_ciInf hDanti hDbdd⟩
  have hclosed : IsClosed (nonlinearLoopBox law) :=
    isClosed_Icc.prod isClosed_Icc
  exact ⟨q, hclosed.mem_of_tendsto hlim (Eventually.of_forall hmem), hlim⟩

/-- A nonlinear trajectory limit is a fixed point. -/
theorem nonlinearTrajectory_limit_is_equilibrium
    {p : LoopParams} {law : NonlinearStockLaw}
    (core : NonlinearLoopCoreAssumptions p law)
    {x : ℕ → LoopState} (traj : IsNonlinearLoopTrajectory p law x)
    {q : LoopState} (hlim : Tendsto x atTop (𝓝 q)) :
    IsNonlinearLoopEquilibrium p law q := by
  have hshift : Tendsto (fun n ↦ x (n + 1)) atTop (𝓝 q) :=
    (tendsto_add_atTop_iff_nat 1).2 hlim
  have hmapToQ : Tendsto (fun n ↦ nonlinearLoopMap p law (x n))
      atTop (𝓝 q) := by
    apply hshift.congr'
    exact Eventually.of_forall fun n ↦ traj n
  have hmapToMap : Tendsto (fun n ↦ nonlinearLoopMap p law (x n))
      atTop (𝓝 (nonlinearLoopMap p law q)) :=
    (core.continuous.tendsto q).comp hlim
  exact tendsto_nhds_unique hmapToMap hmapToQ

/-- Under the nonlinear small-gain bounds, a southeast step cannot be followed
by a northwest step. -/
theorem nonlinear_no_southeast_to_northwest
    {p : LoopParams} {law : NonlinearStockLaw}
    (cross : NonlinearCrossBounds p law)
    {x y : LoopState} (hx : x ∈ nonlinearLoopBox law)
    (hy : y ∈ nonlinearLoopBox law) (hxy : Southeast x y) :
    ¬Northwest (nonlinearLoopMap p law x) (nonlinearLoopMap p law y) := by
  intro hnext
  have hinput : unclippedDeferenceInput p y.1 y.2 <
      unclippedDeferenceInput p x.1 x.2 := by
    by_contra hnot
    have hmono := LoopParams.monotone_clipUnit (not_lt.mp hnot)
    have hpolicy : (nonlinearLoopMap p law x).1 ≤
        (nonlinearLoopMap p law y).1 := by
      simpa only [nonlinearLoopMap, LoopParams.deferenceStep,
        unclippedDeferenceInput] using hmono
    exact (not_lt_of_ge hpolicy) hnext.1
  have hpolicyBound := cross.southeast_policy_lower
    hx hy hxy.1.le hxy.2.le
  have hpolicy : cross.policyDiagonalLower * (y.1 - x.1) <
      cross.policyStockUpper * (x.2 - y.2) := by
    nlinarith
  have hstockBound := cross.southeast_stock_upper
    hx hy hxy.1.le hxy.2.le
  have hstock : cross.stockDiagonalLower * (x.2 - y.2) <
      cross.stockPolicyUpper * (y.1 - x.1) := by
    have hnextStock : 0 < law.step y.1 y.2 - law.step x.1 x.2 := by
      simpa only [nonlinearLoopMap] using sub_pos.mpr hnext.2
    nlinarith
  exact cross_inequalities_impossible (sub_pos.mpr hxy.1)
    (sub_pos.mpr hxy.2) cross.policyStockUpper_pos
    cross.stockDiagonalLower_pos cross.crossProduct_lt hpolicy hstock

/-- Under the nonlinear small-gain bounds, a northwest step cannot be followed
by a southeast step. -/
theorem nonlinear_no_northwest_to_southeast
    {p : LoopParams} {law : NonlinearStockLaw}
    (cross : NonlinearCrossBounds p law)
    {x y : LoopState} (hx : x ∈ nonlinearLoopBox law)
    (hy : y ∈ nonlinearLoopBox law) (hxy : Northwest x y) :
    ¬Southeast (nonlinearLoopMap p law x) (nonlinearLoopMap p law y) := by
  intro hnext
  have hinput : unclippedDeferenceInput p x.1 x.2 <
      unclippedDeferenceInput p y.1 y.2 := by
    by_contra hnot
    have hmono := LoopParams.monotone_clipUnit (not_lt.mp hnot)
    have hpolicy : (nonlinearLoopMap p law y).1 ≤
        (nonlinearLoopMap p law x).1 := by
      simpa only [nonlinearLoopMap, LoopParams.deferenceStep,
        unclippedDeferenceInput] using hmono
    exact (not_lt_of_ge hpolicy) hnext.1
  have hpolicyBound := cross.northwest_policy_upper
    hx hy hxy.1.le hxy.2.le
  have hpolicy : cross.policyDiagonalLower * (x.1 - y.1) <
      cross.policyStockUpper * (y.2 - x.2) := by
    nlinarith
  have hstockBound := cross.northwest_stock_lower
    hx hy hxy.1.le hxy.2.le
  have hstock : cross.stockDiagonalLower * (y.2 - x.2) <
      cross.stockPolicyUpper * (x.1 - y.1) := by
    have hnextStock : law.step y.1 y.2 - law.step x.1 x.2 < 0 := by
      simpa only [nonlinearLoopMap] using sub_neg.mpr hnext.2
    nlinarith
  exact cross_inequalities_impossible (sub_pos.mpr hxy.1)
    (sub_pos.mpr hxy.2) cross.policyStockUpper_pos
    cross.stockDiagonalLower_pos cross.crossProduct_lt hpolicy hstock

/-- If no nonlinear trajectory step is comparable, its first mixed direction
persists forever. -/
theorem nonlinearTrajectory_mixed_direction_persists
    {p : LoopParams} {law : NonlinearStockLaw}
    (cross : NonlinearCrossBounds p law)
    {x : ℕ → LoopState} (traj : IsNonlinearLoopTrajectory p law x)
    (hmem : ∀ n, x n ∈ nonlinearLoopBox law)
    (hnone : ∀ n, ¬(x n ≤ x (n + 1) ∨ x (n + 1) ≤ x n)) :
    (Southeast (x 0) (x 1) → ∀ n, Southeast (x n) (x (n + 1))) ∧
      (Northwest (x 0) (x 1) → ∀ n, Northwest (x n) (x (n + 1))) := by
  constructor
  · intro hfirst n
    induction n with
    | zero => simpa using hfirst
    | succ n ih =>
        rcases southeast_or_northwest_of_not_comparable (hnone (n + 1)) with h | h
        · simpa [Nat.succ_eq_add_one] using h
        · have hforbidden := nonlinear_no_southeast_to_northwest cross
            (hmem n) (hmem (n + 1)) ih
          have hmapped : Northwest
              (nonlinearLoopMap p law (x n))
              (nonlinearLoopMap p law (x (n + 1))) := by
            simpa [traj n, traj (n + 1), Nat.succ_eq_add_one,
              Nat.add_assoc] using h
          exact (hforbidden hmapped).elim
  · intro hfirst n
    induction n with
    | zero => simpa using hfirst
    | succ n ih =>
        rcases southeast_or_northwest_of_not_comparable (hnone (n + 1)) with h | h
        · have hforbidden := nonlinear_no_northwest_to_southeast cross
            (hmem n) (hmem (n + 1)) ih
          have hmapped : Southeast
              (nonlinearLoopMap p law (x n))
              (nonlinearLoopMap p law (x (n + 1))) := by
            simpa [traj n, traj (n + 1), Nat.succ_eq_add_one,
              Nat.add_assoc] using h
          exact (hforbidden hmapped).elim
        · simpa [Nat.succ_eq_add_one] using h

/-- An all-southeast nonlinear trajectory converges in the registered box. -/
theorem nonlinearSoutheastTrajectory_tendsto
    {law : NonlinearStockLaw} {x : ℕ → LoopState}
    (hmem : ∀ n, x n ∈ nonlinearLoopBox law)
    (hstep : ∀ n, Southeast (x n) (x (n + 1))) :
    ∃ q ∈ nonlinearLoopBox law, Tendsto x atTop (𝓝 q) := by
  have hβmono : Monotone (fun n ↦ (x n).1) :=
    monotone_nat_of_le_succ fun n ↦ (hstep n).1.le
  have hDanti : Antitone (fun n ↦ (x n).2) :=
    antitone_nat_of_succ_le fun n ↦ (hstep n).2.le
  have hβbdd : BddAbove (range fun n ↦ (x n).1) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; exact (hmem n).1.2⟩
  have hDbdd : BddBelow (range fun n ↦ (x n).2) :=
    ⟨law.stockLower, by rintro _ ⟨n, rfl⟩; exact (hmem n).2.1⟩
  let q : LoopState := (⨆ n, (x n).1, ⨅ n, (x n).2)
  have hlim : Tendsto x atTop (𝓝 q) := (Prod.tendsto_iff x q).2 ⟨
    by simpa only [q] using tendsto_atTop_ciSup hβmono hβbdd,
    by simpa only [q] using tendsto_atTop_ciInf hDanti hDbdd⟩
  have hclosed : IsClosed (nonlinearLoopBox law) :=
    isClosed_Icc.prod isClosed_Icc
  exact ⟨q, hclosed.mem_of_tendsto hlim (Eventually.of_forall hmem), hlim⟩

/-- An all-northwest nonlinear trajectory converges in the registered box. -/
theorem nonlinearNorthwestTrajectory_tendsto
    {law : NonlinearStockLaw} {x : ℕ → LoopState}
    (hmem : ∀ n, x n ∈ nonlinearLoopBox law)
    (hstep : ∀ n, Northwest (x n) (x (n + 1))) :
    ∃ q ∈ nonlinearLoopBox law, Tendsto x atTop (𝓝 q) := by
  have hβanti : Antitone (fun n ↦ (x n).1) :=
    antitone_nat_of_succ_le fun n ↦ (hstep n).1.le
  have hDmono : Monotone (fun n ↦ (x n).2) :=
    monotone_nat_of_le_succ fun n ↦ (hstep n).2.le
  have hβbdd : BddBelow (range fun n ↦ (x n).1) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact (hmem n).1.1⟩
  have hDbdd : BddAbove (range fun n ↦ (x n).2) :=
    ⟨law.stockUpper, by rintro _ ⟨n, rfl⟩; exact (hmem n).2.2⟩
  let q : LoopState := (⨅ n, (x n).1, ⨆ n, (x n).2)
  have hlim : Tendsto x atTop (𝓝 q) := (Prod.tendsto_iff x q).2 ⟨
    by simpa only [q] using tendsto_atTop_ciInf hβanti hβbdd,
    by simpa only [q] using tendsto_atTop_ciSup hDmono hDbdd⟩
  have hclosed : IsClosed (nonlinearLoopBox law) :=
    isClosed_Icc.prod isClosed_Icc
  exact ⟨q, hclosed.mem_of_tendsto hlim (Eventually.of_forall hmem), hlim⟩

/-- Once a nonlinear trajectory has a comparable step, cooperativity makes
its corresponding tail monotone or antitone.  Compactness and continuity then
give convergence of the full trajectory to a fixed point. -/
theorem nonlinearComparableStep_convergesToEquilibrium
    {p : LoopParams} {law : NonlinearStockLaw}
    (core : NonlinearLoopCoreAssumptions p law)
    {x : ℕ → LoopState} (traj : IsNonlinearLoopTrajectory p law x)
    (hx0 : x 0 ∈ nonlinearLoopBox law) {t : ℕ}
    (hcomparable : x t ≤ x (t + 1) ∨ x (t + 1) ≤ x t) :
    ∃ q ∈ nonlinearLoopBox law, Tendsto x atTop (𝓝 q) ∧
      IsNonlinearLoopEquilibrium p law q := by
  have hmem := nonlinearTrajectory_mem_box core traj hx0
  rcases hcomparable with hstep | hstep
  · have hmono := nonlinearTrajectory_tail_monotone_of_le
      core traj hmem hstep
    obtain ⟨q, hq, hlim⟩ :=
      monotone_sequence_tendsto_in_nonlinearLoopBox hmono
        (fun n ↦ hmem (n + t))
    have hfull : Tendsto x atTop (𝓝 q) :=
      (tendsto_add_atTop_iff_nat t).1 hlim
    exact ⟨q, hq, hfull,
      nonlinearTrajectory_limit_is_equilibrium core traj hfull⟩
  · have hanti := nonlinearTrajectory_tail_antitone_of_ge
      core traj hmem hstep
    obtain ⟨q, hq, hlim⟩ :=
      antitone_sequence_tendsto_in_nonlinearLoopBox hanti
        (fun n ↦ hmem (n + t))
    have hfull : Tendsto x atTop (𝓝 q) :=
      (tendsto_add_atTop_iff_nat t).1 hlim
    exact ⟨q, hq, hfull,
      nonlinearTrajectory_limit_is_equilibrium core traj hfull⟩

/-- Core nonlinear global-bistability conclusions. -/
structure NonlinearGlobalBistabilityConclusions
    (p : LoopParams) (law : NonlinearStockLaw)
    (catalogue : NonlinearEquilibriumCatalogue p law) : Prop where
  ordered_equilibria :
    nonlinearCalibratedPoint law < nonlinearSaddlePoint law catalogue.βdagger ∧
      nonlinearSaddlePoint law catalogue.βdagger < nonlinearCapturedPoint law
  monotone_step : ∀ {x : ℕ → LoopState},
    IsNonlinearLoopTrajectory p law x →
    x 0 ∈ nonlinearLoopBox law → ∀ {t : ℕ},
    (x t ≤ x (t + 1) ∨ x (t + 1) ≤ x t) →
    ∃ q ∈ nonlinearLoopBox law, Tendsto x atTop (𝓝 q) ∧
      IsNonlinearLoopEquilibrium p law q
  global_convergence : ∀ {x : ℕ → LoopState},
    IsNonlinearLoopTrajectory p law x →
    x 0 ∈ nonlinearLoopBox law →
    ∃ q ∈ nonlinearLoopBox law, Tendsto x atTop (𝓝 q) ∧
      (q = nonlinearCalibratedPoint law ∨
        q = nonlinearSaddlePoint law catalogue.βdagger ∨
        q = nonlinearCapturedPoint law)

/-- Global nonlinear robustness theorem: independently checkable rectangle,
cooperativity, continuity, cross bounds, and algebraic equilibrium catalogue
imply ordered three-equilibrium global bistability. -/
theorem nonlinear_global_bistability
    {p : LoopParams} {law : NonlinearStockLaw}
    (core : NonlinearLoopCoreAssumptions p law)
    (cross : NonlinearCrossBounds p law)
    (catalogue : NonlinearEquilibriumCatalogue p law) :
    NonlinearGlobalBistabilityConclusions p law catalogue := by
  have hzero : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hone : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  have hdagger : catalogue.βdagger ∈ Icc (0 : ℝ) 1 :=
    ⟨catalogue.βdagger_mem.1.le, catalogue.βdagger_mem.2.le⟩
  have hDzero : law.characteristic 0 <
      law.characteristic catalogue.βdagger :=
    catalogue.characteristic_strictMono hzero hdagger
      catalogue.βdagger_mem.1
  have hDone : law.characteristic catalogue.βdagger <
      law.characteristic 1 :=
    catalogue.characteristic_strictMono hdagger hone
      catalogue.βdagger_mem.2
  have hordered :
      nonlinearCalibratedPoint law < nonlinearSaddlePoint law catalogue.βdagger ∧
        nonlinearSaddlePoint law catalogue.βdagger < nonlinearCapturedPoint law := by
    constructor
    · exact Prod.mk_lt_mk.2 <| Or.inl
        ⟨catalogue.βdagger_mem.1, hDzero.le⟩
    · exact Prod.mk_lt_mk.2 <| Or.inl
        ⟨catalogue.βdagger_mem.2, hDone.le⟩
  refine ⟨hordered, ?_, ?_⟩
  · intro x traj hx0 t hcomparable
    exact nonlinearComparableStep_convergesToEquilibrium
      core traj hx0 hcomparable
  · intro x traj hx0
    have hmem := nonlinearTrajectory_mem_box core traj hx0
    by_cases hcomparable : ∃ t,
        x t ≤ x (t + 1) ∨ x (t + 1) ≤ x t
    · obtain ⟨t, ht⟩ := hcomparable
      obtain ⟨q, hq, hlim, heq⟩ :=
        nonlinearComparableStep_convergesToEquilibrium core traj hx0 ht
      exact ⟨q, hq, hlim, (catalogue.exactly_three q hq).1 heq⟩
    · have hnone : ∀ n,
          ¬(x n ≤ x (n + 1) ∨ x (n + 1) ≤ x n) := by
        intro n hn
        exact hcomparable ⟨n, hn⟩
      have hpersist := nonlinearTrajectory_mixed_direction_persists
        cross traj hmem hnone
      rcases southeast_or_northwest_of_not_comparable (hnone 0) with hfirst | hfirst
      · obtain ⟨q, hq, hlim⟩ := nonlinearSoutheastTrajectory_tendsto
          hmem (hpersist.1 hfirst)
        have heq := nonlinearTrajectory_limit_is_equilibrium core traj hlim
        exact ⟨q, hq, hlim, (catalogue.exactly_three q hq).1 heq⟩
      · obtain ⟨q, hq, hlim⟩ := nonlinearNorthwestTrajectory_tendsto
          hmem (hpersist.2 hfirst)
        have heq := nonlinearTrajectory_limit_is_equilibrium core traj hlim
        exact ⟨q, hq, hlim, (catalogue.exactly_three q hq).1 heq⟩

#print axioms nonlinearTrajectory_mem_box
#print axioms nonlinearTrajectory_limit_is_equilibrium
#print axioms nonlinear_no_southeast_to_northwest
#print axioms nonlinear_no_northwest_to_southeast
#print axioms nonlinear_global_bistability

end

end CivicAlignment.PaperII
