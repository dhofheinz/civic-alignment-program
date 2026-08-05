/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.Hysteresis

/-!
# Paper II: corner attractors and basin topology

This file completes the topological clauses of `thm:bistable` that sit above
the fixed-point, spectrum, and convergence results in
`BistabilityTheorem.lean` and `Convergence.lean`.
-/

namespace CivicAlignment.PaperII

open Filter Function Set Topology

noncomputable section

/-! ## The unweighted map as civic weight zero -/

/-- The civic-weighted map at weight zero is definitionally the original
Paper II loop map after unfolding the two controller inputs. -/
theorem civicWeightedLoopMap_zero (p : LoopParams) (x : LoopState) :
    civicWeightedLoopMap p 0 x = p.loopMap x := by
  simp only [civicWeightedLoopMap, civicWeightedDeferenceStep,
    civicWeightedInput, civicWeightedGradient, zero_mul, sub_zero,
    LoopParams.loopMap, LoopParams.deferenceStep]

/-- Every ordinary loop trajectory is the zero-weight civic trajectory. -/
theorem IsLoopTrajectory.toCivicWeightedZero {p : LoopParams}
    {x : ℕ → LoopState} (traj : IsLoopTrajectory p x) :
    IsCivicWeightedTrajectory p 0 x := by
  intro n
  rw [traj n, civicWeightedLoopMap_zero]

/-- Every ordinary loop trajectory is also a zero-valued scheduled civic
trajectory. -/
theorem IsLoopTrajectory.toCivicWeightedZeroSchedule {p : LoopParams}
    {x : ℕ → LoopState} (traj : IsLoopTrajectory p x) :
    IsCivicWeightedScheduleTrajectory p (fun _ ↦ 0) x := by
  intro n
  rw [traj n, civicWeightedLoopMap_zero]

/-! ## Corner attractors -/

/-- The calibrated corner attracts a neighborhood in the invariant state box.
The same neighborhood in fact works for arbitrary nonnegative civic-weight
schedules, but this specialization is the literal unweighted clause of
`thm:bistable`. -/
theorem calibratedPoint_localAttraction {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (threshold : ThresholdAssumption p) :
    ∃ N : Set LoopState, N ∈ 𝓝 (calibratedPoint p) ∧
      ∀ {x : ℕ → LoopState}, IsLoopTrajectory p x →
        x 0 ∈ absorbingBox p → x 0 ∈ N →
        Tendsto x atTop (𝓝 (calibratedPoint p)) := by
  refine ⟨calibratedPreventionNeighborhood p threshold,
    calibratedPreventionNeighborhood_mem_nhds model threshold, ?_⟩
  intro x traj hx₀ hnear
  exact civicWeighted_prevention_uniform_attraction model ss threshold
    (fun _ ↦ le_rfl) traj.toCivicWeightedZeroSchedule hx₀ hnear

/-- The captured corner attracts a neighborhood in the invariant state box. -/
theorem capturedPoint_localAttraction {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (threshold : ThresholdAssumption p) :
    ∃ N : Set LoopState, N ∈ 𝓝 (capturedPoint p) ∧
      ∀ {x : ℕ → LoopState}, IsLoopTrajectory p x →
        x 0 ∈ absorbingBox p → x 0 ∈ N →
        Tendsto x atTop (𝓝 (capturedPoint p)) := by
  obtain ⟨N, hN, hattract⟩ := civicWeighted_captured_local_attraction
    model ss (show (0 : ℝ) ≤ 0 by norm_num) (cureThreshold_pos model threshold)
  refine ⟨N, hN, ?_⟩
  intro x traj hx₀ hxN
  exact hattract traj.toCivicWeightedZero hx₀ hxN

/-- Paper II, Theorem 3.14(b) (`thm:bistable`), `civic_drift.tex:237`:
both clipped corners have basin neighborhoods in `B`. -/
theorem bistability_cornerAttractors {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (threshold : ThresholdAssumption p) :
    (∃ N : Set LoopState, N ∈ 𝓝 (calibratedPoint p) ∧
      ∀ {x : ℕ → LoopState}, IsLoopTrajectory p x →
        x 0 ∈ absorbingBox p → x 0 ∈ N →
        Tendsto x atTop (𝓝 (calibratedPoint p))) ∧
    (∃ N : Set LoopState, N ∈ 𝓝 (capturedPoint p) ∧
      ∀ {x : ℕ → LoopState}, IsLoopTrajectory p x →
        x 0 ∈ absorbingBox p → x 0 ∈ N →
        Tendsto x atTop (𝓝 (capturedPoint p))) :=
  ⟨calibratedPoint_localAttraction model ss threshold,
    capturedPoint_localAttraction model ss threshold⟩

/-! ## Canonical orbits and relative basins -/

/-- The canonical forward orbit of the unweighted Paper II loop. -/
def loopOrbit (p : LoopParams) (x₀ : LoopState) (n : ℕ) : LoopState :=
  (p.loopMap^[n]) x₀

/-- The canonical orbit obeys the simultaneous loop recursion. -/
theorem loopOrbit_isTrajectory (p : LoopParams) (x₀ : LoopState) :
    IsLoopTrajectory p (loopOrbit p x₀) := by
  intro n
  simp only [loopOrbit, Function.iterate_succ_apply']

/-- Every canonical orbit started in `B` remains in `B`. -/
theorem loopOrbit_mem_absorbingBox {p : LoopParams}
    (model : DriftModelAssumptions p) {x₀ : LoopState}
    (hx₀ : x₀ ∈ absorbingBox p) (n : ℕ) :
    loopOrbit p x₀ n ∈ absorbingBox p :=
  trajectory_mem_absorbingBox model (loopOrbit_isTrajectory p x₀) hx₀ n

/-- The invariant box, regarded as a state space with its relative topology. -/
abbrev LoopBox (p : LoopParams) := {x : LoopState // x ∈ absorbingBox p}

/-- The loop map restricted to its forward-invariant box. -/
def loopMapOnBox (p : LoopParams) (model : DriftModelAssumptions p) :
    LoopBox p → LoopBox p := fun x ↦
  ⟨p.loopMap x.1, invariantBox model x.2⟩

/-- The basin in `B` of a specified ambient-state limit. -/
def loopBasinInBox (p : LoopParams) (q : LoopState) : Set (LoopBox p) :=
  {x | Tendsto (loopOrbit p x.1) atTop (𝓝 q)}

/-- The stable set `Γ` of the interior saddle, relative to `B`. -/
def saddleStableSetInBox (p : LoopParams)
    (threshold : ThresholdAssumption p) : Set (LoopBox p) :=
  loopBasinInBox p (saddlePoint p threshold)

/-- The same saddle stable set as an ambient subset of the policy--stock
plane.  Keeping the box condition explicit lets the local smoothness claim be
stated in the normed vector space `ℝ × ℝ`, rather than on a subtype with no
vector-space structure. -/
def ambientSaddleStableSet (p : LoopParams)
    (threshold : ThresholdAssumption p) : Set LoopState :=
  {x | x ∈ absorbingBox p ∧
    Tendsto (loopOrbit p x) atTop (𝓝 (saddlePoint p threshold))}

/-- A precise reading of “near `q`, `s` is a `C¹` decreasing arc.”  The local
piece is the image of an injective `C¹` parametrization whose policy coordinate
strictly increases and whose stock coordinate strictly decreases. -/
def IsLocalC1DecreasingArcAt (s : Set LoopState) (q : LoopState) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → LoopState, ∃ V : Set LoopState,
    IsOpen V ∧ q ∈ V ∧
      ContDiffOn ℝ 1 γ (Ioo (-ε) ε) ∧
      γ 0 = q ∧
      InjOn γ (Ioo (-ε) ε) ∧
      StrictMonoOn (fun t ↦ (γ t).1) (Ioo (-ε) ε) ∧
      StrictAntiOn (fun t ↦ (γ t).2) (Ioo (-ε) ε) ∧
      s ∩ V = γ '' Ioo (-ε) ε

/-- Restricting a continuous loop iterate to `B` remains continuous. -/
theorem continuous_loopIterateOnBox (p : LoopParams) (n : ℕ) :
    Continuous (fun x : LoopBox p ↦ loopOrbit p x.1 n) := by
  exact ((continuous_loopMap p).iterate n).comp continuous_subtype_val

/-- Starting the orbit at its `n`th state gives its `n`-shifted tail. -/
theorem loopOrbit_from_iterate (p : LoopParams) (x₀ : LoopState) (n k : ℕ) :
    loopOrbit p (loopOrbit p x₀ n) k = loopOrbit p x₀ (k + n) := by
  simp only [loopOrbit, Function.iterate_add_apply]

/-- Convergence of a canonical orbit is unchanged by deleting a finite prefix. -/
theorem loopOrbit_tendsto_iff_tail (p : LoopParams) (x₀ q : LoopState)
    (n : ℕ) :
    Tendsto (loopOrbit p (loopOrbit p x₀ n)) atTop (𝓝 q) ↔
      Tendsto (loopOrbit p x₀) atTop (𝓝 q) := by
  have hfun : loopOrbit p (loopOrbit p x₀ n) =
      fun k ↦ loopOrbit p x₀ (k + n) := by
    funext k
    exact loopOrbit_from_iterate p x₀ n k
  rw [hfun]
  exact tendsto_add_atTop_iff_nat n

/-- A basin in `B` is open whenever its limit has a trapping neighborhood
for all trajectories started in `B`. -/
theorem loopBasinInBox_isOpen_of_attractingNeighborhood {p : LoopParams}
    (model : DriftModelAssumptions p) {q : LoopState} {N : Set LoopState}
    (hN : N ∈ 𝓝 q)
    (hattract : ∀ {x : ℕ → LoopState}, IsLoopTrajectory p x →
      x 0 ∈ absorbingBox p → x 0 ∈ N → Tendsto x atTop (𝓝 q)) :
    IsOpen (loopBasinInBox p q) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨U, hUN, hUopen, hqU⟩ := mem_nhds_iff.mp hN
  have hevent : ∀ᶠ n in atTop, loopOrbit p x.1 n ∈ U :=
    hx (hUopen.mem_nhds hqU)
  obtain ⟨n, hn⟩ := hevent.exists
  let V : Set (LoopBox p) :=
    {y | loopOrbit p y.1 n ∈ U}
  have hVopen : IsOpen V := by
    exact hUopen.preimage (continuous_loopIterateOnBox p n)
  have hxV : x ∈ V := hn
  refine mem_of_superset (hVopen.mem_nhds hxV) ?_
  intro y hy
  have htail := hattract (loopOrbit_isTrajectory p (loopOrbit p y.1 n))
    (loopOrbit_mem_absorbingBox model y.2 n) (hUN hy)
  exact (loopOrbit_tendsto_iff_tail p y.1 q n).mp htail

/-- The calibrated basin is open in the relative topology of `B`. -/
theorem calibratedBasinInBox_isOpen {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (threshold : ThresholdAssumption p) :
    IsOpen (loopBasinInBox p (calibratedPoint p)) := by
  obtain ⟨N, hN, hattract⟩ := calibratedPoint_localAttraction model ss threshold
  exact loopBasinInBox_isOpen_of_attractingNeighborhood model hN hattract

/-- The captured basin is open in the relative topology of `B`. -/
theorem capturedBasinInBox_isOpen {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (threshold : ThresholdAssumption p) :
    IsOpen (loopBasinInBox p (capturedPoint p)) := by
  obtain ⟨N, hN, hattract⟩ := capturedPoint_localAttraction model ss threshold
  exact loopBasinInBox_isOpen_of_attractingNeighborhood model hN hattract

/-- Under `(SS⁺)`, every point of `B` belongs to exactly one of the three
candidate basins before uniqueness is imposed. -/
theorem mem_calibrated_or_saddle_or_captured_basin {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) (x : LoopBox p) :
    x ∈ loopBasinInBox p (calibratedPoint p) ∨
      x ∈ saddleStableSetInBox p threshold ∨
      x ∈ loopBasinInBox p (capturedPoint p) := by
  obtain ⟨q, _hq, hlim, hq⟩ :=
    bistability_globalConvergence_of_convergentStep model ssplus threshold
      (loopOrbit_isTrajectory p x.1) x.2
  rcases hq with rfl | rfl | rfl
  · left
    change Tendsto (loopOrbit p x.1) atTop (𝓝 (calibratedPoint p))
    exact hlim
  · right; left
    change Tendsto (loopOrbit p x.1) atTop (𝓝 (saddlePoint p threshold))
    exact hlim
  · right; right
    change Tendsto (loopOrbit p x.1) atTop (𝓝 (capturedPoint p))
    exact hlim

/-- No orbit can converge to two distinct ambient states. -/
theorem loopBasinInBox_disjoint_of_ne {p : LoopParams} {q₁ q₂ : LoopState}
    (hne : q₁ ≠ q₂) :
    Disjoint (loopBasinInBox p q₁) (loopBasinInBox p q₂) := by
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  change Tendsto (loopOrbit p x.1) atTop (𝓝 q₁) at hx₁
  change Tendsto (loopOrbit p x.1) atTop (𝓝 q₂) at hx₂
  exact hne (tendsto_nhds_unique hx₁ hx₂)

/-- The calibrated and saddle points are distinct. -/
theorem calibratedPoint_ne_saddlePoint {p : LoopParams}
    (threshold : ThresholdAssumption p) :
    calibratedPoint p ≠ saddlePoint p threshold := by
  intro h
  have := congrArg Prod.fst h
  simp only [calibratedPoint, saddlePoint] at this
  linarith [threshold.βdagger_mem.1]

/-- The saddle and captured points are distinct. -/
theorem saddlePoint_ne_capturedPoint {p : LoopParams}
    (threshold : ThresholdAssumption p) :
    saddlePoint p threshold ≠ capturedPoint p := by
  intro h
  have := congrArg Prod.fst h
  simp only [saddlePoint, capturedPoint] at this
  linarith [threshold.βdagger_mem.2]

/-- The calibrated and captured points are distinct. -/
theorem calibratedPoint_ne_capturedPoint (p : LoopParams) :
    calibratedPoint p ≠ capturedPoint p := by
  intro h
  have := congrArg Prod.fst h
  simp only [calibratedPoint, capturedPoint] at this
  norm_num at this

/-- The three basins in `B` are pairwise disjoint. -/
theorem bistableBasins_pairwiseDisjoint {p : LoopParams}
    (threshold : ThresholdAssumption p) :
    Disjoint (loopBasinInBox p (calibratedPoint p))
        (saddleStableSetInBox p threshold) ∧
      Disjoint (loopBasinInBox p (calibratedPoint p))
        (loopBasinInBox p (capturedPoint p)) ∧
      Disjoint (saddleStableSetInBox p threshold)
        (loopBasinInBox p (capturedPoint p)) := by
  simp only [saddleStableSetInBox]
  exact ⟨loopBasinInBox_disjoint_of_ne (calibratedPoint_ne_saddlePoint threshold),
    loopBasinInBox_disjoint_of_ne (calibratedPoint_ne_capturedPoint p),
    loopBasinInBox_disjoint_of_ne (saddlePoint_ne_capturedPoint threshold)⟩

/-- Membership in any basin is invariant under one forward step in `B`. -/
theorem mem_loopBasinInBox_map_iff {p : LoopParams}
    (model : DriftModelAssumptions p) {q : LoopState} (x : LoopBox p) :
    loopMapOnBox p model x ∈ loopBasinInBox p q ↔
      x ∈ loopBasinInBox p q := by
  have htail :
      (fun n ↦ loopOrbit p (loopMapOnBox p model x).1 n) =
        (fun n ↦ loopOrbit p x.1 (n + 1)) := by
    funext n
    simp only [loopMapOnBox, loopOrbit, Function.iterate_succ_apply]
  change Tendsto (fun n ↦ loopOrbit p (loopMapOnBox p model x).1 n)
      atTop (𝓝 q) ↔ Tendsto (loopOrbit p x.1) atTop (𝓝 q)
  rw [htail, tendsto_add_atTop_iff_nat]

/-- The saddle stable set is invariant under the restricted loop map. -/
theorem saddleStableSetInBox_invariant {p : LoopParams}
    (model : DriftModelAssumptions p) (threshold : ThresholdAssumption p) :
    ∀ x : LoopBox p,
      loopMapOnBox p model x ∈ saddleStableSetInBox p threshold ↔
        x ∈ saddleStableSetInBox p threshold := by
  intro x
  exact mem_loopBasinInBox_map_iff model x

/-- Under `(SS⁺)`, the saddle stable set is exactly the relative complement
of the two open corner basins. -/
theorem saddleStableSetInBox_eq_compl_cornerBasins {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) :
    saddleStableSetInBox p threshold =
      (loopBasinInBox p (calibratedPoint p) ∪
        loopBasinInBox p (capturedPoint p))ᶜ := by
  ext x
  constructor
  · intro hx
    rw [mem_compl_iff, mem_union, not_or]
    constructor
    · intro hcal
      change Tendsto (loopOrbit p x.1) atTop (𝓝 (calibratedPoint p)) at hcal
      change Tendsto (loopOrbit p x.1) atTop
        (𝓝 (saddlePoint p threshold)) at hx
      exact (calibratedPoint_ne_saddlePoint threshold)
        (tendsto_nhds_unique hcal hx)
    · intro hcap
      change Tendsto (loopOrbit p x.1) atTop
        (𝓝 (capturedPoint p)) at hcap
      change Tendsto (loopOrbit p x.1) atTop
        (𝓝 (saddlePoint p threshold)) at hx
      exact (saddlePoint_ne_capturedPoint threshold)
        (tendsto_nhds_unique hx hcap)
  · intro hx
    simp only [mem_compl_iff, mem_union] at hx
    rcases mem_calibrated_or_saddle_or_captured_basin model ssplus threshold x with
      hcal | hsad | hcap
    · exact (hx (Or.inl hcal)).elim
    · exact hsad
    · exact (hx (Or.inr hcap)).elim

/-- Under `(SS⁺)`, the saddle stable set is closed in `B`. -/
theorem saddleStableSetInBox_isClosed {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) :
    IsClosed (saddleStableSetInBox p threshold) := by
  rw [saddleStableSetInBox_eq_compl_cornerBasins model ssplus threshold]
  exact (calibratedBasinInBox_isOpen model
    (ssplus.toStrictSmallStep model).toSmallStep threshold).union
      (capturedBasinInBox_isOpen model
        (ssplus.toStrictSmallStep model).toSmallStep threshold) |>.isClosed_compl

/-! ## Ordered differences near the interior saddle -/

/-- Exact coefficients obtained by expanding the difference of the loop map
at two componentwise ordered states. The asymmetric choice of endpoints makes
the two difference identities algebraic, rather than mean-value estimates. -/
def orderedDifferenceCoefficients (p : LoopParams)
    (x y : LoopState) : LoopJacobian where
  a := 1 - 2 * p.α * p.c ^ 2 * y.2
  b := 2 * p.α * p.c * (1 - p.c * x.1)
  cJ := (1 - p.lambda₀) * p.η *
    (2 * (1 - p.η) + p.η * (x.1 + y.1)) * y.2
  d := p.s x.1

/-- At coincident states, the ordered-difference coefficients are the ordinary
unclipped Jacobian. -/
theorem orderedDifferenceCoefficients_self (p : LoopParams) (x : LoopState) :
    orderedDifferenceCoefficients p x x =
      interiorLoopJacobian p x.1 x.2 := by
  rcases x with ⟨β, D⟩
  simp only [orderedDifferenceCoefficients, interiorLoopJacobian,
    LoopParams.sSlope]
  congr 1
  ring

/-- The ordered policy-diagonal coefficient is continuous in both states. -/
theorem continuous_orderedDifferenceCoefficients_a (p : LoopParams) :
    Continuous (fun z : LoopState × LoopState ↦
      (orderedDifferenceCoefficients p z.1 z.2).a) := by
  simp only [orderedDifferenceCoefficients]
  fun_prop

/-- The ordered stock-to-policy coefficient is continuous in both states. -/
theorem continuous_orderedDifferenceCoefficients_b (p : LoopParams) :
    Continuous (fun z : LoopState × LoopState ↦
      (orderedDifferenceCoefficients p z.1 z.2).b) := by
  simp only [orderedDifferenceCoefficients]
  fun_prop

/-- The ordered policy-to-stock coefficient is continuous in both states. -/
theorem continuous_orderedDifferenceCoefficients_cJ (p : LoopParams) :
    Continuous (fun z : LoopState × LoopState ↦
      (orderedDifferenceCoefficients p z.1 z.2).cJ) := by
  simp only [orderedDifferenceCoefficients]
  fun_prop

/-- The ordered stock-diagonal coefficient is continuous in both states. -/
theorem continuous_orderedDifferenceCoefficients_d (p : LoopParams) :
    Continuous (fun z : LoopState × LoopState ↦
      (orderedDifferenceCoefficients p z.1 z.2).d) := by
  simp only [orderedDifferenceCoefficients, LoopParams.s]
  fun_prop

/-- Once the two projected policy outputs are interior, their coordinate gaps
obey the exact ordered-difference linear identities. -/
theorem loopMap_orderedDifference_eq {p : LoopParams}
    (model : DriftModelAssumptions p) (x y : LoopState)
    (hxout : (p.loopMap x).1 ∈ Ioo (0 : ℝ) 1)
    (hyout : (p.loopMap y).1 ∈ Ioo (0 : ℝ) 1) :
    let C := orderedDifferenceCoefficients p x y
    (p.loopMap y).1 - (p.loopMap x).1 =
        C.a * (y.1 - x.1) + C.b * (y.2 - x.2) ∧
      (p.loopMap y).2 - (p.loopMap x).2 =
        C.cJ * (y.1 - x.1) + C.d * (y.2 - x.2) := by
  let C := orderedDifferenceCoefficients p x y
  have hxclip : LoopParams.clipUnit (unclippedDeferenceInput p x.1 x.2) =
      (p.loopMap x).1 := by
    rfl
  have hyclip : LoopParams.clipUnit (unclippedDeferenceInput p y.1 y.2) =
      (p.loopMap y).1 := by
    rfl
  have hxinput := (clipUnit_eq_interior_iff hxout).mp hxclip
  have hyinput := (clipUnit_eq_interior_iff hyout).mp hyclip
  constructor
  · simp only [orderedDifferenceCoefficients]
    simp only [unclippedDeferenceInput, LoopParams.gradU] at hxinput hyinput
    rw [← hxinput, ← hyinput]
    ring
  · simp only [orderedDifferenceCoefficients, LoopParams.loopMap,
      LoopParams.stockStep, model.no_content_gain, add_zero, LoopParams.s]
    ring

/-- Order preservation propagates an initial comparison along both canonical
orbits. -/
theorem loopOrbit_mono_of_le {p : LoopParams}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    {x₀ y₀ : LoopState} (hx₀ : x₀ ∈ absorbingBox p)
    (hy₀ : y₀ ∈ absorbingBox p) (hxy₀ : x₀ ≤ y₀) :
    ∀ n, loopOrbit p x₀ n ≤ loopOrbit p y₀ n := by
  intro n
  induction n with
  | zero => simpa only [loopOrbit, Function.iterate_zero_apply] using hxy₀
  | succ n ih =>
      rw [show n + 1 = n.succ by omega]
      simp only [loopOrbit, Function.iterate_succ_apply']
      exact loopMap_monotoneOn_box model ss
        (loopOrbit_mem_absorbingBox model hx₀ n)
        (loopOrbit_mem_absorbingBox model hy₀ n) ih

/-- Under `(SS⁺)`, a nontrivial ordered pair acquires a strictly positive
stock gap after one step. -/
theorem loopMap_stock_lt_of_le_of_ne {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    {x y : LoopState} (hx : x ∈ absorbingBox p) (hy : y ∈ absorbingBox p)
    (hxy : x ≤ y) (hne : x ≠ y) :
    (p.loopMap x).2 < (p.loopMap y).2 := by
  have hs0 : 0 < p.s 0 := by
    simpa only [stockDiagonalLower] using ssplus.stockDiagonalLower_pos model
  have hsx : 0 < p.s x.1 :=
    hs0.trans_le ((driftStockMultiplier_strictMonoOn model).monotoneOn
      (by norm_num) hx.1 hx.1.1)
  rcases lt_or_eq_of_le hxy.1 with hβ | hβ
  · have hslt := driftStockMultiplier_strictMonoOn model hx.1 hy.1 hβ
    have hyDpos : 0 < y.2 := model.I_pos.trans_le hy.2.1
    have hpolicy : p.s x.1 * x.2 ≤ p.s x.1 * y.2 :=
      mul_le_mul_of_nonneg_left hxy.2 hsx.le
    have hstock : p.s x.1 * y.2 < p.s y.1 * y.2 :=
      mul_lt_mul_of_pos_right hslt hyDpos
    simp only [LoopParams.loopMap, LoopParams.stockStep,
      model.no_content_gain, add_zero]
    linarith
  · have hDlt : x.2 < y.2 := by
      rcases lt_or_eq_of_le hxy.2 with h | h
      · exact h
      · exact (hne (Prod.ext hβ h)).elim
    have hsy : 0 < p.s y.1 := hβ ▸ hsx
    have hmul := mul_lt_mul_of_pos_left hDlt hsy
    simp only [LoopParams.loopMap, LoopParams.stockStep,
      model.no_content_gain, add_zero]
    rw [hβ]
    linarith

/-- A distinct ordered pair of canonical orbits has a strict stock gap at
every positive time. -/
theorem loopOrbit_stock_lt_of_le_of_ne {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    {x₀ y₀ : LoopState} (hx₀ : x₀ ∈ absorbingBox p)
    (hy₀ : y₀ ∈ absorbingBox p) (hxy₀ : x₀ ≤ y₀)
    (hne : x₀ ≠ y₀) :
    ∀ n, 0 < n → (loopOrbit p x₀ n).2 < (loopOrbit p y₀ n).2 := by
  have ss := (ssplus.toStrictSmallStep model).toSmallStep
  intro n
  induction n with
  | zero => intro hn; omega
  | succ n ih =>
      intro _hn
      have horder := loopOrbit_mono_of_le model ss hx₀ hy₀ hxy₀ n
      have hneStep : loopOrbit p x₀ n ≠ loopOrbit p y₀ n := by
        by_cases hnzero : n = 0
        · simpa only [hnzero, loopOrbit, Function.iterate_zero_apply] using hne
        · have hstock := ih (Nat.pos_of_ne_zero hnzero)
          intro heq
          rw [heq] at hstock
          exact (lt_irrefl _ hstock).elim
      simpa only [loopOrbit, Function.iterate_succ_apply'] using
        loopMap_stock_lt_of_le_of_ne model ssplus
          (loopOrbit_mem_absorbingBox model hx₀ n)
          (loopOrbit_mem_absorbingBox model hy₀ n) horder hneStep

/-- A scale strictly between the reciprocal unstable eigenvalue and one. -/
def saddleExpansionScale (J : LoopJacobian) : ℝ :=
  (J.largerEigenvalue + 1) / (2 * J.largerEigenvalue)

/-- The expansion scale is positive, below one, and still leaves an expansion
factor above one. -/
theorem saddleExpansionScale_spec (J : LoopJacobian)
    (hlarger : 1 < J.largerEigenvalue) :
    0 < saddleExpansionScale J ∧ saddleExpansionScale J < 1 ∧
      1 < saddleExpansionScale J * J.largerEigenvalue := by
  have hlargerPos : 0 < J.largerEigenvalue := zero_lt_one.trans hlarger
  have hden : 0 < 2 * J.largerEigenvalue := mul_pos two_pos hlargerPos
  have hscalePos : 0 < saddleExpansionScale J := by
    rw [saddleExpansionScale]
    exact div_pos (by linarith) hden
  have hscaleLt : saddleExpansionScale J < 1 := by
    rw [saddleExpansionScale]
    exact (div_lt_one hden).2 (by linarith)
  have hproduct :
      saddleExpansionScale J * J.largerEigenvalue =
        (J.largerEigenvalue + 1) / 2 := by
    rw [saddleExpansionScale]
    field_simp [hlargerPos.ne']
  exact ⟨hscalePos, hscaleLt, by rw [hproduct]; linarith⟩

/-- The positive left-eigenvector functional used in the antichain argument. -/
def unstableFunctional (J : LoopJacobian) (δβ δD : ℝ) : ℝ :=
  J.cJ * δβ + (J.largerEigenvalue - J.a) * δD

/-- The explicit functional is a left eigenvector for the larger root. -/
theorem unstableFunctional_jacobian (J : LoopJacobian)
    (hdisc : 0 ≤ J.discriminant) (δβ δD : ℝ) :
    unstableFunctional J (J.a * δβ + J.b * δD)
        (J.cJ * δβ + J.d * δD) =
      J.largerEigenvalue * unstableFunctional J δβ δD := by
  have hchar := J.charPoly_largerEigenvalue_eq_zero hdisc
  simp only [LoopJacobian.charPoly, LoopJacobian.trace, LoopJacobian.det] at hchar
  simp only [unstableFunctional]
  linear_combination -δD * hchar

/-- Scaling both coordinates after applying the Jacobian scales its unstable
functional by the same factor. -/
theorem unstableFunctional_scaled_jacobian (J : LoopJacobian)
    (hdisc : 0 ≤ J.discriminant) (r δβ δD : ℝ) :
    unstableFunctional J (r * (J.a * δβ + J.b * δD))
        (r * (J.cJ * δβ + J.d * δD)) =
      r * J.largerEigenvalue * unstableFunctional J δβ δD := by
  rw [show unstableFunctional J (r * (J.a * δβ + J.b * δD))
      (r * (J.cJ * δβ + J.d * δD)) =
      r * unstableFunctional J (J.a * δβ + J.b * δD)
        (J.cJ * δβ + J.d * δD) by
        simp only [unstableFunctional]; ring,
    unstableFunctional_jacobian J hdisc]
  ring

/-- Under `(SS⁺)`, every entry of the saddle Jacobian is strictly positive. -/
theorem saddleJacobian_entry_pos {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) :
    let J := interiorLoopJacobian p threshold.βdagger
      (p.stationaryStock threshold.βdagger)
    0 < J.a ∧ 0 < J.b ∧ 0 < J.cJ ∧ 0 < J.d := by
  let β := threshold.βdagger
  let D := p.stationaryStock β
  let J := interiorLoopJacobian p β D
  have hβ : β ∈ Icc (0 : ℝ) 1 :=
    ⟨threshold.βdagger_mem.1.le, threshold.βdagger_mem.2.le⟩
  have hD := stationaryStock_mem_stockInterval model hβ
  have hentries := saddleJacobian_entry_bounds model
    (ssplus.toStrictSmallStep model) threshold
  have hk : 0 ≤ 2 * p.α * p.c ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) (sq_nonneg p.c)
  have haLower : policyDiagonalLower p ≤ J.a := by
    dsimp only [J, interiorLoopJacobian, policyDiagonalLower]
    have := mul_le_mul_of_nonneg_left hD.2 hk
    linarith
  have ha : 0 < J.a := (ssplus.policyDiagonalLower_pos model).trans_le haLower
  have hs0 : 0 < p.s 0 := by
    simpa only [stockDiagonalLower] using ssplus.stockDiagonalLower_pos model
  have hd : 0 < J.d := by
    change 0 < p.s β
    exact hs0.trans_le ((driftStockMultiplier_strictMonoOn model).monotoneOn
      (by norm_num) hβ hβ.1)
  exact ⟨ha, hentries.2.2.1, hentries.2.2.2.1, hd⟩

/-- The saddle's explicit larger root exceeds one under the oriented crossing
assumption. -/
theorem saddle_largerEigenvalue_gt_one {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) :
    let J := interiorLoopJacobian p threshold.βdagger
      (p.stationaryStock threshold.βdagger)
    1 < J.largerEigenvalue := by
  exact (saddle_largerEigenvalue_gt_one_iff_GSlope_pos model
    (ssplus.toStrictSmallStep model) threshold).2 threshold.GSlope_pos

/-- Two ordered orbits converging to the saddle eventually have a
nondecreasing positive-left-eigenvector gap. -/
theorem ordered_saddle_orbits_eventually_functional_mono {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) {x₀ y₀ : LoopState}
    (hx₀ : x₀ ∈ absorbingBox p) (hy₀ : y₀ ∈ absorbingBox p)
    (hxy₀ : x₀ ≤ y₀)
    (hxlim : Tendsto (loopOrbit p x₀) atTop
      (𝓝 (saddlePoint p threshold)))
    (hylim : Tendsto (loopOrbit p y₀) atTop
      (𝓝 (saddlePoint p threshold))) :
    let J := interiorLoopJacobian p threshold.βdagger
      (p.stationaryStock threshold.βdagger)
    ∃ N, ∀ n ≥ N,
      unstableFunctional J
          ((loopOrbit p y₀ n).1 - (loopOrbit p x₀ n).1)
          ((loopOrbit p y₀ n).2 - (loopOrbit p x₀ n).2) ≤
        unstableFunctional J
          ((loopOrbit p y₀ (n + 1)).1 - (loopOrbit p x₀ (n + 1)).1)
          ((loopOrbit p y₀ (n + 1)).2 - (loopOrbit p x₀ (n + 1)).2) := by
  let q := saddlePoint p threshold
  let J := interiorLoopJacobian p threshold.βdagger
    (p.stationaryStock threshold.βdagger)
  let r := saddleExpansionScale J
  let X := loopOrbit p x₀
  let Y := loopOrbit p y₀
  let C := fun n ↦ orderedDifferenceCoefficients p (X n) (Y n)
  have hentries := saddleJacobian_entry_bounds model
    (ssplus.toStrictSmallStep model) threshold
  have hJpos := saddleJacobian_entry_pos model ssplus threshold
  have hlarger := saddle_largerEigenvalue_gt_one model ssplus threshold
  have hr := saddleExpansionScale_spec J hlarger
  have hdisc : 0 ≤ J.discriminant :=
    J.discriminant_nonneg hJpos.2.1.le hJpos.2.2.1.le
  have hweightD : 0 < J.largerEigenvalue - J.a := by
    linarith [hentries.2.1]
  have hpair : Tendsto (fun n ↦ (X n, Y n)) atTop (𝓝 (q, q)) := by
    exact (Prod.tendsto_iff _ _).2 ⟨by simpa only [X, q] using hxlim,
      by simpa only [Y, q] using hylim⟩
  have hCa : Tendsto (fun n ↦ (C n).a) atTop (𝓝 J.a) := by
    have h := (continuous_orderedDifferenceCoefficients_a p).tendsto (q, q) |>.comp hpair
    change Tendsto (fun n ↦
      (orderedDifferenceCoefficients p (X n) (Y n)).a) atTop
        (𝓝 (orderedDifferenceCoefficients p q q).a) at h
    rw [orderedDifferenceCoefficients_self] at h
    simpa only [C, q, J, saddlePoint] using h
  have hCb : Tendsto (fun n ↦ (C n).b) atTop (𝓝 J.b) := by
    have h := (continuous_orderedDifferenceCoefficients_b p).tendsto (q, q) |>.comp hpair
    change Tendsto (fun n ↦
      (orderedDifferenceCoefficients p (X n) (Y n)).b) atTop
        (𝓝 (orderedDifferenceCoefficients p q q).b) at h
    rw [orderedDifferenceCoefficients_self] at h
    simpa only [C, q, J, saddlePoint] using h
  have hCc : Tendsto (fun n ↦ (C n).cJ) atTop (𝓝 J.cJ) := by
    have h := (continuous_orderedDifferenceCoefficients_cJ p).tendsto (q, q) |>.comp hpair
    change Tendsto (fun n ↦
      (orderedDifferenceCoefficients p (X n) (Y n)).cJ) atTop
        (𝓝 (orderedDifferenceCoefficients p q q).cJ) at h
    rw [orderedDifferenceCoefficients_self] at h
    simpa only [C, q, J, saddlePoint] using h
  have hCd : Tendsto (fun n ↦ (C n).d) atTop (𝓝 J.d) := by
    have h := (continuous_orderedDifferenceCoefficients_d p).tendsto (q, q) |>.comp hpair
    change Tendsto (fun n ↦
      (orderedDifferenceCoefficients p (X n) (Y n)).d) atTop
        (𝓝 (orderedDifferenceCoefficients p q q).d) at h
    rw [orderedDifferenceCoefficients_self] at h
    simpa only [C, q, J, saddlePoint] using h
  have haEvent : ∀ᶠ n in atTop, r * J.a < (C n).a :=
    hCa.eventually_const_lt (by nlinarith [hJpos.1, hr.2.1])
  have hbEvent : ∀ᶠ n in atTop, r * J.b < (C n).b :=
    hCb.eventually_const_lt (by nlinarith [hJpos.2.1, hr.2.1])
  have hcEvent : ∀ᶠ n in atTop, r * J.cJ < (C n).cJ :=
    hCc.eventually_const_lt (by nlinarith [hJpos.2.2.1, hr.2.1])
  have hdEvent : ∀ᶠ n in atTop, r * J.d < (C n).d :=
    hCd.eventually_const_lt (by nlinarith [hJpos.2.2.2, hr.2.1])
  have hIoo : Ioo (0 : ℝ) 1 ∈ 𝓝 q.1 := by
    simpa only [q, saddlePoint] using
      Ioo_mem_nhds threshold.βdagger_mem.1 threshold.βdagger_mem.2
  have hxNext : Tendsto (fun n ↦ (X (n + 1)).1) atTop (𝓝 q.1) :=
    (continuous_fst.tendsto q).comp
      (hxlim.comp (tendsto_add_atTop_nat 1))
  have hyNext : Tendsto (fun n ↦ (Y (n + 1)).1) atTop (𝓝 q.1) :=
    (continuous_fst.tendsto q).comp
      (hylim.comp (tendsto_add_atTop_nat 1))
  have hxInterior : ∀ᶠ n in atTop, (X (n + 1)).1 ∈ Ioo (0 : ℝ) 1 :=
    hxNext.eventually hIoo
  have hyInterior : ∀ᶠ n in atTop, (Y (n + 1)).1 ∈ Ioo (0 : ℝ) 1 :=
    hyNext.eventually hIoo
  have hgood : ∀ᶠ n in atTop,
      r * J.a < (C n).a ∧ r * J.b < (C n).b ∧
      r * J.cJ < (C n).cJ ∧ r * J.d < (C n).d ∧
      (X (n + 1)).1 ∈ Ioo (0 : ℝ) 1 ∧
      (Y (n + 1)).1 ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [haEvent, hbEvent, hcEvent, hdEvent,
      hxInterior, hyInterior] with n ha hb hc hd hxint hyint
    exact ⟨ha, hb, hc, hd, hxint, hyint⟩
  obtain ⟨N, hN⟩ := hgood.exists_forall_of_atTop
  refine ⟨N, ?_⟩
  intro n hn
  rcases hN n hn with ⟨ha, hb, hc, hd, hxint, hyint⟩
  have horder := loopOrbit_mono_of_le model
    (ssplus.toStrictSmallStep model).toSmallStep hx₀ hy₀ hxy₀ n
  have hβnonneg : 0 ≤ (Y n).1 - (X n).1 := sub_nonneg.mpr horder.1
  have hDnonneg : 0 ≤ (Y n).2 - (X n).2 := sub_nonneg.mpr horder.2
  have hxout : (p.loopMap (X n)).1 ∈ Ioo (0 : ℝ) 1 := by
    simpa only [X, loopOrbit, Function.iterate_succ_apply'] using hxint
  have hyout : (p.loopMap (Y n)).1 ∈ Ioo (0 : ℝ) 1 := by
    simpa only [Y, loopOrbit, Function.iterate_succ_apply'] using hyint
  have heq := loopMap_orderedDifference_eq model (X n) (Y n) hxout hyout
  have heqβ :
      (Y (n + 1)).1 - (X (n + 1)).1 =
        (C n).a * ((Y n).1 - (X n).1) +
          (C n).b * ((Y n).2 - (X n).2) := by
    simpa only [C, X, Y, loopOrbit, Function.iterate_succ_apply'] using heq.1
  have heqD :
      (Y (n + 1)).2 - (X (n + 1)).2 =
        (C n).cJ * ((Y n).1 - (X n).1) +
          (C n).d * ((Y n).2 - (X n).2) := by
    simpa only [C, X, Y, loopOrbit, Function.iterate_succ_apply'] using heq.2
  have hβrec :
      r * (J.a * ((Y n).1 - (X n).1) +
          J.b * ((Y n).2 - (X n).2)) ≤
        (Y (n + 1)).1 - (X (n + 1)).1 := by
    calc
      r * (J.a * ((Y n).1 - (X n).1) +
          J.b * ((Y n).2 - (X n).2)) =
          (r * J.a) * ((Y n).1 - (X n).1) +
            (r * J.b) * ((Y n).2 - (X n).2) := by ring
      _ ≤ (C n).a * ((Y n).1 - (X n).1) +
          (C n).b * ((Y n).2 - (X n).2) :=
        add_le_add (mul_le_mul_of_nonneg_right ha.le hβnonneg)
          (mul_le_mul_of_nonneg_right hb.le hDnonneg)
      _ = (Y (n + 1)).1 - (X (n + 1)).1 := heqβ.symm
  have hDrec :
      r * (J.cJ * ((Y n).1 - (X n).1) +
          J.d * ((Y n).2 - (X n).2)) ≤
        (Y (n + 1)).2 - (X (n + 1)).2 := by
    calc
      r * (J.cJ * ((Y n).1 - (X n).1) +
          J.d * ((Y n).2 - (X n).2)) =
          (r * J.cJ) * ((Y n).1 - (X n).1) +
            (r * J.d) * ((Y n).2 - (X n).2) := by ring
      _ ≤ (C n).cJ * ((Y n).1 - (X n).1) +
          (C n).d * ((Y n).2 - (X n).2) :=
        add_le_add (mul_le_mul_of_nonneg_right hc.le hβnonneg)
          (mul_le_mul_of_nonneg_right hd.le hDnonneg)
      _ = (Y (n + 1)).2 - (X (n + 1)).2 := heqD.symm
  have hΦnonneg : 0 ≤ unstableFunctional J
      ((Y n).1 - (X n).1) ((Y n).2 - (X n).2) := by
    simp only [unstableFunctional]
    exact add_nonneg (mul_nonneg hJpos.2.2.1.le hβnonneg)
      (mul_nonneg hweightD.le hDnonneg)
  have hscaled :
      unstableFunctional J
          (r * (J.a * ((Y n).1 - (X n).1) +
            J.b * ((Y n).2 - (X n).2)))
          (r * (J.cJ * ((Y n).1 - (X n).1) +
            J.d * ((Y n).2 - (X n).2))) ≤
        unstableFunctional J
          ((Y (n + 1)).1 - (X (n + 1)).1)
          ((Y (n + 1)).2 - (X (n + 1)).2) := by
    simp only [unstableFunctional]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hβrec hJpos.2.2.1.le)
      (mul_le_mul_of_nonneg_left hDrec hweightD.le)
  calc
    unstableFunctional J ((Y n).1 - (X n).1) ((Y n).2 - (X n).2) ≤
        r * J.largerEigenvalue *
          unstableFunctional J ((Y n).1 - (X n).1) ((Y n).2 - (X n).2) := by
      nlinarith [hr.2.2]
    _ = unstableFunctional J
          (r * (J.a * ((Y n).1 - (X n).1) +
            J.b * ((Y n).2 - (X n).2)))
          (r * (J.cJ * ((Y n).1 - (X n).1) +
            J.d * ((Y n).2 - (X n).2))) := by
      rw [unstableFunctional_scaled_jacobian J hdisc]
    _ ≤ unstableFunctional J
          ((Y (n + 1)).1 - (X (n + 1)).1)
          ((Y (n + 1)).2 - (X (n + 1)).2) := hscaled

/-- No two distinct componentwise ordered points of `B` can both converge to
the interior saddle. This is the antichain core of Paper II, Theorem 3.14(e). -/
theorem saddleStableSetInBox_ordered_eq {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) {x y : LoopBox p}
    (hx : x ∈ saddleStableSetInBox p threshold)
    (hy : y ∈ saddleStableSetInBox p threshold) (hxy : x ≤ y) :
    x = y := by
  apply Subtype.ext
  by_contra hne
  let J := interiorLoopJacobian p threshold.βdagger
    (p.stationaryStock threshold.βdagger)
  let X := loopOrbit p x.1
  let Y := loopOrbit p y.1
  let Φ := fun n ↦ unstableFunctional J
    ((Y n).1 - (X n).1) ((Y n).2 - (X n).2)
  change Tendsto X atTop (𝓝 (saddlePoint p threshold)) at hx
  change Tendsto Y atTop (𝓝 (saddlePoint p threshold)) at hy
  have hmonoRaw := ordered_saddle_orbits_eventually_functional_mono
    model ssplus threshold x.2 y.2 hxy hx hy
  obtain ⟨N₀, hmono⟩ : ∃ N, ∀ n ≥ N, Φ n ≤ Φ (n + 1) := by
    simpa only [Φ, X, Y, J] using hmonoRaw
  let N := N₀ + 1
  have hJpos := saddleJacobian_entry_pos model ssplus threshold
  have hlarger := saddle_largerEigenvalue_gt_one model ssplus threshold
  have hentries := saddleJacobian_entry_bounds model
    (ssplus.toStrictSmallStep model) threshold
  have hweightD : 0 < J.largerEigenvalue - J.a := by
    linarith [hentries.2.1]
  have horder : ∀ n, X n ≤ Y n :=
    loopOrbit_mono_of_le model (ssplus.toStrictSmallStep model).toSmallStep
      x.2 y.2 hxy
  have hstockN : (X N).2 < (Y N).2 := by
    exact loopOrbit_stock_lt_of_le_of_ne model ssplus x.2 y.2 hxy hne N (by
      simp only [N]
      omega)
  have hΦNpos : 0 < Φ N := by
    have hβnonneg : 0 ≤ (Y N).1 - (X N).1 := sub_nonneg.mpr (horder N).1
    have hDpos : 0 < (Y N).2 - (X N).2 := sub_pos.mpr hstockN
    simp only [Φ, unstableFunctional]
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg hJpos.2.2.1.le hβnonneg)
      (mul_pos hweightD hDpos)
  have htailLower : ∀ k, Φ N ≤ Φ (N + k) := by
    intro k
    induction k with
    | zero => simpa only [Nat.add_zero] using (le_refl (Φ N))
    | succ k ih =>
        calc
          Φ N ≤ Φ (N + k) := ih
          _ ≤ Φ ((N + k) + 1) := hmono (N + k) (by
            simp only [N]
            omega)
          _ = Φ (N + (k + 1)) := by rw [Nat.add_assoc]
  have hxβ : Tendsto (fun n ↦ (X n).1) atTop
      (𝓝 (saddlePoint p threshold).1) :=
    (continuous_fst.tendsto _).comp hx
  have hyβ : Tendsto (fun n ↦ (Y n).1) atTop
      (𝓝 (saddlePoint p threshold).1) :=
    (continuous_fst.tendsto _).comp hy
  have hxD : Tendsto (fun n ↦ (X n).2) atTop
      (𝓝 (saddlePoint p threshold).2) :=
    (continuous_snd.tendsto _).comp hx
  have hyD : Tendsto (fun n ↦ (Y n).2) atTop
      (𝓝 (saddlePoint p threshold).2) :=
    (continuous_snd.tendsto _).comp hy
  have hβgap : Tendsto (fun n ↦ (Y n).1 - (X n).1) atTop (𝓝 0) := by
    simpa only [sub_self] using hyβ.sub hxβ
  have hDgap : Tendsto (fun n ↦ (Y n).2 - (X n).2) atTop (𝓝 0) := by
    simpa only [sub_self] using hyD.sub hxD
  have hΦlim : Tendsto Φ atTop (𝓝 0) := by
    have hfirst : Tendsto (fun n ↦ J.cJ * ((Y n).1 - (X n).1))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using hβgap.const_mul J.cJ
    have hsecond : Tendsto (fun n ↦
        (J.largerEigenvalue - J.a) * ((Y n).2 - (X n).2))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using hDgap.const_mul (J.largerEigenvalue - J.a)
    simpa only [Φ, unstableFunctional, mul_zero, add_zero] using
      hfirst.add hsecond
  have hsmall : ∀ᶠ n in atTop, Φ n < Φ N / 2 :=
    hΦlim.eventually_lt_const (by nlinarith)
  obtain ⟨n, hnsmall, hnN⟩ :=
    (hsmall.and (eventually_ge_atTop N)).exists
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnN
  have hlower := htailLower k
  nlinarith

/-- The saddle stable set is an antichain for componentwise order. -/
theorem saddleStableSetInBox_isAntichain {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) :
    IsAntichain (· ≤ ·) (saddleStableSetInBox p threshold) := by
  intro x hx y hy hne hxy
  exact hne (saddleStableSetInBox_ordered_eq model ssplus threshold hx hy hxy)

/-! ## Empty interior -/

/-- Every relative neighborhood in `B` contains a distinct point comparable
to its center. The perturbation uses only the policy coordinate, so it remains
valid on either stock face. -/
theorem exists_nearby_comparable_in_loopBox {p : LoopParams}
    (x : LoopBox p) {U : Set (LoopBox p)} (hU : U ∈ 𝓝 x) :
    ∃ y ∈ U, y ≠ x ∧ (x ≤ y ∨ y ≤ x) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  by_cases hup : x.1.1 < 1
  · let δ := min ((1 - x.1.1) / 2) (ε / 2)
    have hgap : 0 < (1 - x.1.1) / 2 := by linarith
    have hhalfε : 0 < ε / 2 := by linarith
    have hδ : 0 < δ := lt_min hgap hhalfε
    have hδgap : δ ≤ (1 - x.1.1) / 2 := min_le_left _ _
    have hδε : δ < ε := (min_le_right _ _).trans_lt (by linarith)
    have hpolicy : x.1.1 + δ ∈ Icc (0 : ℝ) 1 := by
      constructor
      · linarith [x.2.1.1]
      · linarith
    let y : LoopBox p :=
      ⟨(x.1.1 + δ, x.1.2), ⟨hpolicy, x.2.2⟩⟩
    have hdist : dist y x = δ := by
      change dist (x.1.1 + δ, x.1.2) (x.1.1, x.1.2) = δ
      rw [dist_prod_same_right, Real.dist_eq]
      simp only [add_sub_cancel_left, abs_of_pos hδ]
    have hyU : y ∈ U := hball (by
      rw [Metric.mem_ball, hdist]
      exact hδε)
    have hyne : y ≠ x := by
      intro heq
      have hfirst := congrArg (fun z : LoopBox p ↦ z.1.1) heq
      simp only [y] at hfirst
      linarith
    have hxy : x ≤ y := by
      constructor
      · change x.1.1 ≤ x.1.1 + δ
        linarith
      · exact le_rfl
    exact ⟨y, hyU, hyne, Or.inl hxy⟩
  · have hxone : x.1.1 = 1 := by linarith [x.2.1.2]
    let δ := min ((1 : ℝ) / 2) (ε / 2)
    have hhalf : 0 < (1 : ℝ) / 2 := by norm_num
    have hhalfε : 0 < ε / 2 := by linarith
    have hδ : 0 < δ := lt_min hhalf hhalfε
    have hδhalf : δ ≤ (1 : ℝ) / 2 := min_le_left _ _
    have hδε : δ < ε := (min_le_right _ _).trans_lt (by linarith)
    have hpolicy : 1 - δ ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith
    let y : LoopBox p := ⟨(1 - δ, x.1.2), ⟨hpolicy, x.2.2⟩⟩
    have hdist : dist y x = δ := by
      change dist (1 - δ, x.1.2) (x.1.1, x.1.2) = δ
      rw [hxone, dist_prod_same_right, Real.dist_eq]
      simp only [sub_sub_cancel_left, abs_neg, abs_of_pos hδ]
    have hyU : y ∈ U := hball (by
      rw [Metric.mem_ball, hdist]
      exact hδε)
    have hyne : y ≠ x := by
      intro heq
      have hfirst := congrArg (fun z : LoopBox p ↦ z.1.1) heq
      simp only [y, hxone] at hfirst
      linarith
    have hyx : y ≤ x := by
      constructor
      · change 1 - δ ≤ x.1.1
        rw [hxone]
        linarith
      · exact le_rfl
    exact ⟨y, hyU, hyne, Or.inr hyx⟩

/-- The saddle stable set has empty relative interior in `B`. -/
theorem saddleStableSetInBox_interior_eq_empty {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) :
    interior (saddleStableSetInBox p threshold) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hxInterior
  have hnhds : interior (saddleStableSetInBox p threshold) ∈ 𝓝 x :=
    isOpen_interior.mem_nhds hxInterior
  obtain ⟨y, hyInterior, hyne, hcomp⟩ :=
    exists_nearby_comparable_in_loopBox x hnhds
  have hxStable : x ∈ saddleStableSetInBox p threshold := interior_subset hxInterior
  have hyStable : y ∈ saddleStableSetInBox p threshold := interior_subset hyInterior
  rcases hcomp with hxy | hyx
  · exact hyne.symm
      (saddleStableSetInBox_ordered_eq model ssplus threshold hxStable hyStable hxy)
  · exact hyne
      (saddleStableSetInBox_ordered_eq model ssplus threshold hyStable hxStable hyx)

/-! ## Two-sided perturbations and the common basin boundary -/

/-- The interior saddle as a point of the invariant box. -/
def saddlePointInBox (p : LoopParams) (model : DriftModelAssumptions p)
    (threshold : ThresholdAssumption p) : LoopBox p :=
  ⟨saddlePoint p threshold,
    ⟨⟨threshold.βdagger_mem.1.le, threshold.βdagger_mem.2.le⟩,
      stationaryStock_mem_stockInterval model
        ⟨threshold.βdagger_mem.1.le, threshold.βdagger_mem.2.le⟩⟩⟩

/-- The saddle itself belongs to its stable set. -/
theorem saddlePointInBox_mem_stable {p : LoopParams}
    (model : DriftModelAssumptions p) (threshold : ThresholdAssumption p) :
    saddlePointInBox p model threshold ∈ saddleStableSetInBox p threshold := by
  let q := saddlePoint p threshold
  have hfixed := saddlePoint_fixed model threshold
  change p.loopMap q = q at hfixed
  have horbit : loopOrbit p q = fun _ ↦ q := by
    funext n
    induction n with
    | zero => simp only [loopOrbit, Function.iterate_zero_apply]
    | succ n ih =>
        simp only [loopOrbit, Function.iterate_succ_apply'] at ih ⊢
        rw [ih, hfixed]
  change Tendsto (loopOrbit p q) atTop (𝓝 q)
  rw [horbit]
  exact tendsto_const_nhds

/-- A stable-set point has room to move strictly downward in at least one
coordinate of `B`. -/
theorem saddleStablePoint_has_lower_room {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) (z : LoopBox p)
    (hz : z ∈ saddleStableSetInBox p threshold) :
    0 < z.1.1 ∨ p.I < z.1.2 := by
  by_cases hpolicy : 0 < z.1.1
  · exact Or.inl hpolicy
  · right
    by_contra hstock
    have hpolicyZero : z.1.1 = 0 :=
      le_antisymm (not_lt.mp hpolicy) z.2.1.1
    have hstockI : z.1.2 = p.I :=
      le_antisymm (not_lt.mp hstock) z.2.2.1
    have hzle : z ≤ saddlePointInBox p model threshold := by
      constructor
      · simp only [saddlePointInBox, saddlePoint, hpolicyZero]
        exact threshold.βdagger_mem.1.le
      · simp only [saddlePointInBox, saddlePoint, hstockI]
        exact (stationaryStock_mem_stockInterval model
          ⟨threshold.βdagger_mem.1.le, threshold.βdagger_mem.2.le⟩).1
    have heq := saddleStableSetInBox_ordered_eq model ssplus threshold hz
      (saddlePointInBox_mem_stable model threshold) hzle
    have hfirst := congrArg (fun w : LoopBox p ↦ w.1.1) heq
    simp only [saddlePointInBox, saddlePoint, hpolicyZero] at hfirst
    linarith [threshold.βdagger_mem.1]

/-- A stable-set point has room to move strictly upward in at least one
coordinate of `B`. -/
theorem saddleStablePoint_has_upper_room {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) (z : LoopBox p)
    (hz : z ∈ saddleStableSetInBox p threshold) :
    z.1.1 < 1 ∨ z.1.2 < p.I / p.lambda₀ := by
  by_cases hpolicy : z.1.1 < 1
  · exact Or.inl hpolicy
  · right
    by_contra hstock
    have hpolicyOne : z.1.1 = 1 :=
      le_antisymm z.2.1.2 (not_lt.mp hpolicy)
    have hstockTop : z.1.2 = p.I / p.lambda₀ :=
      le_antisymm z.2.2.2 (not_lt.mp hstock)
    have hleZ : saddlePointInBox p model threshold ≤ z := by
      constructor
      · simp only [saddlePointInBox, saddlePoint, hpolicyOne]
        exact threshold.βdagger_mem.2.le
      · simp only [saddlePointInBox, saddlePoint, hstockTop]
        exact (stationaryStock_mem_stockInterval model
          ⟨threshold.βdagger_mem.1.le, threshold.βdagger_mem.2.le⟩).2
    have heq := saddleStableSetInBox_ordered_eq model ssplus threshold
      (saddlePointInBox_mem_stable model threshold) hz hleZ
    have hfirst := congrArg (fun w : LoopBox p ↦ w.1.1) heq
    simp only [saddlePointInBox, saddlePoint, hpolicyOne] at hfirst
    linarith [threshold.βdagger_mem.2]

/-- Every relative neighborhood of a stable-set point contains a distinct
componentwise larger point of `B`. -/
theorem exists_nearby_above_stablePoint {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) (z : LoopBox p)
    (hz : z ∈ saddleStableSetInBox p threshold) {U : Set (LoopBox p)}
    (hU : U ∈ 𝓝 z) :
    ∃ y ∈ U, z ≤ y ∧ y ≠ z := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  rcases saddleStablePoint_has_upper_room model ssplus threshold z hz with
    hpolicy | hstock
  · let δ := min ((1 - z.1.1) / 2) (ε / 2)
    have hδ : 0 < δ := lt_min (by linarith) (by linarith)
    have hδgap : δ ≤ (1 - z.1.1) / 2 := min_le_left _ _
    have hδε : δ < ε := (min_le_right _ _).trans_lt (by linarith)
    have hpolicyMem : z.1.1 + δ ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [z.2.1.1]
    let y : LoopBox p :=
      ⟨(z.1.1 + δ, z.1.2), ⟨hpolicyMem, z.2.2⟩⟩
    have hyU : y ∈ U := hball (by
      rw [Metric.mem_ball]
      change dist (z.1.1 + δ, z.1.2) (z.1.1, z.1.2) < ε
      rw [dist_prod_same_right, Real.dist_eq]
      simpa only [add_sub_cancel_left, abs_of_pos hδ] using hδε)
    have hzy : z ≤ y := ⟨by change z.1.1 ≤ z.1.1 + δ; linarith, le_rfl⟩
    have hyne : y ≠ z := by
      intro heq
      have := congrArg (fun w : LoopBox p ↦ w.1.1) heq
      simp only [y] at this
      linarith
    exact ⟨y, hyU, hzy, hyne⟩
  · let δ := min ((p.I / p.lambda₀ - z.1.2) / 2) (ε / 2)
    have hδ : 0 < δ := lt_min (by linarith) (by linarith)
    have hδgap : δ ≤ (p.I / p.lambda₀ - z.1.2) / 2 := min_le_left _ _
    have hδε : δ < ε := (min_le_right _ _).trans_lt (by linarith)
    have hstockMem : z.1.2 + δ ∈ Icc p.I (p.I / p.lambda₀) := by
      constructor <;> linarith [z.2.2.1]
    let y : LoopBox p :=
      ⟨(z.1.1, z.1.2 + δ), ⟨z.2.1, hstockMem⟩⟩
    have hyU : y ∈ U := hball (by
      rw [Metric.mem_ball]
      change dist (z.1.1, z.1.2 + δ) (z.1.1, z.1.2) < ε
      rw [dist_prod_same_left, Real.dist_eq]
      simpa only [add_sub_cancel_left, abs_of_pos hδ] using hδε)
    have hzy : z ≤ y := ⟨le_rfl, by change z.1.2 ≤ z.1.2 + δ; linarith⟩
    have hyne : y ≠ z := by
      intro heq
      have := congrArg (fun w : LoopBox p ↦ w.1.2) heq
      simp only [y] at this
      linarith
    exact ⟨y, hyU, hzy, hyne⟩

/-- Every relative neighborhood of a stable-set point contains a distinct
componentwise smaller point of `B`. -/
theorem exists_nearby_below_stablePoint {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) (z : LoopBox p)
    (hz : z ∈ saddleStableSetInBox p threshold) {U : Set (LoopBox p)}
    (hU : U ∈ 𝓝 z) :
    ∃ y ∈ U, y ≤ z ∧ y ≠ z := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  rcases saddleStablePoint_has_lower_room model ssplus threshold z hz with
    hpolicy | hstock
  · let δ := min (z.1.1 / 2) (ε / 2)
    have hδ : 0 < δ := lt_min (by linarith) (by linarith)
    have hδgap : δ ≤ z.1.1 / 2 := min_le_left _ _
    have hδε : δ < ε := (min_le_right _ _).trans_lt (by linarith)
    have hpolicyMem : z.1.1 - δ ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [z.2.1.2]
    let y : LoopBox p :=
      ⟨(z.1.1 - δ, z.1.2), ⟨hpolicyMem, z.2.2⟩⟩
    have hyU : y ∈ U := hball (by
      rw [Metric.mem_ball]
      change dist (z.1.1 - δ, z.1.2) (z.1.1, z.1.2) < ε
      rw [dist_prod_same_right, Real.dist_eq]
      simpa only [sub_sub_cancel_left, abs_neg, abs_of_pos hδ] using hδε)
    have hyz : y ≤ z := ⟨by change z.1.1 - δ ≤ z.1.1; linarith, le_rfl⟩
    have hyne : y ≠ z := by
      intro heq
      have := congrArg (fun w : LoopBox p ↦ w.1.1) heq
      simp only [y] at this
      linarith
    exact ⟨y, hyU, hyz, hyne⟩
  · let δ := min ((z.1.2 - p.I) / 2) (ε / 2)
    have hδ : 0 < δ := lt_min (by linarith) (by linarith)
    have hδgap : δ ≤ (z.1.2 - p.I) / 2 := min_le_left _ _
    have hδε : δ < ε := (min_le_right _ _).trans_lt (by linarith)
    have hstockMem : z.1.2 - δ ∈ Icc p.I (p.I / p.lambda₀) := by
      constructor <;> linarith [z.2.2.2]
    let y : LoopBox p :=
      ⟨(z.1.1, z.1.2 - δ), ⟨z.2.1, hstockMem⟩⟩
    have hyU : y ∈ U := hball (by
      rw [Metric.mem_ball]
      change dist (z.1.1, z.1.2 - δ) (z.1.1, z.1.2) < ε
      rw [dist_prod_same_left, Real.dist_eq]
      simpa only [sub_sub_cancel_left, abs_neg, abs_of_pos hδ] using hδε)
    have hyz : y ≤ z := ⟨le_rfl, by change z.1.2 - δ ≤ z.1.2; linarith⟩
    have hyne : y ≠ z := by
      intro heq
      have := congrArg (fun w : LoopBox p ↦ w.1.2) heq
      simp only [y] at this
      linarith
    exact ⟨y, hyU, hyz, hyne⟩

/-- Pointwise order of two convergent orbits passes to their limits. -/
theorem loopOrbit_limit_le_limit {p : LoopParams} {x₀ y₀ q₁ q₂ : LoopState}
    (horder : ∀ n, loopOrbit p x₀ n ≤ loopOrbit p y₀ n)
    (hxlim : Tendsto (loopOrbit p x₀) atTop (𝓝 q₁))
    (hylim : Tendsto (loopOrbit p y₀) atTop (𝓝 q₂)) :
    q₁ ≤ q₂ :=
  le_of_tendsto_of_tendsto' hxlim hylim horder

/-- A strict upward perturbation of a stable-set point belongs to the captured
basin. -/
theorem above_stablePoint_mem_capturedBasin {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) {z y : LoopBox p}
    (hz : z ∈ saddleStableSetInBox p threshold) (hzy : z ≤ y)
    (hyne : y ≠ z) :
    y ∈ loopBasinInBox p (capturedPoint p) := by
  rcases mem_calibrated_or_saddle_or_captured_basin model ssplus threshold y with
    hcal | hsad | hcap
  · have horder := loopOrbit_mono_of_le model
      (ssplus.toStrictSmallStep model).toSmallStep z.2 y.2 hzy
    have hzlim : Tendsto (loopOrbit p z.1) atTop
        (𝓝 (saddlePoint p threshold)) := hz
    have hyLim : Tendsto (loopOrbit p y.1) atTop
        (𝓝 (calibratedPoint p)) := hcal
    have hlimits := loopOrbit_limit_le_limit horder hzlim hyLim
    have hpolicy := hlimits.1
    simp only [saddlePoint, calibratedPoint] at hpolicy
    linarith [threshold.βdagger_mem.1]
  · have heq := saddleStableSetInBox_ordered_eq model ssplus threshold hz hsad hzy
    exact (hyne heq.symm).elim
  · exact hcap

/-- A strict downward perturbation of a stable-set point belongs to the
calibrated basin. -/
theorem below_stablePoint_mem_calibratedBasin {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) {z y : LoopBox p}
    (hz : z ∈ saddleStableSetInBox p threshold) (hyz : y ≤ z)
    (hyne : y ≠ z) :
    y ∈ loopBasinInBox p (calibratedPoint p) := by
  rcases mem_calibrated_or_saddle_or_captured_basin model ssplus threshold y with
    hcal | hsad | hcap
  · exact hcal
  · have heq := saddleStableSetInBox_ordered_eq model ssplus threshold hsad hz hyz
    exact (hyne heq).elim
  · have horder := loopOrbit_mono_of_le model
      (ssplus.toStrictSmallStep model).toSmallStep y.2 z.2 hyz
    have hyLim : Tendsto (loopOrbit p y.1) atTop
        (𝓝 (capturedPoint p)) := hcap
    have hzlim : Tendsto (loopOrbit p z.1) atTop
        (𝓝 (saddlePoint p threshold)) := hz
    have hlimits := loopOrbit_limit_le_limit horder hyLim hzlim
    have hpolicy := hlimits.1
    simp only [capturedPoint, saddlePoint] at hpolicy
    linarith [threshold.βdagger_mem.2]

/-- Every saddle-stable point lies in the relative closure of the captured
basin. -/
theorem saddleStableSetInBox_subset_closure_capturedBasin {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) :
    saddleStableSetInBox p threshold ⊆
      closure (loopBasinInBox p (capturedPoint p)) := by
  intro z hz
  rw [mem_closure_iff]
  intro U hUopen hzU
  obtain ⟨y, hyU, hzy, hyne⟩ := exists_nearby_above_stablePoint
    model ssplus threshold z hz (hUopen.mem_nhds hzU)
  exact ⟨y, hyU, above_stablePoint_mem_capturedBasin
    model ssplus threshold hz hzy hyne⟩

/-- Every saddle-stable point lies in the relative closure of the calibrated
basin. -/
theorem saddleStableSetInBox_subset_closure_calibratedBasin {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) :
    saddleStableSetInBox p threshold ⊆
      closure (loopBasinInBox p (calibratedPoint p)) := by
  intro z hz
  rw [mem_closure_iff]
  intro U hUopen hzU
  obtain ⟨y, hyU, hyz, hyne⟩ := exists_nearby_below_stablePoint
    model ssplus threshold z hz (hUopen.mem_nhds hzU)
  exact ⟨y, hyU, below_stablePoint_mem_calibratedBasin
    model ssplus threshold hz hyz hyne⟩

/-- The relative closure of the calibrated basin consists exactly of that
basin together with the saddle stable set. -/
theorem closure_calibratedBasinInBox_eq {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) :
    closure (loopBasinInBox p (calibratedPoint p)) =
      loopBasinInBox p (calibratedPoint p) ∪
        saddleStableSetInBox p threshold := by
  apply Set.Subset.antisymm
  · intro z hzClosure
    have hdisjoint := loopBasinInBox_disjoint_of_ne (p := p)
      (calibratedPoint_ne_capturedPoint p)
    have hsubset : loopBasinInBox p (calibratedPoint p) ⊆
        (loopBasinInBox p (capturedPoint p))ᶜ := by
      intro w hwcal hwcap
      exact Set.disjoint_left.mp hdisjoint hwcal hwcap
    have hzNotCaptured : z ∉ loopBasinInBox p (capturedPoint p) :=
      (closure_minimal hsubset
        (capturedBasinInBox_isOpen model
          (ssplus.toStrictSmallStep model).toSmallStep threshold).isClosed_compl
        hzClosure)
    rcases mem_calibrated_or_saddle_or_captured_basin model ssplus threshold z with
      hcal | hsad | hcap
    · exact Or.inl hcal
    · exact Or.inr hsad
    · exact (hzNotCaptured hcap).elim
  · intro z hz
    rcases hz with hcal | hsad
    · exact subset_closure hcal
    · exact saddleStableSetInBox_subset_closure_calibratedBasin
        model ssplus threshold hsad

/-- The relative closure of the captured basin consists exactly of that basin
together with the saddle stable set. -/
theorem closure_capturedBasinInBox_eq {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) :
    closure (loopBasinInBox p (capturedPoint p)) =
      loopBasinInBox p (capturedPoint p) ∪
        saddleStableSetInBox p threshold := by
  apply Set.Subset.antisymm
  · intro z hzClosure
    have hdisjoint := loopBasinInBox_disjoint_of_ne (p := p)
      (calibratedPoint_ne_capturedPoint p)
    have hsubset : loopBasinInBox p (capturedPoint p) ⊆
        (loopBasinInBox p (calibratedPoint p))ᶜ := by
      intro w hwcap hwcal
      exact Set.disjoint_left.mp hdisjoint hwcal hwcap
    have hzNotCalibrated : z ∉ loopBasinInBox p (calibratedPoint p) :=
      (closure_minimal hsubset
        (calibratedBasinInBox_isOpen model
          (ssplus.toStrictSmallStep model).toSmallStep threshold).isClosed_compl
        hzClosure)
    rcases mem_calibrated_or_saddle_or_captured_basin model ssplus threshold z with
      hcal | hsad | hcap
    · exact (hzNotCalibrated hcal).elim
    · exact Or.inr hsad
    · exact Or.inl hcap
  · intro z hz
    rcases hz with hcap | hsad
    · exact subset_closure hcap
    · exact saddleStableSetInBox_subset_closure_capturedBasin
        model ssplus threshold hsad

/-- The saddle stable set is the relative frontier of the calibrated basin. -/
theorem frontier_calibratedBasinInBox_eq {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) :
    frontier (loopBasinInBox p (calibratedPoint p)) =
      saddleStableSetInBox p threshold := by
  rw [(calibratedBasinInBox_isOpen model
    (ssplus.toStrictSmallStep model).toSmallStep threshold).frontier_eq,
    closure_calibratedBasinInBox_eq model ssplus threshold]
  ext z
  constructor
  · rintro ⟨hcal | hsad, hnotCal⟩
    · exact (hnotCal hcal).elim
    · exact hsad
  · intro hsad
    refine ⟨Or.inr hsad, ?_⟩
    intro hcal
    exact (calibratedPoint_ne_saddlePoint threshold)
      (tendsto_nhds_unique hcal hsad)

/-- The saddle stable set is the relative frontier of the captured basin. -/
theorem frontier_capturedBasinInBox_eq {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) :
    frontier (loopBasinInBox p (capturedPoint p)) =
      saddleStableSetInBox p threshold := by
  rw [(capturedBasinInBox_isOpen model
    (ssplus.toStrictSmallStep model).toSmallStep threshold).frontier_eq,
    closure_capturedBasinInBox_eq model ssplus threshold]
  ext z
  constructor
  · rintro ⟨hcap | hsad, hnotCap⟩
    · exact (hnotCap hcap).elim
    · exact hsad
  · intro hsad
    refine ⟨Or.inr hsad, ?_⟩
    intro hcap
    exact (saddlePoint_ne_capturedPoint threshold)
      (tendsto_nhds_unique hsad hcap)

/-- Paper II, Theorem 3.14(e): the stable set is the common relative boundary of
the two open corner basins. -/
theorem bistability_commonBasinBoundary {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) :
    frontier (loopBasinInBox p (calibratedPoint p)) =
        saddleStableSetInBox p threshold ∧
      frontier (loopBasinInBox p (capturedPoint p)) =
        saddleStableSetInBox p threshold :=
  ⟨frontier_calibratedBasinInBox_eq model ssplus threshold,
    frontier_capturedBasinInBox_eq model ssplus threshold⟩

/-- The complement of the stable set is exactly the union of the two corner
basins. -/
theorem compl_saddleStableSetInBox_eq_cornerBasins {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) :
    (saddleStableSetInBox p threshold)ᶜ =
      loopBasinInBox p (calibratedPoint p) ∪
        loopBasinInBox p (capturedPoint p) := by
  rw [saddleStableSetInBox_eq_compl_cornerBasins model ssplus threshold,
    compl_compl]

/-! ## Orientation and hyperbolicity under `(SS⁺)` -/

/-- The stronger step bound makes the unclipped Jacobian determinant strictly
positive at every state of `B`. -/
theorem interiorLoopJacobian_det_pos_on_box {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    {x : LoopState} (hx : x ∈ absorbingBox p) :
    0 < (interiorLoopJacobian p x.1 x.2).det := by
  let J := interiorLoopJacobian p x.1 x.2
  have hk : 0 ≤ 2 * p.α * p.c ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) (sq_nonneg p.c)
  have ha : policyDiagonalLower p ≤ J.a := by
    dsimp only [J, interiorLoopJacobian, policyDiagonalLower]
    have := mul_le_mul_of_nonneg_left hx.2.2 hk
    linarith
  have hd : stockDiagonalLower p ≤ J.d := by
    dsimp only [J, interiorLoopJacobian, stockDiagonalLower]
    exact (driftStockMultiplier_strictMonoOn model).monotoneOn
      (by norm_num) hx.1 hx.1.1
  have hb : J.b ≤ policyStockUpper p := by
    have hcx : 0 ≤ p.c * x.1 := mul_nonneg model.c_pos.le hx.1.1
    have hcoef : 0 ≤ 2 * p.α * p.c :=
      mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) model.c_pos.le
    dsimp only [J, interiorLoopJacobian, policyStockUpper]
    nlinarith [mul_le_mul_of_nonneg_left
      (show 1 - p.c * x.1 ≤ 1 by linarith) hcoef]
  have hslopeNonneg : 0 ≤ p.sSlope x.1 := by
    simp only [LoopParams.sSlope]
    have hinner : 0 ≤ 1 - p.η * (1 - x.1) := by
      have hresidual : 1 - x.1 ≤ 1 := by linarith [hx.1.1]
      have hmul := mul_le_mul_of_nonneg_left hresidual model.η_pos.le
      nlinarith [model.η_le_one]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) model.η_pos.le)
        (sub_nonneg.mpr model.lambda₀_lt_one.le)) hinner
  have hslopeSharp : p.sSlope x.1 ≤ 2 * p.η * (1 - p.lambda₀) := by
    have hinnerLe : 1 - p.η * (1 - x.1) ≤ 1 := by
      exact sub_le_self _ (mul_nonneg model.η_pos.le (sub_nonneg.mpr hx.1.2))
    have hcoef : 0 ≤ 2 * p.η * (1 - p.lambda₀) :=
      mul_nonneg (mul_nonneg (by norm_num) model.η_pos.le)
        (sub_nonneg.mpr model.lambda₀_lt_one.le)
    simp only [LoopParams.sSlope]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hinnerLe hcoef
  have hcJ : J.cJ ≤ stockPolicyUpper p := by
    have hcoef : 0 ≤ 2 * p.η * (1 - p.lambda₀) :=
      mul_nonneg (mul_nonneg (by norm_num) model.η_pos.le)
        (sub_nonneg.mpr model.lambda₀_lt_one.le)
    have hproduct := mul_le_mul hslopeSharp hx.2.2
      (model.I_pos.le.trans hx.2.1) hcoef
    dsimp only [J, interiorLoopJacobian, stockPolicyUpper]
    exact hproduct
  have haPos := ssplus.policyDiagonalLower_pos model
  have hdPos := ssplus.stockDiagonalLower_pos model
  have hbNonneg : 0 ≤ J.b := by
    dsimp only [J, interiorLoopJacobian]
    have hcβ : p.c * x.1 < 1 := calc
      p.c * x.1 ≤ p.c * 1 := mul_le_mul_of_nonneg_left hx.1.2 model.c_pos.le
      _ = p.c := mul_one _
      _ < 1 := model.c_lt_one
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) model.c_pos.le)
      (sub_nonneg.mpr hcβ.le)
  have hcJNonneg : 0 ≤ J.cJ := by
    dsimp only [J, interiorLoopJacobian]
    exact mul_nonneg hslopeNonneg (model.I_pos.le.trans hx.2.1)
  have hdiag : policyDiagonalLower p * stockDiagonalLower p ≤ J.a * J.d :=
    mul_le_mul ha hd hdPos.le (haPos.trans_le ha).le
  have hcross : J.b * J.cJ ≤ policyStockUpper p * stockPolicyUpper p :=
    mul_le_mul hb hcJ hcJNonneg
      (by exact (policyStockUpper_pos model).le)
  have hdom := ssplus.crossProduct_lt_diagonalProduct model
  simp only [LoopJacobian.det]
  linarith

/-- At the saddle, the second explicit eigenvalue lies strictly between zero
and one under `(SS⁺)`. -/
theorem saddle_smallerEigenvalue_mem_Ioo_zero_one {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) :
    let J := interiorLoopJacobian p threshold.βdagger
      (p.stationaryStock threshold.βdagger)
    J.smallerEigenvalue ∈ Ioo (0 : ℝ) 1 := by
  let β := threshold.βdagger
  let D := p.stationaryStock β
  let J := interiorLoopJacobian p β D
  have hβ : β ∈ Icc (0 : ℝ) 1 :=
    ⟨threshold.βdagger_mem.1.le, threshold.βdagger_mem.2.le⟩
  have hD := stationaryStock_mem_stockInterval model hβ
  have hdet : 0 < J.det := by
    simpa only [J, β, D] using
      (interiorLoopJacobian_det_pos_on_box model ssplus
        (x := (β, D)) ⟨hβ, hD⟩)
  have hJpos := saddleJacobian_entry_pos model ssplus threshold
  have hdisc : 0 ≤ J.discriminant :=
    J.discriminant_nonneg hJpos.2.1.le hJpos.2.2.1.le
  have hlarger := saddle_largerEigenvalue_gt_one model ssplus threshold
  have hfactor := J.charPoly_eq_mul_eigenvalues hdisc 0
  have hproduct : J.det = J.largerEigenvalue * J.smallerEigenvalue := by
    simpa [LoopJacobian.charPoly] using hfactor
  have hlarger' : 1 < J.largerEigenvalue := by
    simpa only [J, β, D] using hlarger
  have hsmallPos : 0 < J.smallerEigenvalue := by
    rw [hproduct] at hdet
    rcases mul_pos_iff.mp hdet with hpos | hneg
    · exact hpos.2
    · linarith [hlarger', hneg.1]
  exact ⟨hsmallPos, saddle_smallerEigenvalue_lt_one model
    (ssplus.toStrictSmallStep model) threshold⟩

/-- Under `(SS⁺)`, the interior crossing is hyperbolic in the literal
two-dimensional sense: one real multiplier is above one and the other lies
strictly between zero and one. -/
theorem bistability_saddle_hyperbolic_spectrum {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) :
    let J := interiorLoopJacobian p threshold.βdagger
      (p.stationaryStock threshold.βdagger)
    1 < J.largerEigenvalue ∧ J.smallerEigenvalue ∈ Ioo (0 : ℝ) 1 :=
  ⟨saddle_largerEigenvalue_gt_one model ssplus threshold,
    saddle_smallerEigenvalue_mem_Ioo_zero_one model ssplus threshold⟩

#print axioms civicWeightedLoopMap_zero
#print axioms IsLoopTrajectory.toCivicWeightedZero
#print axioms IsLoopTrajectory.toCivicWeightedZeroSchedule
#print axioms calibratedPoint_localAttraction
#print axioms capturedPoint_localAttraction
#print axioms bistability_cornerAttractors
#print axioms loopOrbit_isTrajectory
#print axioms loopOrbit_mem_absorbingBox
#print axioms continuous_loopIterateOnBox
#print axioms loopOrbit_from_iterate
#print axioms loopOrbit_tendsto_iff_tail
#print axioms loopBasinInBox_isOpen_of_attractingNeighborhood
#print axioms calibratedBasinInBox_isOpen
#print axioms capturedBasinInBox_isOpen
#print axioms mem_calibrated_or_saddle_or_captured_basin
#print axioms loopBasinInBox_disjoint_of_ne
#print axioms calibratedPoint_ne_saddlePoint
#print axioms saddlePoint_ne_capturedPoint
#print axioms calibratedPoint_ne_capturedPoint
#print axioms bistableBasins_pairwiseDisjoint
#print axioms mem_loopBasinInBox_map_iff
#print axioms saddleStableSetInBox_invariant
#print axioms saddleStableSetInBox_eq_compl_cornerBasins
#print axioms saddleStableSetInBox_isClosed
#print axioms orderedDifferenceCoefficients_self
#print axioms continuous_orderedDifferenceCoefficients_a
#print axioms continuous_orderedDifferenceCoefficients_b
#print axioms continuous_orderedDifferenceCoefficients_cJ
#print axioms continuous_orderedDifferenceCoefficients_d
#print axioms loopMap_orderedDifference_eq
#print axioms loopOrbit_mono_of_le
#print axioms loopMap_stock_lt_of_le_of_ne
#print axioms loopOrbit_stock_lt_of_le_of_ne
#print axioms saddleExpansionScale_spec
#print axioms unstableFunctional_jacobian
#print axioms unstableFunctional_scaled_jacobian
#print axioms saddleJacobian_entry_pos
#print axioms saddle_largerEigenvalue_gt_one
#print axioms ordered_saddle_orbits_eventually_functional_mono
#print axioms saddleStableSetInBox_ordered_eq
#print axioms saddleStableSetInBox_isAntichain
#print axioms exists_nearby_comparable_in_loopBox
#print axioms saddleStableSetInBox_interior_eq_empty
#print axioms saddlePointInBox_mem_stable
#print axioms saddleStablePoint_has_lower_room
#print axioms saddleStablePoint_has_upper_room
#print axioms exists_nearby_above_stablePoint
#print axioms exists_nearby_below_stablePoint
#print axioms loopOrbit_limit_le_limit
#print axioms above_stablePoint_mem_capturedBasin
#print axioms below_stablePoint_mem_calibratedBasin
#print axioms saddleStableSetInBox_subset_closure_capturedBasin
#print axioms saddleStableSetInBox_subset_closure_calibratedBasin
#print axioms closure_calibratedBasinInBox_eq
#print axioms closure_capturedBasinInBox_eq
#print axioms frontier_calibratedBasinInBox_eq
#print axioms frontier_capturedBasinInBox_eq
#print axioms bistability_commonBasinBoundary
#print axioms compl_saddleStableSetInBox_eq_cornerBasins
#print axioms interiorLoopJacobian_det_pos_on_box
#print axioms saddle_smallerEigenvalue_mem_Ioo_zero_one
#print axioms bistability_saddle_hyperbolic_spectrum

end


end CivicAlignment.PaperII
