/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.ArrheniusProcess

/-!
# Paper II: deterministic funnel substrate for the Arrhenius law

The fixed-window quasipotential argument starts every controlled path at the
calibrated corner.  The block and last-exit arguments for `thm:arr` instead
restart at random intermediate states.  This file supplies the corresponding
general-initial-state path interface, its stock envelope, the exact zero-control
bridge, and the uniform deterministic funnel dominated by one point on the
stationary characteristic.
-/

namespace CivicAlignment.PaperII

open Filter Function Set Topology
open scoped BigOperators Interval

noncomputable section

/-! ## Controlled paths from an arbitrary state -/

/-- The paper's absorbing rectangle is compact. -/
theorem isCompact_absorbingBox (p : LoopParams) :
    IsCompact (absorbingBox p) := by
  simpa only [absorbingBox] using
    (isCompact_Icc.prod isCompact_Icc :
      IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc p.I (p.I / p.lambda₀)))

/-- A controlled civic-weighted path with an explicit initial state. -/
structure IsControlledCivicWeightedPathFrom (p : LoopParams) (rho : ℝ)
    (x₀ : LoopState) (u : ℕ → ℝ) (x : ℕ → LoopState) : Prop where
  initial : x 0 = x₀
  step : ∀ n, x (n + 1) = controlledCivicWeightedStep p rho (u n) (x n)

/-- The canonical controlled recursion from an arbitrary initial state. -/
def controlledCivicWeightedOrbitFrom (p : LoopParams) (rho : ℝ)
    (x₀ : LoopState) (u : ℕ → ℝ) : ℕ → LoopState
  | 0 => x₀
  | n + 1 => controlledCivicWeightedStep p rho (u n)
      (controlledCivicWeightedOrbitFrom p rho x₀ u n)

/-- A finite control history driving the recursion from an arbitrary state,
continued by zero control after its horizon. -/
def finiteControlledOrbitFrom (p : LoopParams) (rho : ℝ) (x₀ : LoopState)
    {T : ℕ} (u : Fin T → ℝ) : ℕ → LoopState
  | 0 => x₀
  | n + 1 => controlledCivicWeightedStep p rho (extendFiniteControl u n)
      (finiteControlledOrbitFrom p rho x₀ u n)

/-- The canonical arbitrary-start recursion satisfies its path predicate. -/
theorem controlledCivicWeightedOrbitFrom_isControlled (p : LoopParams)
    (rho : ℝ) (x₀ : LoopState) (u : ℕ → ℝ) :
    IsControlledCivicWeightedPathFrom p rho x₀ u
      (controlledCivicWeightedOrbitFrom p rho x₀ u) where
  initial := rfl
  step _ := rfl

/-- The finite-history arbitrary-start recursion satisfies its path
predicate. -/
theorem finiteControlledOrbitFrom_isControlled (p : LoopParams) (rho : ℝ)
    (x₀ : LoopState) {T : ℕ} (u : Fin T → ℝ) :
    IsControlledCivicWeightedPathFrom p rho x₀ (extendFiniteControl u)
      (finiteControlledOrbitFrom p rho x₀ u) where
  initial := rfl
  step _ := rfl

/-- At a fixed time, the finite-history endpoint depends jointly continuously
on the initial state and the finite control vector. -/
theorem continuous_finiteControlledOrbitFrom (p : LoopParams) (rho : ℝ)
    {T : ℕ} (n : ℕ) :
    Continuous (fun z : LoopState × (Fin T → ℝ) ↦
      finiteControlledOrbitFrom p rho z.1 z.2 n) := by
  induction n with
  | zero =>
      simp only [finiteControlledOrbitFrom]
      fun_prop
  | succ n ih =>
      simp only [finiteControlledOrbitFrom]
      unfold controlledCivicWeightedStep civicWeightedGradient
        LoopParams.gradU LoopParams.stockStep LoopParams.s LoopParams.clipUnit
        extendFiniteControl
      split <;> fun_prop

/-- On a compact set of initial states, sufficiently small finite controls
keep every fixed-horizon endpoint uniformly close to its zero-control
endpoint.  This is the persistence argument's start-uniform deterministic
tube; compactness is used only here. -/
theorem exists_uniform_finiteControl_radius
    (p : LoopParams) (rho : ℝ) {T : ℕ} {K : Set LoopState}
    (hK : IsCompact K) (N : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ r : ℝ, 0 < r ∧
      ∀ x₀ ∈ K, ∀ u : Fin T → ℝ,
        dist u 0 < r →
          dist (finiteControlledOrbitFrom p rho x₀ (0 : Fin T → ℝ) N)
            (finiteControlledOrbitFrom p rho x₀ u N) < epsilon := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : (Fin T → ℝ) → K → LoopState := fun u x₀ ↦
    finiteControlledOrbitFrom p rho x₀.1 u N
  have hswap : Continuous (fun z : (Fin T → ℝ) × K ↦
      ((z.2.1, z.1) : LoopState × (Fin T → ℝ))) := by
    fun_prop
  have hcontinuous : Continuous (Function.uncurry F) := by
    exact (continuous_finiteControlledOrbitFrom p rho N).comp hswap
  have huniform : TendstoUniformly F (F 0) (nhds 0) :=
    Continuous.tendstoUniformly F hcontinuous 0
  have heventually : ∀ᶠ u in nhds (0 : Fin T → ℝ),
      ∀ x₀ : K, dist (F 0 x₀) (F u x₀) < epsilon :=
    (Metric.tendstoUniformly_iff.mp huniform) epsilon hepsilon
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp heventually
  refine ⟨r, hr, fun x₀ hx₀ u hu ↦ ?_⟩
  exact hball hu ⟨x₀, hx₀⟩

/-- A fixed-horizon endpoint deviation from the zero-control comparison costs
a uniform positive action over a compact set of starts.  This is the abstract
quiet-block charge of the persistence accounting. -/
theorem exists_uniform_action_cost_of_endpoint_deviation
    (p : LoopParams) (rho : ℝ) {T : ℕ} {K : Set LoopState}
    (hK : IsCompact K) (N : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ c : ℝ, 0 < c ∧
      ∀ x₀ ∈ K, ∀ u : Fin T → ℝ,
        epsilon ≤ dist
          (finiteControlledOrbitFrom p rho x₀ (0 : Fin T → ℝ) N)
          (finiteControlledOrbitFrom p rho x₀ u N) →
        c ≤ gaussianVectorAction u := by
  obtain ⟨r, hr, hclose⟩ :=
    exists_uniform_finiteControl_radius p rho hK N hepsilon
  refine ⟨r ^ 2 / 2, div_pos (sq_pos_of_pos hr) (by norm_num), ?_⟩
  intro x₀ hx₀ u hdeviation
  have hcontrol : r ≤ dist u 0 := by
    by_contra hnot
    have hlt : dist u 0 < r := lt_of_not_ge hnot
    exact (not_lt_of_ge hdeviation) (hclose x₀ hx₀ u hlt)
  have hcoordinate : ∃ i : Fin T, r ≤ |u i| := by
    by_contra hnot
    simp only [not_exists, not_le] at hnot
    have hall : ∀ i : Fin T,
        dist (u i) ((0 : Fin T → ℝ) i) < r := by
      intro i
      simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using hnot i
    exact (not_lt_of_ge hcontrol) ((dist_pi_lt_iff hr).2 hall)
  obtain ⟨i, hi⟩ := hcoordinate
  have hsquare : r ^ 2 ≤ (u i) ^ 2 := by
    rw [← sq_abs (u i)]
    exact (sq_le_sq₀ hr.le (abs_nonneg (u i))).2 hi
  have hterm : (u i) ^ 2 ≤ ∑ j : Fin T, (u j) ^ 2 :=
    Finset.single_le_sum (fun j _hj ↦ sq_nonneg (u j))
      (Finset.mem_univ i)
  simp only [gaussianVectorAction]
  nlinarith

/-- Restricting an arbitrary-start controlled path's controls reproduces that
path through the restriction horizon. -/
theorem finiteControlledOrbitFrom_restrict_eq
    {p : LoopParams} {rho : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    {T n : ℕ} (hn : n ≤ T) :
    finiteControlledOrbitFrom p rho x₀ (fun i : Fin T ↦ u i) n = x n := by
  induction n with
  | zero => simpa only [finiteControlledOrbitFrom] using path.initial.symm
  | succ n ih =>
      have hnlt : n < T := by omega
      rw [finiteControlledOrbitFrom, path.step n, ih (by omega)]
      simp only [extendFiniteControl, hnlt, dite_true]

/-- Once a finite arbitrary-start history is exhausted, its continuation is
the unforced weighted orbit from the terminal state. -/
theorem finiteControlledOrbitFrom_tail
    (p : LoopParams) (rho : ℝ) (x₀ : LoopState)
    {T : ℕ} (u : Fin T → ℝ) (k : ℕ) :
    finiteControlledOrbitFrom p rho x₀ u (T + k) =
      civicWeightedOrbit p rho (finiteControlledOrbitFrom p rho x₀ u T) k := by
  induction k with
  | zero =>
      simp only [Nat.add_zero, civicWeightedOrbit,
        Function.iterate_zero_apply]
  | succ k ih =>
      rw [Nat.add_succ, finiteControlledOrbitFrom, ih]
      have hnot : ¬T + k < T := by omega
      simp only [extendFiniteControl, hnot, dite_false,
        controlledCivicWeightedStep, civicWeightedOrbit,
        Function.iterate_succ_apply', civicWeightedLoopMap,
        civicWeightedDeferenceStep, civicWeightedInput, add_zero]

/-- At the calibrated start, the general finite recursion agrees with the
fixed-start recursion used by `EscapeWindow`. -/
theorem finiteControlledOrbitFrom_calibratedPoint
    (p : LoopParams) (rho : ℝ) {T : ℕ} (u : Fin T → ℝ) (n : ℕ) :
    finiteControlledOrbitFrom p rho (calibratedPoint p) u n =
      finiteControlledOrbit p rho u n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [finiteControlledOrbitFrom, finiteControlledOrbit, ih]

/-- A zero finite control vector produces the unforced orbit from the same
initial state. -/
theorem finiteControlledOrbitFrom_zero_eq_civicWeightedOrbit
    (p : LoopParams) (rho : ℝ) (x₀ : LoopState) {T : ℕ} (n : ℕ) :
    finiteControlledOrbitFrom p rho x₀ (0 : Fin T → ℝ) n =
      civicWeightedOrbit p rho x₀ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [finiteControlledOrbitFrom]
      have hzero : extendFiniteControl (0 : Fin T → ℝ) n = 0 := by
        simp only [extendFiniteControl]
        split <;> simp
      rw [hzero, ih]
      simp only [controlledCivicWeightedStep, civicWeightedOrbit,
        Function.iterate_succ_apply', civicWeightedLoopMap,
        civicWeightedDeferenceStep, civicWeightedInput, add_zero]

/-- A path from the calibrated corner is an arbitrary-start path with that
corner supplied explicitly. -/
theorem IsControlledCivicWeightedPath.toFrom {p : LoopParams} {rho : ℝ}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (path : IsControlledCivicWeightedPath p rho u x) :
    IsControlledCivicWeightedPathFrom p rho (calibratedPoint p) u x :=
  ⟨path.initial, path.step⟩

/-- Restarting a controlled path at time `N` gives a controlled path from the
state reached at that time. -/
theorem IsControlledCivicWeightedPathFrom.tail
    {p : LoopParams} {rho : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x) (N : ℕ) :
    IsControlledCivicWeightedPathFrom p rho (x N) (fun n ↦ u (N + n))
      (fun n ↦ x (N + n)) := by
  constructor
  · simp
  · intro n
    simpa only [Nat.add_assoc] using path.step (N + n)

/-- Every post-initial policy coordinate is projected; if the initial policy
is in the unit interval, every policy coordinate is. -/
theorem IsControlledCivicWeightedPathFrom.policy_mem
    {p : LoopParams} {rho : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    (x n).1 ∈ Icc (0 : ℝ) 1 := by
  cases n with
  | zero => simpa only [path.initial] using hx₀
  | succ n =>
      rw [path.step n]
      exact LoopParams.clipUnit_mem _

/-- An arbitrary-start controlled path remains in the absorbing box whenever
its initial state lies there. -/
theorem IsControlledCivicWeightedPathFrom.mem_absorbingBox
    {p : LoopParams} {rho : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p) (n : ℕ) :
    x n ∈ absorbingBox p := by
  induction n with
  | zero => simpa only [path.initial] using hx₀
  | succ n ih =>
      rw [path.step n]
      have hnext := civicWeightedInvariantBox model rho ih
      exact ⟨LoopParams.clipUnit_mem _, by
        simpa only [controlledCivicWeightedStep, civicWeightedLoopMap,
          Prod.snd] using hnext.2⟩

/-- The running policy maximum of an arbitrary-start path stays in the unit
interval. -/
theorem IsControlledCivicWeightedPathFrom.runningMax_mem
    {p : LoopParams} {rho : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    policyRunningMax x n ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact le_runningMax_of_le_zero
      (show (0 : ℝ) ≤ (x 0).1 by simpa only [path.initial] using hx₀.1) n
  · apply runningMax_le_of_forall_le
    intro k _hk
    exact (path.policy_mem hx₀ k).2

/-- A lower calibrated-corner bound is preserved by every controlled path
from an arbitrary state.  Controls affect policy, whose projection is always
nonnegative; the stock comparison is inherited from the unforced map. -/
theorem IsControlledCivicWeightedPathFrom.calibratedPoint_le
    {p : LoopParams} {rho : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p) (hlower₀ : calibratedPoint p ≤ x₀)
    (n : ℕ) : calibratedPoint p ≤ x n := by
  have hzero : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hp₁mem : calibratedPoint p ∈ absorbingBox p :=
    ⟨by simp [calibratedPoint],
      stationaryStock_mem_stockInterval model hzero⟩
  have hstockFixed := stationaryStock_fixed model hzero
  induction n with
  | zero => simpa only [path.initial] using hlower₀
  | succ n ih =>
      have hxmem := path.mem_absorbingBox model hx₀ n
      have hstockMono := (loopMap_monotoneOn_box model ss hp₁mem hxmem ih).2
      rw [path.step n]
      constructor
      · exact (LoopParams.clipUnit_mem _).1
      · calc
          (calibratedPoint p).2 =
              p.stockStep 0 (p.stationaryStock 0) := by
            simpa only [calibratedPoint] using hstockFixed.symm
          _ ≤ p.stockStep (x n).1 (x n).2 := by
            simpa only [LoopParams.loopMap, calibratedPoint] using hstockMono
          _ = (controlledCivicWeightedStep p rho (u n) (x n)).2 := rfl

/-- If the initial stock is below the stationary stock at the initial policy,
then the exact stock recursion stays below the stationary characteristic at
the running policy maximum.  This is the arbitrary-start version of the
pre-crossing compact-rectangle estimate. -/
theorem IsControlledCivicWeightedPathFrom.stock_le_stationary_runningMax
    {p : LoopParams} {rho : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hstock₀ : x₀.2 ≤ p.stationaryStock x₀.1) (n : ℕ) :
    (x n).2 ≤ p.stationaryStock (policyRunningMax x n) := by
  induction n with
  | zero =>
      simpa only [policyRunningMax, runningMax, path.initial] using hstock₀
  | succ n ih =>
      let m := policyRunningMax x n
      let m' := policyRunningMax x (n + 1)
      have hm := path.runningMax_mem hx₀.1 n
      have hm' := path.runningMax_mem hx₀.1 (n + 1)
      have hxmem := path.mem_absorbingBox model hx₀ n
      have hupperMem : (m, p.stationaryStock m) ∈ absorbingBox p :=
        ⟨hm, stationaryStock_mem_stockInterval model hm⟩
      have hxle : x n ≤ (m, p.stationaryStock m) :=
        ⟨policy_le_runningMax x n, ih⟩
      have hstep := (loopMap_monotoneOn_box model ss hxmem hupperMem hxle).2
      have hfixed := stationaryStock_fixed model hm
      have hstockToM :
          p.stockStep (x n).1 (x n).2 ≤ p.stationaryStock m := by
        calc
          p.stockStep (x n).1 (x n).2 ≤
              p.stockStep m (p.stationaryStock m) := by
            simpa only [LoopParams.loopMap] using hstep
          _ = p.stationaryStock m := hfixed
      have hmm' : m ≤ m' :=
        (monotone_runningMax (fun k ↦ (x k).1)) n.le_succ
      have hcharacteristic : p.stationaryStock m ≤ p.stationaryStock m' :=
        (stationaryStock_strictMonoOn model).monotoneOn hm hm' hmm'
      rw [path.step n]
      exact hstockToM.trans hcharacteristic

/-- If policy stays below `b` for `n` steps, stock excess over the stationary
stock at `b` contracts at the geometric rate `s(b)`.  This estimate permits
elevated-stock histories. -/
theorem IsControlledCivicWeightedPathFrom.stock_excess_le_geometric_of_policy_le
    {p : LoopParams} {rho b : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p) (hb : b ∈ Icc (0 : ℝ) 1)
    (n : ℕ) (hpolicy : ∀ k < n, (x k).1 ≤ b) :
    (x n).2 - p.stationaryStock b ≤
      (p.s b) ^ n * (x₀.2 - p.stationaryStock b) := by
  induction n with
  | zero =>
      rw [path.initial]
      simp only [pow_zero, one_mul]
      exact le_rfl
  | succ n ih =>
      have hpolicyBefore : ∀ k < n, (x k).1 ≤ b := by
        intro k hk
        exact hpolicy k (hk.trans (Nat.lt_succ_self n))
      have hinduction := ih hpolicyBefore
      have hxmem := path.mem_absorbingBox model hx₀ n
      have hxpolicy := hxmem.1
      have hsle : p.s (x n).1 ≤ p.s b :=
        (driftStockMultiplier_strictMonoOn model).monotoneOn
          hxpolicy hb (hpolicy n (Nat.lt_succ_self n))
      have hxstockNonneg : 0 ≤ (x n).2 :=
        model.I_pos.le.trans hxmem.2.1
      have hproduct : p.s (x n).1 * (x n).2 ≤ p.s b * (x n).2 :=
        mul_le_mul_of_nonneg_right hsle hxstockNonneg
      have hfixed := stationaryStock_fixed model hb
      have hstep : (x (n + 1)).2 - p.stationaryStock b ≤
          p.s b * ((x n).2 - p.stationaryStock b) := by
        rw [path.step n]
        simp only [controlledCivicWeightedStep, LoopParams.stockStep,
          model.no_content_gain, add_zero] at hfixed ⊢
        nlinarith
      have hmultiplied :
          p.s b * ((x n).2 - p.stationaryStock b) ≤
            p.s b * ((p.s b) ^ n *
              (x₀.2 - p.stationaryStock b)) :=
        mul_le_mul_of_nonneg_left hinduction
          (driftStockMultiplier_nonneg_le model hb).1
      calc
        (x (n + 1)).2 - p.stationaryStock b ≤
            p.s b * ((x n).2 - p.stationaryStock b) := hstep
        _ ≤ p.s b * ((p.s b) ^ n *
            (x₀.2 - p.stationaryStock b)) := hmultiplied
        _ = (p.s b) ^ (n + 1) *
            (x₀.2 - p.stationaryStock b) := by ring

/-- If the initial stock is already below `D*(b)` and policy stays below `b`,
then the stock remains below `D*(b)`.  This is the exact case-B invariant. -/
theorem IsControlledCivicWeightedPathFrom.stock_le_stationary_of_policy_le
    {p : LoopParams} {rho b : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p) (hb : b ∈ Icc (0 : ℝ) 1)
    (hstock₀ : x₀.2 ≤ p.stationaryStock b)
    (n : ℕ) (hpolicy : ∀ k < n, (x k).1 ≤ b) :
    (x n).2 ≤ p.stationaryStock b := by
  have hdecay := path.stock_excess_le_geometric_of_policy_le
    model hx₀ hb n hpolicy
  have hpow : 0 ≤ (p.s b) ^ n :=
    pow_nonneg (driftStockMultiplier_nonneg_le model hb).1 n
  have hright : (p.s b) ^ n *
      (x₀.2 - p.stationaryStock b) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hpow (sub_nonpos.mpr hstock₀)
  linarith

/-- There is a horizon, uniform over all starts in the absorbing box, by
which stock is within `epsilon` above `D*(b)` unless policy has exceeded `b`.
This is the quantitative transition from elevated stock into the funnel. -/
theorem exists_uniform_stock_contraction_time
    {p : LoopParams} {b epsilon : ℝ}
    (model : DriftModelAssumptions p) (hb : b ∈ Icc (0 : ℝ) 1)
    (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ (rho : ℝ) (x₀ : LoopState) (u : ℕ → ℝ)
      (x : ℕ → LoopState),
      IsControlledCivicWeightedPathFrom p rho x₀ u x →
      x₀ ∈ absorbingBox p →
      (∀ k < N, (x k).1 ≤ b) →
      (x N).2 ≤ p.stationaryStock b + epsilon := by
  have hs := driftStockMultiplier_nonneg_le model hb
  have hslt : p.s b < 1 := hs.2.trans_lt (by
    linarith [model.lambda₀_pos])
  have hpow : Tendsto
      (fun n : ℕ ↦ (p.s b) ^ n * (p.I / p.lambda₀))
      atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hs.1 hslt).mul_const
        (p.I / p.lambda₀)
  have heventually : ∀ᶠ n in atTop,
      (p.s b) ^ n * (p.I / p.lambda₀) < epsilon :=
    (tendsto_order.1 hpow).2 epsilon hepsilon
  obtain ⟨N, hN⟩ := eventually_atTop.1 heventually
  refine ⟨N, fun rho x₀ u x path hx₀ hpolicy ↦ ?_⟩
  have hdecay := path.stock_excess_le_geometric_of_policy_le
    model hx₀ hb N hpolicy
  have hstationaryNonneg : 0 ≤ p.stationaryStock b :=
    model.I_pos.le.trans (stationaryStock_mem_stockInterval model hb).1
  have hinitialDifference :
      x₀.2 - p.stationaryStock b ≤ p.I / p.lambda₀ := by
    linarith [hx₀.2.2]
  have hpowNonneg : 0 ≤ (p.s b) ^ N := pow_nonneg hs.1 N
  have hbounded :
      (p.s b) ^ N * (x₀.2 - p.stationaryStock b) ≤
        (p.s b) ^ N * (p.I / p.lambda₀) :=
    mul_le_mul_of_nonneg_left hinitialDifference hpowNonneg
  have hsmall := hN N le_rfl
  linarith

/-! ## The capped-maximum ledger from an arbitrary start -/

/-- Every stopped running maximum of an arbitrary-start path lies on the
closed saddle segment. -/
theorem IsControlledCivicWeightedPathFrom.cappedRunningMax_mem
    {p : LoopParams} {rho : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    cappedPolicyRunningMax weighted.βdagger x n ∈
      Icc (0 : ℝ) weighted.βdagger := by
  have hrun := path.runningMax_mem hx₀ n
  exact ⟨le_min weighted.βdagger_mem.1.le hrun.1, min_le_left _ _⟩

/-- The arbitrary-start stock envelope gives the same running-maximum
gradient estimate as the calibrated-start ledger. -/
theorem IsControlledCivicWeightedPathFrom.gradient_le_runningMax
    {p : LoopParams} {rho : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hstock₀ : x₀.2 ≤ p.stationaryStock x₀.1) (n : ℕ) :
    civicWeightedGradient p rho (x n).1 (x n).2 ≤
      weightedStationaryGradient p rho (policyRunningMax x n) +
        2 * p.c ^ 2 * p.stationaryStock (policyRunningMax x n) *
          (policyRunningMax x n - (x n).1) := by
  let beta := (x n).1
  let D := (x n).2
  let b := policyRunningMax x n
  have hbeta := path.policy_mem hx₀.1 n
  have hb := path.runningMax_mem hx₀.1 n
  have hD := path.stock_le_stationary_runningMax model ss hx₀ hstock₀ n
  have hcoef := weighted_stock_coefficient_nonnegative model hcoop hbeta
  have hmul :
      (2 * p.c * (1 - p.c * beta) - rho) * D ≤
        (2 * p.c * (1 - p.c * beta) - rho) * p.stationaryStock b :=
    mul_le_mul_of_nonneg_left hD hcoef
  calc
    civicWeightedGradient p rho beta D =
        -p.v + (2 * p.c * (1 - p.c * beta) - rho) * D := by
      simp only [civicWeightedGradient, LoopParams.gradU]
      ring
    _ ≤ -p.v + (2 * p.c * (1 - p.c * beta) - rho) *
        p.stationaryStock b := by linarith
    _ = weightedStationaryGradient p rho b +
        2 * p.c ^ 2 * p.stationaryStock b * (b - beta) := by
      rw [← civicWeightedGradient_stationary_eq_weightedStationaryGradient
        rho hb]
      simp only [civicWeightedGradient, LoopParams.gradU]
      ring

/-- On a step which advances the stopped maximum, an arbitrary-start path's
control pays the same local barrier-plus-advance charge. -/
theorem IsControlledCivicWeightedPathFrom.control_ge_barrier_add_advance
    {p : LoopParams} {rho : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hstock₀ : x₀.2 ≤ p.stationaryStock x₀.1) {n : ℕ}
    (hadvance : cappedPolicyRunningMax weighted.βdagger x n <
      cappedPolicyRunningMax weighted.βdagger x (n + 1)) :
    weightedBarrierIntegrand p rho
        (cappedPolicyRunningMax weighted.βdagger x n) +
      (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
          cappedPolicyRunningMax weighted.βdagger x n) / p.α ≤ u n := by
  let b := cappedPolicyRunningMax weighted.βdagger x n
  let b' := cappedPolicyRunningMax weighted.βdagger x (n + 1)
  let beta := (x n).1
  let D := (x n).2
  obtain ⟨hold, hnewPolicy⟩ := cappedRunningMax_advance_structure hadvance
  have hbRunning : b = policyRunningMax x n := hold
  have hbmem : b ∈ Icc (0 : ℝ) 1 := by
    rw [hbRunning]
    exact path.runningMax_mem hx₀.1 n
  have hbetaMem := path.policy_mem hx₀.1 n
  have hbetaB : beta ≤ b := by
    rw [hbRunning]
    exact policy_le_runningMax x n
  have hbnonneg : 0 ≤ b := hbmem.1
  have hb'pos : 0 < b' := hbnonneg.trans_lt hadvance
  have hxnextPos : 0 < (x (n + 1)).1 := hb'pos.trans_le hnewPolicy
  have hxnext : (x (n + 1)).1 = LoopParams.clipUnit
      (beta + p.α * (civicWeightedGradient p rho beta D + u n)) := by
    have hstep := congrArg Prod.fst (path.step n)
    simpa only [controlledCivicWeightedStep] using hstep
  have hinput : b' ≤ beta + p.α *
      (civicWeightedGradient p rho beta D + u n) := by
    calc
      b' ≤ (x (n + 1)).1 := hnewPolicy
      _ = LoopParams.clipUnit
          (beta + p.α * (civicWeightedGradient p rho beta D + u n)) := hxnext
      _ ≤ beta + p.α * (civicWeightedGradient p rho beta D + u n) :=
        clipUnit_le_input_of_pos (by rwa [← hxnext])
  have hgradient : civicWeightedGradient p rho beta D ≤
      weightedStationaryGradient p rho b +
        2 * p.c ^ 2 * p.stationaryStock b * (b - beta) := by
    simpa only [hbRunning] using
      path.gradient_le_runningMax model ss hcoop hx₀ hstock₀ n
  have hsmall := two_alpha_c_sq_stationaryStock_le_one model ss hbmem
  have hdip : 0 ≤ b - beta := sub_nonneg.mpr hbetaB
  have hdipCoefficient :
      0 ≤ 1 - 2 * p.α * p.c ^ 2 * p.stationaryStock b := by
    linarith
  have hdipProduct := mul_nonneg hdipCoefficient hdip
  have halphaGradient :=
    mul_le_mul_of_nonneg_left hgradient model.α_pos.le
  have hcross :
      p.α * weightedBarrierIntegrand p rho b + (b' - b) ≤ p.α * u n := by
    simp only [weightedBarrierIntegrand]
    nlinarith
  have hdivide : p.α * ((b' - b) / p.α) = b' - b := by
    field_simp [model.α_pos.ne']
  nlinarith [model.α_pos]

/-- Each arbitrary-start advance pays its left-rectangle barrier charge. -/
theorem IsControlledCivicWeightedPathFrom.advance_barrier_le_half_control_sq
    {p : LoopParams} {rho : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hstock₀ : x₀.2 ≤ p.stationaryStock x₀.1) {n : ℕ}
    (hadvance : cappedPolicyRunningMax weighted.βdagger x n <
      cappedPolicyRunningMax weighted.βdagger x (n + 1)) :
    (2 / p.α) * weightedBarrierIntegrand p rho
        (cappedPolicyRunningMax weighted.βdagger x n) *
      (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
        cappedPolicyRunningMax weighted.βdagger x n) ≤ (u n) ^ 2 / 2 := by
  let b := cappedPolicyRunningMax weighted.βdagger x n
  let b' := cappedPolicyRunningMax weighted.βdagger x (n + 1)
  let a := weightedBarrierIntegrand p rho b
  let d := (b' - b) / p.α
  have hb_le_root : b < weighted.βdagger :=
    hadvance.trans_le (min_le_left _ _)
  have hbnonneg : 0 ≤ b := by
    have hrun := path.runningMax_mem hx₀.1 n
    exact le_min weighted.βdagger_mem.1.le hrun.1
  have hb_lt_one : b < 1 := hb_le_root.trans weighted.βdagger_mem.2
  have ha : 0 < a := by
    simp only [a, weightedBarrierIntegrand, neg_pos]
    by_cases hbzero : b = 0
    · simpa only [hbzero] using weighted.gradient_zero_neg
    · exact weighted.gradient_neg_before b
        ⟨lt_of_le_of_ne hbnonneg (Ne.symm hbzero), hb_lt_one⟩ hb_le_root
  have hdelta : 0 < b' - b := sub_pos.mpr hadvance
  have hd : 0 < d := div_pos hdelta model.α_pos
  have hu := path.control_ge_barrier_add_advance
    model ss hcoop weighted hx₀ hstock₀ hadvance
  have hsum : 0 ≤ a + d := by positivity
  have huNonneg : 0 ≤ u n := hsum.trans hu
  have hproduct : 0 ≤ (u n - (a + d)) * (u n + (a + d)) :=
    mul_nonneg (sub_nonneg.mpr hu) (add_nonneg huNonneg hsum)
  have hsquare := sq_nonneg (a - d)
  have hcore : 2 * a * d ≤ (u n) ^ 2 / 2 := by
    nlinarith
  calc
    (2 / p.α) * a * (b' - b) = 2 * a * d := by
      simp only [d]
      field_simp [model.α_pos.ne']
    _ ≤ (u n) ^ 2 / 2 := hcore

/-- The arbitrary-start advance ledger also holds on nonadvancing steps. -/
theorem IsControlledCivicWeightedPathFrom.barrier_increment_le_half_control_sq
    {p : LoopParams} {rho : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hstock₀ : x₀.2 ≤ p.stationaryStock x₀.1) (n : ℕ) :
    (2 / p.α) * weightedBarrierIntegrand p rho
        (cappedPolicyRunningMax weighted.βdagger x n) *
      (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
        cappedPolicyRunningMax weighted.βdagger x n) ≤ (u n) ^ 2 / 2 := by
  have hmono :=
    (monotone_cappedPolicyRunningMax weighted.βdagger x) n.le_succ
  rcases hmono.lt_or_eq with hadvance | heq
  · exact path.advance_barrier_le_half_control_sq
      model ss hcoop weighted hx₀ hstock₀ hadvance
  · rw [heq]
    simp only [sub_self, mul_zero]
    positivity

/-- The arbitrary-start stopped left sum is bounded by the finite action. -/
theorem IsControlledCivicWeightedPathFrom.sum_barrier_increments_le_action
    {p : LoopParams} {rho : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hstock₀ : x₀.2 ≤ p.stationaryStock x₀.1) (N : ℕ) :
    (2 / p.α) * ∑ n ∈ Finset.range N,
        weightedBarrierIntegrand p rho
            (cappedPolicyRunningMax weighted.βdagger x n) *
          (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
            cappedPolicyRunningMax weighted.βdagger x n) ≤
      controlAction u N := by
  rw [Finset.mul_sum]
  have hsum :
      ∑ n ∈ Finset.range N,
          (2 / p.α) *
            (weightedBarrierIntegrand p rho
                (cappedPolicyRunningMax weighted.βdagger x n) *
              (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
                cappedPolicyRunningMax weighted.βdagger x n)) ≤
        ∑ n ∈ Finset.range N, (u n) ^ 2 / 2 := by
    exact Finset.sum_le_sum fun n _hn ↦ by
      simpa only [mul_assoc] using
        path.barrier_increment_le_half_control_sq
          model ss hcoop weighted hx₀ hstock₀ n
  calc
    ∑ n ∈ Finset.range N,
        (2 / p.α) *
          (weightedBarrierIntegrand p rho
              (cappedPolicyRunningMax weighted.βdagger x n) *
            (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
              cappedPolicyRunningMax weighted.βdagger x n)) ≤
        ∑ n ∈ Finset.range N, (u n) ^ 2 / 2 := hsum
    _ = controlAction u N := by
      simp only [controlAction, div_eq_mul_inv, Finset.mul_sum]
      ring_nf

/-- Each squared stopped-maximum increment of an arbitrary-start path is
controlled by the corresponding squared control. -/
theorem IsControlledCivicWeightedPathFrom.capped_increment_sq_le_control_sq
    {p : LoopParams} {rho : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hstock₀ : x₀.2 ≤ p.stationaryStock x₀.1) (n : ℕ) :
    (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
        cappedPolicyRunningMax weighted.βdagger x n) ^ 2 ≤
      p.α ^ 2 * (u n) ^ 2 := by
  let b := cappedPolicyRunningMax weighted.βdagger x n
  let b' := cappedPolicyRunningMax weighted.βdagger x (n + 1)
  change (b' - b) ^ 2 ≤ p.α ^ 2 * (u n) ^ 2
  have hmono : b ≤ b' :=
    (monotone_cappedPolicyRunningMax weighted.βdagger x) n.le_succ
  rcases hmono.lt_or_eq with hadvance | heq
  · have hbmem := path.cappedRunningMax_mem weighted hx₀.1 n
    have hbarrier : 0 < weightedBarrierIntegrand p rho b :=
      weighted.barrier_pos_before hbmem
        (hadvance.trans_le (min_le_left _ _))
    have hu := path.control_ge_barrier_add_advance
      model ss hcoop weighted hx₀ hstock₀ hadvance
    have hdiv : (b' - b) / p.α ≤ u n := by linarith [hbarrier.le]
    have hdelta : b' - b ≤ p.α * u n := by
      have := (div_le_iff₀ model.α_pos).mp hdiv
      simpa only [mul_comm] using this
    have hdeltaNonneg : 0 ≤ b' - b := sub_nonneg.mpr hmono
    have huNonneg : 0 ≤ u n := by
      have hdivPos : 0 < (b' - b) / p.α :=
        div_pos (sub_pos.mpr hadvance) model.α_pos
      linarith
    have halphaUNonneg : 0 ≤ p.α * u n :=
      mul_nonneg model.α_pos.le huNonneg
    have hsquare : (b' - b) ^ 2 ≤ (p.α * u n) ^ 2 :=
      (sq_le_sq₀ hdeltaNonneg halphaUNonneg).2 hdelta
    nlinarith
  · rw [heq]
    simpa only [sub_self, pow_two, zero_mul] using
      mul_nonneg (sq_nonneg p.α) (sq_nonneg (u n))

/-- Sum of arbitrary-start squared maximum increments is controlled by the
finite action. -/
theorem IsControlledCivicWeightedPathFrom.sum_capped_increment_sq_le_action
    {p : LoopParams} {rho : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hstock₀ : x₀.2 ≤ p.stationaryStock x₀.1) (N : ℕ) :
    ∑ n ∈ Finset.range N,
        (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
          cappedPolicyRunningMax weighted.βdagger x n) ^ 2 ≤
      2 * p.α ^ 2 * controlAction u N := by
  calc
    ∑ n ∈ Finset.range N,
        (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
          cappedPolicyRunningMax weighted.βdagger x n) ^ 2 ≤
        ∑ n ∈ Finset.range N, p.α ^ 2 * (u n) ^ 2 := by
      exact Finset.sum_le_sum fun n _hn ↦
        path.capped_increment_sq_le_control_sq
          model ss hcoop weighted hx₀ hstock₀ n
    _ = 2 * p.α ^ 2 * controlAction u N := by
      simp only [controlAction, Finset.mul_sum]
      ring_nf

/-- A crossing arbitrary-start path partitions the barrier segment from its
initial stopped maximum to the saddle. -/
theorem IsControlledCivicWeightedPathFrom.barrier_integral_le_partition_of_crossing
    {p : LoopParams} {rho L : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p)
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) 1) {N : ℕ}
    (hcross : weighted.βdagger ≤ policyRunningMax x N) :
    (∫ b in cappedPolicyRunningMax weighted.βdagger x 0..
        weighted.βdagger, weightedBarrierIntegrand p rho b) ≤
      (∑ n ∈ Finset.range N,
        weightedBarrierIntegrand p rho
            (cappedPolicyRunningMax weighted.βdagger x n) *
          (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
            cappedPolicyRunningMax weighted.βdagger x n)) +
      (L / 2) * ∑ n ∈ Finset.range N,
        (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
          cappedPolicyRunningMax weighted.βdagger x n) ^ 2 := by
  let b : ℕ → ℝ := fun n ↦
    cappedPolicyRunningMax weighted.βdagger x n
  let f : ℝ → ℝ := weightedBarrierIntegrand p rho
  have hcont : ContinuousOn f (Icc (0 : ℝ) weighted.βdagger) :=
    continuousOn_weightedBarrierIntegrand model rho weighted
  have hbmem : ∀ n, b n ∈ Icc (0 : ℝ) weighted.βdagger :=
    fun n ↦ path.cappedRunningMax_mem weighted hx₀ n
  have hbmono : ∀ n, b n ≤ b (n + 1) := fun n ↦
    (monotone_cappedPolicyRunningMax weighted.βdagger x) n.le_succ
  have hcellInt : ∀ n < N, IntervalIntegrable f MeasureTheory.volume
      (b n) (b (n + 1)) := by
    intro n _hn
    have hsubset : [[b n, b (n + 1)]] ⊆
        Icc (0 : ℝ) weighted.βdagger := by
      rw [uIcc_of_le (hbmono n)]
      intro z hz
      exact ⟨(hbmem n).1.trans hz.1, hz.2.trans (hbmem (n + 1)).2⟩
    exact (hcont.mono hsubset).intervalIntegrable
  have hadjacent :
      ∑ n ∈ Finset.range N, ∫ z in b n..b (n + 1), f z =
        ∫ z in b 0..b N, f z :=
    intervalIntegral.sum_integral_adjacent_intervals hcellInt
  have hend : b N = weighted.βdagger :=
    cappedRunningMax_eq_target hcross
  have hcells :
      ∑ n ∈ Finset.range N, ∫ z in b n..b (n + 1), f z ≤
        ∑ n ∈ Finset.range N,
          (f (b n) * (b (n + 1) - b n) +
            (L / 2) * (b (n + 1) - b n) ^ 2) := by
    exact Finset.sum_le_sum fun n _hn ↦
      integral_le_left_rectangle_add_lipschitz hcont hL
        (hbmem n) (hbmem (n + 1)) (hbmono n)
  change (∫ z in b 0..weighted.βdagger, f z) ≤ _
  calc
    (∫ z in b 0..weighted.βdagger, f z) =
        ∑ n ∈ Finset.range N, ∫ z in b n..b (n + 1), f z := by
      rw [hadjacent, hend]
    _ ≤ ∑ n ∈ Finset.range N,
        (f (b n) * (b (n + 1) - b n) +
          (L / 2) * (b (n + 1) - b n) ^ 2) := hcells
    _ = (∑ n ∈ Finset.range N,
        f (b n) * (b (n + 1) - b n)) +
        (L / 2) * ∑ n ∈ Finset.range N,
          (b (n + 1) - b n) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Corrected from-start action lower bound for every saddle-crossing path.
Its barrier begins at the initial stopped running maximum, which is the exact
quantity needed after a last exit from the home neighborhood. -/
theorem IsControlledCivicWeightedPathFrom.action_lower_bound_of_crossing
    {p : LoopParams} {rho L : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hstock₀ : x₀.2 ≤ p.stationaryStock x₀.1) {N : ℕ}
    (hcross : weighted.βdagger ≤ policyRunningMax x N) :
    (2 / (p.α * (1 + 2 * p.α * L))) *
        (∫ b in cappedPolicyRunningMax weighted.βdagger x 0..
          weighted.βdagger, weightedBarrierIntegrand p rho b) ≤
      controlAction u N := by
  let R : ℝ := ∑ n ∈ Finset.range N,
    weightedBarrierIntegrand p rho
        (cappedPolicyRunningMax weighted.βdagger x n) *
      (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
        cappedPolicyRunningMax weighted.βdagger x n)
  let Q : ℝ := ∑ n ∈ Finset.range N,
    (cappedPolicyRunningMax weighted.βdagger x (n + 1) -
      cappedPolicyRunningMax weighted.βdagger x n) ^ 2
  let A : ℝ := controlAction u N
  let Ibar : ℝ := ∫ b in
    cappedPolicyRunningMax weighted.βdagger x 0..weighted.βdagger,
      weightedBarrierIntegrand p rho b
  have hpartition : Ibar ≤ R + (L / 2) * Q :=
    path.barrier_integral_le_partition_of_crossing
      model weighted hL hx₀.1 hcross
  have hRscaled : (2 / p.α) * R ≤ A :=
    path.sum_barrier_increments_le_action
      model ss hcoop weighted hx₀ hstock₀ N
  have hQ : Q ≤ 2 * p.α ^ 2 * A :=
    path.sum_capped_increment_sq_le_action
      model ss hcoop weighted hx₀ hstock₀ N
  have hhalfAlpha : 0 ≤ p.α / 2 :=
    div_nonneg model.α_pos.le (by norm_num)
  have hR : R ≤ (p.α / 2) * A := by
    have hmul := mul_le_mul_of_nonneg_left hRscaled hhalfAlpha
    calc
      R = (p.α / 2) * ((2 / p.α) * R) := by
        field_simp [model.α_pos.ne']
      _ ≤ (p.α / 2) * A := hmul
  have hLhalf : 0 ≤ L / 2 := div_nonneg hL.nonneg (by norm_num)
  have hmeshMul := mul_le_mul_of_nonneg_left hQ hLhalf
  have hmesh : (L / 2) * Q ≤ L * p.α ^ 2 * A := by
    calc
      (L / 2) * Q ≤ (L / 2) * (2 * p.α ^ 2 * A) := hmeshMul
      _ = L * p.α ^ 2 * A := by ring
  have hI : Ibar ≤ (p.α / 2) * (1 + 2 * p.α * L) * A := by
    calc
      Ibar ≤ R + (L / 2) * Q := hpartition
      _ ≤ (p.α / 2) * A + L * p.α ^ 2 * A := add_le_add hR hmesh
      _ = (p.α / 2) * (1 + 2 * p.α * L) * A := by ring
  have hcorrectionPos : 0 < 1 + 2 * p.α * L := by
    have hterm : 0 ≤ 2 * p.α * L :=
      mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) hL.nonneg
    linarith
  have hdenPos : 0 < (p.α / 2) * (1 + 2 * p.α * L) :=
    mul_pos (div_pos model.α_pos (by norm_num)) hcorrectionPos
  have hdiv : Ibar / ((p.α / 2) * (1 + 2 * p.α * L)) ≤ A :=
    (div_le_iff₀ hdenPos).2 (by simpa only [mul_comm] using hI)
  change (2 / (p.α * (1 + 2 * p.α * L))) * Ibar ≤ A
  convert hdiv using 1
  field_simp [model.α_pos.ne', hcorrectionPos.ne']

/-- If a restarted path begins at policy at most `betaOut`, crossing the
saddle pays the corrected barrier localized to `[betaOut, betaDagger]`.
This is the from-start ledger used in the last-exit persistence proof. -/
theorem IsControlledCivicWeightedPathFrom.localized_action_lower_bound_of_crossing
    {p : LoopParams} {rho L betaOut : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hstock₀ : x₀.2 ≤ p.stationaryStock x₀.1)
    (hbetaOut : betaOut ∈ Icc (0 : ℝ) weighted.βdagger)
    (hstart : x₀.1 ≤ betaOut) {N : ℕ}
    (hcross : weighted.βdagger ≤ policyRunningMax x N) :
    (2 / (p.α * (1 + 2 * p.α * L))) *
        (∫ b in betaOut..weighted.βdagger,
          weightedBarrierIntegrand p rho b) ≤
      controlAction u N := by
  let start := cappedPolicyRunningMax weighted.βdagger x 0
  let f := weightedBarrierIntegrand p rho
  have hstartEq : start = x₀.1 := by
    simp only [start, cappedPolicyRunningMax, policyRunningMax, runningMax]
    rw [path.initial]
    exact min_eq_right (hstart.trans hbetaOut.2)
  have hstartMem : start ∈ Icc (0 : ℝ) weighted.βdagger :=
    path.cappedRunningMax_mem weighted hx₀.1 0
  have hstartLe : start ≤ betaOut := by
    rw [hstartEq]
    exact hstart
  have hcont : ContinuousOn f (Icc (0 : ℝ) weighted.βdagger) :=
    continuousOn_weightedBarrierIntegrand model rho weighted
  have hleftSubset : [[start, betaOut]] ⊆
      Icc (0 : ℝ) weighted.βdagger := by
    rw [uIcc_of_le hstartLe]
    intro z hz
    exact ⟨hstartMem.1.trans hz.1, hz.2.trans hbetaOut.2⟩
  have hrightSubset : [[betaOut, weighted.βdagger]] ⊆
      Icc (0 : ℝ) weighted.βdagger := by
    rw [uIcc_of_le hbetaOut.2]
    intro z hz
    exact ⟨hbetaOut.1.trans hz.1, hz.2⟩
  have hleftInt : IntervalIntegrable f MeasureTheory.volume start betaOut :=
    (hcont.mono hleftSubset).intervalIntegrable
  have hrightInt : IntervalIntegrable f MeasureTheory.volume betaOut
      weighted.βdagger :=
    (hcont.mono hrightSubset).intervalIntegrable
  have hleftNonneg : 0 ≤ ∫ b in start..betaOut, f b := by
    apply intervalIntegral.integral_nonneg hstartLe
    intro z hz
    exact weighted.barrier_nonneg_before
      ⟨hstartMem.1.trans hz.1, hz.2.trans hbetaOut.2⟩
  have hadd :
      (∫ b in start..betaOut, f b) +
          (∫ b in betaOut..weighted.βdagger, f b) =
        ∫ b in start..weighted.βdagger, f b :=
    intervalIntegral.integral_add_adjacent_intervals hleftInt hrightInt
  have hintegral :
      (∫ b in betaOut..weighted.βdagger, f b) ≤
        ∫ b in start..weighted.βdagger, f b := by
    linarith
  have hcorrectionPos : 0 < 1 + 2 * p.α * L := by
    have hterm : 0 ≤ 2 * p.α * L :=
      mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) hL.nonneg
    linarith
  have hcoefficient :
      0 ≤ 2 / (p.α * (1 + 2 * p.α * L)) :=
    div_nonneg (by norm_num) (mul_pos model.α_pos hcorrectionPos).le
  calc
    (2 / (p.α * (1 + 2 * p.α * L))) *
        (∫ b in betaOut..weighted.βdagger, f b) ≤
      (2 / (p.α * (1 + 2 * p.α * L))) *
        (∫ b in start..weighted.βdagger, f b) :=
      mul_le_mul_of_nonneg_left hintegral hcoefficient
    _ ≤ controlAction u N := by
      simpa only [start, f] using path.action_lower_bound_of_crossing
        model ss hcoop weighted hL hx₀ hstock₀ hcross

/-! ## Zero-control and monotone-comparison bridges -/

@[simp]
theorem controlledCivicWeightedStep_zero (p : LoopParams) (rho : ℝ)
    (x : LoopState) :
    controlledCivicWeightedStep p rho 0 x = civicWeightedLoopMap p rho x := by
  simp only [controlledCivicWeightedStep, civicWeightedLoopMap,
    civicWeightedDeferenceStep, civicWeightedInput, add_zero]

/-- A controlled path with identically zero control is the unforced orbit
from its stated initial condition. -/
theorem IsControlledCivicWeightedPathFrom.eq_civicWeightedOrbit_of_control_eq_zero
    {p : LoopParams} {rho : ℝ} {x₀ : LoopState}
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hu : ∀ n, u n = 0) (n : ℕ) :
    x n = civicWeightedOrbit p rho x₀ n := by
  induction n with
  | zero => simp only [path.initial, civicWeightedOrbit,
      Function.iterate_zero_apply]
  | succ n ih =>
      rw [path.step n, hu n, controlledCivicWeightedStep_zero, ih]
      simp only [civicWeightedOrbit, Function.iterate_succ_apply']

/-- The canonical zero-control recursion is definitionally the unforced
civic-weighted orbit. -/
theorem controlledCivicWeightedOrbitFrom_zero (p : LoopParams) (rho : ℝ)
    (x₀ : LoopState) (n : ℕ) :
    controlledCivicWeightedOrbitFrom p rho x₀ (fun _ ↦ 0) n =
      civicWeightedOrbit p rho x₀ n :=
  (controlledCivicWeightedOrbitFrom_isControlled p rho x₀
    (fun _ ↦ 0)).eq_civicWeightedOrbit_of_control_eq_zero (fun _ ↦ rfl) n

/-- Order between two starts in the invariant box is preserved along their
unforced weighted orbits. -/
theorem civicWeightedOrbit_mono_of_le
    {p : LoopParams} {rho : ℝ}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    {x₀ y₀ : LoopState} (hx₀ : x₀ ∈ absorbingBox p)
    (hy₀ : y₀ ∈ absorbingBox p) (hxy : x₀ ≤ y₀) (n : ℕ) :
    civicWeightedOrbit p rho x₀ n ≤ civicWeightedOrbit p rho y₀ n := by
  let x := civicWeightedOrbit p rho x₀
  let y := civicWeightedOrbit p rho y₀
  have hxmem : ∀ k, x k ∈ absorbingBox p :=
    civicWeightedTrajectory_mem_absorbingBox model
      (civicWeightedOrbit_isTrajectory p rho x₀) hx₀
  have hymem : ∀ k, y k ∈ absorbingBox p :=
    civicWeightedTrajectory_mem_absorbingBox model
      (civicWeightedOrbit_isTrajectory p rho y₀) hy₀
  induction n with
  | zero => simpa only [x, y, civicWeightedOrbit,
      Function.iterate_zero_apply] using hxy
  | succ n ih =>
      simpa only [x, y, civicWeightedOrbit,
        Function.iterate_succ_apply'] using
        civicWeightedLoopMap_monotoneOn_box model ss hcoop
          (hxmem n) (hymem n) ih

/-- The unforced orbit of the calibrated corner is constant. -/
theorem civicWeightedOrbit_calibratedPoint
    {p : LoopParams} (model : DriftModelAssumptions p)
    (threshold : ThresholdAssumption p) {rho : ℝ} (hrho : 0 ≤ rho)
    (n : ℕ) :
    civicWeightedOrbit p rho (calibratedPoint p) n = calibratedPoint p := by
  have hfixed := civicWeighted_calibrated_fixed model threshold hrho
  induction n with
  | zero => simp only [civicWeightedOrbit, Function.iterate_zero_apply]
  | succ n ih =>
      rw [(civicWeightedOrbit_isTrajectory p rho (calibratedPoint p)) n, ih]
      exact hfixed

/-! ## The weighted saddle and the corrected pre-crossing funnel -/

/-- The stationary state at the unique civic-weighted crossing. -/
def weightedSaddlePoint {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) : LoopState :=
  (weighted.βdagger, p.stationaryStock weighted.βdagger)

/-- The weighted saddle lies in the invariant rectangle. -/
theorem weightedSaddlePoint_mem_absorbingBox
    {p : LoopParams} (model : DriftModelAssumptions p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) :
    weightedSaddlePoint weighted ∈ absorbingBox p := by
  have hβ : weighted.βdagger ∈ Icc (0 : ℝ) 1 :=
    ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩
  exact ⟨hβ, stationaryStock_mem_stockInterval model hβ⟩

/-- The weighted saddle is an actual fixed point of the projected map. -/
theorem civicWeightedLoopMap_weightedSaddlePoint
    {p : LoopParams} (model : DriftModelAssumptions p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) :
    civicWeightedLoopMap p rho (weightedSaddlePoint weighted) =
      weightedSaddlePoint weighted := by
  have hβ : weighted.βdagger ∈ Icc (0 : ℝ) 1 :=
    ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩
  have hgradient : civicWeightedGradient p rho weighted.βdagger
      (p.stationaryStock weighted.βdagger) = 0 := by
    rw [civicWeightedGradient_stationary_eq_weightedStationaryGradient rho hβ]
    exact weighted.gradient_zero
  have hstock := stationaryStock_fixed model hβ
  apply Prod.ext
  · simp only [civicWeightedLoopMap, civicWeightedDeferenceStep,
      civicWeightedInput, weightedSaddlePoint, hgradient, mul_zero, add_zero]
    exact clipUnit_eq_self hβ
  · simpa only [civicWeightedLoopMap, weightedSaddlePoint] using hstock

/-- The stock multiplier is strictly positive at every interior policy. -/
theorem driftStockMultiplier_pos_of_mem_Ioo
    {p : LoopParams} (model : DriftModelAssumptions p) {beta : ℝ}
    (hbeta : beta ∈ Ioo (0 : ℝ) 1) :
    0 < p.s beta := by
  have hresidual : 0 < 1 - p.η * (1 - beta) := by
    have heta : p.η * (1 - beta) < 1 := by
      calc
        p.η * (1 - beta) ≤ 1 * (1 - beta) := by
          exact mul_le_mul_of_nonneg_right model.η_le_one
            (sub_nonneg.mpr hbeta.2.le)
        _ = 1 - beta := one_mul _
        _ < 1 := by linarith [hbeta.1]
    linarith
  simp only [LoopParams.s]
  exact mul_pos (sub_pos.mpr model.lambda₀_lt_one) (sq_pos_of_pos hresidual)

/-- A distinct state weakly below the weighted saddle acquires a strict stock
gap after one unforced step.  Unlike the global strict-order lemma, this needs
only `(SS)`: positivity of the stock multiplier is used at the interior
saddle, not at the calibrated endpoint. -/
theorem civicWeightedLoopMap_stock_lt_weightedSaddle_of_le_of_ne
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    {x : LoopState} (hx : x ∈ absorbingBox p)
    (hxle : x ≤ weightedSaddlePoint weighted)
    (hne : x ≠ weightedSaddlePoint weighted) :
    (civicWeightedLoopMap p rho x).2 <
      (weightedSaddlePoint weighted).2 := by
  let q : LoopState := weightedSaddlePoint weighted
  have hqmem : q ∈ absorbingBox p :=
    weightedSaddlePoint_mem_absorbingBox model weighted
  have hsle : p.s x.1 ≤ p.s q.1 :=
    (driftStockMultiplier_strictMonoOn model).monotoneOn
      hx.1 hqmem.1 hxle.1
  have hsq : 0 < p.s q.1 := by
    simpa only [q, weightedSaddlePoint] using
      driftStockMultiplier_pos_of_mem_Ioo model weighted.βdagger_mem
  have hqDpos : 0 < q.2 := model.I_pos.trans_le hqmem.2.1
  have hmul : p.s x.1 * x.2 < p.s q.1 * q.2 := by
    rcases lt_or_eq_of_le hxle.2 with hD | hD
    · have hleft : p.s x.1 * x.2 ≤ p.s q.1 * x.2 :=
        mul_le_mul_of_nonneg_right hsle (model.I_pos.le.trans hx.2.1)
      exact hleft.trans_lt (mul_lt_mul_of_pos_left hD hsq)
    · have hβ : x.1 < q.1 := by
        rcases lt_or_eq_of_le hxle.1 with h | h
        · exact h
        · exact (hne (Prod.ext h hD)).elim
      have hslt : p.s x.1 < p.s q.1 :=
        driftStockMultiplier_strictMonoOn model hx.1 hqmem.1 hβ
      rw [hD]
      exact mul_lt_mul_of_pos_right hslt hqDpos
  have hfixed := stationaryStock_fixed model hqmem.1
  simp only [civicWeightedLoopMap, LoopParams.stockStep,
    model.no_content_gain, add_zero, q, weightedSaddlePoint] at hmul hfixed ⊢
  linarith

/-- A raw policy input strictly below an interior target remains strictly
below that target after projection. -/
theorem clipUnit_lt_of_lt_interior_target {z target : ℝ}
    (htarget : target ∈ Ioo (0 : ℝ) 1) (hz : z < target) :
    LoopParams.clipUnit z < target := by
  by_cases hz0 : z ≤ 0
  · rw [(clipUnit_eq_zero_iff z).2 hz0]
    exact htarget.1
  · rw [clipUnit_eq_self ⟨(not_le.mp hz0).le, hz.le.trans htarget.2.le⟩]
    exact hz

/-- If a state lies weakly below the weighted saddle and has a strict stock
gap, its next policy is strictly below the saddle policy. -/
theorem civicWeightedLoopMap_policy_lt_weightedSaddle_of_stock_lt
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    {x : LoopState} (hx : x ∈ absorbingBox p)
    (hxle : x ≤ weightedSaddlePoint weighted)
    (hstock : x.2 < (weightedSaddlePoint weighted).2) :
    (civicWeightedLoopMap p rho x).1 < weighted.βdagger := by
  let q : LoopState := weightedSaddlePoint weighted
  have hqmem : q ∈ absorbingBox p :=
    weightedSaddlePoint_mem_absorbingBox model weighted
  have hpolicyMono : civicWeightedInput p rho x.1 x.2 ≤
      civicWeightedInput p rho q.1 x.2 :=
    civicWeightedInput_mono_policy (ρ := rho) model ss
      hx.1 hqmem.1 hxle.1 hx.2
  have hcoef : 0 < 2 * p.c * (1 - p.c * weighted.βdagger) - rho := by
    have hcore : 0 < 2 * p.c ^ 2 * (1 - weighted.βdagger) :=
      mul_pos (mul_pos two_pos (sq_pos_of_pos model.c_pos))
        (sub_pos.mpr weighted.βdagger_mem.2)
    nlinarith [hcoop]
  have hstrict : civicWeightedInput p rho q.1 x.2 <
      civicWeightedInput p rho q.1 q.2 := by
    have hstock' : x.2 < p.stationaryStock weighted.βdagger := by
      simpa only [q, weightedSaddlePoint] using hstock
    have halphaCoef : 0 < p.α *
        (2 * p.c * (1 - p.c * weighted.βdagger) - rho) :=
      mul_pos model.α_pos hcoef
    have hproduct : 0 < p.α *
        (2 * p.c * (1 - p.c * weighted.βdagger) - rho) *
        (p.stationaryStock weighted.βdagger - x.2) :=
      mul_pos halphaCoef (sub_pos.mpr hstock')
    simp only [civicWeightedInput, civicWeightedGradient, LoopParams.gradU,
      q, weightedSaddlePoint]
    nlinarith
  have hqinput : civicWeightedInput p rho q.1 q.2 = weighted.βdagger := by
    have hβ : weighted.βdagger ∈ Icc (0 : ℝ) 1 :=
      ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩
    have hgradient : civicWeightedGradient p rho weighted.βdagger
        (p.stationaryStock weighted.βdagger) = 0 := by
      rw [civicWeightedGradient_stationary_eq_weightedStationaryGradient rho hβ]
      exact weighted.gradient_zero
    simp only [civicWeightedInput, q, weightedSaddlePoint, hgradient,
      mul_zero, add_zero]
  have hraw : civicWeightedInput p rho x.1 x.2 < weighted.βdagger := by
    rw [← hqinput]
    exact hpolicyMono.trans_lt hstrict
  simpa only [civicWeightedLoopMap, civicWeightedDeferenceStep] using
    clipUnit_lt_of_lt_interior_target weighted.βdagger_mem hraw

/-- Every state in the saddle order interval other than the saddle itself is
strictly below it in both coordinates after two unforced steps.  This is the
elementary replacement for the policy-only case split in the printed R1
argument. -/
theorem civicWeightedOrbit_two_strictly_below_saddle
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    {x : LoopState} (hx : x ∈ absorbingBox p)
    (hxle : x ≤ weightedSaddlePoint weighted)
    (hne : x ≠ weightedSaddlePoint weighted) :
    (civicWeightedOrbit p rho x 2).1 < weighted.βdagger ∧
      (civicWeightedOrbit p rho x 2).2 <
        p.stationaryStock weighted.βdagger := by
  let q : LoopState := weightedSaddlePoint weighted
  let y : LoopState := civicWeightedLoopMap p rho x
  have hqmem : q ∈ absorbingBox p :=
    weightedSaddlePoint_mem_absorbingBox model weighted
  have hymem : y ∈ absorbingBox p := by
    exact civicWeightedTrajectory_mem_absorbingBox model
      (civicWeightedOrbit_isTrajectory p rho x) hx 1
  have hyle : y ≤ q := by
    have hmono := civicWeightedLoopMap_monotoneOn_box model ss hcoop
      hx hqmem hxle
    rw [civicWeightedLoopMap_weightedSaddlePoint model weighted] at hmono
    exact hmono
  have hyStock : y.2 < q.2 :=
    civicWeightedLoopMap_stock_lt_weightedSaddle_of_le_of_ne
      model weighted hx hxle hne
  have hpolicy : (civicWeightedLoopMap p rho y).1 < weighted.βdagger :=
    civicWeightedLoopMap_policy_lt_weightedSaddle_of_stock_lt
      model ss hcoop weighted hymem hyle hyStock
  have hstock : (civicWeightedLoopMap p rho y).2 < q.2 :=
    civicWeightedLoopMap_stock_lt_weightedSaddle_of_le_of_ne
      model weighted hymem hyle (fun heq ↦ by
        rw [heq] at hyStock
        exact (lt_irrefl q.2 hyStock).elim)
  simpa only [civicWeightedOrbit, Function.iterate_succ_apply',
    Function.iterate_zero_apply, y, q, weightedSaddlePoint] using
    And.intro hpolicy hstock

/-- Any state strictly below the weighted saddle in both coordinates is
dominated by one point strictly below it on the stationary characteristic. -/
theorem exists_characteristic_dominating_of_strictly_below_weightedSaddle
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    {x : LoopState}
    (hpolicy : x.1 < weighted.βdagger)
    (hstock : x.2 < p.stationaryStock weighted.βdagger) :
    ∃ b : ℝ, b ∈ Ioo (0 : ℝ) 1 ∧ b < weighted.βdagger ∧
      x ≤ (b, p.stationaryStock b) := by
  have hβclosed : weighted.βdagger ∈ Icc (0 : ℝ) 1 :=
    ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩
  have hcontinuous : ContinuousAt p.stationaryStock weighted.βdagger :=
    (hasDerivAt_stationaryStock_zeroGain model hβclosed).continuousAt
  have heventually : ∀ᶠ b in 𝓝 weighted.βdagger,
      x.2 < p.stationaryStock b :=
    hcontinuous.tendsto.eventually_const_lt hstock
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp heventually
  let d : ℝ := min (delta / 2)
    (min ((weighted.βdagger - x.1) / 2) (weighted.βdagger / 2))
  let b : ℝ := weighted.βdagger - d
  have hdpos : 0 < d := by
    dsimp only [d]
    apply lt_min (half_pos hdelta)
    exact lt_min (half_pos (sub_pos.mpr hpolicy))
      (half_pos weighted.βdagger_mem.1)
  have hdDelta : d < delta :=
    (min_le_left _ _).trans_lt (half_lt_self hdelta)
  have hdPolicy : d ≤ (weighted.βdagger - x.1) / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hdRoot : d ≤ weighted.βdagger / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hbPolicy : x.1 < b := by
    dsimp only [b]
    linarith
  have hbPos : 0 < b := by
    dsimp only [b]
    linarith
  have hbRoot : b < weighted.βdagger := by
    dsimp only [b]
    linarith
  have hdist : dist b weighted.βdagger < delta := by
    have hsub : b - weighted.βdagger = -d := by
      dsimp only [b]
      ring
    rw [Real.dist_eq, hsub, abs_neg, abs_of_pos hdpos]
    exact hdDelta
  have hbStock : x.2 < p.stationaryStock b := hball hdist
  exact ⟨b, ⟨hbPos, hbRoot.trans weighted.βdagger_mem.2⟩,
    hbRoot, ⟨hbPolicy.le, hbStock.le⟩⟩

/-- Every state in the closed order interval from calibration to the weighted
saddle, except the saddle itself, converges to calibration.  No weighted
`(SS⁺)` assumption is used. -/
theorem civicWeightedOrbit_tendsto_calibrated_of_le_weightedSaddle_of_ne
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    {x : LoopState} (hx : x ∈ absorbingBox p)
    (hlower : calibratedPoint p ≤ x)
    (hupper : x ≤ weightedSaddlePoint weighted)
    (hne : x ≠ weightedSaddlePoint weighted) :
    Tendsto (civicWeightedOrbit p rho x) atTop
      (𝓝 (calibratedPoint p)) := by
  let y : LoopState := civicWeightedOrbit p rho x 2
  have hymem : y ∈ absorbingBox p :=
    civicWeightedTrajectory_mem_absorbingBox model
      (civicWeightedOrbit_isTrajectory p rho x) hx 2
  have hstrict := civicWeightedOrbit_two_strictly_below_saddle
    model ss hcoop weighted hx hupper hne
  obtain ⟨b, hb, hbelow, hyUpper⟩ :=
    exists_characteristic_dominating_of_strictly_below_weightedSaddle
      model weighted hstrict.1 hstrict.2
  have hp₁mem : calibratedPoint p ∈ absorbingBox p :=
    ⟨by simp [calibratedPoint],
      stationaryStock_mem_stockInterval model (by norm_num)⟩
  have hyLower : calibratedPoint p ≤ y := by
    have hmono := civicWeightedOrbit_mono_of_le model ss hcoop
      hp₁mem hx hlower 2
    simpa only [civicWeightedOrbit_calibratedPoint model threshold hrho 2,
      y] using hmono
  have hyTendsto : Tendsto (civicWeightedOrbit p rho y) atTop
      (𝓝 (calibratedPoint p)) :=
    mem_civicWeightedCalibratedBasin_of_le_characteristic_below
      model ss threshold hrho hcoop weighted hymem hyLower hyUpper hb hbelow
  have horbitTail : civicWeightedOrbit p rho y =
      fun n ↦ civicWeightedOrbit p rho x (n + 2) := by
    funext n
    simp only [y, civicWeightedOrbit, Function.iterate_add_apply]
  have htail : Tendsto (fun n ↦ civicWeightedOrbit p rho x (n + 2)) atTop
      (𝓝 (calibratedPoint p)) := by
    rwa [horbitTail] at hyTendsto
  exact (tendsto_add_atTop_iff_nat 2).1 htail

/-- A coordinate rectangle of radius `epsilon` above the calibrated corner.
This order-compatible neighborhood is convenient for the block proof. -/
def calibratedHomeRectangle (p : LoopParams) (epsilon : ℝ) : Set LoopState :=
  Icc (0 : ℝ) epsilon ×ˢ
    Icc (p.stationaryStock 0) (p.stationaryStock 0 + epsilon)

/-- Every calibrated home rectangle is compact. -/
theorem isCompact_calibratedHomeRectangle (p : LoopParams) (epsilon : ℝ) :
    IsCompact (calibratedHomeRectangle p epsilon) := by
  simpa only [calibratedHomeRectangle] using
    (isCompact_Icc.prod isCompact_Icc :
      IsCompact (Icc (0 : ℝ) epsilon ×ˢ
        Icc (p.stationaryStock 0) (p.stationaryStock 0 + epsilon)))

/-- The closed order interval trapped between calibration and a sub-saddle
point on the stationary characteristic. -/
def weightedCharacteristicRectangle (p : LoopParams) (b : ℝ) : Set LoopState :=
  Icc (calibratedPoint p) (b, p.stationaryStock b)

/-- A sub-saddle characteristic rectangle is forward invariant under the
unforced weighted map. -/
theorem civicWeightedLoopMap_mem_weightedCharacteristicRectangle
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho b : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hb : b ∈ Ioo (0 : ℝ) 1) (hbelow : b < weighted.βdagger)
    {x : LoopState} (hx : x ∈ weightedCharacteristicRectangle p b) :
    civicWeightedLoopMap p rho x ∈ weightedCharacteristicRectangle p b := by
  have hbclosed : b ∈ Icc (0 : ℝ) 1 := ⟨hb.1.le, hb.2.le⟩
  have hp₁mem : calibratedPoint p ∈ absorbingBox p :=
    ⟨by simp [calibratedPoint],
      stationaryStock_mem_stockInterval model (by norm_num)⟩
  have hubmem : (b, p.stationaryStock b) ∈ absorbingBox p :=
    ⟨hbclosed, stationaryStock_mem_stockInterval model hbclosed⟩
  have hxmem : x ∈ absorbingBox p := by
    exact ⟨⟨by simpa only [calibratedPoint] using hx.1.1,
        hx.2.1.trans hubmem.1.2⟩,
      ⟨hp₁mem.2.1.trans hx.1.2, hx.2.2.trans hubmem.2.2⟩⟩
  have hlower := civicWeightedLoopMap_monotoneOn_box model ss hcoop
    hp₁mem hxmem hx.1
  have hupper := civicWeightedLoopMap_monotoneOn_box model ss hcoop
    hxmem hubmem hx.2
  have hp₁fixed : civicWeightedLoopMap p rho (calibratedPoint p) =
      calibratedPoint p := civicWeighted_calibrated_fixed model threshold hrho
  have hubStep := civicWeighted_characteristic_step_le_of_below
    model weighted hb hbelow
  constructor
  · rw [hp₁fixed] at hlower
    exact hlower
  · exact hupper.trans hubStep

/-- Once an unforced orbit enters a sub-saddle characteristic rectangle, it
remains there at every later time. -/
theorem civicWeightedOrbit_mem_weightedCharacteristicRectangle
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho b : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hb : b ∈ Ioo (0 : ℝ) 1) (hbelow : b < weighted.βdagger)
    {x : LoopState} (hx : x ∈ weightedCharacteristicRectangle p b) :
    ∀ n, civicWeightedOrbit p rho x n ∈
      weightedCharacteristicRectangle p b := by
  intro n
  induction n with
  | zero => simpa only [civicWeightedOrbit, Function.iterate_zero_apply] using hx
  | succ n ih =>
      simpa only [civicWeightedOrbit, Function.iterate_succ_apply'] using
        civicWeightedLoopMap_mem_weightedCharacteristicRectangle
          model ss threshold hrho hcoop weighted hb hbelow ih

/-- There is a sub-saddle characteristic rectangle inside every positive
calibrated home rectangle. -/
theorem exists_weightedCharacteristicRectangle_subset_home
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho epsilon : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (hepsilon : 0 < epsilon) :
    ∃ b : ℝ, b ∈ Ioo (0 : ℝ) 1 ∧ b < weighted.βdagger ∧
      b ≤ epsilon ∧
      p.stationaryStock b < p.stationaryStock 0 + epsilon := by
  have hzero : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hcontinuous : ContinuousAt p.stationaryStock 0 :=
    (hasDerivAt_stationaryStock_zeroGain model hzero).continuousAt
  have heventually : ∀ᶠ b in 𝓝 (0 : ℝ),
      p.stationaryStock b < p.stationaryStock 0 + epsilon :=
    hcontinuous.tendsto.eventually_lt_const (by linarith)
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp heventually
  let b : ℝ := min (delta / 2)
    (min (epsilon / 2) (weighted.βdagger / 2))
  have hbpos : 0 < b := by
    dsimp only [b]
    exact lt_min (half_pos hdelta)
      (lt_min (half_pos hepsilon)
        (half_pos weighted.βdagger_mem.1))
  have hbDelta : b < delta :=
    (min_le_left _ _).trans_lt (half_lt_self hdelta)
  have hbEpsilon : b ≤ epsilon := by
    have hhalf : epsilon / 2 ≤ epsilon := by linarith
    exact ((min_le_right _ _).trans (min_le_left _ _)).trans hhalf
  have hbRoot : b < weighted.βdagger := by
    have hhalf : weighted.βdagger / 2 < weighted.βdagger :=
      half_lt_self weighted.βdagger_mem.1
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans_lt hhalf
  have hdist : dist b 0 < delta := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hbpos]
    exact hbDelta
  exact ⟨b, ⟨hbpos, hbRoot.trans weighted.βdagger_mem.2⟩,
    hbRoot, hbEpsilon, hball hdist⟩

/-- The compact pre-crossing order interval with a metric neighborhood of the
weighted saddle removed. -/
def weightedPreCrossingAwaySet
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (radius : ℝ) :
    Set LoopState :=
  (absorbingBox p ∩
      Icc (calibratedPoint p) (weightedSaddlePoint weighted)) \
    Metric.ball (weightedSaddlePoint weighted) radius

/-- Before the running maximum reaches the weighted saddle, the actual
controlled state lies in the closed order interval below the full saddle
state. -/
theorem IsControlledCivicWeightedPath.mem_weightedSaddleOrderInterval
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (path : IsControlledCivicWeightedPath p rho u x)
    {N : ℕ} (hmax : policyRunningMax x N ≤ weighted.βdagger) :
    x N ∈ absorbingBox p ∩
      Icc (calibratedPoint p) (weightedSaddlePoint weighted) := by
  have hxmem := path.mem_absorbingBox model N
  have hlower := path.calibratedPoint_le model ss N
  have hmMem := path.runningMax_mem N
  have hstock := path.stock_le_stationary_runningMax model ss N
  have hstockMono : p.stationaryStock (policyRunningMax x N) ≤
      p.stationaryStock weighted.βdagger :=
    (stationaryStock_strictMonoOn model).monotoneOn hmMem
      ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩ hmax
  exact ⟨hxmem, hlower,
    ⟨(policy_le_runningMax x N).trans hmax,
      hstock.trans hstockMono⟩⟩

/-- The exact R1 state split: every pre-crossing state is either in the
closed saddle ball or in the compact away-from-saddle funnel set. -/
theorem IsControlledCivicWeightedPath.mem_saddleBall_or_awaySet
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho radius : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    {u : ℕ → ℝ} {x : ℕ → LoopState}
    (path : IsControlledCivicWeightedPath p rho u x)
    {N : ℕ} (hmax : policyRunningMax x N ≤ weighted.βdagger) :
    x N ∈ Metric.closedBall (weightedSaddlePoint weighted) radius ∨
      x N ∈ weightedPreCrossingAwaySet weighted radius := by
  by_cases hnear : dist (x N) (weightedSaddlePoint weighted) ≤ radius
  · exact Or.inl hnear
  · exact Or.inr ⟨path.mem_weightedSaddleOrderInterval
      model ss weighted hmax, fun hball ↦ hnear hball.le⟩

/-- The away-from-saddle pre-crossing set is compact. -/
theorem isCompact_weightedPreCrossingAwaySet
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (radius : ℝ) :
    IsCompact (weightedPreCrossingAwaySet weighted radius) := by
  exact ((isCompact_absorbingBox p).inter_right isClosed_Icc).diff
    Metric.isOpen_ball

/-- Outside any positive saddle neighborhood, every pre-crossing state enters
one common calibrated home rectangle at one common time.  This compact funnel
uses only `(SS)` and cooperativity; it does not assume weighted `(SS⁺)` or a
global convergence theorem. -/
theorem exists_uniform_away_saddle_funnel_time
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho saddleRadius epsilon : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hsaddleRadius : 0 < saddleRadius) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ x ∈ weightedPreCrossingAwaySet weighted saddleRadius,
      civicWeightedOrbit p rho x N ∈ calibratedHomeRectangle p epsilon := by
  obtain ⟨b, hb, hbelow, hbEpsilon, hbStock⟩ :=
    exists_weightedCharacteristicRectangle_subset_home
      model weighted hepsilon
  let K : Set LoopState :=
    weightedPreCrossingAwaySet weighted saddleRadius
  let U : ℕ → Set LoopState := fun n ↦
    {x | (civicWeightedOrbit p rho x n).1 < b} ∩
      {x | (civicWeightedOrbit p rho x n).2 < p.stationaryStock b}
  have hUopen : ∀ n, IsOpen (U n) := by
    intro n
    have hcontinuous : Continuous
        (fun x : LoopState ↦ civicWeightedOrbit p rho x n) :=
      (continuous_civicWeightedLoopMap p rho).iterate n
    exact (isOpen_Iio.preimage hcontinuous.fst).inter
      (isOpen_Iio.preimage hcontinuous.snd)
  have hcover : K ⊆ ⋃ n, U n := by
    intro x hx
    have hxmem : x ∈ absorbingBox p := hx.1.1
    have hlower : calibratedPoint p ≤ x := hx.1.2.1
    have hupper : x ≤ weightedSaddlePoint weighted := hx.1.2.2
    have hne : x ≠ weightedSaddlePoint weighted := by
      intro heq
      apply hx.2
      rw [heq]
      exact Metric.mem_ball_self hsaddleRadius
    have htendsto :=
      civicWeightedOrbit_tendsto_calibrated_of_le_weightedSaddle_of_ne
        model ss threshold hrho hcoop weighted hxmem hlower hupper hne
    have hpolicyLim : Tendsto
        (fun n ↦ (civicWeightedOrbit p rho x n).1) atTop (𝓝 0) := by
      change Tendsto (Prod.fst ∘ civicWeightedOrbit p rho x) atTop (𝓝 0)
      simpa only [calibratedPoint] using
        (continuous_fst.tendsto (calibratedPoint p)).comp htendsto
    have hstockLim : Tendsto
        (fun n ↦ (civicWeightedOrbit p rho x n).2) atTop
          (𝓝 (p.stationaryStock 0)) := by
      change Tendsto (Prod.snd ∘ civicWeightedOrbit p rho x) atTop
        (𝓝 (p.stationaryStock 0))
      simpa only [calibratedPoint] using
        (continuous_snd.tendsto (calibratedPoint p)).comp htendsto
    have hstock0lt : p.stationaryStock 0 < p.stationaryStock b :=
      stationaryStock_strictMonoOn model (by norm_num)
        ⟨hb.1.le, hb.2.le⟩ hb.1
    have hpolicyEventually : ∀ᶠ n in atTop,
        (civicWeightedOrbit p rho x n).1 < b :=
      (tendsto_order.1 hpolicyLim).2 b hb.1
    have hstockEventually : ∀ᶠ n in atTop,
        (civicWeightedOrbit p rho x n).2 < p.stationaryStock b :=
      (tendsto_order.1 hstockLim).2 _ hstock0lt
    obtain ⟨n, hn⟩ := eventually_atTop.1
      (hpolicyEventually.and hstockEventually)
    exact mem_iUnion.2 ⟨n, hn n le_rfl⟩
  obtain ⟨times, htimes⟩ :=
    (isCompact_weightedPreCrossingAwaySet weighted saddleRadius).elim_finite_subcover
      U hUopen hcover
  let N : ℕ := times.sup id
  refine ⟨N, fun x hx ↦ ?_⟩
  obtain ⟨n, hnTimes, hxn⟩ := mem_iUnion₂.1 (htimes hx)
  have hnN : n ≤ N := Finset.le_sup (f := id) hnTimes
  have hxmem : x ∈ absorbingBox p := hx.1.1
  have hp₁mem : calibratedPoint p ∈ absorbingBox p :=
    ⟨by simp [calibratedPoint],
      stationaryStock_mem_stockInterval model (by norm_num)⟩
  have hlowerN : calibratedPoint p ≤ civicWeightedOrbit p rho x n := by
    have hmono := civicWeightedOrbit_mono_of_le model ss hcoop
      hp₁mem hxmem hx.1.2.1 n
    simpa only [civicWeightedOrbit_calibratedPoint model threshold hrho n]
      using hmono
  have hxnTrap : civicWeightedOrbit p rho x n ∈
      weightedCharacteristicRectangle p b :=
    ⟨hlowerN, ⟨hxn.1.le, hxn.2.le⟩⟩
  have htailTrap := civicWeightedOrbit_mem_weightedCharacteristicRectangle
    model ss threshold hrho hcoop weighted hb hbelow hxnTrap (N - n)
  have horbitEq : civicWeightedOrbit p rho
      (civicWeightedOrbit p rho x n) (N - n) =
        civicWeightedOrbit p rho x N := by
    simp only [civicWeightedOrbit]
    rw [← Function.iterate_add_apply]
    rw [Nat.sub_add_cancel hnN]
  rw [horbitEq] at htailTrap
  constructor
  · exact ⟨by simpa only [weightedCharacteristicRectangle, calibratedPoint]
        using htailTrap.1.1,
      htailTrap.2.1.trans hbEpsilon⟩
  · exact ⟨by simpa only [weightedCharacteristicRectangle, calibratedPoint]
        using htailTrap.1.2,
      htailTrap.2.2.trans hbStock.le⟩

/-! ## A uniform deterministic home funnel -/

/-- Every start between the calibrated corner and one sub-saddle point on the
stationary characteristic enters the same calibrated home rectangle at one
common finite time.  This is the deterministic characteristic funnel;
uniformity follows from domination by the single endpoint orbit. -/
theorem exists_uniform_characteristic_funnel_time
    {p : LoopParams} {rho b epsilon : ℝ}
    (model : DriftModelAssumptions p) (ss : SmallStepAssumption p)
    (threshold : ThresholdAssumption p) (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hb : b ∈ Ioo (0 : ℝ) 1) (hbelow : b < weighted.βdagger)
    (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ z : LoopState, z ∈ absorbingBox p →
      calibratedPoint p ≤ z → z ≤ (b, p.stationaryStock b) →
      civicWeightedOrbit p rho z N ∈ calibratedHomeRectangle p epsilon := by
  let upper : ℕ → LoopState :=
    civicWeightedOrbit p rho (b, p.stationaryStock b)
  have hbclosed : b ∈ Icc (0 : ℝ) 1 := ⟨hb.1.le, hb.2.le⟩
  have hp₁mem : calibratedPoint p ∈ absorbingBox p :=
    ⟨by simp [calibratedPoint],
      stationaryStock_mem_stockInterval model (by norm_num)⟩
  have hu₀mem : (b, p.stationaryStock b) ∈ absorbingBox p :=
    ⟨hbclosed, stationaryStock_mem_stockInterval model hbclosed⟩
  have hupperLim : Tendsto upper atTop (nhds (calibratedPoint p)) :=
    civicWeighted_characteristic_below_tendsto_calibrated
      model ss hcoop weighted hb hbelow
  have hpolicyLim : Tendsto (fun n ↦ (upper n).1) atTop (nhds 0) := by
    change Tendsto (Prod.fst ∘ upper) atTop (nhds 0)
    simpa only [calibratedPoint] using
      (continuous_fst.tendsto (calibratedPoint p)).comp hupperLim
  have hstockLim : Tendsto (fun n ↦ (upper n).2) atTop
      (nhds (p.stationaryStock 0)) := by
    change Tendsto (Prod.snd ∘ upper) atTop
      (nhds (p.stationaryStock 0))
    simpa only [calibratedPoint] using
      (continuous_snd.tendsto (calibratedPoint p)).comp hupperLim
  have hpolicyEventually : ∀ᶠ n in atTop, (upper n).1 < epsilon :=
    (tendsto_order.1 hpolicyLim).2 epsilon hepsilon
  have hstockEventually : ∀ᶠ n in atTop,
      (upper n).2 < p.stationaryStock 0 + epsilon :=
    (tendsto_order.1 hstockLim).2 _ (by linarith)
  obtain ⟨N, hN⟩ := (eventually_atTop.1
    (hpolicyEventually.and hstockEventually))
  refine ⟨N, fun z hzmem hlower hupper ↦ ?_⟩
  have hcalibratedOrder : calibratedPoint p ≤
      civicWeightedOrbit p rho z N := by
    have hmono := civicWeightedOrbit_mono_of_le model ss hcoop
      hp₁mem hzmem hlower N
    simpa only [civicWeightedOrbit_calibratedPoint model threshold hrho N]
      using hmono
  have hcharacteristicOrder : civicWeightedOrbit p rho z N ≤ upper N :=
    civicWeightedOrbit_mono_of_le model ss hcoop hzmem hu₀mem hupper N
  obtain ⟨hpolicyUpper, hstockUpper⟩ := hN N le_rfl
  constructor
  · constructor
    · simpa only [calibratedPoint] using hcalibratedOrder.1
    · exact (hcharacteristicOrder.1.trans_lt hpolicyUpper).le
  · constructor
    · simpa only [calibratedPoint] using hcalibratedOrder.2
    · exact (hcharacteristicOrder.2.trans_lt hstockUpper).le

#print axioms controlledCivicWeightedOrbitFrom_isControlled
#print axioms isCompact_absorbingBox
#print axioms finiteControlledOrbitFrom_isControlled
#print axioms continuous_finiteControlledOrbitFrom
#print axioms exists_uniform_finiteControl_radius
#print axioms exists_uniform_action_cost_of_endpoint_deviation
#print axioms finiteControlledOrbitFrom_restrict_eq
#print axioms finiteControlledOrbitFrom_tail
#print axioms finiteControlledOrbitFrom_calibratedPoint
#print axioms finiteControlledOrbitFrom_zero_eq_civicWeightedOrbit
#print axioms IsControlledCivicWeightedPath.toFrom
#print axioms IsControlledCivicWeightedPathFrom.tail
#print axioms IsControlledCivicWeightedPathFrom.policy_mem
#print axioms IsControlledCivicWeightedPathFrom.mem_absorbingBox
#print axioms IsControlledCivicWeightedPathFrom.runningMax_mem
#print axioms IsControlledCivicWeightedPathFrom.calibratedPoint_le
#print axioms IsControlledCivicWeightedPathFrom.stock_le_stationary_runningMax
#print axioms IsControlledCivicWeightedPathFrom.stock_excess_le_geometric_of_policy_le
#print axioms IsControlledCivicWeightedPathFrom.stock_le_stationary_of_policy_le
#print axioms exists_uniform_stock_contraction_time
#print axioms IsControlledCivicWeightedPathFrom.cappedRunningMax_mem
#print axioms IsControlledCivicWeightedPathFrom.gradient_le_runningMax
#print axioms IsControlledCivicWeightedPathFrom.control_ge_barrier_add_advance
#print axioms IsControlledCivicWeightedPathFrom.advance_barrier_le_half_control_sq
#print axioms IsControlledCivicWeightedPathFrom.barrier_increment_le_half_control_sq
#print axioms IsControlledCivicWeightedPathFrom.sum_barrier_increments_le_action
#print axioms IsControlledCivicWeightedPathFrom.capped_increment_sq_le_control_sq
#print axioms IsControlledCivicWeightedPathFrom.sum_capped_increment_sq_le_action
#print axioms IsControlledCivicWeightedPathFrom.barrier_integral_le_partition_of_crossing
#print axioms IsControlledCivicWeightedPathFrom.action_lower_bound_of_crossing
#print axioms IsControlledCivicWeightedPathFrom.localized_action_lower_bound_of_crossing
#print axioms controlledCivicWeightedStep_zero
#print axioms IsControlledCivicWeightedPathFrom.eq_civicWeightedOrbit_of_control_eq_zero
#print axioms controlledCivicWeightedOrbitFrom_zero
#print axioms civicWeightedOrbit_mono_of_le
#print axioms civicWeightedOrbit_calibratedPoint
#print axioms weightedSaddlePoint_mem_absorbingBox
#print axioms civicWeightedLoopMap_weightedSaddlePoint
#print axioms driftStockMultiplier_pos_of_mem_Ioo
#print axioms civicWeightedLoopMap_stock_lt_weightedSaddle_of_le_of_ne
#print axioms clipUnit_lt_of_lt_interior_target
#print axioms civicWeightedLoopMap_policy_lt_weightedSaddle_of_stock_lt
#print axioms civicWeightedOrbit_two_strictly_below_saddle
#print axioms exists_characteristic_dominating_of_strictly_below_weightedSaddle
#print axioms civicWeightedOrbit_tendsto_calibrated_of_le_weightedSaddle_of_ne
#print axioms civicWeightedLoopMap_mem_weightedCharacteristicRectangle
#print axioms civicWeightedOrbit_mem_weightedCharacteristicRectangle
#print axioms exists_weightedCharacteristicRectangle_subset_home
#print axioms IsControlledCivicWeightedPath.mem_weightedSaddleOrderInterval
#print axioms IsControlledCivicWeightedPath.mem_saddleBall_or_awaySet
#print axioms isCompact_weightedPreCrossingAwaySet
#print axioms exists_uniform_away_saddle_funnel_time
#print axioms isCompact_calibratedHomeRectangle
#print axioms exists_uniform_characteristic_funnel_time

end

end CivicAlignment.PaperII
