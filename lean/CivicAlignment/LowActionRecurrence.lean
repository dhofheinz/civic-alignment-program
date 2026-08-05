/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import Mathlib

/-!
# Uniform low-action recurrence for discrete controlled maps

This file develops a compact-state recurrence lemma independently of the
Paper II crossing and Arrhenius constructions.  A continuous discrete map is
driven by a finite real-valued control vector.  On a compact set whose
zero-control orbits converge to one point, compactness supplies a uniform
entrance horizon.  Joint continuity then makes avoidance of a larger
neighborhood cost a uniform positive amount of quadratic action.

The result is deterministic.  Its role in a small-noise exit theorem is to
reduce arbitrarily long excursions to fixed-dimensional charged blocks.
-/

namespace CivicAlignment

open Filter Function Set Topology
open scoped BigOperators

noncomputable section

universe u

variable {X : Type u} [PseudoMetricSpace X]

/-- A finite control history, continued by zero after its horizon. -/
def finiteControlValue {T : ℕ} (u : Fin T → ℝ) (n : ℕ) : ℝ :=
  if h : n < T then u ⟨n, h⟩ else 0

/-- The controlled recursion from an arbitrary initial state. -/
def finiteControlOrbit (step : ℝ → X → X) (x₀ : X)
    {T : ℕ} (u : Fin T → ℝ) : ℕ → X
  | 0 => x₀
  | n + 1 => step (finiteControlValue u n)
      (finiteControlOrbit step x₀ u n)

/-- Half the squared Euclidean norm of a finite control history. -/
def finiteQuadraticAction {T : ℕ} (u : Fin T → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, (u i) ^ 2

/-- The controlled recursion driven by an infinite control sequence. -/
def controlOrbit (step : ℝ → X → X) (x₀ : X)
    (u : ℕ → ℝ) : ℕ → X
  | 0 => x₀
  | n + 1 => step (u n) (controlOrbit step x₀ u n)

/-- Quadratic action accumulated over an initial segment. -/
def quadraticActionPrefix (u : ℕ → ℝ) (T : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∑ n ∈ Finset.range T, (u n) ^ 2

/-- Finite quadratic action is nonnegative. -/
theorem finiteQuadraticAction_nonneg {T : ℕ} (u : Fin T → ℝ) :
    0 ≤ finiteQuadraticAction u := by
  simp only [finiteQuadraticAction]
  positivity

/-- Restarting an infinite controlled orbit at a deterministic time is the
same recursion driven by the corresponding shifted control sequence. -/
theorem controlOrbit_add {Y : Type*} (step : ℝ → Y → Y) (x₀ : Y)
    (u : ℕ → ℝ) (m n : ℕ) :
    controlOrbit step x₀ u (m + n) =
      controlOrbit step (controlOrbit step x₀ u m)
        (fun k ↦ u (m + k)) n := by
  induction n with
  | zero => simp only [Nat.add_zero, controlOrbit]
  | succ n ih =>
      rw [Nat.add_succ, controlOrbit, ih, controlOrbit]

/-- A finite control slice reproduces the corresponding segment of an
infinite controlled orbit. -/
theorem finiteControlOrbit_block_eq_controlOrbit
    {Y : Type*} (step : ℝ → Y → Y) (x₀ : Y) (u : ℕ → ℝ)
    (start T n : ℕ) (hn : n ≤ T) :
    finiteControlOrbit step (controlOrbit step x₀ u start)
        (fun i : Fin T ↦ u (start + i)) n =
      controlOrbit step x₀ u (start + n) := by
  rw [controlOrbit_add]
  induction n with
  | zero => rfl
  | succ n ih =>
      have hnlt : n < T := by omega
      rw [finiteControlOrbit, controlOrbit, ih (by omega)]
      simp only [finiteControlValue, hnlt, dite_true]

/-- Before a concatenation point, an appended finite control agrees with its
prefix. -/
theorem finiteControlOrbit_append_left
    {Y : Type*} (step : ℝ → Y → Y) (x₀ : Y)
    {N T : ℕ} (u : Fin N → ℝ) (v : Fin T → ℝ)
    {n : ℕ} (hn : n ≤ N) :
    finiteControlOrbit step x₀ (Fin.append u v) n =
      finiteControlOrbit step x₀ u n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hnlt : n < N := by omega
      have hbig : n < N + T := hnlt.trans_le (Nat.le_add_right N T)
      rw [finiteControlOrbit, finiteControlOrbit, ih (by omega)]
      simp only [finiteControlValue, hbig, hnlt, dite_true]
      rw [show (⟨n, hbig⟩ : Fin (N + T)) = Fin.castAdd T ⟨n, hnlt⟩ by
        ext
        rfl]
      rw [Fin.append_left]

/-- After a concatenation point, an appended finite control restarts from the
prefix endpoint and follows the suffix. -/
theorem finiteControlOrbit_append_right
    {Y : Type*} (step : ℝ → Y → Y) (x₀ : Y)
    {N T : ℕ} (u : Fin N → ℝ) (v : Fin T → ℝ)
    {k : ℕ} (hk : k ≤ T) :
    finiteControlOrbit step x₀ (Fin.append u v) (N + k) =
      finiteControlOrbit step (finiteControlOrbit step x₀ u N) v k := by
  induction k with
  | zero =>
      simpa only [Nat.add_zero, finiteControlOrbit] using
        finiteControlOrbit_append_left step x₀ u v le_rfl
  | succ k ih =>
      have hklt : k < T := by omega
      rw [Nat.add_succ, finiteControlOrbit, ih (by omega), finiteControlOrbit]
      have hNk : N + k < N + T := Nat.add_lt_add_left hklt N
      simp only [finiteControlValue, hNk, hklt, dite_true]
      rw [show (⟨N + k, hNk⟩ : Fin (N + T)) = Fin.natAdd N ⟨k, hklt⟩ by
        ext
        simp]
      exact congrArg
        (fun control ↦ step control
          (finiteControlOrbit step (finiteControlOrbit step x₀ u N) v k))
        (Fin.append_right u v ⟨k, hklt⟩)

/-- The action of a finite slice is the prefix action of the shifted infinite
control sequence. -/
theorem finiteQuadraticAction_slice_eq
    (u : ℕ → ℝ) (start T : ℕ) :
    finiteQuadraticAction (fun i : Fin T ↦ u (start + i)) =
      quadraticActionPrefix (fun n ↦ u (start + n)) T := by
  simp only [finiteQuadraticAction, quadraticActionPrefix]
  rw [← Fin.sum_univ_eq_sum_range]

/-- Prefix action over equal consecutive blocks is the sum of the individual
block actions. -/
theorem quadraticActionPrefix_mul_eq_sum_blocks
    (u : ℕ → ℝ) (q T : ℕ) :
    quadraticActionPrefix u (q * T) =
      ∑ j ∈ Finset.range q,
        quadraticActionPrefix (fun n ↦ u (j * T + n)) T := by
  induction q with
  | zero => simp [quadraticActionPrefix]
  | succ q ih =>
      calc
        quadraticActionPrefix u ((q + 1) * T) =
            quadraticActionPrefix u (q * T) +
              quadraticActionPrefix (fun n ↦ u (q * T + n)) T := by
          simp only [Nat.succ_mul, quadraticActionPrefix,
            Finset.sum_range_add, mul_add]
        _ = (∑ j ∈ Finset.range q,
              quadraticActionPrefix (fun n ↦ u (j * T + n)) T) +
              quadraticActionPrefix (fun n ↦ u (q * T + n)) T := by
          rw [ih]
        _ = ∑ j ∈ Finset.range (q + 1),
              quadraticActionPrefix (fun n ↦ u (j * T + n)) T := by
          rw [Finset.sum_range_succ]

/-- Zero control reproduces iteration of the zero-control map. -/
theorem finiteControlOrbit_zero_eq_iterate
    {Y : Type*} (step : ℝ → Y → Y) (x₀ : Y) {T : ℕ} (n : ℕ) :
    finiteControlOrbit step x₀ (0 : Fin T → ℝ) n =
      ((step 0)^[n]) x₀ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [finiteControlOrbit, finiteControlValue, Pi.zero_apply]
      split <;> simp_all [Function.iterate_succ_apply']

/-- Every fixed controlled endpoint depends jointly continuously on the
initial state and the finite control vector. -/
theorem continuous_finiteControlOrbit
    (step : ℝ → X → X) (hstep : Continuous (Function.uncurry step))
    {T : ℕ} (n : ℕ) :
    Continuous (fun z : X × (Fin T → ℝ) ↦
      finiteControlOrbit step z.1 z.2 n) := by
  induction n with
  | zero =>
      simp only [finiteControlOrbit]
      fun_prop
  | succ n ih =>
      simp only [finiteControlOrbit, finiteControlValue]
      have hpair : Continuous (fun z : X × (Fin T → ℝ) ↦
          ((if h : n < T then z.2 ⟨n, h⟩ else 0),
            finiteControlOrbit step z.1 z.2 n)) := by
        split <;> fun_prop
      change Continuous (Function.uncurry step ∘
        fun z : X × (Fin T → ℝ) ↦
          ((if h : n < T then z.2 ⟨n, h⟩ else 0),
            finiteControlOrbit step z.1 z.2 n))
      exact hstep.comp hpair

/-- The complete finite controlled path depends jointly continuously on its
initial state and control vector. -/
theorem continuous_finiteControlPath
    (step : ℝ → X → X) (hstep : Continuous (Function.uncurry step))
    (T : ℕ) :
    Continuous (fun z : X × (Fin T → ℝ) ↦
      fun n : Fin (T + 1) ↦ finiteControlOrbit step z.1 z.2 n) := by
  apply continuous_pi
  intro n
  exact continuous_finiteControlOrbit step hstep n

/-- Pointwise convergence to a point is uniform in entrance time over a
compact set of initial states. -/
theorem exists_uniform_iterate_entrance_time
    {f : X → X} {a : X} {K H : Set X}
    (hf : Continuous f) (hK : IsCompact K)
    (hH : IsOpen H) (haH : a ∈ H)
    (hconv : ∀ x ∈ K, Tendsto (fun n : ℕ ↦ (f^[n]) x) atTop (nhds a)) :
    ∃ N : ℕ, ∀ x ∈ K, ∃ n ≤ N, (f^[n]) x ∈ H := by
  let U : ℕ → Set X := fun n ↦ (f^[n]) ⁻¹' H
  have hUopen : ∀ n, IsOpen (U n) := by
    intro n
    exact hH.preimage (hf.iterate n)
  have hcover : K ⊆ ⋃ n, U n := by
    intro x hx
    have heventually : ∀ᶠ n : ℕ in atTop, (f^[n]) x ∈ H :=
      hconv x hx (hH.mem_nhds haH)
    obtain ⟨n, hn⟩ := heventually.exists
    exact mem_iUnion.2 ⟨n, hn⟩
  obtain ⟨times, htimes⟩ :=
    hK.elim_finite_subcover U hUopen hcover
  let N : ℕ := times.sup id
  refine ⟨N, fun x hx ↦ ?_⟩
  obtain ⟨n, hnTimes, hxn⟩ := mem_iUnion₂.1 (htimes hx)
  exact ⟨n, Finset.le_sup (f := id) hnTimes, hxn⟩

/-- On a compact set of starts, sufficiently small controls keep the entire
finite controlled path uniformly close to its zero-control comparison. -/
theorem exists_uniform_finiteControl_path_radius
    (step : ℝ → X → X) (hstep : Continuous (Function.uncurry step))
    {K : Set X} (hK : IsCompact K) (T : ℕ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ r : ℝ, 0 < r ∧
      ∀ x₀ ∈ K, ∀ u : Fin T → ℝ,
        dist u 0 < r →
          ∀ n : Fin (T + 1),
            dist
              (finiteControlOrbit step x₀ (0 : Fin T → ℝ) n)
              (finiteControlOrbit step x₀ u n) < epsilon := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : (Fin T → ℝ) → K → (Fin (T + 1) → X) := fun u x₀ n ↦
    finiteControlOrbit step x₀.1 u n
  have hswap : Continuous (fun z : (Fin T → ℝ) × K ↦
      ((z.2.1, z.1) : X × (Fin T → ℝ))) := by
    fun_prop
  have hcontinuous : Continuous (Function.uncurry F) := by
    exact (continuous_finiteControlPath step hstep T).comp hswap
  have huniform : TendstoUniformly F (F 0) (nhds 0) :=
    Continuous.tendstoUniformly F hcontinuous 0
  have heventually : ∀ᶠ u in nhds (0 : Fin T → ℝ),
      ∀ x₀ : K, dist (F 0 x₀) (F u x₀) < epsilon :=
    (Metric.tendstoUniformly_iff.mp huniform) epsilon hepsilon
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp heventually
  refine ⟨r, hr, fun x₀ hx₀ u hu n ↦ ?_⟩
  have hpath := hball hu ⟨x₀, hx₀⟩
  exact (dist_pi_lt_iff hepsilon).mp hpath n

/-- Compact attraction forces a positive block-action charge whenever a
controlled path avoids a larger attractor neighborhood throughout the block.
The horizon and charge are uniform over all starts in the compact set. -/
theorem exists_uniform_action_cost_of_avoiding_attractor
    (step : ℝ → X → X) (hstep : Continuous (Function.uncurry step))
    {a : X} {K : Set X} (hK : IsCompact K)
    {inner outer : ℝ} (hinner : 0 < inner) (hgap : inner < outer)
    (hconv : ∀ x ∈ K,
      Tendsto (fun n : ℕ ↦ ((step 0)^[n]) x) atTop (nhds a)) :
    ∃ N : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ x₀ ∈ K, ∀ u : Fin (N + 1) → ℝ,
        (∀ n ≤ N, outer ≤ dist (finiteControlOrbit step x₀ u n) a) →
          c ≤ finiteQuadraticAction u := by
  have hzeroContinuous : Continuous (step 0) := by
    have hpair : Continuous (fun x : X ↦ ((0 : ℝ), x)) := by
      fun_prop
    change Continuous (Function.uncurry step ∘ fun x : X ↦ ((0 : ℝ), x))
    exact hstep.comp hpair
  obtain ⟨N, hentrance⟩ := exists_uniform_iterate_entrance_time
    (f := step 0) (a := a) (K := K) (H := Metric.ball a inner)
      hzeroContinuous hK Metric.isOpen_ball
      (Metric.mem_ball_self hinner) hconv
  have hepsilon : 0 < outer - inner := sub_pos.mpr hgap
  obtain ⟨r, hr, hclose⟩ :=
    exists_uniform_finiteControl_path_radius step hstep hK (N + 1) hepsilon
  refine ⟨N, r ^ 2 / 2, div_pos (sq_pos_of_pos hr) (by norm_num), ?_⟩
  intro x₀ hx₀ u havoid
  have hcontrol : r ≤ dist u 0 := by
    by_contra hnot
    have hsmall : dist u 0 < r := lt_of_not_ge hnot
    obtain ⟨n, hnN, hnInner⟩ := hentrance x₀ hx₀
    let i : Fin (N + 2) := ⟨n, by omega⟩
    have hnear := hclose x₀ hx₀ u hsmall i
    have hzero : finiteControlOrbit step x₀
        (0 : Fin (N + 1) → ℝ) n = ((step 0)^[n]) x₀ :=
      finiteControlOrbit_zero_eq_iterate step x₀ n
    have htriangle : dist (finiteControlOrbit step x₀ u n) a < outer := by
      have htri := dist_triangle (finiteControlOrbit step x₀ u n)
        (finiteControlOrbit step x₀ (0 : Fin (N + 1) → ℝ) n) a
      rw [hzero] at htri
      have hnDist : dist ((step 0)^[n] x₀) a < inner := hnInner
      change dist
          (finiteControlOrbit step x₀ (0 : Fin (N + 1) → ℝ) n)
          (finiteControlOrbit step x₀ u n) < outer - inner at hnear
      have hnear' : dist (finiteControlOrbit step x₀ u n)
          ((step 0)^[n] x₀) < outer - inner := by
        simpa only [hzero, dist_comm] using hnear
      linarith
    exact (not_lt_of_ge (havoid n hnN)) htriangle
  have hcoordinate : ∃ i : Fin (N + 1), r ≤ |u i| := by
    by_contra hnot
    simp only [not_exists, not_le] at hnot
    have hall : ∀ i : Fin (N + 1),
        dist (u i) ((0 : Fin (N + 1) → ℝ) i) < r := by
      intro i
      simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using hnot i
    exact (not_lt_of_ge hcontrol) ((dist_pi_lt_iff hr).2 hall)
  obtain ⟨i, hi⟩ := hcoordinate
  have hsquare : r ^ 2 ≤ (u i) ^ 2 := by
    rw [← sq_abs (u i)]
    exact (sq_le_sq₀ hr.le (abs_nonneg (u i))).2 hi
  have hterm : (u i) ^ 2 ≤ ∑ j : Fin (N + 1), (u j) ^ 2 :=
    Finset.single_le_sum (fun j _hj ↦ sq_nonneg (u j))
      (Finset.mem_univ i)
  simp only [finiteQuadraticAction]
  nlinarith

/-- The block charge accumulates linearly over arbitrarily many consecutive
blocks.  No asymptotic notation or growing-dimensional estimate is used:
the conclusion is an exact inequality at every block count. -/
theorem exists_uniform_linear_action_cost_of_avoiding_attractor
    (step : ℝ → X → X) (hstep : Continuous (Function.uncurry step))
    {a : X} {K : Set X} (hK : IsCompact K)
    {inner outer : ℝ} (hinner : 0 < inner) (hgap : inner < outer)
    (hconv : ∀ x ∈ K,
      Tendsto (fun n : ℕ ↦ ((step 0)^[n]) x) atTop (nhds a)) :
    ∃ N : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) (x₀ : X) (u : ℕ → ℝ),
        (∀ j < q,
          controlOrbit step x₀ u (j * (N + 1)) ∈ K) →
        (∀ n < q * (N + 1),
          outer ≤ dist (controlOrbit step x₀ u n) a) →
        (q : ℝ) * c ≤ quadraticActionPrefix u (q * (N + 1)) := by
  obtain ⟨N, c, hc, hblock⟩ :=
    exists_uniform_action_cost_of_avoiding_attractor
      step hstep hK hinner hgap hconv
  refine ⟨N, c, hc, ?_⟩
  intro q x₀ u hstarts havoid
  have hblockCharge : ∀ j < q,
      c ≤ quadraticActionPrefix
        (fun n ↦ u (j * (N + 1) + n)) (N + 1) := by
    intro j hj
    have hlocalAvoid : ∀ n ≤ N,
        outer ≤ dist
          (finiteControlOrbit step
            (controlOrbit step x₀ u (j * (N + 1)))
            (fun i : Fin (N + 1) ↦ u (j * (N + 1) + i)) n) a := by
      intro n hn
      rw [finiteControlOrbit_block_eq_controlOrbit
        step x₀ u (j * (N + 1)) (N + 1) n (by omega)]
      have hlocalIndex : j * (N + 1) + n < (j + 1) * (N + 1) := by
        rw [Nat.add_mul]
        simp only [one_mul]
        exact Nat.add_lt_add_left (by omega) _
      have hblockEnd : (j + 1) * (N + 1) ≤ q * (N + 1) :=
        Nat.mul_le_mul_right (N + 1) (Nat.succ_le_of_lt hj)
      exact havoid _ (hlocalIndex.trans_le hblockEnd)
    have hcFinite := hblock
      (controlOrbit step x₀ u (j * (N + 1))) (hstarts j hj)
      (fun i : Fin (N + 1) ↦ u (j * (N + 1) + i)) hlocalAvoid
    rw [finiteQuadraticAction_slice_eq] at hcFinite
    exact hcFinite
  calc
    (q : ℝ) * c = ∑ j ∈ Finset.range q, c := by simp
    _ ≤ ∑ j ∈ Finset.range q,
        quadraticActionPrefix
          (fun n ↦ u (j * (N + 1) + n)) (N + 1) := by
      exact Finset.sum_le_sum fun j hj ↦
        hblockCharge j (Finset.mem_range.mp hj)
    _ = quadraticActionPrefix u (q * (N + 1)) :=
      (quadraticActionPrefix_mul_eq_sum_blocks u q (N + 1)).symm

#print axioms exists_uniform_iterate_entrance_time
#print axioms exists_uniform_finiteControl_path_radius
#print axioms exists_uniform_action_cost_of_avoiding_attractor
#print axioms exists_uniform_linear_action_cost_of_avoiding_attractor

end

end CivicAlignment
