/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.ArrheniusBlocks

/-!
# Paper II: Gaussian block restart

This file proves the finite-product Markov restart used by the escape half of
the Arrhenius law.  A Gaussian vector is split into independent prefix and
suffix blocks, the controlled recursion is concatenated exactly, and a
uniform one-block crossing probability is iterated into geometric survival.
-/

namespace CivicAlignment.PaperII

open Filter Function MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal

noncomputable section

/-! ## Splitting finite Gaussian vectors -/

/-- The measurable equivalence which splits a vector of length `N + T` into
its first `N` and last `T` coordinates. -/
def gaussianVectorSplitEquiv (N T : ℕ) :
    (Fin (N + T) → ℝ) ≃ᵐ (Fin N → ℝ) × (Fin T → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (N + T) ↦ ℝ)
      (finSumFinEquiv : Fin N ⊕ Fin T ≃ Fin (N + T))).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ Fin T ↦ ℝ))

/-- Splitting a finite standard-Gaussian vector gives the product of the two
shorter standard-Gaussian vector laws. -/
theorem measurePreserving_gaussianVectorSplitEquiv (N T : ℕ) :
    MeasurePreserving (gaussianVectorSplitEquiv N T)
      (standardGaussianVector (N + T))
      ((standardGaussianVector N).prod (standardGaussianVector T)) := by
  unfold gaussianVectorSplitEquiv standardGaussianVector
  let μ : Fin (N + T) → Measure ℝ := fun _ ↦ gaussianReal 0 1
  have hrename :=
    (measurePreserving_piCongrLeft μ
      (finSumFinEquiv : Fin N ⊕ Fin T ≃ Fin (N + T))).symm
  have hsplit :=
    measurePreserving_sumPiEquivProdPi
      (fun _ : Fin N ⊕ Fin T ↦ gaussianReal 0 1)
  exact hsplit.comp hrename

/-- The split equivalence sends `Fin.append u v` to `(u,v)`. -/
@[simp]
theorem gaussianVectorSplitEquiv_append
    {N T : ℕ} (u : Fin N → ℝ) (v : Fin T → ℝ) :
    gaussianVectorSplitEquiv N T (Fin.append u v) = (u, v) := by
  ext i
  · change Fin.append u v
        (finSumFinEquiv (Sum.inl i)) = u i
    rw [finSumFinEquiv_apply_left, Fin.append_left]
  · change Fin.append u v
        (finSumFinEquiv (Sum.inr i)) = v i
    rw [finSumFinEquiv_apply_right, Fin.append_right]

/-- Applying the inverse split equivalence concatenates the two vectors. -/
@[simp]
theorem gaussianVectorSplitEquiv_symm_pair
    {N T : ℕ} (u : Fin N → ℝ) (v : Fin T → ℝ) :
    (gaussianVectorSplitEquiv N T).symm (u, v) = Fin.append u v := by
  apply (gaussianVectorSplitEquiv N T).injective
  simp only [MeasurableEquiv.apply_symm_apply,
    gaussianVectorSplitEquiv_append]

/-- A measurable event can be evaluated after the Gaussian split under the
product law of its prefix and suffix. -/
theorem standardGaussianVector_split_preimage
    {N T : ℕ} {s : Set ((Fin N → ℝ) × (Fin T → ℝ))}
    (hs : MeasurableSet s) :
    standardGaussianVector (N + T)
        (gaussianVectorSplitEquiv N T ⁻¹' s) =
      (standardGaussianVector N).prod (standardGaussianVector T) s := by
  rw [← Measure.map_apply (gaussianVectorSplitEquiv N T).measurable hs,
    (measurePreserving_gaussianVectorSplitEquiv N T).map_eq]

/-! ## Concatenating controlled histories -/

/-- Before the split time, an appended finite control agrees with its prefix. -/
theorem finiteControlledOrbitFrom_append_left
    (p : LoopParams) (rho : ℝ) (x₀ : LoopState)
    {N T : ℕ} (u : Fin N → ℝ) (v : Fin T → ℝ)
    {n : ℕ} (hn : n ≤ N) :
    finiteControlledOrbitFrom p rho x₀ (Fin.append u v) n =
      finiteControlledOrbitFrom p rho x₀ u n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hnlt : n < N := by omega
      have hbig : n < N + T := hnlt.trans_le (Nat.le_add_right N T)
      rw [finiteControlledOrbitFrom, finiteControlledOrbitFrom, ih (by omega)]
      simp only [extendFiniteControl, hbig, hnlt, dite_true]
      rw [show (⟨n, hbig⟩ : Fin (N + T)) = Fin.castAdd T ⟨n, hnlt⟩ by
        ext
        rfl]
      rw [Fin.append_left]

/-- After the split time, an appended finite control restarts the same
recursion from the prefix endpoint and uses the suffix controls. -/
theorem finiteControlledOrbitFrom_append_right
    (p : LoopParams) (rho : ℝ) (x₀ : LoopState)
    {N T : ℕ} (u : Fin N → ℝ) (v : Fin T → ℝ)
    {k : ℕ} (hk : k ≤ T) :
    finiteControlledOrbitFrom p rho x₀ (Fin.append u v) (N + k) =
      finiteControlledOrbitFrom p rho
        (finiteControlledOrbitFrom p rho x₀ u N) v k := by
  induction k with
  | zero =>
      simpa only [Nat.add_zero, finiteControlledOrbitFrom] using
        finiteControlledOrbitFrom_append_left p rho x₀ u v le_rfl
  | succ k ih =>
      have hklt : k < T := by omega
      rw [Nat.add_succ, finiteControlledOrbitFrom, ih (by omega),
        finiteControlledOrbitFrom]
      simp only [extendFiniteControl]
      have hNk : N + k < N + T := Nat.add_lt_add_left hklt N
      simp only [hNk, hklt, dite_true]
      rw [show (⟨N + k, hNk⟩ : Fin (N + T)) = Fin.natAdd N ⟨k, hklt⟩ by
        ext
        simp]
      exact congrArg (fun control ↦ controlledCivicWeightedStep p rho control
        (finiteControlledOrbitFrom p rho
          (finiteControlledOrbitFrom p rho x₀ u N) v k))
        (Fin.append_right u v ⟨k, hklt⟩)

/-- Scaling a concatenated Gaussian vector concatenates the corresponding
finite control vectors. -/
theorem scaledGaussianControl_append
    {N T : ℕ} (sigma : ℝ) (u : Fin N → ℝ) (v : Fin T → ℝ) :
    scaledGaussianControl sigma (Fin.append u v) =
      Fin.append (scaledGaussianControl sigma u)
        (scaledGaussianControl sigma v) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [scaledGaussianControl]
  · intro j
    simp [scaledGaussianControl]

/-! ## Finite survival and the restart identity -/

/-- A running maximum is strictly below a level exactly when every coordinate
through that time is strictly below the level. -/
theorem runningMax_lt_iff {a : ℕ → ℝ} {c : ℝ} {n : ℕ} :
    runningMax a n < c ↔ ∀ k ≤ n, a k < c := by
  constructor
  · intro h k hk
    exact (policy_le_runningMax (fun j ↦ (a j, 0)) k).trans_lt
      ((monotone_runningMax a hk).trans_lt h)
  · intro h
    exact lt_of_not_ge fun hge ↦ by
      obtain ⟨k, hk, hck⟩ := (le_runningMax_iff (a := a)).1 hge
      exact (not_le_of_gt (h k hk)) hck

/-- Failure to cross the saddle during a finite arbitrary-start window. -/
def gaussianSurvivalEventFrom {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (x₀ : LoopState)
    (T : ℕ) (sigma : ℝ) : Set (Fin T → ℝ) :=
  (gaussianCrossingEventFrom weighted x₀ T sigma)ᶜ

/-- The arbitrary-start finite-window survival probability. -/
def gaussianSurvivalProbabilityFrom {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (x₀ : LoopState)
    (T : ℕ) (sigma : ℝ) : ℝ≥0∞ :=
  standardGaussianVector T
    (gaussianSurvivalEventFrom weighted x₀ T sigma)

/-- Finite survival is Borel measurable. -/
theorem measurableSet_gaussianSurvivalEventFrom
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (x₀ : LoopState)
    (T : ℕ) (sigma : ℝ) :
    MeasurableSet (gaussianSurvivalEventFrom weighted x₀ T sigma) :=
  (measurableSet_gaussianCrossingEventFrom weighted x₀ T sigma).compl

/-- Survival probability is one minus crossing probability. -/
theorem gaussianSurvivalProbabilityFrom_eq_one_sub
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (x₀ : LoopState)
    (T : ℕ) (sigma : ℝ) :
    gaussianSurvivalProbabilityFrom weighted x₀ T sigma =
      1 - gaussianCrossingProbabilityFrom weighted x₀ T sigma := by
  letI : IsProbabilityMeasure (standardGaussianVector T) := by
    unfold standardGaussianVector
    infer_instance
  unfold gaussianSurvivalProbabilityFrom gaussianSurvivalEventFrom
  rw [measure_compl
    (measurableSet_gaussianCrossingEventFrom weighted x₀ T sigma)
    (measure_ne_top (standardGaussianVector T) _)]
  rw [measure_univ]
  rfl

/-- Exact pathwise restart: a concatenated noise vector survives precisely
when its prefix survives and its suffix survives from the prefix endpoint. -/
theorem mem_gaussianSurvivalEventFrom_append_iff
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (x₀ : LoopState)
    {N T : ℕ} (sigma : ℝ) (u : Fin N → ℝ) (v : Fin T → ℝ) :
    Fin.append u v ∈ gaussianSurvivalEventFrom weighted x₀ (N + T) sigma ↔
      u ∈ gaussianSurvivalEventFrom weighted x₀ N sigma ∧
      v ∈ gaussianSurvivalEventFrom weighted
        (finiteControlledOrbitFrom p rho x₀
          (scaledGaussianControl sigma u) N) T sigma := by
  simp only [gaussianSurvivalEventFrom, mem_compl_iff,
    gaussianCrossingEventFrom, mem_setOf_eq, not_le]
  simp only [policyRunningMax]
  rw [runningMax_lt_iff, runningMax_lt_iff, runningMax_lt_iff]
  constructor
  · intro h
    constructor
    · intro n hn
      rw [← finiteControlledOrbitFrom_append_left p rho x₀
        (scaledGaussianControl sigma u) (scaledGaussianControl sigma v) hn,
        ← scaledGaussianControl_append]
      exact h n (hn.trans (Nat.le_add_right N T))
    · intro k hk
      rw [← finiteControlledOrbitFrom_append_right p rho x₀
        (scaledGaussianControl sigma u) (scaledGaussianControl sigma v) hk,
        ← scaledGaussianControl_append]
      exact h (N + k) (Nat.add_le_add_left hk N)
  · rintro ⟨hprefix, hsuffix⟩ n hn
    by_cases hnPrefix : n ≤ N
    · rw [scaledGaussianControl_append,
        finiteControlledOrbitFrom_append_left p rho x₀
          (scaledGaussianControl sigma u) (scaledGaussianControl sigma v) hnPrefix]
      exact hprefix n hnPrefix
    · have hNn : N ≤ n := Nat.le_of_lt (lt_of_not_ge hnPrefix)
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNn
      have hk : k ≤ T := by omega
      rw [scaledGaussianControl_append,
        finiteControlledOrbitFrom_append_right p rho x₀
          (scaledGaussianControl sigma u) (scaledGaussianControl sigma v) hk]
      exact hsuffix k hk

/-! ## One-block probability recurrence -/

/-- The survival event transported to independent prefix/suffix coordinates. -/
def gaussianRestartSurvivalSet {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (x₀ : LoopState)
    (N T : ℕ) (sigma : ℝ) :
    Set ((Fin N → ℝ) × (Fin T → ℝ)) :=
  (gaussianVectorSplitEquiv N T).symm ⁻¹'
    gaussianSurvivalEventFrom weighted x₀ (N + T) sigma

/-- The transported restart event is measurable. -/
theorem measurableSet_gaussianRestartSurvivalSet
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (x₀ : LoopState)
    (N T : ℕ) (sigma : ℝ) :
    MeasurableSet (gaussianRestartSurvivalSet weighted x₀ N T sigma) := by
  exact (measurableSet_gaussianSurvivalEventFrom
    weighted x₀ (N + T) sigma).preimage
      (gaussianVectorSplitEquiv N T).symm.measurable

/-- After a surviving prefix, the restart fiber is exactly the suffix-survival
event from the prefix endpoint. -/
theorem gaussianRestartSurvivalSet_fiber_of_mem
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (x₀ : LoopState)
    {N T : ℕ} (sigma : ℝ) (u : Fin N → ℝ)
    (hu : u ∈ gaussianSurvivalEventFrom weighted x₀ N sigma) :
    Prod.mk u ⁻¹' gaussianRestartSurvivalSet weighted x₀ N T sigma =
      gaussianSurvivalEventFrom weighted
        (finiteControlledOrbitFrom p rho x₀
          (scaledGaussianControl sigma u) N) T sigma := by
  ext v
  simp only [mem_preimage]
  rw [show ((u, v) ∈ gaussianRestartSurvivalSet weighted x₀ N T sigma) ↔
      Fin.append u v ∈
        gaussianSurvivalEventFrom weighted x₀ (N + T) sigma by
    simp only [gaussianRestartSurvivalSet, mem_preimage,
      gaussianVectorSplitEquiv_symm_pair]]
  rw [mem_gaussianSurvivalEventFrom_append_iff]
  simp only [hu, true_and]

/-- After a failed prefix, the restart fiber is empty. -/
theorem gaussianRestartSurvivalSet_fiber_of_notMem
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (x₀ : LoopState)
    {N T : ℕ} (sigma : ℝ) (u : Fin N → ℝ)
    (hu : u ∉ gaussianSurvivalEventFrom weighted x₀ N sigma) :
    Prod.mk u ⁻¹' gaussianRestartSurvivalSet weighted x₀ N T sigma = ∅ := by
  ext v
  simp only [mem_preimage]
  rw [show ((u, v) ∈ gaussianRestartSurvivalSet weighted x₀ N T sigma) ↔
      Fin.append u v ∈
        gaussianSurvivalEventFrom weighted x₀ (N + T) sigma by
    simp only [gaussianRestartSurvivalSet, mem_preimage,
      gaussianVectorSplitEquiv_symm_pair]]
  rw [mem_gaussianSurvivalEventFrom_append_iff]
  simp only [hu, false_and, mem_empty_iff_false]

/-- Under the product decomposition, the measure of full survival is the
measure of the restart set. -/
theorem gaussianSurvivalProbabilityFrom_eq_restartMeasure
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (x₀ : LoopState)
    (N T : ℕ) (sigma : ℝ) :
    gaussianSurvivalProbabilityFrom weighted x₀ (N + T) sigma =
      (standardGaussianVector N).prod (standardGaussianVector T)
        (gaussianRestartSurvivalSet weighted x₀ N T sigma) := by
  unfold gaussianSurvivalProbabilityFrom
  have hpreimage :
      gaussianVectorSplitEquiv N T ⁻¹'
          gaussianRestartSurvivalSet weighted x₀ N T sigma =
        gaussianSurvivalEventFrom weighted x₀ (N + T) sigma := by
    ext xi
    simp only [gaussianRestartSurvivalSet, mem_preimage,
      MeasurableEquiv.symm_apply_apply]
  rw [← hpreimage]
  exact standardGaussianVector_split_preimage
    (measurableSet_gaussianRestartSurvivalSet weighted x₀ N T sigma)

/-- If every pre-crossing state has one-block crossing probability at least
`q`, then survival from the calibrated state contracts by `1-q` after that
block.  The prefix length `N` is arbitrary, which is the finite-dimensional
Markov restart needed for iteration. -/
theorem gaussianSurvivalProbabilityFrom_add_le
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    (N T : ℕ) (sigma : ℝ) (q : ℝ≥0∞)
    (hq : ∀ x ∈ absorbingBox p ∩
        Icc (calibratedPoint p) (weightedSaddlePoint weighted),
      q ≤ gaussianCrossingProbabilityFrom weighted x T sigma) :
    gaussianSurvivalProbabilityFrom weighted (calibratedPoint p)
        (N + T) sigma ≤
      gaussianSurvivalProbabilityFrom weighted (calibratedPoint p) N sigma *
        (1 - q) := by
  let μN := standardGaussianVector N
  let μT := standardGaussianVector T
  let S := gaussianRestartSurvivalSet weighted (calibratedPoint p) N T sigma
  let A := gaussianSurvivalEventFrom weighted (calibratedPoint p) N sigma
  letI : IsProbabilityMeasure μN := by
    dsimp only [μN, standardGaussianVector]
    infer_instance
  letI : IsProbabilityMeasure μT := by
    dsimp only [μT, standardGaussianVector]
    infer_instance
  have hS : MeasurableSet S :=
    measurableSet_gaussianRestartSurvivalSet
      weighted (calibratedPoint p) N T sigma
  have hA : MeasurableSet A :=
    measurableSet_gaussianSurvivalEventFrom
      weighted (calibratedPoint p) N sigma
  have hfiber : ∀ u : Fin N → ℝ,
      μT (Prod.mk u ⁻¹' S) ≤ A.indicator (fun _ ↦ 1 - q) u := by
    intro u
    by_cases hu : u ∈ A
    · rw [indicator_of_mem hu]
      have hmaxlt :
          policyRunningMax
              (finiteControlledOrbitFrom p rho (calibratedPoint p)
                (scaledGaussianControl sigma u)) N < weighted.βdagger := by
        simpa only [A, gaussianSurvivalEventFrom, mem_compl_iff,
          gaussianCrossingEventFrom, mem_setOf_eq, not_le] using hu
      have hstart :
          finiteControlledOrbitFrom p rho (calibratedPoint p)
              (scaledGaussianControl sigma u) N ∈
            absorbingBox p ∩
              Icc (calibratedPoint p) (weightedSaddlePoint weighted) := by
        have hpath : IsControlledCivicWeightedPath p rho
            (extendFiniteControl (scaledGaussianControl sigma u))
            (finiteControlledOrbitFrom p rho (calibratedPoint p)
              (scaledGaussianControl sigma u)) := by
          constructor
          · rfl
          · intro n
            rfl
        have hmem := hpath.mem_weightedSaddleOrderInterval
          model ss weighted hmaxlt.le
        exact hmem
      have hu' : u ∈ gaussianSurvivalEventFrom weighted
          (calibratedPoint p) N sigma := hu
      dsimp only [S]
      rw [gaussianRestartSurvivalSet_fiber_of_mem weighted
        (calibratedPoint p) sigma u hu']
      exact prob_compl_le_one_sub_of_le_prob
        (hq _ hstart)
        (measurableSet_gaussianCrossingEventFrom weighted
          (finiteControlledOrbitFrom p rho (calibratedPoint p)
            (scaledGaussianControl sigma u) N) T sigma)
    · rw [indicator_of_notMem hu]
      have hu' : u ∉ gaussianSurvivalEventFrom weighted
          (calibratedPoint p) N sigma := hu
      dsimp only [S]
      rw [gaussianRestartSurvivalSet_fiber_of_notMem weighted
        (calibratedPoint p) sigma u hu']
      simp only [measure_empty]
      exact le_rfl
  calc
    gaussianSurvivalProbabilityFrom weighted (calibratedPoint p)
        (N + T) sigma = μN.prod μT S := by
      exact gaussianSurvivalProbabilityFrom_eq_restartMeasure
        weighted (calibratedPoint p) N T sigma
    _ = ∫⁻ u, μT (Prod.mk u ⁻¹' S) ∂μN :=
      Measure.prod_apply hS
    _ ≤ ∫⁻ u, A.indicator (fun _ ↦ 1 - q) u ∂μN :=
      lintegral_mono hfiber
    _ = (1 - q) * μN A := lintegral_indicator_const hA (1 - q)
    _ = gaussianSurvivalProbabilityFrom weighted (calibratedPoint p) N sigma *
        (1 - q) := by
      rw [mul_comm]
      rfl

/-! ## Geometric iteration and mean-time bridge -/

/-- At the calibrated start, the arbitrary-start crossing probability is the
finite-window escape probability used by the canonical process. -/
theorem gaussianCrossingProbabilityFrom_calibratedPoint
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (T : ℕ) (sigma : ℝ) :
    gaussianCrossingProbabilityFrom weighted (calibratedPoint p) T sigma =
      gaussianEscapeProbability weighted T sigma := by
  unfold gaussianCrossingProbabilityFrom gaussianEscapeProbability
  congr 1
  ext xi
  simp only [gaussianCrossingEventFrom, gaussianEscapeEvent, mem_setOf_eq]
  have horbit :
      finiteControlledOrbitFrom p rho (calibratedPoint p)
          (scaledGaussianControl sigma xi) =
        finiteControlledOrbit p rho (scaledGaussianControl sigma xi) := by
    funext n
    exact finiteControlledOrbitFrom_calibratedPoint p rho
      (scaledGaussianControl sigma xi) n
  rw [horbit]

/-- Escape probability is monotone in the time horizon. -/
theorem monotone_gaussianEscapeProbability
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (sigma : ℝ) :
    Monotone (fun T ↦ gaussianEscapeProbability weighted T sigma) := by
  intro N T hNT
  change gaussianEscapeProbability weighted N sigma ≤
    gaussianEscapeProbability weighted T sigma
  rw [← standardGaussianSequence_escapeByEvent weighted N sigma,
    ← standardGaussianSequence_escapeByEvent weighted T sigma]
  apply measure_mono
  intro xi hxi
  exact hxi.trans
    ((monotone_runningMax
      (fun n ↦ (gaussianNoisyOrbit p rho sigma xi n).1)) hNT)

/-- A uniform one-block crossing lower bound gives geometric survival on
integer multiples of the block horizon. -/
theorem gaussianSurvivalProbabilityFrom_mul_le_pow
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    (T : ℕ) (sigma : ℝ) (q : ℝ≥0∞)
    (hq : ∀ x ∈ absorbingBox p ∩
        Icc (calibratedPoint p) (weightedSaddlePoint weighted),
      q ≤ gaussianCrossingProbabilityFrom weighted x T sigma) :
    ∀ k : ℕ,
      gaussianSurvivalProbabilityFrom weighted (calibratedPoint p)
          (k * T) sigma ≤ (1 - q) ^ k := by
  intro k
  induction k with
  | zero =>
      letI : IsProbabilityMeasure (standardGaussianVector 0) := by
        unfold standardGaussianVector
        infer_instance
      simp only [zero_mul, pow_zero]
      unfold gaussianSurvivalProbabilityFrom
      exact prob_le_one
  | succ k ih =>
      calc
        gaussianSurvivalProbabilityFrom weighted (calibratedPoint p)
            ((k + 1) * T) sigma =
            gaussianSurvivalProbabilityFrom weighted (calibratedPoint p)
              (k * T + T) sigma := by
                rw [Nat.add_mul, one_mul]
        _ ≤ gaussianSurvivalProbabilityFrom weighted (calibratedPoint p)
              (k * T) sigma * (1 - q) :=
          gaussianSurvivalProbabilityFrom_add_le
            model ss weighted (k * T) T sigma q hq
        _ ≤ (1 - q) ^ k * (1 - q) :=
          mul_le_mul_of_nonneg_right ih bot_le
        _ = (1 - q) ^ (k + 1) := (pow_succ (1 - q) k).symm

/-- The same geometric estimate stated for the canonical finite-window escape
probabilities. -/
theorem one_sub_gaussianEscapeProbability_mul_le_pow
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    (T : ℕ) (sigma : ℝ) (q : ℝ≥0∞)
    (hq : ∀ x ∈ absorbingBox p ∩
        Icc (calibratedPoint p) (weightedSaddlePoint weighted),
      q ≤ gaussianCrossingProbabilityFrom weighted x T sigma)
    (k : ℕ) :
    1 - gaussianEscapeProbability weighted (k * T) sigma ≤
      (1 - q) ^ k := by
  rw [← gaussianCrossingProbabilityFrom_calibratedPoint]
  rw [← gaussianSurvivalProbabilityFrom_eq_one_sub]
  exact gaussianSurvivalProbabilityFrom_mul_le_pow
    model ss weighted T sigma q hq k

/-- Repeating each term of a geometric series `T` times multiplies its sum by
`T`.  The quotient/remainder equivalence makes the block accounting exact. -/
theorem tsum_pow_nat_div
    (T : ℕ) (hT : 0 < T) (r : ℝ≥0∞) :
    (∑' n : ℕ, r ^ (n / T)) =
      (T : ℝ≥0∞) * (1 - r)⁻¹ := by
  letI : NeZero T := ⟨hT.ne'⟩
  calc
    (∑' n : ℕ, r ^ (n / T)) =
        ∑' z : ℕ × Fin T,
          r ^ (((Nat.divModEquiv T).symm z) / T) :=
      ((Nat.divModEquiv T).symm.tsum_eq
        (fun n : ℕ ↦ r ^ (n / T))).symm
    _ = ∑' z : ℕ × Fin T, r ^ z.1 := by
      congr 1
      funext z
      congr 1
      rw [Nat.divModEquiv_symm_apply, Nat.mul_comm z.1 T,
        Nat.mul_add_div hT,
        Nat.div_eq_of_lt z.2.isLt, add_zero]
    _ = ∑' k : ℕ, ∑' _i : Fin T, r ^ k := by
      simpa only using
        (ENNReal.tsum_prod
          (f := fun (k : ℕ) (_i : Fin T) ↦ r ^ k))
    _ = ∑' k : ℕ, (T : ℝ≥0∞) * r ^ k := by
      congr 1
      funext k
      rw [tsum_fintype]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    _ = (T : ℝ≥0∞) * ∑' k : ℕ, r ^ k := ENNReal.tsum_mul_left
    _ = (T : ℝ≥0∞) * (1 - r)⁻¹ := by
      rw [ENNReal.tsum_geometric]

/-- The block-geometric restart estimate bounds the full mean first-passage
time by the block length times the inverse one-block success probability. -/
theorem meanGaussianEscapeTime_le_block_mul_inv
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    (T : ℕ) (hT : 0 < T) (sigma : ℝ) (q : ℝ≥0∞)
    (hq : ∀ x ∈ absorbingBox p ∩
        Icc (calibratedPoint p) (weightedSaddlePoint weighted),
      q ≤ gaussianCrossingProbabilityFrom weighted x T sigma) :
    meanGaussianEscapeTime weighted sigma ≤ (T : ℝ≥0∞) * q⁻¹ := by
  have hsurvival : ∀ n : ℕ,
      1 - gaussianEscapeProbability weighted n sigma ≤
        (1 - q) ^ (n / T) := by
    intro n
    have hblock : n / T * T ≤ n := Nat.div_mul_le_self n T
    have hanti :
        1 - gaussianEscapeProbability weighted n sigma ≤
          1 - gaussianEscapeProbability weighted (n / T * T) sigma :=
      tsub_le_tsub_left
        (monotone_gaussianEscapeProbability weighted sigma hblock) 1
    exact hanti.trans
      (one_sub_gaussianEscapeProbability_mul_le_pow
        model ss weighted T sigma q hq (n / T))
  have hqOne : q ≤ 1 := by
    have hzero : (0 : ℝ) ∈ Icc 0 1 := by norm_num
    have hbeta : weighted.βdagger ∈ Icc (0 : ℝ) 1 :=
      ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩
    have hp₁mem : calibratedPoint p ∈ absorbingBox p :=
      ⟨by simp [calibratedPoint],
        stationaryStock_mem_stockInterval model hzero⟩
    have hp₁le : calibratedPoint p ≤ weightedSaddlePoint weighted := by
      constructor
      · simpa only [calibratedPoint, weightedSaddlePoint] using
          weighted.βdagger_mem.1.le
      · exact (stationaryStock_strictMonoOn model).monotoneOn
          hzero hbeta weighted.βdagger_mem.1.le
    have hcross := hq (calibratedPoint p) ⟨hp₁mem, le_rfl, hp₁le⟩
    letI : IsProbabilityMeasure (standardGaussianVector T) := by
      unfold standardGaussianVector
      infer_instance
    exact hcross.trans prob_le_one
  calc
    meanGaussianEscapeTime weighted sigma ≤
        ∑' n : ℕ, (1 - q) ^ (n / T) :=
      meanGaussianEscapeTime_le_tsum_of_survival_le
        weighted sigma (fun n ↦ (1 - q) ^ (n / T)) hsurvival
    _ = (T : ℝ≥0∞) * (1 - (1 - q))⁻¹ :=
      tsum_pow_nat_div T hT (1 - q)
    _ = (T : ℝ≥0∞) * q⁻¹ := by
      rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top hqOne]

#print axioms measurePreserving_gaussianVectorSplitEquiv
#print axioms gaussianVectorSplitEquiv_append
#print axioms gaussianVectorSplitEquiv_symm_pair
#print axioms standardGaussianVector_split_preimage
#print axioms finiteControlledOrbitFrom_append_left
#print axioms finiteControlledOrbitFrom_append_right
#print axioms scaledGaussianControl_append
#print axioms runningMax_lt_iff
#print axioms measurableSet_gaussianSurvivalEventFrom
#print axioms gaussianSurvivalProbabilityFrom_eq_one_sub
#print axioms mem_gaussianSurvivalEventFrom_append_iff
#print axioms measurableSet_gaussianRestartSurvivalSet
#print axioms gaussianRestartSurvivalSet_fiber_of_mem
#print axioms gaussianRestartSurvivalSet_fiber_of_notMem
#print axioms gaussianSurvivalProbabilityFrom_eq_restartMeasure
#print axioms gaussianSurvivalProbabilityFrom_add_le
#print axioms gaussianCrossingProbabilityFrom_calibratedPoint
#print axioms monotone_gaussianEscapeProbability
#print axioms gaussianSurvivalProbabilityFrom_mul_le_pow
#print axioms one_sub_gaussianEscapeProbability_mul_le_pow
#print axioms tsum_pow_nat_div
#print axioms meanGaussianEscapeTime_le_block_mul_inv

end

end CivicAlignment.PaperII
