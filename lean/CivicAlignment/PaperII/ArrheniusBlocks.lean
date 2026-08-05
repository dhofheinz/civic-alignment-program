/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.ArrheniusFlooredLedger
import CivicAlignment.PaperII.ArrheniusCrossing

/-!
# Paper II: parameterized crossing blocks

The persistence proof for the Arrhenius law uses the same finite-dimensional
Gaussian estimate at two different deterministic rates.  The printed bracket
uses the last-exit ledger, while the sharp theorem uses the crossing
quasipotential together with a finite-horizon transport error.  This file keeps
that probability argument independent of either source: a
`NoCheapCrossingRate` certificate is exactly the deterministic input consumed
by the Chernoff bound.
-/

namespace CivicAlignment.PaperII

open Filter Function MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal Interval

noncomputable section

/-! ## Arbitrary-start finite crossing windows -/

/-- The saddle-crossing event over a finite noise window from an arbitrary
initial state. -/
def gaussianCrossingEventFrom {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (x₀ : LoopState)
    (T : ℕ) (sigma : ℝ) : Set (Fin T → ℝ) :=
  {xi | weighted.βdagger ≤
    policyRunningMax
      (finiteControlledOrbitFrom p rho x₀
        (scaledGaussianControl sigma xi)) T}

/-- The probability of the arbitrary-start finite crossing event. -/
def gaussianCrossingProbabilityFrom {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (x₀ : LoopState)
    (T : ℕ) (sigma : ℝ) : ℝ≥0∞ :=
  standardGaussianVector T
    (gaussianCrossingEventFrom weighted x₀ T sigma)

/-- Reaching a strip of width `margin` immediately below the saddle over a
finite arbitrary-start noise window. -/
def gaussianNearCrossingEventFrom {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (margin : ℝ)
    (x₀ : LoopState) (T : ℕ) (sigma : ℝ) : Set (Fin T → ℝ) :=
  {xi | weighted.βdagger - margin ≤
    policyRunningMax
      (finiteControlledOrbitFrom p rho x₀
        (scaledGaussianControl sigma xi)) T}

/-- Probability of reaching the near-saddle strip in a finite window. -/
def gaussianNearCrossingProbabilityFrom {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (margin : ℝ)
    (x₀ : LoopState) (T : ℕ) (sigma : ℝ) : ℝ≥0∞ :=
  standardGaussianVector T
    (gaussianNearCrossingEventFrom weighted margin x₀ T sigma)

/-- At fixed start and horizon, the policy running maximum is continuous in
the finite control vector. -/
theorem continuous_policyRunningMax_finiteControlledOrbitFrom
    (p : LoopParams) (rho : ℝ) (x₀ : LoopState) {T : ℕ} (n : ℕ) :
    Continuous (fun u : Fin T → ℝ ↦
      policyRunningMax (finiteControlledOrbitFrom p rho x₀ u) n) := by
  induction n with
  | zero =>
      simpa only [policyRunningMax, runningMax_zero,
        finiteControlledOrbitFrom] using
        (continuous_const : Continuous (fun _ : Fin T → ℝ ↦ x₀.1))
  | succ n ih =>
      have hstate : Continuous (fun u : Fin T → ℝ ↦
        finiteControlledOrbitFrom p rho x₀ u (n + 1)) := by
        have hpair : Continuous (fun u : Fin T → ℝ ↦ (x₀, u)) :=
          continuous_const.prodMk continuous_id
        exact (continuous_finiteControlledOrbitFrom p rho (T := T)
          (n + 1)).comp hpair
      simpa only [policyRunningMax, runningMax_succ] using
        ih.max hstate.fst

/-- The arbitrary-start finite crossing event is Borel measurable. -/
theorem measurableSet_gaussianCrossingEventFrom
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (x₀ : LoopState)
    (T : ℕ) (sigma : ℝ) :
    MeasurableSet (gaussianCrossingEventFrom weighted x₀ T sigma) := by
  change MeasurableSet ((fun xi : Fin T → ℝ ↦
    policyRunningMax
      (finiteControlledOrbitFrom p rho x₀
        (scaledGaussianControl sigma xi)) T) ⁻¹'
          Ici weighted.βdagger)
  apply measurableSet_Ici.preimage
  exact (continuous_policyRunningMax_finiteControlledOrbitFrom
      p rho x₀ T).measurable.comp
    (by unfold scaledGaussianControl; fun_prop)

/-- The arbitrary-start near-saddle reaching event is Borel measurable. -/
theorem measurableSet_gaussianNearCrossingEventFrom
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (margin : ℝ)
    (x₀ : LoopState) (T : ℕ) (sigma : ℝ) :
    MeasurableSet
      (gaussianNearCrossingEventFrom weighted margin x₀ T sigma) := by
  change MeasurableSet ((fun xi : Fin T → ℝ ↦
    policyRunningMax
      (finiteControlledOrbitFrom p rho x₀
        (scaledGaussianControl sigma xi)) T) ⁻¹'
          Ici (weighted.βdagger - margin))
  apply measurableSet_Ici.preimage
  exact (continuous_policyRunningMax_finiteControlledOrbitFrom
      p rho x₀ T).measurable.comp
    (by unfold scaledGaussianControl; fun_prop)

/-- Scaling every coordinate by `sigma` scales the quadratic action by
`sigma^2`. -/
theorem gaussianVectorAction_scaledGaussianControl
    {T : ℕ} (sigma : ℝ) (xi : Fin T → ℝ) :
    gaussianVectorAction (scaledGaussianControl sigma xi) =
      sigma ^ 2 * gaussianVectorAction xi := by
  simp only [gaussianVectorAction, scaledGaussianControl, mul_pow,
    Finset.mul_sum]
  ring_nf

/-! ## Uniform finite-history continuity -/

/-- The complete finite state history through time `T`. -/
def finiteControlledHistoryFrom (p : LoopParams) (rho : ℝ)
    (x₀ : LoopState) {T : ℕ} (u : Fin T → ℝ) :
    Fin (T + 1) → LoopState :=
  fun n ↦ finiteControlledOrbitFrom p rho x₀ u n

/-- The complete finite history depends jointly continuously on the start and
control vector. -/
theorem continuous_finiteControlledHistoryFrom
    (p : LoopParams) (rho : ℝ) {T : ℕ} :
    Continuous (fun z : LoopState × (Fin T → ℝ) ↦
      finiteControlledHistoryFrom p rho z.1 z.2) := by
  apply continuous_pi
  intro n
  exact continuous_finiteControlledOrbitFrom p rho n

/-- On a bounded set of finite controls, all states through a fixed horizon
depend uniformly continuously on the initial state. -/
theorem exists_uniform_start_radius_on_controlBall
    (p : LoopParams) (rho : ℝ) (y₀ : LoopState)
    {T : ℕ} (R : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ r : ℝ, 0 < r ∧
      ∀ x₀ : LoopState, dist x₀ y₀ < r →
        ∀ u : Fin T → ℝ, dist u 0 ≤ R →
          ∀ n : Fin (T + 1),
            dist (finiteControlledOrbitFrom p rho y₀ u n)
              (finiteControlledOrbitFrom p rho x₀ u n) < epsilon := by
  let K : Set (Fin T → ℝ) := Metric.closedBall 0 R
  have hK : IsCompact K := ProperSpace.isCompact_closedBall 0 R
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : LoopState → K → (Fin (T + 1) → LoopState) := fun x₀ u ↦
    finiteControlledHistoryFrom p rho x₀ u.1
  have hswap : Continuous (fun z : LoopState × K ↦
      ((z.1, z.2.1) : LoopState × (Fin T → ℝ))) := by
    fun_prop
  have hcontinuous : Continuous (Function.uncurry F) := by
    exact (continuous_finiteControlledHistoryFrom p rho).comp hswap
  have huniform : TendstoUniformly F (F y₀) (nhds y₀) :=
    Continuous.tendstoUniformly F hcontinuous y₀
  have heventually : ∀ᶠ x₀ in nhds y₀,
      ∀ u : K, dist (F y₀ u) (F x₀ u) < epsilon :=
    (Metric.tendstoUniformly_iff.mp huniform) epsilon hepsilon
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp heventually
  refine ⟨r, hr, fun x₀ hx₀ u hu n ↦ ?_⟩
  have hhistory := hball hx₀ ⟨u, hu⟩
  exact (dist_pi_lt_iff hepsilon).1 hhistory n

/-- A quadratic-action bound gives a simple sup-metric bound on the finite
control vector.  The deliberately loose radius `2*A+1` avoids square-root API
friction and is sufficient for compactness. -/
theorem dist_control_zero_le_two_mul_actionBound_add_one
    {T : ℕ} {u : Fin T → ℝ} {A : ℝ}
    (hA : gaussianVectorAction u ≤ A) (hA0 : 0 ≤ A) :
    dist u 0 ≤ 2 * A + 1 := by
  have hR : 0 ≤ 2 * A + 1 := by linarith
  apply (dist_pi_le_iff hR).2
  intro i
  have hterm : (u i) ^ 2 ≤ ∑ j : Fin T, (u j) ^ 2 :=
    Finset.single_le_sum (fun j _hj ↦ sq_nonneg (u j))
      (Finset.mem_univ i)
  have hsum : ∑ j : Fin T, (u j) ^ 2 ≤ 2 * A := by
    simp only [gaussianVectorAction] at hA
    linarith
  have habs : |u i| ≤ (u i) ^ 2 + 1 := by
    nlinarith [sq_nonneg (|u i| - 1), sq_abs (u i)]
  simp only [Pi.zero_apply, Real.dist_eq, sub_zero]
  exact habs.trans (by linarith)

/-! ## A one-coordinate crossing correction -/

/-- Add `q` to one coordinate of a finite control vector. -/
def bumpFiniteControl {T : ℕ} (u : Fin T → ℝ) (i : Fin T) (q : ℝ) :
    Fin T → ℝ :=
  fun j ↦ u j + if j = i then q else 0

@[simp]
theorem bumpFiniteControl_self {T : ℕ} (u : Fin T → ℝ)
    (i : Fin T) (q : ℝ) :
    bumpFiniteControl u i q i = u i + q := by
  simp only [bumpFiniteControl, ↓reduceIte]

@[simp]
theorem bumpFiniteControl_of_ne {T : ℕ} (u : Fin T → ℝ)
    {i j : Fin T} (q : ℝ) (hji : j ≠ i) :
    bumpFiniteControl u i q j = u j := by
  simp only [bumpFiniteControl, hji, ↓reduceIte, add_zero]

/-- A bump at coordinate `i` does not change the path through time `i`. -/
theorem finiteControlledOrbitFrom_bump_eq_of_le
    (p : LoopParams) (rho : ℝ) (x₀ : LoopState)
    {T : ℕ} (u : Fin T → ℝ) (i : Fin T) (q : ℝ)
    {n : ℕ} (hn : n ≤ i) :
    finiteControlledOrbitFrom p rho x₀ (bumpFiniteControl u i q) n =
      finiteControlledOrbitFrom p rho x₀ u n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hnltT : n < T := by omega
      have hindexNe : (⟨n, hnltT⟩ : Fin T) ≠ i := by
        intro heq
        have : n = i := congrArg Fin.val heq
        omega
      rw [finiteControlledOrbitFrom, finiteControlledOrbitFrom,
        ih (by omega)]
      simp only [extendFiniteControl, hnltT, dite_true,
        bumpFiniteControl_of_ne u q hindexNe]

/-- At the bumped coordinate's step, the raw policy input increases by
exactly `alpha*q`. -/
theorem finiteControlledOrbitFrom_bump_succ_policy
    (p : LoopParams) (rho : ℝ) (x₀ : LoopState)
    {T : ℕ} (u : Fin T → ℝ) (i : Fin T) (q : ℝ) :
    (finiteControlledOrbitFrom p rho x₀ (bumpFiniteControl u i q)
        ((i : ℕ) + 1)).1 =
      LoopParams.clipUnit
        ((finiteControlledOrbitFrom p rho x₀ u i).1 +
          p.α * (civicWeightedGradient p rho
              (finiteControlledOrbitFrom p rho x₀ u i).1
              (finiteControlledOrbitFrom p rho x₀ u i).2 + u i) +
          p.α * q) := by
  rw [finiteControlledOrbitFrom,
    finiteControlledOrbitFrom_bump_eq_of_le p rho x₀ u i q le_rfl]
  simp only [controlledCivicWeightedStep, extendFiniteControl, i.isLt,
    dite_true, bumpFiniteControl_self]
  congr 1
  ring

/-- The bump changes the quadratic action by exactly the expected single
coordinate cross term. -/
theorem gaussianVectorAction_bumpFiniteControl
    {T : ℕ} (u : Fin T → ℝ) (i : Fin T) (q : ℝ) :
    gaussianVectorAction (bumpFiniteControl u i q) =
      gaussianVectorAction u + u i * q + q ^ 2 / 2 := by
  classical
  have hsquare : ∀ j : Fin T,
      (bumpFiniteControl u i q j) ^ 2 =
        (u j) ^ 2 + if j = i then (2 * u i * q + q ^ 2) else 0 := by
    intro j
    by_cases hji : j = i
    · subst j
      simp only [bumpFiniteControl_self, ↓reduceIte]
      ring
    · simp only [bumpFiniteControl_of_ne u q hji, hji, ↓reduceIte,
        add_zero]
  simp only [gaussianVectorAction]
  rw [Finset.sum_congr rfl fun j _hj ↦ hsquare j,
    Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

/-- If an unclipped input already projects to within `d` below an interior
target, adding `d` to that input makes the projection reach the target. -/
theorem target_le_clipUnit_add_of_close
    {raw target d : ℝ} (htarget : target ∈ Ioo (0 : ℝ) 1)
    (hd : 0 < d) (hdtarget : d < target)
    (hclose : target - d < LoopParams.clipUnit raw) :
    target ≤ LoopParams.clipUnit (raw + d) := by
  by_cases halready : target ≤ LoopParams.clipUnit raw
  · calc
      target ≤ LoopParams.clipUnit raw := halready
      _ ≤ LoopParams.clipUnit (raw + d) :=
        LoopParams.monotone_clipUnit (le_add_of_nonneg_right hd.le)
  · have houtlt : LoopParams.clipUnit raw < target := lt_of_not_ge halready
    have houtpos : 0 < LoopParams.clipUnit raw := by linarith
    have houtInterior : LoopParams.clipUnit raw ∈ Ioo (0 : ℝ) 1 :=
      ⟨houtpos, houtlt.trans htarget.2⟩
    have hraw : raw = LoopParams.clipUnit raw :=
      (clipUnit_eq_interior_iff houtInterior).1 rfl
    rw [hraw]
    have htargetMem : target ∈ Icc (0 : ℝ) 1 :=
      ⟨htarget.1.le, htarget.2.le⟩
    rw [← clipUnit_eq_self htargetMem]
    exact LoopParams.monotone_clipUnit (by linarith)

/-- Adding a positive amount to an input whose projection has already reached
an interior target moves the projected output strictly beyond that target. -/
theorem target_lt_clipUnit_add_of_le
    {raw target d : ℝ} (htarget : target ∈ Ioo (0 : ℝ) 1)
    (hd : 0 < d) (hreached : target ≤ LoopParams.clipUnit raw) :
    target < LoopParams.clipUnit (raw + d) := by
  have houtPos : 0 < LoopParams.clipUnit raw :=
    htarget.1.trans_le hreached
  have hrawLower : LoopParams.clipUnit raw ≤ raw := by
    simpa only [clipUnit_eq_clipTo] using
      (clipTo_le_input (lo := (0 : ℝ)) (hi := 1) houtPos)
  simp only [clipUnit_eq_clipTo]
  exact lt_clipTo (lo := (0 : ℝ)) (hi := 1)
    (by linarith) htarget.2

/-! ## Fixed-horizon transport to the calibrated corner -/

/-- At every fixed horizon and finite action ceiling, crossing controls from
sufficiently nearby starts cost at least `V^x - delta`.  The proof transports
the same control vector to the calibrated corner and adds a vanishing
one-coordinate correction at the original crossing step.  This is the
finite-horizon transport lemma isolated in the sharp-rate upgrade. -/
theorem exists_home_radius_crossing_action_lower_bound
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (T : ℕ) {A delta : ℝ} (hA0 : 0 ≤ A) (hdelta : 0 < delta) :
    ∃ r : ℝ, 0 < r ∧
      ∀ x₀ : LoopState, dist x₀ (calibratedPoint p) < r →
        ∀ u : Fin T → ℝ, gaussianVectorAction u ≤ A →
          weighted.βdagger ≤
              policyRunningMax
                (finiteControlledOrbitFrom p rho x₀ u) T →
            civicCrossingQuasipotential weighted - delta ≤
              gaussianVectorAction u := by
  let R : ℝ := 2 * A + 1
  have hRpos : 0 < R := by dsimp only [R]; linarith
  let q : ℝ := min 1
    (min (delta / (4 * (R + 1)))
      (weighted.βdagger / (2 * p.α)))
  have hdeltaFraction : 0 < delta / (4 * (R + 1)) := by
    positivity
  have hsaddleFraction :
      0 < weighted.βdagger / (2 * p.α) := by
    exact div_pos weighted.βdagger_mem.1
      (mul_pos (by norm_num) model.α_pos)
  have hqpos : 0 < q := by
    dsimp only [q]
    rw [lt_min_iff, lt_min_iff]
    exact ⟨one_pos, hdeltaFraction, hsaddleFraction⟩
  have hqleOne : q ≤ 1 := min_le_left _ _
  have hqleDelta : q ≤ delta / (4 * (R + 1)) :=
    (min_le_right (1 : ℝ) _).trans (min_le_left _ _)
  have hqleSaddle : q ≤ weighted.βdagger / (2 * p.α) :=
    (min_le_right (1 : ℝ) _).trans (min_le_right _ _)
  have hqnonneg : 0 ≤ q := hqpos.le
  have hAlphaQle : p.α * q ≤ weighted.βdagger / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hqleSaddle model.α_pos.le
    calc
      p.α * q ≤ p.α * (weighted.βdagger / (2 * p.α)) := hmul
      _ = weighted.βdagger / 2 := by
        field_simp [model.α_pos.ne']
  have hcorrectionAction : R * q + q ^ 2 / 2 < delta := by
    have hqsq : q ^ 2 ≤ q := by nlinarith
    have hmul : (R + 1) * q ≤ delta / 4 := by
      calc
        (R + 1) * q ≤
            (R + 1) * (delta / (4 * (R + 1))) :=
          mul_le_mul_of_nonneg_left hqleDelta (by linarith)
        _ = delta / 4 := by
          field_simp [show R + 1 ≠ 0 by linarith]
    nlinarith
  let epsilon : ℝ := min (weighted.βdagger / 2) (p.α * q / 2)
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    rw [lt_min_iff]
    exact ⟨div_pos weighted.βdagger_mem.1 (by norm_num),
      div_pos (mul_pos model.α_pos hqpos) (by norm_num)⟩
  obtain ⟨r, hr, huniform⟩ :=
    exists_uniform_start_radius_on_controlBall
      p rho (calibratedPoint p) R hepsilon
  refine ⟨r, hr, fun x₀ hx₀ u haction hcross ↦ ?_⟩
  have hcontrolRadius : dist u 0 ≤ R := by
    simpa only [R] using
      dist_control_zero_le_two_mul_actionBound_add_one haction hA0
  have hhistory := huniform x₀ hx₀ u hcontrolRadius
  obtain ⟨j, hjT, hjcross⟩ :=
    (le_runningMax_iff (a := fun n ↦
      (finiteControlledOrbitFrom p rho x₀ u n).1)).1 hcross
  let jf : Fin (T + 1) := ⟨j, by omega⟩
  have hstateDist := hhistory jf
  rw [Prod.dist_eq, max_lt_iff] at hstateDist
  have hpolicyDist := hstateDist.1
  rw [Real.dist_eq] at hpolicyDist
  have hepsilonLe : epsilon ≤ p.α * q / 2 :=
    min_le_right _ _
  have htransportClose :
      weighted.βdagger - p.α * q <
        (finiteControlledOrbitFrom p rho (calibratedPoint p) u j).1 := by
    have hlower := (abs_lt.mp hpolicyDist).1
    nlinarith
  cases j with
  | zero =>
      simp only [finiteControlledOrbitFrom, calibratedPoint] at htransportClose
      nlinarith [weighted.βdagger_mem.1]
  | succ j =>
      have hjltT : j < T := by omega
      let i : Fin T := ⟨j, hjltT⟩
      let raw : ℝ :=
        (finiteControlledOrbitFrom p rho (calibratedPoint p) u j).1 +
          p.α * (civicWeightedGradient p rho
              (finiteControlledOrbitFrom p rho (calibratedPoint p) u j).1
              (finiteControlledOrbitFrom p rho (calibratedPoint p) u j).2 +
            u i)
      have hunbumpedPolicy :
          (finiteControlledOrbitFrom p rho (calibratedPoint p) u (j + 1)).1 =
            LoopParams.clipUnit raw := by
        simp only [finiteControlledOrbitFrom, controlledCivicWeightedStep,
          extendFiniteControl, hjltT, dite_true, raw, i]
      have hcloseRaw : weighted.βdagger - p.α * q <
          LoopParams.clipUnit raw := by
        rw [← hunbumpedPolicy]
        simpa only [Nat.succ_eq_add_one] using htransportClose
      have hAlphaQpos : 0 < p.α * q :=
        mul_pos model.α_pos hqpos
      have hAlphaQlt : p.α * q < weighted.βdagger := by
        nlinarith [weighted.βdagger_mem.1]
      have hbumpedPolicy : weighted.βdagger ≤
          (finiteControlledOrbitFrom p rho (calibratedPoint p)
            (bumpFiniteControl u i q) (j + 1)).1 := by
        rw [show j + 1 = (i : ℕ) + 1 by rfl,
          finiteControlledOrbitFrom_bump_succ_policy]
        change weighted.βdagger ≤ LoopParams.clipUnit (raw + p.α * q)
        exact target_le_clipUnit_add_of_close weighted.βdagger_mem
          hAlphaQpos hAlphaQlt hcloseRaw
      have hbumpedCross : weighted.βdagger ≤
          policyRunningMax
            (finiteControlledOrbitFrom p rho (calibratedPoint p)
              (bumpFiniteControl u i q)) T := by
        exact hbumpedPolicy.trans
          ((policy_le_runningMax
              (finiteControlledOrbitFrom p rho (calibratedPoint p)
                (bumpFiniteControl u i q)) (j + 1)).trans
            ((monotone_runningMax fun n ↦
              (finiteControlledOrbitFrom p rho (calibratedPoint p)
                (bumpFiniteControl u i q) n).1) hjT))
      have horbit : finiteControlledOrbitFrom p rho (calibratedPoint p)
          (bumpFiniteControl u i q) =
          finiteControlledOrbit p rho (bumpFiniteControl u i q) := by
        funext n
        exact finiteControlledOrbitFrom_calibratedPoint
          p rho (bumpFiniteControl u i q) n
      rw [horbit] at hbumpedCross
      have hVbumped :=
        civicCrossingQuasipotential_le_gaussianVectorAction
          weighted hbumpedCross
      have huiAbs : |u i| ≤ R := by
        have hui := (dist_pi_le_iff hRpos.le).1 hcontrolRadius i
        simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using hui
      have huiMul : u i * q ≤ R * q := by
        exact (mul_le_mul_of_nonneg_right
          ((le_abs_self (u i)).trans huiAbs) hqnonneg)
      have hbumpedAction :
          gaussianVectorAction (bumpFiniteControl u i q) <
            gaussianVectorAction u + delta := by
        rw [gaussianVectorAction_bumpFiniteControl]
        linarith
      linarith

/-- Once the action ceiling is chosen above `V^x`, the transport lower bound
extends to every control: controls above the ceiling are already expensive
enough. -/
theorem exists_home_radius_crossing_action_lower_bound_unrestricted
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (T : ℕ) {A delta : ℝ} (hA0 : 0 ≤ A)
    (hVleA : civicCrossingQuasipotential weighted ≤ A)
    (hdelta : 0 < delta) :
    ∃ r : ℝ, 0 < r ∧
      ∀ x₀ : LoopState, dist x₀ (calibratedPoint p) < r →
        ∀ u : Fin T → ℝ,
          weighted.βdagger ≤
              policyRunningMax
                (finiteControlledOrbitFrom p rho x₀ u) T →
            civicCrossingQuasipotential weighted - delta ≤
              gaussianVectorAction u := by
  obtain ⟨r, hr, htransport⟩ :=
    exists_home_radius_crossing_action_lower_bound
      model weighted T hA0 hdelta
  refine ⟨r, hr, fun x₀ hx₀ u hcross ↦ ?_⟩
  by_cases haction : gaussianVectorAction u ≤ A
  · exact htransport x₀ hx₀ u haction hcross
  · have hAbove : A < gaussianVectorAction u := lt_of_not_ge haction
    linarith

/-- Reaching a sufficiently thin strip below the saddle already costs
`V^x - delta`, uniformly over a small home ball.  A one-coordinate bump at
the first strip-reaching step turns the path into an exact crossing; its
action cost can be made smaller than `delta/2`.  This is the deterministic
rate source for the first-entry decomposition in the persistence proof. -/
theorem exists_home_radius_nearCrossing_action_lower_bound_unrestricted
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (T : ℕ) {A delta : ℝ} (hA0 : 0 ≤ A)
    (hVleA : civicCrossingQuasipotential weighted ≤ A)
    (hdelta : 0 < delta) :
    ∃ margin : ℝ, 0 < margin ∧ margin < weighted.βdagger ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ x₀ : LoopState, dist x₀ (calibratedPoint p) < r →
          ∀ u : Fin T → ℝ,
            weighted.βdagger - margin ≤
                policyRunningMax
                  (finiteControlledOrbitFrom p rho x₀ u) T →
              civicCrossingQuasipotential weighted - delta ≤
                gaussianVectorAction u := by
  let R : ℝ := 2 * A + 1
  have hRpos : 0 < R := by dsimp only [R]; linarith
  let q : ℝ := min 1
    (min (delta / (8 * (R + 1)))
      (weighted.βdagger / (2 * p.α)))
  have hdeltaFraction : 0 < delta / (8 * (R + 1)) := by
    positivity
  have hsaddleFraction :
      0 < weighted.βdagger / (2 * p.α) := by
    exact div_pos weighted.βdagger_mem.1
      (mul_pos (by norm_num) model.α_pos)
  have hqpos : 0 < q := by
    dsimp only [q]
    rw [lt_min_iff, lt_min_iff]
    exact ⟨one_pos, hdeltaFraction, hsaddleFraction⟩
  have hqleOne : q ≤ 1 := min_le_left _ _
  have hqleDelta : q ≤ delta / (8 * (R + 1)) :=
    (min_le_right (1 : ℝ) _).trans (min_le_left _ _)
  have hqleSaddle : q ≤ weighted.βdagger / (2 * p.α) :=
    (min_le_right (1 : ℝ) _).trans (min_le_right _ _)
  have hqnonneg : 0 ≤ q := hqpos.le
  let d : ℝ := p.α * q
  have hdpos : 0 < d := mul_pos model.α_pos hqpos
  have hdle : d ≤ weighted.βdagger / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hqleSaddle model.α_pos.le
    dsimp only [d]
    calc
      p.α * q ≤ p.α * (weighted.βdagger / (2 * p.α)) := hmul
      _ = weighted.βdagger / 2 := by
        field_simp [model.α_pos.ne']
  have hdlt : d < weighted.βdagger := by
    linarith [weighted.βdagger_mem.1]
  let margin : ℝ := d / 2
  have hmargin : 0 < margin := div_pos hdpos (by norm_num)
  have hmarginlt : margin < weighted.βdagger := by
    dsimp only [margin]
    nlinarith [weighted.βdagger_mem.1, hdle]
  have hcorrectionAction : R * q + q ^ 2 / 2 < delta / 2 := by
    have hqsq : q ^ 2 ≤ q := by nlinarith
    have hmul : (R + 1) * q ≤ delta / 8 := by
      calc
        (R + 1) * q ≤
            (R + 1) * (delta / (8 * (R + 1))) :=
          mul_le_mul_of_nonneg_left hqleDelta (by linarith)
        _ = delta / 8 := by
          field_simp [show R + 1 ≠ 0 by linarith]
    nlinarith
  obtain ⟨rCross, hrCross, hcrossRate⟩ :=
    exists_home_radius_crossing_action_lower_bound_unrestricted
      model weighted T hA0 hVleA (half_pos hdelta)
  let r : ℝ := min rCross ((weighted.βdagger - margin) / 2)
  have hsaddleMinusMargin : 0 < weighted.βdagger - margin :=
    sub_pos.mpr hmarginlt
  have hr : 0 < r := by
    dsimp only [r]
    rw [lt_min_iff]
    exact ⟨hrCross, div_pos hsaddleMinusMargin (by norm_num)⟩
  refine ⟨margin, hmargin, hmarginlt, r, hr,
    fun x₀ hx₀ u hnear ↦ ?_⟩
  have hxCross : dist x₀ (calibratedPoint p) < rCross :=
    hx₀.trans_le (min_le_left _ _)
  by_cases haction : gaussianVectorAction u ≤ A
  · have hcontrolRadius : dist u 0 ≤ R := by
      simpa only [R] using
        dist_control_zero_le_two_mul_actionBound_add_one haction hA0
    obtain ⟨j, hjT, hjnear⟩ :=
      (le_runningMax_iff (a := fun n ↦
        (finiteControlledOrbitFrom p rho x₀ u n).1)).1 hnear
    cases j with
    | zero =>
        have hxHalf : dist x₀ (calibratedPoint p) <
            (weighted.βdagger - margin) / 2 :=
          hx₀.trans_le (min_le_right _ _)
        rw [Prod.dist_eq, max_lt_iff] at hxHalf
        have hxPolicy := hxHalf.1
        rw [Real.dist_eq] at hxPolicy
        simp only [calibratedPoint, sub_zero] at hxPolicy
        simp only [finiteControlledOrbitFrom] at hjnear
        linarith [le_abs_self x₀.1]
    | succ j =>
        have hjltT : j < T := by omega
        let i : Fin T := ⟨j, hjltT⟩
        let raw : ℝ :=
          (finiteControlledOrbitFrom p rho x₀ u j).1 +
            p.α * (civicWeightedGradient p rho
                (finiteControlledOrbitFrom p rho x₀ u j).1
                (finiteControlledOrbitFrom p rho x₀ u j).2 + u i)
        have hunbumpedPolicy :
            (finiteControlledOrbitFrom p rho x₀ u (j + 1)).1 =
              LoopParams.clipUnit raw := by
          simp only [finiteControlledOrbitFrom, controlledCivicWeightedStep,
            extendFiniteControl, hjltT, dite_true, raw, i]
        have hcloseRaw : weighted.βdagger - d <
            LoopParams.clipUnit raw := by
          rw [← hunbumpedPolicy]
          dsimp only [margin] at hjnear
          nlinarith
        have hbumpedPolicy : weighted.βdagger ≤
            (finiteControlledOrbitFrom p rho x₀
              (bumpFiniteControl u i q) (j + 1)).1 := by
          rw [show j + 1 = (i : ℕ) + 1 by rfl,
            finiteControlledOrbitFrom_bump_succ_policy]
          change weighted.βdagger ≤
            LoopParams.clipUnit (raw + p.α * q)
          simpa only [d] using
            target_le_clipUnit_add_of_close weighted.βdagger_mem
              hdpos hdlt hcloseRaw
        have hbumpedCross : weighted.βdagger ≤
            policyRunningMax
              (finiteControlledOrbitFrom p rho x₀
                (bumpFiniteControl u i q)) T := by
          exact hbumpedPolicy.trans
            ((policy_le_runningMax
                (finiteControlledOrbitFrom p rho x₀
                  (bumpFiniteControl u i q)) (j + 1)).trans
              ((monotone_runningMax fun n ↦
                (finiteControlledOrbitFrom p rho x₀
                  (bumpFiniteControl u i q) n).1) hjT))
        have hVbumped := hcrossRate x₀ hxCross
          (bumpFiniteControl u i q) hbumpedCross
        have huiAbs : |u i| ≤ R := by
          have hui := (dist_pi_le_iff hRpos.le).1 hcontrolRadius i
          simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using hui
        have huiMul : u i * q ≤ R * q :=
          mul_le_mul_of_nonneg_right
            ((le_abs_self (u i)).trans huiAbs) hqnonneg
        have hbumpedAction :
            gaussianVectorAction (bumpFiniteControl u i q) <
              gaussianVectorAction u + delta / 2 := by
          rw [gaussianVectorAction_bumpFiniteControl]
          linarith
        linarith
  · have hAbove : A < gaussianVectorAction u := lt_of_not_ge haction
    linarith

/-! ## Robust `V^x` approximants -/

/-- Every positive tolerance admits a calibrated crossing control with a
strict policy margin and action still within that tolerance of `V^x`.  A
single positive bump is placed at an actual crossing step. -/
theorem exists_margin_crossing_control_lt_quasipotential_add
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho delta : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (hdelta : 0 < delta) :
    ∃ (T : ℕ) (u : Fin T → ℝ) (margin : ℝ),
      0 < margin ∧
      weighted.βdagger + margin ≤
          policyRunningMax (finiteControlledOrbit p rho u) T ∧
        gaussianVectorAction u <
          civicCrossingQuasipotential weighted + delta := by
  obtain ⟨T, u, hcross, haction⟩ :=
    exists_crossing_control_lt_quasipotential_add
      model weighted (half_pos hdelta)
  have horbit : finiteControlledOrbitFrom p rho (calibratedPoint p) u =
      finiteControlledOrbit p rho u := by
    funext n
    exact finiteControlledOrbitFrom_calibratedPoint p rho u n
  have hcrossFrom : weighted.βdagger ≤
      policyRunningMax
        (finiteControlledOrbitFrom p rho (calibratedPoint p) u) T := by
    rwa [horbit]
  obtain ⟨k, hkT, hkcross⟩ :=
    (le_runningMax_iff (a := fun n ↦
      (finiteControlledOrbitFrom p rho (calibratedPoint p) u n).1)).1
      hcrossFrom
  cases k with
  | zero =>
      simp only [finiteControlledOrbitFrom, calibratedPoint] at hkcross
      exact ((not_le_of_gt weighted.βdagger_mem.1) hkcross).elim
  | succ k =>
      have hkltT : k < T := by omega
      let i : Fin T := ⟨k, hkltT⟩
      let q : ℝ := min 1
        (delta / (4 * (|u i| + 1)))
      have hdenPos : 0 < 4 * (|u i| + 1) := by positivity
      have hqpos : 0 < q := by
        dsimp only [q]
        rw [lt_min_iff]
        exact ⟨one_pos, div_pos hdelta hdenPos⟩
      have hqleOne : q ≤ 1 := min_le_left _ _
      have hqleDelta : q ≤ delta / (4 * (|u i| + 1)) :=
        min_le_right _ _
      let raw : ℝ :=
        (finiteControlledOrbitFrom p rho (calibratedPoint p) u k).1 +
          p.α * (civicWeightedGradient p rho
              (finiteControlledOrbitFrom p rho (calibratedPoint p) u k).1
              (finiteControlledOrbitFrom p rho (calibratedPoint p) u k).2 +
            u i)
      have hunbumpedPolicy :
          (finiteControlledOrbitFrom p rho (calibratedPoint p) u (k + 1)).1 =
            LoopParams.clipUnit raw := by
        simp only [finiteControlledOrbitFrom, controlledCivicWeightedStep,
          extendFiniteControl, hkltT, dite_true, raw, i]
      have hreachedRaw : weighted.βdagger ≤ LoopParams.clipUnit raw := by
        rw [← hunbumpedPolicy]
        simpa only [Nat.succ_eq_add_one] using hkcross
      have hbumpedPolicyStrict : weighted.βdagger <
          (finiteControlledOrbitFrom p rho (calibratedPoint p)
            (bumpFiniteControl u i q) (k + 1)).1 := by
        rw [show k + 1 = (i : ℕ) + 1 by rfl,
          finiteControlledOrbitFrom_bump_succ_policy]
        change weighted.βdagger <
          LoopParams.clipUnit (raw + p.α * q)
        exact target_lt_clipUnit_add_of_le weighted.βdagger_mem
          (mul_pos model.α_pos hqpos) hreachedRaw
      let margin : ℝ :=
        ((finiteControlledOrbitFrom p rho (calibratedPoint p)
            (bumpFiniteControl u i q) (k + 1)).1 -
          weighted.βdagger) / 2
      have hmargin : 0 < margin := by
        dsimp only [margin]
        linarith
      have hbumpedAt : weighted.βdagger + margin ≤
          (finiteControlledOrbitFrom p rho (calibratedPoint p)
            (bumpFiniteControl u i q) (k + 1)).1 := by
        dsimp only [margin]
        linarith
      have hbumpedCrossFrom : weighted.βdagger + margin ≤
          policyRunningMax
            (finiteControlledOrbitFrom p rho (calibratedPoint p)
              (bumpFiniteControl u i q)) T := by
        exact hbumpedAt.trans
          ((policy_le_runningMax
              (finiteControlledOrbitFrom p rho (calibratedPoint p)
                (bumpFiniteControl u i q)) (k + 1)).trans
            ((monotone_runningMax fun n ↦
              (finiteControlledOrbitFrom p rho (calibratedPoint p)
                (bumpFiniteControl u i q) n).1) hkT))
      have hbumpedOrbit :
          finiteControlledOrbitFrom p rho (calibratedPoint p)
              (bumpFiniteControl u i q) =
            finiteControlledOrbit p rho (bumpFiniteControl u i q) := by
        funext n
        exact finiteControlledOrbitFrom_calibratedPoint
          p rho (bumpFiniteControl u i q) n
      have hbumpedCross : weighted.βdagger + margin ≤
          policyRunningMax
            (finiteControlledOrbit p rho (bumpFiniteControl u i q)) T := by
        rwa [← hbumpedOrbit]
      have hqnonneg : 0 ≤ q := hqpos.le
      have hqsq : q ^ 2 ≤ q := by nlinarith
      have hextra : u i * q + q ^ 2 / 2 < delta / 2 := by
        have hui : u i * q ≤ |u i| * q :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hqnonneg
        have hmul : (|u i| + 1) * q ≤ delta / 4 := by
          calc
            (|u i| + 1) * q ≤
                (|u i| + 1) *
                  (delta / (4 * (|u i| + 1))) :=
              mul_le_mul_of_nonneg_left hqleDelta (by positivity)
            _ = delta / 4 := by
              field_simp [show |u i| + 1 ≠ 0 by positivity]
        nlinarith
      have hbumpedAction :
          gaussianVectorAction (bumpFiniteControl u i q) <
            civicCrossingQuasipotential weighted + delta := by
        rw [gaussianVectorAction_bumpFiniteControl]
        linarith
      exact ⟨T, bumpFiniteControl u i q, margin, hmargin,
        hbumpedCross, hbumpedAction⟩

/-! ## The abstract no-cheap-crossing interface -/

/-- A deterministic finite-horizon lower bound for saddle crossing, uniform
over a specified set of initial states.  The usable rate is `rate - error`;
the error slot is where the sharp theorem records finite-horizon transport
from a home neighborhood back to the calibrated corner. -/
structure NoCheapCrossingRate {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) where
  starts : Set LoopState
  horizon : ℕ
  rate : ℝ
  error : ℝ
  error_nonneg : 0 ≤ error
  action_lower : ∀ x₀ ∈ starts, ∀ u : Fin horizon → ℝ,
    weighted.βdagger ≤
        policyRunningMax (finiteControlledOrbitFrom p rho x₀ u) horizon →
      rate - error ≤ gaussianVectorAction u

/-- Deterministic finite-horizon lower bound for reaching a specified strip
below the saddle.  This prices the first near-saddle entrance in the
last-exit decomposition. -/
structure NoCheapNearCrossingRate {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) where
  margin : ℝ
  margin_pos : 0 < margin
  starts : Set LoopState
  horizon : ℕ
  rate : ℝ
  error : ℝ
  error_nonneg : 0 ≤ error
  action_lower : ∀ x₀ ∈ starts, ∀ u : Fin horizon → ℝ,
    weighted.βdagger - margin ≤
        policyRunningMax (finiteControlledOrbitFrom p rho x₀ u) horizon →
      rate - error ≤ gaussianVectorAction u

/-- The realized noisy crossing event lies in a radial Gaussian action tail
at the certificate's usable rate. -/
theorem gaussianCrossingEventFrom_subset_actionTail
    {p : LoopParams} {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (certificate : NoCheapCrossingRate weighted)
    {x₀ : LoopState} (hx₀ : x₀ ∈ certificate.starts)
    {sigma : ℝ} (hsigma : sigma ≠ 0) :
    gaussianCrossingEventFrom weighted x₀ certificate.horizon sigma ⊆
      {xi : Fin certificate.horizon → ℝ |
        (certificate.rate - certificate.error) / sigma ^ 2 ≤
          gaussianVectorAction xi} := by
  intro xi hcross
  have hpay := certificate.action_lower x₀ hx₀
    (scaledGaussianControl sigma xi) hcross
  rw [gaussianVectorAction_scaledGaussianControl] at hpay
  exact (div_le_iff₀ (sq_pos_of_ne_zero hsigma)).2
    (by simpa only [mul_comm] using hpay)

/-- A certified near-saddle reaching event lies in the corresponding radial
Gaussian action tail. -/
theorem gaussianNearCrossingEventFrom_subset_actionTail
    {p : LoopParams} {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (certificate : NoCheapNearCrossingRate weighted)
    {x₀ : LoopState} (hx₀ : x₀ ∈ certificate.starts)
    {sigma : ℝ} (hsigma : sigma ≠ 0) :
    gaussianNearCrossingEventFrom weighted certificate.margin x₀
        certificate.horizon sigma ⊆
      {xi : Fin certificate.horizon → ℝ |
        (certificate.rate - certificate.error) / sigma ^ 2 ≤
          gaussianVectorAction xi} := by
  intro xi hreach
  have hpay := certificate.action_lower x₀ hx₀
    (scaledGaussianControl sigma xi) hreach
  rw [gaussianVectorAction_scaledGaussianControl] at hpay
  exact (div_le_iff₀ (sq_pos_of_ne_zero hsigma)).2
    (by simpa only [mul_comm] using hpay)

/-- Parameterized finite-dimensional Chernoff estimate.  This theorem is the
bounded-length probability engine shared by the bracket and sharp-rate
persistence arguments. -/
theorem gaussianCrossingProbabilityFrom_le_chernoff
    {p : LoopParams} {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (certificate : NoCheapCrossingRate weighted)
    {x₀ : LoopState} (hx₀ : x₀ ∈ certificate.starts)
    {sigma t : ℝ} (hsigma : sigma ≠ 0) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    gaussianCrossingProbabilityFrom weighted x₀ certificate.horizon sigma ≤
      ENNReal.ofReal
        (Real.exp (-t *
            ((certificate.rate - certificate.error) / sigma ^ 2)) *
          mgf gaussianVectorAction
            (standardGaussianVector certificate.horizon) t) := by
  letI : IsProbabilityMeasure
      (standardGaussianVector certificate.horizon) := by
    unfold standardGaussianVector
    infer_instance
  let B : ℝ := certificate.rate - certificate.error
  have hsubset :
      gaussianCrossingEventFrom weighted x₀ certificate.horizon sigma ⊆
        {xi : Fin certificate.horizon → ℝ |
          B / sigma ^ 2 ≤ gaussianVectorAction xi} := by
    simpa only [B] using
      gaussianCrossingEventFrom_subset_actionTail certificate hx₀ hsigma
  have hmono :
      (standardGaussianVector certificate.horizon).real
          (gaussianCrossingEventFrom weighted x₀
            certificate.horizon sigma) ≤
        (standardGaussianVector certificate.horizon).real
          {xi : Fin certificate.horizon → ℝ |
            B / sigma ^ 2 ≤ gaussianVectorAction xi} :=
    measureReal_mono hsubset
  have hchernoff :
      (standardGaussianVector certificate.horizon).real
          {xi : Fin certificate.horizon → ℝ |
            B / sigma ^ 2 ≤ gaussianVectorAction xi} ≤
        Real.exp (-t * (B / sigma ^ 2)) *
          mgf gaussianVectorAction
            (standardGaussianVector certificate.horizon) t :=
    measure_ge_le_exp_mul_mgf (B / sigma ^ 2) ht0
      (integrable_exp_gaussianVectorAction ht1)
  have hnonneg : 0 ≤ Real.exp (-t * (B / sigma ^ 2)) *
      mgf gaussianVectorAction
        (standardGaussianVector certificate.horizon) t :=
    mul_nonneg (Real.exp_pos _).le mgf_nonneg
  have hprob_ne_top :
      gaussianCrossingProbabilityFrom weighted x₀
        certificate.horizon sigma ≠ ∞ := by
    exact measure_ne_top _ _
  apply (ENNReal.toReal_le_toReal hprob_ne_top (by simp)).1
  change (standardGaussianVector certificate.horizon).real
      (gaussianCrossingEventFrom weighted x₀
        certificate.horizon sigma) ≤ _
  rw [ENNReal.toReal_ofReal hnonneg]
  exact hmono.trans hchernoff

/-- Parameterized finite-dimensional Chernoff estimate for first entrance
into a certified near-saddle strip. -/
theorem gaussianNearCrossingProbabilityFrom_le_chernoff
    {p : LoopParams} {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (certificate : NoCheapNearCrossingRate weighted)
    {x₀ : LoopState} (hx₀ : x₀ ∈ certificate.starts)
    {sigma t : ℝ} (hsigma : sigma ≠ 0) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    gaussianNearCrossingProbabilityFrom weighted certificate.margin x₀
        certificate.horizon sigma ≤
      ENNReal.ofReal
        (Real.exp (-t *
            ((certificate.rate - certificate.error) / sigma ^ 2)) *
          mgf gaussianVectorAction
            (standardGaussianVector certificate.horizon) t) := by
  letI : IsProbabilityMeasure
      (standardGaussianVector certificate.horizon) := by
    unfold standardGaussianVector
    infer_instance
  let B : ℝ := certificate.rate - certificate.error
  have hsubset :
      gaussianNearCrossingEventFrom weighted certificate.margin x₀
          certificate.horizon sigma ⊆
        {xi : Fin certificate.horizon → ℝ |
          B / sigma ^ 2 ≤ gaussianVectorAction xi} := by
    simpa only [B] using
      gaussianNearCrossingEventFrom_subset_actionTail
        certificate hx₀ hsigma
  have hmono :
      (standardGaussianVector certificate.horizon).real
          (gaussianNearCrossingEventFrom weighted certificate.margin x₀
            certificate.horizon sigma) ≤
        (standardGaussianVector certificate.horizon).real
          {xi : Fin certificate.horizon → ℝ |
            B / sigma ^ 2 ≤ gaussianVectorAction xi} :=
    measureReal_mono hsubset
  have hchernoff :
      (standardGaussianVector certificate.horizon).real
          {xi : Fin certificate.horizon → ℝ |
            B / sigma ^ 2 ≤ gaussianVectorAction xi} ≤
        Real.exp (-t * (B / sigma ^ 2)) *
          mgf gaussianVectorAction
            (standardGaussianVector certificate.horizon) t :=
    measure_ge_le_exp_mul_mgf (B / sigma ^ 2) ht0
      (integrable_exp_gaussianVectorAction ht1)
  have hnonneg : 0 ≤ Real.exp (-t * (B / sigma ^ 2)) *
      mgf gaussianVectorAction
        (standardGaussianVector certificate.horizon) t :=
    mul_nonneg (Real.exp_pos _).le mgf_nonneg
  have hprob_ne_top :
      gaussianNearCrossingProbabilityFrom weighted certificate.margin x₀
        certificate.horizon sigma ≠ ∞ := by
    exact measure_ne_top _ _
  apply (ENNReal.toReal_le_toReal hprob_ne_top (by simp)).1
  change (standardGaussianVector certificate.horizon).real
      (gaussianNearCrossingEventFrom weighted certificate.margin x₀
        certificate.horizon sigma) ≤ _
  rw [ENNReal.toReal_ofReal hnonneg]
  exact hmono.trans hchernoff

/-- A single Chernoff constant works for every start covered by the
certificate. -/
theorem gaussianCrossingProbabilityFrom_le_uniform_chernoff
    {p : LoopParams} {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (certificate : NoCheapCrossingRate weighted)
    {sigma t : ℝ} (hsigma : sigma ≠ 0) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∀ x₀ ∈ certificate.starts,
      gaussianCrossingProbabilityFrom weighted x₀
          certificate.horizon sigma ≤
        ENNReal.ofReal
          (Real.exp (-t *
              ((certificate.rate - certificate.error) / sigma ^ 2)) *
            mgf gaussianVectorAction
              (standardGaussianVector certificate.horizon) t) := by
  intro x₀ hx₀
  exact gaussianCrossingProbabilityFrom_le_chernoff
    certificate hx₀ hsigma ht0 ht1

/-- Sharp fixed-horizon crossing bound, uniform on a sufficiently small metric
home ball.  The only model-specific input beyond continuity is any explicit
action ceiling above `V^x`; `V^x ≤ Vplus` supplies one in the final theorem. -/
theorem exists_home_radius_gaussianCrossingProbability_le_chernoff
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (T : ℕ) {A delta : ℝ} (hA0 : 0 ≤ A)
    (hVleA : civicCrossingQuasipotential weighted ≤ A)
    (hdelta : 0 < delta) :
    ∃ r : ℝ, 0 < r ∧
      ∀ x₀ : LoopState, dist x₀ (calibratedPoint p) < r →
        ∀ {sigma t : ℝ}, sigma ≠ 0 → 0 ≤ t → t < 1 →
          gaussianCrossingProbabilityFrom weighted x₀ T sigma ≤
            ENNReal.ofReal
              (Real.exp (-t *
                  ((civicCrossingQuasipotential weighted - delta) /
                    sigma ^ 2)) *
                mgf gaussianVectorAction (standardGaussianVector T) t) := by
  obtain ⟨r, hr, hrate⟩ :=
    exists_home_radius_crossing_action_lower_bound_unrestricted
      model weighted T hA0 hVleA hdelta
  let certificate : NoCheapCrossingRate weighted :=
    { starts := Metric.ball (calibratedPoint p) r
      horizon := T
      rate := civicCrossingQuasipotential weighted
      error := delta
      error_nonneg := hdelta.le
      action_lower := fun x₀ hx₀ u hcross ↦
        hrate x₀ hx₀ u hcross }
  refine ⟨r, hr, fun x₀ hx₀ sigma t hsigma ht0 ht1 ↦ ?_⟩
  simpa only [certificate] using
    gaussianCrossingProbabilityFrom_le_chernoff
      certificate hx₀ hsigma ht0 ht1

/-- Sharp fixed-horizon bound for first entrance into a sufficiently thin
near-saddle strip, uniform on a small home ball. -/
theorem exists_home_radius_gaussianNearCrossingProbability_le_chernoff
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (T : ℕ) {A delta : ℝ} (hA0 : 0 ≤ A)
    (hVleA : civicCrossingQuasipotential weighted ≤ A)
    (hdelta : 0 < delta) :
    ∃ margin : ℝ, 0 < margin ∧ margin < weighted.βdagger ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ x₀ : LoopState, dist x₀ (calibratedPoint p) < r →
          ∀ {sigma t : ℝ}, sigma ≠ 0 → 0 ≤ t → t < 1 →
            gaussianNearCrossingProbabilityFrom weighted margin x₀ T sigma ≤
              ENNReal.ofReal
                (Real.exp (-t *
                    ((civicCrossingQuasipotential weighted - delta) /
                      sigma ^ 2)) *
                  mgf gaussianVectorAction
                    (standardGaussianVector T) t) := by
  obtain ⟨margin, hmargin, hmarginlt, r, hr, hrate⟩ :=
    exists_home_radius_nearCrossing_action_lower_bound_unrestricted
      model weighted T hA0 hVleA hdelta
  let certificate : NoCheapNearCrossingRate weighted :=
    { margin := margin
      margin_pos := hmargin
      starts := Metric.ball (calibratedPoint p) r
      horizon := T
      rate := civicCrossingQuasipotential weighted
      error := delta
      error_nonneg := hdelta.le
      action_lower := fun x₀ hx₀ u hreach ↦
        hrate x₀ hx₀ u hreach }
  refine ⟨margin, hmargin, hmarginlt, r, hr,
    fun x₀ hx₀ sigma t hsigma ht0 ht1 ↦ ?_⟩
  simpa only [certificate] using
    gaussianNearCrossingProbabilityFrom_le_chernoff
      certificate hx₀ hsigma ht0 ht1

/-! ## The abstract robust-crossing-tube interface -/

/-- A finite control tube which crosses uniformly over a set of initial
states.  `actionBound` is an exposed upper bound on the center action, so the
same block skeleton can use either the printed two-phase strategy or a
`V^x`-approximating control. -/
structure RobustCrossingTube {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) where
  starts : Set LoopState
  horizon : ℕ
  center : Fin horizon → ℝ
  radius : ℝ
  radius_pos : 0 < radius
  actionBound : ℝ
  center_action_le : gaussianVectorAction center ≤ actionBound
  crosses : ∀ x₀ ∈ starts, ∀ u ∈ Metric.ball center radius,
    weighted.βdagger ≤
      policyRunningMax
        (finiteControlledOrbitFrom p rho x₀ u) horizon

/-- A Gaussian control box around the tube center is contained in the
arbitrary-start crossing event. -/
theorem gaussianControlBox_subset_crossingEventFrom
    {p : LoopParams} {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (tube : RobustCrossingTube weighted)
    {x₀ : LoopState} (hx₀ : x₀ ∈ tube.starts)
    {sigma : ℝ} (hsigma : 0 < sigma) (hsigmaRadius : sigma < tube.radius) :
    gaussianControlBox tube.center sigma ⊆
      gaussianCrossingEventFrom weighted x₀ tube.horizon sigma := by
  intro xi hxi
  exact tube.crosses x₀ hx₀ (scaledGaussianControl sigma xi)
    (scaledGaussianControl_mem_ball_of_mem_controlBox
      hsigma hsigmaRadius hxi)

/-- Explicit lower bound for every start covered by a robust crossing tube. -/
theorem robustCrossingTube_probability_lower
    {p : LoopParams} {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (tube : RobustCrossingTube weighted)
    {x₀ : LoopState} (hx₀ : x₀ ∈ tube.starts)
    {sigma : ℝ} (hsigma : 0 < sigma) (hsigmaRadius : sigma < tube.radius) :
    ENNReal.ofReal
        (∏ i, gaussianCoordinateLowerBound (tube.center i) sigma) ≤
      gaussianCrossingProbabilityFrom weighted x₀ tube.horizon sigma := by
  calc
    ENNReal.ofReal
        (∏ i, gaussianCoordinateLowerBound (tube.center i) sigma) ≤
        standardGaussianVector tube.horizon
          (gaussianControlBox tube.center sigma) :=
      gaussianControlBox_probability_lower tube.center hsigma
    _ ≤ standardGaussianVector tube.horizon
        (gaussianCrossingEventFrom weighted x₀ tube.horizon sigma) :=
      measure_mono (gaussianControlBox_subset_crossingEventFrom
        tube hx₀ hsigma hsigmaRadius)
    _ = gaussianCrossingProbabilityFrom weighted x₀ tube.horizon sigma := rfl

/-- The arbitrary-start finite-window logarithmic crossing rate. -/
def gaussianCrossingLogRateFrom {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (x₀ : LoopState)
    (T : ℕ) (sigma : ℝ) : EReal :=
  (sigma ^ 2 : ℝ) *
    ENNReal.log (gaussianCrossingProbabilityFrom weighted x₀ T sigma)

/-- Every robust tube has lower logarithmic rate at least minus its center
action, uniformly in the sense that the same center and radius apply to every
covered start. -/
theorem robustCrossingTube_logRate_liminf
    {p : LoopParams} {rho : ℝ}
    {weighted : WeightedThresholdAssumption p rho}
    (tube : RobustCrossingTube weighted)
    {x₀ : LoopState} (hx₀ : x₀ ∈ tube.starts) :
    ((-gaussianVectorAction tube.center : ℝ) : EReal) ≤
      liminf
        (gaussianCrossingLogRateFrom weighted x₀ tube.horizon)
        (nhdsWithin 0 (Ioi (0 : ℝ))) := by
  have hrNhds : ∀ᶠ sigma : ℝ in nhds 0, sigma < tube.radius :=
    Iio_mem_nhds tube.radius_pos
  have hrEventually : ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      sigma < tube.radius := hrNhds.filter_mono inf_le_left
  have hpointwise : ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      (sigma ^ 2 : ℝ) *
          ENNReal.log
            (standardGaussianVector tube.horizon
              (gaussianControlBox tube.center sigma)) ≤
        gaussianCrossingLogRateFrom weighted x₀ tube.horizon sigma := by
    filter_upwards [self_mem_nhdsWithin, hrEventually] with sigma hsigma hsigmaR
    have hsubsetMeasure :
        standardGaussianVector tube.horizon
            (gaussianControlBox tube.center sigma) ≤
          gaussianCrossingProbabilityFrom weighted x₀ tube.horizon sigma := by
      exact measure_mono (gaussianControlBox_subset_crossingEventFrom
        tube hx₀ hsigma hsigmaR)
    have hlog := ENNReal.logOrderIso.monotone hsubsetMeasure
    change ENNReal.log
        (standardGaussianVector tube.horizon
          (gaussianControlBox tube.center sigma)) ≤
      ENNReal.log
        (gaussianCrossingProbabilityFrom weighted x₀
          tube.horizon sigma) at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog
      (show (0 : EReal) ≤ (sigma ^ 2 : ℝ) by
        exact_mod_cast sq_nonneg sigma)
    simpa only [gaussianCrossingLogRateFrom] using hmul
  exact (gaussianControlBox_logRate_liminf tube.center).trans
    (liminf_le_liminf hpointwise)

/-! ## Producing robust tubes from uniform margins -/

/-- The running maximum depends jointly continuously on the start and finite
control vector. -/
theorem continuous_policyRunningMax_finiteControlledOrbitFrom_joint
    (p : LoopParams) (rho : ℝ) {T : ℕ} (n : ℕ) :
    Continuous (fun z : LoopState × (Fin T → ℝ) ↦
      policyRunningMax
        (finiteControlledOrbitFrom p rho z.1 z.2) n) := by
  induction n with
  | zero =>
      simpa only [policyRunningMax, runningMax_zero,
        finiteControlledOrbitFrom] using
        (continuous_fst.fst : Continuous
          (fun z : LoopState × (Fin T → ℝ) ↦ z.1.1))
  | succ n ih =>
      simpa only [policyRunningMax, runningMax_succ] using
        ih.max (continuous_finiteControlledOrbitFrom p rho (T := T)
          (n + 1)).fst

/-- On a compact set of starts, sufficiently small perturbations of a fixed
control vector keep the fixed-horizon running maximum uniformly close. -/
theorem exists_uniform_runningMax_control_radius
    (p : LoopParams) (rho : ℝ) {T : ℕ} {K : Set LoopState}
    (hK : IsCompact K) (center : Fin T → ℝ) (N : ℕ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ r : ℝ, 0 < r ∧
      ∀ x₀ ∈ K, ∀ u : Fin T → ℝ, dist u center < r →
        dist
          (policyRunningMax
            (finiteControlledOrbitFrom p rho x₀ center) N)
          (policyRunningMax
            (finiteControlledOrbitFrom p rho x₀ u) N) < epsilon := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : (Fin T → ℝ) → K → ℝ := fun u x₀ ↦
    policyRunningMax (finiteControlledOrbitFrom p rho x₀.1 u) N
  have hswap : Continuous (fun z : (Fin T → ℝ) × K ↦
      ((z.2.1, z.1) : LoopState × (Fin T → ℝ))) := by
    fun_prop
  have hcontinuous : Continuous (Function.uncurry F) := by
    exact (continuous_policyRunningMax_finiteControlledOrbitFrom_joint
      p rho N).comp hswap
  have huniform : TendstoUniformly F (F center) (nhds center) :=
    Continuous.tendstoUniformly F hcontinuous center
  have heventually : ∀ᶠ u in nhds center,
      ∀ x₀ : K, dist (F center x₀) (F u x₀) < epsilon :=
    (Metric.tendstoUniformly_iff.mp huniform) epsilon hepsilon
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp heventually
  exact ⟨r, hr, fun x₀ hx₀ u hu ↦ hball hu ⟨x₀, hx₀⟩⟩

/-- A strict running-maximum margin for one control, uniform over a compact
start set, yields a robust crossing control radius. -/
theorem exists_robust_crossing_control_radius_of_uniform_margin
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    {T : ℕ} {K : Set LoopState} (hK : IsCompact K)
    (center : Fin T → ℝ) {margin : ℝ} (hmargin : 0 < margin)
    (hcross : ∀ x₀ ∈ K,
      weighted.βdagger + margin ≤
        policyRunningMax
          (finiteControlledOrbitFrom p rho x₀ center) T) :
    ∃ r : ℝ, 0 < r ∧
      ∀ x₀ ∈ K, ∀ u ∈ Metric.ball center r,
        weighted.βdagger ≤
          policyRunningMax
            (finiteControlledOrbitFrom p rho x₀ u) T := by
  obtain ⟨r, hr, hclose⟩ :=
    exists_uniform_runningMax_control_radius
      p rho hK center T hmargin
  refine ⟨r, hr, fun x₀ hx₀ u hu ↦ ?_⟩
  have hdist := hclose x₀ hx₀ u hu
  rw [Real.dist_eq] at hdist
  have hlower := (abs_lt.mp hdist).2
  linarith [hcross x₀ hx₀]

/-- A strict margin at an arbitrary base state persists on a compact closed
start ball. -/
theorem exists_closedBall_uniform_margin_of_start
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    (base : LoopState) {T : ℕ} (center : Fin T → ℝ)
    {margin : ℝ} (hmargin : 0 < margin)
    (hcross : weighted.βdagger + margin ≤
      policyRunningMax
        (finiteControlledOrbitFrom p rho base center) T) :
    ∃ r : ℝ, 0 < r ∧
      ∀ x₀ ∈ Metric.closedBall base r,
        weighted.βdagger + margin / 2 ≤
          policyRunningMax
            (finiteControlledOrbitFrom p rho x₀ center) T := by
  let F : LoopState → ℝ := fun x₀ ↦
    policyRunningMax (finiteControlledOrbitFrom p rho x₀ center) T
  have hpair : Continuous (fun x₀ : LoopState ↦
      ((x₀, center) : LoopState × (Fin T → ℝ))) :=
    continuous_id.prodMk continuous_const
  have hcontinuous : Continuous F :=
    (continuous_policyRunningMax_finiteControlledOrbitFrom_joint
      p rho T).comp hpair
  have hcontinuousAt : ContinuousAt F base := hcontinuous.continuousAt
  rw [Metric.continuousAt_iff] at hcontinuousAt
  obtain ⟨r, hr, hclose⟩ :=
    hcontinuousAt (margin / 2) (half_pos hmargin)
  refine ⟨r / 2, half_pos hr, fun x₀ hx₀ ↦ ?_⟩
  have hxdist : dist x₀ base < r := by
    have hxle : dist x₀ base ≤ r / 2 := hx₀
    linarith
  have houtDist := hclose hxdist
  rw [Real.dist_eq] at houtDist
  have hlower := (abs_lt.mp houtDist).1
  dsimp only [F] at hlower
  linarith

/-- A strict calibrated-start margin persists on a compact closed start ball. -/
theorem exists_closedBall_uniform_margin_of_calibrated
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    {T : ℕ} (center : Fin T → ℝ)
    {margin : ℝ} (hmargin : 0 < margin)
    (hcross : weighted.βdagger + margin ≤
      policyRunningMax
        (finiteControlledOrbitFrom p rho (calibratedPoint p) center) T) :
    ∃ r : ℝ, 0 < r ∧
      ∀ x₀ ∈ Metric.closedBall (calibratedPoint p) r,
        weighted.βdagger + margin / 2 ≤
          policyRunningMax
            (finiteControlledOrbitFrom p rho x₀ center) T := by
  let F : LoopState → ℝ := fun x₀ ↦
    policyRunningMax (finiteControlledOrbitFrom p rho x₀ center) T
  have hpair : Continuous (fun x₀ : LoopState ↦
      ((x₀, center) : LoopState × (Fin T → ℝ))) :=
    continuous_id.prodMk continuous_const
  have hcontinuous : Continuous F :=
    (continuous_policyRunningMax_finiteControlledOrbitFrom_joint
      p rho T).comp hpair
  have hcontinuousAt : ContinuousAt F (calibratedPoint p) :=
    hcontinuous.continuousAt
  rw [Metric.continuousAt_iff] at hcontinuousAt
  obtain ⟨r, hr, hclose⟩ :=
    hcontinuousAt (margin / 2) (half_pos hmargin)
  refine ⟨r / 2, half_pos hr, fun x₀ hx₀ ↦ ?_⟩
  have hxdist : dist x₀ (calibratedPoint p) < r := by
    have hxle : dist x₀ (calibratedPoint p) ≤ r / 2 := hx₀
    linarith
  have houtDist := hclose hxdist
  rw [Real.dist_eq] at houtDist
  have hlower := (abs_lt.mp houtDist).1
  dsimp only [F] at hlower
  linarith

/-- A calibrated finite control with a strict margin generates a
`RobustCrossingTube` on some compact start ball. -/
theorem exists_robustCrossingTube_of_calibrated_margin
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    {T : ℕ} (center : Fin T → ℝ)
    {margin actionBound : ℝ} (hmargin : 0 < margin)
    (hcross : weighted.βdagger + margin ≤
      policyRunningMax
        (finiteControlledOrbitFrom p rho (calibratedPoint p) center) T)
    (haction : gaussianVectorAction center ≤ actionBound) :
    ∃ startRadius : ℝ, 0 < startRadius ∧
      ∃ tube : RobustCrossingTube weighted,
        tube.starts = Metric.closedBall (calibratedPoint p) startRadius ∧
        tube.actionBound = actionBound := by
  obtain ⟨startRadius, hstartRadius, hstartMargin⟩ :=
    exists_closedBall_uniform_margin_of_calibrated
      weighted center hmargin hcross
  let K : Set LoopState :=
    Metric.closedBall (calibratedPoint p) startRadius
  have hK : IsCompact K :=
    ProperSpace.isCompact_closedBall (calibratedPoint p) startRadius
  obtain ⟨controlRadius, hcontrolRadius, hrobust⟩ :=
    exists_robust_crossing_control_radius_of_uniform_margin
      weighted hK center (half_pos hmargin) hstartMargin
  let tube : RobustCrossingTube weighted :=
    { starts := K
      horizon := T
      center := center
      radius := controlRadius
      radius_pos := hcontrolRadius
      actionBound := actionBound
      center_action_le := haction
      crosses := hrobust }
  exact ⟨startRadius, hstartRadius, tube, rfl, rfl⟩

/-- An arbitrary-start finite control with a strict margin generates a robust
crossing tube on some compact ball about that start. -/
theorem exists_robustCrossingTube_of_start_margin
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    (base : LoopState) {T : ℕ} (center : Fin T → ℝ)
    {margin actionBound : ℝ} (hmargin : 0 < margin)
    (hcross : weighted.βdagger + margin ≤
      policyRunningMax
        (finiteControlledOrbitFrom p rho base center) T)
    (haction : gaussianVectorAction center ≤ actionBound) :
    ∃ startRadius : ℝ, 0 < startRadius ∧
      ∃ tube : RobustCrossingTube weighted,
        tube.starts = Metric.closedBall base startRadius ∧
        tube.actionBound = actionBound := by
  obtain ⟨startRadius, hstartRadius, hstartMargin⟩ :=
    exists_closedBall_uniform_margin_of_start
      weighted base center hmargin hcross
  let K : Set LoopState := Metric.closedBall base startRadius
  have hK : IsCompact K := ProperSpace.isCompact_closedBall base startRadius
  obtain ⟨controlRadius, hcontrolRadius, hrobust⟩ :=
    exists_robust_crossing_control_radius_of_uniform_margin
      weighted hK center (half_pos hmargin) hstartMargin
  let tube : RobustCrossingTube weighted :=
    { starts := K
      horizon := T
      center := center
      radius := controlRadius
      radius_pos := hcontrolRadius
      actionBound := actionBound
      center_action_le := haction
      crosses := hrobust }
  exact ⟨startRadius, hstartRadius, tube, rfl, rfl⟩

/-- Around the full weighted saddle state—not merely its policy coordinate—one
step gives a robust crossing tube with arbitrarily small center action.  This
is the near-saddle half of the corrected R1 split. -/
theorem exists_weightedSaddle_robustCrossingTube_small_action
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho delta : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (hdelta : 0 < delta) :
    ∃ startRadius : ℝ, 0 < startRadius ∧
      ∃ tube : RobustCrossingTube weighted,
        tube.starts = Metric.closedBall
          (weightedSaddlePoint weighted) startRadius ∧
        tube.actionBound = delta := by
  let e : ℝ := min delta 1
  have hepos : 0 < e := lt_min hdelta zero_lt_one
  have heDelta : e ≤ delta := min_le_left _ _
  have heOne : e ≤ 1 := min_le_right _ _
  let margin : ℝ := min ((1 - weighted.βdagger) / 2)
    (p.α * e / 2)
  have hmargin : 0 < margin := by
    dsimp only [margin]
    exact lt_min (half_pos (sub_pos.mpr weighted.βdagger_mem.2))
      (half_pos (mul_pos model.α_pos hepos))
  have hmarginRoom : weighted.βdagger + margin ≤ 1 := by
    have hhalf : (1 - weighted.βdagger) / 2 ≤
        1 - weighted.βdagger := by
      linarith [weighted.βdagger_mem.2]
    have := (min_le_left ((1 - weighted.βdagger) / 2)
      (p.α * e / 2)).trans hhalf
    dsimp only [margin]
    linarith
  have hmarginAlpha : margin ≤ p.α * e / 2 :=
    min_le_right _ _
  let center : Fin 1 → ℝ := fun _ ↦ margin / p.α
  have hcenterAction : gaussianVectorAction center ≤ delta := by
    have halpha : 0 < p.α := model.α_pos
    have hratio : margin / p.α ≤ e / 2 :=
      (div_le_iff₀ halpha).2 (by nlinarith [hmarginAlpha])
    have hratioNonneg : 0 ≤ margin / p.α :=
      div_nonneg hmargin.le halpha.le
    have heNonneg : 0 ≤ e := hepos.le
    have hsquare : (margin / p.α) ^ 2 ≤ (e / 2) ^ 2 :=
      (sq_le_sq₀ hratioNonneg (by positivity)).2 hratio
    have heSquare : e ^ 2 ≤ e := by nlinarith
    have hactionEq : gaussianVectorAction center =
        (1 / 2 : ℝ) * (margin / p.α) ^ 2 := by
      simp [gaussianVectorAction, center]
    rw [hactionEq]
    nlinarith [heDelta]
  have hstepPolicy :
      (finiteControlledOrbitFrom p rho (weightedSaddlePoint weighted)
        center 1).1 = weighted.βdagger + margin := by
    have hβ : weighted.βdagger ∈ Icc (0 : ℝ) 1 :=
      ⟨weighted.βdagger_mem.1.le, weighted.βdagger_mem.2.le⟩
    have hgradient : civicWeightedGradient p rho weighted.βdagger
        (p.stationaryStock weighted.βdagger) = 0 := by
      rw [civicWeightedGradient_stationary_eq_weightedStationaryGradient rho hβ]
      exact weighted.gradient_zero
    simp only [finiteControlledOrbitFrom, extendFiniteControl, zero_lt_one,
      dite_true, center, controlledCivicWeightedStep,
      weightedSaddlePoint, hgradient]
    have halphaCancel : p.α * (margin / p.α) = margin := by
      field_simp [model.α_pos.ne']
    rw [zero_add, halphaCancel]
    exact clipUnit_eq_self ⟨by linarith [weighted.βdagger_mem.1], hmarginRoom⟩
  have hcross : weighted.βdagger + margin ≤
      policyRunningMax
        (finiteControlledOrbitFrom p rho (weightedSaddlePoint weighted)
          center) 1 := by
    rw [policyRunningMax, runningMax_succ, runningMax_zero, hstepPolicy]
    exact le_max_right _ _
  exact exists_robustCrossingTube_of_start_margin
    weighted (weightedSaddlePoint weighted) center hmargin hcross hcenterAction

/-- The sharp upper-rate source: for every tolerance there is a robust
crossing tube from a compact calibrated neighborhood whose center action is at
most `V^x + delta`. -/
theorem exists_quasipotential_robustCrossingTube
    {p : LoopParams} (model : DriftModelAssumptions p)
    {rho delta : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (hdelta : 0 < delta) :
    ∃ startRadius : ℝ, 0 < startRadius ∧
      ∃ tube : RobustCrossingTube weighted,
        tube.starts = Metric.closedBall (calibratedPoint p) startRadius ∧
        tube.actionBound =
          civicCrossingQuasipotential weighted + delta := by
  obtain ⟨T, center, margin, hmargin, hcross, haction⟩ :=
    exists_margin_crossing_control_lt_quasipotential_add
      model weighted hdelta
  have hcrossFrom : weighted.βdagger + margin ≤
      policyRunningMax
        (finiteControlledOrbitFrom p rho (calibratedPoint p) center) T := by
    have horbit : finiteControlledOrbitFrom p rho (calibratedPoint p) center =
        finiteControlledOrbit p rho center := by
      funext n
      exact finiteControlledOrbitFrom_calibratedPoint p rho center n
    rwa [horbit]
  obtain ⟨startRadius, hstartRadius, tube,
      htubeStarts, htubeAction⟩ :=
    exists_robustCrossingTube_of_calibrated_margin
      weighted center hmargin hcrossFrom haction.le
  exact ⟨startRadius, hstartRadius, tube, htubeStarts, htubeAction⟩

/-! ## Concrete deterministic rate sources -/

/-- Last-exit starts dominated by the stationary characteristic at the home
policy floor. -/
def flooredLedgerStartSet (p : LoopParams) (floor : ℝ) : Set LoopState :=
  absorbingBox p ∩
    ({x | x.1 ≤ floor} ∩ {x | x.2 ≤ p.stationaryStock floor})

/-- The last-exit start set is compact. -/
theorem isCompact_flooredLedgerStartSet (p : LoopParams) (floor : ℝ) :
    IsCompact (flooredLedgerStartSet p floor) := by
  have hpolicy : IsClosed {x : LoopState | x.1 ≤ floor} :=
    isClosed_Iic.preimage continuous_fst
  have hstock : IsClosed
      {x : LoopState | x.2 ≤ p.stationaryStock floor} :=
    isClosed_Iic.preimage continuous_snd
  exact (isCompact_absorbingBox p).inter_right (hpolicy.inter hstock)

/-- The corrected localized barrier appearing in the last-exit ledger. -/
def flooredLedgerCrossingRate
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (L floor : ℝ) : ℝ :=
  (2 / (p.α * (1 + 2 * p.α * L))) *
    (∫ b in floor..weighted.βdagger,
      weightedBarrierIntegrand p rho b)

/-- The floored last-exit ledger supplies a no-cheap-crossing certificate at
every finite horizon. -/
def flooredLedgerNoCheapCrossingRate
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho L floor : ℝ}
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (hfloor : floor ∈ Icc (0 : ℝ) weighted.βdagger) (T : ℕ) :
    NoCheapCrossingRate weighted where
  starts := flooredLedgerStartSet p floor
  horizon := T
  rate := flooredLedgerCrossingRate weighted L floor
  error := 0
  error_nonneg := le_rfl
  action_lower x₀ hx₀ u hcross := by
    have path := finiteControlledOrbitFrom_isControlled p rho x₀ u
    have hpay := path.floored_action_lower_bound_of_crossing
      model ss hcoop weighted hL hx₀.1 hfloor hx₀.2.1 hx₀.2.2 hcross
    rw [controlAction_extendFiniteControl] at hpay
    simpa only [flooredLedgerCrossingRate, sub_zero] using hpay

/-- At the calibrated corner, the definition of the crossing
quasipotential itself is a zero-error no-cheap-crossing certificate. -/
def calibratedNoCheapCrossingRate
    {p : LoopParams} {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho) (T : ℕ) :
    NoCheapCrossingRate weighted where
  starts := {calibratedPoint p}
  horizon := T
  rate := civicCrossingQuasipotential weighted
  error := 0
  error_nonneg := le_rfl
  action_lower x₀ hx₀ u hcross := by
    have hx₀eq : x₀ = calibratedPoint p := by simpa only [mem_singleton_iff] using hx₀
    subst x₀
    have horbit : finiteControlledOrbitFrom p rho (calibratedPoint p) u =
        finiteControlledOrbit p rho u := by
      funext n
      exact finiteControlledOrbitFrom_calibratedPoint p rho u n
    rw [horbit] at hcross
    simpa only [sub_zero] using
      civicCrossingQuasipotential_le_gaussianVectorAction weighted hcross

#print axioms continuous_policyRunningMax_finiteControlledOrbitFrom
#print axioms measurableSet_gaussianCrossingEventFrom
#print axioms gaussianVectorAction_scaledGaussianControl
#print axioms continuous_finiteControlledHistoryFrom
#print axioms exists_uniform_start_radius_on_controlBall
#print axioms dist_control_zero_le_two_mul_actionBound_add_one
#print axioms bumpFiniteControl_self
#print axioms bumpFiniteControl_of_ne
#print axioms finiteControlledOrbitFrom_bump_eq_of_le
#print axioms finiteControlledOrbitFrom_bump_succ_policy
#print axioms gaussianVectorAction_bumpFiniteControl
#print axioms target_le_clipUnit_add_of_close
#print axioms target_lt_clipUnit_add_of_le
#print axioms exists_home_radius_crossing_action_lower_bound
#print axioms exists_home_radius_crossing_action_lower_bound_unrestricted
#print axioms exists_home_radius_nearCrossing_action_lower_bound_unrestricted
#print axioms measurableSet_gaussianNearCrossingEventFrom
#print axioms gaussianCrossingEventFrom_subset_actionTail
#print axioms gaussianNearCrossingEventFrom_subset_actionTail
#print axioms gaussianCrossingProbabilityFrom_le_chernoff
#print axioms gaussianNearCrossingProbabilityFrom_le_chernoff
#print axioms gaussianCrossingProbabilityFrom_le_uniform_chernoff
#print axioms exists_home_radius_gaussianCrossingProbability_le_chernoff
#print axioms exists_home_radius_gaussianNearCrossingProbability_le_chernoff
#print axioms gaussianControlBox_subset_crossingEventFrom
#print axioms robustCrossingTube_probability_lower
#print axioms robustCrossingTube_logRate_liminf
#print axioms continuous_policyRunningMax_finiteControlledOrbitFrom_joint
#print axioms exists_uniform_runningMax_control_radius
#print axioms exists_robust_crossing_control_radius_of_uniform_margin
#print axioms exists_closedBall_uniform_margin_of_start
#print axioms exists_closedBall_uniform_margin_of_calibrated
#print axioms exists_robustCrossingTube_of_calibrated_margin
#print axioms exists_robustCrossingTube_of_start_margin
#print axioms exists_weightedSaddle_robustCrossingTube_small_action
#print axioms exists_margin_crossing_control_lt_quasipotential_add
#print axioms exists_quasipotential_robustCrossingTube
#print axioms isCompact_flooredLedgerStartSet
#print axioms flooredLedgerNoCheapCrossingRate
#print axioms calibratedNoCheapCrossingRate

end

end CivicAlignment.PaperII
