/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.ArrheniusMatching
import CivicAlignment.PaperII.ArrheniusSaddle

/-!
# Paper II: lower Arrhenius bound and renewal accounting

This file assembles the persistence half of `thm:arr`.  It starts with the
finite-product restart needed to use the weighted-saddle anti-concentration
bound at a random state determined by an arbitrary Gaussian prefix.
-/

namespace CivicAlignment.PaperII

open Filter Function MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal

noncomputable section

/-! ## Horizon-free pricing of first near-saddle entrance -/

/-- Action surcharge for boosting a control which has reached within
`margin` of the saddle policy into an exact crossing.  The coarse coordinate
bound `2 * B + 1` is the same horizon-independent bound used by the finite
transport lemmas in `ArrheniusBlocks`. -/
def nearCrossingBoostError (p : LoopParams) (B margin : ℝ) : ℝ :=
  (2 * B + 1) * (2 * margin / p.α) + (2 * margin / p.α) ^ 2 / 2

/-- Policy matching makes the cost of reaching a thin strip below the saddle
uniform in the horizon.  A bump at the already advancing entrance step turns
the strip entrance into an exact crossing; no fresh cancellation step is
introduced. -/
theorem nearCrossing_action_lower_of_policyMatching
    {p : LoopParams} (model : DriftModelAssumptions p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    {epsilon B margin : ℝ} (hB0 : 0 ≤ B)
    (hvalue : civicCrossingQuasipotential weighted ≤ B)
    (hepsilon0 : 0 ≤ epsilon) (hepsilon : epsilon ≤ 1)
    (hepsilonStrip : epsilon < weighted.βdagger - margin)
    (hmargin : 0 < margin) (hmarginSaddle : 2 * margin < weighted.βdagger)
    {T : ℕ} {z : LoopState} (hz : z ∈ absorbingBox p)
    (hzdistance : dist z (calibratedPoint p) ≤ epsilon)
    {u : Fin T → ℝ}
    (hnear : weighted.βdagger - margin ≤
      policyRunningMax (finiteControlledOrbitFrom p rho z u) T) :
    civicCrossingQuasipotential weighted -
        (nearCrossingBoostError p B margin +
          policyMatchingActionConstant p rho * epsilon *
            (1 + √(2 * (B + nearCrossingBoostError p B margin)))) ≤
      gaussianVectorAction u := by
  let q : ℝ := 2 * margin / p.α
  let R : ℝ := 2 * B + 1
  let boost : ℝ := R * q + q ^ 2 / 2
  have hq : 0 < q := div_pos (by linarith) model.α_pos
  have hR : 0 < R := by dsimp only [R]; linarith
  have hboost : 0 ≤ boost := by
    dsimp only [boost]
    positivity
  have hBboost : civicCrossingQuasipotential weighted ≤ B + boost :=
    hvalue.trans (le_add_of_nonneg_right hboost)
  have hmatchNonneg : 0 ≤
      policyMatchingActionConstant p rho * epsilon *
        (1 + √(2 * (B + boost))) := by
    exact mul_nonneg
      (mul_nonneg (policyMatchingActionConstant_nonneg model rho) hepsilon0)
      (add_nonneg zero_le_one (Real.sqrt_nonneg _))
  rcases le_total (gaussianVectorAction u) B with haction | hlarge
  · have hcontrolRadius : dist u 0 ≤ R := by
      simpa only [R] using
        dist_control_zero_le_two_mul_actionBound_add_one haction hB0
    obtain ⟨j, hjT, hjnear⟩ :=
      (le_runningMax_iff (a := fun n ↦
        (finiteControlledOrbitFrom p rho z u n).1)).1 hnear
    cases j with
    | zero =>
        have hzPolicyDist : z.1 ≤ dist z (calibratedPoint p) := by
          have h := le_max_left (dist z.1 (calibratedPoint p).1)
            (dist z.2 (calibratedPoint p).2)
          rw [← Prod.dist_eq] at h
          have habs : |z.1| ≤ dist z (calibratedPoint p) := by
            simpa only [calibratedPoint, Real.dist_eq, sub_zero] using h
          exact (le_abs_self z.1).trans habs
        simp only [finiteControlledOrbitFrom] at hjnear
        linarith
    | succ j =>
        have hjltT : j < T := by omega
        let i : Fin T := ⟨j, hjltT⟩
        let raw : ℝ :=
          (finiteControlledOrbitFrom p rho z u j).1 +
            p.α * (civicWeightedGradient p rho
                (finiteControlledOrbitFrom p rho z u j).1
                (finiteControlledOrbitFrom p rho z u j).2 + u i)
        have hunbumpedPolicy :
            (finiteControlledOrbitFrom p rho z u (j + 1)).1 =
              LoopParams.clipUnit raw := by
          simp only [finiteControlledOrbitFrom, controlledCivicWeightedStep,
            extendFiniteControl, hjltT, dite_true, raw, i]
        have hcloseRaw : weighted.βdagger - margin ≤
            LoopParams.clipUnit raw := by
          rw [← hunbumpedPolicy]
          simpa only [Nat.succ_eq_add_one] using hjnear
        have hAlphaQ : p.α * q = 2 * margin := by
          dsimp only [q]
          field_simp [model.α_pos.ne']
        have hcloseRaw' : weighted.βdagger - 2 * margin <
            LoopParams.clipUnit raw := by
          linarith
        have hbumpedPolicy : weighted.βdagger ≤
            (finiteControlledOrbitFrom p rho z
              (bumpFiniteControl u i q) (j + 1)).1 := by
          rw [show j + 1 = (i : ℕ) + 1 by rfl,
            finiteControlledOrbitFrom_bump_succ_policy]
          change weighted.βdagger ≤
            LoopParams.clipUnit (raw + p.α * q)
          rw [hAlphaQ]
          exact target_le_clipUnit_add_of_close weighted.βdagger_mem
            (by linarith) hmarginSaddle hcloseRaw'
        have hbumpedCross : weighted.βdagger ≤
            policyRunningMax
              (finiteControlledOrbitFrom p rho z
                (bumpFiniteControl u i q)) T := by
          exact hbumpedPolicy.trans
            ((policy_le_runningMax
                (finiteControlledOrbitFrom p rho z
                  (bumpFiniteControl u i q)) (j + 1)).trans
              ((monotone_runningMax fun n ↦
                (finiteControlledOrbitFrom p rho z
                  (bumpFiniteControl u i q) n).1) hjT))
        have hzbelow : z.1 < weighted.βdagger := by
          have hzPolicyDist : z.1 ≤ dist z (calibratedPoint p) := by
            have h := le_max_left (dist z.1 (calibratedPoint p).1)
              (dist z.2 (calibratedPoint p).2)
            rw [← Prod.dist_eq] at h
            have habs : |z.1| ≤ dist z (calibratedPoint p) := by
              simpa only [calibratedPoint, Real.dist_eq, sub_zero] using h
            exact (le_abs_self z.1).trans habs
          linarith
        have hmatched :=
          civicCrossingQuasipotential_sub_matchingError_le_action
            model weighted hz hzbelow hzdistance hepsilon hBboost hbumpedCross
        have huiAbs : |u i| ≤ R := by
          have hui := (dist_pi_le_iff hR.le).1 hcontrolRadius i
          simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using hui
        have huiMul : u i * q ≤ R * q :=
          mul_le_mul_of_nonneg_right
            ((le_abs_self (u i)).trans huiAbs) hq.le
        have hbumpedAction :
            gaussianVectorAction (bumpFiniteControl u i q) ≤
              gaussianVectorAction u + boost := by
          rw [gaussianVectorAction_bumpFiniteControl]
          dsimp only [boost]
          linarith
        dsimp only [nearCrossingBoostError]
        change civicCrossingQuasipotential weighted -
            (boost + policyMatchingActionConstant p rho * epsilon *
              (1 + √(2 * (B + boost)))) ≤ gaussianVectorAction u
        linarith
  · dsimp only [nearCrossingBoostError]
    change civicCrossingQuasipotential weighted -
        (boost + policyMatchingActionConstant p rho * epsilon *
          (1 + √(2 * (B + boost)))) ≤ gaussianVectorAction u
    linarith

/-- The closed saddle order interval remains valid from an arbitrary
last-exit state already in that interval, as long as the future running
maximum has not crossed.  This is the restart form of the pre-crossing
geometry used below. -/
theorem IsControlledCivicWeightedPathFrom.mem_weightedSaddleOrderInterval
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    {x₀ : LoopState} {u : ℕ → ℝ} {x : ℕ → LoopState}
    (path : IsControlledCivicWeightedPathFrom p rho x₀ u x)
    (hx₀ : x₀ ∈ absorbingBox p)
    (hlower₀ : calibratedPoint p ≤ x₀)
    (hupper₀ : x₀ ≤ weightedSaddlePoint weighted)
    {N n : ℕ} (hn : n ≤ N)
    (hmax : policyRunningMax x N ≤ weighted.βdagger) :
    x n ∈ absorbingBox p ∩
      Set.Icc (calibratedPoint p) (weightedSaddlePoint weighted) := by
  have hsaddleMem : weightedSaddlePoint weighted ∈ absorbingBox p :=
    weightedSaddlePoint_mem_absorbingBox model weighted
  have hlower : calibratedPoint p ≤ x n :=
    path.calibratedPoint_le model ss hx₀ hlower₀ n
  have hbox : x n ∈ absorbingBox p := path.mem_absorbingBox model hx₀ n
  have hupperAll : ∀ m ≤ N, x m ≤ weightedSaddlePoint weighted := by
    intro m hm
    induction m with
    | zero => simpa only [path.initial] using hupper₀
    | succ m ih =>
        have hmN : m ≤ N := m.le_succ.trans hm
        have ih' : x m ≤ weightedSaddlePoint weighted := ih hmN
        have hxmem : x m ∈ absorbingBox p :=
          path.mem_absorbingBox model hx₀ m
        have hstockStep :=
          (loopMap_monotoneOn_box model ss hxmem hsaddleMem ih').2
        have hmaxMono : policyRunningMax x (m + 1) ≤
            policyRunningMax x N := by
          exact (monotone_runningMax fun k ↦ (x k).1) hm
        have hpolicy : (x (m + 1)).1 ≤ weighted.βdagger :=
          (policy_le_runningMax x (m + 1)).trans (hmaxMono.trans hmax)
        have hstock : (x (m + 1)).2 ≤
            (weightedSaddlePoint weighted).2 := by
          rw [path.step m]
          change p.stockStep (x m).1 (x m).2 ≤
            (weightedSaddlePoint weighted).2
          have hsaddleFixed :=
            civicWeightedLoopMap_weightedSaddlePoint model weighted
          have hsaddleStock : p.stockStep
                (weightedSaddlePoint weighted).1
                (weightedSaddlePoint weighted).2 =
              (weightedSaddlePoint weighted).2 := by
            simpa only [civicWeightedLoopMap] using congrArg Prod.snd hsaddleFixed
          simpa only [LoopParams.loopMap, hsaddleStock] using hstockStep
        exact ⟨by simpa only [weightedSaddlePoint] using hpolicy, hstock⟩
  have hupper : x n ≤ weightedSaddlePoint weighted := hupperAll n hn
  exact ⟨hbox, hlower, hupper⟩

/-! ## Last-exit excursions and first strip entrance -/

/-- At every fixed time, the arbitrary-start Gaussian recursion is a
continuous function of the infinite noise history. -/
theorem continuous_gaussianNoisyOrbitFrom
    (p : LoopParams) (rho : ℝ) (z : LoopState) (sigma : ℝ) (n : ℕ) :
    Continuous (fun xi : GaussianNoisePath ↦
      gaussianNoisyOrbitFrom p rho z sigma xi n) := by
  induction n with
  | zero =>
      simp only [gaussianNoisyOrbitFrom, controlledCivicWeightedOrbitFrom]
      fun_prop
  | succ n ih =>
      change Continuous (fun xi : GaussianNoisePath ↦
        controlledCivicWeightedStep p rho (sigma * xi n)
          (gaussianNoisyOrbitFrom p rho z sigma xi n))
      unfold controlledCivicWeightedStep civicWeightedGradient
        LoopParams.gradU LoopParams.stockStep LoopParams.s LoopParams.clipUnit
      fun_prop

/-- Histories which first complete an excursion at the specified time:
the state reaches the near-saddle policy strip while every positive-time
state through that time remains outside the closed home ball.  Minimality of
the strip entrance is selected later from this event's witness. -/
def nearCrossingExcursionAtTimeEvent
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (z : LoopState) (sigma homeRadius margin : ℝ) (n : ℕ) :
    Set GaussianNoisePath :=
  {xi | 1 ≤ n ∧
    weighted.βdagger - margin ≤
      (gaussianNoisyOrbitFrom p rho z sigma xi n).1 ∧
    ∀ k ∈ Finset.Icc 1 n,
      homeRadius <
        dist (gaussianNoisyOrbitFrom p rho z sigma xi k)
          (calibratedPoint p)}

/-- The exact-time excursion event is Borel measurable. -/
theorem measurableSet_nearCrossingExcursionAtTimeEvent
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (z : LoopState) (sigma homeRadius margin : ℝ) (n : ℕ) :
    MeasurableSet
      (nearCrossingExcursionAtTimeEvent
        weighted z sigma homeRadius margin n) := by
  by_cases hn : 1 ≤ n
  · have htarget : MeasurableSet
        {xi : GaussianNoisePath | weighted.βdagger - margin ≤
          (gaussianNoisyOrbitFrom p rho z sigma xi n).1} := by
      exact measurableSet_Ici.preimage
        (continuous_gaussianNoisyOrbitFrom p rho z sigma n).fst.measurable
    have hout : ∀ k : ℕ, MeasurableSet
        {xi : GaussianNoisePath | homeRadius <
          dist (gaussianNoisyOrbitFrom p rho z sigma xi k)
            (calibratedPoint p)} := by
      intro k
      exact measurableSet_Ioi.preimage
        ((continuous_gaussianNoisyOrbitFrom p rho z sigma k).dist
          continuous_const).measurable
    rw [show nearCrossingExcursionAtTimeEvent
          weighted z sigma homeRadius margin n =
        {xi : GaussianNoisePath | weighted.βdagger - margin ≤
          (gaussianNoisyOrbitFrom p rho z sigma xi n).1} ∩
          ⋂ k ∈ Finset.Icc 1 n,
            {xi : GaussianNoisePath | homeRadius <
              dist (gaussianNoisyOrbitFrom p rho z sigma xi k)
                (calibratedPoint p)} by
      ext xi
      simp only [nearCrossingExcursionAtTimeEvent, Set.mem_setOf_eq,
        Set.mem_inter_iff, Set.mem_iInter, hn, true_and]]
    exact htarget.inter
      (Finset.measurableSet_biInter (Finset.Icc 1 n) fun k _hk ↦ hout k)
  · have hempty : nearCrossingExcursionAtTimeEvent
        weighted z sigma homeRadius margin n = ∅ := by
      ext xi
      simp only [nearCrossingExcursionAtTimeEvent, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false]
      exact fun h ↦ hn h.1
    rw [hempty]
    exact MeasurableSet.empty

/-- An excursion which reaches the near-saddle policy strip before returning
to the home ball, at some finite positive time. -/
def nearCrossingExcursionEvent
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (z : LoopState) (sigma homeRadius margin : ℝ) :
    Set GaussianNoisePath :=
  ⋃ n : ℕ,
    nearCrossingExcursionAtTimeEvent weighted z sigma homeRadius margin n

/-- Literal membership semantics for a near-crossing excursion. -/
theorem mem_nearCrossingExcursionEvent_iff
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (z : LoopState) (sigma homeRadius margin : ℝ)
    (xi : GaussianNoisePath) :
    xi ∈ nearCrossingExcursionEvent weighted z sigma homeRadius margin ↔
      ∃ n : ℕ, 1 ≤ n ∧
        weighted.βdagger - margin ≤
          (gaussianNoisyOrbitFrom p rho z sigma xi n).1 ∧
        ∀ k ∈ Finset.Icc 1 n,
          homeRadius <
            dist (gaussianNoisyOrbitFrom p rho z sigma xi k)
              (calibratedPoint p) := by
  simp only [nearCrossingExcursionEvent, Set.mem_iUnion,
    nearCrossingExcursionAtTimeEvent, Set.mem_setOf_eq]

/-- The unrestricted excursion event is measurable as a countable union. -/
theorem measurableSet_nearCrossingExcursionEvent
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (z : LoopState) (sigma homeRadius margin : ℝ) :
    MeasurableSet
      (nearCrossingExcursionEvent weighted z sigma homeRadius margin) := by
  exact MeasurableSet.iUnion fun n ↦
    measurableSet_nearCrossingExcursionAtTimeEvent
      weighted z sigma homeRadius margin n

/-- The near-strip event by a fixed horizon, phrased on the canonical
infinite history space through its finite prefix. -/
def gaussianNearCrossingByEventFrom
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (margin : ℝ) (z : LoopState) (T : ℕ) (sigma : ℝ) :
    Set GaussianNoisePath :=
  gaussianPrefix T ⁻¹'
    gaussianNearCrossingEventFrom weighted margin z T sigma

/-- The fixed-horizon arbitrary-start near-strip event is measurable. -/
theorem measurableSet_gaussianNearCrossingByEventFrom
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (margin : ℝ) (z : LoopState) (T : ℕ) (sigma : ℝ) :
    MeasurableSet
      (gaussianNearCrossingByEventFrom weighted margin z T sigma) := by
  exact (measurableSet_gaussianNearCrossingEventFrom
    weighted margin z T sigma).preimage (measurable_gaussianPrefix T)

/-- The infinite-history near-strip event has exactly the corresponding
finite-vector probability. -/
theorem standardGaussianSequence_gaussianNearCrossingByEventFrom
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (margin : ℝ) (z : LoopState) (T : ℕ) (sigma : ℝ) :
    standardGaussianSequence
        (gaussianNearCrossingByEventFrom weighted margin z T sigma) =
      gaussianNearCrossingProbabilityFrom weighted margin z T sigma := by
  unfold gaussianNearCrossingByEventFrom
  rw [← Measure.map_apply (measurable_gaussianPrefix T)
      (measurableSet_gaussianNearCrossingEventFrom
        weighted margin z T sigma),
    standardGaussianSequence_map_prefix]
  rfl

/-- First-entrance decomposition for a last-exit excursion.  Before the
first visit to the thin near-saddle policy strip, every positive-time state
is outside the full saddle ball.  If the visit occurs early, policy matching
prices it directly; if it occurs later, `K` disjoint away-set funnel windows
have already paid `K*c`.  Thus the entire unbounded excursion event is
contained in one fixed-dimensional Gaussian action tail. -/
theorem exists_nearCrossingExcursionEvent_subset_actionTail
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho epsilon margin : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hepsilon : 0 < epsilon) (hmargin : 0 < margin) :
    ∃ T : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ (K : ℕ) (base B sigma : ℝ) (z : LoopState),
        0 ≤ B → civicCrossingQuasipotential weighted ≤ B →
        2 * epsilon ≤ 1 →
        2 * epsilon < weighted.βdagger - margin →
        2 * margin < weighted.βdagger →
        base ≤ civicCrossingQuasipotential weighted -
          (nearCrossingBoostError p B margin +
            policyMatchingActionConstant p rho * (2 * epsilon) *
              (1 + √(2 * (B + nearCrossingBoostError p B margin)))) →
        base ≤ (K : ℝ) * c →
        z ∈ absorbingBox p → calibratedPoint p ≤ z →
        z ≤ weightedSaddlePoint weighted →
        dist z (calibratedPoint p) ≤ 2 * epsilon → sigma ≠ 0 →
        nearCrossingExcursionEvent
            weighted z sigma (2 * epsilon) margin ⊆
          gaussianPrefixActionTailEvent ((K + 1) * (T + 1))
            (base / sigma ^ 2) := by
  obtain ⟨T, c, hc, hspaced⟩ :=
    exists_awaySaddle_spacedWindow_action_bound
      model ss threshold hrho hcoop weighted hmargin hepsilon
  refine ⟨T, c, hc, ?_⟩
  intro K base B sigma z hB0 hvalue hepsilonOne hepsilonStrip
    hmarginSaddle hbaseNear hbaseWindows hz hlower hupper hzdistance hsigma xi hxi
  obtain ⟨n, hn1, hnTarget, hnHome⟩ :=
    (mem_nearCrossingExcursionEvent_iff
      weighted z sigma (2 * epsilon) margin xi).1 hxi
  let target : ℕ → Prop := fun m ↦
    1 ≤ m ∧ weighted.βdagger - margin ≤
      (gaussianNoisyOrbitFrom p rho z sigma xi m).1
  have hex : ∃ m, target m := ⟨n, hn1, hnTarget⟩
  let first : ℕ := Nat.find hex
  have hfirst := Nat.find_spec hex
  have hfirstLe : first ≤ n := Nat.find_min' hex ⟨hn1, hnTarget⟩
  let stride : ℕ := T + 1
  let horizon : ℕ := (K + 1) * stride
  let u : ℕ → ℝ := fun k ↦ sigma * xi k
  let x : ℕ → LoopState := gaussianNoisyOrbitFrom p rho z sigma xi
  have path : IsControlledCivicWeightedPathFrom p rho z u x := by
    exact controlledCivicWeightedOrbitFrom_isControlled p rho z u
  have hscaledAction : controlAction u horizon =
      sigma ^ 2 * gaussianVectorAction (gaussianPrefix horizon xi) := by
    rw [← gaussianVectorAction_restrict u horizon]
    exact gaussianVectorAction_scaledGaussianControl
      sigma (gaussianPrefix horizon xi)
  have htailMembership : base / sigma ^ 2 ≤
      gaussianVectorAction (gaussianPrefix horizon xi) →
      xi ∈ gaussianPrefixActionTailEvent horizon (base / sigma ^ 2) := by
    intro hpay
    exact hpay
  by_cases hfirstShort : first ≤ horizon
  · have hstateEq :
        finiteControlledOrbitFrom p rho z
            (scaledGaussianControl sigma (gaussianPrefix horizon xi)) first =
          x first := by
      simpa only [x] using
        finiteControlledOrbitFrom_gaussianPrefix_eq_gaussianNoisyOrbitFrom
          p rho z sigma xi hfirstShort
    have hnear : weighted.βdagger - margin ≤
        policyRunningMax
          (finiteControlledOrbitFrom p rho z
            (scaledGaussianControl sigma (gaussianPrefix horizon xi)))
          horizon := by
      calc
        weighted.βdagger - margin ≤ (x first).1 := hfirst.2
        _ = (finiteControlledOrbitFrom p rho z
            (scaledGaussianControl sigma (gaussianPrefix horizon xi)) first).1 :=
          congrArg Prod.fst hstateEq.symm
        _ ≤ policyRunningMax
            (finiteControlledOrbitFrom p rho z
              (scaledGaussianControl sigma (gaussianPrefix horizon xi)))
            first := policy_le_runningMax _ _
        _ ≤ policyRunningMax
            (finiteControlledOrbitFrom p rho z
              (scaledGaussianControl sigma (gaussianPrefix horizon xi)))
            horizon :=
          (monotone_runningMax fun m ↦
            (finiteControlledOrbitFrom p rho z
              (scaledGaussianControl sigma (gaussianPrefix horizon xi)) m).1)
            hfirstShort
    have hpay := nearCrossing_action_lower_of_policyMatching
      model weighted hB0 hvalue (by linarith : 0 ≤ 2 * epsilon)
        hepsilonOne hepsilonStrip hmargin hmarginSaddle hz hzdistance hnear
    have hbaseControl : base ≤ controlAction u horizon := by
      calc
        base ≤ gaussianVectorAction
            (scaledGaussianControl sigma (gaussianPrefix horizon xi)) :=
          hbaseNear.trans hpay
        _ = controlAction u horizon := by
          rw [gaussianVectorAction_scaledGaussianControl, hscaledAction]
    apply htailMembership
    apply (div_le_iff₀ (sq_pos_of_ne_zero hsigma)).2
    rw [hscaledAction] at hbaseControl
    simpa only [mul_comm] using hbaseControl
  · have hhorizonFirst : horizon < first := lt_of_not_ge hfirstShort
    let S : Finset ℕ := Finset.Icc 1 K
    have hS : S ⊆ Finset.range (K + 1) := by
      intro j hj
      simp only [S, Finset.mem_Icc] at hj
      simp only [Finset.mem_range]
      omega
    have hstartBefore : ∀ j ∈ S, j * stride < first := by
      intro j hj
      have hjK : j ≤ K := (Finset.mem_Icc.mp hj).2
      calc
        j * stride ≤ K * stride := Nat.mul_le_mul_right stride hjK
        _ < (K + 1) * stride := by
          have hstride : 0 < stride := by dsimp only [stride]; omega
          nlinarith
        _ = horizon := rfl
        _ < first := hhorizonFirst
    have htargetFree : ∀ m, 1 ≤ m → m < first →
        (x m).1 < weighted.βdagger - margin := by
      intro m hm1 hmfirst
      have hnot := Nat.find_min hex hmfirst
      change ¬target m at hnot
      dsimp only [target] at hnot
      exact lt_of_not_ge (fun h ↦ hnot ⟨hm1, h⟩)
    have haway : ∀ j ∈ S,
        x (j * stride) ∈ weightedPreCrossingAwaySet weighted margin := by
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have htime1 : 1 ≤ j * stride := by
        have hstride : 1 ≤ stride := by dsimp only [stride]; omega
        exact Nat.mul_pos hj1 hstride
      have htimeFirst := hstartBefore j hj
      have hpolicyStrip := htargetFree (j * stride) htime1 htimeFirst
      have hmax : policyRunningMax x (j * stride) ≤ weighted.βdagger := by
        apply runningMax_le_of_forall_le
        intro m hm
        by_cases hm0 : m = 0
        · subst m
          have hzPolicyDist : z.1 ≤ dist z (calibratedPoint p) := by
            have h := le_max_left (dist z.1 (calibratedPoint p).1)
              (dist z.2 (calibratedPoint p).2)
            rw [← Prod.dist_eq] at h
            have habs : |z.1| ≤ dist z (calibratedPoint p) := by
              simpa only [calibratedPoint, Real.dist_eq, sub_zero] using h
            exact (le_abs_self z.1).trans habs
          have hzle : z.1 ≤ weighted.βdagger :=
            (hzPolicyDist.trans hzdistance).trans
              (hepsilonStrip.trans (sub_lt_self _ hmargin)).le
          simpa only [x, gaussianNoisyOrbitFrom,
            controlledCivicWeightedOrbitFrom] using hzle
        · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
          have hmFirst : m < first :=
            hm.trans_lt htimeFirst
          exact (htargetFree m hm1 hmFirst).le.trans
            (sub_le_self _ hmargin.le)
      have horder := path.mem_weightedSaddleOrderInterval
        model ss weighted hz hlower hupper le_rfl hmax
      refine ⟨horder, ?_⟩
      intro hball
      have hcoord : dist (x (j * stride)).1
          (weightedSaddlePoint weighted).1 ≤
          dist (x (j * stride)) (weightedSaddlePoint weighted) := by
        rw [Prod.dist_eq]
        exact le_max_left _ _
      have hdistPolicy : dist (x (j * stride)).1
          weighted.βdagger ≤ margin := by
        simpa only [weightedSaddlePoint] using hcoord.trans hball.le
      rw [Real.dist_eq] at hdistPolicy
      have hpolicyLe : (x (j * stride)).1 ≤ weighted.βdagger :=
        hpolicyStrip.le.trans (sub_le_self _ hmargin.le)
      rw [abs_of_nonpos (sub_nonpos.mpr hpolicyLe)] at hdistPolicy
      linarith
    have hout : ∀ j ∈ S,
        2 * epsilon ≤
          dist (x (j * stride + T)) (calibratedPoint p) := by
      intro j hj
      have hjK : j ≤ K := (Finset.mem_Icc.mp hj).2
      have hendpointFirst : j * stride + T < first := by
        calc
          j * stride + T < j * stride + stride := by
            dsimp only [stride]
            omega
          _ = (j + 1) * stride := by ring
          _ ≤ (K + 1) * stride :=
            Nat.mul_le_mul_right stride (Nat.add_le_add_right hjK 1)
          _ = horizon := rfl
          _ < first := hhorizonFirst
      have hendpoint1 : 1 ≤ j * stride + T := by
        have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
        have hstride : 1 ≤ stride := by dsimp only [stride]; omega
        exact (Nat.mul_pos hj1 hstride).trans_le (Nat.le_add_right _ _)
      have hendpointLeN : j * stride + T ≤ n :=
        hendpointFirst.le.trans hfirstLe
      have hmem : j * stride + T ∈ Finset.Icc 1 n := by
        exact Finset.mem_Icc.mpr ⟨hendpoint1, hendpointLeN⟩
      exact (hnHome (j * stride + T) hmem).le
    have hcharged := hspaced z u x path stride (K + 1) S
      (by dsimp only [stride]; omega) hS haway hout
    have hcard : S.card = K := by
      simp only [S, Nat.card_Icc]
      omega
    rw [hcard] at hcharged
    have hbaseControl : base ≤ controlAction u horizon := by
      simpa only [horizon] using hbaseWindows.trans hcharged
    apply htailMembership
    apply (div_le_iff₀ (sq_pos_of_ne_zero hsigma)).2
    rw [hscaledAction] at hbaseControl
    simpa only [mul_comm] using hbaseControl

/-- Fixed-horizon action-tail packaging of the first-entrance decomposition,
with the number of away windows chosen by a natural ceiling. -/
theorem exists_nearCrossingExcursionEvent_subset_fixed_actionTail
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho epsilon margin base B : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hepsilon : 0 < epsilon) (hmargin : 0 < margin)
    (hB0 : 0 ≤ B) (hvalue : civicCrossingQuasipotential weighted ≤ B)
    (hepsilonOne : 2 * epsilon ≤ 1)
    (hepsilonStrip : 2 * epsilon < weighted.βdagger - margin)
    (hmarginSaddle : 2 * margin < weighted.βdagger)
    (hbaseNear : base ≤ civicCrossingQuasipotential weighted -
      (nearCrossingBoostError p B margin +
        policyMatchingActionConstant p rho * (2 * epsilon) *
          (1 + √(2 * (B + nearCrossingBoostError p B margin))))) :
    ∃ H : ℕ, ∀ z : LoopState,
      z ∈ absorbingBox p → calibratedPoint p ≤ z →
      z ≤ weightedSaddlePoint weighted →
      dist z (calibratedPoint p) ≤ 2 * epsilon →
      ∀ {sigma : ℝ}, sigma ≠ 0 →
        nearCrossingExcursionEvent
            weighted z sigma (2 * epsilon) margin ⊆
          gaussianPrefixActionTailEvent H (base / sigma ^ 2) := by
  obtain ⟨T, c, hc, hsubset⟩ :=
    exists_nearCrossingExcursionEvent_subset_actionTail
      model ss threshold hrho hcoop weighted hepsilon hmargin
  let K : ℕ := ⌈max 0 base / c⌉₊
  let H : ℕ := (K + 1) * (T + 1)
  have hbaseK : base ≤ (K : ℝ) * c := by
    have hceil : max 0 base / c ≤ (K : ℝ) := Nat.le_ceil _
    have hmul : max 0 base ≤ (K : ℝ) * c := by
      have hscaled := mul_le_mul_of_nonneg_right hceil hc.le
      calc
        max 0 base = (max 0 base / c) * c := by
          field_simp [hc.ne']
        _ ≤ (K : ℝ) * c := hscaled
    exact (le_max_right 0 base).trans hmul
  refine ⟨H, fun z hz hlower hupper hzdistance sigma hsigma ↦ ?_⟩
  simpa only [H] using
    hsubset K base B sigma z hB0 hvalue hepsilonOne hepsilonStrip
      hmarginSaddle hbaseNear hbaseK hz hlower hupper hzdistance hsigma

/-- Probabilistic form of the first-entrance decomposition.  Once the direct
near-strip price is at least `base`, a finite number of disjoint away windows
also reaches `base`; hence one fixed-dimensional chi-square Chernoff bound is
uniform over every admissible last-exit state and over excursions of arbitrary
duration. -/
theorem exists_nearCrossingExcursionProbability_le_chernoff
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho epsilon margin base B : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hepsilon : 0 < epsilon) (hmargin : 0 < margin)
    (hB0 : 0 ≤ B) (hvalue : civicCrossingQuasipotential weighted ≤ B)
    (hepsilonOne : 2 * epsilon ≤ 1)
    (hepsilonStrip : 2 * epsilon < weighted.βdagger - margin)
    (hmarginSaddle : 2 * margin < weighted.βdagger)
    (hbaseNear : base ≤ civicCrossingQuasipotential weighted -
      (nearCrossingBoostError p B margin +
        policyMatchingActionConstant p rho * (2 * epsilon) *
          (1 + √(2 * (B + nearCrossingBoostError p B margin))))) :
    ∃ H : ℕ, ∀ z : LoopState,
      z ∈ absorbingBox p → calibratedPoint p ≤ z →
      z ≤ weightedSaddlePoint weighted →
      dist z (calibratedPoint p) ≤ 2 * epsilon →
      ∀ {sigma t : ℝ}, sigma ≠ 0 → 0 ≤ t → t < 1 →
        standardGaussianSequence
            (nearCrossingExcursionEvent
              weighted z sigma (2 * epsilon) margin) ≤
          ENNReal.ofReal
            (Real.exp (-t * (base / sigma ^ 2)) *
              mgf gaussianVectorAction (standardGaussianVector H) t) := by
  obtain ⟨T, c, hc, hsubset⟩ :=
    exists_nearCrossingExcursionEvent_subset_actionTail
      model ss threshold hrho hcoop weighted hepsilon hmargin
  let K : ℕ := ⌈max 0 base / c⌉₊
  let H : ℕ := (K + 1) * (T + 1)
  have hbaseK : base ≤ (K : ℝ) * c := by
    have hceil : max 0 base / c ≤ (K : ℝ) := by
      exact Nat.le_ceil _
    have hmul : max 0 base ≤ (K : ℝ) * c := by
      have := mul_le_mul_of_nonneg_right hceil hc.le
      calc
        max 0 base = (max 0 base / c) * c := by
          field_simp [hc.ne']
        _ ≤ (K : ℝ) * c := this
    exact (le_max_right 0 base).trans hmul
  refine ⟨H, fun z hz hlower hupper hzdistance sigma t hsigma ht0 ht1 ↦ ?_⟩
  have hset := hsubset K base B sigma z hB0 hvalue hepsilonOne
    hepsilonStrip hmarginSaddle hbaseNear hbaseK hz hlower hupper
      hzdistance hsigma
  calc
    standardGaussianSequence
        (nearCrossingExcursionEvent
          weighted z sigma (2 * epsilon) margin) ≤
        standardGaussianSequence
          (gaussianPrefixActionTailEvent H (base / sigma ^ 2)) := by
      simpa only [H] using measure_mono hset
    _ = gaussianActionTailProbability H (base / sigma ^ 2) :=
      standardGaussianSequence_gaussianPrefixActionTailEvent _ _
    _ ≤ ENNReal.ofReal
          (Real.exp (-t * (base / sigma ^ 2)) *
            mgf gaussianVectorAction (standardGaussianVector H) t) :=
      by simpa only [mgf_gaussianVectorAction_eq_pow] using
        (gaussianActionTailProbability_le_chernoff
          H (B := base / sigma ^ 2) ht0 ht1)

/-- Every positive tolerance admits a home ball and a near-saddle strip for
which the probability of a complete last-exit excursion is bounded at rate
`V^x - delta`, uniformly over all admissible last-exit states. -/
theorem exists_uniform_nearCrossingExcursionProbability_le
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho delta : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hdelta : 0 < delta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ margin : ℝ, 0 < margin ∧
        2 * epsilon < weighted.βdagger - margin ∧
        ∃ H : ℕ,
          (∀ z : LoopState,
            z ∈ absorbingBox p → calibratedPoint p ≤ z →
            z ≤ weightedSaddlePoint weighted →
            dist z (calibratedPoint p) ≤ 2 * epsilon →
            ∀ {sigma : ℝ}, sigma ≠ 0 →
              nearCrossingExcursionEvent
                  weighted z sigma (2 * epsilon) margin ⊆
                gaussianPrefixActionTailEvent H
                  ((civicCrossingQuasipotential weighted - delta) /
                    sigma ^ 2)) ∧
          ∀ z : LoopState,
            z ∈ absorbingBox p → calibratedPoint p ≤ z →
            z ≤ weightedSaddlePoint weighted →
            dist z (calibratedPoint p) ≤ 2 * epsilon →
            ∀ {sigma t : ℝ}, sigma ≠ 0 → 0 ≤ t → t < 1 →
              standardGaussianSequence
                  (nearCrossingExcursionEvent
                    weighted z sigma (2 * epsilon) margin) ≤
                ENNReal.ofReal
                  (Real.exp (-t *
                      ((civicCrossingQuasipotential weighted - delta) /
                        sigma ^ 2)) *
                    mgf gaussianVectorAction
                      (standardGaussianVector H) t) := by
  let V : ℝ := civicCrossingQuasipotential weighted
  have hV0 : 0 ≤ V := civicCrossingQuasipotential_nonneg model weighted
  let R : ℝ := 2 * V + 1
  have hR : 0 < R := by dsimp only [R]; linarith
  let q : ℝ := min 1
    (min (delta / (16 * (R + 1)))
      (weighted.βdagger / (4 * p.α)))
  have hdenDelta : 0 < 16 * (R + 1) := by positivity
  have hdenSaddle : 0 < 4 * p.α := mul_pos (by norm_num) model.α_pos
  have hq : 0 < q := by
    dsimp only [q]
    rw [lt_min_iff, lt_min_iff]
    exact ⟨one_pos, div_pos hdelta hdenDelta,
      div_pos weighted.βdagger_mem.1 hdenSaddle⟩
  have hqOne : q ≤ 1 := min_le_left _ _
  have hqDelta : q ≤ delta / (16 * (R + 1)) :=
    (min_le_right (1 : ℝ) _).trans (min_le_left _ _)
  have hqSaddle : q ≤ weighted.βdagger / (4 * p.α) :=
    (min_le_right (1 : ℝ) _).trans (min_le_right _ _)
  let margin : ℝ := p.α * q / 2
  have hmargin : 0 < margin := by
    dsimp only [margin]
    exact div_pos (mul_pos model.α_pos hq) (by norm_num)
  have hmarginSaddle : 2 * margin < weighted.βdagger := by
    have hmul := mul_le_mul_of_nonneg_left hqSaddle model.α_pos.le
    have hquarter : p.α * (weighted.βdagger / (4 * p.α)) =
        weighted.βdagger / 4 := by
      field_simp [model.α_pos.ne']
    dsimp only [margin]
    rw [div_eq_mul_inv]
    norm_num
    rw [hquarter] at hmul
    linarith [weighted.βdagger_mem.1]
  have hboostEq : nearCrossingBoostError p V margin =
      R * q + q ^ 2 / 2 := by
    simp only [nearCrossingBoostError, V, R, margin]
    field_simp [model.α_pos.ne']
  have hqSq : q ^ 2 ≤ q := by nlinarith
  have hRq : (R + 1) * q ≤ delta / 16 := by
    calc
      (R + 1) * q ≤
          (R + 1) * (delta / (16 * (R + 1))) :=
        mul_le_mul_of_nonneg_left hqDelta (by linarith)
      _ = delta / 16 := by
        field_simp [show R + 1 ≠ 0 by linarith]
  have hboostBound : nearCrossingBoostError p V margin ≤ delta / 16 := by
    rw [hboostEq]
    nlinarith
  let boost : ℝ := nearCrossingBoostError p V margin
  have hboost0 : 0 ≤ boost := by
    dsimp only [boost]
    rw [hboostEq]
    positivity
  let F : ℝ := policyMatchingActionConstant p rho *
    (1 + √(2 * (V + boost)))
  have hF : 0 ≤ F := by
    dsimp only [F]
    exact mul_nonneg (policyMatchingActionConstant_nonneg model rho)
      (add_nonneg zero_le_one (Real.sqrt_nonneg _))
  have hrootMargin : 0 < weighted.βdagger - margin := by
    linarith
  let e : ℝ := min (1 / 2 : ℝ)
    (min ((weighted.βdagger - margin) / 2)
      (delta / (16 * (F + 1))))
  have he : 0 < e := by
    dsimp only [e]
    rw [lt_min_iff, lt_min_iff]
    exact ⟨by norm_num, div_pos hrootMargin (by norm_num),
      div_pos hdelta (by positivity)⟩
  have heOne : e ≤ 1 :=
    (min_le_left _ _).trans (by norm_num)
  have heStrip : e < weighted.βdagger - margin := by
    have heHalf : e ≤ (weighted.βdagger - margin) / 2 :=
      (min_le_right (1 / 2 : ℝ) _).trans (min_le_left _ _)
    linarith
  have heDelta : e ≤ delta / (16 * (F + 1)) :=
    (min_le_right (1 / 2 : ℝ) _).trans (min_le_right _ _)
  have hFe : F * e ≤ delta / 16 := by
    have hmul := mul_le_mul_of_nonneg_left heDelta (by linarith : 0 ≤ F + 1)
    have htotal : (F + 1) * e ≤ delta / 16 := by
      calc
        (F + 1) * e ≤ (F + 1) * (delta / (16 * (F + 1))) := hmul
        _ = delta / 16 := by
          field_simp [show F + 1 ≠ 0 by linarith]
    nlinarith [mul_nonneg hF he.le]
  let epsilon : ℝ := e / 2
  have hepsilon : 0 < epsilon := by dsimp only [epsilon]; positivity
  have htwoEpsilon : 2 * epsilon = e := by
    dsimp only [epsilon]
    ring
  have hbaseNear : V - delta ≤ V -
      (nearCrossingBoostError p V margin +
        policyMatchingActionConstant p rho * (2 * epsilon) *
          (1 + √(2 * (V + nearCrossingBoostError p V margin)))) := by
    have hmatchEq :
        policyMatchingActionConstant p rho * (2 * epsilon) *
            (1 + √(2 * (V + nearCrossingBoostError p V margin))) =
          F * e := by
      rw [htwoEpsilon]
      simp only [F, boost]
      ring
    rw [hmatchEq]
    have htotal : nearCrossingBoostError p V margin + F * e ≤ delta := by
      linarith
    linarith
  obtain ⟨H, hset⟩ :=
    exists_nearCrossingExcursionEvent_subset_fixed_actionTail
      model ss threshold hrho hcoop weighted hepsilon hmargin hV0 le_rfl
        (by simpa only [htwoEpsilon] using heOne)
        (by simpa only [htwoEpsilon] using heStrip)
        hmarginSaddle (by simpa only [V] using hbaseNear)
  refine ⟨epsilon, hepsilon, margin, hmargin, ?_, H, ?_, ?_⟩
  · simpa only [htwoEpsilon] using heStrip
  · intro z hz hlower hupper hzdistance sigma hsigma
    simpa only [V] using
      hset z hz hlower hupper hzdistance hsigma
  · intro z hz hlower hupper hzdistance sigma t hsigma ht0 ht1
    have hsubset := hset z hz hlower hupper hzdistance hsigma
    calc
      standardGaussianSequence
          (nearCrossingExcursionEvent
            weighted z sigma (2 * epsilon) margin) ≤
          standardGaussianSequence
            (gaussianPrefixActionTailEvent H
              ((V - delta) / sigma ^ 2)) := measure_mono hsubset
      _ = gaussianActionTailProbability H ((V - delta) / sigma ^ 2) :=
        standardGaussianSequence_gaussianPrefixActionTailEvent _ _
      _ ≤ ENNReal.ofReal
            (Real.exp (-t * ((V - delta) / sigma ^ 2)) *
              mgf gaussianVectorAction (standardGaussianVector H) t) := by
        simpa only [mgf_gaussianVectorAction_eq_pow] using
          (gaussianActionTailProbability_le_chernoff
            H (B := (V - delta) / sigma ^ 2) ht0 ht1)

/-! ## Last-exit restart on the canonical process -/

/-- Restarting the canonical noisy orbit at deterministic time `M` and
feeding it the shifted Gaussian history reproduces the original orbit. -/
theorem gaussianNoisyOrbitFrom_tail_eq
    (p : LoopParams) (rho sigma : ℝ) (xi : GaussianNoisePath)
    (M n : ℕ) :
    gaussianNoisyOrbitFrom p rho
        (gaussianNoisyOrbit p rho sigma xi M) sigma (gaussianTail M xi) n =
      gaussianNoisyOrbit p rho sigma xi (M + n) := by
  induction n with
  | zero =>
      simp only [gaussianNoisyOrbitFrom, controlledCivicWeightedOrbitFrom,
        Nat.add_zero]
  | succ n ih =>
      rw [show M + (n + 1) = (M + n) + 1 by omega]
      simp only [gaussianNoisyOrbitFrom, controlledCivicWeightedOrbitFrom,
        gaussianNoisyOrbit, gaussianTail]
      congr 1

/-- At deterministic time `M`, the path is at an admissible last-exit state
and its shifted future completes a near-crossing excursion. -/
def lastExitNearCrossingEvent
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (sigma epsilon margin : ℝ) (M : ℕ) : Set GaussianNoisePath :=
  {xi |
    let z := gaussianNoisyOrbit p rho sigma xi M
    z ∈ absorbingBox p ∧ calibratedPoint p ≤ z ∧
      z ≤ weightedSaddlePoint weighted ∧
      dist z (calibratedPoint p) ≤ 2 * epsilon ∧
      gaussianTail M xi ∈
        nearCrossingExcursionEvent
          weighted z sigma (2 * epsilon) margin}

/-- A uniform arbitrary-start excursion inclusion transfers pathwise to
every deterministic last-exit time. -/
theorem lastExitNearCrossingEvent_subset_tail_actionTail
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    {sigma epsilon margin base : ℝ} {H : ℕ}
    (hset : ∀ z : LoopState,
      z ∈ absorbingBox p → calibratedPoint p ≤ z →
      z ≤ weightedSaddlePoint weighted →
      dist z (calibratedPoint p) ≤ 2 * epsilon →
      nearCrossingExcursionEvent
          weighted z sigma (2 * epsilon) margin ⊆
        gaussianPrefixActionTailEvent H (base / sigma ^ 2))
    (M : ℕ) :
    lastExitNearCrossingEvent weighted sigma epsilon margin M ⊆
      gaussianTail M ⁻¹'
        gaussianPrefixActionTailEvent H (base / sigma ^ 2) := by
  intro xi hxi
  rcases hxi with ⟨hz, hlower, hupper, hdist, hexcursion⟩
  exact hset _ hz hlower hupper hdist hexcursion

/-- Every deterministic last-exit event has the same fixed-dimensional
Chernoff bound, independently of its location in the global history. -/
theorem lastExitNearCrossingEvent_probability_le_chernoff
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    {sigma epsilon margin base t : ℝ} {H : ℕ}
    (hset : ∀ z : LoopState,
      z ∈ absorbingBox p → calibratedPoint p ≤ z →
      z ≤ weightedSaddlePoint weighted →
      dist z (calibratedPoint p) ≤ 2 * epsilon →
      nearCrossingExcursionEvent
          weighted z sigma (2 * epsilon) margin ⊆
        gaussianPrefixActionTailEvent H (base / sigma ^ 2))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (M : ℕ) :
    standardGaussianSequence
        (lastExitNearCrossingEvent weighted sigma epsilon margin M) ≤
      ENNReal.ofReal
        (Real.exp (-t * (base / sigma ^ 2)) *
          mgf gaussianVectorAction (standardGaussianVector H) t) := by
  calc
    standardGaussianSequence
        (lastExitNearCrossingEvent weighted sigma epsilon margin M) ≤
        standardGaussianSequence
          (gaussianTail M ⁻¹'
            gaussianPrefixActionTailEvent H (base / sigma ^ 2)) :=
      measure_mono
        (lastExitNearCrossingEvent_subset_tail_actionTail
          weighted hset M)
    _ = standardGaussianSequence
          (gaussianPrefixActionTailEvent H (base / sigma ^ 2)) :=
      standardGaussianSequence_tail_preimage M
        (measurableSet_gaussianPrefixActionTailEvent H (base / sigma ^ 2))
    _ = gaussianActionTailProbability H (base / sigma ^ 2) :=
      standardGaussianSequence_gaussianPrefixActionTailEvent _ _
    _ ≤ ENNReal.ofReal
          (Real.exp (-t * (base / sigma ^ 2)) *
            mgf gaussianVectorAction (standardGaussianVector H) t) := by
      simpa only [mgf_gaussianVectorAction_eq_pow] using
        (gaussianActionTailProbability_le_chernoff
          H (B := base / sigma ^ 2) ht0 ht1)

/-- The last-exit combinatorics.  Any global crossing by time `N` has a
first entrance into the near-saddle strip.  The last visit to the closed home
ball before that entrance starts one of the deterministic-time excursion
events above. -/
theorem gaussianEscapeByEvent_subset_lastExitNearCrossing
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho sigma epsilon margin : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    (hepsilonStrip : 2 * epsilon < weighted.βdagger - margin)
    (hepsilon : 0 ≤ epsilon) (hmargin : 0 ≤ margin) (N : ℕ) :
    gaussianEscapeByEvent weighted N sigma ⊆
      ⋃ M ∈ Finset.range (N + 1),
        lastExitNearCrossingEvent weighted sigma epsilon margin M := by
  intro xi hescape
  let x : ℕ → LoopState := gaussianNoisyOrbit p rho sigma xi
  have path := gaussianNoisyOrbit_isControlled p rho sigma xi
  obtain ⟨n, hnN, hnCross⟩ :=
    (le_runningMax_iff (a := fun k ↦ (x k).1)).1 hescape
  have hn1 : 1 ≤ n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp only [x, gaussianNoisyOrbit, calibratedPoint] at hnCross
    linarith [weighted.βdagger_mem.1]
  let target : ℕ → Prop := fun k ↦
    1 ≤ k ∧ weighted.βdagger - margin ≤ (x k).1
  have hex : ∃ k, target k := by
    exact ⟨n, hn1, (sub_le_self _ hmargin).trans hnCross⟩
  let first : ℕ := Nat.find hex
  have hfirst : 1 ≤ first ∧
      weighted.βdagger - margin ≤ (x first).1 := by
    simpa only [first, target] using Nat.find_spec hex
  have hfirstN : first ≤ N :=
    (Nat.find_min' hex ⟨hn1,
      (sub_le_self _ hmargin).trans hnCross⟩).trans hnN
  let home : ℕ → Prop := fun k ↦
    dist (x k) (calibratedPoint p) ≤ 2 * epsilon
  have hhome0 : home 0 := by
    dsimp only [home, x]
    simp only [gaussianNoisyOrbit, dist_self]
    linarith
  let last : ℕ := Nat.findGreatest home first
  have hlastHome : home last :=
    Nat.findGreatest_spec (Nat.zero_le first) hhome0
  have hlastLe : last ≤ first := Nat.findGreatest_le _
  have hfirstNotHome : ¬home first := by
    intro hhomeFirst
    dsimp only [home] at hhomeFirst
    have hfirstBox : x first ∈ absorbingBox p := path.mem_absorbingBox model first
    have hpolicyDist : (x first).1 ≤
        dist (x first) (calibratedPoint p) := by
      have h := le_max_left (dist (x first).1 (calibratedPoint p).1)
        (dist (x first).2 (calibratedPoint p).2)
      rw [← Prod.dist_eq] at h
      have habs : |(x first).1| ≤
          dist (x first) (calibratedPoint p) := by
        simpa only [calibratedPoint, Real.dist_eq, sub_zero] using h
      exact (le_abs_self _).trans habs
    linarith
  have hlastFirst : last < first :=
    hlastLe.lt_of_ne (fun h ↦ hfirstNotHome (h ▸ hlastHome))
  have hlastN : last ∈ Finset.range (N + 1) := by
    simp only [Finset.mem_range]
    omega
  apply Set.mem_iUnion.2
  refine ⟨last, Set.mem_iUnion.2 ⟨hlastN, ?_⟩⟩
  have hmaxLast : policyRunningMax x last ≤ weighted.βdagger := by
    apply runningMax_le_of_forall_le
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      simp only [x, gaussianNoisyOrbit, calibratedPoint]
      exact weighted.βdagger_mem.1.le
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hkFirst : k < first := hk.trans_lt hlastFirst
      have hnot := Nat.find_min hex hkFirst
      change ¬target k at hnot
      have hlt : (x k).1 < weighted.βdagger - margin :=
        lt_of_not_ge (fun h ↦ hnot ⟨hk1, h⟩)
      exact hlt.le.trans (sub_le_self _ hmargin)
  have horder := path.mem_weightedSaddleOrderInterval
    model ss weighted hmaxLast
  have hduration : 1 ≤ first - last := by omega
  have hrestart : gaussianTail last xi ∈
      nearCrossingExcursionEvent weighted (x last) sigma
        (2 * epsilon) margin := by
    rw [mem_nearCrossingExcursionEvent_iff]
    refine ⟨first - last, hduration, ?_, ?_⟩
    · have heq := gaussianNoisyOrbitFrom_tail_eq
        p rho sigma xi last (first - last)
      rw [Nat.add_sub_of_le hlastLe] at heq
      rw [heq]
      exact hfirst.2
    · intro r hr
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
      have hrLe : r ≤ first - last := (Finset.mem_Icc.mp hr).2
      have hlastLt : last < last + r := by omega
      have haddLe : last + r ≤ first := by omega
      have hnotHome : ¬home (last + r) :=
        Nat.findGreatest_is_greatest hlastLt haddLe
      have heq := gaussianNoisyOrbitFrom_tail_eq p rho sigma xi last r
      rw [heq]
      exact lt_of_not_ge hnotHome
  exact ⟨horder.1, horder.2.1, horder.2.2,
    hlastHome, hrestart⟩

/-- A uniform first-entrance action bound prices every crossing by time `N`.
The only horizon cost is the union-bound factor `N + 1`; the action tail
itself has the fixed dimension supplied by the local excursion theorem. -/
theorem gaussianEscapeProbability_le_lastExit_chernoff
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho sigma epsilon margin base t : ℝ}
    (weighted : WeightedThresholdAssumption p rho) {H : ℕ}
    (hepsilonStrip : 2 * epsilon < weighted.βdagger - margin)
    (hepsilon : 0 ≤ epsilon) (hmargin : 0 ≤ margin)
    (hset : ∀ z : LoopState,
      z ∈ absorbingBox p → calibratedPoint p ≤ z →
      z ≤ weightedSaddlePoint weighted →
      dist z (calibratedPoint p) ≤ 2 * epsilon →
      nearCrossingExcursionEvent
          weighted z sigma (2 * epsilon) margin ⊆
        gaussianPrefixActionTailEvent H (base / sigma ^ 2))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (N : ℕ) :
    gaussianEscapeProbability weighted N sigma ≤
      (N + 1 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-t * (base / sigma ^ 2)) *
            mgf gaussianVectorAction (standardGaussianVector H) t) := by
  rw [← standardGaussianSequence_escapeByEvent weighted N sigma]
  calc
    standardGaussianSequence (gaussianEscapeByEvent weighted N sigma) ≤
        standardGaussianSequence
          (⋃ M ∈ Finset.range (N + 1),
            lastExitNearCrossingEvent weighted sigma epsilon margin M) :=
      measure_mono
        (gaussianEscapeByEvent_subset_lastExitNearCrossing
          model ss weighted hepsilonStrip hepsilon hmargin N)
    _ ≤ ∑ M ∈ Finset.range (N + 1),
          standardGaussianSequence
            (lastExitNearCrossingEvent
              weighted sigma epsilon margin M) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _M ∈ Finset.range (N + 1),
          ENNReal.ofReal
            (Real.exp (-t * (base / sigma ^ 2)) *
              mgf gaussianVectorAction (standardGaussianVector H) t) := by
      exact Finset.sum_le_sum fun M _ ↦
        lastExitNearCrossingEvent_probability_le_chernoff
          weighted hset ht0 ht1 M
    _ = (N + 1 : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp (-t * (base / sigma ^ 2)) *
              mgf gaussianVectorAction (standardGaussianVector H) t) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      norm_cast

/-- A positive activated horizon, including the union-bound endpoint, is at
most twice its defining real exponential. -/
theorem exponentialEscapeHorizon_add_one_le
    {rate sigma : ℝ} (hrate : 0 ≤ rate) :
    (exponentialEscapeHorizon rate sigma : ℝ≥0∞) + 1 ≤
      ENNReal.ofReal (2 * Real.exp (rate / sigma ^ 2)) := by
  have hexpOne : 1 ≤ Real.exp (rate / sigma ^ 2) := by
    exact Real.one_le_exp (div_nonneg hrate (sq_nonneg sigma))
  have hfloor : (exponentialEscapeHorizon rate sigma : ℝ) ≤
      Real.exp (rate / sigma ^ 2) := by
    simpa only [exponentialEscapeHorizon] using
      Nat.floor_le (Real.exp_pos _).le
  have hreal : (exponentialEscapeHorizon rate sigma : ℝ) + 1 ≤
      2 * Real.exp (rate / sigma ^ 2) := by
    linarith
  have henn :
      ((exponentialEscapeHorizon rate sigma + 1 : ℕ) : ℝ≥0∞) ≤
        ENNReal.ofReal (2 * Real.exp (rate / sigma ^ 2)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by
      simpa only [Nat.cast_add, Nat.cast_one] using hreal)
  simpa only [Nat.cast_add, Nat.cast_one] using henn

/-- The discrete exponential horizon is monotone in its requested rate. -/
theorem monotone_exponentialEscapeHorizon (sigma : ℝ) :
    Monotone fun rate : ℝ ↦ exponentialEscapeHorizon rate sigma := by
  intro a b hab
  unfold exponentialEscapeHorizon
  apply Nat.floor_mono
  apply Real.exp_le_exp.mpr
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hab (inv_nonneg.mpr (sq_nonneg sigma))

/-- Whenever the exponential horizon rate is strictly below a Chernoff
fraction of the uniform first-entrance action, the crossing probability
tends to zero.  This is the quantitative persistence engine for the lower
Arrhenius bound. -/
theorem exponentialEscapeProbability_tendsto_zero_of_rate_lt
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho delta rate t : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hdelta : 0 < delta) (hrate : 0 < rate)
    (ht0 : 0 < t) (ht1 : t < 1)
    (hgap : rate < t *
      (civicCrossingQuasipotential weighted - delta)) :
    Tendsto
      (fun sigma : ℝ ↦ gaussianEscapeProbability weighted
        (exponentialEscapeHorizon rate sigma) sigma)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
  obtain ⟨epsilon, hepsilon, margin, hmargin, hepsilonStrip,
      H, hset, _hprobability⟩ :=
    exists_uniform_nearCrossingExcursionProbability_le
      model ss threshold hrho hcoop weighted hdelta
  let base : ℝ := civicCrossingQuasipotential weighted - delta
  let gap : ℝ := t * base - rate
  have hgapPos : 0 < gap := by
    dsimp only [gap, base]
    linarith
  have hmgf : 0 ≤
      mgf gaussianVectorAction (standardGaussianVector H) t := by
    rw [mgf_gaussianVectorAction_eq_pow]
    exact pow_nonneg (gaussianHalfSquareMgf_pos ht1).le H
  let majorant : ℝ → ℝ≥0∞ := fun sigma ↦
    ENNReal.ofReal
      (2 * mgf gaussianVectorAction (standardGaussianVector H) t *
        Real.exp (-gap / sigma ^ 2))
  have hbound : ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      gaussianEscapeProbability weighted
          (exponentialEscapeHorizon rate sigma) sigma ≤ majorant sigma := by
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    have hsigmaNe : sigma ≠ 0 := ne_of_gt hsigma
    have hlocal : ∀ z : LoopState,
        z ∈ absorbingBox p → calibratedPoint p ≤ z →
        z ≤ weightedSaddlePoint weighted →
        dist z (calibratedPoint p) ≤ 2 * epsilon →
        nearCrossingExcursionEvent
            weighted z sigma (2 * epsilon) margin ⊆
          gaussianPrefixActionTailEvent H (base / sigma ^ 2) := by
      intro z hz hlower hupper hdist
      simpa only [base] using hset z hz hlower hupper hdist hsigmaNe
    have hglobal := gaussianEscapeProbability_le_lastExit_chernoff
      model ss weighted hepsilonStrip hepsilon.le hmargin.le hlocal
        ht0.le ht1 (exponentialEscapeHorizon rate sigma)
    have hhorizon := exponentialEscapeHorizon_add_one_le
      (sigma := sigma) hrate.le
    calc
      gaussianEscapeProbability weighted
          (exponentialEscapeHorizon rate sigma) sigma ≤
          (exponentialEscapeHorizon rate sigma + 1 : ℝ≥0∞) *
            ENNReal.ofReal
              (Real.exp (-t * (base / sigma ^ 2)) *
                mgf gaussianVectorAction
                  (standardGaussianVector H) t) := by
        simpa only [base] using hglobal
      _ ≤ ENNReal.ofReal (2 * Real.exp (rate / sigma ^ 2)) *
            ENNReal.ofReal
              (Real.exp (-t * (base / sigma ^ 2)) *
                mgf gaussianVectorAction
                  (standardGaussianVector H) t) :=
        mul_le_mul' hhorizon le_rfl
      _ = majorant sigma := by
        dsimp only [majorant]
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have hexp :
          Real.exp (rate / sigma ^ 2) *
              Real.exp (-t * (base / sigma ^ 2)) =
            Real.exp (-gap / sigma ^ 2) := by
          rw [← Real.exp_add]
          congr 1
          dsimp only [gap]
          ring
        calc
          2 * Real.exp (rate / sigma ^ 2) *
              (Real.exp (-t * (base / sigma ^ 2)) *
                mgf gaussianVectorAction (standardGaussianVector H) t) =
            2 * mgf gaussianVectorAction (standardGaussianVector H) t *
              (Real.exp (rate / sigma ^ 2) *
                Real.exp (-t * (base / sigma ^ 2))) := by ring
          _ = 2 * mgf gaussianVectorAction
                (standardGaussianVector H) t *
              Real.exp (-gap / sigma ^ 2) := by rw [hexp]
  have hactivated :=
    tendsto_exp_neg_const_div_sq_nhdsGT_zero hgapPos
  have hreal : Tendsto
      (fun sigma : ℝ ↦
        2 * mgf gaussianVectorAction (standardGaussianVector H) t *
          Real.exp (-gap / sigma ^ 2))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
    simpa using tendsto_const_nhds.mul hactivated
  have hmajorant : Tendsto majorant
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
    simpa only [majorant, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal hreal
  exact (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (0 : ℝ≥0∞))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0)).squeeze'
    hmajorant (Eventually.of_forall fun _ ↦ bot_le) hbound

/-- The corrected barrier is positive, so the crossing quasipotential is
strictly positive under the Lipschitz hypothesis used in the paper's
two-sided bracket. -/
theorem civicCrossingQuasipotential_pos_of_lipschitz
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho L : ℝ}
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    0 < civicCrossingQuasipotential weighted := by
  have hden : 0 < p.α * (1 + 2 * p.α * L) := by
    exact mul_pos model.α_pos (by
      have hL0 : 0 ≤ L := hL.nonneg
      have hterm : 0 ≤ 2 * p.α * L :=
        mul_nonneg (mul_nonneg (by norm_num) model.α_pos.le) hL0
      linarith)
  have hcoeff : 0 < 2 / (p.α * (1 + 2 * p.α * L)) :=
    div_pos (by norm_num) hden
  have harea : 0 <
      ∫ b in (0 : ℝ)..weighted.βdagger,
        weightedBarrierIntegrand p rho b := by
    simpa only [weightedBarrierArea] using
      weightedBarrierArea_pos model weighted
  exact (mul_pos hcoeff harea).trans_le
    (correctedBarrier_le_civicCrossingQuasipotential
      model ss hcoop weighted hL)

/-- Paper II, Theorem `thm:rate`, persistence clause: for every positive
tolerance, crossing by `exp((Vˣ - delta) / sigma²)` has probability tending
to zero.  A slightly larger positive auxiliary rate handles all `delta`,
including those for which the displayed rate itself is nonpositive. -/
theorem crossingLowerEscapeProbability
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho L delta : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger)
    (hdelta : 0 < delta) :
    Tendsto
      (fun sigma : ℝ ↦ gaussianEscapeProbability weighted
        (exponentialEscapeHorizon
          (civicCrossingQuasipotential weighted - delta) sigma) sigma)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
  let V : ℝ := civicCrossingQuasipotential weighted
  have hV : 0 < V := by
    simpa only [V] using civicCrossingQuasipotential_pos_of_lipschitz
      model ss hcoop weighted hL
  let d : ℝ := min (delta / 4) (V / 8)
  have hd : 0 < d := by
    dsimp only [d]
    exact lt_min (div_pos hdelta (by norm_num))
      (div_pos hV (by norm_num))
  have hdDelta : d ≤ delta / 4 := min_le_left _ _
  have hdV : d ≤ V / 8 := min_le_right _ _
  let base : ℝ := V - d
  let rate : ℝ := V - 2 * d
  have hrate : 0 < rate := by
    dsimp only [rate]
    linarith
  have hbase : 0 < base := by
    dsimp only [base]
    linarith
  have hrateBase : rate < base := by
    dsimp only [rate, base]
    linarith
  let t : ℝ := (rate / base + 1) / 2
  have ht0 : 0 < t := by
    dsimp only [t]
    have : 0 < rate / base := div_pos hrate hbase
    linarith
  have ht1 : t < 1 := by
    dsimp only [t]
    have : rate / base < 1 := (div_lt_one hbase).2 hrateBase
    linarith
  have hgap : rate < t * (V - d) := by
    have hbaseEq : V - d = base := rfl
    rw [hbaseEq]
    dsimp only [t]
    field_simp [hbase.ne']
    linarith
  have haux := exponentialEscapeProbability_tendsto_zero_of_rate_lt
    model ss threshold hrho hcoop weighted hd hrate ht0 ht1
      (by simpa only [V] using hgap)
  have htargetRate : V - delta ≤ rate := by
    dsimp only [rate]
    linarith
  have hpointwise : ∀ sigma : ℝ,
      gaussianEscapeProbability weighted
          (exponentialEscapeHorizon (V - delta) sigma) sigma ≤
        gaussianEscapeProbability weighted
          (exponentialEscapeHorizon rate sigma) sigma := by
    intro sigma
    exact monotone_gaussianEscapeProbability weighted sigma
      (monotone_exponentialEscapeHorizon sigma htargetRate)
  have hzero : Tendsto (fun _ : ℝ ↦ (0 : ℝ≥0∞))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := tendsto_const_nhds
  apply hzero.squeeze' haux (Eventually.of_forall fun _ ↦ bot_le)
  filter_upwards with sigma
  simpa only [V] using hpointwise sigma

/-- A positive discrete exponential horizon eventually retains at least half
of its defining real exponential. -/
theorem eventually_half_exp_le_exponentialEscapeHorizon
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      ENNReal.ofReal (Real.exp (rate / sigma ^ 2) / 2) ≤
        (exponentialEscapeHorizon rate sigma : ℝ≥0∞) := by
  have hdiverge := tendsto_exp_const_div_sq_atTop_nhdsGT_zero hrate
  have htwo : ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      2 ≤ Real.exp (rate / sigma ^ 2) :=
    (tendsto_atTop.1 hdiverge) 2
  filter_upwards [htwo] with sigma hsigma
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (by
    simpa only [exponentialEscapeHorizon] using
      half_le_natFloor_of_two_le hsigma)

/-- Persistence at a positive exponential horizon forces the logarithmic
mean first-crossing time to have liminf at least that horizon rate. -/
theorem meanGaussianEscapeLogRate_liminf_ge_of_persistence
    {p : LoopParams} {rho rate : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    (hrate : 0 < rate)
    (hpersistence : Tendsto
      (fun sigma : ℝ ↦ gaussianEscapeProbability weighted
        (exponentialEscapeHorizon rate sigma) sigma)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0)) :
    ((rate : ℝ) : EReal) ≤
      liminf (meanGaussianEscapeLogRate weighted)
        (nhdsWithin 0 (Ioi (0 : ℝ))) := by
  have hprobHalf : ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      gaussianEscapeProbability weighted
          (exponentialEscapeHorizon rate sigma) sigma <
        (1 / 2 : ℝ≥0∞) :=
    (tendsto_order.1 hpersistence).2 _ (by norm_num)
  have hhorizon := eventually_half_exp_le_exponentialEscapeHorizon hrate
  have hpointwise : ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi (0 : ℝ)),
      ((rate - sigma ^ 2 * Real.log 4 : ℝ) : EReal) ≤
        meanGaussianEscapeLogRate weighted sigma := by
    filter_upwards [self_mem_nhdsWithin, hprobHalf, hhorizon] with
        sigma hsigma hprob hhorizonSigma
    let H : ℕ := exponentialEscapeHorizon rate sigma
    let probability : ℝ≥0∞ :=
      gaussianEscapeProbability weighted H sigma
    letI : IsProbabilityMeasure (standardGaussianVector H) := by
      unfold standardGaussianVector
      infer_instance
    have hprobTop : probability ≠ ∞ := by
      dsimp only [probability, gaussianEscapeProbability]
      exact measure_ne_top _ _
    have hprob' : probability < (1 / 2 : ℝ≥0∞) := by
      simpa only [probability, H] using hprob
    have hsurvival : (1 / 2 : ℝ≥0∞) ≤ 1 - probability := by
      apply ENNReal.le_sub_of_add_le_left hprobTop
      calc
        probability + (1 / 2 : ℝ≥0∞) ≤
            (1 / 2 : ℝ≥0∞) + (1 / 2 : ℝ≥0∞) :=
          by simpa only [add_comm] using
            add_le_add_right hprob'.le (1 / 2 : ℝ≥0∞)
        _ = 1 := by
          simpa only [one_div] using ENNReal.add_halves (1 : ℝ≥0∞)
    have hbridge := horizon_mul_survival_le_meanGaussianEscapeTime
      weighted H sigma
    have hproduct :
        ENNReal.ofReal (Real.exp (rate / sigma ^ 2) / 2) *
            (1 / 2 : ℝ≥0∞) ≤
          meanGaussianEscapeTime weighted sigma := by
      exact (mul_le_mul' hhorizonSigma hsurvival).trans hbridge
    have hquarter :
        ENNReal.ofReal (Real.exp (rate / sigma ^ 2) / 4) =
          ENNReal.ofReal (Real.exp (rate / sigma ^ 2) / 2) *
            (1 / 2 : ℝ≥0∞) := by
      rw [show (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
          norm_num,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    have hmeanLower :
        ENNReal.ofReal (Real.exp (rate / sigma ^ 2) / 4) ≤
          meanGaussianEscapeTime weighted sigma := by
      rw [hquarter]
      exact hproduct
    have hlog := ENNReal.logOrderIso.monotone hmeanLower
    change ENNReal.log
        (ENNReal.ofReal (Real.exp (rate / sigma ^ 2) / 4)) ≤
      ENNReal.log (meanGaussianEscapeTime weighted sigma) at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog
      (show (0 : EReal) ≤ (sigma ^ 2 : ℝ) by
        exact_mod_cast sq_nonneg sigma)
    have hsigmaSq : sigma ^ 2 ≠ 0 := (sq_pos_of_pos hsigma).ne'
    have hlogLower :
        ENNReal.log
            (ENNReal.ofReal (Real.exp (rate / sigma ^ 2) / 4)) =
          ((rate / sigma ^ 2 - Real.log 4 : ℝ) : EReal) := by
      rw [ENNReal.log_ofReal_of_pos (div_pos (Real.exp_pos _) (by norm_num))]
      norm_cast
      rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp]
    rw [hlogLower] at hmul
    have hexplicit :
        ((rate - sigma ^ 2 * Real.log 4 : ℝ) : EReal) =
          (sigma ^ 2 : ℝ) *
            ((rate / sigma ^ 2 - Real.log 4 : ℝ) : EReal) := by
      norm_cast
      calc
        rate - sigma ^ 2 * Real.log 4 =
            (rate / sigma ^ 2) * sigma ^ 2 -
              sigma ^ 2 * Real.log 4 := by
          rw [div_mul_cancel₀ rate hsigmaSq]
        _ = sigma ^ 2 * (rate / sigma ^ 2 - Real.log 4) := by ring
    rw [hexplicit]
    simpa only [meanGaussianEscapeLogRate] using hmul
  have hreal : Tendsto
      (fun sigma : ℝ ↦ rate - sigma ^ 2 * Real.log 4)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds rate) := by
    have hcont : ContinuousAt
        (fun sigma : ℝ ↦ rate - sigma ^ 2 * Real.log 4) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hereal : Tendsto
      (fun sigma : ℝ ↦
        ((rate - sigma ^ 2 * Real.log 4 : ℝ) : EReal))
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds ((rate : ℝ) : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hreal
  exact hereal.liminf_eq.symm.le.trans (liminf_le_liminf hpointwise)

/-- Paper II, Theorem `thm:rate`, mean-time lower clause: the logarithmic
mean crossing time has liminf at least the crossing quasipotential. -/
theorem crossingLowerMeanRate
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho L : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    ((civicCrossingQuasipotential weighted : ℝ) : EReal) ≤
      liminf (meanGaussianEscapeLogRate weighted)
        (nhdsWithin 0 (Ioi (0 : ℝ))) := by
  let V : ℝ := civicCrossingQuasipotential weighted
  let R : EReal := liminf (meanGaussianEscapeLogRate weighted)
    (nhdsWithin 0 (Ioi (0 : ℝ)))
  have hV : 0 < V := by
    simpa only [V] using civicCrossingQuasipotential_pos_of_lipschitz
      model ss hcoop weighted hL
  let delta : ℕ → ℝ := fun n ↦ V / (n + 1 : ℝ)
  let rate : ℕ → ℝ := fun n ↦ V - delta n
  have hdelta : ∀ n, 0 < delta n := by
    intro n
    dsimp only [delta]
    positivity
  have hrate : ∀ n, 1 ≤ n → 0 < rate n := by
    intro n hn
    have hden : 2 ≤ (n + 1 : ℝ) := by exact_mod_cast (show 2 ≤ n + 1 by omega)
    have hfrac : delta n ≤ V / 2 := by
      dsimp only [delta]
      exact div_le_div_of_nonneg_left hV.le (by norm_num) hden
    dsimp only [rate]
    linarith
  have hparameter : ∀ᶠ n : ℕ in atTop,
      ((rate n : ℝ) : EReal) ≤ R := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hpersistence := crossingLowerEscapeProbability
      model ss threshold hrho hcoop weighted hL (hdelta n)
    have hlower := meanGaussianEscapeLogRate_liminf_ge_of_persistence
      weighted (hrate n hn) hpersistence
    simpa only [R] using hlower
  have hinv : Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ))
      atTop (nhds (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hdeltaLimit : Tendsto delta atTop (nhds (0 : ℝ)) := by
    have hmul : Tendsto (fun n : ℕ ↦ V * (1 / (n + 1 : ℝ)))
        atTop (nhds (0 : ℝ)) := by
      simpa using tendsto_const_nhds.mul hinv
    apply hmul.congr'
    filter_upwards with n
    dsimp only [delta]
    ring
  have hrateLimit : Tendsto rate atTop (nhds V) := by
    simpa only [rate, sub_zero] using tendsto_const_nhds.sub hdeltaLimit
  have hereal : Tendsto (fun n ↦ ((rate n : ℝ) : EReal))
      atTop (nhds ((V : ℝ) : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hrateLimit
  have hclosed : ((V : ℝ) : EReal) ∈ Iic R :=
    isClosed_Iic.mem_of_tendsto hereal hparameter
  simpa only [V, R, mem_Iic] using hclosed

/-- Combining the persistence lower bound with the constructive restart
upper bound identifies the exact logarithmic mean crossing-time rate. -/
theorem crossingMeanRate
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) (threshold : ThresholdAssumption p)
    {rho L : ℝ} (hrho : 0 ≤ rho)
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho)
    (hL : IsLipschitzConstantOn (weightedBarrierIntegrand p rho) L
      0 weighted.βdagger) :
    Tendsto (meanGaussianEscapeLogRate weighted)
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds ((civicCrossingQuasipotential weighted : ℝ) : EReal)) := by
  exact tendsto_of_le_liminf_of_limsup_le
    (crossingLowerMeanRate model ss threshold hrho hcoop weighted hL)
    (crossingUpperMeanRate model ss threshold hrho hcoop weighted)

/-! ## Deterministic-time saddle restart -/

/-- Scaling commutes with concatenation, and the arbitrary-start recursion
restarts exactly at the split time. -/
theorem finiteControlledOrbitFrom_scaled_append_right
    (p : LoopParams) (rho sigma : ℝ) (x₀ : LoopState)
    {M T : ℕ} (pref : Fin M → ℝ) (suffix : Fin T → ℝ)
    {k : ℕ} (hk : k ≤ T) :
    finiteControlledOrbitFrom p rho x₀
        (scaledGaussianControl sigma (Fin.append pref suffix)) (M + k) =
      finiteControlledOrbitFrom p rho
        (finiteControlledOrbitFrom p rho x₀
          (scaledGaussianControl sigma pref) M)
        (scaledGaussianControl sigma suffix) k := by
  rw [scaledGaussianControl_append]
  exact finiteControlledOrbitFrom_append_right p rho x₀
    (scaledGaussianControl sigma pref)
    (scaledGaussianControl sigma suffix) hk

/-- After a prefix of length `M`, the suffix keeps the path in the weighted
saddle ball for `N+1` consecutive states. -/
def saddleSojournRestartEvent
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (x₀ : LoopState) (M : ℕ) (sigma radius : ℝ) (N : ℕ) :
    Set ((Fin M → ℝ) × (Fin (1 + N) → ℝ)) :=
  ⋂ n ∈ Finset.range (N + 1),
    {w | dist
      (finiteControlledOrbitFrom p rho x₀
        (scaledGaussianControl sigma (Fin.append w.1 w.2))
        (M + (1 + n)))
      (weightedSaddlePoint weighted) < radius}

/-- The deterministic-time restart event is Borel measurable. -/
theorem measurableSet_saddleSojournRestartEvent
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (x₀ : LoopState) (M : ℕ) (sigma radius : ℝ) (N : ℕ) :
    MeasurableSet
      (saddleSojournRestartEvent weighted x₀ M sigma radius N) := by
  unfold saddleSojournRestartEvent
  refine Finset.measurableSet_biInter (Finset.range (N + 1)) fun n _hn ↦ ?_
  have happend : Continuous (fun w : (Fin M → ℝ) × (Fin (1 + N) → ℝ) ↦
      Fin.append w.1 w.2) := Fin.continuous_append M (1 + N)
  have hscaled : Continuous
      (fun w : (Fin M → ℝ) × (Fin (1 + N) → ℝ) ↦
        scaledGaussianControl sigma (Fin.append w.1 w.2)) := by
    unfold scaledGaussianControl
    fun_prop
  have hinput : Continuous
      (fun w : (Fin M → ℝ) × (Fin (1 + N) → ℝ) ↦
        (x₀, scaledGaussianControl sigma (Fin.append w.1 w.2))) :=
    continuous_const.prodMk hscaled
  have horbit : Continuous
      (fun w : (Fin M → ℝ) × (Fin (1 + N) → ℝ) ↦
        finiteControlledOrbitFrom p rho x₀
          (scaledGaussianControl sigma (Fin.append w.1 w.2))
          (M + (1 + n))) :=
    (continuous_finiteControlledOrbitFrom p rho
      (T := M + (1 + N)) (M + (1 + n))).comp hinput
  change MeasurableSet
    ((fun w : (Fin M → ℝ) × (Fin (1 + N) → ℝ) ↦
      finiteControlledOrbitFrom p rho x₀
        (scaledGaussianControl sigma (Fin.append w.1 w.2))
        (M + (1 + n))) ⁻¹'
      Metric.ball (weightedSaddlePoint weighted) radius)
  exact Metric.isOpen_ball.measurableSet.preimage horbit.measurable

/-- Conditioning on a prefix turns the restart fiber into exactly the
ordinary finite-vector saddle-sojourn event from the prefix endpoint. -/
theorem saddleSojournRestartEvent_fiber
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (x₀ : LoopState) (M : ℕ) (sigma radius : ℝ) (N : ℕ)
    (pref : Fin M → ℝ) :
    Prod.mk pref ⁻¹'
        saddleSojournRestartEvent weighted x₀ M sigma radius N =
      saddleSojournFiniteEvent weighted
        (finiteControlledOrbitFrom p rho x₀
          (scaledGaussianControl sigma pref) M)
        sigma radius N := by
  ext suffix
  simp only [Set.mem_preimage, saddleSojournRestartEvent,
    Set.mem_iInter, Set.mem_setOf_eq, Finset.mem_range]
  rw [mem_saddleSojournFiniteEvent_iff]
  constructor
  · intro h n hn
    rw [← finiteControlledOrbitFrom_scaled_append_right
      p rho sigma x₀ pref suffix (by omega : 1 + n ≤ 1 + N)]
    exact h n (by omega)
  · intro h n hn
    rw [finiteControlledOrbitFrom_scaled_append_right
      p rho sigma x₀ pref suffix (by omega : 1 + n ≤ 1 + N)]
    exact h n (by omega)

/-- A uniform finite-vector saddle estimate remains valid after conditioning
on any Gaussian prefix: the random prefix endpoint stays in the absorbing
box, and the suffix law is fresh. -/
theorem saddleSojournRestartEvent_probability_le
    {p : LoopParams} (model : DriftModelAssumptions p) {rho : ℝ}
    (weighted : WeightedThresholdAssumption p rho)
    {mu radius C : ℝ}
    (hfinite : ∀ (z : LoopState), z ∈ absorbingBox p →
      ∀ sigma : ℝ, 0 < sigma → ∀ N : ℕ,
        standardGaussianVector (1 + N)
            (saddleSojournFiniteEvent weighted z sigma radius N) ≤
          ENNReal.ofReal (2 * (C / (sigma * mu ^ N))))
    {x₀ : LoopState} (hx₀ : x₀ ∈ absorbingBox p)
    (M : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) (N : ℕ) :
    (standardGaussianVector M).prod (standardGaussianVector (1 + N))
        (saddleSojournRestartEvent weighted x₀ M sigma radius N) ≤
      ENNReal.ofReal (2 * (C / (sigma * mu ^ N))) := by
  letI : IsProbabilityMeasure (standardGaussianVector M) := by
    unfold standardGaussianVector
    infer_instance
  letI : IsProbabilityMeasure (standardGaussianVector (1 + N)) := by
    unfold standardGaussianVector
    infer_instance
  rw [Measure.prod_apply
    (measurableSet_saddleSojournRestartEvent
      weighted x₀ M sigma radius N)]
  calc
    (∫⁻ pref,
        standardGaussianVector (1 + N)
          (Prod.mk pref ⁻¹'
            saddleSojournRestartEvent weighted x₀ M sigma radius N)
        ∂standardGaussianVector M) ≤
        ∫⁻ _pref,
          ENNReal.ofReal (2 * (C / (sigma * mu ^ N)))
          ∂standardGaussianVector M := by
      apply lintegral_mono
      intro pref
      change standardGaussianVector (1 + N)
          (Prod.mk pref ⁻¹'
            saddleSojournRestartEvent weighted x₀ M sigma radius N) ≤
        ENNReal.ofReal (2 * (C / (sigma * mu ^ N)))
      rw [saddleSojournRestartEvent_fiber]
      apply hfinite _ _ sigma hsigma N
      exact (finiteControlledOrbitFrom_isControlled p rho x₀
        (scaledGaussianControl sigma pref)).mem_absorbingBox model hx₀ M
    _ = ENNReal.ofReal (2 * (C / (sigma * mu ^ N))) := by simp

/-! ## Transfer back to a single Gaussian history -/

/-- The restart event pulled back to a single finite Gaussian vector. -/
def saddleSojournRestartFiniteEvent
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (x₀ : LoopState) (M : ℕ) (sigma radius : ℝ) (N : ℕ) :
    Set (Fin (M + (1 + N)) → ℝ) :=
  gaussianVectorSplitEquiv M (1 + N) ⁻¹'
    saddleSojournRestartEvent weighted x₀ M sigma radius N

/-- The single-vector restart event is measurable. -/
theorem measurableSet_saddleSojournRestartFiniteEvent
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (x₀ : LoopState) (M : ℕ) (sigma radius : ℝ) (N : ℕ) :
    MeasurableSet
      (saddleSojournRestartFiniteEvent weighted x₀ M sigma radius N) := by
  exact (measurableSet_saddleSojournRestartEvent
    weighted x₀ M sigma radius N).preimage
      (gaussianVectorSplitEquiv M (1 + N)).measurable

/-- Splitting the finite Gaussian law evaluates the restart event under the
product of the prefix and suffix laws. -/
theorem standardGaussianVector_saddleSojournRestartFiniteEvent
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (x₀ : LoopState) (M : ℕ) (sigma radius : ℝ) (N : ℕ) :
    standardGaussianVector (M + (1 + N))
        (saddleSojournRestartFiniteEvent weighted x₀ M sigma radius N) =
      (standardGaussianVector M).prod (standardGaussianVector (1 + N))
        (saddleSojournRestartEvent weighted x₀ M sigma radius N) := by
  unfold saddleSojournRestartFiniteEvent
  exact standardGaussianVector_split_preimage
    (measurableSet_saddleSojournRestartEvent
      weighted x₀ M sigma radius N)

/-- The deterministic-time saddle residence event on the canonical infinite
Gaussian history space. -/
def saddleSojournAfterTimeEvent
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (x₀ : LoopState) (M : ℕ) (sigma radius : ℝ) (N : ℕ) :
    Set GaussianNoisePath :=
  gaussianPrefix (M + (1 + N)) ⁻¹'
    saddleSojournRestartFiniteEvent weighted x₀ M sigma radius N

/-- The deterministic-time restart event has the literal path-space
interpretation: the original noisy recursion stays in the weighted saddle
ball from time `M+1` through time `M+1+N`. -/
theorem mem_saddleSojournAfterTimeEvent_iff
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (x₀ : LoopState) (M : ℕ) (sigma radius : ℝ) (N : ℕ)
    (xi : GaussianNoisePath) :
    xi ∈ saddleSojournAfterTimeEvent weighted x₀ M sigma radius N ↔
      ∀ n ≤ N,
        dist (gaussianNoisyOrbitFrom p rho x₀ sigma xi (M + (1 + n)))
          (weightedSaddlePoint weighted) < radius := by
  simp only [saddleSojournAfterTimeEvent, saddleSojournRestartFiniteEvent,
    saddleSojournRestartEvent, Set.mem_preimage, Set.mem_iInter,
    Set.mem_setOf_eq, Finset.mem_range]
  have hreconstruct :
      Fin.append
          (gaussianVectorSplitEquiv M (1 + N)
            (gaussianPrefix (M + (1 + N)) xi)).1
          (gaussianVectorSplitEquiv M (1 + N)
            (gaussianPrefix (M + (1 + N)) xi)).2 =
        gaussianPrefix (M + (1 + N)) xi := by
    rw [← gaussianVectorSplitEquiv_symm_pair,
      MeasurableEquiv.symm_apply_apply]
  rw [hreconstruct]
  constructor
  · intro h n hn
    rw [← finiteControlledOrbitFrom_gaussianPrefix_eq_gaussianNoisyOrbitFrom
      p rho x₀ sigma xi (by omega : M + (1 + n) ≤ M + (1 + N))]
    exact h n (by omega)
  · intro h n hn
    rw [finiteControlledOrbitFrom_gaussianPrefix_eq_gaussianNoisyOrbitFrom
      p rho x₀ sigma xi (by omega : M + (1 + n) ≤ M + (1 + N))]
    exact h n (by omega)

/-- The canonical-history event is measurable. -/
theorem measurableSet_saddleSojournAfterTimeEvent
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (x₀ : LoopState) (M : ℕ) (sigma radius : ℝ) (N : ℕ) :
    MeasurableSet
      (saddleSojournAfterTimeEvent weighted x₀ M sigma radius N) := by
  exact (measurableSet_saddleSojournRestartFiniteEvent
    weighted x₀ M sigma radius N).preimage
      (measurable_gaussianPrefix (M + (1 + N)))

/-- Evaluation on the infinite history agrees with the prefix/suffix product
restart law. -/
theorem standardGaussianSequence_saddleSojournAfterTimeEvent
    {p : LoopParams} {rho : ℝ} (weighted : WeightedThresholdAssumption p rho)
    (x₀ : LoopState) (M : ℕ) (sigma radius : ℝ) (N : ℕ) :
    standardGaussianSequence
        (saddleSojournAfterTimeEvent weighted x₀ M sigma radius N) =
      (standardGaussianVector M).prod (standardGaussianVector (1 + N))
        (saddleSojournRestartEvent weighted x₀ M sigma radius N) := by
  unfold saddleSojournAfterTimeEvent
  rw [← Measure.map_apply (measurable_gaussianPrefix (M + (1 + N)))
      (measurableSet_saddleSojournRestartFiniteEvent
        weighted x₀ M sigma radius N),
    standardGaussianSequence_map_prefix,
    standardGaussianVector_saddleSojournRestartFiniteEvent]

/-- The saddle-sojourn estimate is uniform after every deterministic restart
time, despite the restart state being random. -/
theorem exists_weightedSaddle_sojourn_after_time_probability_bound
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho) :
    ∃ mu : ℝ, 1 < mu ∧ ∃ radius : ℝ, 0 < radius ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (x₀ : LoopState), x₀ ∈ absorbingBox p →
          ∀ M : ℕ, ∀ sigma : ℝ, 0 < sigma → ∀ N : ℕ,
            standardGaussianSequence
                (saddleSojournAfterTimeEvent
                  weighted x₀ M sigma radius N) ≤
              ENNReal.ofReal (2 * (C / (sigma * mu ^ N))) := by
  obtain ⟨mu, hmu, radius, hradius, C, hC, hfinite⟩ :=
    exists_weightedSaddle_sojourn_finite_probability_bound
      model ss hcoop weighted
  refine ⟨mu, hmu, radius, hradius, C, hC, ?_⟩
  intro x₀ hx₀ M sigma hsigma N
  rw [standardGaussianSequence_saddleSojournAfterTimeEvent]
  exact saddleSojournRestartEvent_probability_le
    model weighted hfinite hx₀ M hsigma N

/-- Uniform deterministic-time version of the logarithmic saddle-residence
tail.  The state at time `M` may depend on the entire Gaussian prefix; every
additional `s` steps beyond the logarithmic burn-in still cost `mu⁻ˢ`. -/
theorem exists_weightedSaddle_sojourn_after_time_logarithmic_tail
    {p : LoopParams} (model : DriftModelAssumptions p)
    (ss : SmallStepAssumption p) {rho : ℝ}
    (hcoop : rho ≤ 2 * p.c * (1 - p.c))
    (weighted : WeightedThresholdAssumption p rho) :
    ∃ mu : ℝ, 1 < mu ∧ ∃ radius : ℝ, 0 < radius ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (x₀ : LoopState), x₀ ∈ absorbingBox p →
          ∀ M : ℕ, ∀ sigma : ℝ, 0 < sigma → ∀ s : ℕ,
            standardGaussianSequence
                (saddleSojournAfterTimeEvent weighted x₀ M sigma radius
                  (saddleSojournBurnIn mu sigma + s)) ≤
              ENNReal.ofReal (2 * (C / mu ^ s)) := by
  obtain ⟨mu, hmu, radius, hradius, C, hC, hprob⟩ :=
    exists_weightedSaddle_sojourn_after_time_probability_bound
      model ss hcoop weighted
  refine ⟨mu, hmu, radius, hradius, C, hC, ?_⟩
  intro x₀ hx₀ M sigma hsigma s
  let t := saddleSojournBurnIn mu sigma
  have hscale : 1 ≤ sigma * mu ^ t :=
    one_le_sigma_mul_pow_saddleSojournBurnIn hmu hsigma
  calc
    standardGaussianSequence
          (saddleSojournAfterTimeEvent weighted x₀ M sigma radius (t + s)) ≤
        ENNReal.ofReal (2 * (C / (sigma * mu ^ (t + s)))) :=
      hprob x₀ hx₀ M sigma hsigma (t + s)
    _ ≤ ENNReal.ofReal (2 * (C / mu ^ s)) := by
      apply ENNReal.ofReal_le_ofReal
      have hpowS : 0 < mu ^ s := pow_pos (zero_lt_one.trans hmu) s
      have hden : mu ^ s ≤ sigma * mu ^ (t + s) := by
        rw [pow_add]
        calc
          mu ^ s = 1 * mu ^ s := by ring
          _ ≤ (sigma * mu ^ t) * mu ^ s :=
            mul_le_mul_of_nonneg_right hscale hpowS.le
          _ = sigma * (mu ^ t * mu ^ s) := by ring
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hC.le hpowS hden) (by norm_num)

#print axioms nearCrossing_action_lower_of_policyMatching
#print axioms IsControlledCivicWeightedPathFrom.mem_weightedSaddleOrderInterval
#print axioms continuous_gaussianNoisyOrbitFrom
#print axioms measurableSet_nearCrossingExcursionAtTimeEvent
#print axioms mem_nearCrossingExcursionEvent_iff
#print axioms measurableSet_nearCrossingExcursionEvent
#print axioms measurableSet_gaussianNearCrossingByEventFrom
#print axioms standardGaussianSequence_gaussianNearCrossingByEventFrom
#print axioms exists_nearCrossingExcursionEvent_subset_actionTail
#print axioms exists_nearCrossingExcursionEvent_subset_fixed_actionTail
#print axioms exists_nearCrossingExcursionProbability_le_chernoff
#print axioms exists_uniform_nearCrossingExcursionProbability_le
#print axioms gaussianNoisyOrbitFrom_tail_eq
#print axioms lastExitNearCrossingEvent_subset_tail_actionTail
#print axioms lastExitNearCrossingEvent_probability_le_chernoff
#print axioms gaussianEscapeByEvent_subset_lastExitNearCrossing
#print axioms gaussianEscapeProbability_le_lastExit_chernoff
#print axioms exponentialEscapeHorizon_add_one_le
#print axioms monotone_exponentialEscapeHorizon
#print axioms exponentialEscapeProbability_tendsto_zero_of_rate_lt
#print axioms civicCrossingQuasipotential_pos_of_lipschitz
#print axioms crossingLowerEscapeProbability
#print axioms eventually_half_exp_le_exponentialEscapeHorizon
#print axioms meanGaussianEscapeLogRate_liminf_ge_of_persistence
#print axioms crossingLowerMeanRate
#print axioms crossingMeanRate
#print axioms finiteControlledOrbitFrom_scaled_append_right
#print axioms measurableSet_saddleSojournRestartEvent
#print axioms saddleSojournRestartEvent_fiber
#print axioms saddleSojournRestartEvent_probability_le
#print axioms measurableSet_saddleSojournRestartFiniteEvent
#print axioms standardGaussianVector_saddleSojournRestartFiniteEvent
#print axioms mem_saddleSojournAfterTimeEvent_iff
#print axioms measurableSet_saddleSojournAfterTimeEvent
#print axioms standardGaussianSequence_saddleSojournAfterTimeEvent
#print axioms exists_weightedSaddle_sojourn_after_time_probability_bound
#print axioms exists_weightedSaddle_sojourn_after_time_logarithmic_tail

end

end CivicAlignment.PaperII
