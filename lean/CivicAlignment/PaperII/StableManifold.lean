/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.StableManifoldBridge
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# The local stable manifold at the interior saddle

The final assembly.  Irwin's stable curve for the saddle germ
(`PaperII/StableCurve.lean`, instantiated by `PaperII/SaddleGerm.lean`) is
transported back to model coordinates and matched against the ambient stable
set: the bridge of `PaperII/StableManifoldBridge.lean` shows a stable orbit
starting near the saddle stays near the saddle, where the projection is
inactive and the conjugation is exact, so the implicit-function uniqueness
pins it to the curve.  Orientation and injectivity follow from tangency to
the contracting eigenvector `(b, λ₂ - a)`, whose components have opposite
signs by the kernel-proved entry positivity and `λ₂ < a`.

The result, `saddleLocalStableManifold`, supplies
`Imported.localStableManifoldForBistableLoop`, which restates it under that
module's historical name.
-/

namespace CivicAlignment
namespace PaperII

open BoundedContinuousFunction Metric Set Filter Topology LoopParams

variable {p : LoopParams}

/-- The germ map read back in model coordinates. -/
theorem saddleGerm_map_eq (model : DriftModelAssumptions p)
    (ssplus : ConvergentStepAssumption p) (threshold : ThresholdAssumption p)
    (z : LoopState) :
    (saddleGerm model ssplus threshold).map z =
      eigenBasisInv p threshold
        (unclippedLoopMap p
          (saddlePoint p threshold + eigenBasis p threshold z) -
          saddlePoint p threshold) := by
  have h := saddleGerm_map_conj model ssplus threshold z
  have h2 : eigenBasis p threshold ((saddleGerm model ssplus threshold).map z) =
      unclippedLoopMap p
        (saddlePoint p threshold + eigenBasis p threshold z) -
        saddlePoint p threshold := by
    rw [← h, add_sub_cancel_left]
  calc (saddleGerm model ssplus threshold).map z
      = eigenBasisInv p threshold (eigenBasis p threshold
          ((saddleGerm model ssplus threshold).map z)) :=
        (eigenBasisInv_eigenBasis model ssplus threshold _).symm
    _ = eigenBasisInv p threshold
        (unclippedLoopMap p
          (saddlePoint p threshold + eigenBasis p threshold z) -
          saddlePoint p threshold) := by rw [h2]

/-- Forward transfer: while the transported germ orbit stays in the
projection-inactive zone, it is the loop orbit. -/
theorem loopOrbit_eq_fromEigen (model : DriftModelAssumptions p)
    (ssplus : ConvergentStepAssumption p) (threshold : ThresholdAssumption p)
    {dz : ℝ}
    (hdz : ∀ ⦃y : LoopState⦄, dist y (saddlePoint p threshold) < dz →
      p.loopMap y = unclippedLoopMap p y)
    {z : LoopState}
    (hz : ∀ n, dist (saddlePoint p threshold + eigenBasis p threshold
      ((saddleGerm model ssplus threshold).map^[n] z))
      (saddlePoint p threshold) < dz) :
    ∀ n, loopOrbit p (saddlePoint p threshold + eigenBasis p threshold z) n =
      saddlePoint p threshold + eigenBasis p threshold
        ((saddleGerm model ssplus threshold).map^[n] z) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have hstep : loopOrbit p
          (saddlePoint p threshold + eigenBasis p threshold z) (n + 1) =
          p.loopMap (loopOrbit p
            (saddlePoint p threshold + eigenBasis p threshold z) n) :=
        Function.iterate_succ_apply' _ _ _
      have hsucc : (saddleGerm model ssplus threshold).map^[n + 1] z =
          (saddleGerm model ssplus threshold).map
            ((saddleGerm model ssplus threshold).map^[n] z) :=
        Function.iterate_succ_apply' _ _ _
      rw [hstep, ih, hdz (hz n), hsucc,
        saddleGerm_map_conj model ssplus threshold]

/-- Backward transfer: while the loop orbit stays in the zone, its
eigencoordinates follow the germ. -/
theorem germOrbit_eq_toEigen (model : DriftModelAssumptions p)
    (ssplus : ConvergentStepAssumption p) (threshold : ThresholdAssumption p)
    {dz : ℝ}
    (hdz : ∀ ⦃y : LoopState⦄, dist y (saddlePoint p threshold) < dz →
      p.loopMap y = unclippedLoopMap p y)
    {x : LoopState}
    (hx : ∀ n, dist (loopOrbit p x n) (saddlePoint p threshold) < dz) :
    ∀ n, (saddleGerm model ssplus threshold).map^[n]
        (eigenBasisInv p threshold (x - saddlePoint p threshold)) =
      eigenBasisInv p threshold
        (loopOrbit p x n - saddlePoint p threshold) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have hstep : loopOrbit p x (n + 1) = p.loopMap (loopOrbit p x n) :=
        Function.iterate_succ_apply' _ _ _
      rw [Function.iterate_succ_apply', ih,
        saddleGerm_map_eq model ssplus threshold,
        eigenBasis_eigenBasisInv model ssplus threshold,
        add_sub_cancel, ← hdz (hx n), hstep]

/-- **The local stable-manifold theorem for the bistable loop, proved.**
Under the model assumptions, `(SS⁺)`, and `(H)`, the ambient stable set of
the interior saddle agrees, in an open neighborhood of the saddle, with the
image of an injective `C¹` arc whose policy coordinate strictly increases
and whose stock coordinate strictly decreases. -/
theorem saddleLocalStableManifold (model : DriftModelAssumptions p)
    (ssplus : ConvergentStepAssumption p) (threshold : ThresholdAssumption p) :
    IsLocalC1DecreasingArcAt (ambientSaddleStableSet p threshold)
      (saddlePoint p threshold) := by
  classical
  obtain ⟨data⟩ := (saddleGerm model ssplus threshold).exists_stableCurveData
  set q : LoopState := saddlePoint p threshold with hqdef
  set P : LoopState →L[ℝ] LoopState := eigenBasis p threshold with hPdef
  set Pi' : LoopState →L[ℝ] LoopState := eigenBasisInv p threshold with hPidef
  have hPleft : ∀ z, Pi' (P z) = z :=
    eigenBasisInv_eigenBasis model ssplus threshold
  have hPright : ∀ w, P (Pi' w) = w :=
    eigenBasis_eigenBasisInv model ssplus threshold
  set CP : ℝ := ‖P‖ + 1 with hCPdef
  set CPi : ℝ := ‖Pi'‖ + 1 with hCPidef
  have hCPpos : 0 < CP := by positivity
  have hCPipos : 0 < CPi := by positivity
  have hPltCP : ‖P‖ < CP := by rw [hCPdef]; linarith
  have hPiltCPi : ‖Pi'‖ < CPi := by rw [hCPidef]; linarith
  -- the projection-inactive zone
  obtain ⟨dz, hdzpos, hdz⟩ :=
    Metric.eventually_nhds_iff.mp (eventually_loopMap_eq_unclipped threshold)
  -- the interior box
  have hβ := threshold.βdagger_mem
  have hD := stationaryStock_mem_Ioo model threshold
  set dB : ℝ := min (min threshold.βdagger (1 - threshold.βdagger))
    (min (p.stationaryStock threshold.βdagger - p.I)
      (p.I / p.lambda₀ - p.stationaryStock threshold.βdagger)) with hdBdef
  have hdBpos : 0 < dB := by
    apply lt_min (lt_min hβ.1 (by linarith [hβ.2]))
    exact lt_min (by linarith [hD.1]) (by linarith [hD.2])
  have hballB : ∀ y : LoopState, dist y q < dB → y ∈ absorbingBox p := by
    intro y hy
    have h1 : dist y.1 q.1 < dB := by
      apply lt_of_le_of_lt _ hy
      rw [Prod.dist_eq]
      exact le_max_left _ _
    have h2 : dist y.2 q.2 < dB := by
      apply lt_of_le_of_lt _ hy
      rw [Prod.dist_eq]
      exact le_max_right _ _
    rw [Real.dist_eq] at h1 h2
    have hb1 : |y.1 - threshold.βdagger| <
        min threshold.βdagger (1 - threshold.βdagger) :=
      lt_of_lt_of_le h1 (min_le_left _ _)
    have hb2 : |y.2 - p.stationaryStock threshold.βdagger| <
        min (p.stationaryStock threshold.βdagger - p.I)
          (p.I / p.lambda₀ - p.stationaryStock threshold.βdagger) :=
      lt_of_lt_of_le h2 (min_le_right _ _)
    rw [abs_lt] at hb1 hb2
    have hm1 : min threshold.βdagger (1 - threshold.βdagger) ≤
        threshold.βdagger := min_le_left _ _
    have hm2 : min threshold.βdagger (1 - threshold.βdagger) ≤
        1 - threshold.βdagger := min_le_right _ _
    have hm3 : min (p.stationaryStock threshold.βdagger - p.I)
        (p.I / p.lambda₀ - p.stationaryStock threshold.βdagger) ≤
        p.stationaryStock threshold.βdagger - p.I := min_le_left _ _
    have hm4 : min (p.stationaryStock threshold.βdagger - p.I)
        (p.I / p.lambda₀ - p.stationaryStock threshold.βdagger) ≤
        p.I / p.lambda₀ - p.stationaryStock threshold.βdagger := min_le_right _ _
    exact ⟨⟨by linarith [hb1.1], by linarith [hb1.2]⟩,
      ⟨by linarith [hb2.1], by linarith [hb2.2]⟩⟩
  -- the sign window of the transported tangent
  have hbpos : 0 < (saddleJac p threshold).b := by
    have h := saddleJacobian_entry_pos model ssplus threshold
    simp only at h
    simpa [saddleJac] using h.2.1
  have hl2a : (saddleJac p threshold).smallerEigenvalue -
      (saddleJac p threshold).a < 0 := by
    linarith [saddle_smallerEigenvalue_lt_a model ssplus threshold]
  have hderivOn : ContinuousOn (fun σ => deriv data.curve σ)
      (Ioo (-data.ε) data.ε) :=
    data.curve_contDiffOn.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have h0mem : (0 : ℝ) ∈ Ioo (-data.ε) data.ε :=
    ⟨by linarith [data.ε_pos], data.ε_pos⟩
  have hgcont : ContinuousAt (fun σ => deriv data.curve σ) 0 :=
    hderivOn.continuousAt (isOpen_Ioo.mem_nhds h0mem)
  have hg0 : deriv data.curve 0 = ((0 : ℝ), (1 : ℝ)) :=
    data.curve_hasDerivAt.deriv
  set A : ℝ → ℝ := fun σ => (saddleJac p threshold).b * (deriv data.curve σ).1 +
    (saddleJac p threshold).b * (deriv data.curve σ).2 with hAdef
  set Bf : ℝ → ℝ := fun σ =>
    ((saddleJac p threshold).largerEigenvalue - (saddleJac p threshold).a) *
      (deriv data.curve σ).1 +
    ((saddleJac p threshold).smallerEigenvalue - (saddleJac p threshold).a) *
      (deriv data.curve σ).2 with hBfdef
  have hA0 : 0 < A 0 := by
    simp only [hAdef, hg0]
    simpa using hbpos
  have hB0 : Bf 0 < 0 := by
    simp only [hBfdef, hg0]
    simpa using hl2a
  have hAcont : ContinuousAt A 0 := by
    apply ContinuousAt.add
    · exact continuousAt_const.mul (continuous_fst.continuousAt.comp hgcont)
    · exact continuousAt_const.mul (continuous_snd.continuousAt.comp hgcont)
  have hBcont : ContinuousAt Bf 0 := by
    apply ContinuousAt.add
    · exact continuousAt_const.mul (continuous_fst.continuousAt.comp hgcont)
    · exact continuousAt_const.mul (continuous_snd.continuousAt.comp hgcont)
  have hwin : ∀ᶠ σ in 𝓝 (0 : ℝ), 0 < A σ ∧ Bf σ < 0 := by
    have h1 : ∀ᶠ σ in 𝓝 (0 : ℝ), A σ ∈ Ioi (0 : ℝ) :=
      hAcont.eventually_mem (isOpen_Ioi.mem_nhds hA0)
    have h2 : ∀ᶠ σ in 𝓝 (0 : ℝ), Bf σ ∈ Iio (0 : ℝ) :=
      hBcont.eventually_mem (isOpen_Iio.mem_nhds hB0)
    filter_upwards [h1, h2] with σ hσ1 hσ2
    exact ⟨hσ1, hσ2⟩
  obtain ⟨εs, hεspos, hεs⟩ := Metric.eventually_nhds_iff.mp hwin
  -- the radii
  set d : ℝ := min (min dz dB) (data.ρ / CPi) with hddef
  have hdpos : 0 < d :=
    lt_min (lt_min hdzpos hdBpos) (div_pos data.ρ_pos hCPipos)
  have hd_le_dz : d ≤ dz := (min_le_left _ _).trans (min_le_left _ _)
  have hd_le_dB : d ≤ dB := (min_le_left _ _).trans (min_le_right _ _)
  have hd_le_ρ : CPi * d ≤ data.ρ := by
    have h1 : d ≤ data.ρ / CPi := min_le_right _ _
    calc CPi * d ≤ CPi * (data.ρ / CPi) :=
          mul_le_mul_of_nonneg_left h1 hCPipos.le
      _ = data.ρ := by
          rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hCPipos)]
  set εf : ℝ := min (min data.ε εs) (d / (2 * CP)) with hεfdef
  have hεfpos : 0 < εf :=
    lt_min (lt_min data.ε_pos hεspos) (div_pos hdpos (by positivity))
  have hεf_le_ε : εf ≤ data.ε := (min_le_left _ _).trans (min_le_left _ _)
  have hεf_le_εs : εf ≤ εs := (min_le_left _ _).trans (min_le_right _ _)
  have hεf_d : 2 * CP * εf ≤ d := by
    have h1 : εf ≤ d / (2 * CP) := min_le_right _ _
    calc 2 * CP * εf ≤ 2 * CP * (d / (2 * CP)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = d := by
          rw [mul_comm, div_mul_cancel₀ _ (by positivity)]
  have hIooSub : Ioo (-εf) εf ⊆ Ioo (-data.ε) data.ε :=
    Ioo_subset_Ioo (by linarith) hεf_le_ε
  -- the P-image bound for curve orbits
  have hPbound : ∀ (σ : ℝ), |σ| < εf → ∀ w : LoopState, ‖w‖ ≤ 2 * |σ| →
      dist (q + P w) q < d := by
    intro σ hσ w hw
    rw [dist_eq_norm, add_sub_cancel_left]
    calc ‖P w‖ ≤ ‖P‖ * ‖w‖ := P.le_opNorm w
      _ ≤ ‖P‖ * (2 * |σ|) :=
          mul_le_mul_of_nonneg_left hw (norm_nonneg _)
      _ < d := by nlinarith [norm_nonneg (P : LoopState →L[ℝ] LoopState),
          abs_nonneg σ]
  -- the window as a bound on the interval
  have hwin' : ∀ σ ∈ Ioo (-εf) εf, 0 < A σ ∧ Bf σ < 0 := by
    intro σ hσ
    apply hεs
    rw [Real.dist_eq, sub_zero]
    rw [mem_Ioo] at hσ
    exact lt_of_lt_of_le (abs_lt.mpr hσ) hεf_le_εs
  -- derivatives of the transported curve components
  have hcurveAt : ∀ σ ∈ Ioo (-εf) εf,
      HasDerivAt data.curve (deriv data.curve σ) σ := by
    intro σ hσ
    exact ((data.curve_contDiffOn.contDiffAt
      (isOpen_Ioo.mem_nhds (hIooSub hσ))).differentiableAt one_ne_zero).hasDerivAt
  have hγ1At : ∀ σ ∈ Ioo (-εf) εf,
      HasDerivAt (fun t => (q + P (data.curve t)).1) (A σ) σ := by
    intro σ hσ
    have hqσ : HasDerivAt (fun t => q + P (data.curve t))
        (P (deriv data.curve σ)) σ :=
      (P.hasFDerivAt.comp_hasDerivAt σ (hcurveAt σ hσ)).const_add q
    have hcomp : HasDerivAt (fun t => (q + P (data.curve t)).1)
        ((P (deriv data.curve σ)).1) σ := by
      have h := ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt
        σ hqσ)
      exact h
    have hval : (P (deriv data.curve σ)).1 = A σ := by
      simp [hPdef, eigenBasis, entriesCLM_apply, hAdef]
    rwa [hval] at hcomp
  have hγ2At : ∀ σ ∈ Ioo (-εf) εf,
      HasDerivAt (fun t => (q + P (data.curve t)).2) (Bf σ) σ := by
    intro σ hσ
    have hqσ : HasDerivAt (fun t => q + P (data.curve t))
        (P (deriv data.curve σ)) σ :=
      (P.hasFDerivAt.comp_hasDerivAt σ (hcurveAt σ hσ)).const_add q
    have hcomp : HasDerivAt (fun t => (q + P (data.curve t)).2)
        ((P (deriv data.curve σ)).2) σ := by
      have h := ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt
        σ hqσ)
      exact h
    have hval : (P (deriv data.curve σ)).2 = Bf σ := by
      simp [hPdef, eigenBasis, entriesCLM_apply, hBfdef]
    rwa [hval] at hcomp
  -- smoothness of the transported curve
  have hγcd : ContDiffOn ℝ 1 (fun σ => q + P (data.curve σ)) (Ioo (-εf) εf) := by
    have houter : ContDiff ℝ 1 (fun w : LoopState => q + P w) :=
      contDiff_const.add P.contDiff
    exact houter.comp_contDiffOn (data.curve_contDiffOn.mono hIooSub)
  -- assemble the arc
  refine ⟨εf, hεfpos, fun σ => q + P (data.curve σ),
    Metric.ball q d ∩ {y : LoopState | (Pi' (y - q)).2 ∈ Ioo (-εf) εf},
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- open
    apply Metric.isOpen_ball.inter
    have hcont : Continuous fun y : LoopState => (Pi' (y - q)).2 :=
      continuous_snd.comp (Pi'.continuous.comp (continuous_id.sub
        continuous_const))
    exact isOpen_Ioo.preimage hcont
  · -- the saddle is inside
    refine ⟨mem_ball_self hdpos, ?_⟩
    simp only [Set.mem_setOf_eq, sub_self, map_zero, Prod.snd_zero]
    exact ⟨by linarith, hεfpos⟩
  · -- C¹
    exact hγcd
  · -- through the saddle
    simp only [data.curve_zero, map_zero, add_zero]
  · -- injective
    have hmono : StrictMonoOn (fun t => (q + P (data.curve t)).1)
        (Ioo (-εf) εf) := by
      apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
      · exact continuous_fst.comp_continuousOn hγcd.continuousOn
      · intro σ hσ
        rw [interior_Ioo] at hσ
        rw [(hγ1At σ hσ).deriv]
        exact (hwin' σ hσ).1
    intro s hs t ht hst
    exact hmono.injOn hs ht (congrArg Prod.fst hst)
  · -- policy strictly increases
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    · exact continuous_fst.comp_continuousOn hγcd.continuousOn
    · intro σ hσ
      rw [interior_Ioo] at hσ
      rw [(hγ1At σ hσ).deriv]
      exact (hwin' σ hσ).1
  · -- stock strictly decreases
    apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    · exact continuous_snd.comp_continuousOn hγcd.continuousOn
    · intro σ hσ
      rw [interior_Ioo] at hσ
      rw [(hγ2At σ hσ).deriv]
      exact (hwin' σ hσ).2
  · -- the set identity
    apply Set.Subset.antisymm
    · -- ambient stable points in the window lie on the curve
      rintro y ⟨hyΓ, hyb, hyw⟩
      have hdisty : dist y q < d := mem_ball.mp hyb
      have horbz : ∀ n, dist (loopOrbit p y n) q < dz := fun n =>
        lt_of_le_of_lt (stable_orbit_dist_le model ssplus threshold hyΓ n)
          (lt_of_lt_of_le hdisty hd_le_dz)
      have hgerm := germOrbit_eq_toEigen model ssplus threshold hdz horbz
      have hnorm : ∀ n, ‖(saddleGerm model ssplus threshold).map^[n]
          (Pi' (y - q))‖ ≤ data.ρ := by
        intro n
        rw [hgerm n]
        calc ‖Pi' (loopOrbit p y n - q)‖
            ≤ ‖Pi'‖ * ‖loopOrbit p y n - q‖ := Pi'.le_opNorm _
          _ ≤ ‖Pi'‖ * d := by
              apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
              rw [← dist_eq_norm]
              exact (lt_of_le_of_lt (stable_orbit_dist_le model ssplus
                threshold hyΓ n) hdisty).le
          _ ≤ CPi * d := mul_le_mul_of_nonneg_right hPiltCPi.le hdpos.le
          _ ≤ data.ρ := hd_le_ρ
      obtain ⟨hz2, hzeq⟩ := data.staying_mem_graph (Pi' (y - q)) hnorm
      refine ⟨(Pi' (y - q)).2, hyw, ?_⟩
      calc q + P (data.curve ((Pi' (y - q)).2))
          = q + P (Pi' (y - q)) := by rw [← hzeq]
        _ = q + (y - q) := by rw [hPright]
        _ = y := by rw [add_sub_cancel]
    · -- curve points are ambient stable and in the window
      rintro y ⟨σ, hσ, rfl⟩
      have hσ' := hσ
      rw [mem_Ioo] at hσ'
      have hσabs : |σ| < εf := abs_lt.mpr hσ'
      have hσdata : σ ∈ Ioo (-data.ε) data.ε := hIooSub hσ
      have hnorm := data.orbit_norm_le σ hσdata
      have hzone : ∀ n, dist (q + P
          ((saddleGerm model ssplus threshold).map^[n] (data.curve σ))) q < d :=
        fun n => hPbound σ hσabs _ (hnorm n)
      have htransfer := loopOrbit_eq_fromEigen model ssplus threshold hdz
        (fun n => lt_of_lt_of_le (hzone n) hd_le_dz)
      have hball : dist (q + P (data.curve σ)) q < d := by
        have h0 := hzone 0
        simpa using h0
      constructor
      · refine ⟨hballB _ (lt_of_lt_of_le hball hd_le_dB), ?_⟩
        have hlim := data.orbit_tendsto σ hσdata
        have hcomp : Tendsto (fun n => q + P
            ((saddleGerm model ssplus threshold).map^[n] (data.curve σ)))
            atTop (𝓝 (q + P 0)) :=
          ((continuous_const.add P.continuous).tendsto 0).comp hlim
        have hfun : loopOrbit p (q + P (data.curve σ)) = fun n => q + P
            ((saddleGerm model ssplus threshold).map^[n] (data.curve σ)) :=
          funext htransfer
        rw [hfun]
        simpa using hcomp
      · refine ⟨mem_ball.mpr hball, ?_⟩
        simp only [Set.mem_setOf_eq, add_sub_cancel_left, hPleft,
          data.curve_snd]
        exact hσ

end PaperII
end CivicAlignment

#print axioms CivicAlignment.PaperII.saddleLocalStableManifold
