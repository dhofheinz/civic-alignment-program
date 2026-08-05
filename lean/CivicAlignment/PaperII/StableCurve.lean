/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.PlanarHadamardPerron

/-!
# The local stable curve of a planar hyperbolic germ

This file packages the implicit solution family of
`PaperII/PlanarHadamardPerron.lean` into the local stable-manifold statement:
a `C¹` curve `σ ↦ (w σ, σ)` through the origin, tangent to the contracting
axis, whose points converge to the origin under the germ, and which captures
*every* orbit that remains uniformly small — the latter because a bounded
small orbit is a Green solution, and the implicit function theorem's local
uniqueness pins it to the graph.  Convergence is geometric: each tail of a
graph orbit is itself the graph value at its own initial contracting
coordinate, so the local Lipschitz bound on the graph converts the
contracting recursion into a strict contraction of the initial coordinate.

Nothing here mentions the loop model; `PaperII/StableManifold.lean`
instantiates it at the interior saddle.
-/

namespace CivicAlignment
namespace PaperII
namespace PlanarHyperbolicGerm

open BoundedContinuousFunction Metric Set Filter Topology

open scoped NNReal

variable (Γ : PlanarHyperbolicGerm)

/-- The contracting injection is a contraction of norms. -/
theorem contractInjection_norm_le : ‖Γ.contractInjection‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- First-order smallness of the remainder transfers to a linear bound on a
ball, by the mean value inequality along segments from the origin. -/
theorem norm_r_le {ρν εν : ℝ}
    (hband : ∀ w : ℝ × ℝ, ‖w‖ ≤ ρν → ‖Γ.r' w‖ ≤ εν)
    {z : ℝ × ℝ} (hz : ‖z‖ ≤ ρν) : ‖Γ.r z‖ ≤ εν * ‖z‖ := by
  have hseg : ∀ w ∈ segment ℝ (0 : ℝ × ℝ) ((0 : ℝ × ℝ) + z),
      ‖Γ.r' w - Γ.r' 0‖ ≤ εν := by
    intro w hw
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hw
    rw [Γ.r'_zero, sub_zero]
    apply hband
    have hb1 : b ≤ 1 := by linarith
    calc ‖a • (0 : ℝ × ℝ) + b • ((0 : ℝ × ℝ) + z)‖
        = ‖b • z‖ := by rw [smul_zero, zero_add, zero_add]
      _ = b * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg hb]
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hb1 (norm_nonneg z)
      _ ≤ ρν := by rw [one_mul]; exact hz
  have h := norm_increment_sub_deriv_le Γ.r_hasFDerivAt hseg
  rw [zero_add, Γ.r_zero, Γ.r'_zero] at h
  simpa using h

/-- Bounded orbits of the germ transport along the graph: the `n`-th iterate
of an initial graph point is the `n`-th slot of the solution sequence. -/
theorem iterate_eq_of_orbit {x : SeqPair}
    (horb : ∀ n, x (n + 1) = Γ.map (x n)) :
    ∀ n, Γ.map^[n] (x 0) = x n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, horb n]

/-- The output bundle of the planar local stable-manifold theorem, in
eigencoordinates: a `C¹` curve `σ ↦ (w σ, σ)` through the origin, tangent to
the contracting axis, converging orbitwise to the origin, and capturing every
uniformly `ρ`-small orbit. -/
structure StableCurveData (Γ : PlanarHyperbolicGerm) where
  /-- The parameter half-width of the curve. -/
  ε : ℝ
  /-- The staying radius characterized by the curve. -/
  ρ : ℝ
  /-- The curve, parametrized by the contracting coordinate. -/
  curve : ℝ → ℝ × ℝ
  ε_pos : 0 < ε
  ρ_pos : 0 < ρ
  ρ_lt_ε : ρ < ε
  curve_snd : ∀ σ, (curve σ).2 = σ
  curve_contDiffOn : ContDiffOn ℝ 1 curve (Ioo (-ε) ε)
  curve_zero : curve 0 = 0
  curve_hasDerivAt : HasDerivAt curve ((0 : ℝ), (1 : ℝ)) 0
  orbit_tendsto : ∀ σ ∈ Ioo (-ε) ε,
    Tendsto (fun n => Γ.map^[n] (curve σ)) atTop (𝓝 0)
  orbit_norm_le : ∀ σ ∈ Ioo (-ε) ε, ∀ n,
    ‖Γ.map^[n] (curve σ)‖ ≤ 2 * |σ|
  staying_mem_graph : ∀ z : ℝ × ℝ, (∀ n, ‖Γ.map^[n] z‖ ≤ ρ) →
    z.2 ∈ Ioo (-ε) ε ∧ z = curve z.2

/-- Irwin's construction of the local stable curve. -/
theorem exists_stableCurveData : Nonempty (StableCurveData Γ) := by
  classical
  -- (a) the uniqueness neighborhood, thickened to a metric ball
  obtain ⟨U, hU, hUiff⟩ := eventually_iff_exists_mem.mp Γ.stableGraph_iff
  obtain ⟨δU, hδUpos, hδU⟩ := Metric.mem_nhds_iff.mp hU
  -- (b) the local Lipschitz bound on the graph
  have hK2 : ‖Γ.contractInjection‖₊ < (2 : ℝ≥0) := by
    have h1 : ‖Γ.contractInjection‖ < 2 :=
      lt_of_le_of_lt Γ.contractInjection_norm_le one_lt_two
    exact_mod_cast h1
  obtain ⟨s, hs, hLip⟩ :=
    Γ.stableGraph_hasStrictFDerivAt.exists_lipschitzOnWith_of_nnnorm_lt 2 hK2
  obtain ⟨ρL, hρLpos, hρL⟩ := Metric.mem_nhds_iff.mp hs
  have h0s : (0 : ℝ) ∈ s := mem_of_mem_nhds hs
  -- (c) the solution property near zero
  obtain ⟨εsol, hεsolpos, hεsol⟩ :=
    Metric.eventually_nhds_iff.mp Γ.stableGraph_solves
  -- (d) smoothness near zero
  obtain ⟨εcd, hεcdpos, hεcd⟩ :=
    Metric.eventually_nhds_iff.mp Γ.stableGraph_eventually_contDiffAt
  -- (e) first-order smallness of the remainder
  have hεν : (0 : ℝ) < (1 - Γ.ν) / 4 := by linarith [Γ.ν_lt_one]
  have hcont : ContinuousAt Γ.r' 0 := Γ.r'_continuous.continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨ρν, hρνpos, hρν⟩ := hcont ((1 - Γ.ν) / 4) hεν
  have hband : ∀ w : ℝ × ℝ, ‖w‖ ≤ ρν / 2 → ‖Γ.r' w‖ ≤ (1 - Γ.ν) / 4 := by
    intro w hw
    have hdist : dist w 0 < ρν := by
      rw [dist_zero_right]
      linarith
    have := hρν hdist
    rw [Γ.r'_zero, dist_zero_right] at this
    exact this.le
  -- (f) continuity of the graph at zero, aimed at the combined radius
  set rψ : ℝ := min δU (min ρL (ρν / 2)) with hrψdef
  have hrψpos : 0 < rψ := by
    apply lt_min hδUpos
    exact lt_min hρLpos (by linarith)
  have hψc0 : ContinuousAt Γ.stableGraph 0 :=
    Γ.stableGraph_contDiffAt_zero.continuousAt
  rw [Metric.continuousAt_iff] at hψc0
  obtain ⟨εc, hεcpos, hεc⟩ := hψc0 rψ hrψpos
  have hψnorm : ∀ σ : ℝ, |σ| < εc → ‖Γ.stableGraph σ‖ < rψ := by
    intro σ hσ
    have hd : dist σ 0 < εc := by rwa [dist_zero_right, Real.norm_eq_abs]
    have := hεc hd
    rwa [Γ.stableGraph_zero, dist_zero_right] at this
  -- the final radii
  set ε : ℝ := min εsol (min εcd εc) with hεdef
  have hεpos : 0 < ε := lt_min hεsolpos (lt_min hεcdpos hεcpos)
  set ρ : ℝ := min ε rψ / 2 with hρdef
  have hρpos : 0 < ρ := by
    apply half_pos
    exact lt_min hεpos hrψpos
  have hρltε : ρ < ε := by
    have h1 : min ε rψ ≤ ε := min_le_left _ _
    have h2 : 0 < min ε rψ := lt_min hεpos hrψpos
    calc ρ = min ε rψ / 2 := rfl
      _ < min ε rψ := by linarith
      _ ≤ ε := h1
  -- the curve
  set curve : ℝ → ℝ × ℝ := fun σ => ((Γ.stableGraph σ 0).1, σ) with hcurvedef
  -- the contraction factor
  set θ : ℝ := (1 + Γ.ν) / 2 with hθdef
  have hθ0 : 0 ≤ θ := by
    have := Γ.ν_pos
    positivity
  have hθ1 : θ < 1 := by
    have := Γ.ν_lt_one
    rw [hθdef]
    linarith
  -- membership of pairs in the uniqueness ball
  have hpair_mem : ∀ (τ : ℝ) (y : SeqPair), |τ| < rψ → ‖y‖ < rψ →
      (τ, y) ∈ U := by
    intro τ y hτ hy
    apply hδU
    rw [mem_ball]
    have hd : dist ((τ, y)) (((0 : ℝ), (0 : SeqPair))) =
        max (dist τ 0) (dist y 0) := Prod.dist_eq
    rw [hd, dist_zero_right, dist_zero_right, Real.norm_eq_abs]
    apply max_lt (lt_of_lt_of_le hτ (min_le_left _ _))
      (lt_of_lt_of_le hy (min_le_left _ _))
  -- the Lipschitz consequence: graph values at small parameters
  have hgraph_le : ∀ τ : ℝ, |τ| < rψ → ‖Γ.stableGraph τ‖ ≤ 2 * |τ| := by
    intro τ hτ
    have hτs : τ ∈ s := by
      apply hρL
      rw [mem_ball, dist_zero_right, Real.norm_eq_abs]
      exact lt_of_lt_of_le hτ ((min_le_right _ _).trans (min_le_left _ _))
    have := hLip.dist_le_mul τ hτs 0 h0s
    rw [Γ.stableGraph_zero, dist_zero_right, dist_zero_right,
      Real.norm_eq_abs] at this
    calc ‖Γ.stableGraph τ‖ ≤ (2 : ℝ≥0) * |τ| := this
      _ = 2 * |τ| := by norm_num
  -- geometric decay along solutions with small graph norm
  have hdecay : ∀ σ : ℝ, |σ| < ε →
      (∀ m, |(Γ.stableGraph σ m).2| ≤ θ ^ m * |σ|) ∧
      (∀ m, ‖Γ.stableGraph σ m‖ ≤ 2 * |(Γ.stableGraph σ m).2|) := by
    intro σ hσ
    have hσsol : Γ.IsGreenSolution σ (Γ.stableGraph σ) := by
      apply hεsol
      rw [dist_zero_right, Real.norm_eq_abs]
      exact lt_of_lt_of_le hσ (min_le_left _ _)
    have horbit := hσsol.orbit
    have hψsmall : ‖Γ.stableGraph σ‖ < rψ :=
      hψnorm σ (lt_of_lt_of_le hσ ((min_le_right _ _).trans (min_le_right _ _)))
    -- each tail is the graph value at its own initial contracting coordinate
    have htail : ∀ m, Γ.stableGraph ((Γ.stableGraph σ m).2) =
        ofNormedAddCommGroupDiscrete (fun k => Γ.stableGraph σ (m + k))
          ‖Γ.stableGraph σ‖ (fun k => (Γ.stableGraph σ).norm_coe_le_norm (m + k)) := by
      intro m
      set tail : SeqPair := ofNormedAddCommGroupDiscrete
        (fun k => Γ.stableGraph σ (m + k)) ‖Γ.stableGraph σ‖
        (fun k => (Γ.stableGraph σ).norm_coe_le_norm (m + k)) with htaildef
      have htail_apply : ∀ k, tail k = Γ.stableGraph σ (m + k) := fun k => rfl
      have htail_sol : Γ.IsGreenSolution ((Γ.stableGraph σ m).2) tail := by
        apply isGreenSolution_of_orbit
        · exact congrArg (fun t => (Γ.stableGraph σ t).2) (Nat.add_zero m)
        · intro k
          rw [htail_apply (k + 1), htail_apply k]
          exact horbit.2 (m + k)
      have htail_norm : ‖tail‖ ≤ ‖Γ.stableGraph σ‖ :=
        (norm_le (norm_nonneg _)).mpr fun k =>
          (Γ.stableGraph σ).norm_coe_le_norm (m + k)
      have hσm : |(Γ.stableGraph σ m).2| < rψ :=
        lt_of_le_of_lt ((norm_snd_le _).trans
          ((Γ.stableGraph σ).norm_coe_le_norm m)) hψsmall
      have hmemU : ((Γ.stableGraph σ m).2, tail) ∈ U :=
        hpair_mem _ _ hσm (lt_of_le_of_lt htail_norm hψsmall)
      exact (hUiff _ hmemU).mp
        ((Γ.orbitEquationMap_eq_zero_iff _ _).mpr htail_sol)
    have hnorm_le : ∀ m, ‖Γ.stableGraph σ m‖ ≤ 2 * |(Γ.stableGraph σ m).2| := by
      intro m
      have hσm : |(Γ.stableGraph σ m).2| < rψ :=
        lt_of_le_of_lt ((norm_snd_le _).trans
          ((Γ.stableGraph σ).norm_coe_le_norm m)) hψsmall
      calc ‖Γ.stableGraph σ m‖
          = ‖(ofNormedAddCommGroupDiscrete (fun k => Γ.stableGraph σ (m + k))
              ‖Γ.stableGraph σ‖
              (fun k => (Γ.stableGraph σ).norm_coe_le_norm (m + k))) 0‖ := rfl
        _ ≤ ‖Γ.stableGraph ((Γ.stableGraph σ m).2)‖ := by
            rw [← htail m]
            exact (Γ.stableGraph _).norm_coe_le_norm 0
        _ ≤ 2 * |(Γ.stableGraph σ m).2| := hgraph_le _ hσm
    refine ⟨?_, hnorm_le⟩
    intro m
    induction m with
    | zero =>
        rw [pow_zero, one_mul, horbit.1]
    | succ m ih =>
        have hstep : (Γ.stableGraph σ (m + 1)).2 =
            Γ.ν * (Γ.stableGraph σ m).2 + (Γ.r (Γ.stableGraph σ m)).2 :=
          (congrArg Prod.snd (horbit.2 m)).trans rfl
        have hrb : |(Γ.r (Γ.stableGraph σ m)).2| ≤
            (1 - Γ.ν) / 4 * ‖Γ.stableGraph σ m‖ := by
          have hz : ‖Γ.stableGraph σ m‖ ≤ ρν / 2 := by
            have h1 : ‖Γ.stableGraph σ m‖ ≤ ‖Γ.stableGraph σ‖ :=
              (Γ.stableGraph σ).norm_coe_le_norm m
            have h2 : rψ ≤ ρν / 2 := (min_le_right _ _).trans (min_le_right _ _)
            linarith [lt_of_le_of_lt h1 hψsmall]
          exact (norm_snd_le _).trans (Γ.norm_r_le hband hz)
        have hchain : |(Γ.stableGraph σ (m + 1)).2| ≤ θ * |(Γ.stableGraph σ m).2| := by
          rw [hstep]
          calc |Γ.ν * (Γ.stableGraph σ m).2 + (Γ.r (Γ.stableGraph σ m)).2|
              ≤ |Γ.ν * (Γ.stableGraph σ m).2| + |(Γ.r (Γ.stableGraph σ m)).2| := by
                simpa [Real.norm_eq_abs] using
                  norm_add_le (Γ.ν * (Γ.stableGraph σ m).2)
                    ((Γ.r (Γ.stableGraph σ m)).2)
            _ ≤ Γ.ν * |(Γ.stableGraph σ m).2| +
                (1 - Γ.ν) / 4 * (2 * |(Γ.stableGraph σ m).2|) := by
                apply add_le_add
                · rw [abs_mul, abs_of_nonneg Γ.ν_pos.le]
                · exact hrb.trans (mul_le_mul_of_nonneg_left (hnorm_le m) hεν.le)
            _ = θ * |(Γ.stableGraph σ m).2| := by rw [hθdef]; ring
        calc |(Γ.stableGraph σ (m + 1)).2| ≤ θ * |(Γ.stableGraph σ m).2| := hchain
          _ ≤ θ * (θ ^ m * |σ|) := mul_le_mul_of_nonneg_left ih hθ0
          _ = θ ^ (m + 1) * |σ| := by ring
  -- assemble the data
  -- the orbit of a curve point is the solution sequence
  have horbit_iter : ∀ σ : ℝ, |σ| < ε →
      ∀ n, Γ.map^[n] (curve σ) = Γ.stableGraph σ n := by
    intro σ hσε
    have hσsol : Γ.IsGreenSolution σ (Γ.stableGraph σ) := by
      apply hεsol
      rw [dist_zero_right, Real.norm_eq_abs]
      exact lt_of_lt_of_le hσε (min_le_left _ _)
    have hcurve_eq : curve σ = Γ.stableGraph σ 0 :=
      Prod.ext rfl hσsol.orbit.1.symm
    intro n
    rw [hcurve_eq]
    exact Γ.iterate_eq_of_orbit hσsol.orbit.2 n
  refine ⟨⟨ε, ρ, curve, hεpos, hρpos, hρltε, fun σ => rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- ContDiffOn
    intro σ hσ
    have hσcd : |σ| < εcd := by
      rw [mem_Ioo] at hσ
      have : |σ| < ε := abs_lt.mpr hσ
      exact lt_of_lt_of_le this ((min_le_right _ _).trans (min_le_left _ _))
    have hψ : ContDiffAt ℝ 1 Γ.stableGraph σ :=
      hεcd (by rwa [dist_zero_right, Real.norm_eq_abs])
    have hval : ContDiffAt ℝ 1 (fun τ => Γ.stableGraph τ 0) σ := by
      have h : (fun τ => Γ.stableGraph τ 0) =
          ⇑(BoundedContinuousFunction.evalCLM (𝕜 := ℝ) (0 : ℕ)) ∘
            Γ.stableGraph := rfl
      rw [h]
      exact ((BoundedContinuousFunction.evalCLM (𝕜 := ℝ)
        (0 : ℕ)).contDiff.contDiffAt).comp σ hψ
    have hfst : ContDiffAt ℝ 1 (fun τ => (Γ.stableGraph τ 0).1) σ := by
      have h : (fun τ => (Γ.stableGraph τ 0).1) =
          ⇑(ContinuousLinearMap.fst ℝ ℝ ℝ) ∘ (fun τ => Γ.stableGraph τ 0) := rfl
      rw [h]
      exact ((ContinuousLinearMap.fst ℝ ℝ ℝ).contDiff.contDiffAt).comp σ hval
    exact (hfst.prodMk contDiffAt_id).contDiffWithinAt
  · -- curve_zero
    rw [hcurvedef]
    have h : Γ.stableGraph 0 0 = (0 : ℝ × ℝ) := by
      rw [Γ.stableGraph_zero]
      rfl
    simp [h]
  · -- tangency
    have hψF : HasFDerivAt Γ.stableGraph Γ.contractInjection 0 :=
      Γ.stableGraph_hasStrictFDerivAt.hasFDerivAt
    have hval : HasFDerivAt (fun τ => Γ.stableGraph τ 0)
        ((BoundedContinuousFunction.evalCLM (𝕜 := ℝ) (0 : ℕ)).comp
          Γ.contractInjection) 0 := by
      have h : (fun τ => Γ.stableGraph τ 0) =
          ⇑(BoundedContinuousFunction.evalCLM (𝕜 := ℝ) (0 : ℕ)) ∘
            Γ.stableGraph := rfl
      rw [h]
      exact ((BoundedContinuousFunction.evalCLM (𝕜 := ℝ)
        (0 : ℕ)).hasFDerivAt).comp 0 hψF
    have hfst : HasFDerivAt (fun τ => (Γ.stableGraph τ 0).1)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
          ((BoundedContinuousFunction.evalCLM (𝕜 := ℝ) (0 : ℕ)).comp
            Γ.contractInjection)) 0 := by
      have h : (fun τ => (Γ.stableGraph τ 0).1) =
          ⇑(ContinuousLinearMap.fst ℝ ℝ ℝ) ∘ (fun τ => Γ.stableGraph τ 0) := rfl
      rw [h]
      exact ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt).comp 0 hval
    have hd1 := hfst.hasDerivAt
    have hvalue : ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
        ((BoundedContinuousFunction.evalCLM (𝕜 := ℝ) (0 : ℕ)).comp
          Γ.contractInjection)) 1 = 0 := by
      simp [contractInjection_apply]
    rw [hvalue] at hd1
    exact hd1.prodMk (hasDerivAt_id 0)
  · -- orbit convergence
    intro σ hσ
    rw [mem_Ioo] at hσ
    have hσε : |σ| < ε := abs_lt.mpr hσ
    obtain ⟨hcontract, hnorm_le⟩ := hdecay σ hσε
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbound : ∀ n, ‖Γ.map^[n] (curve σ)‖ ≤ 2 * |σ| * θ ^ n := by
      intro n
      rw [horbit_iter σ hσε n]
      calc ‖Γ.stableGraph σ n‖ ≤ 2 * |(Γ.stableGraph σ n).2| := hnorm_le n
        _ ≤ 2 * (θ ^ n * |σ|) :=
            mul_le_mul_of_nonneg_left (hcontract n) (by norm_num)
        _ = 2 * |σ| * θ ^ n := by ring
    have hgeom : Tendsto (fun n : ℕ => 2 * |σ| * θ ^ n) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).const_mul (2 * |σ|)
      simpa using this
    exact squeeze_zero (fun n => norm_nonneg _) hbound hgeom
  · -- uniform smallness of curve orbits
    intro σ hσ n
    rw [mem_Ioo] at hσ
    have hσε : |σ| < ε := abs_lt.mpr hσ
    obtain ⟨hcontract, hnorm_le⟩ := hdecay σ hσε
    rw [horbit_iter σ hσε n]
    calc ‖Γ.stableGraph σ n‖ ≤ 2 * |(Γ.stableGraph σ n).2| := hnorm_le n
      _ ≤ 2 * (θ ^ n * |σ|) :=
          mul_le_mul_of_nonneg_left (hcontract n) (by norm_num)
      _ ≤ 2 * (1 * |σ|) := by
          have hpow : θ ^ n ≤ 1 := pow_le_one₀ hθ0 hθ1.le
          have := mul_le_mul_of_nonneg_right hpow (abs_nonneg σ)
          linarith
      _ = 2 * |σ| := by ring
  · -- staying orbits lie on the graph
    intro z hz
    have hz0 : ‖z‖ ≤ ρ := by simpa using hz 0
    have hz2 : |z.2| ≤ ρ := (norm_snd_le z).trans hz0
    set x : SeqPair := ofNormedAddCommGroupDiscrete
      (fun n => Γ.map^[n] z) ρ hz with hxdef
    have hx_apply : ∀ n, x n = Γ.map^[n] z := fun n => rfl
    have hx_sol : Γ.IsGreenSolution z.2 x := by
      apply isGreenSolution_of_orbit
      · rw [hx_apply 0]
        rfl
      · intro n
        rw [hx_apply (n + 1), hx_apply n, Function.iterate_succ_apply']
    have hxnorm : ‖x‖ ≤ ρ := (norm_le hρpos.le).mpr fun n => hz n
    have hρrψ : ρ < rψ := by
      have h2 : 0 < min ε rψ := lt_min hεpos hrψpos
      calc ρ = min ε rψ / 2 := rfl
        _ < min ε rψ := by linarith
        _ ≤ rψ := min_le_right _ _
    have hmemU : (z.2, x) ∈ U :=
      hpair_mem _ _ (lt_of_le_of_lt hz2 hρrψ) (lt_of_le_of_lt hxnorm hρrψ)
    have huniq : Γ.stableGraph z.2 = x :=
      (hUiff _ hmemU).mp ((Γ.orbitEquationMap_eq_zero_iff _ _).mpr hx_sol)
    have hx0 : Γ.stableGraph z.2 0 = z := by
      rw [huniq]
      rfl
    constructor
    · rw [mem_Ioo]
      exact abs_lt.mp (lt_of_le_of_lt hz2 hρltε)
    · exact Prod.ext (by rw [hcurvedef]; exact (congrArg Prod.fst hx0).symm) rfl

end PlanarHyperbolicGerm
end PaperII
end CivicAlignment

#print axioms CivicAlignment.PaperII.PlanarHyperbolicGerm.exists_stableCurveData
