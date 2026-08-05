/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.StableCurve
import CivicAlignment.PaperII.BistabilityTopology
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# The loop map as a planar hyperbolic germ at the interior saddle

Near the interior saddle the policy projection is inactive, so the loop map
agrees with the unclipped polynomial map.  This file records that agreement,
differentiates the unclipped map (the derivative is the printed interior
Jacobian), passes to the explicit eigenbasis of the saddle Jacobian — whose
hyperbolic spectrum `0 < λ₂ < 1 < λ₁` is already kernel-proved — and packages
the conjugated map as a `PlanarHyperbolicGerm`, the input to Irwin's theorem
in `PaperII/StableCurve.lean`.  The germ's remainder is polynomial, so all
smoothness hypotheses are explicit.

`PaperII/StableManifold.lean` combines the resulting stable curve with the
internally proved order structure of the stable set.
-/

namespace CivicAlignment
namespace PaperII

open BoundedContinuousFunction Metric Set Filter Topology LoopParams

variable {p : LoopParams}

/-! ## The unclipped map and its derivative -/

/-- The unclipped simultaneous loop map: the raw gradient step with no
policy projection. -/
def unclippedLoopMap (p : LoopParams) (x : LoopState) : LoopState :=
  (x.1 + p.α * p.gradU x.1 x.2, p.stockStep x.1 x.2)

/-- A constant-coefficient scalar row on the plane. -/
noncomputable def rowCLM (a₁ a₂ : ℝ) : LoopState →L[ℝ] ℝ :=
  a₁ • ContinuousLinearMap.fst ℝ ℝ ℝ + a₂ • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem rowCLM_apply (a₁ a₂ : ℝ) (y : LoopState) :
    rowCLM a₁ a₂ y = a₁ * y.1 + a₂ * y.2 := by
  simp [rowCLM]

/-- The planar constant-coefficient operator with the given entries. -/
noncomputable def entriesCLM (a₁ a₂ b₁ b₂ : ℝ) : LoopState →L[ℝ] LoopState :=
  (rowCLM a₁ a₂).prod (rowCLM b₁ b₂)

@[simp] theorem entriesCLM_apply (a₁ a₂ b₁ b₂ : ℝ) (y : LoopState) :
    entriesCLM a₁ a₂ b₁ b₂ y = (a₁ * y.1 + a₂ * y.2, b₁ * y.1 + b₂ * y.2) := by
  simp [entriesCLM]

/-- The derivative field of the unclipped map: the printed interior
Jacobian, as an operator. -/
noncomputable def unclippedDeriv (p : LoopParams) (x : LoopState) :
    LoopState →L[ℝ] LoopState :=
  entriesCLM (1 - 2 * p.α * p.c ^ 2 * x.2) (2 * p.α * p.c * (1 - p.c * x.1))
    (p.sSlope x.1 * x.2) (p.s x.1 + p.g)

/-- The unclipped map is differentiable everywhere, with derivative the
interior Jacobian. -/
theorem unclippedLoopMap_hasFDerivAt (x : LoopState) :
    HasFDerivAt (unclippedLoopMap p) (unclippedDeriv p x) x := by
  have hfst : HasFDerivAt (fun y : LoopState => y.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) x := hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun y : LoopState => y.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) x := hasFDerivAt_snd
  have hmul : HasFDerivAt (fun y : LoopState => y.1 * y.2)
      (x.1 • ContinuousLinearMap.snd ℝ ℝ ℝ +
        x.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) x := hfst.mul hsnd
  -- the policy component
  have h2 : HasFDerivAt (fun y : LoopState => 2 * p.α * p.c * y.2)
      ((2 * p.α * p.c) • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    hsnd.const_mul _
  have h3 : HasFDerivAt (fun y : LoopState => 2 * p.α * p.c ^ 2 * (y.1 * y.2))
      ((2 * p.α * p.c ^ 2) • (x.1 • ContinuousLinearMap.snd ℝ ℝ ℝ +
        x.2 • ContinuousLinearMap.fst ℝ ℝ ℝ)) x :=
    hmul.const_mul _
  have h5 := hfst.add ((h2.sub h3).const_add (p.α * (-p.v)))
  have h1clm : ContinuousLinearMap.fst ℝ ℝ ℝ +
      ((2 * p.α * p.c) • ContinuousLinearMap.snd ℝ ℝ ℝ -
        (2 * p.α * p.c ^ 2) • (x.1 • ContinuousLinearMap.snd ℝ ℝ ℝ +
          x.2 • ContinuousLinearMap.fst ℝ ℝ ℝ)) =
      rowCLM (1 - 2 * p.α * p.c ^ 2 * x.2) (2 * p.α * p.c * (1 - p.c * x.1)) := by
    apply ContinuousLinearMap.ext
    intro y
    simp only [rowCLM, _root_.add_apply,
      _root_.sub_apply, FunLike.coe_smul,
      Pi.smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_eq_mul]
    ring
  rw [h1clm] at h5
  have h1 : HasFDerivAt (fun y : LoopState => (unclippedLoopMap p y).1)
      (rowCLM (1 - 2 * p.α * p.c ^ 2 * x.2)
        (2 * p.α * p.c * (1 - p.c * x.1))) x := by
    apply h5.congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro y
    simp only [unclippedLoopMap, LoopParams.gradU, Pi.sub_apply, Pi.add_apply]
    ring
  -- the stock component
  have hs1 : HasFDerivAt (fun y : LoopState => p.s y.1)
      ((p.sSlope x.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) x :=
    (hasDerivAt_s p x.1).comp_hasFDerivAt x hfst
  have h6 := ((hs1.mul hsnd).add (hsnd.const_mul p.g)).add_const p.I
  have h2clm : (p.s x.1) • ContinuousLinearMap.snd ℝ ℝ ℝ +
      x.2 • ((p.sSlope x.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) +
      p.g • ContinuousLinearMap.snd ℝ ℝ ℝ =
      rowCLM (p.sSlope x.1 * x.2) (p.s x.1 + p.g) := by
    apply ContinuousLinearMap.ext
    intro y
    simp only [rowCLM, _root_.add_apply,
      FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
    ring
  rw [h2clm] at h6
  have h2' : HasFDerivAt (fun y : LoopState => (unclippedLoopMap p y).2)
      (rowCLM (p.sSlope x.1 * x.2) (p.s x.1 + p.g)) x := by
    apply h6.congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro y
    simp only [unclippedLoopMap, LoopParams.stockStep, Pi.add_apply,
      Pi.mul_apply]
    ring
  exact h1.prodMk h2'

/-- The derivative field of the unclipped map is continuous. -/
theorem continuous_unclippedDeriv : Continuous (unclippedDeriv p) := by
  have hrow : ∀ (c₁ c₂ : LoopState → ℝ), Continuous c₁ → Continuous c₂ →
      Continuous (fun x => rowCLM (c₁ x) (c₂ x)) := by
    intro c₁ c₂ h₁ h₂
    simp only [rowCLM]
    exact (h₁.smul continuous_const).add (h₂.smul continuous_const)
  have hsScont : Continuous p.sSlope := by
    have h : p.sSlope = fun β : ℝ =>
        2 * p.η * (1 - p.lambda₀) * (1 - p.η * (1 - β)) := rfl
    rw [h]
    fun_prop
  have hscont : Continuous p.s := by
    have h : p.s = fun β : ℝ =>
        (1 - p.lambda₀) * (1 - p.η * (1 - β)) ^ 2 := rfl
    rw [h]
    fun_prop
  have h₁ : Continuous fun x : LoopState =>
      rowCLM (1 - 2 * p.α * p.c ^ 2 * x.2) (2 * p.α * p.c * (1 - p.c * x.1)) := by
    apply hrow
    · exact continuous_const.sub (continuous_const.mul continuous_snd)
    · exact continuous_const.mul
        (continuous_const.sub (continuous_const.mul continuous_fst))
  have h₂ : Continuous fun x : LoopState =>
      rowCLM (p.sSlope x.1 * x.2) (p.s x.1 + p.g) := by
    apply hrow
    · exact (hsScont.comp continuous_fst).mul continuous_snd
    · exact (hscont.comp continuous_fst).add continuous_const
  have hpair : Continuous fun x : LoopState =>
      ((rowCLM (1 - 2 * p.α * p.c ^ 2 * x.2)
        (2 * p.α * p.c * (1 - p.c * x.1))),
       (rowCLM (p.sSlope x.1 * x.2) (p.s x.1 + p.g))) := h₁.prodMk h₂
  have hiso := (ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ) (E := LoopState)
    (F := ℝ) (G := ℝ) ℝ).continuous
  exact hiso.comp hpair

/-! ## Agreement with the loop map near the saddle -/

/-- The saddle Jacobian. -/
noncomputable def saddleJac (p : LoopParams) (threshold : ThresholdAssumption p) :
    LoopJacobian :=
  interiorLoopJacobian p threshold.βdagger
    (p.stationaryStock threshold.βdagger)

/-- The unclipped map fixes the saddle. -/
theorem unclippedLoopMap_saddle (model : DriftModelAssumptions p)
    (threshold : ThresholdAssumption p) :
    unclippedLoopMap p (saddlePoint p threshold) = saddlePoint p threshold := by
  have hβ : threshold.βdagger ∈ Icc (0 : ℝ) 1 :=
    ⟨threshold.βdagger_mem.1.le, threshold.βdagger_mem.2.le⟩
  have hgrad : p.gradU threshold.βdagger
      (p.stationaryStock threshold.βdagger) = 0 := by
    rw [← G_eq_gradU_stationary]
    exact threshold.G_zero
  have hstock := stationaryStock_fixed model hβ
  simp only [unclippedLoopMap, saddlePoint, hgrad, mul_zero, add_zero]
  rw [hstock]

/-- Near the saddle, the projection is inactive: the loop map agrees with
the unclipped map. -/
theorem eventually_loopMap_eq_unclipped
    (threshold : ThresholdAssumption p) :
    ∀ᶠ x : LoopState in 𝓝 (saddlePoint p threshold),
      p.loopMap x = unclippedLoopMap p x := by
  have hcont : Continuous (fun x : LoopState => x.1 + p.α * p.gradU x.1 x.2) := by
    simp only [LoopParams.gradU]
    fun_prop
  have hq : (saddlePoint p threshold).1 + p.α *
      p.gradU (saddlePoint p threshold).1 (saddlePoint p threshold).2 =
      threshold.βdagger := by
    have hgrad : p.gradU threshold.βdagger
        (p.stationaryStock threshold.βdagger) = 0 := by
      rw [← G_eq_gradU_stationary]
      exact threshold.G_zero
    simp [saddlePoint, hgrad]
  have hmem : (fun x : LoopState => x.1 + p.α * p.gradU x.1 x.2) ⁻¹'
      (Ioo (0 : ℝ) 1) ∈ 𝓝 (saddlePoint p threshold) := by
    apply (isOpen_Ioo.preimage hcont).mem_nhds
    rw [Set.mem_preimage, hq]
    exact threshold.βdagger_mem
  filter_upwards [hmem] with x hx
  have hclip : clipUnit (x.1 + p.α * p.gradU x.1 x.2) =
      x.1 + p.α * p.gradU x.1 x.2 :=
    clipUnit_eq_self ⟨hx.1.le, hx.2.le⟩
  simp only [LoopParams.loopMap, LoopParams.deferenceStep, unclippedLoopMap,
    hclip]

/-! ## The eigenbasis at the saddle -/

section Eigen

/-- The saddle discriminant is nonnegative. -/
theorem saddleJac_discriminant_nonneg (model : DriftModelAssumptions p)
    (ssplus : ConvergentStepAssumption p) (threshold : ThresholdAssumption p) :
    0 ≤ (saddleJac p threshold).discriminant := by
  have hpos := saddleJacobian_entry_pos model ssplus threshold
  exact (saddleJac p threshold).discriminant_nonneg hpos.2.1.le hpos.2.2.1.le

/-- The smaller saddle eigenvalue lies strictly below the policy diagonal
entry. -/
theorem saddle_smallerEigenvalue_lt_a (model : DriftModelAssumptions p)
    (ssplus : ConvergentStepAssumption p) (threshold : ThresholdAssumption p) :
    (saddleJac p threshold).smallerEigenvalue < (saddleJac p threshold).a := by
  set J := saddleJac p threshold with hJ
  have hdisc := saddleJac_discriminant_nonneg model ssplus threshold
  have hpos := saddleJacobian_entry_pos model ssplus threshold
  have hfactor := J.charPoly_eq_mul_eigenvalues hdisc J.a
  have hval : J.charPoly J.a = -(J.b * J.cJ) := by
    simp only [LoopJacobian.charPoly, LoopJacobian.trace, LoopJacobian.det]
    ring
  have hneg : (J.a - J.largerEigenvalue) * (J.a - J.smallerEigenvalue) < 0 := by
    rw [← hfactor, hval]
    have : 0 < J.b * J.cJ := mul_pos hpos.2.1 hpos.2.2.1
    linarith
  have horder := J.smallerEigenvalue_le_largerEigenvalue
  by_contra hnot
  rw [not_lt] at hnot
  have h1 : J.a - J.largerEigenvalue ≤ 0 := by linarith
  have h2 : J.a - J.smallerEigenvalue ≤ 0 := by linarith
  nlinarith [mul_nonneg (neg_nonneg.mpr h1) (neg_nonneg.mpr h2)]

end Eigen

/-! ## The eigenbasis conjugation -/

/-- The determinant of the saddle eigenbasis. -/
noncomputable def eigenDet (p : LoopParams) (threshold : ThresholdAssumption p) : ℝ :=
  (saddleJac p threshold).b *
    ((saddleJac p threshold).smallerEigenvalue -
      (saddleJac p threshold).largerEigenvalue)

/-- Eigencoordinates to ambient displacements: columns are the expanding and
contracting eigenvectors `(b, λᵢ - a)`. -/
noncomputable def eigenBasis (p : LoopParams) (threshold : ThresholdAssumption p) :
    LoopState →L[ℝ] LoopState :=
  entriesCLM (saddleJac p threshold).b (saddleJac p threshold).b
    ((saddleJac p threshold).largerEigenvalue - (saddleJac p threshold).a)
    ((saddleJac p threshold).smallerEigenvalue - (saddleJac p threshold).a)

/-- The inverse change of basis, by Cramer's rule. -/
noncomputable def eigenBasisInv (p : LoopParams)
    (threshold : ThresholdAssumption p) : LoopState →L[ℝ] LoopState :=
  entriesCLM
    (((saddleJac p threshold).smallerEigenvalue - (saddleJac p threshold).a) /
      eigenDet p threshold)
    (-(saddleJac p threshold).b / eigenDet p threshold)
    (-((saddleJac p threshold).largerEigenvalue - (saddleJac p threshold).a) /
      eigenDet p threshold)
    ((saddleJac p threshold).b / eigenDet p threshold)

/-- The eigenbasis determinant does not vanish at a hyperbolic saddle. -/
theorem eigenDet_ne_zero (model : DriftModelAssumptions p)
    (ssplus : ConvergentStepAssumption p) (threshold : ThresholdAssumption p) :
    eigenDet p threshold ≠ 0 := by
  have hpos := saddleJacobian_entry_pos model ssplus threshold
  have hlarge := saddle_largerEigenvalue_gt_one model ssplus threshold
  have hsmall := saddle_smallerEigenvalue_mem_Ioo_zero_one model ssplus threshold
  simp only at hpos hlarge hsmall
  have hlt : (saddleJac p threshold).smallerEigenvalue -
      (saddleJac p threshold).largerEigenvalue < 0 := by
    have h1 : (saddleJac p threshold).smallerEigenvalue < 1 := hsmall.2
    have h2 : (1 : ℝ) < (saddleJac p threshold).largerEigenvalue := hlarge
    simp only [saddleJac]
    simp only [saddleJac] at h1 h2
    linarith
  have hb : 0 < (saddleJac p threshold).b := by
    simpa [saddleJac] using hpos.2.1
  simp only [eigenDet]
  exact mul_ne_zero (ne_of_gt hb) (ne_of_lt hlt)

/-- Cramer left inverse. -/
theorem eigenBasisInv_eigenBasis (model : DriftModelAssumptions p)
    (ssplus : ConvergentStepAssumption p) (threshold : ThresholdAssumption p)
    (z : LoopState) :
    eigenBasisInv p threshold (eigenBasis p threshold z) = z := by
  have hΔ := eigenDet_ne_zero model ssplus threshold
  simp only [eigenBasis, eigenBasisInv, entriesCLM_apply] at *
  refine Prod.ext ?_ ?_ <;>
    (field_simp
     simp only [eigenDet] at *
     field_simp
     ring)

/-- Cramer right inverse. -/
theorem eigenBasis_eigenBasisInv (model : DriftModelAssumptions p)
    (ssplus : ConvergentStepAssumption p) (threshold : ThresholdAssumption p)
    (w : LoopState) :
    eigenBasis p threshold (eigenBasisInv p threshold w) = w := by
  have hΔ := eigenDet_ne_zero model ssplus threshold
  simp only [eigenBasis, eigenBasisInv, entriesCLM_apply] at *
  refine Prod.ext ?_ ?_ <;>
    (field_simp
     simp only [eigenDet] at *
     field_simp
     ring)

/-! ## The two diagonalization identities -/

/-- First diagonalization component: conjugating the Jacobian by the
eigenbasis scales the expanding coordinate by `λ₁`. -/
theorem conj_component_fst (a b cJ d l₁ l₂ w₁ w₂ : ℝ)
    (h₁ : l₁ ^ 2 - (a + d) * l₁ + (a * d - b * cJ) = 0)
    (h₂ : l₂ ^ 2 - (a + d) * l₂ + (a * d - b * cJ) = 0) :
    (l₂ - a) * (a * (b * w₁ + b * w₂) + b * ((l₁ - a) * w₁ + (l₂ - a) * w₂)) -
      b * (cJ * (b * w₁ + b * w₂) + d * ((l₁ - a) * w₁ + (l₂ - a) * w₂)) =
    (b * (l₂ - l₁)) * (l₁ * w₁) := by
  linear_combination (b * w₁) * h₁ + (b * w₂) * h₂

/-- Second diagonalization component: the contracting coordinate scales by
`λ₂`. -/
theorem conj_component_snd (a b cJ d l₁ l₂ w₁ w₂ : ℝ)
    (h₁ : l₁ ^ 2 - (a + d) * l₁ + (a * d - b * cJ) = 0)
    (h₂ : l₂ ^ 2 - (a + d) * l₂ + (a * d - b * cJ) = 0) :
    -(l₁ - a) * (a * (b * w₁ + b * w₂) + b * ((l₁ - a) * w₁ + (l₂ - a) * w₂)) +
      b * (cJ * (b * w₁ + b * w₂) + d * ((l₁ - a) * w₁ + (l₂ - a) * w₂)) =
    (b * (l₂ - l₁)) * (l₂ * w₂) := by
  linear_combination (-(b * w₁)) * h₁ + (-(b * w₂)) * h₂

/-! ## The germ at the saddle -/

/-- The loop map at the interior saddle, conjugated to eigencoordinates, as
a planar hyperbolic germ: the input to Irwin's stable-curve construction. -/
noncomputable def saddleGerm (model : DriftModelAssumptions p)
    (ssplus : ConvergentStepAssumption p) (threshold : ThresholdAssumption p) :
    PlanarHyperbolicGerm where
  μ := (saddleJac p threshold).largerEigenvalue
  ν := (saddleJac p threshold).smallerEigenvalue
  r := fun z => eigenBasisInv p threshold
      (unclippedLoopMap p (saddlePoint p threshold + eigenBasis p threshold z) -
        saddlePoint p threshold) -
    ((saddleJac p threshold).largerEigenvalue * z.1,
      (saddleJac p threshold).smallerEigenvalue * z.2)
  r' := fun z => ((eigenBasisInv p threshold).comp
      ((unclippedDeriv p (saddlePoint p threshold + eigenBasis p threshold z)).comp
        (eigenBasis p threshold))) -
    entriesCLM (saddleJac p threshold).largerEigenvalue 0 0
      (saddleJac p threshold).smallerEigenvalue
  one_lt_μ := by
    have h := saddle_largerEigenvalue_gt_one model ssplus threshold
    simpa [saddleJac] using h
  ν_pos := by
    have h := saddle_smallerEigenvalue_mem_Ioo_zero_one model ssplus threshold
    simp only at h
    simpa [saddleJac] using h.1
  ν_lt_one := by
    have h := saddle_smallerEigenvalue_mem_Ioo_zero_one model ssplus threshold
    simp only at h
    simpa [saddleJac] using h.2
  r_hasFDerivAt := by
    intro z
    have haff : HasFDerivAt
        (fun w : LoopState => saddlePoint p threshold + eigenBasis p threshold w)
        (eigenBasis p threshold) z :=
      (eigenBasis p threshold).hasFDerivAt.const_add _
    have hmid := (unclippedLoopMap_hasFDerivAt (p := p)
      (saddlePoint p threshold + eigenBasis p threshold z)).comp z haff
    have hsub := hmid.sub_const (saddlePoint p threshold)
    have hout := (eigenBasisInv p threshold).hasFDerivAt.comp z hsub
    have hlin : HasFDerivAt
        (fun w : LoopState => ((saddleJac p threshold).largerEigenvalue * w.1,
          (saddleJac p threshold).smallerEigenvalue * w.2))
        (entriesCLM (saddleJac p threshold).largerEigenvalue 0 0
          (saddleJac p threshold).smallerEigenvalue) z := by
      apply (entriesCLM (saddleJac p threshold).largerEigenvalue 0 0
        (saddleJac p threshold).smallerEigenvalue).hasFDerivAt.congr_of_eventuallyEq
      apply Filter.Eventually.of_forall
      intro w
      simp [entriesCLM_apply]
    exact hout.sub hlin
  r'_continuous := by
    have h1 : Continuous fun z : LoopState =>
        unclippedDeriv p (saddlePoint p threshold + eigenBasis p threshold z) :=
      continuous_unclippedDeriv.comp
        (continuous_const.add (eigenBasis p threshold).continuous)
    have h2 : Continuous fun z : LoopState =>
        (unclippedDeriv p
          (saddlePoint p threshold + eigenBasis p threshold z)).comp
          (eigenBasis p threshold) :=
      h1.clm_comp continuous_const
    have h3 : Continuous fun z : LoopState =>
        (eigenBasisInv p threshold).comp
          ((unclippedDeriv p
            (saddlePoint p threshold + eigenBasis p threshold z)).comp
            (eigenBasis p threshold)) :=
      continuous_const.clm_comp h2
    exact h3.sub continuous_const
  r_zero := by
    have h0 : eigenBasis p threshold (0 : LoopState) = 0 := map_zero _
    rw [h0, add_zero, unclippedLoopMap_saddle model threshold, sub_self,
      map_zero]
    have h1 : ((saddleJac p threshold).largerEigenvalue * (0 : LoopState).1,
        (saddleJac p threshold).smallerEigenvalue * (0 : LoopState).2) =
        (0 : LoopState) := by
      simp
    rw [h1, sub_zero]
  r'_zero := by
    have hΔ := eigenDet_ne_zero model ssplus threshold
    have hdisc := saddleJac_discriminant_nonneg model ssplus threshold
    have hr₁ : (saddleJac p threshold).largerEigenvalue ^ 2 -
        ((saddleJac p threshold).a + (saddleJac p threshold).d) *
          (saddleJac p threshold).largerEigenvalue +
        ((saddleJac p threshold).a * (saddleJac p threshold).d -
          (saddleJac p threshold).b * (saddleJac p threshold).cJ) = 0 := by
      have h := (saddleJac p threshold).charPoly_largerEigenvalue_eq_zero hdisc
      simpa [LoopJacobian.charPoly, LoopJacobian.trace, LoopJacobian.det]
        using h
    have hr₂ : (saddleJac p threshold).smallerEigenvalue ^ 2 -
        ((saddleJac p threshold).a + (saddleJac p threshold).d) *
          (saddleJac p threshold).smallerEigenvalue +
        ((saddleJac p threshold).a * (saddleJac p threshold).d -
          (saddleJac p threshold).b * (saddleJac p threshold).cJ) = 0 := by
      have h := (saddleJac p threshold).charPoly_smallerEigenvalue_eq_zero hdisc
      simpa [LoopJacobian.charPoly, LoopJacobian.trace, LoopJacobian.det]
        using h
    have h0 : eigenBasis p threshold (0 : LoopState) = 0 := map_zero _
    rw [h0, add_zero]
    have hUD : unclippedDeriv p (saddlePoint p threshold) =
        entriesCLM (saddleJac p threshold).a (saddleJac p threshold).b
          (saddleJac p threshold).cJ (saddleJac p threshold).d := by
      simp only [unclippedDeriv, saddleJac, interiorLoopJacobian, saddlePoint,
        model.no_content_gain, add_zero]
    rw [hUD]
    rw [sub_eq_zero]
    apply ContinuousLinearMap.ext
    intro w
    have happly : ((eigenBasisInv p threshold).comp
        ((entriesCLM (saddleJac p threshold).a (saddleJac p threshold).b
          (saddleJac p threshold).cJ (saddleJac p threshold).d).comp
          (eigenBasis p threshold))) w =
        eigenBasisInv p threshold
          (entriesCLM (saddleJac p threshold).a (saddleJac p threshold).b
            (saddleJac p threshold).cJ (saddleJac p threshold).d
            (eigenBasis p threshold w)) := rfl
    rw [happly]
    simp only [eigenBasis, eigenBasisInv, entriesCLM_apply]
    refine Prod.ext ?_ ?_
    · simp only [eigenDet] at hΔ ⊢
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
        div_eq_iff hΔ]
      linear_combination conj_component_fst (saddleJac p threshold).a
        (saddleJac p threshold).b (saddleJac p threshold).cJ
        (saddleJac p threshold).d (saddleJac p threshold).largerEigenvalue
        (saddleJac p threshold).smallerEigenvalue w.1 w.2 hr₁ hr₂
    · simp only [eigenDet] at hΔ ⊢
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
        div_eq_iff hΔ]
      linear_combination conj_component_snd (saddleJac p threshold).a
        (saddleJac p threshold).b (saddleJac p threshold).cJ
        (saddleJac p threshold).d (saddleJac p threshold).largerEigenvalue
        (saddleJac p threshold).smallerEigenvalue w.1 w.2 hr₁ hr₂

/-- Conjugation identity: the germ map is the unclipped loop map read in
eigencoordinates. -/
theorem saddleGerm_map_conj (model : DriftModelAssumptions p)
    (ssplus : ConvergentStepAssumption p) (threshold : ThresholdAssumption p)
    (z : LoopState) :
    saddlePoint p threshold +
        eigenBasis p threshold ((saddleGerm model ssplus threshold).map z) =
      unclippedLoopMap p (saddlePoint p threshold + eigenBasis p threshold z) := by
  have hmap : (saddleGerm model ssplus threshold).map z =
      eigenBasisInv p threshold
        (unclippedLoopMap p (saddlePoint p threshold + eigenBasis p threshold z) -
          saddlePoint p threshold) := by
    have h1 : ((saddleGerm model ssplus threshold).map z).1 =
        (eigenBasisInv p threshold
          (unclippedLoopMap p
            (saddlePoint p threshold + eigenBasis p threshold z) -
            saddlePoint p threshold)).1 := by
      have hr : ((saddleGerm model ssplus threshold).map z).1 =
          (saddleJac p threshold).largerEigenvalue * z.1 +
            ((eigenBasisInv p threshold
              (unclippedLoopMap p
                (saddlePoint p threshold + eigenBasis p threshold z) -
                saddlePoint p threshold)).1 -
              (saddleJac p threshold).largerEigenvalue * z.1) := rfl
      rw [hr]
      ring
    have h2 : ((saddleGerm model ssplus threshold).map z).2 =
        (eigenBasisInv p threshold
          (unclippedLoopMap p
            (saddlePoint p threshold + eigenBasis p threshold z) -
            saddlePoint p threshold)).2 := by
      have hr : ((saddleGerm model ssplus threshold).map z).2 =
          (saddleJac p threshold).smallerEigenvalue * z.2 +
            ((eigenBasisInv p threshold
              (unclippedLoopMap p
                (saddlePoint p threshold + eigenBasis p threshold z) -
                saddlePoint p threshold)).2 -
              (saddleJac p threshold).smallerEigenvalue * z.2) := rfl
      rw [hr]
      ring
    exact Prod.ext h1 h2
  rw [hmap, eigenBasis_eigenBasisInv model ssplus threshold, add_sub_cancel]

end PaperII
end CivicAlignment

#print axioms CivicAlignment.PaperII.saddleGerm_map_conj
#print axioms CivicAlignment.PaperII.unclippedLoopMap_hasFDerivAt
#print axioms CivicAlignment.PaperII.continuous_unclippedDeriv
#print axioms CivicAlignment.PaperII.eventually_loopMap_eq_unclipped
#print axioms CivicAlignment.PaperII.saddle_smallerEigenvalue_lt_a
#print axioms CivicAlignment.PaperII.eigenBasisInv_eigenBasis
#print axioms CivicAlignment.PaperII.conj_component_fst
