/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.Basic

/-!
# Paper III: exact scalar gain ceilings

This file formalizes the two affine recursions in `prop:ceiling`.  In addition
to locating each unit-multiplier threshold, it treats all three regimes:
convergence below the threshold, linear divergence at the threshold, and
geometric divergence above it.
-/

namespace CivicAlignment.PaperIII

open Filter Set Topology

/-! ## The two capture recursions -/

/-- The full-capture multiplier of the portfolio stock recursion. -/
def portfolioCaptureMultiplier (lambda₀ g : ℝ) : ℝ :=
  1 - lambda₀ + g

/-- The portfolio stock path at full capture. -/
def portfolioCapturePath (lambda₀ g I D₀ : ℝ) : ℕ → ℝ :=
  arithGeom (portfolioCaptureMultiplier lambda₀ g) I D₀

/-- The finite full-capture portfolio stock below the gain ceiling. -/
noncomputable def portfolioCaptureStationary (lambda₀ g I : ℝ) : ℝ :=
  I / (lambda₀ - g)

/-- The full-capture multiplier of the companion amplitude recursion. -/
def amplitudeCaptureMultiplier (η e ζ : ℝ) : ℝ :=
  1 - η * e + ζ

/-- The companion amplitude path at full capture. -/
def amplitudeCapturePath (η e ζ injection x₀ : ℝ) : ℕ → ℝ :=
  arithGeom (amplitudeCaptureMultiplier η e ζ) injection x₀

/-- The finite full-capture companion amplitude below its gain ceiling. -/
noncomputable def amplitudeCaptureStationary (η e ζ injection : ℝ) : ℝ :=
  injection / (η * e - ζ)

/-! ## Affine-recursion facts used in both models -/

/-- At multiplier one, an arithmetic-geometric sequence grows exactly linearly. -/
theorem arithGeom_one_eq_linear (b u₀ : ℝ) (n : ℕ) :
    arithGeom 1 b u₀ n = u₀ + (n : ℝ) * b := by
  rw [arithGeom_eq_add_sum]
  simp
  ring

/-- A positive injection makes the unit-multiplier recursion diverge to infinity. -/
theorem tendsto_arithGeom_one_atTop {b u₀ : ℝ} (hb : 0 < b) :
    Tendsto (arithGeom 1 b u₀) atTop atTop := by
  have hlinear : Tendsto (fun n : ℕ ↦ b * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hb
  have hadd : Tendsto (fun n : ℕ ↦ u₀ + b * (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop u₀ hlinear
  apply hadd.congr'
  filter_upwards [] with n
  rw [arithGeom_one_eq_linear]
  ring

/-- Above multiplier one, a positive-injection affine recursion diverges. -/
theorem tendsto_arithGeom_supercritical {a b u₀ : ℝ}
    (ha : 1 < a) (hb : 0 < b) (hu₀ : 0 ≤ u₀) :
    Tendsto (arithGeom a b u₀) atTop atTop := by
  apply tendsto_arithGeom_atTop_of_one_lt ha
  have hdenominator : 1 - a < 0 := sub_neg.mpr ha
  have hratio : b / (1 - a) < 0 := div_neg_of_pos_of_neg hb hdenominator
  exact hratio.trans_le hu₀

/-- The successive-term ratio of a supercritical affine recursion tends to its multiplier. -/
theorem tendsto_arithGeom_supercritical_ratio {a b u₀ : ℝ}
    (ha : 1 < a) (hb : 0 < b) (hu₀ : 0 ≤ u₀) :
    Tendsto (fun n ↦ arithGeom a b u₀ (n + 1) / arithGeom a b u₀ n)
      atTop (nhds a) := by
  have htop : Tendsto (arithGeom a b u₀) atTop atTop :=
    tendsto_arithGeom_supercritical ha hb hu₀
  have hinv : Tendsto (fun n ↦ (arithGeom a b u₀ n)⁻¹) atTop (nhds 0) :=
    htop.inv_tendsto_atTop
  have herror : Tendsto (fun n ↦ b * (arithGeom a b u₀ n)⁻¹) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hinv
  have hsum : Tendsto (fun n ↦ a + b * (arithGeom a b u₀ n)⁻¹)
      atTop (nhds a) := by
    simpa only [add_zero] using tendsto_const_nhds.add herror
  apply hsum.congr'
  filter_upwards [htop.eventually_gt_atTop 0] with n hn
  rw [arithGeom_succ]
  field_simp [hn.ne']

/-- With nonnegative multiplier and initial value, a positive-injection affine
recursion has a finite real limit exactly below multiplier one. -/
theorem arithGeom_hasFiniteLimit_iff {a b u₀ : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hu₀ : 0 ≤ u₀) :
    (∃ L : ℝ, Tendsto (arithGeom a b u₀) atTop (nhds L)) ↔ a < 1 := by
  constructor
  · rintro ⟨L, hL⟩
    by_contra hnot
    have hone_le : 1 ≤ a := le_of_not_gt hnot
    rcases hone_le.eq_or_lt with ha_one | ha_super
    · subst a
      exact not_tendsto_nhds_of_tendsto_atTop
        (tendsto_arithGeom_one_atTop hb) L hL
    · exact not_tendsto_nhds_of_tendsto_atTop
        (tendsto_arithGeom_supercritical ha_super hb hu₀) L hL
  · intro halt
    exact ⟨b / (1 - a), tendsto_affineRecursion a b u₀ ha halt⟩

/-! ## Stationary-value behavior at the ceiling -/

/-- The finite portfolio fixed point is strictly increasing in gain. -/
theorem portfolioCaptureStationary_strictMonoOn {lambda₀ I : ℝ} (hI : 0 < I) :
    StrictMonoOn (fun g ↦ portfolioCaptureStationary lambda₀ g I) (Iio lambda₀) := by
  intro g₁ hg₁ g₂ hg₂ hg
  have hdenominator₁ : 0 < lambda₀ - g₁ := sub_pos.mpr hg₁
  have hdenominator₂ : 0 < lambda₀ - g₂ := sub_pos.mpr hg₂
  simp only [portfolioCaptureStationary]
  apply (div_lt_div_iff₀ hdenominator₁ hdenominator₂).2
  exact mul_lt_mul_of_pos_left (by linarith) hI

/-- The finite portfolio fixed point tends to infinity as gain approaches its ceiling. -/
theorem tendsto_portfolioCaptureStationary_at_ceiling {lambda₀ I : ℝ} (hI : 0 < I) :
    Tendsto (fun g ↦ portfolioCaptureStationary lambda₀ g I)
      (nhdsWithin lambda₀ (Iio lambda₀)) atTop := by
  have hsub : Tendsto (fun g : ℝ ↦ lambda₀ - g)
      (nhdsWithin lambda₀ (Iio lambda₀)) (nhdsWithin 0 (Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hcontinuous : Tendsto (fun g : ℝ ↦ lambda₀ - g) (nhds lambda₀) (nhds 0) := by
        simpa only [id_eq, sub_self] using
          ((tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ lambda₀) (nhds lambda₀) (nhds lambda₀)).sub
            tendsto_id)
      exact hcontinuous.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with g hg
      exact sub_pos.mpr (show g < lambda₀ from hg)
  have hinv : Tendsto (fun g : ℝ ↦ (lambda₀ - g)⁻¹)
      (nhdsWithin lambda₀ (Iio lambda₀)) atTop :=
    tendsto_inv_nhdsGT_zero.comp hsub
  simpa only [portfolioCaptureStationary, div_eq_mul_inv] using
    Tendsto.const_mul_atTop hI hinv

/-- The finite companion-amplitude fixed point also blows up at its ceiling. -/
theorem tendsto_amplitudeCaptureStationary_at_ceiling {η e injection : ℝ}
    (hinjection : 0 < injection) :
    Tendsto (fun ζ ↦ amplitudeCaptureStationary η e ζ injection)
      (nhdsWithin (η * e) (Iio (η * e))) atTop := by
  simpa only [amplitudeCaptureStationary, portfolioCaptureStationary] using
    (tendsto_portfolioCaptureStationary_at_ceiling
      (lambda₀ := η * e) (I := injection) hinjection)

/-! ## The proposition's combined statement -/

/-- The exact claims packaged by Paper III's scalar ceiling proposition. -/
structure GainCeilingConclusions
    (lambda₀ I D₀ η e injection x₀ : ℝ) : Prop where
  portfolio_threshold : ∀ g : ℝ,
    portfolioCaptureMultiplier lambda₀ g < 1 ↔ g < lambda₀
  portfolio_finite_iff : ∀ g : ℝ, 0 ≤ g →
    ((∃ L : ℝ, Tendsto (portfolioCapturePath lambda₀ g I D₀) atTop (nhds L)) ↔
      g < lambda₀)
  portfolio_stationary_fixed : ∀ {g : ℝ}, g < lambda₀ →
    portfolioCaptureMultiplier lambda₀ g * portfolioCaptureStationary lambda₀ g I + I =
      portfolioCaptureStationary lambda₀ g I
  portfolio_stationary_strictMono :
    StrictMonoOn (fun g ↦ portfolioCaptureStationary lambda₀ g I) (Iio lambda₀)
  portfolio_stationary_blowup :
    Tendsto (fun g ↦ portfolioCaptureStationary lambda₀ g I)
      (nhdsWithin lambda₀ (Iio lambda₀)) atTop
  portfolio_critical_formula : ∀ n : ℕ,
    portfolioCapturePath lambda₀ lambda₀ I D₀ n = D₀ + (n : ℝ) * I
  portfolio_critical_diverges :
    Tendsto (portfolioCapturePath lambda₀ lambda₀ I D₀) atTop atTop
  portfolio_supercritical_formula : ∀ {g : ℝ}, lambda₀ < g → ∀ n : ℕ,
    portfolioCapturePath lambda₀ g I D₀ n =
      portfolioCaptureMultiplier lambda₀ g ^ n *
          (D₀ - I / (1 - portfolioCaptureMultiplier lambda₀ g)) +
        I / (1 - portfolioCaptureMultiplier lambda₀ g)
  portfolio_supercritical_diverges : ∀ {g : ℝ}, lambda₀ < g →
    Tendsto (portfolioCapturePath lambda₀ g I D₀) atTop atTop
  portfolio_supercritical_rate : ∀ {g : ℝ}, lambda₀ < g →
    Tendsto
      (fun n ↦ portfolioCapturePath lambda₀ g I D₀ (n + 1) /
        portfolioCapturePath lambda₀ g I D₀ n)
      atTop (nhds (portfolioCaptureMultiplier lambda₀ g))
  amplitude_threshold : ∀ ζ : ℝ,
    amplitudeCaptureMultiplier η e ζ < 1 ↔ ζ < η * e
  amplitude_finite_iff : ∀ ζ : ℝ, 0 ≤ ζ →
    ((∃ L : ℝ, Tendsto (amplitudeCapturePath η e ζ injection x₀) atTop (nhds L)) ↔
      ζ < η * e)
  amplitude_stationary_fixed : ∀ {ζ : ℝ}, ζ < η * e →
    amplitudeCaptureMultiplier η e ζ * amplitudeCaptureStationary η e ζ injection +
        injection = amplitudeCaptureStationary η e ζ injection
  amplitude_stationary_blowup :
    Tendsto (fun ζ ↦ amplitudeCaptureStationary η e ζ injection)
      (nhdsWithin (η * e) (Iio (η * e))) atTop
  amplitude_critical_formula : ∀ n : ℕ,
    amplitudeCapturePath η e (η * e) injection x₀ n = x₀ + (n : ℝ) * injection
  amplitude_critical_diverges :
    Tendsto (amplitudeCapturePath η e (η * e) injection x₀) atTop atTop
  amplitude_supercritical_formula : ∀ {ζ : ℝ}, η * e < ζ → ∀ n : ℕ,
    amplitudeCapturePath η e ζ injection x₀ n =
      amplitudeCaptureMultiplier η e ζ ^ n *
          (x₀ - injection / (1 - amplitudeCaptureMultiplier η e ζ)) +
        injection / (1 - amplitudeCaptureMultiplier η e ζ)
  amplitude_supercritical_diverges : ∀ {ζ : ℝ}, η * e < ζ →
    Tendsto (amplitudeCapturePath η e ζ injection x₀) atTop atTop
  amplitude_supercritical_rate : ∀ {ζ : ℝ}, η * e < ζ →
    Tendsto
      (fun n ↦ amplitudeCapturePath η e ζ injection x₀ (n + 1) /
        amplitudeCapturePath η e ζ injection x₀ n)
      atTop (nhds (amplitudeCaptureMultiplier η e ζ))
  fullyDeferent_zero_ceiling : η * 0 = 0
  fullyDeferent_no_nonnegative_stable_gain : ∀ ζ : ℝ, 0 ≤ ζ →
    ¬amplitudeCaptureMultiplier η 0 ζ < 1

/--
Paper III, Proposition 5.1 (`prop:ceiling`), `civic_loops.tex:318`.

At full capture, the portfolio ceiling is exactly `g = λ₀`, while the
companion amplitude ceiling is exactly `ζ = ηe`.  Below either ceiling the
affine path has a finite stationary limit; at the ceiling it grows linearly;
above it, the path diverges geometrically and its successive-term ratio tends
to the asserted multiplier.  Setting the captured type's evidence coupling to
zero makes the amplitude ceiling zero.
-/
theorem gainCeilings
    {lambda₀ I D₀ η e injection x₀ : ℝ}
    (hlambda₀_pos : 0 < lambda₀) (hlambda₀_le_one : lambda₀ ≤ 1)
    (hI : 0 < I) (hD₀ : 0 ≤ D₀)
    (heta : 0 ≤ η) (he : 0 ≤ e) (hetae_le_one : η * e ≤ 1)
    (hinjection : 0 < injection) (hx₀ : 0 ≤ x₀) :
    GainCeilingConclusions lambda₀ I D₀ η e injection x₀ := by
  have hlambda₀_nonneg : 0 ≤ lambda₀ := hlambda₀_pos.le
  have hetae_nonneg : 0 ≤ η * e := mul_nonneg heta he
  constructor
  · intro g
    simp only [portfolioCaptureMultiplier]
    constructor <;> intro h <;> linarith
  · intro g hg
    simp only [portfolioCapturePath]
    have hmultiplier_nonneg : 0 ≤ portfolioCaptureMultiplier lambda₀ g := by
      simp only [portfolioCaptureMultiplier]
      linarith [hlambda₀_nonneg]
    rw [arithGeom_hasFiniteLimit_iff hmultiplier_nonneg hI hD₀]
    simp only [portfolioCaptureMultiplier]
    constructor <;> intro h <;> linarith
  · intro g hg
    have hdenominator : lambda₀ - g ≠ 0 := (sub_pos.mpr hg).ne'
    simp only [portfolioCaptureMultiplier, portfolioCaptureStationary]
    field_simp [hdenominator]
    ring
  · exact portfolioCaptureStationary_strictMonoOn hI
  · exact tendsto_portfolioCaptureStationary_at_ceiling hI
  · intro n
    have hmultiplier : portfolioCaptureMultiplier lambda₀ lambda₀ = 1 := by
      simp only [portfolioCaptureMultiplier]
      ring
    rw [portfolioCapturePath, hmultiplier]
    exact arithGeom_one_eq_linear I D₀ n
  · have hmultiplier : portfolioCaptureMultiplier lambda₀ lambda₀ = 1 := by
      simp only [portfolioCaptureMultiplier]
      ring
    rw [portfolioCapturePath, hmultiplier]
    exact tendsto_arithGeom_one_atTop hI
  · intro g hg n
    simp only [portfolioCapturePath]
    apply arithGeom_eq
    simp only [portfolioCaptureMultiplier]
    linarith
  · intro g hg
    simp only [portfolioCapturePath]
    apply tendsto_arithGeom_supercritical
    · simp only [portfolioCaptureMultiplier]
      linarith
    · exact hI
    · exact hD₀
  · intro g hg
    simp only [portfolioCapturePath]
    apply tendsto_arithGeom_supercritical_ratio
    · simp only [portfolioCaptureMultiplier]
      linarith
    · exact hI
    · exact hD₀
  · intro ζ
    simp only [amplitudeCaptureMultiplier]
    constructor <;> intro h <;> linarith
  · intro ζ hζ
    simp only [amplitudeCapturePath]
    have hmultiplier_nonneg : 0 ≤ amplitudeCaptureMultiplier η e ζ := by
      simp only [amplitudeCaptureMultiplier]
      linarith [hetae_nonneg]
    rw [arithGeom_hasFiniteLimit_iff hmultiplier_nonneg hinjection hx₀]
    simp only [amplitudeCaptureMultiplier]
    constructor <;> intro h <;> linarith
  · intro ζ hζ
    have hdenominator : η * e - ζ ≠ 0 := (sub_pos.mpr hζ).ne'
    simp only [amplitudeCaptureMultiplier, amplitudeCaptureStationary]
    field_simp [hdenominator]
    ring
  · exact tendsto_amplitudeCaptureStationary_at_ceiling hinjection
  · intro n
    have hmultiplier : amplitudeCaptureMultiplier η e (η * e) = 1 := by
      simp only [amplitudeCaptureMultiplier]
      ring
    rw [amplitudeCapturePath, hmultiplier]
    exact arithGeom_one_eq_linear injection x₀ n
  · have hmultiplier : amplitudeCaptureMultiplier η e (η * e) = 1 := by
      simp only [amplitudeCaptureMultiplier]
      ring
    rw [amplitudeCapturePath, hmultiplier]
    exact tendsto_arithGeom_one_atTop hinjection
  · intro ζ hζ n
    simp only [amplitudeCapturePath]
    apply arithGeom_eq
    simp only [amplitudeCaptureMultiplier]
    linarith
  · intro ζ hζ
    simp only [amplitudeCapturePath]
    apply tendsto_arithGeom_supercritical
    · simp only [amplitudeCaptureMultiplier]
      linarith
    · exact hinjection
    · exact hx₀
  · intro ζ hζ
    simp only [amplitudeCapturePath]
    apply tendsto_arithGeom_supercritical_ratio
    · simp only [amplitudeCaptureMultiplier]
      linarith
    · exact hinjection
    · exact hx₀
  · ring
  · intro ζ hζ
    simp only [amplitudeCaptureMultiplier, mul_zero]
    linarith

#print axioms arithGeom_one_eq_linear
#print axioms tendsto_arithGeom_one_atTop
#print axioms tendsto_arithGeom_supercritical
#print axioms tendsto_arithGeom_supercritical_ratio
#print axioms arithGeom_hasFiniteLimit_iff
#print axioms portfolioCaptureStationary_strictMonoOn
#print axioms tendsto_portfolioCaptureStationary_at_ceiling
#print axioms tendsto_amplitudeCaptureStationary_at_ceiling
#print axioms gainCeilings

end CivicAlignment.PaperIII
