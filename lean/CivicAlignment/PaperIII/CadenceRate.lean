/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperIII.SeparatrixLimit

/-!
# Paper III: finite-scale consequences of a separatrix rate certificate

The existing separatrix theorem proves a small-adaptation-rate limit.  This
file states exactly what an additional finite-rate estimate would buy.  It
does not manufacture such an estimate for the nonlinear map.
-/

namespace CivicAlignment.PaperIII

open Filter Set Topology

/-- The rescaled separatrix gap whose limit is the jump-map price. -/
def scaledSeparatrixGap (gap : ℝ → ℝ) (α : ℝ) : ℝ :=
  α * gap α

/-- An error bound for the rescaled gap gives an explicit inverse-cadence
interval for the unscaled gap at that operating rate. -/
theorem separatrixGap_bounds_of_scaled_error
    {gap : ℝ → ℝ} {α κ ε : ℝ} (hα : 0 < α)
    (herror : |scaledSeparatrixGap gap α - κ| ≤ ε) :
    (κ - ε) / α ≤ gap α ∧ gap α ≤ (κ + ε) / α := by
  have hb := (abs_le.mp herror)
  constructor
  · rw [div_le_iff₀ hα]
    simp only [scaledSeparatrixGap] at hb
    nlinarith
  · rw [le_div_iff₀ hα]
    simp only [scaledSeparatrixGap] at hb
    nlinarith

/-- If rescaled-gap errors are controlled at `α` and `α/2`, the deviation
from exact doubling after halving cadence has an explicit finite-scale bound. -/
theorem separatrixGap_halving_error
    {gap : ℝ → ℝ} {α κ ε εHalf : ℝ} (hα : 0 < α)
    (herror : |scaledSeparatrixGap gap α - κ| ≤ ε)
    (herrorHalf :
      |scaledSeparatrixGap gap (α / 2) - κ| ≤ εHalf) :
    |gap (α / 2) - 2 * gap α| ≤ 2 * (εHalf + ε) / α := by
  let difference : ℝ := gap (α / 2) - 2 * gap α
  let halfError : ℝ := scaledSeparatrixGap gap (α / 2) - κ
  let fullError : ℝ := scaledSeparatrixGap gap α - κ
  have hidentity : (α / 2) * difference = halfError - fullError := by
    simp only [difference, halfError, fullError, scaledSeparatrixGap]
    ring
  have hscale : 0 ≤ 2 / α := (div_pos (by norm_num) hα).le
  have htriangle : |halfError - fullError| ≤ |halfError| + |fullError| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le halfError (-fullError)
  calc
    |gap (α / 2) - 2 * gap α| = |difference| := rfl
    _ = |(2 / α) * ((α / 2) * difference)| := by
      congr 1
      field_simp
    _ = (2 / α) * |(α / 2) * difference| := by
      rw [abs_mul, abs_of_nonneg hscale]
    _ = (2 / α) * |halfError - fullError| := by rw [hidentity]
    _ ≤ (2 / α) * (|halfError| + |fullError|) :=
      mul_le_mul_of_nonneg_left htriangle hscale
    _ ≤ (2 / α) * (εHalf + ε) := by
      apply mul_le_mul_of_nonneg_left _ hscale
      exact add_le_add herrorHalf herror
    _ = 2 * (εHalf + ε) / α := by ring

/-- A uniform rate envelope is an additional hypothesis beyond convergence.
It packages the exact missing premise for finite cadence claims. -/
structure SeparatrixRateCertificate
    (gap : ℝ → ℝ) (κ : ℝ) where
  maxRate : ℝ
  maxRate_pos : 0 < maxRate
  errorEnvelope : ℝ → ℝ
  errorEnvelope_nonnegative : ∀ α, 0 ≤ errorEnvelope α
  scaled_error : ∀ α ∈ Set.Ioc (0 : ℝ) maxRate,
    |scaledSeparatrixGap gap α - κ| ≤ errorEnvelope α

/-- A supplied rate certificate specializes the finite inverse-cadence
interval at every registered operating rate. -/
theorem SeparatrixRateCertificate.gap_bounds
    {gap : ℝ → ℝ} {κ : ℝ} (certificate : SeparatrixRateCertificate gap κ)
    {α : ℝ} (hα : α ∈ Set.Ioc (0 : ℝ) certificate.maxRate) :
    (κ - certificate.errorEnvelope α) / α ≤ gap α ∧
      gap α ≤ (κ + certificate.errorEnvelope α) / α :=
  separatrixGap_bounds_of_scaled_error hα.1
    (certificate.scaled_error α hα)

/-- Convergence of the rescaled gap gives the exact eventual inverse-cadence
interval for every fixed positive tolerance, without asserting a convergence
rate. -/
theorem eventually_separatrixGap_bounds_of_tendsto
    {gap : ℝ → ℝ} {κ ε : ℝ} (hε : 0 < ε)
    (hlimit : Tendsto (scaledSeparatrixGap gap)
      (nhdsWithin 0 (Ioi 0)) (nhds κ)) :
    ∀ᶠ α in nhdsWithin 0 (Ioi 0),
      (κ - ε) / α ≤ gap α ∧ gap α ≤ (κ + ε) / α := by
  have herror : ∀ᶠ α in nhdsWithin 0 (Ioi 0),
      |scaledSeparatrixGap gap α - κ| < ε := by
    have hball := hlimit.eventually (Metric.ball_mem_nhds κ hε)
    filter_upwards [hball] with α hα
    simpa [Metric.mem_ball, Real.dist_eq] using hα
  filter_upwards [self_mem_nhdsWithin, herror] with α hα herrorα
  exact separatrixGap_bounds_of_scaled_error hα (le_of_lt herrorα)

/-- The same rescaled convergence controls the finite discrepancy from exact
doubling after cadence is halved.  The assertion is eventual for each fixed
tolerance; it does not supply an operating-scale cutoff. -/
theorem eventually_separatrixGap_halving_error_of_tendsto
    {gap : ℝ → ℝ} {κ ε : ℝ} (hε : 0 < ε)
    (hlimit : Tendsto (scaledSeparatrixGap gap)
      (nhdsWithin 0 (Ioi 0)) (nhds κ)) :
    ∀ᶠ α in nhdsWithin 0 (Ioi 0),
      |gap (α / 2) - 2 * gap α| ≤ 4 * ε / α := by
  let F : Filter ℝ := nhdsWithin 0 (Ioi 0)
  have hhalf : Tendsto (fun α : ℝ ↦ α / 2) F F := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hcontinuous : ContinuousAt (fun α : ℝ ↦ α / 2) 0 := by
        fun_prop
      simpa only [zero_div] using
        hcontinuous.tendsto.mono_left (nhdsWithin_le_nhds : F ≤ nhds 0)
    · filter_upwards [self_mem_nhdsWithin] with α hα
      change 0 < α at hα
      exact div_pos hα (by norm_num)
  have hfullError : ∀ᶠ α in F,
      |scaledSeparatrixGap gap α - κ| ≤ ε := by
    have hball := hlimit.eventually (Metric.ball_mem_nhds κ hε)
    filter_upwards [hball] with α hα
    exact le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using hα)
  have hhalfError : ∀ᶠ α in F,
      |scaledSeparatrixGap gap (α / 2) - κ| ≤ ε := by
    have hball := (hlimit.comp hhalf).eventually
      (Metric.ball_mem_nhds κ hε)
    filter_upwards [hball] with α hα
    exact le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using hα)
  filter_upwards [self_mem_nhdsWithin, hfullError, hhalfError] with
      α hα hfullα hhalfα
  convert separatrixGap_halving_error hα hfullα hhalfα using 1
  ring

/-- The actual loop separatrix stock excess at a registered initial policy. -/
noncomputable def loopSeparatrixGap (p : LoopParams) (β₀ α : ℝ) : ℝ :=
  separatrixStock (withAdaptationRate p α) β₀ - p.stationaryStock β₀

/-- The proved separatrix limit specializes to an eventual two-sided
inverse-cadence interval at every positive tolerance. -/
theorem loopSeparatrixGap_eventually_inverse_bounds
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀)
    (threshold : PaperII.ThresholdAssumption p) {β₀ ε : ℝ}
    (transit : SaddleBracketingTransit p threshold β₀) (hε : 0 < ε) :
    ∀ᶠ α in nhdsWithin 0 (Ioi 0),
      (jumpSeparatrixScale p threshold.βdagger β₀ - ε) / α ≤
          loopSeparatrixGap p β₀ α ∧
        loopSeparatrixGap p β₀ α ≤
          (jumpSeparatrixScale p threshold.βdagger β₀ + ε) / α := by
  apply eventually_separatrixGap_bounds_of_tendsto hε
  change Tendsto
    (fun α : ℝ ↦ α *
      (separatrixStock (withAdaptationRate p α) β₀ -
        p.stationaryStock β₀))
    (nhdsWithin 0 (Ioi 0))
    (nhds (jumpSeparatrixScale p threshold.βdagger β₀))
  exact separatrixScaleLimit model hgain threshold transit

/-- For the actual loop separatrix, cadence halving differs from exact
doubling by at most `4ε/α` eventually, for every fixed positive `ε`. -/
theorem loopSeparatrixGap_eventually_halving_error
    {p : LoopParams} (model : LoopModelAssumptions p)
    (hgain : p.g < p.lambda₀)
    (threshold : PaperII.ThresholdAssumption p) {β₀ ε : ℝ}
    (transit : SaddleBracketingTransit p threshold β₀) (hε : 0 < ε) :
    ∀ᶠ α in nhdsWithin 0 (Ioi 0),
      |loopSeparatrixGap p β₀ (α / 2) -
          2 * loopSeparatrixGap p β₀ α| ≤ 4 * ε / α := by
  apply eventually_separatrixGap_halving_error_of_tendsto hε
  change Tendsto
    (fun α : ℝ ↦ α *
      (separatrixStock (withAdaptationRate p α) β₀ -
        p.stationaryStock β₀))
    (nhdsWithin 0 (Ioi 0))
    (nhds (jumpSeparatrixScale p threshold.βdagger β₀))
  exact separatrixScaleLimit model hgain threshold transit

#print axioms separatrixGap_bounds_of_scaled_error
#print axioms separatrixGap_halving_error
#print axioms SeparatrixRateCertificate.gap_bounds
#print axioms eventually_separatrixGap_bounds_of_tendsto
#print axioms eventually_separatrixGap_halving_error_of_tendsto
#print axioms loopSeparatrixGap_eventually_inverse_bounds
#print axioms loopSeparatrixGap_eventually_halving_error

end CivicAlignment.PaperIII
