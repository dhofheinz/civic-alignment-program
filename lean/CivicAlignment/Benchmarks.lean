/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.Hysteresis

/-!
# Exact benchmark checks

The papers' decimal benchmark values are represented here by exact rationals.
This file records only mathematical consequences of those values; simulation
counts and fitted statistics remain in the verification batteries.
-/

namespace CivicAlignment

open Set

noncomputable section

namespace PaperII

/-- The Paper II benchmark parameters, with the adaptation rate
`alpha = 0.1`. -/
def hysteresisBenchmarkParams : LoopParams where
  η := 1 / 2
  lambda₀ := 1 / 50
  I := 1 / 50
  v := 1 / 10
  c := 9 / 10
  α := 1 / 10
  g := 0

/-- The benchmark satisfies every primitive Paper II restriction. -/
theorem hysteresisBenchmark_model :
    DriftModelAssumptions hysteresisBenchmarkParams := by
  constructor <;> norm_num [hysteresisBenchmarkParams]

/-- The benchmark's sufficient cure-dominance comparison is exactly
`0.0162 < 0.0245`. -/
theorem hysteresisBenchmark_cureDominance_values :
    hysteresisBenchmarkParams.c ^ 2 * hysteresisBenchmarkParams.I =
        (81 / 5000 : ℝ) ∧
      hysteresisBenchmarkParams.v * hysteresisBenchmarkParams.η *
          (1 - hysteresisBenchmarkParams.lambda₀) *
          (1 - hysteresisBenchmarkParams.η) = (49 / 2000 : ℝ) ∧
      (81 / 5000 : ℝ) < 49 / 2000 := by
  norm_num [hysteresisBenchmarkParams]

/-- The exact benchmark satisfies `CureDominance`. -/
theorem hysteresisBenchmark_cureDominance :
    CureDominance hysteresisBenchmarkParams := by
  constructor
  norm_num [hysteresisBenchmarkParams]

/-- At the benchmark, release and restoration coincide at exactly `0.0800`. -/
theorem hysteresisBenchmark_prices :
    restorationPrice hysteresisBenchmarkParams =
        cureThreshold hysteresisBenchmarkParams ∧
      cureThreshold hysteresisBenchmarkParams = (2 / 25 : ℝ) := by
  constructor
  · exact restorationPrice_eq_cureThreshold_of_cureDominance
      hysteresisBenchmark_model hysteresisBenchmark_cureDominance
  · norm_num [cureThreshold, hysteresisBenchmarkParams]

#print axioms hysteresisBenchmark_model
#print axioms hysteresisBenchmark_cureDominance_values
#print axioms hysteresisBenchmark_cureDominance
#print axioms hysteresisBenchmark_prices

end PaperII

end


end CivicAlignment
