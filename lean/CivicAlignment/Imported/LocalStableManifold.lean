/-
Copyright (c) 2026 Daniel Hofheinz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Hofheinz
-/
import CivicAlignment.PaperII.StableManifold

/-!
# The local stable-manifold theorem

The local `C¹` stable-manifold theorem at the interior saddle — classically
cited after Hirsch and Smith (2005) and Kuznetsov (2004), and absent from
Mathlib — is proved here from first principles.
`PaperII/NemytskiiSubstitution.lean`, `PaperII/HyperbolicGreen.lean`,
`PaperII/PlanarHadamardPerron.lean`, and `PaperII/StableCurve.lean` prove
Irwin's stable-manifold theorem for a planar hyperbolic germ from Mathlib's
implicit function theorem on the Banach space of bounded sequences;
`PaperII/SaddleGerm.lean` instantiates the germ at the interior saddle
through the explicit eigenbasis; and `PaperII/StableManifold.lean` combines
the resulting curve with the internally proved antichain and
quadrant-exclusion structure of the stable set.

The module path and declaration name are historical, kept so that downstream
consumers (`bistability_localC1DecreasingArc`, `bistability`) are unchanged;
the declaration is an ordinary theorem, and `#print axioms` reports only
Lean's three foundational axioms.
-/

namespace CivicAlignment.Imported

open CivicAlignment.PaperII

/--
The local stable-manifold theorem for the bistable loop: under the paper's
primitive assumptions, `(H)`, and `(SS⁺)`, the ambient stable set of the
interior saddle agrees in some open neighborhood of that saddle with the
image of an injective `C¹` arc whose policy coordinate is strictly
increasing and whose stock coordinate is strictly decreasing.

Proved by `CivicAlignment.PaperII.saddleLocalStableManifold`.
-/
theorem localStableManifoldForBistableLoop {p : LoopParams}
    (model : DriftModelAssumptions p) (ssplus : ConvergentStepAssumption p)
    (threshold : ThresholdAssumption p) :
    IsLocalC1DecreasingArcAt (ambientSaddleStableSet p threshold)
      (saddlePoint p threshold) :=
  saddleLocalStableManifold model ssplus threshold

#print axioms localStableManifoldForBistableLoop

end CivicAlignment.Imported
