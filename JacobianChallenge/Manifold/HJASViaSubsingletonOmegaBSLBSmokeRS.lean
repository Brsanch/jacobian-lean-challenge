/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianAnalyticStructureSubsingleton
import JacobianChallenge.Manifold.StokesBoundariesTopRiemannSphere

set_option linter.unusedSectionVars false

/-! # Smoke test: HJAS on RS via [Subsingleton ω] + BSLB route

Validates that `HasJacobianAnalyticStructure RiemannSphere` fires
via the explicit `_of_subsingleton_and_BSLB` route, taking a basepoint
and the RS BSLB hypothesis.

This is an explicit alternative to the direct
`instHasJacobianAnalyticStructure_RiemannSphere` instance, validating
that the Subsingleton-ω + BSLB chain composes correctly on RS.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-- **HJAS RS via the Subsingleton-ω + BSLB constructor.** -/
example : HasJacobianAnalyticStructure RiemannSphere :=
  HasJacobianAnalyticStructure.of_subsingleton_and_BSLB
    (Classical.arbitrary RiemannSphere)
    (basedSmoothLoopsBoundHypothesis_RS_holds _)

end RiemannSphere

end JacobianChallenge

end
