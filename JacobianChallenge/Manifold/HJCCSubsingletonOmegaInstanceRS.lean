/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianClassicalContentSubsingleton
import JacobianChallenge.Manifold.StokesBoundariesTopRiemannSphere

set_option linter.unusedSectionVars false

/-! # Smoke: `HasJacobianClassicalContent` and downstream classes on RS via the Subsingleton-ω route

Validates that the in-tree
`HasJacobianClassicalContent.of_subsingleton_and_BSLB` route fires on
`RiemannSphere` via `inferInstance`, and the cascade through to
`HasJacobianAnalyticStructure` works.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-- **HJCC RS via the Subsingleton-ω + BSLB route.** -/
example : HasJacobianClassicalContent RiemannSphere :=
  HasJacobianClassicalContent.of_subsingleton_and_BSLB
    (Classical.arbitrary RiemannSphere)
    (basedSmoothLoopsBoundHypothesis_RS_holds _)

/-- **HJAS RS via the chain `HJCC X → HJAS X`.** -/
example : HasJacobianAnalyticStructure RiemannSphere :=
  letI : HasJacobianClassicalContent RiemannSphere :=
    HasJacobianClassicalContent.of_subsingleton_and_BSLB
      (Classical.arbitrary RiemannSphere)
      (basedSmoothLoopsBoundHypothesis_RS_holds _)
  inferInstance

end RiemannSphere

end JacobianChallenge

end
