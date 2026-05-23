/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HJASFromHasPic0AnalyticEquiv
import JacobianChallenge.Manifold.HasPic0AnalyticEquivRiemannSphere

set_option linter.unusedSectionVars false

/-! # RS smoke test: HJAS via [HasPic0AnalyticEquiv]

Validates that the new
`instHasJacobianAnalyticStructure_of_HasPic0AnalyticEquiv` instance
fires on RiemannSphere via inferInstance, given the unconditional
`instHasPic0AnalyticEquiv_RiemannSphere`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-- **HJAS RS via the new [HJAE → HJAS] bridge instance.** -/
example : HasJacobianAnalyticStructure RiemannSphere := inferInstance

end RiemannSphere

end JacobianChallenge

end
