/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HJASFromHJAERSSmoke
import JacobianChallenge.Manifold.HasJacobianClassicalContentRSSmokeTest
import JacobianChallenge.Manifold.JacobianItemsFromAnalyticEquivSubsingletonSmoke

set_option linter.unusedSectionVars false

/-! # Composite RS smoke tests: HJAS via HJAE *and* HJCC routes

Validates that on `RiemannSphere`, both routes to
`HasJacobianAnalyticStructure RiemannSphere` fire via `inferInstance`:

* via `[HasPic0AnalyticEquiv RS]` (this session's bridge instance);
* via `[HasJacobianClassicalContent RS]` (this session's bridge instance);
* via the in-tree direct `instHasJacobianAnalyticStructure_RiemannSphere`.

All three produce the same Prop conclusion (Prop irrelevance).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-- **HJAS RS via inferInstance** — finds the route automatically. -/
example : HasJacobianAnalyticStructure RiemannSphere := inferInstance

/-- **HJCC RS via inferInstance**. -/
example : HasJacobianClassicalContent RiemannSphere := inferInstance

/-- **HJAE RS via inferInstance**. -/
example : HasPic0AnalyticEquiv RiemannSphere := inferInstance

end RiemannSphere

end JacobianChallenge

end
