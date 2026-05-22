/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianClassicalContent

set_option linter.unusedSectionVars false

/-! # RS smoke tests for `HasJacobianClassicalContent` class synthesis

Verifies via `inferInstance` that the unconditional RS instance of
`HasJacobianClassicalContent` fires and composes through the bridge
instance `instHasJacobianAnalyticStructure_of_HasJacobianClassicalContent`.

This is a regression guard: if either instance ever breaks, these
`example` statements will fail to compile.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-- **HJCC fires on RS via `inferInstance`.** -/
example : HasJacobianClassicalContent RiemannSphere := inferInstance

/-- **HJAS follows on RS via the HJCC → HJAS bridge.** -/
example : HasJacobianAnalyticStructure RiemannSphere := inferInstance

end RiemannSphere

end JacobianChallenge

end
