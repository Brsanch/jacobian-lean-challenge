/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasC3FullClassicalContentFromHJCC
import JacobianChallenge.Manifold.HasJacobianClassicalContent

set_option linter.unusedSectionVars false

/-! # RS smoke: `HasC3FullClassicalContent` via the HJCC instance chain

Validates that `HasC3FullClassicalContent RiemannSphere` fires via
inferInstance through the chain:

* `instHasJacobianClassicalContent_RiemannSphere` (unconditional);
* `instHasC3FullClassicalContent_of_HasJacobianClassicalContent`
  (this session).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-- **HasC3FullClassicalContent RS via inferInstance** through the HJCC chain. -/
example : HasC3FullClassicalContent RiemannSphere := inferInstance

end RiemannSphere

end JacobianChallenge

end
