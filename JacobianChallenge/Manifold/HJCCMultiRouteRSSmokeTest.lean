/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianClassicalContentSubsingleton
import JacobianChallenge.Manifold.HasJacobianClassicalContentGenusOne
import JacobianChallenge.Manifold.HasJacobianClassicalContentGenusTwo
import JacobianChallenge.Manifold.StokesBoundariesTopRiemannSphere

set_option linter.unusedSectionVars false

/-! # Multi-route smoke tests for `HasJacobianClassicalContent`

Combines the multiple discharge routes for HJCC into smoke tests on
`RiemannSphere`:

* Direct genus-0 instance via the unconditional `inferInstance`.
* Subsingleton-ω + BSLB route via
  `HasJacobianClassicalContent.of_subsingleton_and_BSLB` +
  `basedSmoothLoopsBoundHypothesis_RS_holds`.

Both routes produce a `HasJacobianClassicalContent RiemannSphere`
witness; they must agree mathematically (HJCC is a Prop, so any two
witnesses are equal by proof irrelevance).

## Significance

Validates that the HJCC infrastructure is route-agnostic: an X with
multiple discharge paths produces a well-defined Prop conclusion
regardless of route.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-- **HJCC on RS via the direct genus-0 instance.** -/
example : HasJacobianClassicalContent RiemannSphere := inferInstance

/-- **HJCC on RS via the Subsingleton-ω + BSLB route.** -/
example : HasJacobianClassicalContent RiemannSphere :=
  HasJacobianClassicalContent.of_subsingleton_and_BSLB
    (X := RiemannSphere)
    (Classical.arbitrary RiemannSphere)
    (JacobianChallenge.RiemannSphere.basedSmoothLoopsBoundHypothesis_RS_holds _)

end RiemannSphere

end JacobianChallenge

end
