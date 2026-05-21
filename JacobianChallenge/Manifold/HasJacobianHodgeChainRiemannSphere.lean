/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianHodgeChain
import JacobianChallenge.Manifold.HasBasedSmoothLoopsBound

set_option linter.unusedSectionVars false

/-! # Unconditional `HasJacobianHodgeChain RiemannSphere` instance (chip 8)

This file ships the end-to-end validation of the Hodge–Riemann chain on
`RiemannSphere`. Composes:

* The in-tree `Subsingleton (HolomorphicOneForm RiemannSphere)`
  instance (from `RiemannSphereChartSCoeffOverlap.lean`);
* The in-tree `HasBasedSmoothLoopsBound RiemannSphere` instance
  (chip wave: `HasBasedSmoothLoopsBound.lean`);
* Chip 7's `HasJacobianHodgeChain.of_subsingleton_and_BSLB`.

Result: `instHasJacobianHodgeChain_RiemannSphere`, an unconditional
class instance.

## What this file ships

* `instHasJacobianHodgeChain_RiemannSphere` — the unconditional RS
  instance for `HasJacobianHodgeChain`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-- **Unconditional `HasJacobianHodgeChain RiemannSphere` instance.**

Composes the in-tree `Subsingleton (HolomorphicOneForm RiemannSphere)`
+ `HasBasedSmoothLoopsBound RiemannSphere` + chip 7's discharge.

Note: not marked as `instance` because this would create overlapping
typeclass resolution with `instHasJacobianAnalyticStructure_RiemannSphere`.
Downstream consumers can invoke `HasJacobianHodgeChain.of_subsingleton_and_BSLB`
directly when needed. -/
theorem instHasJacobianHodgeChain_RiemannSphere :
    HasJacobianHodgeChain RiemannSphere := by
  haveI : Nonempty RiemannSphere := ConnectedSpace.toNonempty
  let p₀ : RiemannSphere := Classical.arbitrary RiemannSphere
  haveI hBSLB := JacobianChallenge.instHasBasedSmoothLoopsBound_RiemannSphere
  obtain ⟨q₀, h_BSLB⟩ := hBSLB.out
  exact HasJacobianHodgeChain.of_subsingleton_and_BSLB q₀ h_BSLB

end RiemannSphere

end JacobianChallenge

end
