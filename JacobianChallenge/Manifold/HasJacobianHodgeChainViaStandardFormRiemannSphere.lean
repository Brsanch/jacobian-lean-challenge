/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianHodgeChainViaStandardFormSubsingleton
import JacobianChallenge.Manifold.HasBasedSmoothLoopsBound

set_option linter.unusedSectionVars false

/-! # Unconditional `HasJacobianHodgeChainViaStandardForm RiemannSphere`
(chip 18)

Parallel to chip 8. Validates the simplified Hodge-chain route
(`HasJacobianHodgeChainViaStandardForm`) on `RiemannSphere`
unconditionally via:

* `Subsingleton (HolomorphicOneForm RiemannSphere)` (in-tree).
* `HasBasedSmoothLoopsBound RiemannSphere` (in-tree).
* Chip 16's `HasJacobianHodgeChainViaStandardForm.of_subsingleton_and_BSLB`.

## What this file ships

* `instHasJacobianHodgeChainViaStandardForm_RiemannSphere` — the RS
  validation theorem (not registered as global instance, parallel to
  chip 8's design).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-- **Unconditional `HasJacobianHodgeChainViaStandardForm RiemannSphere`
instance.** Validates the simplified Hodge-chain route on RS. -/
theorem instHasJacobianHodgeChainViaStandardForm_RiemannSphere :
    HasJacobianHodgeChainViaStandardForm RiemannSphere := by
  haveI : Nonempty RiemannSphere := ConnectedSpace.toNonempty
  haveI hBSLB := JacobianChallenge.instHasBasedSmoothLoopsBound_RiemannSphere
  obtain ⟨q₀, h_BSLB⟩ := hBSLB.out
  exact HasJacobianHodgeChainViaStandardForm.of_subsingleton_and_BSLB q₀ h_BSLB

end RiemannSphere

end JacobianChallenge

end
