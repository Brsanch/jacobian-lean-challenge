/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasPic0AnalyticEquiv
import JacobianChallenge.Manifold.HasJacobianAnalyticStructure

set_option linter.unusedSectionVars false

/-! # `HasJacobianAnalyticStructure X` from `[HasPic0AnalyticEquiv X]`

The keystone `[HasPic0AnalyticEquiv X]` class includes a
`HasSmoothHomologyDataPackage` witness on its `basis_ω`. The latter
implies `HasJacobianAnalyticStructure X` (basis-anonymous existential).

## What ships

* `instance instHasJacobianAnalyticStructure_of_HasPic0AnalyticEquiv` —
  HJAS X from [HJAE X].

This composes with the in-tree
`instHasJacobianAnalyticStructure_of_HasSmoothHomologyDataPackage` /
`HasJacobianAnalyticStructure.of_hasSmoothHomologyDataPackage` bridge.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

/-- **HJAS X from [HJAE X].** -/
instance instHasJacobianAnalyticStructure_of_HasPic0AnalyticEquiv
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    [HasPic0AnalyticEquiv X] :
    HasJacobianAnalyticStructure X :=
  HasJacobianAnalyticStructure.of_hasSmoothHomologyDataPackage
    (canonicalBasisOmega X)

end JacobianChallenge

end
