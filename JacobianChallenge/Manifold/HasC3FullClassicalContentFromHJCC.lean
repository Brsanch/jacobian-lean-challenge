/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianClassicalContent
import JacobianChallenge.Manifold.HasC3FullClassicalContentFromUpperTriangularScalars

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # `HasC3FullClassicalContent X` from `[HasJacobianClassicalContent X]`

The new `HasJacobianClassicalContent X` typeclass bundles SCD + basis_ω
+ g(g-1)/2 strict-upper Q vanishing + g(g+1)/2 upper-tri Petersson
identities (all the open analytic content of the C3 wave). Combined
with the in-tree
`HasC3FullClassicalContent.of_sesquilinearUpperTriangular_pettersonForm`
+ `RiemannFirstBilinearRelationFromStrictUpperQ`, this gives
`HasC3FullClassicalContent X` automatically.

This is a class-to-class implication: `[HJCC X]` ⟹ `[HasC3FullClassicalContent X]`.

## What ships

* `instance instHasC3FullClassicalContent_of_HasJacobianClassicalContent`
  — instance form of the implication.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

/-- **HasC3FullClassicalContent X from [HJCC X].** -/
instance instHasC3FullClassicalContent_of_HasJacobianClassicalContent
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    [h : HasJacobianClassicalContent X] :
    HasC3FullClassicalContent X := by
  obtain ⟨scd, basis_ω, h_strict, h_upper⟩ := h.out
  exact HasC3FullClassicalContent.of_upperTriangularScalars scd basis_ω
    h_strict h_upper

end JacobianChallenge

end
