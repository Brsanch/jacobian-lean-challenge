/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianClassicalContent
import JacobianChallenge.Manifold.HasJacobianHodgeChainFromUpperTriangularScalars

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # `HasJacobianHodgeChain X` instance from `[HasJacobianClassicalContent X]`

The HJCC class bundles the same upstream data needed by
`HasJacobianHodgeChain.of_upperTriangularScalars`: SCD + basis +
g²-scalar identities. So under [HJCC X], HJHC X follows automatically.

## What ships

* `instance instHasJacobianHodgeChain_of_HasJacobianClassicalContent` —
  instance form.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

/-- **HJHC X from [HJCC X].** -/
instance instHasJacobianHodgeChain_of_HasJacobianClassicalContent
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    [h : HasJacobianClassicalContent X] :
    HasJacobianHodgeChain X := by
  obtain ⟨scd, basis_ω, h_strict, h_upper⟩ := h.out
  exact HasJacobianHodgeChain.of_upperTriangularScalars scd basis_ω
    h_strict h_upper

end JacobianChallenge

end
