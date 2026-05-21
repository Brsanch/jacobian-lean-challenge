/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianHodgeChain
import JacobianChallenge.Manifold.HasBasedSmoothLoopsBound

set_option linter.unusedSectionVars false

/-! # Typeclass derivation of `HasJacobianHodgeChain` from
`Subsingleton ω + HasBasedSmoothLoopsBound` (chip 9)

Provides an `instance` that fires `HasJacobianHodgeChain X` from
`[Subsingleton (HolomorphicOneForm X)]` + `[HasBasedSmoothLoopsBound X]`
via the chip 7 discharge `HasJacobianHodgeChain.of_subsingleton_and_BSLB`.

Result: `instHasJacobianHodgeChain_of_subsingleton_and_HasBSLB`, an
automatic instance. Under this + the in-tree
`HasBasedSmoothLoopsBound RiemannSphere` instance,
`HasJacobianHodgeChain RiemannSphere` is automatic.

## What this file ships

* `instance instHasJacobianHodgeChain_of_subsingleton_and_HasBSLB` —
  typeclass-driven discharge.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Typeclass-driven discharge of `HasJacobianHodgeChain X`** under
`[Subsingleton (HolomorphicOneForm X)]` + `[HasBasedSmoothLoopsBound X]`.

Composes `HasBasedSmoothLoopsBound.out` to extract a basepoint + BSLB
witness, then applies `HasJacobianHodgeChain.of_subsingleton_and_BSLB`. -/
instance instHasJacobianHodgeChain_of_subsingleton_and_HasBSLB
    [Subsingleton (HolomorphicOneForm X)]
    [hBSLB : HasBasedSmoothLoopsBound X] :
    HasJacobianHodgeChain X := by
  obtain ⟨p₀, h_BSLB⟩ := hBSLB.out
  exact HasJacobianHodgeChain.of_subsingleton_and_BSLB p₀ h_BSLB

end JacobianChallenge

end
