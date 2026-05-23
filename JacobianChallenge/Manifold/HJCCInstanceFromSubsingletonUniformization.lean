/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HJCCSubsingletonViaUniformization

set_option linter.unusedSectionVars false

/-! # `HasJacobianClassicalContent X` typeclass instance

Registers `HasJacobianClassicalContent X` as a typeclass instance
automatically derived from `[UniformizationGenus0Hypothesis X]` +
`[Subsingleton (HolomorphicOneForm X)]`. Lets downstream code use
`inferInstance` without explicit constructor invocation.

## What ships

* `instance instHasJacobianClassicalContent_of_uniformizationGenus0_subsingleton`
  — registers `HJCC X` as an instance.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

/-- **`HasJacobianClassicalContent X` typeclass instance** from
`[UniformizationGenus0Hypothesis X] + [Subsingleton (HolomorphicOneForm X)]`. -/
instance instHasJacobianClassicalContent_of_uniformizationGenus0_subsingleton
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    [UniformizationGenus0Hypothesis X]
    [Subsingleton (HolomorphicOneForm X)] :
    HasJacobianClassicalContent X :=
  HasJacobianClassicalContent.of_uniformizationGenus0_subsingleton

end JacobianChallenge

end
