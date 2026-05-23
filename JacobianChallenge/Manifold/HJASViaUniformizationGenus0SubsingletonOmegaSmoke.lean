/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianAnalyticStructureFromUniformizationGenus0
import JacobianChallenge.Manifold.HJCCSubsingletonViaUniformization

set_option linter.unusedSectionVars false

/-! # Smoke: HJAS via `[UniformizationGenus0Hypothesis X] + [Subsingleton ω]`

Validates the chain:
* `[UniformizationGenus0Hypothesis X] + [Subsingleton (HolomorphicOneForm X)]`
  → `[HasJacobianClassicalContent X]` (instance, via
  \`instHasJacobianClassicalContent_of_uniformizationGenus0_subsingleton\`)
  → `HasJacobianAnalyticStructure X` via the in-tree bridge.

Without an explicit `genus X = 0` proof, the two typeclasses already
suffice.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

/-- **HJAS X under [UniformizationGenus0Hypothesis X] + [Subsingleton ω].** -/
example {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    [UniformizationGenus0Hypothesis X]
    [Subsingleton (HolomorphicOneForm X)] :
    HasJacobianAnalyticStructure X :=
  letI : HasJacobianClassicalContent X :=
    HasJacobianClassicalContent.of_uniformizationGenus0_subsingleton
  inferInstance

end JacobianChallenge

end
