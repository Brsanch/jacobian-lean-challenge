/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianClassicalContentFromUniformizationGenus0
import JacobianChallenge.Manifold.DiskChartCoverFiniteDim

set_option linter.unusedSectionVars false

/-! # `HasJacobianClassicalContent X` under `[UniformizationGenus0Hypothesis X]
+ [Subsingleton (HolomorphicOneForm X)]`

Composes the `_of_uniformizationGenus0` chip with the implication
`Subsingleton (HolomorphicOneForm X) → genus X = 0` (via
`finrank_zero_of_subsingleton` + unconditional finite-dim).

## What ships

* `HasJacobianClassicalContent.of_uniformizationGenus0_subsingleton` —
  HJCC X from a UniformizationGenus0Hypothesis class instance + a
  Subsingleton ω instance, without an explicit `genus X = 0` proof.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **HJCC X from `[UniformizationGenus0Hypothesis X] + [Subsingleton (HolomorphicOneForm X)]`.** -/
theorem HasJacobianClassicalContent.of_uniformizationGenus0_subsingleton
    [UniformizationGenus0Hypothesis X]
    [Subsingleton (HolomorphicOneForm X)] :
    HasJacobianClassicalContent X := by
  haveI : FiniteDimensional ℂ (HolomorphicOneForm X) :=
    DiskChartCover.holomorphicOneFormFiniteDim_holds
  have h_genus : JacobianChallenge.genus X = 0 :=
    Module.finrank_zero_of_subsingleton
  exact HasJacobianClassicalContent.of_uniformizationGenus0 h_genus

end JacobianChallenge

end
