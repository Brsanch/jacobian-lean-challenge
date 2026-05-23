/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SubsingletonHolomorphicOneFormInstanceFromBiholomorphism
import JacobianChallenge.Manifold.HJChainFromUniformizationGenus0SubsingletonSmoke

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-! # End-to-end smoke: HJ chain from `[Nonempty (HolomorphicEquiv X RS)]`

Validates the chain
`[Nonempty (HolomorphicEquiv X RS)] ⟹ HasPic0AnalyticEquiv X ⟹ HJAS X`
through typeclass synthesis. Composes:
* `instFactUniformizationToRiemannSphere_of_HolomorphicEquiv` (in tree)
* `instUniformizationGenus0Hypothesis_of_FactUniformizationToRiemannSphere` (in tree)
* `instSubsingleton_holomorphicOneForm_of_nonempty_holomorphicEquiv_RS`
  (this session)
* `instHasPic0AnalyticEquiv_of_uniformizationGenus0_subsingleton_omega`
  (this session)
* `instHasJacobianAnalyticStructure_of_HasPic0AnalyticEquiv` (in tree)

Regression-guard for the just-shipped instance chain.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [Nonempty (HolomorphicEquiv X RiemannSphere)]

example : Subsingleton (HolomorphicOneForm X) := inferInstance
example : FactUniformizationToRiemannSphere X := inferInstance
example : UniformizationGenus0Hypothesis X := inferInstance
example : HasPic0AnalyticEquiv X := inferInstance
example : HasJacobianAnalyticStructure X := inferInstance

end JacobianChallenge

end
