/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SubsingletonHolomorphicOneFormFromBiholomorphism

set_option linter.unusedSectionVars false

/-! # Typeclass instance: Subsingleton (HolomorphicOneForm X) from a biholomorphism to RS

Registers `Subsingleton (HolomorphicOneForm X)` as a typeclass instance
under `[Nonempty (HolomorphicEquiv X RiemannSphere)]`. Combined with the
in-tree
* `instFactUniformizationToRiemannSphere_of_HolomorphicEquiv`
  (`Topology/Item14ClassInstance.lean`)
* `instUniformizationGenus0Hypothesis_of_FactUniformizationToRiemannSphere`
  (`Topology/UniformizationGenus0Hypothesis.lean`)
* `instHasPic0AnalyticEquiv_of_uniformizationGenus0_subsingleton_omega`
  (this session)

this gives the keystone chain
`[Nonempty (HolomorphicEquiv X RS)] ⟹ HasPic0AnalyticEquiv X ⟹ HJAS X ⟹ …`
fully through typeclass synthesis.

## What ships

* `instSubsingleton_holomorphicOneForm_of_nonempty_holomorphicEquiv_RS` —
  typeclass instance.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Typeclass instance**: Subsingleton (HolomorphicOneForm X) under
`[Nonempty (HolomorphicEquiv X RS)]`. -/
instance instSubsingleton_holomorphicOneForm_of_nonempty_holomorphicEquiv_RS
    [hE : Nonempty (HolomorphicEquiv X RiemannSphere)] :
    Subsingleton (HolomorphicOneForm X) :=
  subsingleton_holomorphicOneForm_of_holomorphicEquiv_RS (Classical.choice hE)

end JacobianChallenge

end
