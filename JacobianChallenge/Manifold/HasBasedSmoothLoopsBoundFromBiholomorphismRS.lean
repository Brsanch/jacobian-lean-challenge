/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasBasedSmoothLoopsBound
import JacobianChallenge.Manifold.BasedSmoothLoopsBoundTransport
import JacobianChallenge.Manifold.StokesBoundariesTopRiemannSphere

set_option linter.unusedSectionVars false

/-! # `HasBasedSmoothLoopsBound X` from `[Nonempty (HolomorphicEquiv X RS)]`

Transports the unconditional `HasBasedSmoothLoopsBound RiemannSphere`
to any X biholomorphic to RS via
`basedSmoothLoopsBoundHypothesis_pushforward_biholomorphism`.

## What ships

* `instHasBasedSmoothLoopsBound_of_holomorphicEquiv_RS` — typeclass
  instance.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **HasBasedSmoothLoopsBound X from a biholomorphism X ≃ω RS.** -/
instance instHasBasedSmoothLoopsBound_of_holomorphicEquiv_RS
    [hE : Nonempty (HolomorphicEquiv X RiemannSphere)] :
    HasBasedSmoothLoopsBound X := by
  refine ⟨?_⟩
  let φ : HolomorphicEquiv X RiemannSphere := Classical.choice hE
  let q₀ : RiemannSphere := Classical.arbitrary _
  refine ⟨(φ.symm : HolomorphicEquiv RiemannSphere X).toEquiv q₀, ?_⟩
  exact basedSmoothLoopsBoundHypothesis_pushforward_biholomorphism
    (φ.symm : HolomorphicEquiv RiemannSphere X) q₀
    (RiemannSphere.basedSmoothLoopsBoundHypothesis_RS_holds q₀)

end JacobianChallenge

end
