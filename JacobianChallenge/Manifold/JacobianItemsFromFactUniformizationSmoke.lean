/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.JacobianItemsFromBiholomorphismRSSmoke
import JacobianChallenge.Topology.Item14ClassInstance
import JacobianChallenge.Topology.UniformizationGenus0Hypothesis

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-! # Smoke: items 5/11/12/13/15/17/21 under `[FactUniformizationToRiemannSphere X] + [Subsingleton ω]`

Composes the in-tree chain
`[FactUniformizationToRiemannSphere X] + (genus = 0 disjunct) →
  Nonempty (HolomorphicEquiv X RS)` with this session's
`[Nonempty (HolomorphicEquiv X RS)]`-driven items chain.

Under `[FactUniformizationToRiemannSphere X] + [Subsingleton ω]`, every
remaining Basic.lean item fires conditionally. This is the **strictly
weakest typeclass hypothesis** that triggers the chain (matching the
Item-14 disjunctive class).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [FactUniformizationToRiemannSphere X]
  [Subsingleton (HolomorphicOneForm X)]

/-- Derive `Nonempty (HolomorphicEquiv X RS)` from the disjunctive
class + Subsingleton ω. -/
private theorem nonempty_holomorphicEquiv_RS_of_subsingleton_omega :
    Nonempty (HolomorphicEquiv X RiemannSphere) := by
  haveI : FiniteDimensional ℂ (HolomorphicOneForm X) :=
    DiskChartCover.holomorphicOneFormFiniteDim_holds
  have h_genus : JacobianChallenge.genus X = 0 :=
    Module.finrank_zero_of_subsingleton
  exact UniformizationGenus0Hypothesis.out h_genus

/-- **Typeclass instance**: `[Nonempty (HolomorphicEquiv X RS)]`
under the disjunctive Fact + Subsingleton ω. -/
instance instNonempty_holomorphicEquiv_RS_of_fact_subsingleton :
    Nonempty (HolomorphicEquiv X RiemannSphere) :=
  nonempty_holomorphicEquiv_RS_of_subsingleton_omega

example : HasPic0AnalyticEquiv X := inferInstance
example : HasJacobianAnalyticStructure X := inferInstance
example : HasJacobianClassicalContent X := inferInstance
example : HasJacobianHodgeChain X := inferInstance
example : HasC3FullClassicalContent X := inferInstance
example : HasSurfaceClassificationData X := inferInstance
example : Subsingleton (Pic0 X) := inferInstance
example : HasBasedSmoothLoopsBound X := inferInstance

/-- **Item 5 — CompactSpace (Jacobian X) — fires via inferInstance under
the FactUniformization disjunctive class + Subsingleton ω.** -/
example : CompactSpace (JacobianChallenge.Jacobian X) := inferInstance

/-- **Item 11 — ChartedSpace.** -/
example :
    ChartedSpace (Fin (JacobianChallenge.genus X) → ℂ)
      (JacobianChallenge.Jacobian X) := inferInstance

/-- **Item 12 — IsManifold.** -/
example :
    @IsManifold ℂ _
      (Fin (JacobianChallenge.genus X) → ℂ) _ _
      (Fin (JacobianChallenge.genus X) → ℂ) _
      (modelWithCornersSelf ℂ
        (Fin (JacobianChallenge.genus X) → ℂ)) ω
      (JacobianChallenge.Jacobian X) _ inferInstance := inferInstance

end JacobianChallenge

end
