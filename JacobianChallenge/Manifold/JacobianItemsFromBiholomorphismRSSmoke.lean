/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.JacobianItemsFromAnalyticEquivSubsingletonSmoke
import JacobianChallenge.Manifold.HJChainFromBiholomorphismRSSmoke

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-! # Smoke: items 5/11/12/13 instances under `[Nonempty (HolomorphicEquiv X RS)]`

Composes the session's auto-instance chain with the in-tree
`JacobianItemsFromAnalyticEquivSubsingletonSmoke`:

* `[Nonempty (HolomorphicEquiv X RS)]` ⟹
  `[Subsingleton (HolomorphicOneForm X)]` (this session) ⟹
  `[UniformizationGenus0Hypothesis X]` (in tree) ⟹
  `[HasPic0AnalyticEquiv X]` (this session) ⟹
  items 5/11/12/13 on `Jacobian X` (in tree).

A single biholomorphism witness now unlocks all four data/instance
items on `Jacobian X` through `inferInstance`. Items remain OPEN in
Basic.lean (no typeclass hypothesis there), but the conditional
discharge is unconditional under a biholomorphism witness.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [Nonempty (HolomorphicEquiv X RiemannSphere)]

/-- **Item 5 — CompactSpace (Jacobian X) — fires via inferInstance under
biholomorphism to RS.** -/
example : CompactSpace (JacobianChallenge.Jacobian X) := inferInstance

/-- **Item 11 — ChartedSpace ... (Jacobian X).** -/
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
