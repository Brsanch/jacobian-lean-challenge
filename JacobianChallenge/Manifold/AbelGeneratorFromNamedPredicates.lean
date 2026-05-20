/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelGeneratorFinalLift
import JacobianChallenge.Manifold.LevelSetChainPeriodInLattice

set_option linter.unusedSectionVars false

/-! # `AbelGeneratorPeriodCondition` from named predicates

Restates `abelGeneratorPeriodCondition_of_period_and_endpoints`
(2-hypothesis universal lift) using the named predicates
`MeromorphicNonzero.LevelSetChainPeriodInLattice` and
`MeromorphicNonzero.HasRegularEndpoints`. Pure renaming +
composition — exposes the open content as exactly **two named
universal hypotheses**:

* `h_period` — `∀ f hnc h_ep, LevelSetChainPeriodInLattice f hnc h_ep α`.
* `h_endpoints` — `∀ f non-constant, HasRegularEndpoints f`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter Module
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [PreconnectedSpace X] [Nonempty X]

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
variable {h : PeriodLatticeDiscretenessBundle
  (PeriodPairingData.ofSmoothCycle X) α}

/-- **Universal `AbelGeneratorPeriodCondition` from the two named
universal predicates.**

A restatement of `abelGeneratorPeriodCondition_of_period_and_endpoints`
using `MeromorphicNonzero.LevelSetChainPeriodInLattice` and
`MeromorphicNonzero.HasRegularEndpoints`. The open content is
factored into exactly two named hypotheses — one substantive
(`LevelSetChainPeriodInLattice` universally, the Stokes/residue
content) and one classical-arrangement (`HasRegularEndpoints`
universally, the Möbius/density content). -/
theorem abelGeneratorPeriodCondition_of_named_predicates
    (B : JacobianChallenge.AbelJacobiInput α h)
    (h_period : ∀ (f : MeromorphicNonzero X)
        (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
        (h_ep : f.HasRegularEndpoints),
        f.LevelSetChainPeriodInLattice hnc h_ep α)
    (h_endpoints : ∀ (f : MeromorphicNonzero X),
        ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere →
        f.HasRegularEndpoints) :
    JacobianChallenge.AbelJacobiInput.AbelGeneratorPeriodCondition B :=
  abelGeneratorPeriodCondition_of_period_and_endpoints (B := B)
    (fun f hnc h0_reg h_inf_reg =>
      h_period f hnc ⟨h0_reg, h_inf_reg⟩)
    h_endpoints

end MeromorphicNonzero

end JacobianChallenge

end
