/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelGeneratorAtRegularEndpoints

set_option linter.unusedSectionVars false

/-! # `HasRegularEndpoints`: ergonomic packaging of `(0, ∞)`-regularity

For `f : MeromorphicNonzero X`, the `regularLevelSetChain` requires
both `((0 : ℂ) : RiemannSphere)` and `OnePoint.infty` to be regular
values. This file packages that pair into a single predicate
`HasRegularEndpoints` with named accessors, and provides a
reformulation of
`abelGeneratorPeriodCondition_at_of_regularLevelSetChain_period`
that takes the packaged hypothesis instead of the two separate
membership proofs.

## What ships

* `MeromorphicNonzero.HasRegularEndpoints f` — the predicate.
* `.zero` / `.infty` — accessors.
* `abelGeneratorPeriodCondition_at_of_hasRegularEndpoints_period` —
  per-`f` AbelGenerator reduction with packaged endpoint hypothesis.

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

/-- **`HasRegularEndpoints f`**: both `0` and `∞` are regular values
of `f`. This is precisely the data needed to define
`f.regularLevelSetChain`. -/
def HasRegularEndpoints (f : MeromorphicNonzero X) : Prop :=
  (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet ∧
  (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet

namespace HasRegularEndpoints

variable {f : MeromorphicNonzero X}

/-- `0 ∈ f.regularValueSet` from a `HasRegularEndpoints` witness. -/
lemma zero (h : f.HasRegularEndpoints) :
    (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet := h.1

/-- `∞ ∈ f.regularValueSet` from a `HasRegularEndpoints` witness. -/
lemma infty (h : f.HasRegularEndpoints) :
    (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet := h.2

end HasRegularEndpoints

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
variable {h : PeriodLatticeDiscretenessBundle
  (PeriodPairingData.ofSmoothCycle X) α}

/-- **Per-`f` AbelGenerator reduction with packaged endpoint hypothesis.**
A reformulation of
`abelGeneratorPeriodCondition_at_of_regularLevelSetChain_period`
that takes a `HasRegularEndpoints f` witness instead of two separate
membership proofs. Useful for downstream chips that prefer to
manipulate the single named hypothesis. -/
theorem abelGeneratorPeriodCondition_at_of_hasRegularEndpoints_period
    (B : JacobianChallenge.AbelJacobiInput α h)
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (h_ep : f.HasRegularEndpoints)
    (h_Z_period :
      complexChainPeriodVector α
          (f.regularLevelSetChain hnc h_ep.zero h_ep.infty)
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α) :
    complexChainPeriodVector α
        (B.principalDivisorAJChain (principalDivisorMap f))
      ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α :=
  abelGeneratorPeriodCondition_at_of_regularLevelSetChain_period
    B f hnc h_ep.zero h_ep.infty h_Z_period

end MeromorphicNonzero

end JacobianChallenge

end
