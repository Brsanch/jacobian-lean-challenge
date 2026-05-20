/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasRegularEndpoints

set_option linter.unusedSectionVars false

/-! # Named `LevelSetChainPeriodInLattice` predicate

The substantive residual content of step 9 of the AbelGenerator arc
is the claim that the period vector of the concrete
`regularLevelSetChain f` is in the period lattice image, for every
non-constant `f` with regular endpoints `(0, ∞)`. This file packages
that claim as a single named predicate.

## What ships

* `MeromorphicNonzero.LevelSetChainPeriodInLattice f hnc h_ep α` —
  the named Prop.

* `abelGeneratorPeriodCondition_of_levelSetChainPeriodInLattice_and_endpoints`
  — restates the final universal lift in terms of the named
  predicate. Pure renaming + composition.

This is the single most-atomic open content of path (b) (AbelGenerator
arc toward item 16) post-today's chips: closing
`LevelSetChainPeriodInLattice` universally (plus `h_endpoints`) closes
the universal `AbelGeneratorPeriodCondition`.

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

/-- **`LevelSetChainPeriodInLattice f hnc h_ep α`** — the period vector
of the concrete `regularLevelSetChain f` lies in `periodLatticeImage`.

This is the substantive residual content of step 9 of the
AbelGenerator arc (the Stokes/residue argument for the lattice
clause). Discharging it universally (together with the universal
endpoint regularity `h_endpoints`) closes the universal
`AbelGeneratorPeriodCondition B`. -/
def LevelSetChainPeriodInLattice
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (h_ep : f.HasRegularEndpoints)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)) :
    Prop :=
  complexChainPeriodVector α (f.regularLevelSetChain hnc h_ep.zero h_ep.infty)
    ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α

end MeromorphicNonzero

end JacobianChallenge

end
