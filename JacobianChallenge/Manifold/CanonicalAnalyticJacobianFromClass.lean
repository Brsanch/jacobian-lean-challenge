/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothHomologyDataPackageClass
import JacobianChallenge.Manifold.PeriodLatticeOfRankTwoG_LieGroupWiring

set_option linter.unusedSectionVars false

/-! # Canonical analytic Jacobian from `[HasSmoothHomologyDataPackage X basis_ω]`

For any `X` with `[HasSmoothHomologyDataPackage X basis_ω]`, this file
extracts a *canonical* `PeriodLatticeSymplecticBundle` witness (via
`Classical.choice`), builds a `PeriodLatticeOfRankTwoG X` term, and
provides the four structural instances on the resulting analytic
Jacobian:

* `AddCommGroup`
* `TopologicalSpace`
* `T2Space`
* `CompactSpace`        — item 5 of `OPEN.md`
* `ChartedSpace ℂ^g`    — item 11
* `IsManifold ω`        — item 12
* `LieAddGroup ω`       — item 13

The bundle witness is `Classical.choice`d **once per `(X, basis_ω)`**
at the definition of `canonicalPeriodLatticeSymplecticBundle`; all four
structural instances reference that same witness via the definitional
chain `CanonicalAnalyticJacobian → canonicalPeriodLatticeOfRankTwoG →
canonicalPeriodLatticeSymplecticBundle`. This avoids the trap where
multiple `Classical.choice` invocations would pick different witnesses
and yield non-defeq quotient types.

This is the structural plumbing for the period-lattice arc: once a
universal `[HasSmoothHomologyDataPackage X basis_ω]` instance lands
(the remaining classical content — surface classification + smooth
Hurewicz + Riemann bilinear), items 5/11/12/13 on `Basic.lean`'s
`Jacobian X` flip via the C3 rewire of `Jacobian X` to
`CanonicalAnalyticJacobian basis_ω`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ### Canonical witness extraction -/

/-- **Canonical `SmoothHomologyDataPackage` from the class wrapper.**
Extracted via `Classical.choice` from `[HasSmoothHomologyDataPackage
X basis_ω]`. Used exactly once per `(X, basis_ω)` for the canonical
analytic Jacobian construction below; all four structural instances
reference this single witness. -/
noncomputable def canonicalSmoothHomologyDataPackage
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    [HasSmoothHomologyDataPackage (X := X) basis_ω] :
    SmoothHomologyDataPackage basis_ω :=
  Classical.choice nonempty_smoothHomologyDataPackage_of_class

/-- **Canonical `PeriodLatticeSymplecticBundle` from the class wrapper.**
Built from the canonical `SmoothHomologyDataPackage` via the
single-input composite `nonempty_periodLatticeSymplecticBundle_of_smoothHomologyDataPackage`. -/
noncomputable def canonicalPeriodLatticeSymplecticBundle
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    [HasSmoothHomologyDataPackage (X := X) basis_ω] :
    PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) basis_ω :=
  Classical.choice
    (nonempty_periodLatticeSymplecticBundle_of_smoothHomologyDataPackage
      (canonicalSmoothHomologyDataPackage basis_ω))

/-- **Canonical `PeriodLatticeOfRankTwoG X` from the class wrapper.**
Built from the canonical symplectic bundle via the `ofSymplectic`
constructor. -/
noncomputable def canonicalPeriodLatticeOfRankTwoG
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    [HasSmoothHomologyDataPackage (X := X) basis_ω] :
    PeriodLatticeOfRankTwoG X :=
  PeriodLatticeOfRankTwoG.ofSymplectic
    (PeriodPairingData.ofSmoothCycle X) basis_ω
    (canonicalPeriodLatticeSymplecticBundle basis_ω)

/-! ### Lattice instances (`DiscreteTopology` + `IsZLattice ℝ`) -/

/-- `DiscreteTopology` instance on the canonical lattice's underlying
`Submodule ℤ`. Direct from the bundle's derivation. -/
instance discreteTopology_canonicalPeriodLattice
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    [HasSmoothHomologyDataPackage (X := X) basis_ω] :
    DiscreteTopology
      (canonicalPeriodLatticeOfRankTwoG basis_ω).lattice.toIntSubmodule :=
  PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle
    (canonicalPeriodLatticeSymplecticBundle basis_ω)

/-- `IsZLattice ℝ` instance on the canonical lattice's underlying
`Submodule ℤ`. Direct from the bundle's derivation. -/
instance isZLattice_canonicalPeriodLattice
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    [HasSmoothHomologyDataPackage (X := X) basis_ω] :
    IsZLattice ℝ
      (canonicalPeriodLatticeOfRankTwoG basis_ω).lattice.toIntSubmodule := by
  haveI := discreteTopology_canonicalPeriodLattice basis_ω
  exact PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle
    (canonicalPeriodLatticeSymplecticBundle basis_ω)

/-! ### Canonical analytic Jacobian and its instances -/

/-- **Canonical analytic Jacobian under `[HasSmoothHomologyDataPackage
X basis_ω]`.** The period-lattice quotient `(Fin (genus X) → ℂ) ⧸ Λ`
where `Λ` is the canonical period lattice. -/
def CanonicalAnalyticJacobian
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    [HasSmoothHomologyDataPackage (X := X) basis_ω] : Type :=
  JacobianOfLattice X (canonicalPeriodLatticeOfRankTwoG basis_ω)

namespace CanonicalAnalyticJacobian

variable
  (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
    (HolomorphicOneForm X))
  [HasSmoothHomologyDataPackage (X := X) basis_ω]

instance instAddCommGroup : AddCommGroup (CanonicalAnalyticJacobian basis_ω) :=
  inferInstanceAs (AddCommGroup
    (JacobianOfLattice X (canonicalPeriodLatticeOfRankTwoG basis_ω)))

instance instTopologicalSpace :
    TopologicalSpace (CanonicalAnalyticJacobian basis_ω) :=
  inferInstanceAs (TopologicalSpace
    (JacobianOfLattice X (canonicalPeriodLatticeOfRankTwoG basis_ω)))

instance instT2Space : T2Space (CanonicalAnalyticJacobian basis_ω) :=
  inferInstanceAs (T2Space
    (JacobianOfLattice X (canonicalPeriodLatticeOfRankTwoG basis_ω)))

/-- **Item 5 discharge for the canonical analytic Jacobian.**
`CompactSpace` via `compactSpaceHypothesis_holds` on the canonical
lattice. -/
instance instCompactSpace : CompactSpace (CanonicalAnalyticJacobian basis_ω) :=
  PeriodLatticeOfRankTwoG.compactSpaceHypothesis_holds
    (canonicalPeriodLatticeOfRankTwoG basis_ω)

/-- **Item 11 discharge for the canonical analytic Jacobian.**
`ChartedSpace (Fin g → ℂ)` via `chartedSpaceHypothesis_holds.toChartedSpace`
on the canonical lattice. -/
instance instChartedSpace :
    ChartedSpace (Fin (JacobianChallenge.genus X) → ℂ)
      (CanonicalAnalyticJacobian basis_ω) :=
  (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds
    (canonicalPeriodLatticeOfRankTwoG basis_ω)).toChartedSpace

/-- **Item 12 discharge for the canonical analytic Jacobian.**
Complex-`ω` `IsManifold` via `chartedSpaceHypothesis_holds.toIsManifold`
on the canonical lattice. -/
instance instIsManifold :
    @IsManifold ℂ _
      (Fin (JacobianChallenge.genus X) → ℂ) _ _
      (Fin (JacobianChallenge.genus X) → ℂ) _
      (modelWithCornersSelf ℂ (Fin (JacobianChallenge.genus X) → ℂ)) ω
      (CanonicalAnalyticJacobian basis_ω) _ inferInstance :=
  (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds
    (canonicalPeriodLatticeOfRankTwoG basis_ω)).toIsManifold

/-- **Item 13 discharge for the canonical analytic Jacobian.**
Complex-`ω` `LieAddGroup` via `lieAddGroupHypothesis_holds` on the
canonical lattice. -/
instance instLieAddGroup :
    @LieAddGroup ℂ _
      (Fin (JacobianChallenge.genus X) → ℂ) _
      (Fin (JacobianChallenge.genus X) → ℂ) _ _
      (modelWithCornersSelf ℂ (Fin (JacobianChallenge.genus X) → ℂ)) ω
      (CanonicalAnalyticJacobian basis_ω) _ _ inferInstance :=
  PeriodLatticeOfRankTwoG.lieAddGroupHypothesis_holds
    (canonicalPeriodLatticeOfRankTwoG basis_ω)

end CanonicalAnalyticJacobian

end JacobianChallenge

end
