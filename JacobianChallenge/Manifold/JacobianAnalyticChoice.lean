/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3FullInputExt
import JacobianChallenge.Manifold.C3FullInputInstances
import JacobianChallenge.Manifold.C3FullInputExtClosures
import JacobianChallenge.Manifold.AbelJacobiIso

set_option linter.unusedSectionVars false

/-! # `JacobianAnalyticChoice X` — analytic Jacobian via classical-choice

Given `[Nonempty (C3FullInputExt X)]` (a single typeclass-bundled
classical existence input), `JacobianAnalyticChoice X` is the honest
analytic Jacobian built via `Classical.choice`.

It carries **all the instances** that Basic.lean's `Jacobian X` is
supposed to carry under STRICT-CLOSED:

* `AddCommGroup`, `TopologicalSpace`, `T2Space` (items 3, 4, 10).
* `CompactSpace` (item 11).
* `ChartedSpace (Fin (genus X) → ℂ)` (item 5).
* `IsManifold (𝓘(ℂ, ℂ)) ω` (item 12).
* `LieAddGroup (𝓘(ℂ, ℂ)) ω` (item 13).

Plus the `Pic⁰ X ≃+ JacobianAnalyticChoice X` AddEquiv from the bundle's
Abel-Jacobi isomorphism — the bridge needed to transport instances back
to Basic.lean's `Jacobian X = Pic⁰ X` (or to redefine it).

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology ContDiff
open Module

noncomputable section

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [Nonempty (C3FullInputExt X)]

/-- A canonical `C3FullInputExt X` extracted via `Classical.choice`. -/
noncomputable def chosenC3 : C3FullInputExt X :=
  Classical.choice inferInstance

/-- **The analytic Jacobian via classical choice.** Definitionally
`AnalyticJacobian` instantiated at the chosen bundle's basis/discreteness. -/
noncomputable abbrev JacobianAnalyticChoice : Type :=
  AnalyticJacobian (PeriodPairingData.ofSmoothCycle X)
    (chosenC3 X).base.basis (chosenC3 X).base.discreteness

variable {X}

/-! ## Instance discharges -/

instance instAddCommGroup : AddCommGroup (JacobianAnalyticChoice X) :=
  inferInstanceAs (AddCommGroup
    (AnalyticJacobian _ (chosenC3 X).base.basis (chosenC3 X).base.discreteness))

instance instTopologicalSpace : TopologicalSpace (JacobianAnalyticChoice X) :=
  inferInstanceAs (TopologicalSpace
    (AnalyticJacobian _ (chosenC3 X).base.basis (chosenC3 X).base.discreteness))

instance instT2Space : T2Space (JacobianAnalyticChoice X) :=
  inferInstanceAs (T2Space
    (AnalyticJacobian _ (chosenC3 X).base.basis (chosenC3 X).base.discreteness))

/-- DiscreteTopology on the lattice (needed for downstream ChartedSpace, etc.). -/
instance instDiscreteTopologyLattice :
    DiscreteTopology (PeriodLatticeOfRankTwoG.ofBundle
      (PeriodPairingData.ofSmoothCycle X)
      (chosenC3 X).base.basis (chosenC3 X).base.discreteness).lattice.toIntSubmodule :=
  periodLatticeImage_discreteTopology_of_bundle (chosenC3 X).base.discreteness

/-- IsZLattice on the lattice. -/
instance instIsZLatticeLattice :
    IsZLattice ℝ (PeriodLatticeOfRankTwoG.ofBundle
      (PeriodPairingData.ofSmoothCycle X)
      (chosenC3 X).base.basis (chosenC3 X).base.discreteness).lattice.toIntSubmodule :=
  periodLatticeImage_isZLattice_of_bundle (chosenC3 X).base.discreteness

/-- **Item 11**: `JacobianAnalyticChoice X` is compact. -/
instance instCompactSpace : CompactSpace (JacobianAnalyticChoice X) :=
  PeriodLatticeOfRankTwoG.compactSpaceHypothesis_holds _

/-- **Items 5 + 12**: charted-space + manifold structure. -/
instance instChartedSpace :
    ChartedSpace (Fin (JacobianChallenge.genus X) → ℂ) (JacobianAnalyticChoice X) :=
  (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds _).toChartedSpace

instance instIsManifold :
    @IsManifold ℂ _ (Fin (JacobianChallenge.genus X) → ℂ) _ _
      (Fin (JacobianChallenge.genus X) → ℂ) _
      (modelWithCornersSelf ℂ (Fin (JacobianChallenge.genus X) → ℂ)) ω
      (JacobianAnalyticChoice X) _ instChartedSpace :=
  (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds _).toIsManifold

/-- **Item 13**: Lie-additive-group structure. -/
instance instLieAddGroup :
    @LieAddGroup ℂ _ (Fin (JacobianChallenge.genus X) → ℂ) _
      (Fin (JacobianChallenge.genus X) → ℂ) _ _
      (modelWithCornersSelf ℂ (Fin (JacobianChallenge.genus X) → ℂ)) ω
      (JacobianAnalyticChoice X) _ _ instChartedSpace :=
  PeriodLatticeOfRankTwoG.lieAddGroupHypothesis_holds _

/-! ## The Abel-Jacobi AddEquiv to Pic⁰ X -/

/-- **The classical-choice AddEquiv** `Pic⁰ X ≃+ JacobianAnalyticChoice X`,
extracted from the chosen `C3FullInputExt`'s `abelJacobiEquiv`. -/
noncomputable def picZeroEquiv :
    Pic0 X ≃+ JacobianAnalyticChoice X :=
  (chosenC3 X).base.abelJacobiEquiv

end JacobianChallenge

end
