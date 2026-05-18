/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3FullInputExtSymp
import JacobianChallenge.Manifold.JacobianAnalyticChoice

set_option linter.unusedSectionVars false

/-! # `JacobianAnalyticChoiceSymp X` — analytic Jacobian via the symplectic bundle

Symplectic parallel of `JacobianAnalyticChoice`. Given
`[Nonempty (C3FullInputExtSymp X)]` (a single typeclass-bundled
classical existence input on the corrected `PeriodLatticeSymplecticBundle`),
this file builds the honest analytic Jacobian and all 7 structural
instances:

* `AddCommGroup`, `TopologicalSpace`, `T2Space` (items 3, 4, 10).
* `CompactSpace` (item 11).
* `ChartedSpace (Fin (genus X) → ℂ)` (item 5).
* `IsManifold (𝓘(ℂ, ℂ)) ω` (item 12).
* `LieAddGroup (𝓘(ℂ, ℂ)) ω` (item 13).

Plus `picZeroEquivSymp : Pic⁰ X ≃+ JacobianAnalyticChoiceSymp X` for the
bridge back to Basic.lean's `Jacobian X = Pic⁰ X`.

This is the final chip of the 2026-05-17 `PeriodLatticeSymplecticBundle`
refactor arc. Combined with the prior 8 chips, the full symplectic
chain is now in tree side-by-side with the legacy chain, and the
genus-0 case unconditionally constructs an inhabitant via the bundle
route (no bypass).

No `sorry`, no `axiom`. -/

open scoped Manifold Topology ContDiff
open Module

noncomputable section

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [Nonempty (C3FullInputExtSymp X)]

/-- A canonical `C3FullInputExtSymp X` extracted via `Classical.choice`. -/
noncomputable def chosenC3Symp : C3FullInputExtSymp X :=
  Classical.choice inferInstance

/-- **The analytic Jacobian via classical choice on the symplectic bundle.** -/
noncomputable abbrev JacobianAnalyticChoiceSymp : Type :=
  AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle X)
    (chosenC3Symp X).base.basis (chosenC3Symp X).base.discreteness

variable {X}

/-! ## Instance discharges -/

instance instAddCommGroupSymp : AddCommGroup (JacobianAnalyticChoiceSymp X) :=
  inferInstanceAs (AddCommGroup
    (AnalyticJacobianSymp _ (chosenC3Symp X).base.basis
      (chosenC3Symp X).base.discreteness))

instance instTopologicalSpaceSymp : TopologicalSpace (JacobianAnalyticChoiceSymp X) :=
  inferInstanceAs (TopologicalSpace
    (AnalyticJacobianSymp _ (chosenC3Symp X).base.basis
      (chosenC3Symp X).base.discreteness))

instance instT2SpaceSymp : T2Space (JacobianAnalyticChoiceSymp X) :=
  inferInstanceAs (T2Space
    (AnalyticJacobianSymp _ (chosenC3Symp X).base.basis
      (chosenC3Symp X).base.discreteness))

/-- `DiscreteTopology` on the lattice (needed for downstream instances). -/
instance instDiscreteTopologyLatticeSymp :
    DiscreteTopology (PeriodLatticeOfRankTwoG.ofSymplectic
      (PeriodPairingData.ofSmoothCycle X)
      (chosenC3Symp X).base.basis
      (chosenC3Symp X).base.discreteness).lattice.toIntSubmodule :=
  PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle
    (chosenC3Symp X).base.discreteness

/-- `IsZLattice` on the lattice. -/
instance instIsZLatticeLatticeSymp :
    IsZLattice ℝ (PeriodLatticeOfRankTwoG.ofSymplectic
      (PeriodPairingData.ofSmoothCycle X)
      (chosenC3Symp X).base.basis
      (chosenC3Symp X).base.discreteness).lattice.toIntSubmodule :=
  PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle
    (chosenC3Symp X).base.discreteness

/-- **Item 11**: `JacobianAnalyticChoiceSymp X` is compact. -/
instance instCompactSpaceSymp : CompactSpace (JacobianAnalyticChoiceSymp X) :=
  PeriodLatticeOfRankTwoG.compactSpaceHypothesis_holds _

/-- **Items 5 + 12**: charted-space + manifold structure. -/
instance instChartedSpaceSymp :
    ChartedSpace (Fin (JacobianChallenge.genus X) → ℂ)
      (JacobianAnalyticChoiceSymp X) :=
  (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds _).toChartedSpace

instance instIsManifoldSymp :
    @IsManifold ℂ _ (Fin (JacobianChallenge.genus X) → ℂ) _ _
      (Fin (JacobianChallenge.genus X) → ℂ) _
      (modelWithCornersSelf ℂ (Fin (JacobianChallenge.genus X) → ℂ)) ω
      (JacobianAnalyticChoiceSymp X) _ instChartedSpaceSymp :=
  (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds _).toIsManifold

/-- **Item 13**: Lie-additive-group structure. -/
instance instLieAddGroupSymp :
    @LieAddGroup ℂ _ (Fin (JacobianChallenge.genus X) → ℂ) _
      (Fin (JacobianChallenge.genus X) → ℂ) _ _
      (modelWithCornersSelf ℂ (Fin (JacobianChallenge.genus X) → ℂ)) ω
      (JacobianAnalyticChoiceSymp X) _ _ instChartedSpaceSymp :=
  PeriodLatticeOfRankTwoG.lieAddGroupHypothesis_holds _

/-! ## The Abel-Jacobi AddEquiv to Pic⁰ X -/

/-- **The classical-choice AddEquiv (symplectic):
`Pic⁰ X ≃+ JacobianAnalyticChoiceSymp X`.** Extracted from the chosen
`C3FullInputExtSymp`'s `abelJacobiEquiv`. -/
noncomputable def picZeroEquivSymp :
    Pic0 X ≃+ JacobianAnalyticChoiceSymp X :=
  (chosenC3Symp X).base.abelJacobiEquiv

end JacobianChallenge

end
