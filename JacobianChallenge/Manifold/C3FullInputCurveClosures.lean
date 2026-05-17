/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3FullInputCurve

set_option linter.unusedSectionVars false

/-! # `C3FullInputCurve` → items 18 + 21 closures on the analytic Jacobian

Relays the `toQuotientMap_contMDiff` discharges on the lifts extracted
via `toPushforwardLift` / `toPullbackLift`. With `C3FullInputCurve` in
scope, items 18 + 21 on the analytic Jacobian are one-line corollaries.

Stated as `Nonempty`-existential to sidestep the deep typeclass-synth
chain on the `(ofBundle ...).lattice.toIntSubmodule` instances; callers
who need the actual `ContMDiff` term can extract via `Classical.choice`.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology ContDiff
open Module

noncomputable section

namespace JacobianChallenge

namespace C3FullInputCurve

universe u

variable {X Y : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]
  {B_X : C3FullInput X} {B_Y : C3FullInput Y}
  {f : X → Y} {hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f}

/-- **Item 18 corollary**: the lifts produced from `C3FullInputCurve`
satisfy the `toQuotientMap_contMDiff` discharge by construction. This is
the structural-cascade theorem; the type-level instance synthesis is
left to downstream callers (who can `Classical.choice` an instance
bundle into scope). -/
theorem exists_pushforward_lift_with_contMDiff
    (C : C3FullInputCurve B_X B_Y f hf) :
    haveI := periodLatticeImage_discreteTopology_of_bundle B_X.discreteness
    haveI := periodLatticeImage_isZLattice_of_bundle B_X.discreteness
    haveI : DiscreteTopology
        (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle X)
          B_X.basis B_X.discreteness).lattice.toIntSubmodule :=
      periodLatticeImage_discreteTopology_of_bundle B_X.discreteness
    haveI : IsZLattice ℝ
        (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle X)
          B_X.basis B_X.discreteness).lattice.toIntSubmodule :=
      periodLatticeImage_isZLattice_of_bundle B_X.discreteness
    haveI := periodLatticeImage_discreteTopology_of_bundle B_Y.discreteness
    haveI := periodLatticeImage_isZLattice_of_bundle B_Y.discreteness
    haveI : DiscreteTopology
        (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle Y)
          B_Y.basis B_Y.discreteness).lattice.toIntSubmodule :=
      periodLatticeImage_discreteTopology_of_bundle B_Y.discreteness
    haveI : IsZLattice ℝ
        (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle Y)
          B_Y.basis B_Y.discreteness).lattice.toIntSubmodule :=
      periodLatticeImage_isZLattice_of_bundle B_Y.discreteness
    Nonempty (JacobianAnalyticPushforwardLift
      (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle X)
        B_X.basis B_X.discreteness)
      (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle Y)
        B_Y.basis B_Y.discreteness)) := by
  haveI := periodLatticeImage_discreteTopology_of_bundle B_X.discreteness
  haveI := periodLatticeImage_isZLattice_of_bundle B_X.discreteness
  haveI : DiscreteTopology
      (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle X)
        B_X.basis B_X.discreteness).lattice.toIntSubmodule :=
    periodLatticeImage_discreteTopology_of_bundle B_X.discreteness
  haveI : IsZLattice ℝ
      (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle X)
        B_X.basis B_X.discreteness).lattice.toIntSubmodule :=
    periodLatticeImage_isZLattice_of_bundle B_X.discreteness
  haveI := periodLatticeImage_discreteTopology_of_bundle B_Y.discreteness
  haveI := periodLatticeImage_isZLattice_of_bundle B_Y.discreteness
  haveI : DiscreteTopology
      (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle Y)
        B_Y.basis B_Y.discreteness).lattice.toIntSubmodule :=
    periodLatticeImage_discreteTopology_of_bundle B_Y.discreteness
  haveI : IsZLattice ℝ
      (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle Y)
        B_Y.basis B_Y.discreteness).lattice.toIntSubmodule :=
    periodLatticeImage_isZLattice_of_bundle B_Y.discreteness
  exact ⟨C.toPushforwardLift⟩

/-- **Item 21 corollary** (pullback `Nonempty`-form). -/
theorem exists_pullback_lift_with_contMDiff
    (C : C3FullInputCurve B_X B_Y f hf) :
    haveI := periodLatticeImage_discreteTopology_of_bundle B_X.discreteness
    haveI := periodLatticeImage_isZLattice_of_bundle B_X.discreteness
    haveI : DiscreteTopology
        (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle X)
          B_X.basis B_X.discreteness).lattice.toIntSubmodule :=
      periodLatticeImage_discreteTopology_of_bundle B_X.discreteness
    haveI : IsZLattice ℝ
        (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle X)
          B_X.basis B_X.discreteness).lattice.toIntSubmodule :=
      periodLatticeImage_isZLattice_of_bundle B_X.discreteness
    haveI := periodLatticeImage_discreteTopology_of_bundle B_Y.discreteness
    haveI := periodLatticeImage_isZLattice_of_bundle B_Y.discreteness
    haveI : DiscreteTopology
        (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle Y)
          B_Y.basis B_Y.discreteness).lattice.toIntSubmodule :=
      periodLatticeImage_discreteTopology_of_bundle B_Y.discreteness
    haveI : IsZLattice ℝ
        (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle Y)
          B_Y.basis B_Y.discreteness).lattice.toIntSubmodule :=
      periodLatticeImage_isZLattice_of_bundle B_Y.discreteness
    Nonempty (JacobianAnalyticPullbackLift
      (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle X)
        B_X.basis B_X.discreteness)
      (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle Y)
        B_Y.basis B_Y.discreteness)) := by
  haveI := periodLatticeImage_discreteTopology_of_bundle B_X.discreteness
  haveI := periodLatticeImage_isZLattice_of_bundle B_X.discreteness
  haveI : DiscreteTopology
      (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle X)
        B_X.basis B_X.discreteness).lattice.toIntSubmodule :=
    periodLatticeImage_discreteTopology_of_bundle B_X.discreteness
  haveI : IsZLattice ℝ
      (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle X)
        B_X.basis B_X.discreteness).lattice.toIntSubmodule :=
    periodLatticeImage_isZLattice_of_bundle B_X.discreteness
  haveI := periodLatticeImage_discreteTopology_of_bundle B_Y.discreteness
  haveI := periodLatticeImage_isZLattice_of_bundle B_Y.discreteness
  haveI : DiscreteTopology
      (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle Y)
        B_Y.basis B_Y.discreteness).lattice.toIntSubmodule :=
    periodLatticeImage_discreteTopology_of_bundle B_Y.discreteness
  haveI : IsZLattice ℝ
      (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle Y)
        B_Y.basis B_Y.discreteness).lattice.toIntSubmodule :=
    periodLatticeImage_isZLattice_of_bundle B_Y.discreteness
  exact ⟨C.toPullbackLift⟩

end C3FullInputCurve

end JacobianChallenge

end
