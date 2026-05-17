/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3FullInputInstances
import JacobianChallenge.Manifold.JacobianAnalyticPerCurveBundle
import JacobianChallenge.Manifold.JacobianAnalyticPushforwardLiftOfCurve
import JacobianChallenge.Manifold.JacobianAnalyticPullbackLiftOfCurveCanonical
import JacobianChallenge.Manifold.JacobianAnalyticPushforwardPullbackContMDiff

set_option linter.unusedSectionVars false

/-! # Per-curve `C3FullInput` extension: items 18 + 21

For each smooth curve map `f : X → Y` between compact connected complex
1-manifolds, items 18 (pushforward `ContMDiff`) and 21 (pullback
`ContMDiff`) on the analytic Jacobian require:

* a `C3FullInput X` (the source-side full bundle); and
* a `C3FullInput Y` (the target-side bundle); and
* a **lattice-match certificate** — the per-curve named classical input
  asserting `pushforwardLinearLift αX αY f hf` carries the X-period
  lattice into the Y-period lattice (period-pairing adjunction).

This file packages the per-curve named input as `C3FullInputCurve B_X B_Y f hf`
and provides the analytic-side discharges (items 18 + 21 on AJ).

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology ContDiff
open Module

noncomputable section

namespace JacobianChallenge

universe u

variable {X Y : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-- **Per-curve C3 input.** Given source / target `C3FullInput`s and a
holomorphic curve map `f : X → Y`, the lattice-match certificates for
the pushforward (X→Y) and pullback (Y→X) directions. -/
structure C3FullInputCurve (B_X : C3FullInput X) (B_Y : C3FullInput Y)
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) where
  /-- Pushforward direction lattice-match (period adjunction). -/
  pushforward_match :
    ∀ v ∈ (PeriodLatticeOfRankTwoG.ofBundle
              (PeriodPairingData.ofSmoothCycle X) B_X.basis
              B_X.discreteness).lattice.toIntSubmodule,
      HolomorphicOneForm.pushforwardLinearLift B_X.basis B_Y.basis f hf v
        ∈ (PeriodLatticeOfRankTwoG.ofBundle
              (PeriodPairingData.ofSmoothCycle Y) B_Y.basis
              B_Y.discreteness).lattice.toIntSubmodule
  /-- Pullback direction lattice-match. -/
  pullback_T : (Fin (JacobianChallenge.genus Y) → ℂ) →L[ℂ]
        (Fin (JacobianChallenge.genus X) → ℂ)
  pullback_match :
    ∀ v ∈ (PeriodLatticeOfRankTwoG.ofBundle
              (PeriodPairingData.ofSmoothCycle Y) B_Y.basis
              B_Y.discreteness).lattice.toIntSubmodule,
      pullback_T v ∈ (PeriodLatticeOfRankTwoG.ofBundle
              (PeriodPairingData.ofSmoothCycle X) B_X.basis
              B_X.discreteness).lattice.toIntSubmodule

namespace C3FullInputCurve

variable {B_X : C3FullInput X} {B_Y : C3FullInput Y}
  {f : X → Y} {hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f}

/-- Pushforward `JacobianAnalyticPushforwardLift` from the curve bundle. -/
noncomputable def toPushforwardLift (C : C3FullInputCurve B_X B_Y f hf) :
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
    JacobianAnalyticPushforwardLift
      (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle X)
        B_X.basis B_X.discreteness)
      (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle Y)
        B_Y.basis B_Y.discreteness) := by
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
  exact JacobianAnalyticPushforwardLift.ofCurveMap _ _
    B_X.basis B_Y.basis f hf C.pushforward_match

/-- Pullback `JacobianAnalyticPullbackLift` from the curve bundle. -/
noncomputable def toPullbackLift (C : C3FullInputCurve B_X B_Y f hf) :
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
    JacobianAnalyticPullbackLift
      (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle X)
        B_X.basis B_X.discreteness)
      (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle Y)
        B_Y.basis B_Y.discreteness) := by
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
  exact JacobianAnalyticPullbackLift.ofCurveMap _ _ f hf C.pullback_T
    C.pullback_match

end C3FullInputCurve

end JacobianChallenge

end
