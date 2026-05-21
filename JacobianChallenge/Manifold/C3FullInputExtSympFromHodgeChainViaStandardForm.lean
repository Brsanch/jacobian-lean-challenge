/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothHomologyDataPackageFromHodgeChainViaStandardForm
import JacobianChallenge.Manifold.C3FullInputExtSympFromPackage

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # End-to-end `C3FullInputExtSymp` via simplified Hodge bundle + AJ
(chip 17)

Headline composite: produces `Nonempty (C3FullInputExtSymp X)` from
the smallest known concrete named-hypothesis list using the
`CompleteHodgeRiemannHypothesisViaStandardForm` simplification (chip
14) for the period-lattice side, and the 4 named AJ hypotheses for
the Abel-Jacobi side.

Final atomic-input list at general genus on a compact connected
complex 1-manifold:

* `basis_ω` — a ℂ-basis of `H⁰(X, Ω)` (the trivial `defaultHolomorphicOneFormBasis`
  exists);
* `basePoint` — a chosen point of `X` (`Classical.arbitrary` suffices);
* `SmoothSymplecticBasis` — 2g based loops at `basePoint` (surface
  classification);
* `SmoothHurewiczHypothesis` — smooth-Hurewicz on basis loops;
* `(J, RiemannBilinearFirstRelation, HodgeRiemannBridgeHypothesis(J,
  standardHodgeForm basis_ω))` — the simplified bridge bundle (no PD
  obligation, no choice of `H`);
* `AbelHypothesis` — Abel's theorem (~2000-4000 LOC of classical
  residue theorem);
* `JacobiInversion` — Jacobi's inversion theorem;
* `AbelJacobiSmoothness` — smoothness of Abel-Jacobi map;
* `AbelJacobiInjective` — injectivity of Abel-Jacobi map.

## What this file ships

* `nonempty_c3FullInputExtSymp_of_hodgeChainViaStandardForm_and_AJ_hypotheses`
  — the end-to-end constructor.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Final end-to-end: `Nonempty (C3FullInputExtSymp X)` from the
simplified Hodge chain + 4 AJ named hypotheses.** -/
theorem nonempty_c3FullInputExtSymp_of_hodgeChainViaStandardForm_and_AJ_hypotheses
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (basePoint : X)
    (symplecticBasis :
      SmoothSymplecticBasis 𝓘(ℝ, ℂ) X basePoint (JacobianChallenge.genus X))
    (hurewicz : SmoothHurewiczHypothesis symplecticBasis)
    (hHRStd : CompleteHodgeRiemannHypothesisViaStandardForm
      (PeriodPairingData.ofSmoothCycle X) basis_ω symplecticBasis.cycleGens)
    (hAbel :
      let pkg : SmoothHomologyDataPackage basis_ω :=
        SmoothHomologyDataPackage.ofHodgeChainViaStandardForm basePoint
          symplecticBasis hurewicz hHRStd
      let h_PLSB :=
        Classical.choice
          (nonempty_periodLatticeSymplecticBundle_of_smoothHomologyDataPackage pkg)
      let h_ajInput :=
        AbelJacobiInputSymp.ofSmoothPathConnected (α := basis_ω) (h := h_PLSB)
          smoothPathConnected_of_preconnected (Classical.arbitrary X)
      AbelJacobiInputSymp.AbelHypothesis h_ajInput)
    (hJI :
      let pkg : SmoothHomologyDataPackage basis_ω :=
        SmoothHomologyDataPackage.ofHodgeChainViaStandardForm basePoint
          symplecticBasis hurewicz hHRStd
      let h_PLSB :=
        Classical.choice
          (nonempty_periodLatticeSymplecticBundle_of_smoothHomologyDataPackage pkg)
      let h_ajInput :=
        AbelJacobiInputSymp.ofSmoothPathConnected (α := basis_ω) (h := h_PLSB)
          smoothPathConnected_of_preconnected (Classical.arbitrary X)
      AbelJacobiInputSymp.JacobiInversion h_ajInput hAbel)
    (hSmooth :
      let pkg : SmoothHomologyDataPackage basis_ω :=
        SmoothHomologyDataPackage.ofHodgeChainViaStandardForm basePoint
          symplecticBasis hurewicz hHRStd
      let h_PLSB :=
        Classical.choice
          (nonempty_periodLatticeSymplecticBundle_of_smoothHomologyDataPackage pkg)
      let h_ajInput :=
        AbelJacobiInputSymp.ofSmoothPathConnected (α := basis_ω) (h := h_PLSB)
          smoothPathConnected_of_preconnected (Classical.arbitrary X)
      haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle h_PLSB
      haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle h_PLSB
      haveI : DiscreteTopology
          (PeriodLatticeOfRankTwoG.ofSymplectic
            (PeriodPairingData.ofSmoothCycle X) basis_ω h_PLSB).lattice.toIntSubmodule :=
        PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle h_PLSB
      haveI : IsZLattice ℝ
          (PeriodLatticeOfRankTwoG.ofSymplectic
            (PeriodPairingData.ofSmoothCycle X) basis_ω h_PLSB).lattice.toIntSubmodule :=
        PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle h_PLSB
      AbelJacobiSmoothnessSymp h_ajInput)
    (hInj :
      let pkg : SmoothHomologyDataPackage basis_ω :=
        SmoothHomologyDataPackage.ofHodgeChainViaStandardForm basePoint
          symplecticBasis hurewicz hHRStd
      let h_PLSB :=
        Classical.choice
          (nonempty_periodLatticeSymplecticBundle_of_smoothHomologyDataPackage pkg)
      let h_ajInput :=
        AbelJacobiInputSymp.ofSmoothPathConnected (α := basis_ω) (h := h_PLSB)
          smoothPathConnected_of_preconnected (Classical.arbitrary X)
      AbelJacobiInjectiveSymp h_ajInput) :
    Nonempty (C3FullInputExtSymp X) :=
  nonempty_c3FullInputExtSymp_of_package_and_named_hypotheses basis_ω
    (SmoothHomologyDataPackage.ofHodgeChainViaStandardForm basePoint
      symplecticBasis hurewicz hHRStd)
    hAbel hJI hSmooth hInj

end JacobianChallenge

end
