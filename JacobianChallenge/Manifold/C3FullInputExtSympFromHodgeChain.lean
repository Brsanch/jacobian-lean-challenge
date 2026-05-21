/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothHomologyDataPackageFromHodgeChain
import JacobianChallenge.Manifold.C3FullInputExtSympFromPackage

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # `C3FullInputExtSymp` end-to-end from the Hodge–Riemann chain (chip 6)

This file ships the final composite producing `Nonempty (C3FullInputExtSymp
X)` directly from a small list of named classical hypotheses. It combines
chip 4 (`SmoothHomologyDataPackage` from the Hodge chain) with the
existing `nonempty_c3FullInputExtSymp_of_package_and_named_hypotheses`
(which finishes the rest of the C3 input from a package + 4 AJ
hypotheses).

Net atomic-input list for `Nonempty (C3FullInputExtSymp X)` at general
genus on a compact connected complex 1-manifold:

* `basis_ω` — a chosen ℂ-basis of `H⁰(X, Ω)`;
* `basePoint` — a chosen point of `X`;
* `SmoothSymplecticBasis` — 2g based loops at `basePoint`;
* `SmoothHurewiczHypothesis` — smooth-Hurewicz on the basis loops;
* `CompleteHodgeRiemannHypothesis` — `(J, H, PD, first, bridge)`;
* `AbelHypothesis` — Abel's theorem (Σ residues = 0 ⟹ trivial-in-Jacobian);
* `JacobiInversion` — Jacobi's inversion theorem;
* `AbelJacobiSmoothness` — smoothness of the Abel–Jacobi map;
* `AbelJacobiInjective` — injectivity of the Abel–Jacobi map.

This is the smallest *concrete* named-hypothesis list known to discharge
the C3 input at general genus (each item is a well-established classical
theorem in topology, Hodge theory, or abelian-variety theory).

## What this file ships

* `nonempty_c3FullInputExtSymp_of_hodgeChain_and_AJ_hypotheses` — the
  end-to-end constructor.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **End-to-end: `Nonempty (C3FullInputExtSymp X)` from the Hodge chain
+ 4 AJ named hypotheses.** Combines chip 4 with
`nonempty_c3FullInputExtSymp_of_package_and_named_hypotheses`. -/
theorem nonempty_c3FullInputExtSymp_of_hodgeChain_and_AJ_hypotheses
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (basePoint : X)
    (symplecticBasis :
      SmoothSymplecticBasis 𝓘(ℝ, ℂ) X basePoint (JacobianChallenge.genus X))
    (hurewicz : SmoothHurewiczHypothesis symplecticBasis)
    (hHR : CompleteHodgeRiemannHypothesis
      (PeriodPairingData.ofSmoothCycle X) basis_ω symplecticBasis.cycleGens)
    (hAbel :
      let pkg : SmoothHomologyDataPackage basis_ω :=
        SmoothHomologyDataPackage.ofHodgeChain basePoint symplecticBasis
          hurewicz hHR
      let h_PLSB :=
        Classical.choice
          (nonempty_periodLatticeSymplecticBundle_of_smoothHomologyDataPackage pkg)
      let h_ajInput :=
        AbelJacobiInputSymp.ofSmoothPathConnected (α := basis_ω) (h := h_PLSB)
          smoothPathConnected_of_preconnected (Classical.arbitrary X)
      AbelJacobiInputSymp.AbelHypothesis h_ajInput)
    (hJI :
      let pkg : SmoothHomologyDataPackage basis_ω :=
        SmoothHomologyDataPackage.ofHodgeChain basePoint symplecticBasis
          hurewicz hHR
      let h_PLSB :=
        Classical.choice
          (nonempty_periodLatticeSymplecticBundle_of_smoothHomologyDataPackage pkg)
      let h_ajInput :=
        AbelJacobiInputSymp.ofSmoothPathConnected (α := basis_ω) (h := h_PLSB)
          smoothPathConnected_of_preconnected (Classical.arbitrary X)
      AbelJacobiInputSymp.JacobiInversion h_ajInput hAbel)
    (hSmooth :
      let pkg : SmoothHomologyDataPackage basis_ω :=
        SmoothHomologyDataPackage.ofHodgeChain basePoint symplecticBasis
          hurewicz hHR
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
        SmoothHomologyDataPackage.ofHodgeChain basePoint symplecticBasis
          hurewicz hHR
      let h_PLSB :=
        Classical.choice
          (nonempty_periodLatticeSymplecticBundle_of_smoothHomologyDataPackage pkg)
      let h_ajInput :=
        AbelJacobiInputSymp.ofSmoothPathConnected (α := basis_ω) (h := h_PLSB)
          smoothPathConnected_of_preconnected (Classical.arbitrary X)
      AbelJacobiInjectiveSymp h_ajInput) :
    Nonempty (C3FullInputExtSymp X) :=
  nonempty_c3FullInputExtSymp_of_package_and_named_hypotheses basis_ω
    (SmoothHomologyDataPackage.ofHodgeChain basePoint symplecticBasis
      hurewicz hHR)
    hAbel hJI hSmooth hInj

end JacobianChallenge

end
