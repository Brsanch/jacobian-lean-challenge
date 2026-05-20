/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothHomologyDataPackage
import JacobianChallenge.Manifold.C3FullInputExtSymp
import JacobianChallenge.Manifold.SmoothPathConnectedSymp

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # `C3FullInputExtSymp` from `SmoothHomologyDataPackage` + 4 named hypotheses

End-to-end constructor at general genus. On any compact connected
complex 1-manifold `X`, this exhibits how the open content of
`Nonempty (C3FullInputExtSymp X)` factors:

* `basis_ω` — a ℂ-basis of `HolomorphicOneForm X` (unconditional from
  item 1, taken here as a parameter for flexibility).
* `pkg : SmoothHomologyDataPackage basis_ω` — the single bundled
  period-lattice atom (the three named atoms remaining at general
  genus: surface classification + Hurewicz + Hodge bilinear non-
  degeneracy).
* `hAbel` — Abel's theorem on `X` against an explicit AJ input.
* `hJI` — Jacobi inversion (parametric on `hAbel`).
* `hSmooth` — Abel-Jacobi smoothness on `X` against an explicit AJ input.
* `hInj` — Abel-Jacobi injectivity on `X` against an explicit AJ input.

The smoothness/injectivity arguments are stated against an explicit
`AbelJacobiInputSymp` parameter (`h_ajInput`) so the user can supply
any base point + path-picker (Classical.choose or otherwise). Smooth-
path-connectedness is the natural source for the AJ input via
`smoothPathConnected_of_preconnected`, but this constructor stays
hypothesis-style by taking `h_ajInput` as data.

This is the **cleanest end-to-end statement** of which named classical
hypotheses remain open at general genus to inhabit the analytic
Jacobian: exactly **four** (Abel, Jacobi inversion, AJ smoothness, AJ
injectivity), plus the single bundled period-lattice atom.

## What this file ships

* `c3FullInputExtSymp_of_package` — the explicit constructor (takes
  explicit PLSB witness + AJ input).
* `nonempty_c3FullInputExtSymp_of_package_and_named_hypotheses` —
  `Nonempty`-form headline using `smoothPathConnected_of_preconnected`
  to fill in the AJ input automatically.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Module Submodule

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Explicit `C3FullInputExtSymp X` from an explicit PLSB witness +
explicit AJ input + four named classical hypotheses.**

Hypothesis-style: takes the PLSB and the AJ input as explicit data.
For the auto-discharged version that builds the AJ input from
`smoothPathConnected_of_preconnected`, see
`nonempty_c3FullInputExtSymp_of_package_and_named_hypotheses` below. -/
noncomputable def c3FullInputExtSymp_of_package
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (h_PLSB : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle X) basis_ω)
    (h_ajInput : AbelJacobiInputSymp basis_ω h_PLSB)
    (hAbel : AbelJacobiInputSymp.AbelHypothesis h_ajInput)
    (hJI : AbelJacobiInputSymp.JacobiInversion h_ajInput hAbel)
    (hSmooth :
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
    (hInj : AbelJacobiInjectiveSymp h_ajInput) :
    C3FullInputExtSymp X :=
  { base :=
      { basis := basis_ω
        discreteness := h_PLSB
        ajInput := h_ajInput
        abel := hAbel
        jacobi := hJI }
    smoothness := hSmooth
    injective := hInj }

/-- **`Nonempty (C3FullInputExtSymp X)` from a `SmoothHomologyDataPackage`
+ four named classical hypotheses.**

Headline form: the PLSB witness is filled in by
`nonempty_periodLatticeSymplecticBundle_of_smoothHomologyDataPackage`
(via `Classical.choice`), and the AJ input by
`smoothPathConnected_of_preconnected` + `Classical.arbitrary` (via
`AbelJacobiInputSymp.nonempty_of_preconnected`).

The user must supply Abel + Jacobi + AJ smoothness + AJ injectivity as
named hypotheses on the *specific* PLSB/AJ-input pair (built here).
This makes the four remaining open named classical hypotheses
**explicit at the type level**. -/
theorem nonempty_c3FullInputExtSymp_of_package_and_named_hypotheses
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (pkg : SmoothHomologyDataPackage basis_ω)
    (hAbel :
      let h_PLSB :=
        Classical.choice
          (nonempty_periodLatticeSymplecticBundle_of_smoothHomologyDataPackage pkg)
      let h_ajInput :=
        AbelJacobiInputSymp.ofSmoothPathConnected (α := basis_ω) (h := h_PLSB)
          smoothPathConnected_of_preconnected (Classical.arbitrary X)
      AbelJacobiInputSymp.AbelHypothesis h_ajInput)
    (hJI :
      let h_PLSB :=
        Classical.choice
          (nonempty_periodLatticeSymplecticBundle_of_smoothHomologyDataPackage pkg)
      let h_ajInput :=
        AbelJacobiInputSymp.ofSmoothPathConnected (α := basis_ω) (h := h_PLSB)
          smoothPathConnected_of_preconnected (Classical.arbitrary X)
      AbelJacobiInputSymp.JacobiInversion h_ajInput hAbel)
    (hSmooth :
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
      let h_PLSB :=
        Classical.choice
          (nonempty_periodLatticeSymplecticBundle_of_smoothHomologyDataPackage pkg)
      let h_ajInput :=
        AbelJacobiInputSymp.ofSmoothPathConnected (α := basis_ω) (h := h_PLSB)
          smoothPathConnected_of_preconnected (Classical.arbitrary X)
      AbelJacobiInjectiveSymp h_ajInput) :
    Nonempty (C3FullInputExtSymp X) :=
  ⟨c3FullInputExtSymp_of_package basis_ω
    (Classical.choice
      (nonempty_periodLatticeSymplecticBundle_of_smoothHomologyDataPackage pkg))
    (AbelJacobiInputSymp.ofSmoothPathConnected
      (α := basis_ω)
      (h := Classical.choice
        (nonempty_periodLatticeSymplecticBundle_of_smoothHomologyDataPackage pkg))
      smoothPathConnected_of_preconnected (Classical.arbitrary X))
    hAbel hJI hSmooth hInj⟩

end JacobianChallenge

end
