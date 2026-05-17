/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3FullInputInstances
import JacobianChallenge.Manifold.JacobianAnalyticBasicLeanReduction
import JacobianChallenge.Manifold.JacobianAnalyticOfCurveContMDiff
import JacobianChallenge.Manifold.JacobianAnalyticOfCurveInjective
import JacobianChallenge.Manifold.JacobianAnalyticClosureBundle

set_option linter.unusedSectionVars false

/-! # Extended C3 input: + Abel-Jacobi smoothness/injectivity

`C3FullInput X` carries the four classical inputs that suffice to
construct the analytic Jacobian and its underlying group structure
(items 4, 5, 10, 11, 12, 13 on the analytic side).

To additionally discharge items 16, 17 on the analytic side
(injectivity + smoothness of the pointwise Abel-Jacobi map), we need
two further named inputs:

* `AbelJacobiSmoothness` — `ContMDiff` of `B.abelJacobiPoint`.
* `AbelJacobiInjective` — injectivity of `B.abelJacobiPoint` under
  `0 < genus X`.

This file packages these into `C3FullInputExt X` and extracts the
canonical `JacobianAnalyticClosureBundle` for downstream callers.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology ContDiff
open Module Submodule

noncomputable section

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Extended C3 input bundle**: `C3FullInput X` plus the two extra
predicates needed to discharge items 16 + 17 on the analytic Jacobian. -/
structure C3FullInputExt where
  /-- The base `C3FullInput`. -/
  base : C3FullInput X
  /-- Abel-Jacobi smoothness (item 17). -/
  smoothness :
    haveI := periodLatticeImage_discreteTopology_of_bundle base.discreteness
    haveI := periodLatticeImage_isZLattice_of_bundle base.discreteness
    haveI : DiscreteTopology
        (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle X)
          base.basis base.discreteness).lattice.toIntSubmodule :=
      periodLatticeImage_discreteTopology_of_bundle base.discreteness
    haveI : IsZLattice ℝ
        (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle X)
          base.basis base.discreteness).lattice.toIntSubmodule :=
      periodLatticeImage_isZLattice_of_bundle base.discreteness
    AbelJacobiSmoothness base.ajInput
  /-- Abel-Jacobi point-injectivity (item 16). -/
  injective : AbelJacobiInjective base.ajInput

namespace C3FullInputExt

variable {X}

/-- **Extract the `JacobianAnalyticClosureBundle`** from the extended
C3 input. This bundles items 16 + 17 content for downstream
`analyticJacobian_ofCurve_*_of_bundle` discharges. -/
noncomputable def toClosureBundle (B : C3FullInputExt X) :
    haveI := periodLatticeImage_discreteTopology_of_bundle B.base.discreteness
    haveI := periodLatticeImage_isZLattice_of_bundle B.base.discreteness
    haveI : DiscreteTopology
        (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle X)
          B.base.basis B.base.discreteness).lattice.toIntSubmodule :=
      periodLatticeImage_discreteTopology_of_bundle B.base.discreteness
    haveI : IsZLattice ℝ
        (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle X)
          B.base.basis B.base.discreteness).lattice.toIntSubmodule :=
      periodLatticeImage_isZLattice_of_bundle B.base.discreteness
    JacobianAnalyticClosureBundle B.base.basis B.base.discreteness := by
  haveI := periodLatticeImage_discreteTopology_of_bundle B.base.discreteness
  haveI := periodLatticeImage_isZLattice_of_bundle B.base.discreteness
  haveI : DiscreteTopology
      (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle X)
        B.base.basis B.base.discreteness).lattice.toIntSubmodule :=
    periodLatticeImage_discreteTopology_of_bundle B.base.discreteness
  haveI : IsZLattice ℝ
      (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle X)
        B.base.basis B.base.discreteness).lattice.toIntSubmodule :=
    periodLatticeImage_isZLattice_of_bundle B.base.discreteness
  exact
    { abel_jacobi_input := B.base.ajInput
      abel_jacobi_smoothness := B.smoothness
      abel_jacobi_injective := B.injective }

end C3FullInputExt

end JacobianChallenge

end
