/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3FullInputExt
import JacobianChallenge.Manifold.JacobianAnalyticBasicLeanReduction

set_option linter.unusedSectionVars false

/-! # `C3FullInputExt` → items 16, 17 closures on the analytic Jacobian

Composes `C3FullInputExt.toClosureBundle` with the existing
`analyticJacobian_ofCurve_contMDiff_of_bundle` (item 17) and
`analyticJacobian_ofCurve_injective_of_bundle` (item 16) discharges
that I landed earlier this session.

Headlines:

* `ofCurve_contMDiff` — `ContMDiff` of `B.abelJacobiPoint`.
* `ofCurve_injective` — point-injectivity (under `0 < genus X`).

With these + the chip-7 instance discharges (`compactSpaceHypothesis`,
`chartedSpaceHypothesis`, `lieAddGroupHypothesis`), `C3FullInputExt X`
discharges items 4, 5, 10, 11, 12, 13, 16, 17 simultaneously on the
analytic Jacobian.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology ContDiff
open Module

noncomputable section

namespace JacobianChallenge

namespace C3FullInputExt

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Item 17 on the analytic Jacobian.** `B.base.ajInput.abelJacobiPoint`
is `ContMDiff` (against the canonical chart bundle). -/
theorem ofCurve_contMDiff (B : C3FullInputExt X) :
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
    haveI := (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds
      (PeriodLatticeOfRankTwoG.ofBundle
        (PeriodPairingData.ofSmoothCycle X) B.base.basis
        B.base.discreteness)).toChartedSpace
    ContMDiff (𝓘(ℂ, ℂ))
      (𝓘(ℂ, Fin (JacobianChallenge.genus X) → ℂ)) ω
      (B.base.ajInput.abelJacobiPoint :
        X → AnalyticJacobian (PeriodPairingData.ofSmoothCycle X)
          B.base.basis B.base.discreteness) := by
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
  exact analyticJacobian_ofCurve_contMDiff_of_bundle B.toClosureBundle

/-- **Item 16 on the analytic Jacobian.** `B.base.ajInput.abelJacobiPoint`
is injective under `0 < genus X`. -/
theorem ofCurve_injective (B : C3FullInputExt X) (hpos : 0 < JacobianChallenge.genus X) :
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
    Function.Injective
      (B.base.ajInput.abelJacobiPoint :
        X → AnalyticJacobian (PeriodPairingData.ofSmoothCycle X)
          B.base.basis B.base.discreteness) := by
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
  exact analyticJacobian_ofCurve_injective_of_bundle B.toClosureBundle hpos

end C3FullInputExt

end JacobianChallenge

end
