/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3FullInput
import JacobianChallenge.Manifold.JacobianOfLatticeFromBundle

set_option linter.unusedSectionVars false

/-! # `C3FullInput` → instance discharges on the analytic Jacobian

From a `C3FullInput X` bundle, derive the OPEN.md instance hypotheses
on the resulting `AnalyticJacobian X (ofSmoothCycle X) B.basis
B.discreteness`:

* `JacobianOfLattice.CompactSpaceHypothesis` (item 11 content).
* `JacobianOfLattice.ChartedSpaceHypothesis` (items 5 + 12 content).

These compose `C3FullInput`'s discreteness field with the existing
`PeriodLatticeOfRankTwoG.ofBundle_compactSpace` /
`ofBundle_chartedSpace` discharges, instantiated at
`PeriodPairingData.ofSmoothCycle X`.

The remaining open items (10, 13, 17, 18, 21) similarly cascade once
the corresponding bundle-form discharges are wired
(`PeriodLatticeOfRankTwoG_LieGroupWiring`, `JacobianAnalyticPushforwardPullbackContMDiff`,
etc.).

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology ContDiff
open Module

noncomputable section

namespace JacobianChallenge

namespace C3FullInput

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Item 11 content on the analytic Jacobian.** `JacobianOfLattice`
built from `C3FullInput`'s `(basis, discreteness)` carries
`CompactSpaceHypothesis`. -/
theorem compactSpaceHypothesis (B : C3FullInput X) :
    haveI := periodLatticeImage_discreteTopology_of_bundle B.discreteness
    haveI := periodLatticeImage_isZLattice_of_bundle B.discreteness
    JacobianOfLattice.CompactSpaceHypothesis
      (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle X)
        B.basis B.discreteness) :=
  PeriodLatticeOfRankTwoG.ofBundle_compactSpace
    (PeriodPairingData.ofSmoothCycle X) B.basis B.discreteness

/-- **Items 5 + 12 content on the analytic Jacobian.** -/
noncomputable def chartedSpaceHypothesis (B : C3FullInput X) :
    haveI := periodLatticeImage_discreteTopology_of_bundle B.discreteness
    haveI := periodLatticeImage_isZLattice_of_bundle B.discreteness
    JacobianOfLattice.ChartedSpaceHypothesis
      (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle X)
        B.basis B.discreteness) :=
  PeriodLatticeOfRankTwoG.ofBundle_chartedSpace
    (PeriodPairingData.ofSmoothCycle X) B.basis B.discreteness

end C3FullInput

end JacobianChallenge

end
