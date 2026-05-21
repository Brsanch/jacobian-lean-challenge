/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianHodgeChainFromSurfaceClassificationData
import JacobianChallenge.Manifold.RiemannSecondRelationPositivityNamed
import JacobianChallenge.Manifold.RiemannFirstBilinearRelationGenusZero
import JacobianChallenge.Manifold.RiemannSecondRelationPositivityGenusZero
import JacobianChallenge.Manifold.DefaultHolomorphicOneFormBasis

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # `HasJacobianAnalyticStructure RiemannSphere` via the three named atoms

Validates the chip 20 composite at the C3 universality blocker by
combining the three unconditional RS atoms:

* `SurfaceClassificationData RiemannSphere` — chip 1
  (`surfaceClassificationData_RiemannSphere`).
* `RiemannFirstBilinearRelation` unconditional on RS — chip 11.
* `RiemannSecondRelationPositivity` unconditional on RS — chip 19.

Direct route through chip 4's `ofSurfaceClassificationData` + chip 18's
`completeHodgeRiemannHypothesis_of_RiemannFirst_RiemannSecond`,
producing `HasJacobianAnalyticStructure RiemannSphere`.

## What this file ships

* `hasJacobianAnalyticStructure_RiemannSphere_via_three_atoms` —
  smoke test.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

namespace RiemannSphere

/-- **Smoke test: `HasJacobianAnalyticStructure RiemannSphere` from
the three named atoms.**

The three RS atoms compose through chip 4 + chip 18 to yield the
unconditional HJAS on RS. Independent validation that the chip 20
composite is sound and the named atoms (chips 1, 11, 19) are the
correct minimal inputs. -/
theorem hasJacobianAnalyticStructure_RiemannSphere_via_three_atoms :
    HasJacobianAnalyticStructure RiemannSphere := by
  let scd : SurfaceClassificationData RiemannSphere :=
    surfaceClassificationData_RiemannSphere (Classical.arbitrary _)
  let basis_ω : Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
      (HolomorphicOneForm RiemannSphere) :=
    defaultHolomorphicOneFormBasis RiemannSphere
  -- The two named-atom inputs from chips 11 and 19.
  have h_first :
      @RiemannFirstBilinearRelation RiemannSphere _ _ _
        (PeriodPairingData.ofSmoothCycle RiemannSphere)
        scd.symplecticBasis.cycleGens
        (standardSymplectic (JacobianChallenge.genus RiemannSphere)) :=
    riemannFirstBilinearRelation_RiemannSphere _ _
  have h_second :
      RiemannSecondRelationPositivity
        (PeriodPairingData.ofSmoothCycle RiemannSphere) basis_ω
        scd.symplecticBasis.cycleGens :=
    riemannSecondRelationPositivity_RiemannSphere _ _ _
  -- Compose chip 4 + chip 18 to get HJHC, then inferInstance gives HJAS.
  haveI : HasJacobianHodgeChain RiemannSphere :=
    HasJacobianHodgeChain.ofSurfaceClassificationData scd basis_ω
      (completeHodgeRiemannHypothesis_of_RiemannFirst_RiemannSecond
        (PeriodPairingData.ofSmoothCycle RiemannSphere) basis_ω
        scd.symplecticBasis.cycleGens h_first h_second)
  exact inferInstance

end RiemannSphere

end JacobianChallenge

end
