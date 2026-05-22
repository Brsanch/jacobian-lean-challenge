/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianHodgeChainGenusZeroFromScalars
import JacobianChallenge.Manifold.SurfaceClassificationDataGenusZero
import JacobianChallenge.Manifold.DefaultHolomorphicOneFormBasis

set_option linter.unusedSectionVars false

/-! # RS validation of the HJHC g²-scalars route at genus 0

Regression-guard smoke test that the new
`HasJacobianHodgeChain.of_genus_zero_scd_scalars` discharge fires on
`RiemannSphere`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

namespace RiemannSphere

/-- **RS smoke test for the HJHC g²-scalars route.** -/
theorem HasJacobianHodgeChain_RiemannSphere_via_scalars_route :
    HasJacobianHodgeChain RiemannSphere :=
  HasJacobianHodgeChain.of_genus_zero_scd_scalars
    (X := RiemannSphere)
    JacobianChallenge.RiemannSphere.genus_RiemannSphere_eq_zero
    (surfaceClassificationData_RiemannSphere (Classical.arbitrary _))
    (defaultHolomorphicOneFormBasis RiemannSphere)

end RiemannSphere

end JacobianChallenge

end
