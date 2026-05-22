/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianAnalyticStructureGenusZeroFromScalars
import JacobianChallenge.Manifold.SurfaceClassificationDataGenusZero
import JacobianChallenge.Manifold.DefaultHolomorphicOneFormBasis

set_option linter.unusedSectionVars false

/-! # RS validation of the g²-scalar route at genus 0

Smoke test that the new genus-0-from-g²-scalars discharge fires on
`RiemannSphere` (where `genus RiemannSphere = 0`).

## What ships

* `HasJacobianAnalyticStructure_RiemannSphere_via_scalars_route` —
  unconditional `HasJacobianAnalyticStructure RiemannSphere` via the
  g²-scalars route + the genus-0 SCD witness.

This is a regression guard: if the g²-scalars route ever breaks on
empty index, this example will fail to compile.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

namespace RiemannSphere

/-- **RS smoke test for the g²-scalars route.** -/
theorem HasJacobianAnalyticStructure_RiemannSphere_via_scalars_route :
    HasJacobianAnalyticStructure RiemannSphere :=
  HasJacobianAnalyticStructure.of_genus_zero_scd
    (X := RiemannSphere)
    JacobianChallenge.RiemannSphere.genus_RiemannSphere_eq_zero
    (surfaceClassificationData_RiemannSphere (Classical.arbitrary _))
    (defaultHolomorphicOneFormBasis RiemannSphere)

end RiemannSphere

end JacobianChallenge

end
