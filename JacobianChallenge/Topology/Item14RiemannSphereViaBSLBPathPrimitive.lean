/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Item14FromHSPBSLBAndPathPrimitive
import JacobianChallenge.Manifold.RiemannSphereSimplePole
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap
import JacobianChallenge.Manifold.StokesBoundariesTopRiemannSphere

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Smoke test: item 14 biconditional on `RiemannSphere` via BSLB + path-primitive

End-to-end validation that
`genus_eq_zero_iff_homeo_from_hSP_BSLB_under_subsingleton` from
`Topology/Item14FromHSPBSLBAndPathPrimitive.lean` composes unconditionally
on the Riemann sphere. The required inputs are:

* `hSP := existsSimplePoleGermAtSomePoint_RiemannSphere` (forward leg,
  unconditional on RS via `Manifold/RiemannSphereSimplePole.lean`);
* `h_bslb := basedSmoothLoopsBoundHypothesis_RS_holds` (reverse leg,
  unconditional on RS via the chart-N pullback + tubular bump arc);
* `Subsingleton (HolomorphicOneForm RiemannSphere)` (unconditional via
  `Manifold/RiemannSphereChartSCoeffOverlap.lean`) makes the
  per-1-form smoothness + FTC vacuous.

This validates that the 3-input BSLB+path-primitive route closes
cleanly on the canonical example.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open OnePoint

namespace JacobianChallenge

namespace RiemannSphere

/-- **Item 14 biconditional on `RiemannSphere` via the BSLB + path-primitive
3-input route.** Validates that
`genus_eq_zero_iff_homeo_from_hSP_BSLB_under_subsingleton` composes
unconditionally on RS, with the per-1-form smoothness/FTC hypotheses
auto-discharged via `Subsingleton (HolomorphicOneForm RiemannSphere)`. -/
theorem genus_eq_zero_iff_homeo_RiemannSphere_via_BSLB_pathPrimitive
    (x₀ : RiemannSphere) :
    JacobianChallenge.genus JacobianChallenge.RiemannSphere = 0 ↔
      Nonempty (JacobianChallenge.RiemannSphere ≃ₜ StandardS2) :=
  genus_eq_zero_iff_homeo_from_hSP_BSLB_under_subsingleton x₀
    MeromorphicFunctionField.existsSimplePoleGermAtSomePoint_RiemannSphere
    (fun _ => RiemannSphere.basedSmoothLoopsBoundHypothesis_RS_holds x₀)

end RiemannSphere

end JacobianChallenge

end
