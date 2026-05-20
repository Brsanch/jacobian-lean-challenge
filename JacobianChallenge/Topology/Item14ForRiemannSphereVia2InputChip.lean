/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Item14FromSubsingletonHolomorphicOneForm
import JacobianChallenge.Manifold.RiemannSphereSimplePole
import JacobianChallenge.Manifold.StokesBoundariesTopRiemannSphere

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # End-to-end validation: item 14 on `RiemannSphere` via the
2-input chip + subsingleton ω

Plugs the unconditional RS discharges:

* `existsSimplePoleGermAtSomePoint_RiemannSphere` (forward leg,
  `Manifold/RiemannSphereSimplePole.lean`);
* `basedSmoothLoopsBoundHypothesis_RS_holds p₀` (reverse leg,
  `Manifold/StokesBoundariesTopRiemannSphere.lean`);

into `genus_eq_zero_iff_homeo_from_2_minimal_inputs_under_subsingleton`,
yielding a fully unconditional discharge of item 14's biconditional
on `RiemannSphere`. Parallel to the existing routes in
`Item14ForRiemannSphere.lean`,
`Item14FromUniformization.lean`, and
`Item14FromSingleUniformization.lean` — confirms the 2-input chip
composes correctly.

`Subsingleton (HolomorphicOneForm RiemannSphere)` is in tree
unconditionally as an instance (`Manifold/RiemannSphereChartSCoeffOverlap.lean`),
so the structural subsingleton hypothesis is automatic.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

/-- **Item 14 biconditional on `RiemannSphere`, unconditional via the
2-input chip + subsingleton ω.**

Plugs `existsSimplePoleGermAtSomePoint_RiemannSphere` (forward) +
`basedSmoothLoopsBoundHypothesis_RS_holds` (reverse, base point
chosen via `Classical.arbitrary`) into
`genus_eq_zero_iff_homeo_from_2_minimal_inputs_under_subsingleton`. -/
theorem genus_eq_zero_iff_homeo_RiemannSphere_via_2_input_chip :
    JacobianChallenge.genus RiemannSphere = 0
      ↔ Nonempty (RiemannSphere ≃ₜ StandardS2) :=
  let x₀ : RiemannSphere := Classical.arbitrary _
  genus_eq_zero_iff_homeo_from_2_minimal_inputs_under_subsingleton
    (X := RiemannSphere) x₀
    MeromorphicFunctionField.existsSimplePoleGermAtSomePoint_RiemannSphere
    (fun _ => JacobianChallenge.RiemannSphere.basedSmoothLoopsBoundHypothesis_RS_holds x₀)

end JacobianChallenge

end
