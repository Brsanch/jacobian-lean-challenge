/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Item14From2InputsUnderConvexChartAt
import JacobianChallenge.RiemannSphere.HasConvexChartAtTargetRiemannSphere
import JacobianChallenge.Manifold.RiemannSphereSimplePole
import JacobianChallenge.Manifold.StokesBoundariesTopRiemannSphere

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # End-to-end validation: item 14 on `RiemannSphere` via the
chip-D-based 2-input lemma

Plugs the existing unconditional RS discharges:

* `existsSimplePoleGermAtSomePoint_RiemannSphere` — forward leg
  (`Manifold/RiemannSphereSimplePole.lean`);
* `basedSmoothLoopsBoundHypothesis_RS_holds p₀` — reverse leg
  (`Manifold/StokesBoundariesTopRiemannSphere.lean`);

into `genus_eq_zero_iff_homeo_from_2_classical_inputs_under_convexChartAt`
(the chip-D-based 2-input lemma) together with the
`HasConvexChartAtTarget RiemannSphere` instance, yielding a fully
unconditional discharge of item 14's biconditional on `RiemannSphere`
via the **new** chart-cover-lift route.

This is a **parallel** route to the older
`Item14ForRiemannSphereVia2InputChip.lean` (which uses the Subsingleton-ω
discharge of admissibility) — both reach the same conclusion via
disjoint analytic machinery, validating chip-D end-to-end.

`Subsingleton (HolomorphicOneForm RiemannSphere)` is in tree
unconditionally, so `Basis.empty` on `Fin 0` provides the basis.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

/-- **Item 14 biconditional on `RiemannSphere`, unconditional via the
chip-D-based 2-input lemma + `HasConvexChartAtTarget` instance.** -/
theorem genus_eq_zero_iff_homeo_RiemannSphere_via_convexChartAt :
    JacobianChallenge.genus RiemannSphere = 0
      ↔ Nonempty (RiemannSphere ≃ₜ StandardS2) := by
  let x₀ : RiemannSphere := Classical.arbitrary _
  -- Basis on the trivial (Subsingleton) space HolomorphicOneForm RS.
  let b : Basis (Fin 0) ℂ (HolomorphicOneForm RiemannSphere) := Basis.empty _
  exact genus_eq_zero_iff_homeo_from_2_classical_inputs_under_convexChartAt
    x₀ b
    MeromorphicFunctionField.existsSimplePoleGermAtSomePoint_RiemannSphere
    (fun _ => RiemannSphere.basedSmoothLoopsBoundHypothesis_RS_holds x₀)

end JacobianChallenge

end
