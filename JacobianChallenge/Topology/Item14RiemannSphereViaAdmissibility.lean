/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Item14FromHSPBSLBAndAdmissibility
import JacobianChallenge.Manifold.PathPrimitiveAdmissibleRiemannSphere
import JacobianChallenge.Manifold.RiemannSphereSimplePole
import JacobianChallenge.Manifold.StokesBoundariesTopRiemannSphere

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Item 14 on `RiemannSphere` via the BSLB+admissibility route

End-to-end discharge of all 3 inputs to
`genus_eq_zero_iff_homeo_from_hSP_bslb_and_admissibility` on
`RiemannSphere`:

1. `existsSimplePoleGermAtSomePoint_RiemannSphere`
   (`Manifold/RiemannSphereSimplePole.lean`).
2. `basedSmoothLoopsBoundHypothesis_RS_holds`
   (`Manifold/StokesBoundariesTopRiemannSphere.lean`).
3. `pathPrimitiveAdmissibleChartCover_RS`
   (`Manifold/PathPrimitiveAdmissibleRiemannSphere.lean`, this session).

Yields **unconditional item 14 biconditional on `RiemannSphere`** via
the BSLB+admissibility route — a parallel discharge to the existing
in-tree closures.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

/-- **Item 14 biconditional on `RiemannSphere` via the
BSLB+admissibility route, unconditional.**

Plugs in the in-tree discharges:

* `hSP := existsSimplePoleGermAtSomePoint_RiemannSphere`;
* `h_bslb := fun _ => basedSmoothLoopsBoundHypothesis_RS_holds x₀`;
* `h_admit := fun _ i => pathPrimitiveAdmissibleChartCover_RS (b i)`. -/
theorem genus_eq_zero_iff_homeo_RiemannSphere_via_admissibility
    (x₀ : RiemannSphere) {ι : Type*}
    (b : Basis ι ℂ (HolomorphicOneForm RiemannSphere)) :
    JacobianChallenge.genus RiemannSphere = 0 ↔
      Nonempty (RiemannSphere ≃ₜ StandardS2) :=
  genus_eq_zero_iff_homeo_from_hSP_bslb_and_admissibility x₀ b
    MeromorphicFunctionField.existsSimplePoleGermAtSomePoint_RiemannSphere
    (fun _ => RiemannSphere.basedSmoothLoopsBoundHypothesis_RS_holds x₀)
    (fun _ i => RiemannSphere.pathPrimitiveAdmissibleChartCover_RS (b i))

end JacobianChallenge

end
