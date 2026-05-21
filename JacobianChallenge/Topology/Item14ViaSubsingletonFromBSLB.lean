/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SubsingletonFromBSLBAndPathPrimitive
import JacobianChallenge.Topology.HTopFromSubsingleton

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Item 14 via Subsingleton(ω) from BSLB + path-primitive analytic data

A clean **three-named-hypothesis** route to item 14 that produces
`Subsingleton (HolomorphicOneForm X)` upstream of the existing
single-input `genus_eq_zero_iff_homeo_from_existsSimplePoleGerm_and_subsingleton`
(in `Topology/HTopFromSubsingleton.lean`).

The route:

* `subsingleton_of_BSLB_and_pathPrimitive` (from
  `Manifold/SubsingletonFromBSLBAndPathPrimitive.lean`) gives
  `Subsingleton (HolomorphicOneForm X)` from three analytic inputs:
  * BSLB hypothesis at a basepoint;
  * path-primitive smoothness against the auto-discharged
    `smoothPathConnected_of_preconnected` witness;
  * path-primitive FTC.

* `genus_eq_zero_iff_homeo_from_existsSimplePoleGerm_and_subsingleton`
  then closes item 14 from a single additional input: `hSP`.

Together: **item 14 from `hSP` + BSLB + smoothness + FTC**, going
through the Subsingleton step (instead of the longer Item14Final
chain). This is the parallel composition to
`genus_eq_zero_iff_homeo_from_hSP_BSLB_pathPrimitive` in
`Topology/Item14FromHSPBSLBAndPathPrimitive.lean`, but routes through
the cleaner Subsingleton single-input form rather than through
`S2ImpliesGenus0`.

Both compositions land the same biconditional. This file exists to
expose the alternate route, which is structurally simpler (3 steps via
Subsingleton instead of 4 via S2ImpliesGenus0+FiniteDim).

Note: the BSLB-side analytic hypotheses (`h_bslb`, `h_smooth`,
`h_ftc`) are NOT actually needed once `[Subsingleton ω]` is in scope —
the existing single-input chip closes item 14 from `hSP` alone under
that hypothesis. This chip is for the case where `Subsingleton` itself
needs to be derived from the analytic inputs.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Item 14 biconditional via the Subsingleton(ω) route, from BSLB +
path-primitive analytic data + hSP.**

Inputs:
* `hSP` — `ExistsSimplePoleGermAtSomePoint X` (forward leg, RR-class).
* `h_bslb` — BSLB at basepoint `x₀` (reverse leg, smooth Hurewicz).
* `h_smooth` — path-primitive smoothness.
* `h_ftc` — path-primitive FTC.

Discharges:
1. `subsingleton_of_BSLB_and_pathPrimitive` produces
   `Subsingleton (HolomorphicOneForm X)` from `h_bslb` + `h_smooth` +
   `h_ftc`.
2. `genus_eq_zero_iff_homeo_from_existsSimplePoleGerm_and_subsingleton`
   then closes item 14 from `hSP` under the Subsingleton instance. -/
theorem genus_eq_zero_iff_homeo_via_subsingleton_from_BSLB_pathPrimitive
    (x₀ : X)
    (hSP : MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X)
    (h_bslb : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀)
    (h_smooth : PathPrimitiveSmoothness
      (smoothPathConnected_of_preconnected (X := X)) x₀)
    (h_ftc : PathPrimitiveFTC
      (smoothPathConnected_of_preconnected (X := X)) x₀) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) := by
  haveI : Subsingleton (HolomorphicOneForm X) :=
    subsingleton_of_BSLB_and_pathPrimitive x₀ h_bslb h_smooth h_ftc
  exact MeromorphicFunctionField.genus_eq_zero_iff_homeo_from_existsSimplePoleGerm_and_subsingleton
    X hSP

end JacobianChallenge

end
