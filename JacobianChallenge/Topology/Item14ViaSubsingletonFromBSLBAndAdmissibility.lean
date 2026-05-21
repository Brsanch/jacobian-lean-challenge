/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SubsingletonFromBSLBAndAdmissibility
import JacobianChallenge.Topology.HTopFromSubsingleton

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Item 14 via Subsingleton(ω) from BSLB + universal admissibility

A clean **three-named-hypothesis** route to item 14 that uses the
universal `PathPrimitiveAdmissibleChartCover om` predicate (per `om`)
to discharge the per-form path-primitive analytic content, rather than
the per-basis `h_smooth_b` + `h_ftc_b` or universal
`PathPrimitiveSmoothness` + `PathPrimitiveFTC` shapes.

The chain:

* `subsingleton_of_BSLB_and_universalAdmissibility` (from
  `Manifold/SubsingletonFromBSLBAndAdmissibility.lean`) gives
  `Subsingleton (HolomorphicOneForm X)` from BSLB + universal
  admissibility.
* `genus_eq_zero_iff_homeo_from_existsSimplePoleGerm_and_subsingleton`
  (in `Topology/HTopFromSubsingleton.lean`) then closes item 14 from
  a single additional input: `hSP`.

Together: **item 14 from `hSP` + BSLB + universal admissibility**.

This is a parallel composition to:

* `genus_eq_zero_iff_homeo_from_hSP_BSLB_pathPrimitive` (routes through
  `S2ImpliesGenus0` + `FiniteDim`);
* `genus_eq_zero_iff_homeo_via_subsingleton_from_BSLB_pathPrimitive`
  (routes through Subsingleton from per-form `PathPrimitiveSmoothness`
  + `PathPrimitiveFTC`);
* `genus_eq_zero_iff_homeo_from_hSP_bslb_and_admissibility` (routes
  through `S2ImpliesGenus0` with per-basis admissibility).

This file's chip uses the universal `∀ om, PathPrimitiveAdmissibleChartCover
om` shape, suitable when admissibility is supplied uniformly (e.g. via
a typeclass instance over `HasAdmissibleChartCover X`).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Item 14 from `hSP` + BSLB + universal admissibility,** via the
Subsingleton(ω) single-input form. -/
theorem genus_eq_zero_iff_homeo_via_subsingleton_from_BSLB_and_universalAdmissibility
    (x₀ : X)
    (hSP : MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X)
    (h_bslb : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀)
    (h_admit : ∀ om : HolomorphicOneForm X,
      PathPrimitiveAdmissibleChartCover om) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) := by
  haveI : Subsingleton (HolomorphicOneForm X) :=
    subsingleton_of_BSLB_and_universalAdmissibility x₀ h_bslb h_admit
  exact MeromorphicFunctionField.genus_eq_zero_iff_homeo_from_existsSimplePoleGerm_and_subsingleton
    X hSP

end JacobianChallenge

end
