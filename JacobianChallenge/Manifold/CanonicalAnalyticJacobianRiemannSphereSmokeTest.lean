/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CanonicalOfCurveContMDiffSubsingleton
import JacobianChallenge.Manifold.Pic0RiemannSphereSubsingleton
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option linter.unusedSectionVars false

/-! # End-to-end RS smoke test for the canonical analytic Jacobian chain

This file is a *smoke test* on the Riemann sphere of the canonical
analytic Jacobian chain built across
`CanonicalAnalyticJacobianFromClass`, `DefaultHolomorphicOneFormBasis`,
`HasJacobianAnalyticStructure`, `CanonicalOfCurve`,
`HasJacobianAnalyticStructureSubsingleton`,
`CanonicalAnalyticJacobianSubsingleton`,
`CanonicalOfCurveContMDiffSubsingleton`.

On `RiemannSphere`:

* `[HasJacobianAnalyticStructure RiemannSphere]` is unconditional
  (from the per-basis class instance + existential introduction).
* `CanonicalAnalyticJacobianAnonymous RiemannSphere` has all seven
  structural instances (AddCommGroup, TopologicalSpace, T2Space,
  CompactSpace, ChartedSpace, IsManifold, LieAddGroup).
* `canonicalOfCurve P Q : CanonicalAnalyticJacobianAnonymous RiemannSphere`
  is well-defined for any `P, Q`.
* `canonicalOfCurve P P = 0` (basepoint self-vanishing).
* `canonicalOfCurve P` is `ContMDiff` (via the genus-0 smoothness
  discharge, since `Subsingleton (HolomorphicOneForm RiemannSphere)`).

This file confirms the entire chain compiles end-to-end on RS,
serving as a regression check on the canonical-analytic-Jacobian arc.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-- **End-to-end RS smoke test.** Bundles the seven structural
instances + `canonicalOfCurve`'s smoothness on `RiemannSphere`. -/
example (P : RiemannSphere) :
    ContMDiff (𝓘(ℂ, ℂ))
      (modelWithCornersSelf ℂ (Fin (JacobianChallenge.genus RiemannSphere) → ℂ)) ω
      (canonicalOfCurve P :
        RiemannSphere → CanonicalAnalyticJacobianAnonymous RiemannSphere) :=
  canonicalOfCurve_contMDiff_of_subsingleton_omega P

/-- **End-to-end RS smoke test (self-vanishing).** -/
example (P : RiemannSphere) :
    canonicalOfCurve P P
      = (0 : CanonicalAnalyticJacobianAnonymous RiemannSphere) :=
  canonicalOfCurve_self P

end RiemannSphere

end JacobianChallenge

end
