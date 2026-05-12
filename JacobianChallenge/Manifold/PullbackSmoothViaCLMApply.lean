/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicEquiv
import JacobianChallenge.Manifold.HolomorphicEquivSubsingletonTransfer
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackSmoothness
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackPointwise
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap
import JacobianChallenge.Manifold.Cotangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option diagnostics.threshold 100
set_option maxHeartbeats 400000

/-! # Plan-of-record for the cotangent pullback section's smoothness

The pullback section's smoothness for a `HolomorphicEquiv` is, in
principle, an application of mathlib's
`ContMDiffAt.clm_apply_of_inCoordinates` (from
`Mathlib.Geometry.Manifold.VectorBundle.Hom`) with:

* `b₁ = e.toEquiv : X → Y` (base map for source-side bundle).
* `b₂ = id : X → X` (base map for target-side bundle).
* `v x = α.eval (e x) : T_{e x} Y →L[ℂ] ℂ` (the section evaluated at e x).
* `ϕ x η = η ∘L (mfderiv e x) : T_x X →L[ℂ] ℂ` (precomposition with mfderiv).

The hypotheses of `clm_apply_of_inCoordinates`:

1. `hv : ContMDiffAt _ _ ω (fun x ↦ (v x : TotalSpace F E₁)) x₀`
   — follows from `α.contMDiff` + `e.contMDiff`.

2. `hb₂ : ContMDiffAt _ _ ω id x₀` — trivial.

3. `hϕ : ContMDiffAt _ _ ω (fun x ↦ inCoordinates ... (ϕ x)) x₀` —
   the substantive analytic content: smoothness of `mfderiv e` in
   coordinates, via `ContMDiffAt.mfderiv_const`.

The conclusion gives `ContMDiffAt _ _ ω (fun x ↦ (ϕ x (v x) :
TotalSpace F E₂)) x₀` — which is exactly the section smoothness of
the pullback.

## Why this file is structural and not fully proven

Translating the plan into Lean requires:

* Matching the cotangent bundle's `FiberBundle` and `VectorBundle`
  instances against the generic `clm_apply_of_inCoordinates` slots —
  involves explicit normed-space instances on `TangentSpace 𝓘(ℂ) _`
  that are not auto-resolved by typeclass search at this mathlib pin.

* The `inCoordinates` of `ϕ` for cotangent bundles requires bridging
  through the tangent-bundle in-coordinates form (since `mfderiv`'s
  smoothness lemma `ContMDiffAt.mfderiv_const` is stated in the
  *tangent* in-coordinates form, not the cotangent one).

These are real but tractable mathlib-PR-grade pieces. The plan-of-record
structure above is correct and is what a future chip would expand.

This file ships the intermediate identities `pullbackPointwise` is
expressible as a CLM-apply, plus the docstring plan. No `sorry`, no
`axiom`.
-/

open scoped Manifold ContDiff
open ContinuousLinearMap

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-- The pointwise pullback expressed as a CLM composition. -/
theorem HolomorphicEquiv.pullbackPointwise_eq_clm_comp
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm Y) (x : X) :
    e.pullbackPointwise α x
      = ContinuousLinearMap.comp (HolomorphicOneForm.eval α (e x))
          (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
            ((e.toEquiv : X → Y) : X → Y) x) := rfl

end JacobianChallenge

end
