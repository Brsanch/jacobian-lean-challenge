/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackLinearMap
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackRefl
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackZero
import JacobianChallenge.Manifold.HolomorphicEquivRiemannSphere

set_option diagnostics.threshold 100

/-! # `HolomorphicOneForm.pullback` API surface

Consolidated user-facing API for the holomorphic-1-form pullback
infrastructure built across zz289–zz293:

* **zz289** — Pointwise pullback (function-level) + ℂ-linearity.
* **zz290** — Smoothness obligation as a Prop + trivial discharge
  when the codomain has subsingleton 1-form space.
* **zz291** — Under the smoothness hypothesis, the ℂ-linear map.
* **zz292** — In the trivial case, the linear map is the zero linear map.
* **zz293** — Pullback along the identity biholomorphism is the identity.

This file:

* Re-exports the core API under uniform `HolomorphicOneForm.pullback`
  names.
* Provides the headline **`pullback_RiemannSphere`** unconditional
  linear map: for any biholomorphism `X ≃ RS`, the pullback
  `HolomorphicOneForm RS →ₗ[ℂ] HolomorphicOneForm X` exists
  unconditionally, and equals the zero linear map.
* Provides `pullback_RiemannSphere_apply_eq_zero` —
  the unique form `α : HolomorphicOneForm RS` (which is `0`) pulls
  back to `0`.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

namespace HolomorphicOneForm

variable {X : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]

/-! ## Headline `pullback` API for biholomorphisms into the Riemann sphere -/

/-- **Pullback of holomorphic 1-forms along a biholomorphism into the
Riemann sphere.** For any `e : HolomorphicEquiv X RiemannSphere`, the
pullback is a `ℂ`-linear map from `HolomorphicOneForm RS` to
`HolomorphicOneForm X`. Equivalently the zero linear map (since
`HolomorphicOneForm RS` is subsingleton). -/
noncomputable def pullbackOf_RiemannSphere
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere) :
    HolomorphicOneForm JacobianChallenge.RiemannSphere
      →ₗ[ℂ] HolomorphicOneForm X :=
  HolomorphicEquiv.pullbackLinearMap_RiemannSphere e

/-- The pullback `HolomorphicOneForm RS →ₗ[ℂ] HolomorphicOneForm X`
along any biholomorphism into the Riemann sphere is the zero linear
map. -/
theorem pullbackOf_RiemannSphere_eq_zero
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere) :
    pullbackOf_RiemannSphere e = 0 :=
  HolomorphicEquiv.pullbackLinearMap_RiemannSphere_eq_zero e

/-- Pointwise: the pullback of any form (necessarily `0`) along a
biholomorphism into the Riemann sphere is `(0 : HolomorphicOneForm X)`. -/
theorem pullbackOf_RiemannSphere_apply_eq_zero
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere)
    (α : HolomorphicOneForm JacobianChallenge.RiemannSphere) :
    pullbackOf_RiemannSphere e α = (0 : HolomorphicOneForm X) := by
  rw [pullbackOf_RiemannSphere_eq_zero]; rfl

/-! ## Pullback along the identity biholomorphism -/

/-- For the identity biholomorphism, the function-level pullback applied
to `α` equals the underlying section of `α`. -/
theorem pullback_refl_eval (α : HolomorphicOneForm X) (x : X) :
    HolomorphicEquiv.pullbackPointwise
        (HolomorphicEquiv.refl : HolomorphicEquiv X X) α x
      = HolomorphicOneForm.eval α x :=
  HolomorphicEquiv.pullbackPointwise_refl α x

end HolomorphicOneForm

/-! ## Summary

Repo-wide, after zz289–zz293 + this consolidation file, the pullback
of holomorphic 1-forms is honestly **built** in the following cases:

* **Trivial case (codomain has subsingleton 1-form space):** the
  pullback `LinearMap` exists unconditionally and equals zero.
* **Identity:** pullback along `HolomorphicEquiv.refl` acts as the
  identity at the pointwise function level.

The general analytic case — building the smooth pullback section for
arbitrary `e : HolomorphicEquiv X Y` and using it to deduce
`Subsingleton (HolomorphicOneForm X)` from `Subsingleton
(HolomorphicOneForm Y)` — requires the cotangent-bundle transition
machinery in `Manifold/CotangentPullbackBridge.lean` (already in the
repo) plus a follow-up chip composing it into the
`HolomorphicEquiv.pullbackPointwise`-as-section statement. That chip
remains the substantive analytic obligation for full pullback
functoriality.
-/

end JacobianChallenge

end
