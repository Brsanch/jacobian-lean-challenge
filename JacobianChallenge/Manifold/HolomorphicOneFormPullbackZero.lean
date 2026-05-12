/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackLinearMap

set_option diagnostics.threshold 100

/-! # Pullback collapses to the zero linear map in the subsingleton codomain case

When `HolomorphicOneForm Y` is subsingleton, every form on `Y` is `0`,
so the pointwise pullback is the zero function, and the resulting
`HolomorphicOneForm X` realisation must be the zero form on `X`
(distinct from the zero linear map — see below).

This file makes the structural collapse explicit:

* `pullbackOfAll_eq_zero_of_subsingleton_codomain` — the pullback
  function maps every form to `(0 : HolomorphicOneForm X)`.
* `pullbackLinearMap_eq_zero_of_subsingleton_codomain` — the pullback
  linear map is the zero linear map.
* `pullbackLinearMap_RiemannSphere_eq_zero` — the unconditional
  Riemann-sphere specialisation: every form on RS pulls back to `0` on
  `X`, no matter the biholomorphism.

This is mathematically the statement that there are no non-trivial
1-forms to pull back from the Riemann sphere, so the pullback operator
is necessarily trivial. Useful as a sanity-check identity and as a
building block for downstream injectivity / image-theoretic arguments.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-! ## Function-level collapse -/

/-- The pullback of any form on a subsingleton-codomain `Y` is the zero
form on `X`. -/
theorem HolomorphicEquiv.pullbackOfAll_eq_zero_of_subsingleton_codomain
    (e : HolomorphicEquiv X Y)
    [Subsingleton (HolomorphicOneForm Y)]
    (hAll : IsHolomorphicOneFormPullback_for_all e)
    (α : HolomorphicOneForm Y) :
    e.pullbackOfAll hAll α = (0 : HolomorphicOneForm X) := by
  refine ContMDiffSection.coe_injective ?_
  funext x
  have h_eval : HolomorphicOneForm.eval (e.pullbackOfAll hAll α) x
      = e.pullbackPointwise α x :=
    e.pullbackOfAll_eval hAll α x
  have h_zero : e.pullbackPointwise α x = 0 := by
    have h_fun : e.pullbackPointwise α
        = (fun _ : X => (0 : CotangentSpace (𝓘(ℂ, ℂ)) _)) :=
      HolomorphicEquiv.pullbackPointwise_eq_zero_of_subsingleton e α
    exact congrFun h_fun x
  -- Show LHS-eval-at-x = (0 : HolomorphicOneForm X)-eval-at-x.
  change HolomorphicOneForm.eval (e.pullbackOfAll hAll α) x
      = HolomorphicOneForm.eval (0 : HolomorphicOneForm X) x
  rw [h_eval, h_zero, HolomorphicOneForm.eval_zero]
  rfl

/-! ## LinearMap-level collapse -/

/-- The pullback linear map is the zero linear map when the codomain
`Y` has subsingleton 1-form space. -/
theorem HolomorphicEquiv.pullbackLinearMap_eq_zero_of_subsingleton_codomain
    (e : HolomorphicEquiv X Y)
    [Subsingleton (HolomorphicOneForm Y)]
    (hAll : IsHolomorphicOneFormPullback_for_all e) :
    e.pullbackLinearMap hAll = 0 := by
  ext α
  show e.pullbackOfAll hAll α = (0 : HolomorphicOneForm X)
  exact e.pullbackOfAll_eq_zero_of_subsingleton_codomain hAll α

/-! ## Riemann-sphere specialisation (unconditional) -/

/-- **Unconditional zero collapse for `Y = RiemannSphere`.** The
pullback linear map from `HolomorphicOneForm RiemannSphere` is the
zero linear map for every biholomorphism `e : X ≃ RiemannSphere`. -/
theorem HolomorphicEquiv.pullbackLinearMap_RiemannSphere_eq_zero
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere) :
    e.pullbackLinearMap_RiemannSphere = 0 :=
  e.pullbackLinearMap_eq_zero_of_subsingleton_codomain
    (isHolomorphicOneFormPullback_for_all_RiemannSphere e)

end JacobianChallenge

end
