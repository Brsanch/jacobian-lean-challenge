/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackSmoothness
import JacobianChallenge.Manifold.HolomorphicOneFormLinear

set_option diagnostics.threshold 100

/-! # Holomorphic-1-form pullback as a `LinearMap` (under smoothness)

This file builds the `ℂ`-linear map

  `HolomorphicEquiv.pullback e : HolomorphicOneForm Y →ₗ[ℂ] HolomorphicOneForm X`

under the universal smoothness hypothesis
`IsHolomorphicOneFormPullback_for_all e`. The construction uses the
`Classical.choose` of the existence witness from zz290's
`IsHolomorphicOneFormPullback`.

Linearity in `α` is inherited from zz289's pointwise linearity by the
following bookkeeping: the section produced by `Classical.choose` agrees
with the pointwise pullback in evaluation; combined with
`HolomorphicOneForm.eval` linearity lemmas, the section-level operations
match.

## What this file delivers

* `HolomorphicEquiv.pullbackHolomorphicOneForm e α (hα : Is...) :
  HolomorphicOneForm X` — packaging from the existence witness.
* `HolomorphicEquiv.pullbackLinearMap e (hAll : IsAll...) :
  HolomorphicOneForm Y →ₗ[ℂ] HolomorphicOneForm X`.

## Unconditional specialisation

When the codomain is `Y = RiemannSphere`, zz290 supplies the universal
smoothness obligation unconditionally (via zz274's subsingleton), so the
pullback linear map exists unconditionally for any biholomorphism
`X ≃ RiemannSphere`.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-! ## Pullback as a single `HolomorphicOneForm X` -/

/-- **Pullback section.** Given the existence-of-section hypothesis for
a specific `α`, produce the realising `HolomorphicOneForm X`. -/
def HolomorphicEquiv.pullbackHolomorphicOneForm
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm Y)
    (hα : IsHolomorphicOneFormPullback e α) :
    HolomorphicOneForm X :=
  Classical.choose hα

/-- The chosen pullback section evaluates to the pointwise pullback. -/
theorem HolomorphicEquiv.pullbackHolomorphicOneForm_eval
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm Y)
    (hα : IsHolomorphicOneFormPullback e α) (x : X) :
    HolomorphicOneForm.eval (e.pullbackHolomorphicOneForm α hα) x
      = e.pullbackPointwise α x :=
  Classical.choose_spec hα x

/-! ## Pullback as a `LinearMap` (under universal smoothness)

We build the linear map by routing through the choice function. The
`map_add'` and `map_smul'` proofs use injectivity of `eval` (via
`HolomorphicOneForm.ext` from extensionality of `ContMDiffSection`)
combined with zz289's pointwise linearity. -/

/-- **The pullback as a function** `HolomorphicOneForm Y →
HolomorphicOneForm X`, packaged from the universal smoothness
hypothesis. -/
def HolomorphicEquiv.pullbackOfAll
    (e : HolomorphicEquiv X Y)
    (hAll : IsHolomorphicOneFormPullback_for_all e) :
    HolomorphicOneForm Y → HolomorphicOneForm X :=
  fun α => e.pullbackHolomorphicOneForm α (hAll α)

/-- The pullback function evaluates to the pointwise pullback. -/
theorem HolomorphicEquiv.pullbackOfAll_eval
    (e : HolomorphicEquiv X Y)
    (hAll : IsHolomorphicOneFormPullback_for_all e)
    (α : HolomorphicOneForm Y) (x : X) :
    HolomorphicOneForm.eval (e.pullbackOfAll hAll α) x
      = e.pullbackPointwise α x :=
  e.pullbackHolomorphicOneForm_eval α (hAll α) x

/-- **Pullback as a `ℂ`-linear map.** -/
def HolomorphicEquiv.pullbackLinearMap
    (e : HolomorphicEquiv X Y)
    (hAll : IsHolomorphicOneFormPullback_for_all e) :
    HolomorphicOneForm Y →ₗ[ℂ] HolomorphicOneForm X where
  toFun α := e.pullbackOfAll hAll α
  map_add' α β := by
    -- Extensionality: both sides agree on `eval _ x` for all `x`.
    refine ContMDiffSection.coe_injective ?_
    funext x
    have h_sum : HolomorphicOneForm.eval (e.pullbackOfAll hAll (α + β)) x
        = e.pullbackPointwise (α + β) x :=
      e.pullbackOfAll_eval hAll (α + β) x
    have h_α : HolomorphicOneForm.eval (e.pullbackOfAll hAll α) x
        = e.pullbackPointwise α x :=
      e.pullbackOfAll_eval hAll α x
    have h_β : HolomorphicOneForm.eval (e.pullbackOfAll hAll β) x
        = e.pullbackPointwise β x :=
      e.pullbackOfAll_eval hAll β x
    have h_add :
        HolomorphicOneForm.eval (e.pullbackOfAll hAll α + e.pullbackOfAll hAll β) x
          = HolomorphicOneForm.eval (e.pullbackOfAll hAll α) x
            + HolomorphicOneForm.eval (e.pullbackOfAll hAll β) x :=
      HolomorphicOneForm.eval_add _ _ _
    -- Show eval-LHS at x = eval-RHS at x.
    -- LHS eval = pullbackPointwise (α + β) x = pullbackPointwise α x + pullbackPointwise β x
    -- RHS eval = pullbackPointwise α x + pullbackPointwise β x
    change HolomorphicOneForm.eval (e.pullbackOfAll hAll (α + β)) x
        = HolomorphicOneForm.eval (e.pullbackOfAll hAll α + e.pullbackOfAll hAll β) x
    rw [h_sum, h_add, h_α, h_β]
    exact congrFun (HolomorphicEquiv.pullbackPointwise_add e α β) x
  map_smul' c α := by
    refine ContMDiffSection.coe_injective ?_
    funext x
    have h_smul : HolomorphicOneForm.eval (e.pullbackOfAll hAll (c • α)) x
        = e.pullbackPointwise (c • α) x :=
      e.pullbackOfAll_eval hAll (c • α) x
    have h_α : HolomorphicOneForm.eval (e.pullbackOfAll hAll α) x
        = e.pullbackPointwise α x :=
      e.pullbackOfAll_eval hAll α x
    have h_smul_eval :
        HolomorphicOneForm.eval (c • e.pullbackOfAll hAll α) x
          = c • HolomorphicOneForm.eval (e.pullbackOfAll hAll α) x :=
      HolomorphicOneForm.eval_smul c _ x
    change HolomorphicOneForm.eval (e.pullbackOfAll hAll (c • α)) x
        = HolomorphicOneForm.eval (c • e.pullbackOfAll hAll α) x
    rw [h_smul, h_smul_eval, h_α]
    exact congrFun (HolomorphicEquiv.pullbackPointwise_smul e c α) x

/-- The linear-map shape unfolds to the underlying function. -/
@[simp] theorem HolomorphicEquiv.pullbackLinearMap_apply
    (e : HolomorphicEquiv X Y)
    (hAll : IsHolomorphicOneFormPullback_for_all e)
    (α : HolomorphicOneForm Y) :
    e.pullbackLinearMap hAll α = e.pullbackOfAll hAll α := rfl

/-! ## Unconditional `LinearMap` from `RiemannSphere` codomain -/

/-- **Unconditional pullback linear map for biholomorphisms into the
Riemann sphere.** Combines zz290's unconditional discharge with
`pullbackLinearMap`. -/
noncomputable def HolomorphicEquiv.pullbackLinearMap_RiemannSphere
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere) :
    HolomorphicOneForm JacobianChallenge.RiemannSphere
      →ₗ[ℂ] HolomorphicOneForm X :=
  e.pullbackLinearMap (isHolomorphicOneFormPullback_for_all_RiemannSphere e)

end JacobianChallenge

end
