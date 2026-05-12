/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicEquiv
import JacobianChallenge.Manifold.HolomorphicOneForm
import JacobianChallenge.Manifold.HolomorphicOneFormRealification
import JacobianChallenge.Manifold.HolomorphicOneFormRealificationLinearity
import Mathlib.Geometry.Manifold.MFDeriv.Basic

set_option diagnostics.threshold 100

/-! # Pointwise pullback of a holomorphic 1-form along a `HolomorphicEquiv`

For a biholomorphism `e : X ≃ₕ Y` between complex 1-manifolds modelled
on `ℂ` (a `HolomorphicEquiv` from zz284) and a holomorphic 1-form
`α : HolomorphicOneForm Y`, the **pullback** is the section

  `(e* α) x := α (e x) ∘L mfderiv I I e x`

where `mfderiv I I e x : T_x X →L[ℂ] T_{e x} Y` is the manifold
derivative and `α (e x) : T_{e x} Y →L[ℂ] ℂ` (via the
`HolomorphicOneForm.eval` API).

## What this file delivers

This file packages the **pointwise function-level** pullback, without
addressing smoothness:

* `pullbackPointwise e α : ∀ x : X, CotangentSpace 𝓘(ℂ) x`.
* `pullbackPointwise_apply` — definitional unfolding.
* `pullbackPointwise_add`, `pullbackPointwise_smul`,
  `pullbackPointwise_zero`, `pullbackPointwise_neg`,
  `pullbackPointwise_sub` — `ℂ`-linearity (componentwise lemmas).
* `pullbackPointwiseLinearMap` — packaged `ℂ`-linear map into the
  function space `∀ x, CotangentSpace 𝓘(ℂ) x`.

## What is **not** in this file

Smoothness of the pullback section, which would upgrade it from a
function into a `HolomorphicOneForm X`. That is deferred to a
follow-up file.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff
open ContinuousLinearMap

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-! ## Pointwise pullback definition -/

/-- **Pointwise pullback of a holomorphic 1-form along a biholomorphism.**
Defined as the function

  `x ↦ (α.eval (e x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) e x)`

mapping `X` into the cotangent space at each `x`. Not packaged as a
section here; smoothness is the obligation of a downstream file. -/
def HolomorphicEquiv.pullbackPointwise
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm Y) :
    ∀ x : X, CotangentSpace (𝓘(ℂ, ℂ)) x :=
  fun x => ContinuousLinearMap.comp (HolomorphicOneForm.eval α (e x))
    (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (e : X → Y) x)

/-- Definitional unfolding of `pullbackPointwise`. -/
theorem HolomorphicEquiv.pullbackPointwise_apply
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm Y) (x : X) :
    e.pullbackPointwise α x
      = ContinuousLinearMap.comp (HolomorphicOneForm.eval α (e x))
          (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (e : X → Y) x) := rfl

variable (e : HolomorphicEquiv X Y)

/-- The pointwise pullback is additive in the form `α`. -/
theorem HolomorphicEquiv.pullbackPointwise_add
    (α β : HolomorphicOneForm Y) :
    e.pullbackPointwise (α + β)
      = e.pullbackPointwise α + e.pullbackPointwise β := by
  funext x
  simp only [HolomorphicEquiv.pullbackPointwise_apply,
    HolomorphicOneForm.eval_add, Pi.add_apply]
  exact ContinuousLinearMap.add_comp _ _ _

/-- The pointwise pullback respects `ℂ`-scalar multiplication. -/
theorem HolomorphicEquiv.pullbackPointwise_smul
    (c : ℂ) (α : HolomorphicOneForm Y) :
    e.pullbackPointwise (c • α) = c • e.pullbackPointwise α := by
  funext x
  simp only [HolomorphicEquiv.pullbackPointwise_apply,
    HolomorphicOneForm.eval_smul, Pi.smul_apply]
  exact ContinuousLinearMap.smul_comp _ _ _

/-- The pointwise pullback of the zero form is the zero function. -/
theorem HolomorphicEquiv.pullbackPointwise_zero :
    e.pullbackPointwise (0 : HolomorphicOneForm Y) = 0 := by
  funext x
  show ContinuousLinearMap.comp
      (HolomorphicOneForm.eval (0 : HolomorphicOneForm Y) (e x))
      (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (e : X → Y) x) = 0
  rw [HolomorphicOneForm.eval_zero]
  exact ContinuousLinearMap.zero_comp _

/-- The pointwise pullback is negation-preserving. -/
theorem HolomorphicEquiv.pullbackPointwise_neg
    (α : HolomorphicOneForm Y) :
    e.pullbackPointwise (-α) = -e.pullbackPointwise α := by
  funext x
  simp only [HolomorphicEquiv.pullbackPointwise_apply,
    HolomorphicOneForm.eval_neg, Pi.neg_apply]
  exact ContinuousLinearMap.neg_comp _ _

/-- The pointwise pullback is subtraction-preserving. -/
theorem HolomorphicEquiv.pullbackPointwise_sub
    (α β : HolomorphicOneForm Y) :
    e.pullbackPointwise (α - β)
      = e.pullbackPointwise α - e.pullbackPointwise β := by
  rw [sub_eq_add_neg, sub_eq_add_neg,
    HolomorphicEquiv.pullbackPointwise_add,
    HolomorphicEquiv.pullbackPointwise_neg]

/-! ## Linearity as a `LinearMap` (function-valued) -/

/-- The function-valued `ℂ`-linear map sending a holomorphic 1-form on
`Y` to its pointwise pullback function on `X`. Smoothness is **not**
asserted here; this is the function-level part. -/
def HolomorphicEquiv.pullbackPointwiseLinearMap :
    HolomorphicOneForm Y →ₗ[ℂ]
      (∀ x : X, CotangentSpace (𝓘(ℂ, ℂ)) x) where
  toFun α := e.pullbackPointwise α
  map_add' α β := HolomorphicEquiv.pullbackPointwise_add e α β
  map_smul' c α := HolomorphicEquiv.pullbackPointwise_smul e c α

/-- Definitional unfolding of `pullbackPointwiseLinearMap`. -/
@[simp] theorem HolomorphicEquiv.pullbackPointwiseLinearMap_apply
    (α : HolomorphicOneForm Y) (x : X) :
    e.pullbackPointwiseLinearMap α x = e.pullbackPointwise α x := rfl

/-- The pullback linear map applied to `0` is the zero function. -/
@[simp] theorem HolomorphicEquiv.pullbackPointwiseLinearMap_zero :
    e.pullbackPointwiseLinearMap (0 : HolomorphicOneForm Y) = 0 :=
  HolomorphicEquiv.pullbackPointwise_zero e

end JacobianChallenge

end
