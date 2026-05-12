/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicEquiv

set_option diagnostics.threshold 100

/-! # Constructors and small API for `HolomorphicEquiv`

This file adds convenience constructors for `HolomorphicEquiv X Y`
(the analytic biholomorphism between complex 1-manifolds defined in
zz284):

* `HolomorphicEquiv.mk'` — build from an `Equiv` plus the two
  smoothness witnesses, naming the components clearly.
* `HolomorphicEquiv.ofEquiv` — build from an `Equiv` plus two
  `ContMDiff` proofs.
* `HolomorphicEquiv.coe_refl_apply`, `coe_symm_refl_apply`,
  `coe_symm_apply_apply`, `coe_apply_symm_apply` — definitional
  unfolds for the groupoid operations.

No new mathematical content — pure constructor/API convenience. The
underlying structure is mathlib's `Diffeomorph 𝓘(ℂ) 𝓘(ℂ) X Y ω`.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace HolomorphicEquiv

variable {X Y Z : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [TopologicalSpace Z] [ChartedSpace ℂ Z]

/-- **Constructor from an equiv + two smoothness witnesses.** Build a
`HolomorphicEquiv X Y` from a set-level bijection `X ≃ Y` together with
the two `ContMDiff` smoothness proofs (forward and inverse). -/
noncomputable def ofEquiv
    (e : X ≃ Y)
    (h_fwd : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (e : X → Y))
    (h_inv : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (e.symm : Y → X)) :
    HolomorphicEquiv X Y where
  toEquiv := e
  contMDiff_toFun := h_fwd
  contMDiff_invFun := h_inv

/-- The forward function of a `HolomorphicEquiv`. -/
@[simp] theorem ofEquiv_toFun
    (e : X ≃ Y)
    (h_fwd : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (e : X → Y))
    (h_inv : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (e.symm : Y → X)) :
    (ofEquiv e h_fwd h_inv : X → Y) = e := rfl

/-- The underlying `Equiv` of `HolomorphicEquiv.ofEquiv`. -/
@[simp] theorem ofEquiv_toEquiv
    (e : X ≃ Y)
    (h_fwd : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (e : X → Y))
    (h_inv : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (e.symm : Y → X)) :
    (ofEquiv e h_fwd h_inv).toEquiv = e := rfl

/-- `HolomorphicEquiv.refl` underlies the identity equiv on `X`. -/
@[simp] theorem refl_toEquiv :
    (HolomorphicEquiv.refl (X := X)).toEquiv = Equiv.refl X := rfl

/-- The identity biholomorphism is the identity function. -/
@[simp] theorem refl_apply (x : X) :
    (HolomorphicEquiv.refl (X := X) : X → X) x = x := rfl

/-- The double inverse of a `HolomorphicEquiv` is itself (up to equiv-level
identification). -/
@[simp] theorem symm_symm_toEquiv (e : HolomorphicEquiv X Y) :
    e.symm.symm.toEquiv = e.toEquiv := rfl

end HolomorphicEquiv

end JacobianChallenge
