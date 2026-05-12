/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PullbackSectionSmoothness
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackSmoothness

set_option diagnostics.threshold 100
set_option maxHeartbeats 1600000

/-! # Honest pullback of a `HolomorphicOneForm` along a `HolomorphicEquiv`

zz306 ships the smooth-section conclusion
`HolomorphicEquiv.pullbackSection_contMDiffAt`: the function
`fun x ↦ TotalSpace.mk' _ x (e.pullbackPointwise α x)` is
`ContMDiffAt 𝓘(ℂ) ω` at every `x₀`.

This file packages that result into:

* **`HolomorphicEquiv.pullbackForm e α : HolomorphicOneForm X`** — the
  actual smooth section, whose evaluation equals `e.pullbackPointwise α`.

* **Honest discharge** of zz290's named obligation
  `IsHolomorphicOneFormPullback_for_all e` — no longer through the
  zz287–zz301 tautological "subsingleton ↔ obligation" loop, but as
  the genuine analytic conclusion that the pullback is a smooth section.

* **`Subsingleton (HolomorphicOneForm X)`** for any `X` biholomorphic to
  the Riemann sphere — closing item 14 reverse direction unconditionally
  via the *honest* route (zz302+zz303+zz304+zz305+zz306+zz307).

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff
open ContinuousLinearMap

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-! ## The pullback as a `HolomorphicOneForm` -/

/-- **The smooth pullback section.** For any
`e : HolomorphicEquiv X Y` and `α : HolomorphicOneForm Y`, the
pointwise pullback `e.pullbackPointwise α : ∀ x : X, CotangentSpace x`
is upgraded to a smooth section, i.e. a `HolomorphicOneForm X`. -/
def HolomorphicEquiv.pullbackForm
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm Y) :
    HolomorphicOneForm X where
  toFun := e.pullbackPointwise α
  contMDiff_toFun := by
    intro x₀
    exact HolomorphicEquiv.pullbackSection_contMDiffAt e α x₀

/-- The underlying section of `pullbackForm` equals `pullbackPointwise`. -/
@[simp]
theorem HolomorphicEquiv.pullbackForm_toFun
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm Y) :
    (e.pullbackForm α).toFun = e.pullbackPointwise α := rfl

/-- Evaluating the pullback form via `HolomorphicOneForm.eval` recovers
the pointwise pullback. -/
theorem HolomorphicEquiv.pullbackForm_eval
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm Y) (x : X) :
    HolomorphicOneForm.eval (e.pullbackForm α) x
      = e.pullbackPointwise α x := rfl

/-! ## Pullback along `e.symm` (item-14 reverse direction) -/

/-- **The smooth pullback section along `e.symm`.** For any
`e : HolomorphicEquiv X Y` and `α : HolomorphicOneForm X`, the
pointwise pullback `e.symm.pullbackPointwise α : ∀ y : Y, CotangentSpace y`
is a smooth section. This is the version used to derive
`Subsingleton (HolomorphicOneForm X)` from
`Subsingleton (HolomorphicOneForm Y)` (e.g., when `Y = RiemannSphere`). -/
def HolomorphicEquiv.pullbackForm_symm
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm X) :
    HolomorphicOneForm Y where
  toFun := e.symm.pullbackPointwise α
  contMDiff_toFun := by
    intro y₀
    exact HolomorphicEquiv.pullbackSection_symm_contMDiffAt e α y₀

@[simp]
theorem HolomorphicEquiv.pullbackForm_symm_toFun
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm X) :
    (e.pullbackForm_symm α).toFun = e.symm.pullbackPointwise α := rfl

theorem HolomorphicEquiv.pullbackForm_symm_eval
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm X) (y : Y) :
    HolomorphicOneForm.eval (e.pullbackForm_symm α) y
      = e.symm.pullbackPointwise α y := rfl

/-! ## Honest discharge of `IsHolomorphicOneFormPullback_for_all`

zz290 named the obligation but discharged it only when the codomain is
itself subsingleton (zz287–zz301's tautological loop). The honest
analytic discharge is now:

* `IsHolomorphicOneFormPullback e α` holds for any `α`, witnessed by
  `pullbackForm e α` (whose evaluation equals `pullbackPointwise`).

* `IsHolomorphicOneFormPullback_for_all e` holds for any
  biholomorphism `e` (no subsingleton on the codomain required). -/

/-- **Honest pointwise discharge.** -/
theorem HolomorphicEquiv.isHolomorphicOneFormPullback_of_HolomorphicEquiv
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm Y) :
    IsHolomorphicOneFormPullback e α :=
  ⟨e.pullbackForm α, fun x => e.pullbackForm_eval α x⟩

/-- **Honest universal discharge.** For any
`e : HolomorphicEquiv X Y`, every pointwise pullback of a holomorphic
1-form on `Y` is realised by a `HolomorphicOneForm X` — without any
subsingleton hypothesis on the codomain. -/
theorem HolomorphicEquiv.isHolomorphicOneFormPullback_for_all_of_HolomorphicEquiv
    (e : HolomorphicEquiv X Y) :
    IsHolomorphicOneFormPullback_for_all e :=
  fun α => e.isHolomorphicOneFormPullback_of_HolomorphicEquiv α

/-- **Honest universal discharge (symm direction).** -/
theorem HolomorphicEquiv.isHolomorphicOneFormPullback_for_all_symm_of_HolomorphicEquiv
    (e : HolomorphicEquiv X Y) :
    IsHolomorphicOneFormPullback_for_all e.symm :=
  fun α => ⟨e.pullbackForm_symm α, fun y => e.pullbackForm_symm_eval α y⟩

/-! ## Item-14 reverse closure via the honest route

For `e : HolomorphicEquiv X RiemannSphere`, the honest universal-symm
discharge feeds zz295's
`HolomorphicOneForm.subsingleton_of_holomorphicEquiv_RiemannSphere`,
which combines it with `Subsingleton (HolomorphicOneForm RiemannSphere)`
(zz274, unconditional) to give `Subsingleton (HolomorphicOneForm X)`. -/

/-- **Item-14 reverse, honest closure.** For any `X` biholomorphic to
the Riemann sphere, `HolomorphicOneForm X` is a subsingleton. This is
discharged via:

* `pullbackForm_symm` (this file) — the smooth pullback section along
  `e.symm : RS → X` for any `α : HolomorphicOneForm X`.
* `pullbackSection_symm_contMDiffAt` (zz306) — the unconditional
  analytic content (cotangent bundle pullback is smooth).
* Bridge identities and the algebraic shape (zz302–zz305).

This route does NOT depend on the zz287–zz301 tautological loop
(named-obligation ↔ subsingleton); it goes through the honest analytic
discharge of the named obligation. -/
theorem HolomorphicOneForm.subsingleton_of_holomorphicEquiv_RiemannSphere_honest
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere) :
    Subsingleton (HolomorphicOneForm X) :=
  HolomorphicOneForm.subsingleton_of_holomorphicEquiv_RiemannSphere e
    e.isHolomorphicOneFormPullback_for_all_symm_of_HolomorphicEquiv

/-- **Genus consequence, honest route.** For any `X` biholomorphic to
the Riemann sphere, `genus X = 0`. -/
theorem genus_eq_zero_of_holomorphicEquiv_RiemannSphere_honest
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere) :
    JacobianChallenge.genus X = 0 := by
  haveI := HolomorphicOneForm.subsingleton_of_holomorphicEquiv_RiemannSphere_honest e
  exact genus_eq_zero_of_holomorphicOneForm_subsingleton X inferInstance

end JacobianChallenge

end
