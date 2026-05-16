/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneForm

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Holomorphic 1-forms on an open subset

`HolomorphicOneFormOn X s` is the type of holomorphic (= `C^ω`) 1-form
sections of the cotangent bundle of `X` defined and analytic on a
subset `s : Set X` of a complex 1-manifold.

This is the holomorphic / `𝓘(ℂ, ℂ)`-bundle analogue of
`SmoothOneFormOn` (`Manifold/SmoothOneFormOn.lean`). The bundle is the
`ℂ`-linear cotangent bundle (fiber `ℂ →L[ℂ] ℂ`) with `ω`-smoothness.

Like `SmoothOneFormOn`, this stores a total dependent function on `X`
plus a `ContMDiffOn ω`-on-`s` witness for its total-space lift; the
values off `s` are unconstrained (junk).

Use case: the eventual **trace map** `f_*α : HolomorphicOneForm X →
HolomorphicOneFormOn RiemannSphere f.regularValueSet`, packaging the
holomorphic data of the trace on the open regular set. The completion
to a global `HolomorphicOneForm RiemannSphere` (via n-th-root
cancellation + Riemann removable singularity at critical values) is
the next-stage chip arc; this file ships the *target type* for the
on-regular-set piece.

This file ships only:

* The type `HolomorphicOneFormOn`.
* `CoeFun` (so `om x` extracts the cotangent value).
* `HolomorphicOneForm.restrictHolOn` — canonical restriction from
  global to partial domain.

Algebra (`AddCommGroup`, `Module ℂ`) and the operations relating to
realification are deferred to subsequent chips on a needed basis.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] (s : Set X)

/-- **Holomorphic 1-form on a subset.** A function-valued section
`toFun : ∀ x, CotangentSpace 𝓘(ℂ, ℂ) x` together with a proof that the
total-space lift is `ContMDiffOn 𝓘(ℂ, ℂ) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω`
on `s`. Outside `s`, the value of `toFun` is unconstrained. -/
structure HolomorphicOneFormOn where
  /-- The underlying function-valued section. -/
  toFun : ∀ x : X, CotangentSpace 𝓘(ℂ, ℂ) x
  /-- The `ω`-smoothness witness on `s`. -/
  contMDiffOn_section :
    ContMDiffOn 𝓘(ℂ, ℂ) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun x : X => @Bundle.TotalSpace.mk X (ℂ →L[ℂ] ℂ)
        (CotangentSpace 𝓘(ℂ, ℂ)) x (toFun x)) s

namespace HolomorphicOneFormOn

variable {X s}

instance instCoeFun : CoeFun (HolomorphicOneFormOn X s)
    (fun _ => ∀ x : X, CotangentSpace 𝓘(ℂ, ℂ) x) :=
  ⟨HolomorphicOneFormOn.toFun⟩

@[simp] lemma coeFun_mk
    (f : ∀ x : X, CotangentSpace 𝓘(ℂ, ℂ) x)
    (hf : ContMDiffOn 𝓘(ℂ, ℂ) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun x : X => @Bundle.TotalSpace.mk X (ℂ →L[ℂ] ℂ)
        (CotangentSpace 𝓘(ℂ, ℂ)) x (f x)) s) :
    (mk f hf : ∀ x : X, CotangentSpace 𝓘(ℂ, ℂ) x) = f := rfl

end HolomorphicOneFormOn

/-! ## Restriction from a global holomorphic 1-form -/

/-- **Canonical restriction.** Every global `HolomorphicOneForm X`
restricts to a `HolomorphicOneFormOn X s` for any subset `s ⊆ X`. The
total-space `ContMDiffOn` follows from the global `ContMDiff` via
`ContMDiff.contMDiffOn`. -/
def HolomorphicOneForm.restrictHolOn
    (om : HolomorphicOneForm X) (s : Set X) :
    HolomorphicOneFormOn X s where
  toFun := om.toFun
  contMDiffOn_section := om.contMDiff.contMDiffOn

@[simp] lemma HolomorphicOneForm.restrictHolOn_toFun_apply
    (om : HolomorphicOneForm X) (s : Set X) (x : X) :
    (HolomorphicOneForm.restrictHolOn (X := X) om s).toFun x = om.toFun x := rfl

end
