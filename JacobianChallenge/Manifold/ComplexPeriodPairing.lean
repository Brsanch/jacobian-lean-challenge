/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothCycle
import JacobianChallenge.Manifold.H1SmoothMod
import JacobianChallenge.Manifold.HolomorphicOneFormRealComponent
import JacobianChallenge.Manifold.ComplexManifoldRealification
import JacobianChallenge.Manifold.SmoothPathIntegrability

/-! # Complex-valued period pairing on holomorphic 1-forms (chip PL-2d)

This file delivers the complex-valued period pairing

    `SmoothCycle 𝓘(ℝ, ℂ) X → HolomorphicOneForm X → ℂ`

assembled from PL-1's `realComponent` / `imagComponent` and PL-2a's
`SmoothCycle.integrate`. For a holomorphic 1-form `om` and a smooth cycle
`c` on the realified manifold,

    `complexPeriod c om := ∫_c (Re om) + i · ∫_c (Im om)`,

where both real-side integrals are `SmoothCycle.integrate c (...)` on the
real bundled components.

## What this file does *not* attempt

* Full `ℂ`-linearity of the pairing in the form argument. Additivity
  (`complexPeriod_add_right`) is delivered below using the PL-3e
  integrability witness (`SmoothPathIntegrability.lean`). ℂ-scaling is
  *not* attempted in this file: it mixes the real and imaginary
  components via `realPart (z • om) = Re z · realPart om − Im z · imagPart om`,
  which is an algebraic identity orthogonal to integrability and
  deserves its own chip.

* Factoring through `H₁`. The `StokesBoundaryInvariance` bundle in
  `Manifold/H1SmoothMod.lean` already factors the real-valued pairing
  through its `H1` quotient against a fixed `closedForms` submodule. The
  complex pairing factors symmetrically once the holomorphic-form
  submodule is wired in (separate chip).

## Main definitions

* `JacobianChallenge.complexPeriod : SmoothCycle 𝓘(ℝ, ℂ) X →
  HolomorphicOneForm X → ℂ` — the complex pairing
  `c, om ↦ Re ∫_c om + i · Im ∫_c om`.
* `JacobianChallenge.complexPeriodHom (om) : SmoothCycle 𝓘(ℝ, ℂ) X →+ ℂ`
  — `AddMonoidHom` in the cycle argument with `om` held fixed.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ⊤ X]

/-- The complex-valued period of a holomorphic 1-form `om` along a smooth
1-cycle `c` on the realified manifold:

    `Re ∫_c om + i · Im ∫_c om`,

where each summand is `SmoothCycle.integrate` against the corresponding
PL-1 component. -/
def complexPeriod (c : SmoothCycle 𝓘(ℝ, ℂ) X) (om : HolomorphicOneForm X) : ℂ :=
  ((SmoothCycle.integrate c (realComponent om) : ℝ) : ℂ)
    + Complex.I * ((SmoothCycle.integrate c (imagComponent om) : ℝ) : ℂ)

@[simp] lemma complexPeriod_zero_left (om : HolomorphicOneForm X) :
    complexPeriod (0 : SmoothCycle 𝓘(ℝ, ℂ) X) om = 0 := by
  unfold complexPeriod
  rw [SmoothCycle.integrate_zero_left, SmoothCycle.integrate_zero_left]
  push_cast
  ring

lemma complexPeriod_add_left (c₁ c₂ : SmoothCycle 𝓘(ℝ, ℂ) X)
    (om : HolomorphicOneForm X) :
    complexPeriod (c₁ + c₂) om = complexPeriod c₁ om + complexPeriod c₂ om := by
  unfold complexPeriod
  rw [SmoothCycle.integrate_add_left, SmoothCycle.integrate_add_left]
  push_cast
  ring

/-- The complex-valued period pairing as an `AddMonoidHom` in the cycle
argument, with the holomorphic 1-form held fixed. -/
def complexPeriodHom (om : HolomorphicOneForm X) :
    SmoothCycle 𝓘(ℝ, ℂ) X →+ ℂ where
  toFun c := complexPeriod c om
  map_zero' := complexPeriod_zero_left om
  map_add' c₁ c₂ := complexPeriod_add_left c₁ c₂ om

@[simp] lemma complexPeriodHom_apply (om : HolomorphicOneForm X)
    (c : SmoothCycle 𝓘(ℝ, ℂ) X) :
    complexPeriodHom om c = complexPeriod c om := rfl

/-- Real part of the complex period equals the real-side integral
against `realComponent om`. -/
@[simp] lemma re_complexPeriod (c : SmoothCycle 𝓘(ℝ, ℂ) X)
    (om : HolomorphicOneForm X) :
    (complexPeriod c om).re = SmoothCycle.integrate c (realComponent om) := by
  unfold complexPeriod
  simp

/-- Imaginary part of the complex period equals the real-side integral
against `imagComponent om`. -/
@[simp] lemma im_complexPeriod (c : SmoothCycle 𝓘(ℝ, ℂ) X)
    (om : HolomorphicOneForm X) :
    (complexPeriod c om).im = SmoothCycle.integrate c (imagComponent om) := by
  unfold complexPeriod
  simp

/-! ## Form-side additivity of `realComponent` / `imagComponent` -/

/-- `realComponent` is additive on holomorphic 1-forms (bundled-section
equality). -/
@[simp] lemma realComponent_add (om₁ om₂ : HolomorphicOneForm X) :
    realComponent (om₁ + om₂) = realComponent om₁ + realComponent om₂ := by
  refine ContMDiffSection.coe_inj ?_
  funext x
  -- Pointwise: `(om₁+om₂).realPart x = om₁.realPart x + om₂.realPart x`.
  exact HolomorphicOneForm.realPart_add om₁ om₂ x

/-- `imagComponent` is additive on holomorphic 1-forms (bundled-section
equality). -/
@[simp] lemma imagComponent_add (om₁ om₂ : HolomorphicOneForm X) :
    imagComponent (om₁ + om₂) = imagComponent om₁ + imagComponent om₂ := by
  refine ContMDiffSection.coe_inj ?_
  funext x
  exact HolomorphicOneForm.imagPart_add om₁ om₂ x

/-! ## Form-side additivity of `complexPeriod` (PL-3e consumer) -/

/-- **Form-side additivity of the complex period pairing.** Uses the
PL-3e integrability witness `SmoothPath.intervalIntegrable_integrand`
indirectly through `SmoothCycle.integrate_add_form`. -/
lemma complexPeriod_add_right (c : SmoothCycle 𝓘(ℝ, ℂ) X)
    (om₁ om₂ : HolomorphicOneForm X) :
    complexPeriod c (om₁ + om₂) = complexPeriod c om₁ + complexPeriod c om₂ := by
  unfold complexPeriod
  rw [realComponent_add, imagComponent_add,
      SmoothCycle.integrate_add_form, SmoothCycle.integrate_add_form]
  push_cast
  ring

/-- The complex-valued period pairing as an `AddMonoidHom` in the *form*
argument, with the smooth cycle held fixed. -/
def complexPeriodHomRight (c : SmoothCycle 𝓘(ℝ, ℂ) X) :
    HolomorphicOneForm X →+ ℂ where
  toFun om := complexPeriod c om
  map_zero' := by
    unfold complexPeriod
    -- `realComponent 0 = 0` and `imagComponent 0 = 0` by section
    -- additivity (a-b=a+(-b), then sub from zero), but we can short-cut
    -- via Re/Im of the zero form: pointwise `realPart 0 x = 0`, so
    -- `SmoothCycle.integrate c 0 = 0`.
    have h_re_zero : realComponent (0 : HolomorphicOneForm X)
        = (0 : SmoothOneForm 𝓘(ℝ, ℂ) X) := by
      refine ContMDiffSection.coe_inj ?_
      funext x
      exact HolomorphicOneForm.realPart_zero x
    have h_im_zero : imagComponent (0 : HolomorphicOneForm X)
        = (0 : SmoothOneForm 𝓘(ℝ, ℂ) X) := by
      refine ContMDiffSection.coe_inj ?_
      funext x
      exact HolomorphicOneForm.imagPart_zero x
    rw [h_re_zero, h_im_zero, SmoothCycle.integrate_zero_right]
    push_cast
    ring
  map_add' om₁ om₂ := complexPeriod_add_right c om₁ om₂

@[simp] lemma complexPeriodHomRight_apply (c : SmoothCycle 𝓘(ℝ, ℂ) X)
    (om : HolomorphicOneForm X) :
    complexPeriodHomRight c om = complexPeriod c om := rfl

end JacobianChallenge

end
