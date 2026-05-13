/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothCycle
import JacobianChallenge.Manifold.H1SmoothMod
import JacobianChallenge.Manifold.HolomorphicOneFormRealComponent
import JacobianChallenge.Manifold.ComplexManifoldRealification

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

* `ℂ`-linearity of the pairing in the form argument. This requires
  additivity of the path integral in the 1-form, which in turn requires
  `intervalIntegrable` witnesses on chart-pullback integrands
  (`SmoothPath.integrate_add`). That integrability lemma is a separate
  chip (not part of PL-2).

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

end JacobianChallenge

end
