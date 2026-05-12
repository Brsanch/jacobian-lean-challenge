/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormLinear
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option diagnostics.threshold 100

/-! # Unconditional discharge of the linear-injection bridge for `genus X = 0`

`Manifold/HolomorphicOneFormLinear.lean` ships
`genus_eq_zero_of_injects_into_RiemannSphere`, which takes a `ℂ`-linear
injection into `HolomorphicOneForm RiemannSphere` *and* the open
`subsingleton_statement` for the Riemann sphere. With zz274
(`Manifold/RiemannSphereChartSCoeffOverlap.lean`) discharging that
`Subsingleton` instance unconditionally, the second hypothesis is no
longer needed.

This file ships the resulting one-input form: from a `ℂ`-linear
injection `HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm RiemannSphere`
alone, `genus X = 0` follows. The same goes for the `≃ₗ[ℂ]` and
`Nonempty`-wrapped variants.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- **Unconditional discharge from a one-sided linear injection.** A
`ℂ`-linear injection of `HolomorphicOneForm X` into
`HolomorphicOneForm RiemannSphere` forces `genus X = 0`. The subsingleton
input on the Riemann-sphere side is supplied internally from zz274. -/
theorem genus_eq_zero_of_injects_into_RiemannSphere_unconditional
    (hInj : HolomorphicOneFormInjectsIntoRiemannSphere X) :
    JacobianChallenge.genus X = 0 :=
  genus_eq_zero_of_injects_into_RiemannSphere hInj
    (inferInstance :
      Subsingleton (HolomorphicOneForm JacobianChallenge.RiemannSphere))

/-- **Unconditional discharge from a linear injection (unwrapped).** A
`ℂ`-linear injection plus a proof it is injective discharges `genus X =
0` unconditionally. -/
theorem genus_eq_zero_of_linearMap_injective_into_RiemannSphere
    (f : HolomorphicOneForm X →ₗ[ℂ]
          HolomorphicOneForm JacobianChallenge.RiemannSphere)
    (hf : Function.Injective f) :
    JacobianChallenge.genus X = 0 :=
  genus_eq_zero_of_injects_into_RiemannSphere_unconditional ⟨⟨f, hf⟩⟩

/-- **Unconditional discharge from a linear equivalence.** A `ℂ`-linear
equivalence between the holomorphic-1-form spaces of `X` and the Riemann
sphere discharges `genus X = 0` unconditionally. (Equivalences embed
into injections, so this is a corollary of the linear-injection version,
but downstream code is often written against the `≃ₗ[ℂ]` shape.) -/
theorem genus_eq_zero_of_linearEquiv_RiemannSphere_via_injection
    (e : HolomorphicOneForm X ≃ₗ[ℂ]
          HolomorphicOneForm JacobianChallenge.RiemannSphere) :
    JacobianChallenge.genus X = 0 :=
  genus_eq_zero_of_linearMap_injective_into_RiemannSphere
    e.toLinearMap e.injective

/-- **`HolomorphicOneFormEquivRiemannSphere` implies
`HolomorphicOneFormInjectsIntoRiemannSphere` and yields `genus = 0`
unconditionally.** Wraps the `≃ₗ[ℂ]` → `→ₗ[ℂ]` downcast plus the
linear-injection discharge. -/
theorem genus_eq_zero_of_holomorphicOneFormEquivRiemannSphere_unconditional
    (hEq : HolomorphicOneFormEquivRiemannSphere X) :
    JacobianChallenge.genus X = 0 :=
  genus_eq_zero_of_injects_into_RiemannSphere_unconditional
    (holomorphicOneFormInjectsIntoRiemannSphere_of_equiv hEq)

end JacobianChallenge
