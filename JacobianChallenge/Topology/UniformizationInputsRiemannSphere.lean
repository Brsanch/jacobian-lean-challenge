/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Genus0ImpliesS2Reduction
import JacobianChallenge.Topology.S2ImpliesGenus0Discharge
import JacobianChallenge.Topology.Item14FromUniformization

set_option diagnostics.threshold 100

/-! # Trivial discharge of the uniformization inputs for `X = RiemannSphere`

The two open uniformization-flavored inputs of
`Item14FromUniformization.lean` —
`UniformizationGenus0 X` and `HolomorphicOneFormEquivRiemannSphere X` —
each become **trivially constructible** when `X = RiemannSphere`:

* `UniformizationGenus0 RiemannSphere` ↦ the identity homeomorphism
  `RiemannSphere ≃ₜ RiemannSphere`.
* `HolomorphicOneFormEquivRiemannSphere RiemannSphere` ↦ the identity
  `ℂ`-linear equivalence on `HolomorphicOneForm RiemannSphere`.

This file ships those two trivial discharges and then composes them
through `genus_eq_zero_iff_homeo_of_uniformization_inputs` to give a
second, parallel derivation of `genus_eq_zero_iff_homeo_RiemannSphere`
(the version shipped in `Item14ForRiemannSphere.lean` via the
`SurfaceClassificationGenus` bundle).

This is a non-vacuity witness: the assembly theorems in
`Item14FromUniformization.lean` discharge on at least one concrete
Riemann surface without requiring any external uniformization input.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-- **Trivial forward input for the Riemann sphere.** The forward
uniformization input `UniformizationGenus0 RiemannSphere` is discharged
by `Homeomorph.refl RiemannSphere`: no uniformization theorem is needed
when `X` is already the Riemann sphere. -/
theorem uniformizationGenus0_RiemannSphere :
    JacobianChallenge.UniformizationGenus0 JacobianChallenge.RiemannSphere :=
  fun _ => ⟨Homeomorph.refl _⟩

/-- **Trivial reverse input for the Riemann sphere.** The reverse
uniformization input `HolomorphicOneFormEquivRiemannSphere RiemannSphere`
is discharged by `LinearEquiv.refl ℂ _`: the holomorphic-1-form space of
the Riemann sphere is `ℂ`-linearly equivalent to itself. -/
theorem holomorphicOneFormEquivRiemannSphere_RiemannSphere :
    JacobianChallenge.HolomorphicOneFormEquivRiemannSphere
      JacobianChallenge.RiemannSphere :=
  ⟨LinearEquiv.refl ℂ
    (HolomorphicOneForm JacobianChallenge.RiemannSphere)⟩

/-- **Item 14 specialised to `X = RiemannSphere` — derived via
`Item14FromUniformization`.** Plugs the two trivial uniformization
discharges above into
`genus_eq_zero_iff_homeo_of_uniformization_inputs`. Provides a second,
parallel proof of the X=RS specialisation (alongside zz277's bundle
version). -/
theorem genus_eq_zero_iff_homeo_RiemannSphere_via_uniformization :
    JacobianChallenge.genus JacobianChallenge.RiemannSphere = 0 ↔
      Nonempty (JacobianChallenge.RiemannSphere ≃ₜ StandardS2) :=
  genus_eq_zero_iff_homeo_of_uniformization_inputs
    uniformizationGenus0_RiemannSphere
    holomorphicOneFormEquivRiemannSphere_RiemannSphere

/-- **Bundle form.** Specialise
`surfaceClassificationGenus_of_uniformization_inputs` to
`X = RiemannSphere` with the two trivial uniformization discharges.
This is a different derivation of zz277's
`surfaceClassificationGenus_RiemannSphere` bundle. -/
theorem surfaceClassificationGenus_RiemannSphere_via_uniformization :
    JacobianChallenge.SurfaceClassificationGenus
      JacobianChallenge.RiemannSphere :=
  JacobianChallenge.surfaceClassificationGenus_of_uniformization_inputs
    uniformizationGenus0_RiemannSphere
    holomorphicOneFormEquivRiemannSphere_RiemannSphere

end RiemannSphere

end JacobianChallenge
