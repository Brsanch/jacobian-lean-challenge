/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.SurfaceClassificationGenus
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option diagnostics.threshold 100

/-! # Item 14 (`genus_eq_zero_iff_homeo`) for the Riemann sphere — unconditional

This file ships the **unconditional** closure of challenge item 14
specialised to `X = RiemannSphere`. Both directions of
`genus_eq_zero_iff_homeo` are trivially constructible for the Riemann
sphere itself:

* The forward direction `genus RS = 0 → Nonempty (RS ≃ₜ S²)` is
  immediate from `RiemannSphere.toSphereHomeo` — no uniformization is
  needed when `X` already *is* the Riemann sphere.
* The reverse direction `Nonempty (RS ≃ₜ S²) → genus RS = 0` is
  immediate from zz274's unconditional
  `RiemannSphere.genus_RiemannSphere_eq_zero` — no Hodge-bridge is
  needed when the genus calculation is on `RS` itself.

The biconditional for `X = RiemannSphere` therefore holds without any
open uniformization input. (For a general compact connected Riemann
surface `X`, the uniformization-flavored inputs of
`Item14FromUniformization.lean` are still required.)

This chip is the **specialised closure**: a witness that the assembled
biconditional in `Item14FromUniformization.lean` is non-vacuous, by
exhibiting at least one Riemann surface for which it discharges
unconditionally.

## What is honestly proven here

* `genus0ImpliesS2_RiemannSphere` — `Genus0ImpliesS2 RiemannSphere`.
* `s2ImpliesGenus0_RiemannSphere` — `S2ImpliesGenus0 RiemannSphere`.
* `surfaceClassificationGenus_RiemannSphere` —
  `SurfaceClassificationGenus RiemannSphere` (the bundle).
* `genus_eq_zero_iff_homeo_RiemannSphere` — the headline biconditional
  on `RiemannSphere`: `genus RS = 0 ↔ Nonempty (RS ≃ₜ StandardS2)`.

**No `sorry`, no `axiom`.**
-/

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-- **Forward bridge for the Riemann sphere — unconditional.**
`Genus0ImpliesS2 RiemannSphere` holds: the hypothesis `genus RS = 0` is
not even needed; we ship `RiemannSphere ≃ₜ StandardS2` directly via
`RiemannSphere.toSphereHomeo`. -/
theorem genus0ImpliesS2_RiemannSphere :
    Genus0ImpliesS2 JacobianChallenge.RiemannSphere :=
  fun _ => ⟨RiemannSphere.toSphereHomeo⟩

/-- **Reverse bridge for the Riemann sphere — unconditional.**
`S2ImpliesGenus0 RiemannSphere` holds: the hypothesis `Nonempty (RS ≃ₜ
S²)` is not even needed; we ship `genus RS = 0` directly via zz274's
`RiemannSphere.genus_RiemannSphere_eq_zero`. -/
theorem s2ImpliesGenus0_RiemannSphere :
    S2ImpliesGenus0 JacobianChallenge.RiemannSphere :=
  fun _ => RiemannSphere.genus_RiemannSphere_eq_zero

/-- **Surface classification bundle for the Riemann sphere — unconditional.**
Bundles `genus0ImpliesS2_RiemannSphere` and
`s2ImpliesGenus0_RiemannSphere` into a `SurfaceClassificationGenus`
witness. -/
theorem surfaceClassificationGenus_RiemannSphere :
    SurfaceClassificationGenus JacobianChallenge.RiemannSphere where
  genus_zero_to_sphere := genus0ImpliesS2_RiemannSphere
  sphere_to_genus_zero := s2ImpliesGenus0_RiemannSphere

/-- **Item 14 specialised to the Riemann sphere — unconditional.**
`genus RiemannSphere = 0 ↔ Nonempty (RiemannSphere ≃ₜ StandardS2)`.
This is the headline statement of `genus_eq_zero_iff_homeo` in
`Basic.lean`, instantiated at `X = RiemannSphere`. Both sides are
unconditionally true; the iff therefore reduces to `Iff.intro` on two
trivially-constructible witnesses. -/
theorem genus_eq_zero_iff_homeo_RiemannSphere :
    JacobianChallenge.genus JacobianChallenge.RiemannSphere = 0 ↔
      Nonempty (JacobianChallenge.RiemannSphere ≃ₜ StandardS2) :=
  surfaceClassificationGenus_RiemannSphere.toIff

end RiemannSphere

end JacobianChallenge
