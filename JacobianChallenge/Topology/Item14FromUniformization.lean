/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Genus0ImpliesS2Reduction
import JacobianChallenge.Topology.S2ImpliesGenus0Discharge
import JacobianChallenge.Topology.SurfaceClassificationGenus
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option diagnostics.threshold 100

/-! # Item 14 (`genus_eq_zero_iff_homeo`) from the uniformization inputs

This file packages the **full biconditional** of challenge item 14
(`genus_eq_zero_iff_homeo` in `Basic.lean`) as a one-step assembly from
the two named open uniformization-flavored inputs:

* `UniformizationGenus0 X` — forward: `genus X = 0` produces a
  homeomorphism with the Riemann sphere (uniformization for closed
  Riemann surfaces).
* `HolomorphicOneFormEquivRiemannSphere X` — reverse: the holomorphic
  1-form space of `X` is `ℂ`-linearly equivalent to that of the Riemann
  sphere (uniformization plus pullback of 1-forms).

The Riemann-sphere genus-zero leg, formerly a third open input, is no
longer needed: zz274 (`Manifold/RiemannSphereChartSCoeffOverlap.lean`)
discharged `RiemannSphere.genus_RiemannSphere_statement_holds`
unconditionally. We feed it in internally here.

So item 14 reduces, at the pinned mathlib commit, to **exactly the two
uniformization inputs above** — neither of which is in mathlib at the
pin, but both of which are the genuine classical analytic content
required by every textbook proof.

## What is honestly proven here

* `surfaceClassificationGenus_of_uniformization_inputs` — packages the
  two uniformization-flavored inputs into a `SurfaceClassificationGenus
  X` bundle, internally supplying the unconditional Riemann-sphere
  genus-zero leg.
* `genus_eq_zero_iff_homeo_of_uniformization_inputs` — the assembled
  biconditional `genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2)` from the two
  uniformization inputs alone.

**No `sorry`, no `axiom`.**

## What is left open

The two uniformization inputs (`UniformizationGenus0 X` and
`HolomorphicOneFormEquivRiemannSphere X`). Both require uniformization
for closed Riemann surfaces, which is not in mathlib at the pinned
commit. This file therefore does NOT close item 14; it consolidates the
open frontier from three inputs down to the two genuinely deep ones.
-/

open scoped Manifold ContDiff

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Bundle from the two uniformization inputs.** Given the forward
uniformization input `UniformizationGenus0 X` and the reverse
holomorphic-1-form linear-equivalence input
`HolomorphicOneFormEquivRiemannSphere X`, produce a
`SurfaceClassificationGenus X` bundle. The Riemann-sphere genus-zero leg
is supplied internally from `genus_RiemannSphere_statement_holds`
(`Manifold/RiemannSphereChartSCoeffOverlap.lean`).

Once a `SurfaceClassificationGenus X` is in hand, the biconditional
`genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2)` follows by
`SurfaceClassificationGenus.toIff`. -/
theorem surfaceClassificationGenus_of_uniformization_inputs
    (hU : UniformizationGenus0 X)
    (hEq : HolomorphicOneFormEquivRiemannSphere X) :
    SurfaceClassificationGenus X where
  genus_zero_to_sphere := genus0ImpliesS2_of_homeoRiemannSphere hU
  sphere_to_genus_zero :=
    s2ImpliesGenus0_of_linearEquiv hEq
      RiemannSphere.genus_RiemannSphere_statement_holds

/-- **Item 14 biconditional from the two uniformization inputs.** The
biconditional `JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ
StandardS2)` (the statement of `genus_eq_zero_iff_homeo` in `Basic.lean`)
follows from the two named uniformization inputs alone. The
Riemann-sphere genus-zero ingredient is supplied internally from
zz274's `genus_RiemannSphere_statement_holds`. -/
theorem genus_eq_zero_iff_homeo_of_uniformization_inputs
    (hU : UniformizationGenus0 X)
    (hEq : HolomorphicOneFormEquivRiemannSphere X) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) :=
  (surfaceClassificationGenus_of_uniformization_inputs hU hEq).toIff

/-- Variant taking the linear equivalence directly (not wrapped in
`Nonempty`). -/
theorem genus_eq_zero_iff_homeo_of_uniformization_inputs'
    (hU : UniformizationGenus0 X)
    (e : HolomorphicOneForm X ≃ₗ[ℂ]
          HolomorphicOneForm JacobianChallenge.RiemannSphere) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) :=
  genus_eq_zero_iff_homeo_of_uniformization_inputs hU ⟨e⟩

end JacobianChallenge
