/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.SurfaceClassificationGenus
import JacobianChallenge.Manifold.RiemannSphere
import JacobianChallenge.Manifold.PullbackHolomorphicOneForm
import JacobianChallenge.Manifold.PullbackLinearEquiv

set_option diagnostics.threshold 100

/-! # Item 14 (`genus_eq_zero_iff_homeo`) from a single uniformization input

This file ships the **single-input reduction** of challenge item 14
(`genus_eq_zero_iff_homeo` in `Basic.lean`). Following the honest
holomorphic pullback chain landed in `PullbackHolomorphicOneForm.lean`
(zz307) and `PullbackLinearEquiv.lean` (zz308), the open frontier of
item 14 is now compressed into one named open hypothesis:

* `UniformizationToRiemannSphere X : Prop` —
  `(genus X = 0 ∨ Nonempty (X ≃ₜ StandardS2)) → Nonempty (HolomorphicEquiv X RS)`

i.e., "any compact connected Riemann surface that is either of geometric
genus 0 *or* topologically a 2-sphere is biholomorphic to the standard
Riemann sphere". This is the classical content of the uniformization
theorem for closed Riemann surfaces of genus 0, packaged in the exact
shape required to close both directions of item 14.

## How both directions follow from this single input

* **Forward** (`genus X = 0 → ∃ ≃ₜ S²`): supply `Or.inl hg` to the
  hypothesis to get `e : HolomorphicEquiv X RS`; downcast via
  `e.toHomeomorph` and compose with
  `RiemannSphere.toSphereHomeo : RiemannSphere ≃ₜ StandardS2`.

* **Reverse** (`∃ ≃ₜ S² → genus X = 0`): supply `Or.inr h` to the
  hypothesis to get `e : HolomorphicEquiv X RS`; feed it to
  `genus_eq_zero_of_holomorphicEquiv_RiemannSphere_honest` (zz307) to
  conclude `genus X = 0`.

## What is honestly proven here

* `UniformizationToRiemannSphere X : Prop` — the single named open
  hypothesis (definition).
* `genus0ImpliesS2_of_uniformizationToRiemannSphere` — forward bridge
  from the single input.
* `s2ImpliesGenus0_of_uniformizationToRiemannSphere` — reverse bridge
  from the single input.
* `surfaceClassificationGenus_of_uniformizationToRiemannSphere` —
  bundle from the single input.
* `genus_eq_zero_iff_homeo_of_uniformizationToRiemannSphere` — the
  assembled biconditional from the single input.

**No `sorry`, no `axiom`.**

## Relation to the two-input version (`Item14FromUniformization.lean`)

zz275's `Item14FromUniformization.lean` packaged item 14 from two open
inputs:

* `UniformizationGenus0 X` — homeomorphism-level forward direction.
* `HolomorphicOneFormEquivRiemannSphere X` — linear-equivalence reverse
  direction.

Each of those was strictly weaker than a biholomorphism with the Riemann
sphere — zz308 showed both can be supplied from a single
`HolomorphicEquiv X RS`. This file consolidates that observation into
a **single** named open hypothesis. The previous two-input file remains
in place as the lower-level lemma; this is its honest one-input upgrade.

## What is left open

The single named hypothesis `UniformizationToRiemannSphere X` itself.
This is uniformization for closed Riemann surfaces of genus 0, which is
not in mathlib at the pinned commit. **Item 14 in `Basic.lean` therefore
remains `sorry`**: this chip reduces the open frontier to one named
classical input, but does not close it.
-/

open scoped Manifold ContDiff

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The single named open hypothesis -/

/-- **Single uniformization input for item 14.** A compact connected
Riemann surface `X` that is either of geometric genus 0 *or*
topologically the standard 2-sphere admits a biholomorphism with the
standard Riemann sphere `OnePoint ℂ`.

Classically, the disjunction reflects two routes through the
uniformization theorem:

* `genus X = 0` route: uniformization for genus-0 surfaces says any
  compact connected Riemann surface of geometric genus 0 is
  biholomorphic to `OnePoint ℂ`.

* `Nonempty (X ≃ₜ StandardS2)` route: a complex structure on the
  topological 2-sphere is biholomorphic to `OnePoint ℂ` (also by
  uniformization).

Both routes yield the same conclusion — a biholomorphism with the
Riemann sphere — and either alone suffices to close one direction of
item 14. Packaged as a single hypothesis here.

Not provable at the pinned mathlib commit. -/
def UniformizationToRiemannSphere (X : Type*)
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Prop :=
  (JacobianChallenge.genus X = 0 ∨ Nonempty (X ≃ₜ StandardS2)) →
    Nonempty (HolomorphicEquiv X JacobianChallenge.RiemannSphere)

/-! ## Forward direction from the single input -/

/-- **Forward bridge from the single uniformization input.**
`Genus0ImpliesS2 X` follows from `UniformizationToRiemannSphere X`: apply
the hypothesis with the left disjunct `Or.inl hg`, downcast the resulting
biholomorphism to a homeomorphism via `Diffeomorph.toHomeomorph`, and
compose with the topological identification
`RiemannSphere.toSphereHomeo : RiemannSphere ≃ₜ StandardS2`. -/
theorem genus0ImpliesS2_of_uniformizationToRiemannSphere
    (hU : UniformizationToRiemannSphere X) :
    Genus0ImpliesS2 X := by
  intro hg
  obtain ⟨e⟩ := hU (Or.inl hg)
  exact ⟨e.toHomeomorph.trans RiemannSphere.toSphereHomeo⟩

/-! ## Reverse direction from the single input -/

/-- **Reverse bridge from the single uniformization input.**
`S2ImpliesGenus0 X` follows from `UniformizationToRiemannSphere X`:
apply the hypothesis with the right disjunct `Or.inr h` to obtain a
biholomorphism `e : HolomorphicEquiv X RS`, then feed it to
`genus_eq_zero_of_holomorphicEquiv_RiemannSphere_honest` (zz307,
`PullbackHolomorphicOneForm.lean`). -/
theorem s2ImpliesGenus0_of_uniformizationToRiemannSphere
    (hU : UniformizationToRiemannSphere X) :
    S2ImpliesGenus0 X := by
  intro h
  obtain ⟨e⟩ := hU (Or.inr h)
  exact genus_eq_zero_of_holomorphicEquiv_RiemannSphere_honest e

/-! ## Bundle and biconditional from the single input -/

/-- **`SurfaceClassificationGenus X` bundle from the single
uniformization input.** Packages the two bridge lemmas above into the
`SurfaceClassificationGenus` record used by
`Item14FromUniformization.lean`. -/
theorem surfaceClassificationGenus_of_uniformizationToRiemannSphere
    (hU : UniformizationToRiemannSphere X) :
    SurfaceClassificationGenus X where
  genus_zero_to_sphere := genus0ImpliesS2_of_uniformizationToRiemannSphere hU
  sphere_to_genus_zero := s2ImpliesGenus0_of_uniformizationToRiemannSphere hU

/-- **Item 14 biconditional from the single uniformization input.**
The full statement of `genus_eq_zero_iff_homeo` from `Basic.lean`
(`genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2)`) follows from the single
named open hypothesis `UniformizationToRiemannSphere X`.

This is the cleanest reduction of item 14 currently available: a single
classical input (uniformization for closed Riemann surfaces of genus 0)
implies the full biconditional. The input itself is not in mathlib at
the pinned commit, so item 14 in `Basic.lean` remains `sorry`. -/
theorem genus_eq_zero_iff_homeo_of_uniformizationToRiemannSphere
    (hU : UniformizationToRiemannSphere X) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) :=
  (surfaceClassificationGenus_of_uniformizationToRiemannSphere hU).toIff

/-! ## Non-vacuity witness: discharge for `X = RiemannSphere` -/

namespace RiemannSphere

/-- **Trivial discharge of the single uniformization input on the
Riemann sphere.** For `X = RiemannSphere` no uniformization theorem is
needed; the identity biholomorphism witnesses the conclusion.

This shows the single-input reduction in this file is non-vacuous: on
at least one concrete Riemann surface, the single open hypothesis
discharges unconditionally. -/
theorem uniformizationToRiemannSphere_RiemannSphere :
    JacobianChallenge.UniformizationToRiemannSphere
      JacobianChallenge.RiemannSphere :=
  fun _ => ⟨(HolomorphicEquiv.refl :
    HolomorphicEquiv JacobianChallenge.RiemannSphere
      JacobianChallenge.RiemannSphere)⟩

/-- **Item 14 specialised to the Riemann sphere — via the single-input
reduction.** Plugs `uniformizationToRiemannSphere_RiemannSphere` into
`genus_eq_zero_iff_homeo_of_uniformizationToRiemannSphere`. This is a
third parallel derivation of `genus_eq_zero_iff_homeo_RiemannSphere`
(alongside zz277's bundle version in `Item14ForRiemannSphere.lean` and
zz278's two-input version in `UniformizationInputsRiemannSphere.lean`),
testifying that the single-input reduction discharges on
`X = RiemannSphere`. -/
theorem genus_eq_zero_iff_homeo_RiemannSphere_via_single_uniformization :
    JacobianChallenge.genus JacobianChallenge.RiemannSphere = 0 ↔
      Nonempty (JacobianChallenge.RiemannSphere ≃ₜ StandardS2) :=
  genus_eq_zero_iff_homeo_of_uniformizationToRiemannSphere
    uniformizationToRiemannSphere_RiemannSphere

end RiemannSphere

end JacobianChallenge
