/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.SurfaceClassificationGenus
import JacobianChallenge.Manifold.RiemannSphere

set_option diagnostics.threshold 100

/-! # Reduction of `Genus0ImpliesS2` to the uniformization theorem

This file discharges the named hypothesis
`JacobianChallenge.Genus0ImpliesS2 X` from
`JacobianChallenge/Topology/SurfaceClassificationGenus.lean`
(challenge item 14, **forward direction**) under a single explicit
intermediate hypothesis: a homeomorphism

```
X ≃ₜ JacobianChallenge.RiemannSphere
```

(produced classically from genus 0 by the **uniformization theorem** for
closed Riemann surfaces, which gives a biholomorphism whose underlying
map is a homeomorphism).

## Why an intermediate hypothesis is necessary

The classical proof of the forward direction goes
`genus X = 0` → (uniformization on a compact connected Riemann surface)
→ `X` biholomorphic to `OnePoint ℂ` → `X ≃ₜ OnePoint ℂ`. The
biholomorphism step is genuine deep mathematics not present in mathlib at
the pinned commit. The biholomorphism-to-homeomorphism downgrade is
mechanical: any biholomorphism is in particular a homeomorphism. We
package the input at the homeomorphism level, so a future caller that
produces a biholomorphism (or smooth equivalence) needs only the trivial
downcast.

The transit from `OnePoint ℂ ≃ₜ X` to `X ≃ₜ StandardS2` (the form used in
`Basic.lean`'s `genus_eq_zero_iff_homeo` statement) is closed mechanically
here using `RiemannSphere.toSphereHomeo : RiemannSphere ≃ₜ StandardS2`
already established in `Manifold/RiemannSphere.lean`.

## What is honestly proven here

* `genus0ImpliesS2_of_homeoRiemannSphere` — given the open hypothesis
  `UniformizationGenus0 X`, the named bridge `Genus0ImpliesS2 X` follows.
  **No `sorry`, no axiom.**

* `genus0ImpliesS2_of_homeoRiemannSphere'` — same, taking the
  homeomorphism witness directly under the assumption `genus X = 0`.

## What is left as an open hypothesis

* `UniformizationGenus0 X : Prop` — `genus X = 0 → Nonempty
  (X ≃ₜ RiemannSphere)`. Classically supplied by uniformization for
  closed Riemann surfaces. Not in mathlib at the pinned commit.

The reduction in this file converts the single open input
`UniformizationGenus0 X` into the open output `Genus0ImpliesS2 X`, moving
the open frontier strictly closer to the analytic content classical
proofs use.
-/

open scoped Manifold ContDiff

namespace JacobianChallenge

/-! ### Named open hypothesis -/

/-- **Open hypothesis (forward, uniformization layer).** A closed
connected Riemann surface of geometric genus 0 admits a homeomorphism
with the Riemann sphere `OnePoint ℂ`.

Classically, uniformization gives a *biholomorphism*, which restricts to
a homeomorphism. Stated at the homeomorphism level so the downstream
reduction is mechanical; any future caller producing a biholomorphism
can supply this hypothesis by extracting the underlying continuous
inverse pair.

Stated as `Nonempty` to be `Prop`-valued, matching the convention of the
sister file `S2ImpliesGenus0Discharge.lean`. -/
def UniformizationGenus0 (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Prop :=
  JacobianChallenge.genus X = 0 →
    Nonempty (X ≃ₜ JacobianChallenge.RiemannSphere)

/-! ### Discharge of `Genus0ImpliesS2` -/

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Discharge of `Genus0ImpliesS2`** under the single explicit
hypothesis `UniformizationGenus0 X`.

The proof is mechanical: extract the homeomorphism `X ≃ₜ RiemannSphere`
from the uniformization hypothesis, then compose with the topological
identification `RiemannSphere.toSphereHomeo : RiemannSphere ≃ₜ StandardS2`
to obtain `X ≃ₜ StandardS2`. **No `sorry`, no axiom.** -/
theorem genus0ImpliesS2_of_homeoRiemannSphere
    (hU : UniformizationGenus0 X) :
    Genus0ImpliesS2 X := by
  intro hg
  obtain ⟨e⟩ := hU hg
  exact ⟨e.trans RiemannSphere.toSphereHomeo⟩

/-- Specialisation taking the homeomorphism with the Riemann sphere
directly under the assumption `genus X = 0`. -/
theorem genus0ImpliesS2_of_homeoRiemannSphere'
    (hg : JacobianChallenge.genus X = 0)
    (e : X ≃ₜ JacobianChallenge.RiemannSphere) :
    Nonempty (X ≃ₜ StandardS2) :=
  ⟨e.trans RiemannSphere.toSphereHomeo⟩

end JacobianChallenge
