/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormLinear
import JacobianChallenge.Topology.SurfaceClassificationGenus

set_option diagnostics.threshold 100

/-! # Item 14 from `Subsingleton (HolomorphicOneForm X)` and a homeomorphism

A genuinely orthogonal reduction of challenge item 14
(`genus_eq_zero_iff_homeo`): if `X` is *already known* to have a
subsingleton holomorphic-1-form space (i.e. `genus X = 0` for the
linear-algebra reason — no Hodge / uniformization needed) and `X` is
already known to be homeomorphic to `S²`, then the biconditional
`genus X = 0 ↔ Nonempty (X ≃ₜ S²)` holds trivially: both sides are
just unconditionally true.

This is the *purely combinatorial* path through item 14: it costs no
analytic input, only the assumption that the analytic content is
already established for the specific `X` of interest.

The Riemann sphere (zz277) is the canonical example where both
hypotheses hold unconditionally — zz274 supplies the subsingleton, and
`RiemannSphere.toSphereHomeo` supplies the homeomorphism. But this
file gives the generic form: for *any* `X` where both inputs hold,
item 14 collapses.

## What is honestly proven

* `genus0ImpliesS2_of_homeo` — `Genus0ImpliesS2 X` holds from a
  homeomorphism `X ≃ₜ S²` alone.
* `s2ImpliesGenus0_of_subsingleton` — `S2ImpliesGenus0 X` holds from
  `Subsingleton (HolomorphicOneForm X)` alone.
* `surfaceClassificationGenus_of_subsingleton_and_homeo` — the bundled
  classification from both inputs.
* `genus_eq_zero_iff_homeo_of_subsingleton_and_homeo` — the assembled
  biconditional `genus X = 0 ↔ Nonempty (X ≃ₜ S²)`.

**No `sorry`, no `axiom`.**
-/

open scoped Manifold ContDiff

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Forward bridge from a homeomorphism alone.** `Genus0ImpliesS2 X`
holds for any `X` that is already homeomorphic to `S²`: the
`genus X = 0` hypothesis is unused; the conclusion comes from the
homeomorphism directly. -/
theorem genus0ImpliesS2_of_homeo
    (h : Nonempty (X ≃ₜ StandardS2)) :
    Genus0ImpliesS2 X :=
  fun _ => h

/-- **Reverse bridge from a subsingleton alone.** `S2ImpliesGenus0 X`
holds for any `X` whose `HolomorphicOneForm X` space is a subsingleton:
the `Nonempty (X ≃ₜ S²)` hypothesis is unused; the conclusion comes
from `Module.finrank_zero_of_subsingleton`. -/
theorem s2ImpliesGenus0_of_subsingleton
    [Subsingleton (HolomorphicOneForm X)] :
    S2ImpliesGenus0 X :=
  fun _ => genus_eq_zero_of_holomorphicOneForm_subsingleton X inferInstance

/-- **Bundle from the two combinatorial inputs.** From a homeomorphism
`X ≃ₜ S²` and a subsingleton instance on `HolomorphicOneForm X`,
produce a `SurfaceClassificationGenus X` bundle. -/
theorem surfaceClassificationGenus_of_subsingleton_and_homeo
    [Subsingleton (HolomorphicOneForm X)]
    (h : Nonempty (X ≃ₜ StandardS2)) :
    SurfaceClassificationGenus X where
  genus_zero_to_sphere := genus0ImpliesS2_of_homeo h
  sphere_to_genus_zero := s2ImpliesGenus0_of_subsingleton

/-- **Item 14 biconditional from the two combinatorial inputs.** -/
theorem genus_eq_zero_iff_homeo_of_subsingleton_and_homeo
    [Subsingleton (HolomorphicOneForm X)]
    (h : Nonempty (X ≃ₜ StandardS2)) :
    JacobianChallenge.genus X = 0 ↔
      Nonempty (X ≃ₜ StandardS2) :=
  (surfaceClassificationGenus_of_subsingleton_and_homeo h).toIff

end JacobianChallenge
