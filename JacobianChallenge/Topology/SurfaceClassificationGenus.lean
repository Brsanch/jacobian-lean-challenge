/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneForm
import JacobianChallenge.Topology.SurfaceGenus
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.NormedSpace.Real

set_option diagnostics.threshold 100

/-! # Surface classification bridge for `genus_eq_zero_iff_homeo`

This file packages challenge item 14 (`genus_eq_zero_iff_homeo` from
`JacobianChallenge/Basic.lean`) as a **tier-2 reduction**: the
biconditional
`JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ S²)` is split into two
named hypotheses and an assembly theorem, and a single bundle
`SurfaceClassificationGenus` records both hypotheses simultaneously.

## What is honestly proven here

* `genus_zero_iff_homeo_of_bridges` — given the two named-hypothesis
  reductions `Genus0ImpliesS2 X` and `S2ImpliesGenus0 X`, assembles the
  biconditional. **No `sorry`, no axiom.**

* `SurfaceClassificationGenus.toIff` — the same assembly, packaged as a
  method on the bundle.

* `genus_zero_iff_homeo_of_classification` — the bundle-level version,
  taking a `SurfaceClassificationGenus X` and returning the iff.

The two named hypothesis types `Genus0ImpliesS2` and `S2ImpliesGenus0`
are `Prop`-valued definitions (not theorems): they record exactly the
content that, at this mathlib pin, requires either uniformization /
Riemann mapping (forward) or Hodge identification of geometric and
topological genus (reverse).

## What is left as a `Prop`-only statement (open)

* `Genus0ImpliesS2 X : Prop` —
  `JacobianChallenge.genus X = 0 → Nonempty (X ≃ₜ S²)`. Classical proof:
  uniformization theorem + simply-connectedness of a closed Riemann
  surface with `H⁰(X, Ω¹) = 0`. **Not in mathlib at the v0.3 pin.**

* `S2ImpliesGenus0 X : Prop` —
  `Nonempty (X ≃ₜ S²) → JacobianChallenge.genus X = 0`. Classical proof:
  Hodge identification of geometric and topological genus, plus
  computation of `H¹(S²; ℚ) = 0` (`RiemannSphereGenus.lean` records the
  geometric side via Liouville). **The geometric-vs-topological-genus
  bridge is the missing input here; `H¹(S²; ℚ) = 0` itself is a separate
  upstream gap noted in `SurfaceGenus.lean`.**

## Why this is a tier-2 reduction, not a closed proof

Both directions require deep mathematics not present at the pinned
mathlib commit (`8e3c989...`, 15 April 2026):

1. **Uniformization theorem** for closed Riemann surfaces — needed for
   `Genus0ImpliesS2`. mathlib has Riemann-mapping-on-the-disk but not
   the uniformization-of-compact-surfaces statement.

2. **Hodge decomposition** identifying `dim_ℂ H⁰(X, Ω¹)` with
   `½ rank ℤ H¹(X; ℤ)` (or equivalently the topological-genus invariant
   from `JacobianChallenge.Topology.SurfaceGenus`). mathlib has neither
   the Hodge theorem nor the singular-homology computational tools
   (Mayer-Vietoris, excision, Hurewicz) that would let us compute
   `H¹(S²) = 0` from below.

3. **Closed-orientable-2-manifold classification** — needed indirectly
   to identify `X ≃ₜ S² ↔ topological genus 0`. Not in mathlib.

What this chip *does* close: the trivial assembly step. Given the two
mathematically-deep one-directional bridges as input, the iff statement
falls out by `Iff.intro`.
-/

universe u

namespace JacobianChallenge

open scoped Manifold ContDiff

/-- The standard 2-sphere as the unit sphere in `EuclideanSpace ℝ (Fin 3)`,
matching the statement of `genus_eq_zero_iff_homeo` in `Basic.lean`. -/
abbrev StandardS2 : Type :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-! ### Named hypothesis types -/

/-- **Open hypothesis (forward).** A compact connected Riemann surface
with vanishing geometric genus is homeomorphic to the standard 2-sphere.

Classical proof: uniformization theorem + simply-connectedness. Not
provable at the pinned mathlib commit. -/
def Genus0ImpliesS2 (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Prop :=
  JacobianChallenge.genus X = 0 → Nonempty (X ≃ₜ StandardS2)

/-- **Open hypothesis (reverse).** A compact connected Riemann surface
homeomorphic to the standard 2-sphere has vanishing geometric genus.

Classical proof: Hodge identification of geometric with topological
genus, combined with `H¹(S²; ℚ) = 0`. The geometric-vs-topological
bridge is not in mathlib at the pinned commit. -/
def S2ImpliesGenus0 (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Prop :=
  Nonempty (X ≃ₜ StandardS2) → JacobianChallenge.genus X = 0

/-! ### Bundle -/

/-- **Tier-2 bundle.** The classification input to `genus_eq_zero_iff_homeo`.

A `SurfaceClassificationGenus X` records both directions of the
biconditional as named hypotheses. The point of the bundle is to make
downstream callers depend on a single typeclass-free witness rather
than two independent assumptions. -/
structure SurfaceClassificationGenus (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Prop where
  /-- The forward direction: `genus = 0` implies `X ≃ₜ S²`. -/
  genus_zero_to_sphere : Genus0ImpliesS2 X
  /-- The reverse direction: `X ≃ₜ S²` implies `genus = 0`. -/
  sphere_to_genus_zero : S2ImpliesGenus0 X

/-! ### Honest assembly -/

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Honest assembly.** Given the two named-hypothesis reductions, the
biconditional `genus = 0 ↔ Nonempty (X ≃ₜ S²)` follows by `Iff.intro`.

This is the trivial half of challenge item 14: it shows the iff is
exactly the conjunction of the two implications, with no further
content. -/
theorem genus_zero_iff_homeo_of_bridges
    (h1 : Genus0ImpliesS2 X) (h2 : S2ImpliesGenus0 X) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) :=
  ⟨h1, h2⟩

/-- Method form of `genus_zero_iff_homeo_of_bridges`. -/
theorem SurfaceClassificationGenus.toIff
    (S : SurfaceClassificationGenus X) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) :=
  genus_zero_iff_homeo_of_bridges S.genus_zero_to_sphere S.sphere_to_genus_zero

/-- Bundle-level version of `genus_zero_iff_homeo_of_bridges`. -/
theorem genus_zero_iff_homeo_of_classification
    (S : SurfaceClassificationGenus X) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) :=
  S.toIff

/-! ### Sanity: the bundle is sufficient

Both directions are recoverable from the bundle alone, so any future
proof that produces a `SurfaceClassificationGenus` discharges the
biconditional via `genus_zero_iff_homeo_of_classification`. -/

theorem SurfaceClassificationGenus.mp
    (S : SurfaceClassificationGenus X) (h : JacobianChallenge.genus X = 0) :
    Nonempty (X ≃ₜ StandardS2) :=
  S.genus_zero_to_sphere h

theorem SurfaceClassificationGenus.mpr
    (S : SurfaceClassificationGenus X) (h : Nonempty (X ≃ₜ StandardS2)) :
    JacobianChallenge.genus X = 0 :=
  S.sphere_to_genus_zero h

end JacobianChallenge
