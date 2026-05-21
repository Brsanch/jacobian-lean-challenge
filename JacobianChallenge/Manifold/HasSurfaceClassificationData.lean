/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SurfaceClassificationData
import JacobianChallenge.Manifold.SurfaceClassificationDataComplexTorus

set_option linter.unusedSectionVars false

/-! # `HasSurfaceClassificationData X` — typeclass wrapper

A Prop typeclass on `X` asserting `Nonempty (SurfaceClassificationData X)`.
Mirrors the shape of `HasJacobianAnalyticStructure X` — once instances
on `RS` and `T_L = ℂ ⧸ L` fire, downstream `[HasSurfaceClassificationData
X]`-parametric constructions automatically dispatch.

The two unconditional instances:

* `instHasSurfaceClassificationData_RiemannSphere` — chip 1.
* `instHasSurfaceClassificationData_complexTorus` — chip 2.

For general genus, `HasSurfaceClassificationData X` is the named
classical hypothesis "X is a compact connected oriented topological
2-manifold of genus g for which the smooth-symplectic-basis +
smooth-Hurewicz data exist" — i.e., topological surface classification
+ smooth-Hurewicz. It is not unconditional in tree at general genus;
the canonical-form discharge is what chip 1 named.

## What this file ships

* `HasSurfaceClassificationData X` — class.
* `instHasSurfaceClassificationData_RiemannSphere` — instance.
* `instHasSurfaceClassificationData_complexTorus L` — instance.
* `canonicalSurfaceClassificationData X` — `Classical.choice` extractor.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasSurfaceClassificationData X`** — Prop typeclass asserting
`Nonempty (SurfaceClassificationData X)`. -/
class HasSurfaceClassificationData (X : Type u) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X] : Prop where
  /-- The witness. -/
  out : Nonempty (SurfaceClassificationData X)

/-- **Canonical extractor.** `Classical.choice`'d once; downstream
constructions reference this exact witness. -/
noncomputable def canonicalSurfaceClassificationData
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    [HasSurfaceClassificationData X] : SurfaceClassificationData X :=
  Classical.choice HasSurfaceClassificationData.out

/-! ## Instance: `RiemannSphere` -/

namespace RiemannSphere

/-- **Unconditional instance on `RiemannSphere`.** -/
instance instHasSurfaceClassificationData_RiemannSphere :
    HasSurfaceClassificationData RiemannSphere where
  out := nonempty_surfaceClassificationData_RiemannSphere

end RiemannSphere

/-! ## Instance: `T_L = ℂ ⧸ L` -/

namespace ComplexTorus

variable (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- **Unconditional instance on the complex torus `T_L`.** -/
instance instHasSurfaceClassificationData_complexTorus :
    HasSurfaceClassificationData (ℂ ⧸ L) where
  out := nonempty_surfaceClassificationData_complexTorus L

end ComplexTorus

end JacobianChallenge

end
