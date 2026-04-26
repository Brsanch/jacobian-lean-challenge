/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Cotangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.Complex
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Holomorphic 1-forms and the genus of a compact Riemann surface

This file defines the complex vector space `HolomorphicOneForm X` of global
holomorphic 1-forms on a complex manifold `X` modelled on `ℂ`, and then the
*geometric genus* `genus X := Module.finrank ℂ (HolomorphicOneForm X)`.

For a compact connected Riemann surface, `genus X` agrees with the topological
genus; that identification is *not* proved here (it is challenge item 14).
This file only sets up the linear-algebraic object.

## Main definitions

* `HolomorphicOneForm X` — the complex vector space of `Cᵒ`-smooth global
  sections of the cotangent bundle of `X`, where `Cᵒ` is the analytic
  regularity `ω` (so smoothness here means *holomorphic*, in line with the
  way mathlib treats complex analyticity as `C^ω`-smoothness).
* `genus X` — the `ℕ`-valued dimension of `HolomorphicOneForm X` over `ℂ`.

## Design notes

The natural mathlib definition of a smooth section of a vector bundle is
`ContMDiffSection`. At the mathlib pin used by this project
(`8e3c989104daaa052921bf43de9eef0e1ac9fbf5`, 15 Apr 2026), the file
`Mathlib/Geometry/Manifold/VectorBundle/SmoothSection.lean` defines

```
structure ContMDiffSection
    (I : ModelWithCorners 𝕜 E H) (F : Type*) (n : WithTop ℕ∞)
    (V : M → Type*)
    [TopologicalSpace (TotalSpace F V)] [∀ x : M, TopologicalSpace (V x)]
    [FiberBundle F V] : Type _
```

and provides `AddCommGroup` and `Module 𝕜` instances *under just*
`[VectorBundle 𝕜 F V]` (no `ContMDiffVectorBundle` typeclass is required at
this pin). The sister file `Cotangent.lean` already supplies
`FiberBundle` and `VectorBundle` instances for the cotangent bundle (it does
not yet supply a `ContMDiffVectorBundle` instance, but we do not need one).

Since `Cotangent.lean`'s instances are stated under `[IsManifold I 1 M]`, and
mathlib's `IsManifold` API gives an automatic instance
`[IsManifold I ω M] → [IsManifold I a M]` for any regularity `a`, the `ω`
hypothesis on `X` discharges that prerequisite automatically.

The genus is defined via `Module.finrank`, which returns `0` when the
underlying space is infinite-dimensional. For a *compact* Riemann surface the
space `HolomorphicOneForm X` is in fact finite-dimensional; that
finite-dimensionality (and hence the agreement with the topological genus) is
a separate theorem and is not asserted here.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

set_option diagnostics.threshold 100

variable (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- A holomorphic 1-form on the complex manifold `X` is a `C^ω` section of
the cotangent bundle of `X`.

Mathlib treats complex analyticity as `C^ω`-smoothness in its manifold API,
so a `ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω _` of the cotangent bundle is
exactly a holomorphic global 1-form. -/
def HolomorphicOneForm : Type _ :=
  ContMDiffSection (𝕜 := ℂ) (E := ℂ) (H := ℂ) (M := X)
    𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω (CotangentSpace 𝓘(ℂ) : X → Type _)

namespace HolomorphicOneForm

/-- Holomorphic 1-forms form an additive commutative group under pointwise
addition. Inherited from `ContMDiffSection`. -/
instance instAddCommGroup : AddCommGroup (HolomorphicOneForm X) :=
  inferInstanceAs <| AddCommGroup
    (ContMDiffSection (𝕜 := ℂ) (E := ℂ) (H := ℂ) (M := X)
      𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω (CotangentSpace 𝓘(ℂ) : X → Type _))

/-- Holomorphic 1-forms form a complex vector space under pointwise scalar
multiplication. Inherited from `ContMDiffSection`. -/
instance instModule : Module ℂ (HolomorphicOneForm X) :=
  inferInstanceAs <| Module ℂ
    (ContMDiffSection (𝕜 := ℂ) (E := ℂ) (H := ℂ) (M := X)
      𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω (CotangentSpace 𝓘(ℂ) : X → Type _))

end HolomorphicOneForm

/-- The (geometric) genus of a complex manifold `X` modelled on `ℂ`, defined
as the complex dimension of the space of global holomorphic 1-forms.

For a compact connected Riemann surface this agrees with the topological
genus (challenge item 14, not proved here). For a non-compact or
infinite-dimensional `H⁰(X, Ω¹)` situation, `Module.finrank` returns `0` by
convention.

Lives in the `JacobianChallenge` namespace so it does not collide with the
verbatim challenge `def _root_.genus ... := sorry` in `Basic.lean`; that
top-level `genus` will eventually be filled in as `JacobianChallenge.genus
X`, modulo lining up the (slightly different) typeclass hypotheses. -/
def JacobianChallenge.genus : ℕ :=
  Module.finrank ℂ (HolomorphicOneForm X)

end
