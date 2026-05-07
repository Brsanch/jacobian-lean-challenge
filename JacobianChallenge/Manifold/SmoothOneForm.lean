/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Cotangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

/-! # Smooth real 1-forms on a finite-dimensional smooth manifold

This file introduces the real vector space `SmoothOneForm I X` of `C^∞`
global sections of the cotangent bundle of a real smooth manifold `X`
modelled on `(E, H)` with model with corners `I : ModelWithCorners ℝ E H`.

This is the foundational analytic type for the partition-of-unity-Stokes
infrastructure (R5 route). Subsequent chips will build pullbacks, chart
pullbacks, exterior derivative, integration over chains, etc. on top of
this object.

## Main definitions

* `SmoothOneForm I X` — the type of `C^∞` sections of the cotangent bundle
  of `X`, defined as a `ContMDiffSection` of the cotangent bundle with
  regularity `⊤` (which mathlib uses for `C^∞`).

## Instances

* `AddCommGroup (SmoothOneForm I X)` — pointwise addition.
* `Module ℝ (SmoothOneForm I X)` — pointwise scalar multiplication.

These instances are inherited from `ContMDiffSection`, which provides them
under the (already-discharged) hypotheses `[FiberBundle ...]` and
`[VectorBundle ℝ ...]` supplied by `JacobianChallenge.Manifold.Cotangent`.

## Coercion

* `SmoothOneForm.coeFun` — every smooth 1-form gives a function
  `(x : X) → CotangentSpace I x`. Inherited from `ContMDiffSection` via
  its `CoeFun` instance.

## Design notes

The shape mirrors `HolomorphicOneForm` exactly: we reuse `CotangentSpace`
from `JacobianChallenge.Manifold.Cotangent`, and `ContMDiffSection` from
mathlib's `Geometry.Manifold.VectorBundle.SmoothSection`.

The smoothness regularity is `⊤ : WithTop ℕ∞` (i.e. `C^∞`) rather than the
stronger `ω` (analytic) used for the holomorphic case. Pullbacks under
smooth maps and chart pullbacks (items 4 and 5 of the original chip
specification) are deferred to later chips: implementing them at this pin
requires building the mfderiv-based bundle map for the cotangent bundle,
which is non-trivial work that warrants its own chip.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

set_option diagnostics.threshold 100

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (X : Type*) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- A smooth real 1-form on a real smooth manifold `X` modelled on `(E, H)`
with model with corners `I` is a `C^∞` section of the cotangent bundle
of `X`.

The cotangent bundle (`CotangentSpace I`) is built in
`JacobianChallenge.Manifold.Cotangent`; here we wrap mathlib's
`ContMDiffSection` with regularity `⊤` (= `C^∞`) and the cotangent fibre
type `E →L[ℝ] ℝ`. -/
def SmoothOneForm : Type _ :=
  ContMDiffSection (𝕜 := ℝ) (E := E) (H := H) (M := X)
    I (E →L[ℝ] ℝ) ⊤ (CotangentSpace I : X → Type _)

namespace SmoothOneForm

/-- Smooth 1-forms form an additive commutative group under pointwise
addition. Inherited from `ContMDiffSection`. -/
instance instAddCommGroup : AddCommGroup (SmoothOneForm I X) :=
  inferInstanceAs <| AddCommGroup
    (ContMDiffSection (𝕜 := ℝ) (E := E) (H := H) (M := X)
      I (E →L[ℝ] ℝ) ⊤ (CotangentSpace I : X → Type _))

/-- Smooth 1-forms form a real vector space under pointwise scalar
multiplication. Inherited from `ContMDiffSection`. -/
instance instModule : Module ℝ (SmoothOneForm I X) :=
  inferInstanceAs <| Module ℝ
    (ContMDiffSection (𝕜 := ℝ) (E := E) (H := H) (M := X)
      I (E →L[ℝ] ℝ) ⊤ (CotangentSpace I : X → Type _))

/-- Coercion of a smooth 1-form to its underlying section, viewing it as
a function `(x : X) → CotangentSpace I x`. Inherited from the
`CoeFun` instance on `ContMDiffSection`. -/
instance instCoeFun : CoeFun (SmoothOneForm I X)
    (fun _ => ∀ x : X, CotangentSpace I x) :=
  inferInstanceAs <| CoeFun
    (ContMDiffSection (𝕜 := ℝ) (E := E) (H := H) (M := X)
      I (E →L[ℝ] ℝ) ⊤ (CotangentSpace I : X → Type _))
    (fun _ => ∀ x : X, CotangentSpace I x)

end SmoothOneForm

end
