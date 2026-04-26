/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor
import JacobianChallenge.Manifold.MeromorphicAt
import JacobianChallenge.Manifold.MeromorphicDivisor

set_option diagnostics.threshold 100

/-! # The principal divisor map

This file builds the **principal divisor map** that sends a non-zero global
meromorphic function `f : X → ℂ` on a compact complex 1-manifold to its
order divisor `(f) := ∑_x ord_x(f) · [x]` in `Div X`. Concretely, it is a
genuine `Div X`-valued function on the type `MeromorphicNonzero X`, defined
by invoking `JacobianChallenge.MMeromorphicOn.divisor` (the chart-pullback
order divisor packaged in `Manifold/MeromorphicDivisor.lean`).

## The intended use

The set `range principalDivisorMap` is the future honest `PrincDiv X`
subgroup of `Div X` (currently `⊥` in `Divisor.lean`). The remaining
input — that the range is contained in `Div⁰ X`, equivalently the
residue theorem on a compact Riemann surface — is **not** in this file;
this file only builds the map.

## What's load-bearing

The `MeromorphicNonzero X` structure carries three fields:

* `toFun : X → ℂ`
* `meromorphic : MMeromorphicOn (𝓘(ℂ, ℂ)) toFun Set.univ`
* `nonvanishing_germ : ∀ x, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) toFun x ≠ ⊤`

The `nonvanishing_germ` field is the standard non-vanishing-germ hypothesis
("no point has identically-zero germ"). It is **load-bearing**: without it,
`MMeromorphicOn.divisor` cannot be applied (its third argument is exactly
this hypothesis, and the local-finiteness of the support fails for the
identically-zero function).

The constant-zero function does not give a `MeromorphicNonzero X` because
`mmeromorphicOrderAt 𝓘(ℂ,ℂ) 0 x = ⊤` everywhere (the germ is identically
zero). This is the correct semantic exclusion. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace JacobianChallenge

universe u

/-- A **non-vanishing-germ meromorphic function** on `X`: a function
`f : X → ℂ`, a proof that `f` is meromorphic on `Set.univ`, and a proof
that no germ of `f` is identically zero (`mmeromorphicOrderAt I f x ≠ ⊤`
everywhere).

The non-vanishing-germ field is the standard hypothesis under which the
order divisor is locally finite and `principalDivisorMap` is well-defined.
The model is hard-coded to `𝓘(ℂ, ℂ)` (the trivial complex model), matching
the rest of the manifold-meromorphic API in this repository. -/
structure MeromorphicNonzero (X : Type u)
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] where
  /-- The underlying function `X → ℂ`. -/
  toFun : X → ℂ
  /-- `toFun` is meromorphic on the whole manifold. -/
  meromorphic : MMeromorphicOn (𝓘(ℂ, ℂ)) toFun Set.univ
  /-- No point of `X` carries an identically-zero germ of `toFun`
  (equivalently, `toFun` is not the zero function in any chart neighborhood). -/
  nonvanishing_germ :
    ∀ x, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) toFun x ≠ ⊤

namespace MeromorphicNonzero

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- Coercion from `MeromorphicNonzero X` to the underlying function `X → ℂ`. -/
instance : CoeFun (MeromorphicNonzero X) (fun _ => X → ℂ) where
  coe f := f.toFun

end MeromorphicNonzero

/-- The **principal divisor map**: send a non-vanishing-germ meromorphic
function `f : MeromorphicNonzero X` to its order divisor `(f)` in `Div X`.

The body genuinely invokes `JacobianChallenge.MMeromorphicOn.divisor` from
`Manifold/MeromorphicDivisor.lean`; in particular all three fields of
`MeromorphicNonzero` are load-bearing inputs to that divisor construction. -/
noncomputable def principalDivisorMap
    {X : Type u}
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (f : MeromorphicNonzero X) : Div X :=
  JacobianChallenge.MMeromorphicOn.divisor (𝓘(ℂ, ℂ)) f.toFun
    f.meromorphic f.nonvanishing_germ

/-- The pointwise value of `principalDivisorMap f` at `x` is the integer
order `orderFun 𝓘(ℂ,ℂ) f.toFun x = (mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x).untop₀`.
This unfolds the divisor's `toFun` field and is the API-friendly form of the
underlying definition. -/
@[simp] lemma principalDivisorMap_apply
    {X : Type u}
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (f : MeromorphicNonzero X) (x : X) :
    (principalDivisorMap f : X → ℤ) x
      = JacobianChallenge.MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x := rfl

end JacobianChallenge
