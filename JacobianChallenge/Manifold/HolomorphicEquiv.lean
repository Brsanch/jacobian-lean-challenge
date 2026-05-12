/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.Complex

set_option diagnostics.threshold 100

/-! # `HolomorphicEquiv X Y`: a biholomorphism between complex 1-manifolds

This file packages mathlib's `Diffeomorph 𝓘(ℂ) 𝓘(ℂ) X Y ω` (an
`ω`-regularity smooth diffeomorphism between complex manifolds modelled
on `ℂ`) under the name `HolomorphicEquiv`, with a small structural API.

## Background

In mathlib (at the pin `8e3c989...`):

* `Diffeomorph I I' M M' n` is a structure extending `M ≃ M'` with
  `protected contMDiff_toFun : ContMDiff I I' n toEquiv` and
  `protected contMDiff_invFun : ContMDiff I' I n toEquiv.symm`.
* At regularity `n = ω` (analytic) and base model `𝓘(ℂ)` on both sides,
  this is exactly a **biholomorphism** between complex 1-manifolds: a
  bijection that is analytic in both directions.
* `Diffeomorph.refl`, `Diffeomorph.symm`, `Diffeomorph.trans` give the
  groupoid structure.
* `Diffeomorph.toHomeomorph` extracts the underlying `M ≃ₜ N`.

## What this file adds

* `HolomorphicEquiv X Y` — alias for `Diffeomorph 𝓘(ℂ) 𝓘(ℂ) X Y ω`.
* `HolomorphicEquiv.refl`, `.symm`, `.trans` — re-exports.
* `HolomorphicEquiv.toHomeomorph` — re-export of `Diffeomorph.toHomeomorph`.
* `HolomorphicEquiv.nonempty_homeomorph` — a `HolomorphicEquiv X Y`
  implies `Nonempty (X ≃ₜ Y)`, which is the form used by the
  uniformization-flavored hypotheses in the challenge.

No new mathematical content — pure API packaging. The downstream
benefit is uniform naming: every chip that wants a "biholomorphism
between complex 1-manifolds" can write `HolomorphicEquiv X Y` instead
of `Diffeomorph 𝓘(ℂ) 𝓘(ℂ) X Y ω`, which is less typo-prone and reads
closer to the math.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

namespace JacobianChallenge

variable (X Y Z : Type*)
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [TopologicalSpace Z] [ChartedSpace ℂ Z]

/-- A **biholomorphism** between complex 1-manifolds `X` and `Y`: a
bijection `X ≃ Y` that is analytic (`ω`-smooth) in both directions
with respect to the base model `𝓘(ℂ)`. -/
abbrev HolomorphicEquiv : Type _ :=
  Diffeomorph (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) X Y ω

namespace HolomorphicEquiv

variable {X Y Z}

/-- The identity biholomorphism. -/
protected noncomputable def refl : HolomorphicEquiv X X :=
  Diffeomorph.refl 𝓘(ℂ, ℂ) X ω

/-- The inverse biholomorphism. -/
protected noncomputable def symm (e : HolomorphicEquiv X Y) :
    HolomorphicEquiv Y X :=
  Diffeomorph.symm e

/-- The composition of two biholomorphisms. -/
protected noncomputable def trans
    (e₁ : HolomorphicEquiv X Y) (e₂ : HolomorphicEquiv Y Z) :
    HolomorphicEquiv X Z :=
  Diffeomorph.trans e₁ e₂

/-- A biholomorphism gives a homeomorphism on the underlying types. -/
noncomputable def toHomeomorph (e : HolomorphicEquiv X Y) : X ≃ₜ Y :=
  Diffeomorph.toHomeomorph e

/-- A biholomorphism witnesses that the two manifolds are homeomorphic
(in the `Nonempty (X ≃ₜ Y)` form used by the uniformization-flavored
hypotheses in this repo). -/
theorem nonempty_homeomorph_of_holomorphicEquiv
    (e : HolomorphicEquiv X Y) : Nonempty (X ≃ₜ Y) :=
  ⟨e.toHomeomorph⟩

/-- A `HolomorphicEquiv` is `ContMDiff` (analytic) on the forward
direction. -/
theorem contMDiff_forward (e : HolomorphicEquiv X Y) :
    ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (e.toEquiv : X → Y) :=
  e.contMDiff_toFun

/-- A `HolomorphicEquiv` is `ContMDiff` (analytic) on the inverse
direction. -/
theorem contMDiff_inverse (e : HolomorphicEquiv X Y) :
    ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (e.toEquiv.symm : Y → X) :=
  e.contMDiff_invFun

end HolomorphicEquiv

/-! ### Nonempty wrapper

The uniformization-flavored hypotheses in
`Topology/Genus0ImpliesS2Reduction.lean` use `Nonempty (X ≃ₜ
RiemannSphere)`. The analytically-correct strengthening is `Nonempty
(HolomorphicEquiv X RiemannSphere)` (or directly the
`HolomorphicEquiv` itself for non-`Prop` contexts). We expose the
relationship. -/

/-- **`Prop`-valued statement.** `X` is biholomorphic to `Y` (as
complex 1-manifolds modelled on `ℂ`). -/
def NonemptyHolomorphicEquiv (X Y : Type*)
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] : Prop :=
  Nonempty (HolomorphicEquiv X Y)

/-- A `NonemptyHolomorphicEquiv X Y` implies `Nonempty (X ≃ₜ Y)`
(the uniformization-flavored form). -/
theorem nonempty_homeo_of_nonemptyHolomorphicEquiv
    {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (h : NonemptyHolomorphicEquiv X Y) : Nonempty (X ≃ₜ Y) := by
  obtain ⟨e⟩ := h
  exact e.nonempty_homeomorph_of_holomorphicEquiv

/-- Reflexivity of the biholomorphism relation. -/
theorem nonemptyHolomorphicEquiv_refl (X : Type*)
    [TopologicalSpace X] [ChartedSpace ℂ X] :
    NonemptyHolomorphicEquiv X X :=
  ⟨HolomorphicEquiv.refl⟩

/-- Symmetry of the biholomorphism relation. -/
theorem nonemptyHolomorphicEquiv_symm {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (h : NonemptyHolomorphicEquiv X Y) :
    NonemptyHolomorphicEquiv Y X := by
  obtain ⟨e⟩ := h
  exact ⟨e.symm⟩

/-- Transitivity of the biholomorphism relation. -/
theorem nonemptyHolomorphicEquiv_trans {X Y Z : Type*}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [TopologicalSpace Z] [ChartedSpace ℂ Z]
    (h₁ : NonemptyHolomorphicEquiv X Y)
    (h₂ : NonemptyHolomorphicEquiv Y Z) :
    NonemptyHolomorphicEquiv X Z := by
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  exact ⟨e₁.trans e₂⟩

end JacobianChallenge
