/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import JacobianChallenge.Manifold.SmoothChain

/-! # Pairing of 0-chains with real-valued functions and the endpoint
identity for `SmoothChain.boundary`

`SmoothChain.lean` (ZZ132 / ZZ139) introduced

* the boundary operator `SmoothChain.boundary : SmoothChain I X →ₗ[ℤ] (X →₀ ℤ)`
  sending a path `γ` to `δ_{γ.target} - δ_{γ.source}`, and
* the basic linearity lemmas (`boundary_zero`, `boundary_add`, `boundary_neg`,
  `boundary_single`).

This file adds the missing **evaluation pairing** that lets the boundary
do work in path-integral computations: a `ℤ`-linear functional

    `eval : (X →₀ ℤ) →ₗ[ℤ] (X → ℝ) → ℝ`,         -- (formally curried)

i.e. for a real-valued function `f : X → ℝ` and a 0-chain `c = ∑ nᵢ δ_{xᵢ}`,
the pairing is `eval c f := ∑ nᵢ * f xᵢ`. Specialised to the boundary of a
single path this gives the **endpoint identity**

    `eval (∂γ) f = f γ.target - f γ.source`,

which is the right-hand side of the fundamental theorem of calculus that
the eventual Stokes-on-paths chip will match against
`SmoothPath.integrate (df) γ`.

We deliberately stay in the simpler signature `(X → ℝ)` (no smoothness)
because the endpoint identity is purely combinatorial — smoothness only
enters when we want to actually call `df` on a `SmoothOneForm`. The
current file has no manifold prerequisites beyond what `SmoothChain`
already imports.
-/

open scoped Manifold Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace SmoothChain

/-- Pair a 0-chain `c : X →₀ ℤ` with a real-valued function `f : X → ℝ`,
returning `∑_{x ∈ c.support} (c x : ℝ) * f x`. This is the canonical
ℝ-linear evaluation that turns the abstract boundary `∂c ∈ X →₀ ℤ` into
a concrete real number once a 0-form `f` is chosen. -/
def evalPoints (c : X →₀ ℤ) (f : X → ℝ) : ℝ :=
  c.support.sum (fun x => (c x : ℝ) * f x)

@[simp] lemma evalPoints_zero (f : X → ℝ) :
    evalPoints (0 : X →₀ ℤ) f = 0 := by
  unfold evalPoints
  simp

@[simp] lemma evalPoints_single (x : X) (n : ℤ) (f : X → ℝ) :
    evalPoints (Finsupp.single x n) f = (n : ℝ) * f x := by
  classical
  unfold evalPoints
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [Finsupp.support_single_ne_zero _ hn]
    simp

@[simp] lemma evalPoints_add (c₁ c₂ : X →₀ ℤ) (f : X → ℝ) :
    evalPoints (c₁ + c₂) f = evalPoints c₁ f + evalPoints c₂ f := by
  classical
  unfold evalPoints
  -- Reindex both sides on the union support and split.
  have e₀ : (c₁ + c₂).support.sum (fun x => (((c₁ + c₂) x) : ℝ) * f x) =
      (c₁.support ∪ c₂.support).sum
        (fun x => (((c₁ + c₂) x) : ℝ) * f x) := by
    apply Finset.sum_subset Finsupp.support_add
    intro x _ hx
    have h0 : (c₁ + c₂) x = 0 := Finsupp.notMem_support_iff.mp hx
    rw [h0]; push_cast; ring
  have e₁ : c₁.support.sum (fun x => ((c₁ x) : ℝ) * f x) =
      (c₁.support ∪ c₂.support).sum
        (fun x => ((c₁ x) : ℝ) * f x) := by
    apply Finset.sum_subset Finset.subset_union_left
    intro x _ hx
    have h0 : c₁ x = 0 := Finsupp.notMem_support_iff.mp hx
    rw [h0]; push_cast; ring
  have e₂ : c₂.support.sum (fun x => ((c₂ x) : ℝ) * f x) =
      (c₁.support ∪ c₂.support).sum
        (fun x => ((c₂ x) : ℝ) * f x) := by
    apply Finset.sum_subset Finset.subset_union_right
    intro x _ hx
    have h0 : c₂ x = 0 := Finsupp.notMem_support_iff.mp hx
    rw [h0]; push_cast; ring
  rw [e₀, e₁, e₂, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have hadd : (c₁ + c₂) x = c₁ x + c₂ x := Finsupp.add_apply _ _ _
  rw [hadd]; push_cast; ring

@[simp] lemma evalPoints_neg (c : X →₀ ℤ) (f : X → ℝ) :
    evalPoints (-c) f = - evalPoints c f := by
  classical
  unfold evalPoints
  -- The support of `-c` equals the support of `c`.
  have hsupp : (-c).support = c.support := by
    ext x
    simp [Finsupp.mem_support_iff, Finsupp.neg_apply]
  rw [hsupp, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have : (-c) x = -(c x) := Finsupp.neg_apply _ _
  rw [this]; push_cast; ring

@[simp] lemma evalPoints_sub (c₁ c₂ : X →₀ ℤ) (f : X → ℝ) :
    evalPoints (c₁ - c₂) f = evalPoints c₁ f - evalPoints c₂ f := by
  rw [sub_eq_add_neg, evalPoints_add, evalPoints_neg, sub_eq_add_neg]

/-- **Endpoint identity for the boundary of a single path.** Pairing
`∂γ = δ_{γ.target} - δ_{γ.source}` against a function `f : X → ℝ` returns
`f γ.target - f γ.source`, the right-hand side of the fundamental
theorem of calculus along `γ`. -/
@[simp] theorem evalPoints_boundarySingle (γ : SmoothPath I X) (f : X → ℝ) :
    evalPoints (boundarySingle γ) f = f γ.target - f γ.source := by
  unfold boundarySingle
  rw [evalPoints_sub, evalPoints_single, evalPoints_single]
  simp [SmoothPath.target, SmoothPath.source]

/-- Endpoint identity expressed at the level of `SmoothChain.boundary`
applied to a single-generator chain. -/
@[simp] theorem evalPoints_boundary_single (γ : SmoothPath I X) (f : X → ℝ) :
    evalPoints ((SmoothChain.single γ : SmoothChain I X).boundary) f
      = f γ.target - f γ.source := by
  rw [boundary_single, evalPoints_boundarySingle]

end SmoothChain

end
