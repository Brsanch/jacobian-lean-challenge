/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Compactness.Compact

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Disjoint open neighbourhoods of finite fibre points (obligation B)

For a finite set `S` in a `T2` space, there exist pairwise-disjoint open
neighbourhoods of each point. This is a direct application of mathlib's
`Set.Finite.t2_separation`. We package it in the form consumed by the
Riemann-Hurwitz total-weight proof.

Plus a stronger variant: refining the disjoint open nbhds to lie inside
prescribed open `V_x`-shrinks (e.g., chart balls of bounded radius). -/

@[expose] public section

open Set Filter Topology

namespace JacobianChallenge

namespace Manifold

universe u

/-- **Disjoint open neighbourhoods of finite set in T2.** Mathlib's
`Set.Finite.t2_separation` packaged in the per-point shape we consume. -/
theorem exists_disjoint_open_nbhds_of_finite
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {S : Set X} (hS : S.Finite) :
    ∃ U : X → Set X, (∀ x ∈ S, x ∈ U x ∧ IsOpen (U x)) ∧
      S.PairwiseDisjoint U := by
  -- Mathlib gives U on all of X; restrict the conclusions to S.
  obtain ⟨U, hU_mem_open, hU_disjoint⟩ := hS.t2_separation
  refine ⟨U, ?_, hU_disjoint⟩
  intro x _
  exact hU_mem_open x

/-- **Refined disjoint open nbhds: shrunk to lie inside given opens.**
For finite `S` in T2, plus a prescribed family of open neighbourhoods
`V x ∋ x` for each `x ∈ S`, there exist pairwise-disjoint open
neighbourhoods `W x ⊆ V x` of each `x ∈ S`. -/
theorem exists_disjoint_open_nbhds_in_of_finite
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {S : Set X} (hS : S.Finite)
    (V : X → Set X) (hV_open : ∀ x ∈ S, IsOpen (V x))
    (hV_mem : ∀ x ∈ S, x ∈ V x) :
    ∃ W : X → Set X,
      (∀ x ∈ S, x ∈ W x ∧ IsOpen (W x) ∧ W x ⊆ V x) ∧
      S.PairwiseDisjoint W := by
  -- Get raw disjoint U, then intersect with V.
  obtain ⟨U, hU_mem_open, hU_disjoint⟩ := exists_disjoint_open_nbhds_of_finite hS
  refine ⟨fun x => U x ∩ V x, ?_, ?_⟩
  · intro x hxS
    obtain ⟨hxU, hUopen⟩ := hU_mem_open x hxS
    refine ⟨⟨hxU, hV_mem x hxS⟩, hUopen.inter (hV_open x hxS), ?_⟩
    intro z hz
    exact hz.2
  · -- S.PairwiseDisjoint (fun x => U x ∩ V x). Inherits from U-disjointness.
    intro x hxS y hyS hne
    have h := hU_disjoint hxS hyS hne
    -- h : Disjoint (U x) (U y). Intersection with V is still disjoint.
    rw [Function.onFun, disjoint_iff_inter_eq_empty] at *
    rw [show (U x ∩ V x) ∩ (U y ∩ V y) = (U x ∩ U y) ∩ (V x ∩ V y) by
        ext z; simp; tauto, h, Set.empty_inter]

/-- **Compactness preimage-cover.** For `X` compact, `f : X → Y` continuous,
finite set `F ⊆ X` lying inside open `U ⊆ X`, with `f` mapping all of `F`
to a single point `y₀ ∈ Y` and `f`'s image of `X \ U` not containing `y₀`,
there exists an open neighbourhood `W` of `y₀` such that
`f ⁻¹' W ⊆ U`.

Proof: `X \ U` is closed in compact `X`, hence compact; `f(X \ U)` is
compact in `Y`, hence closed (in T2 `Y`); `y₀ ∉ f(X \ U)`, so by openness
of the complement of `f(X \ U)` we get an open `W ∋ y₀` disjoint from
`f(X \ U)`. Any preimage of `W` lies outside `X \ U`, i.e. inside `U`. -/
theorem exists_open_nbhd_preimage_in_of_compact
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) {U : Set X} (hU_open : IsOpen U)
    {y₀ : Y} (h_disj : ∀ x ∈ (Uᶜ : Set X), f x ≠ y₀) :
    ∃ W : Set Y, IsOpen W ∧ y₀ ∈ W ∧ f ⁻¹' W ⊆ U := by
  -- `Uᶜ` is closed and X is compact, so `Uᶜ` is compact.
  have hUc_compact : IsCompact (Uᶜ : Set X) :=
    (hU_open.isClosed_compl).isCompact
  -- `f(Uᶜ)` is compact in `Y`.
  have h_image_compact : IsCompact (f '' (Uᶜ : Set X)) :=
    hUc_compact.image hf
  -- In T2 `Y`, compact sets are closed.
  have h_image_closed : IsClosed (f '' (Uᶜ : Set X)) :=
    h_image_compact.isClosed
  -- `y₀ ∉ f(Uᶜ)`.
  have hy₀_not_image : y₀ ∉ f '' (Uᶜ : Set X) := by
    intro hy
    obtain ⟨x, hx_compl, hxy⟩ := hy
    exact h_disj x hx_compl hxy
  -- The complement of `f(Uᶜ)` is open and contains `y₀`.
  have h_open_compl : IsOpen ((f '' (Uᶜ : Set X))ᶜ : Set Y) :=
    h_image_closed.isOpen_compl
  refine ⟨(f '' (Uᶜ : Set X))ᶜ, h_open_compl, hy₀_not_image, ?_⟩
  -- For x with f x ∉ f(Uᶜ): in particular f x ≠ f x' for any x' ∈ Uᶜ;
  -- equivalently x ∉ Uᶜ, i.e. x ∈ U.
  intro x hxW
  -- hxW : f x ∈ (f '' Uᶜ)ᶜ, i.e. f x ∉ f '' Uᶜ.
  by_contra hxU
  -- hxU : x ∉ U, i.e. x ∈ Uᶜ.
  apply hxW
  exact ⟨x, hxU, rfl⟩

end Manifold

end JacobianChallenge
