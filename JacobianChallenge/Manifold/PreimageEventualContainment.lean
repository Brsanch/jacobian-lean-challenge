/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousOn

/-! # Preimage eventual containment in fibre neighbourhoods

This file proves a pure-topology lemma needed as **step 3** of the
Riemann-Hurwitz total-weight identity (`rsum`, see
`JacobianChallenge/Manifold/RamificationSumEqualsDegree.lean`):

> Let `f : X → Y` be continuous, `X` compact, `Y` Hausdorff, `y : Y`,
> `F = f ⁻¹' {y}` finite, and let each `x ∈ F` be equipped with an open
> neighbourhood `U x ∋ x`. Then there exists an open neighbourhood `V`
> of `y` such that `f ⁻¹' V ⊆ ⋃ x ∈ F, U x`.

Proof sketch. Let `K := X \ ⋃ x ∈ F, U x`. Since `K` is the
complement of a finite union of opens, `K` is closed; closed subsets of
a compact space are compact, so `K` is compact. Its image `f '' K` is
compact in `Y` (continuous image of a compact set), and because `Y` is
T2, `f '' K` is closed. Now `y ∉ f '' K`: if `y = f z` for some
`z ∈ K` then `z ∈ F` so `z ∈ U z ⊆ ⋃ x ∈ F, U x`, contradicting
`z ∈ K`. Therefore `V := (f '' K)ᶜ` is open, contains `y`, and any
`x ∈ f ⁻¹' V` has `f x ∉ f '' K`, so `x ∉ K`, i.e.
`x ∈ ⋃ x' ∈ F, U x'`.

No `sorry`, no `axiom`. -/

@[expose] public section

namespace JacobianChallenge

namespace PreimageEventualContainment

universe u v

/-- **Preimage eventual containment.**

For a continuous map `f : X → Y` from a compact space to a Hausdorff
space, if the fibre `f ⁻¹' {y}` is finite and each of its points is
equipped with an open neighbourhood, then a small enough open
neighbourhood `V` of `y` has its preimage entirely contained in the
union of those fibre-point neighbourhoods. -/
theorem preimage_eventually_in_fibre_neighbourhoods
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f)
    (y : Y) (hF : (f ⁻¹' {y}).Finite)
    (U : X → Set X)
    (hU_open : ∀ x ∈ f ⁻¹' {y}, IsOpen (U x))
    (hU_mem : ∀ x ∈ f ⁻¹' {y}, x ∈ U x) :
    ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧
      f ⁻¹' V ⊆ ⋃ x ∈ hF.toFinset, U x := by
  -- The "good" union of fibre-point neighbourhoods.
  set G : Set X := ⋃ x ∈ hF.toFinset, U x with hG_def
  -- `G` is open: it is a finite union of opens.
  have hG_open : IsOpen G := by
    refine isOpen_biUnion ?_
    intro x hx
    have hx' : x ∈ f ⁻¹' {y} := by
      simpa [Set.Finite.mem_toFinset] using hx
    exact hU_open x hx'
  -- The bad set `K = Gᶜ` is closed, hence compact in `X`.
  set K : Set X := Gᶜ with hK_def
  have hK_closed : IsClosed K := hG_open.isClosed_compl
  have hK_compact : IsCompact K := hK_closed.isCompact
  -- Its image is compact, hence closed in T2 `Y`.
  have hfK_compact : IsCompact (f '' K) := hK_compact.image hf
  have hfK_closed : IsClosed (f '' K) := hfK_compact.isClosed
  -- `y` is not in `f '' K`.
  have hy_not_image : y ∉ f '' K := by
    rintro ⟨z, hzK, hzy⟩
    -- `z ∈ f ⁻¹' {y}` so `z ∈ U z ⊆ G`, contradicting `z ∈ K = Gᶜ`.
    have hzF : z ∈ f ⁻¹' {y} := by
      simpa [Set.mem_preimage, Set.mem_singleton_iff] using hzy
    have hzU : z ∈ U z := hU_mem z hzF
    have hzG : z ∈ G := by
      refine Set.mem_biUnion ?_ hzU
      simpa [Set.Finite.mem_toFinset] using hzF
    exact hzK hzG
  -- Take `V := (f '' K)ᶜ`.
  refine ⟨(f '' K)ᶜ, hfK_closed.isOpen_compl, hy_not_image, ?_⟩
  intro x hxV
  -- `f x ∉ f '' K`, so `x ∉ K`, so `x ∈ G`.
  have hfx : f x ∉ f '' K := hxV
  have hxK : x ∉ K := by
    intro hxK
    exact hfx ⟨x, hxK, rfl⟩
  -- `x ∉ K = Gᶜ` means `x ∈ G`.
  have hxG : x ∈ G := by
    by_contra hxG'
    exact hxK hxG'
  exact hxG

end PreimageEventualContainment

end JacobianChallenge
