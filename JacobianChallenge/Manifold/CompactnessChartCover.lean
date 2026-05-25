/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Complex.Basic

/-! # Chip 5.1 — finite chart cover from compactness

Given a compact charted space `X` on `ℂ`, this file bundles the
classical finite-subcover of chart sources into a single reusable
structure `FiniteChartCover X`.

The construction is the standard one: chart sources are open,
`mem_chart_source` says every `y : X` lies in `(chartAt ℂ y).source`,
hence `{(chartAt ℂ x).source | x : X}` is an open cover of `X`. On a
compact space, `IsCompact.elim_finite_subcover` extracts a finite
subset of base points whose chart sources still cover `X`.

This is the entry-point data for the genus-0 globalization argument
(Chip 5): downstream sub-chips will

* subordinate a partition of unity to the chart cover
  (Sub-chip 5.2),
* form chart-local Pompeiu solutions on each chart source
  (Sub-chip 5.3),
* multiply by cutoffs and assemble (Sub-chip 5.4-5.6).

A leaner sibling of `JacobianChallenge.DiskChartCover` (defined in
`Manifold/CompactDiskChartCover.lean`): no radii, no closed-disk
containment — just the bare covering property that the partition of
unity needs.

## Main definitions

* `JacobianChallenge.FiniteChartCover X` — `Finset` of base points
  whose chart sources cover `X`.

## Main results

* `JacobianChallenge.FiniteChartCover.exists_of_compact` — every
  compact charted space on `ℂ` admits a finite chart cover.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology
open Set

noncomputable section

namespace JacobianChallenge

/-- A *finite chart cover* of a charted space `X` over `ℂ`: a finite
set of base points whose chart sources cover `X`. -/
structure FiniteChartCover (X : Type*) [TopologicalSpace X]
    [ChartedSpace ℂ X] where
  /-- The (finite) collection of base points. -/
  basePoints : Finset X
  /-- Every point of `X` lies in the chart source of some base point. -/
  covers : ∀ y : X, ∃ x ∈ basePoints, y ∈ (chartAt ℂ x).source

namespace FiniteChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The union of the chart sources over a finite chart cover equals
the whole space `X`. Restatement of the `covers` field as a set-level
equality, convenient for rewriting. -/
theorem iUnion_source_eq_univ (cover : FiniteChartCover X) :
    (⋃ x ∈ cover.basePoints, (chartAt ℂ x).source) = (Set.univ : Set X) := by
  refine Set.eq_univ_iff_forall.mpr fun y => ?_
  obtain ⟨x, hxS, hxy⟩ := cover.covers y
  exact Set.mem_biUnion hxS hxy

/-- The base point set is nonempty whenever `X` is nonempty: the
cover covers every point, so at least one base point exists. -/
theorem basePoints_nonempty (cover : FiniteChartCover X) [Nonempty X] :
    cover.basePoints.Nonempty := by
  obtain ⟨y⟩ := ‹Nonempty X›
  obtain ⟨x, hx, _⟩ := cover.covers y
  exact ⟨x, hx⟩

end FiniteChartCover

/-! ## Existence on compact charted spaces -/

section Existence

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Existence of a finite chart cover on a compact charted space on
`ℂ`.** No nonemptiness assumption: an empty `X` admits the empty
cover trivially. -/
theorem FiniteChartCover.exists_of_compact [CompactSpace X] :
    Nonempty (FiniteChartCover X) := by
  -- Chart sources are open and cover `X`.
  have h_open : ∀ x : X, IsOpen ((chartAt ℂ x).source) :=
    fun x => (chartAt ℂ x).open_source
  have h_cover : (Set.univ : Set X) ⊆ ⋃ x : X, (chartAt ℂ x).source := by
    intro y _
    exact Set.mem_iUnion.mpr ⟨y, mem_chart_source ℂ y⟩
  -- Extract a finite subcover.
  have h_compact : IsCompact (Set.univ : Set X) := CompactSpace.isCompact_univ
  obtain ⟨S, hS⟩ := h_compact.elim_finite_subcover
    (fun x : X => (chartAt ℂ x).source) h_open h_cover
  -- Package as a `FiniteChartCover`.
  refine ⟨⟨S, ?_⟩⟩
  intro y
  obtain ⟨x, hxS, hxy⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ y))
  exact ⟨x, hxS, hxy⟩

end Existence

end JacobianChallenge

end
