/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Complex.Basic

/-! # Finite chart-source cover of a compact charted space

For any compact `ChartedSpace ℂ X`, the collection
`{(chartAt ℂ y).source : y : X}` is an open cover of `X` (since
`y ∈ (chartAt ℂ y).source` for every `y`). By compactness it admits
a **finite subcover**.

This is the first sub-chip of the partition-of-unity assembly arc
that lifts `chartLocalL2Sq` to a global L²-square norm: we need a
finite atlas to even define the partition of unity (mathlib's
`SmoothPartitionOfUnity.exists_isSubordinate` takes a cover indexed
by a finset / fintype).

Headline:

```
theorem exists_finite_chartAt_source_cover :
    ∃ s : Finset X, ⋃ y ∈ s, (chartAt ℂ y).source = (Set.univ : Set X)
```

No `sorry`, no `axiom`. -/

open scoped Manifold ContDiff Topology

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X] [CompactSpace X]

/-- **Finite chart-source cover.** Every compact charted space modelled
on `ℂ` admits a finite cover by chart sources. -/
theorem exists_finite_chartAt_source_cover :
    ∃ s : Finset X, ⋃ y ∈ s, (chartAt ℂ y).source = (Set.univ : Set X) := by
  -- The collection {(chartAt ℂ y).source : y : X} is an open cover of univ:
  -- every x is in (chartAt ℂ x).source.
  have h_cover : (Set.univ : Set X) ⊆ ⋃ y : X, (chartAt ℂ y).source := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, mem_chart_source ℂ x⟩
  have h_open : ∀ y : X, IsOpen ((chartAt ℂ y).source) :=
    fun y => (chartAt ℂ y).open_source
  -- Apply IsCompact.elim_finite_subcover on isCompact_univ.
  obtain ⟨s, hs⟩ :=
    isCompact_univ.elim_finite_subcover (fun y : X => (chartAt ℂ y).source)
      h_open h_cover
  refine ⟨s, ?_⟩
  -- hs : univ ⊆ ⋃ y ∈ s, (chartAt ℂ y).source. We need set equality.
  apply Set.eq_univ_of_univ_subset hs

end JacobianChallenge
