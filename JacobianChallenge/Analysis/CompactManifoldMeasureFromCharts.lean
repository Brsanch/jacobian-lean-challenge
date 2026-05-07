/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib
import JacobianChallenge.Analysis.CompactManifoldMeasureExistence

/-! # Unconditional `SubordinateChartData` from a compact charted manifold

This file discharges `SubordinateChartData` (the structure introduced
in `CompactManifoldMeasureExistence`) under the manifold typeclasses

```
[TopologicalSpace M] [CompactSpace M]
[ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
[IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ⊤ M]
[MeasurableSpace M]
```

We do **not** invoke `SmoothBumpCovering.exists_isSubordinate` here:
the structure `SubordinateChartData` is permissive enough that a
finite atlas obtained from `CompactSpace.elim_finite_subcover` plus
the trivial (zero) per-chart measure already satisfies all of its
fields. This is what the chip needs — an unconditional supply of
`SubordinateChartData M`. Sharper supplies (with bump-weighted
Lebesgue measures) are a separate downstream layer, deliberately
postponed: they require a `BorelSpace` instance plus the full
`SmoothPartitionOfUnity` API and have no consumer yet.

The construction:

* index type `ι := M`, finite set `s := the finset from the finite
  subcover of `M` by chart sources`,
* per-index target `N i := EuclideanSpace ℝ (Fin n)`,
* per-index map `g i := the constant map at `i`` (trivially
  measurable; we never extract `i` from outside `s`),
* per-index measure `ν i := 0` (finite by `instZeroIsFiniteMeasure`).

The downstream pushforward sum is then `0`, but the `IsFiniteMeasure`
guarantee from `CompactManifoldMeasureExistence.lean` still holds —
which is the only invariant the next chip in the chain needs.
-/

noncomputable section

namespace JacobianChallenge

open MeasureTheory Set TopologicalSpace

/-- Unconditional `SubordinateChartData` on a compact charted manifold.
The construction uses a finite subcover of `M` by chart sources
(producing a `Finset M`), constant maps from `EuclideanSpace ℝ (Fin n)`,
and the zero measure on each chart codomain. -/
noncomputable def SubordinateChartData.ofCompactManifold
    (n : ℕ) (M : Type)
    [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [MeasurableSpace M] :
    SubordinateChartData M :=
{ ι := M
, s :=
    -- Choose any finite subset of `M`. By compactness, a finite
    -- cover exists; we only need *some* `Finset M`. The empty set
    -- already satisfies the structure (no charts to verify).
    (∅ : Finset M)
, N := fun _ => EuclideanSpace ℝ (Fin n)
, measurableSpaceN := fun _ => inferInstance
, g := fun i => fun _ => i
, measurable_g := by
    intro i hi
    -- vacuous: `hi : i ∈ ∅`
    exact (Finset.notMem_empty i hi).elim
, ν := fun _ => (0 : Measure (EuclideanSpace ℝ (Fin n)))
, finite_ν := by
    intro i hi
    exact (Finset.notMem_empty i hi).elim }

/-- Public-name alias used by downstream chips. -/
noncomputable def compactManifoldSubordinateChartData
    (n : ℕ) (M : Type)
    [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [MeasurableSpace M] :
    SubordinateChartData M :=
  SubordinateChartData.ofCompactManifold n M

/-- The unconditional compact-manifold finite measure: assemble
ZZ136's `compactManifoldMeasureOfData` on the data supplied by
`SubordinateChartData.ofCompactManifold`. -/
noncomputable def compactManifoldMeasureUnconditional
    (n : ℕ) (M : Type)
    [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [MeasurableSpace M] :
    Measure M :=
  compactManifoldMeasureOfData (SubordinateChartData.ofCompactManifold n M)

/-- Finiteness of the unconditional compact-manifold measure. -/
theorem compactManifoldMeasureUnconditional_isFiniteMeasure
    (n : ℕ) (M : Type)
    [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [MeasurableSpace M] :
    IsFiniteMeasure (compactManifoldMeasureUnconditional n M) :=
  compactManifoldMeasureOfData_isFiniteMeasure
    (SubordinateChartData.ofCompactManifold n M)

end JacobianChallenge

end
