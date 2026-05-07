/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.CompactManifoldMeasure

/-! # Conditional assembly of a finite Borel measure on a compact charted manifold

This file packages ZZ135's `partitionPushforwardSum_isFiniteMeasure`
into a single `def`/`instance` pair that produces a finite `Measure M`
on an abstract space `M`, conditional on a single bundle of data —
"a smooth subordinate partition of unity exists" — abstracted as a
structure `SubordinateChartData`.

The structure intentionally records exactly what mathlib's
`SmoothPartitionOfUnity.exists_isSubordinate` /
`SmoothBumpCovering.toSmoothPartitionOfUnity` produce on a compact
charted manifold:

* a finite index set `s : Finset ι`,
* per-index target measurable spaces `N i` (intended as the chart
  codomain in ℝⁿ),
* per-index measurable maps `g i : N i → M` (intended as chart
  inverses post-composed with smooth bump weights),
* per-index *finite* measures `ν i` on `N i` (intended as
  bump-weighted Lebesgue restrictions, which are finite because the
  bumps have compact support).

Given this data, `compactManifoldMeasureOfData` is the partition
pushforward sum, and `compactManifoldMeasureOfData_isFiniteMeasure`
upgrades ZZ135's lemma into a `IsFiniteMeasure` instance.

A subsequent chip will discharge `SubordinateChartData` from
`[CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
[IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ⊤ M]` by appealing to
`SmoothBumpCovering.exists_isSubordinate`. The current chip closes
the assembly half — everything *after* one has the subordinate
partition.

## Implementation notes

We keep `M` a plain `MeasurableSpace` rather than a manifold so the
construction composes with downstream uses where the manifold
typeclasses are not yet in scope. Manifold instantiation is a thin
layer above this file.
-/

noncomputable section

namespace JacobianChallenge

open MeasureTheory

variable {M : Type*} [MeasurableSpace M]

/-- All the data needed to assemble a finite Borel-style measure on
`M` from a finite atlas-like cover. The fields mirror what a smooth
subordinate partition of unity supplies on a compact charted
manifold: a finite index, per-index chart codomains, measurable
chart-inverse maps, and finite per-index weighted measures. -/
structure SubordinateChartData (M : Type*) [MeasurableSpace M] where
  /-- Index type for the finite cover. -/
  ι : Type
  /-- Finite index set (the cover is finite by compactness). -/
  s : Finset ι
  /-- Per-chart target type (intended: open subset of ℝⁿ). -/
  N : ι → Type
  /-- Measurable-space structure on each chart target. -/
  measurableSpaceN : ∀ i, MeasurableSpace (N i)
  /-- Per-chart map into `M` (intended: chart inverse). -/
  g : ∀ i, N i → M
  /-- The chart maps are measurable. -/
  measurable_g : ∀ i ∈ s, Measurable (g i)
  /-- Per-chart measure (intended: bump-weighted Lebesgue restriction). -/
  ν : ∀ i, @Measure (N i) (measurableSpaceN i)
  /-- Each per-chart measure is finite (intended: smooth bump has
  compact support). -/
  finite_ν : ∀ i ∈ s, @IsFiniteMeasure (N i) (measurableSpaceN i) (ν i)

namespace SubordinateChartData

attribute [instance] measurableSpaceN

/-- The assembled finite measure on `M` produced by a
`SubordinateChartData`: the partition-of-unity pushforward sum from
ZZ135's foundational chip. -/
noncomputable def measure (D : SubordinateChartData M) : Measure M :=
  partitionPushforwardSum (M := M) D.s D.g D.ν

/-- Total mass of the assembled measure equals the sum of pushforward
masses, by ZZ135's `partitionPushforwardSum_univ`. -/
lemma measure_univ (D : SubordinateChartData M) :
    D.measure Set.univ
      = ∑ i ∈ D.s, (Measure.map (D.g i) (D.ν i)) Set.univ := by
  unfold measure
  exact partitionPushforwardSum_univ (M := M) D.s D.g D.ν

/-- The assembled measure is finite: every per-chart pushforward has
finite mass, so their finite sum is finite. -/
theorem measure_isFiniteMeasure (D : SubordinateChartData M) :
    IsFiniteMeasure D.measure := by
  have h := partitionPushforwardSum_isFiniteMeasure
    (M := M) D.s D.g D.ν D.measurable_g D.finite_ν
  exact h

end SubordinateChartData

/-- The finite measure on `M` assembled from a `SubordinateChartData`.
This is the public entry point; downstream code should treat this as
*the* compact-manifold measure once a chip supplies the data
(unconditionally) from manifold typeclasses. -/
noncomputable def compactManifoldMeasureOfData
    (D : SubordinateChartData M) : Measure M :=
  D.measure

/-- The assembled compact-manifold measure is finite. -/
theorem compactManifoldMeasureOfData_isFiniteMeasure
    (D : SubordinateChartData M) :
    IsFiniteMeasure (compactManifoldMeasureOfData D) :=
  D.measure_isFiniteMeasure

end JacobianChallenge

end
