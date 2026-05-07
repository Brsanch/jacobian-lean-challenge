/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Defs.Basic

/-! # Partition-of-unity pushforward sum (foundational chip)

This file provides the *abstract* finite-sum pushforward measure that
the partition-of-unity construction of a Riemannian-style volume measure
on a compact charted manifold reduces to. It is the second analytic
chip in the Hodge cluster (companion to `Analysis/L2OnManifold.lean`).

For a finite index family `i : ι` together with chart inverses
`g i : N i → M` and per-chart positive measures `ν i : Measure (N i)`,
we define

  `partitionPushforwardSum g ν = ∑ i, Measure.map (g i) (ν i)`.

When each `ν i` is finite and the index family is a `Finset` (or
`Fintype`), the resulting measure is finite. This matches the
manifold-level construction where:

* `ι` indexes a finite atlas covering the compact manifold `M`,
* `N i` is the chart codomain (an open set in `ℝⁿ`),
* `g i : N i → M` is the chart inverse,
* `ν i = χ i • volume` is a smooth-bump-weighted Lebesgue measure
  with compact support inside `N i`, hence finite.

A subsequent chip will plug in
`Mathlib.Geometry.Manifold.PartitionOfUnity` to instantiate this on a
`CompactSpace` `ChartedSpace`.

## Implementation notes

We deliberately keep `M` and `N i` as plain measurable spaces so this
layer composes equally with `M` a manifold and `N i = ℝⁿ`. The
`Measurable (g i)` hypothesis is required by `Measure.map` to behave
as the genuine pushforward.

The `Finset.sum` of measures used here is the `MeasureTheory.Measure`
additive monoid sum, available in mathlib for any countable family.
-/

noncomputable section

namespace JacobianChallenge

open MeasureTheory

variable {ι : Type*}
variable {M : Type*} [MeasurableSpace M]

/-- Pushforward sum of per-chart measures: given for each index `i`
a measurable map `g i : N i → M` and a measure `ν i` on `N i`, the
total pushforward is `∑ i, Measure.map (g i) (ν i)`.

This is the abstract form of the partition-of-unity volume measure
on a compact charted manifold. -/
def partitionPushforwardSum
    {N : ι → Type*} [∀ i, MeasurableSpace (N i)]
    (s : Finset ι) (g : ∀ i, N i → M) (ν : ∀ i, Measure (N i)) :
    Measure M :=
  ∑ i ∈ s, Measure.map (g i) (ν i)

/-- The total mass of the partition-of-unity pushforward sum equals
the (finite) sum of the per-chart pushforward masses. -/
lemma partitionPushforwardSum_univ
    {N : ι → Type*} [∀ i, MeasurableSpace (N i)]
    (s : Finset ι) (g : ∀ i, N i → M) (ν : ∀ i, Measure (N i)) :
    (partitionPushforwardSum (M := M) s g ν) Set.univ
      = ∑ i ∈ s, (Measure.map (g i) (ν i)) Set.univ := by
  unfold partitionPushforwardSum
  rw [Measure.finset_sum_apply]

/-- Finiteness of the partition-of-unity pushforward sum: if every
per-chart measure is finite and every chart map is measurable, the
total measure is finite. This is the lemma the manifold-level chip
will invoke after producing finitely many bump-weighted Lebesgue
restrictions. -/
theorem partitionPushforwardSum_isFiniteMeasure
    {N : ι → Type*} [∀ i, MeasurableSpace (N i)]
    (s : Finset ι) (g : ∀ i, N i → M) (ν : ∀ i, Measure (N i))
    (hg : ∀ i ∈ s, Measurable (g i))
    (hν : ∀ i ∈ s, IsFiniteMeasure (ν i)) :
    IsFiniteMeasure (partitionPushforwardSum (M := M) s g ν) := by
  refine ⟨?_⟩
  rw [partitionPushforwardSum_univ]
  refine (ENNReal.sum_lt_top).mpr (fun i hi => ?_)
  have hmeas : Measurable (g i) := hg i hi
  have : IsFiniteMeasure (ν i) := hν i hi
  rw [Measure.map_apply hmeas MeasurableSet.univ]
  simpa [Set.preimage_univ] using (measure_lt_top (ν i) Set.univ)

/-- Trivial case: empty index gives the zero measure. -/
@[simp]
lemma partitionPushforwardSum_empty
    {N : ι → Type*} [∀ i, MeasurableSpace (N i)]
    (g : ∀ i, N i → M) (ν : ∀ i, Measure (N i)) :
    partitionPushforwardSum (M := M) (∅ : Finset ι) g ν = 0 := by
  unfold partitionPushforwardSum
  simp

end JacobianChallenge

end
