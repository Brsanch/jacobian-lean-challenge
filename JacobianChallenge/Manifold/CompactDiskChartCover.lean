/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneForm
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Field.Basic

set_option diagnostics.threshold 100

/-! # Finite chart cover of a compact complex 1-manifold with disk hierarchy

For a compact complex 1-manifold `X` (charted on `ℂ`), this file
constructs a finite *disk chart cover*: a finite set of base points
`{x_1, ..., x_n} ⊆ X`, each equipped with an outer radius `R_i > 0`
and an inner radius `0 < r_i < R_i`, such that

* the *closed outer disk* `closedBall ((chartAt ℂ x_i) x_i) R_i` is
  contained in `(chartAt ℂ x_i).target`;
* the *open inner disks* `(chartAt ℂ x_i).symm '' ball ((chartAt ℂ x_i)
  x_i) r_i` cover `X`.

This is the geometric setup for the Forster/Montel/Riesz
finite-dimensionality proof of `HolomorphicOneForm X`. The outer
radius provides room for Cauchy estimates over the closed disk; the
inner radius bounds the chart pullback in which a holomorphic 1-form's
representative is controlled.

## Main definitions

* `JacobianChallenge.DiskChartCover X` — the bundled structure.

## Main results

* `JacobianChallenge.DiskChartCover.exists_of_compact` — existence
  of a disk chart cover on any compact nonempty complex 1-manifold.

## Implementation

The construction is the standard finite-subcover argument. For each
`x : X`, the chart target is open in `ℂ` and contains the chart image
of `x`, so there exists `R(x) > 0` with the closed disk of radius
`R(x)` contained in the chart target. Setting `r(x) := R(x) / 2`, the
chart preimages of the open balls of radius `r(x)` form an open cover
of `X` (each one being a neighbourhood of `x` itself). Compactness
yields a finite subcover.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology
open Set Metric

noncomputable section

namespace JacobianChallenge

/-- A *disk chart cover* of a complex 1-manifold `X`: a finite set of
base points, each with an outer radius `R` and an inner radius `r`
satisfying `0 < r < R`, such that the closed outer disk fits inside
the chart target and the open inner disks (pulled back through the
chart) cover `X`. -/
structure DiskChartCover (X : Type*) [TopologicalSpace X]
    [ChartedSpace ℂ X] where
  /-- The (finite) collection of base points. -/
  basePoints : Finset X
  /-- The outer radius at each base point. -/
  outerRadius : X → ℝ
  /-- The inner radius at each base point. -/
  innerRadius : X → ℝ
  /-- Positivity of the outer radius. -/
  outerRadius_pos : ∀ x ∈ basePoints, 0 < outerRadius x
  /-- Positivity of the inner radius. -/
  innerRadius_pos : ∀ x ∈ basePoints, 0 < innerRadius x
  /-- The inner radius is strictly less than the outer radius. -/
  innerRadius_lt_outerRadius :
    ∀ x ∈ basePoints, innerRadius x < outerRadius x
  /-- The closed outer disk at each base point fits inside the chart
  target. -/
  closedDisk_in_target : ∀ x ∈ basePoints,
    closedBall ((chartAt ℂ x) x) (outerRadius x) ⊆ (chartAt ℂ x).target
  /-- The chart preimages of the open inner disks cover `X`. -/
  covers : ∀ y : X, ∃ x ∈ basePoints,
    y ∈ (chartAt ℂ x).source ∧
    (chartAt ℂ x) y ∈ ball ((chartAt ℂ x) x) (innerRadius x)

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- For each base point, the inner radius is positive. -/
theorem innerRadius_pos_of_mem (cover : DiskChartCover X) {x : X}
    (hx : x ∈ cover.basePoints) : 0 < cover.innerRadius x :=
  cover.innerRadius_pos x hx

/-- For each base point, the outer radius is positive. -/
theorem outerRadius_pos_of_mem (cover : DiskChartCover X) {x : X}
    (hx : x ∈ cover.basePoints) : 0 < cover.outerRadius x :=
  cover.outerRadius_pos x hx

/-- The base point set is nonempty whenever `X` is nonempty: the cover
covers every point, so at least one base point exists. -/
theorem basePoints_nonempty (cover : DiskChartCover X) [Nonempty X] :
    cover.basePoints.Nonempty := by
  obtain ⟨y⟩ := ‹Nonempty X›
  obtain ⟨x, hx, _, _⟩ := cover.covers y
  exact ⟨x, hx⟩

end DiskChartCover

/-! ## Existence of a disk chart cover on compact spaces -/

section Existence

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- For any `x : X`, the chart target is open in `ℂ` and contains the
chart image of `x`, so there exists a positive radius `R` such that
the closed disk of radius `R` around the chart image is contained in
the chart target. -/
private lemma exists_chartRadius (x : X) :
    ∃ R : ℝ, 0 < R ∧
      closedBall ((chartAt ℂ x) x) R ⊆ (chartAt ℂ x).target := by
  have h_open : IsOpen (chartAt ℂ x).target := (chartAt ℂ x).open_target
  have h_mem : (chartAt ℂ x) x ∈ (chartAt ℂ x).target :=
    (chartAt ℂ x).map_source (mem_chart_source _ x)
  have h_nhds : (chartAt ℂ x).target ∈ 𝓝 ((chartAt ℂ x) x) :=
    h_open.mem_nhds h_mem
  rcases Metric.mem_nhds_iff.mp h_nhds with ⟨ε, hε_pos, hε_sub⟩
  refine ⟨ε / 2, by linarith, ?_⟩
  intro w hw
  apply hε_sub
  rw [mem_closedBall] at hw
  rw [mem_ball]
  linarith

/-- Classical choice of a radius for each `x`. -/
private noncomputable def chartRadius (x : X) : ℝ :=
  (exists_chartRadius x).choose

private lemma chartRadius_pos (x : X) : 0 < chartRadius x :=
  (exists_chartRadius x).choose_spec.1

private lemma chartRadius_closedBall_subset (x : X) :
    closedBall ((chartAt ℂ x) x) (chartRadius x) ⊆ (chartAt ℂ x).target :=
  (exists_chartRadius x).choose_spec.2

/-- The chart preimage of the open inner ball at `x`, restricted to
the chart source. -/
private def innerBallPreimage (x : X) : Set X :=
  (chartAt ℂ x).source ∩
    (chartAt ℂ x) ⁻¹' ball ((chartAt ℂ x) x) (chartRadius x / 2)

/-- The inner ball preimage is open in `X`. -/
private lemma innerBallPreimage_isOpen (x : X) :
    IsOpen (innerBallPreimage x) :=
  (chartAt ℂ x).continuousOn.isOpen_inter_preimage (chartAt ℂ x).open_source
    Metric.isOpen_ball

/-- The inner ball preimage at `x` contains `x`. -/
private lemma mem_innerBallPreimage_self (x : X) :
    x ∈ innerBallPreimage x := by
  refine ⟨mem_chart_source _ x, ?_⟩
  show (chartAt ℂ x) x ∈ ball ((chartAt ℂ x) x) (chartRadius x / 2)
  rw [mem_ball]
  have h := chartRadius_pos x
  rw [dist_self]
  linarith

/-- **Existence of a disk chart cover on a compact nonempty complex
1-manifold.** -/
theorem DiskChartCover.exists_of_compact
    [CompactSpace X] [Nonempty X] :
    Nonempty (DiskChartCover X) := by
  have h_cover : ∀ x : X, x ∈ ⋃ y : X, innerBallPreimage y := by
    intro x
    exact mem_iUnion.mpr ⟨x, mem_innerBallPreimage_self x⟩
  have h_compact : IsCompact (Set.univ : Set X) := CompactSpace.isCompact_univ
  have h_open_cover : ∀ x : X, IsOpen (innerBallPreimage x) :=
    fun x => innerBallPreimage_isOpen x
  rcases h_compact.elim_finite_subcover innerBallPreimage h_open_cover
    (fun x _ => h_cover x) with ⟨S, hS⟩
  refine ⟨⟨S, chartRadius, fun x => chartRadius x / 2, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro x _hx; exact chartRadius_pos x
  · intro x _hx; have := chartRadius_pos x; linarith
  · intro x _hx; have := chartRadius_pos x; linarith
  · intro x _hx; exact chartRadius_closedBall_subset x
  · intro y
    rcases mem_iUnion₂.mp (hS (Set.mem_univ y)) with ⟨x, hxS, hxy⟩
    refine ⟨x, hxS, ?_, ?_⟩
    · exact hxy.1
    · exact hxy.2

end Existence

end JacobianChallenge

end
