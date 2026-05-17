/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CompactDiskChartCover

set_option linter.unusedSectionVars false

/-! # Cover-refinement primitives for the multi-chart density bound

The Forster route to `FiniteDimensional ℂ (HolomorphicOneForm X)` needs
to bridge per-inner-disk uniform convergence to outer-disk seminorm
convergence. The key tool is the **multi-chart density bound**: every
point of the X-side outer disk at chart-`x` lies in some X-side inner
disk at another chart-`y`; on the overlap the cotangent transition is
continuous and bounded, giving a uniform bound.

This file ships the **topological refinement primitives** that
underwrite that bound:

* `DiskChartCover.outerDiskX cover x` — the X-side outer disk at base
  point `x`, the `(chartAt ℂ x).symm`-image of the closed outer ball in
  `ℂ`. **Compact** (continuous image of compact under `chartAt symm`).

* `DiskChartCover.innerSetX cover y` — the X-side inner open
  neighbourhood at base point `y`, the `chartAt`-preimage of the open
  inner ball in `ℂ`. **Open**.

* `DiskChartCover.innerSetX_covers_X` — the `basePoints`' inner sets
  cover all of `X`. Direct from `cover.covers`.

* `DiskChartCover.outerDiskX_subset_iUnion_innerSetX` — the X-side outer
  disk at any base point is covered by the union of basePoints' inner
  sets (since they cover all of `X`).

These primitives are the foundation for the next chip (cotangent
transition continuity bound on the overlap) and ultimately the
density-bound inequality. No `sorry`, no `axiom`.
-/

open Set Metric

open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ## X-side outer disk -/

/-- The X-side outer disk at base point `x`: the `(chartAt ℂ x).symm`-image
of the closed outer ball in `ℂ`. -/
def outerDiskX (cover : DiskChartCover X) (x : X) : Set X :=
  (chartAt ℂ x).symm '' closedBall ((chartAt ℂ x) x) (cover.outerRadius x)

/-- The X-side outer disk at a base point is compact (continuous image
of a compact closed disk under the inverse chart, which is continuous on
its target — and the closed disk fits inside the target). -/
theorem outerDiskX_isCompact (cover : DiskChartCover X) {x : X}
    (hx : x ∈ cover.basePoints) :
    IsCompact (cover.outerDiskX x) := by
  refine (isCompact_closedBall _ _).image_of_continuousOn ?_
  exact (chartAt ℂ x).continuousOn_symm.mono (cover.closedDisk_in_target x hx)

/-- The X-side outer disk at a base point is nonempty (it contains the
base point itself via the chart's `left_inv`). -/
theorem outerDiskX_nonempty (cover : DiskChartCover X) {x : X}
    (hx : x ∈ cover.basePoints) :
    (cover.outerDiskX x).Nonempty := by
  refine ⟨x, ?_⟩
  refine ⟨(chartAt ℂ x) x, ?_, (chartAt ℂ x).left_inv (mem_chart_source _ x)⟩
  rw [mem_closedBall]
  rw [dist_self]
  exact (cover.outerRadius_pos x hx).le

/-! ## X-side inner open neighbourhood -/

/-- The X-side inner open neighbourhood at base point `y`: the
`chartAt`-preimage of the open inner ball in `ℂ`, intersected with the
chart source. -/
def innerSetX (cover : DiskChartCover X) (y : X) : Set X :=
  (chartAt ℂ y).source ∩
    (chartAt ℂ y) ⁻¹' ball ((chartAt ℂ y) y) (cover.innerRadius y)

/-- The X-side inner neighbourhood is open. -/
theorem innerSetX_isOpen (cover : DiskChartCover X) (y : X) :
    IsOpen (cover.innerSetX y) :=
  (chartAt ℂ y).continuousOn.isOpen_inter_preimage (chartAt ℂ y).open_source
    Metric.isOpen_ball

/-- Membership in `innerSetX y` rewritten in its two-conjunct form. -/
theorem mem_innerSetX_iff (cover : DiskChartCover X) (y z : X) :
    z ∈ cover.innerSetX y ↔
      z ∈ (chartAt ℂ y).source ∧
        (chartAt ℂ y) z ∈ ball ((chartAt ℂ y) y) (cover.innerRadius y) :=
  Iff.rfl

/-! ## Coverage statements -/

/-- The `basePoints`' inner sets cover all of `X`. Direct restatement of
`cover.covers`. -/
theorem innerSetX_covers_X (cover : DiskChartCover X) (z : X) :
    ∃ y ∈ cover.basePoints, z ∈ cover.innerSetX y := by
  obtain ⟨y, hy_base, hy_source, hy_ball⟩ := cover.covers z
  exact ⟨y, hy_base, hy_source, hy_ball⟩

/-- The X-side outer disk at any base point is contained in the union of
the `basePoints`' inner sets (because those inner sets cover all of X). -/
theorem outerDiskX_subset_iUnion_innerSetX (cover : DiskChartCover X)
    (x : X) :
    cover.outerDiskX x ⊆ ⋃ y ∈ cover.basePoints, cover.innerSetX y := by
  intro z _hz
  obtain ⟨y, hy_base, hy_mem⟩ := cover.innerSetX_covers_X z
  exact mem_iUnion₂.mpr ⟨y, hy_base, hy_mem⟩

end DiskChartCover

end JacobianChallenge

end
