/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverDensityTransitionBound

set_option linter.unusedSectionVars false

/-! # Closed-inner-disk X-side primitive + per-pair density bound

The open inner set `innerSetX y` is open in `X` but isn't compact. For
the multi-chart density bound we need a *closed* counterpart: the
X-side closed inner disk `closedInnerDiskX cover y`. It is compact (the
continuous image of a closed ball under `chartAt.symm`), contained in
`(chartAt ℂ y).source`, and contains the closure of `innerSetX y`.

This file ships:

* `DiskChartCover.closedInnerDiskX cover y` — X-side closed inner disk
  at base point `y`.
* `DiskChartCover.closedInnerDiskX_isCompact`.
* `DiskChartCover.closedInnerDiskX_subset_source` — contained in chart-y
  source.
* `DiskChartCover.outerDiskX_inter_closedInnerDiskX_isCompact` — the
  intersection with `outerDiskX x` is compact.
* `DiskChartCover.outerDiskX_inter_closedInnerDiskX_subset_overlap` — and
  it's in the chart-overlap.
* `DiskChartCover.norm_localCoeff_le_outerInner_bound` — per-pair density
  bound: a constant `C(x,y)` and the inequality
  `‖localCoeff om x ((chartAt x) q)‖ ≤ C(x,y) · ‖localCoeff om y ((chartAt y) q)‖`
  on `outerDiskX x ∩ closedInnerDiskX y`.

No `sorry`, no `axiom`.
-/

open Set Metric

open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-! ## X-side closed inner disk -/

/-- The X-side closed inner disk at base point `y`: the
`(chartAt ℂ y).symm`-image of the closed inner ball in `ℂ`. -/
def closedInnerDiskX (cover : DiskChartCover X) (y : X) : Set X :=
  (chartAt ℂ y).symm '' closedBall ((chartAt ℂ y) y) (cover.innerRadius y)

/-- The X-side closed inner disk is compact. Continuous image of a
compact closed ball under `chartAt.symm` (continuous on its target,
which contains the closed inner ball via inner-inside-outer-inside-target). -/
theorem closedInnerDiskX_isCompact (cover : DiskChartCover X) {y : X}
    (hy : y ∈ cover.basePoints) :
    IsCompact (cover.closedInnerDiskX y) := by
  refine (isCompact_closedBall _ _).image_of_continuousOn ?_
  -- Chain: closedBall innerRadius ⊆ closedBall outerRadius ⊆ chart-y target.
  have h_inner_le_outer : cover.innerRadius y ≤ cover.outerRadius y :=
    (cover.innerRadius_lt_outerRadius y hy).le
  have h_sub :
      closedBall ((chartAt ℂ y) y) (cover.innerRadius y) ⊆
        (chartAt ℂ y).target := by
    intro p hp
    apply cover.closedDisk_in_target y hy
    exact closedBall_subset_closedBall h_inner_le_outer hp
  exact (chartAt ℂ y).continuousOn_symm.mono h_sub

/-- The X-side closed inner disk is contained in the chart-`y` source. -/
theorem closedInnerDiskX_subset_source (cover : DiskChartCover X) {y : X}
    (hy : y ∈ cover.basePoints) :
    cover.closedInnerDiskX y ⊆ (chartAt ℂ y).source := by
  intro q hq
  obtain ⟨p, hp_mem, hp_eq⟩ := hq
  rw [← hp_eq]
  -- `(chartAt y).symm` maps target into source (via `OpenPartialHomeomorph.map_target`).
  have hp_target : p ∈ (chartAt ℂ y).target := by
    apply cover.closedDisk_in_target y hy
    have h_inner_le_outer : cover.innerRadius y ≤ cover.outerRadius y :=
      (cover.innerRadius_lt_outerRadius y hy).le
    exact closedBall_subset_closedBall h_inner_le_outer hp_mem
  exact (chartAt ℂ y).map_target hp_target

/-! ## outerDiskX ∩ closedInnerDiskX -/

/-- The intersection of the outer disk at `x` and the closed inner disk
at `y` is compact (intersection of two compact sets in a T2 space). -/
theorem outerDiskX_inter_closedInnerDiskX_isCompact
    [T2Space X] (cover : DiskChartCover X)
    {x y : X} (hx : x ∈ cover.basePoints) (hy : y ∈ cover.basePoints) :
    IsCompact (cover.outerDiskX x ∩ cover.closedInnerDiskX y) := by
  exact (cover.outerDiskX_isCompact hx).inter_right
    (cover.closedInnerDiskX_isCompact hy).isClosed

/-- The intersection is contained in the chart overlap. -/
theorem outerDiskX_inter_closedInnerDiskX_subset_overlap
    (cover : DiskChartCover X)
    {x y : X} (hx : x ∈ cover.basePoints) (hy : y ∈ cover.basePoints) :
    cover.outerDiskX x ∩ cover.closedInnerDiskX y ⊆
      (chartAt ℂ x).source ∩ (chartAt ℂ y).source := by
  intro q ⟨hq_outer, hq_inner⟩
  refine ⟨?_, cover.closedInnerDiskX_subset_source hy hq_inner⟩
  -- outerDiskX x ⊆ (chartAt x).source via .symm '' target ⊆ source.
  obtain ⟨p, hp_target, hp_eq⟩ := hq_outer
  rw [← hp_eq]
  exact (chartAt ℂ x).map_target (cover.closedDisk_in_target x hx hp_target)

/-! ## Per-pair density bound -/

/-- **Per-pair density bound** on `outerDiskX x ∩ closedInnerDiskX y`:
a uniform constant `C(x, y) ≥ 0` and the inequality
`‖localCoeff om x ((chartAt x) q)‖ ≤ C(x, y) · ‖localCoeff om y ((chartAt y) q)‖`
holding for every `om : HolomorphicOneForm X`. The constant depends only
on `x` and `y` (not on `om`). -/
theorem norm_localCoeff_le_outerInner_bound
    [T2Space X] (cover : DiskChartCover X)
    {x y : X} (hx : x ∈ cover.basePoints) (hy : y ∈ cover.basePoints) :
    ∃ C : ℝ, ∀ (om : HolomorphicOneForm X)
        (q : X), q ∈ cover.outerDiskX x ∩ cover.closedInnerDiskX y →
      ‖HolomorphicOneForm.localCoeff om x ((chartAt ℂ x) q)‖
        ≤ C * ‖HolomorphicOneForm.localCoeff om y ((chartAt ℂ y) q)‖ := by
  obtain ⟨C, hC⟩ := exists_bound_transitionFactor x y
    (cover.outerDiskX_inter_closedInnerDiskX_isCompact hx hy)
    (fun q hq =>
      ((cover.outerDiskX_inter_closedInnerDiskX_subset_overlap hx hy) hq).1)
    (fun q hq =>
      ((cover.outerDiskX_inter_closedInnerDiskX_subset_overlap hx hy) hq).2)
  refine ⟨C, fun om q hq => ?_⟩
  have h_x : q ∈ (chartAt ℂ x).source :=
    ((cover.outerDiskX_inter_closedInnerDiskX_subset_overlap hx hy) hq).1
  have h_y : q ∈ (chartAt ℂ y).source :=
    ((cover.outerDiskX_inter_closedInnerDiskX_subset_overlap hx hy) hq).2
  refine (norm_localCoeff_le om h_x h_y).trans ?_
  exact mul_le_mul_of_nonneg_right (hC q hq) (norm_nonneg _)

end DiskChartCover

end JacobianChallenge

end
