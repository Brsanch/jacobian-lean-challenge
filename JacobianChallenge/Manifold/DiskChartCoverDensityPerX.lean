/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverDensityClosedInner
import JacobianChallenge.Manifold.DiskChartCoverSeminorm
import JacobianChallenge.Manifold.DiskChartCoverSeminormInner

set_option linter.unusedSectionVars false

/-! # Per-`x` density bound

For each base point `x ∈ basePoints`, every `w ∈ closedBall outerRadius`
at `x` satisfies
`‖localCoeff om x w‖ ≤ M_x · seminormValInner cover om`,
with `M_x` independent of `om`.

Aggregating over `w` gives the local-bound form
`localCoeffMax cover x om ≤ M_x · seminormValInner cover om`.

Strategy: take `q := (chartAt x).symm w ∈ outerDiskX x`. By the
cover-refinement (`outerDiskX_subset_iUnion_innerSetX`) plus
`innerSetX ⊆ closedInnerDiskX`, we have `q ∈ closedInnerDiskX y` for
some `y ∈ basePoints`. Apply the per-pair density bound
`norm_localCoeff_le_outerInner_bound`, and dominate the right-hand side
by `seminormValInner cover om` (which is `Finset.sup'` of
`localCoeffMaxInner cover · om` over `basePoints`).

No `sorry`, no `axiom`.
-/

open Set Metric

open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- `innerSetX y ⊆ closedInnerDiskX y`. -/
private theorem innerSetX_subset_closedInnerDiskX (cover : DiskChartCover X)
    {y : X} (_hy : y ∈ cover.basePoints) :
    cover.innerSetX y ⊆ cover.closedInnerDiskX y := by
  intro q ⟨hq_src, hq_ball⟩
  -- `q ∈ chart-y source` and `(chartAt y) q ∈ open ball`. Open ⊆ closed.
  refine ⟨(chartAt ℂ y) q, ball_subset_closedBall hq_ball, ?_⟩
  exact (chartAt ℂ y).left_inv hq_src

/-- Every point of `outerDiskX x` lies in some `closedInnerDiskX y` for
`y ∈ basePoints`. -/
theorem outerDiskX_subset_iUnion_closedInnerDiskX
    (cover : DiskChartCover X) (x : X) :
    cover.outerDiskX x ⊆ ⋃ y ∈ cover.basePoints, cover.closedInnerDiskX y := by
  intro q hq
  obtain ⟨y, hy_base, hy_mem⟩ :=
    mem_iUnion₂.mp (cover.outerDiskX_subset_iUnion_innerSetX x hq)
  exact mem_iUnion₂.mpr
    ⟨y, hy_base, cover.innerSetX_subset_closedInnerDiskX hy_base hy_mem⟩

/-- The per-`y` density bound on the outer-`x` ∩ closed-inner-`y` set,
in the form using `seminormValInner` on the right. The constant is
`om`-independent (universally quantified after `∃ C`). -/
theorem norm_localCoeff_le_seminormValInner_bound
    [T2Space X] (cover : DiskChartCover X) [Nonempty X]
    {x y : X} (hx : x ∈ cover.basePoints) (hy : y ∈ cover.basePoints) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (om : HolomorphicOneForm X)
        (q : X), q ∈ cover.outerDiskX x ∩ cover.closedInnerDiskX y →
      ‖HolomorphicOneForm.localCoeff om x ((chartAt ℂ x) q)‖
        ≤ C * seminormValInner cover om := by
  obtain ⟨C, hC⟩ :=
    cover.norm_localCoeff_le_outerInner_bound hx hy
  refine ⟨max C 0, le_max_right _ _, fun om q hq => ?_⟩
  have h_C := hC om q hq
  -- `q ∈ closedInnerDiskX y` ⇒ `(chartAt y) q ∈ closedBall innerRadius`.
  have hq_y_chartImage : (chartAt ℂ y) q ∈
      closedBall ((chartAt ℂ y) y) (cover.innerRadius y) := by
    obtain ⟨w, hw, hw_eq⟩ := hq.2
    rw [← hw_eq, (chartAt ℂ y).right_inv]
    · exact hw
    · apply cover.closedDisk_in_target y hy
      exact closedBall_subset_closedBall
        (cover.innerRadius_lt_outerRadius y hy).le hw
  have h_inner : ‖HolomorphicOneForm.localCoeff om y ((chartAt ℂ y) q)‖
      ≤ localCoeffMaxInner cover y om :=
    norm_localCoeff_le_localCoeffMaxInner cover om hy hq_y_chartImage
  have h_aggr : localCoeffMaxInner cover y om ≤ seminormValInner cover om := by
    unfold seminormValInner
    exact Finset.le_sup' (fun z => localCoeffMaxInner cover z om) hy
  -- Bridge through `max C 0`. LHS ≤ C · ‖localCoeff y‖ ≤ max C 0 · ‖localCoeff y‖.
  have h_step1 :
      C * ‖HolomorphicOneForm.localCoeff om y ((chartAt ℂ y) q)‖
        ≤ max C 0 * ‖HolomorphicOneForm.localCoeff om y ((chartAt ℂ y) q)‖ :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have h_step2 :
      max C 0 * ‖HolomorphicOneForm.localCoeff om y ((chartAt ℂ y) q)‖
        ≤ max C 0 * seminormValInner cover om :=
    mul_le_mul_of_nonneg_left (h_inner.trans h_aggr) (le_max_right _ _)
  exact h_C.trans (h_step1.trans h_step2)

end DiskChartCover

end JacobianChallenge

end
