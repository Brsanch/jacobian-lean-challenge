/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverSeminormSeparating
import Mathlib.Data.Real.Pointwise
import Mathlib.Algebra.Group.Pointwise.Set.Scalar

set_option diagnostics.threshold 100

/-! # Inner-disk variant of the disk-cover seminorm

The existing `seminormVal cover om` sups `‖localCoeff om x ·‖` over the
*outer* closed disk at every base point `x`. This file defines the
analogous *inner*-disk variant:

```
DiskChartCover.localCoeffMaxInner cover x om
  := sSup (‖localCoeff om x ·‖ '' closedBall ((chartAt ℂ x) x) (cover.innerRadius x))
DiskChartCover.seminormValInner cover om
  := basePoints.sup' h (fun x => localCoeffMaxInner cover x om)
```

Why this exists: the per-chart Arzelà-Ascoli `extract_diagonal_subseq`
in `DiskChartCoverDiagonal.lean` produces sub-sequence convergence in
the `BoundedContinuousFunction` metric on the *inner* closed disk.
Bridging that to convergence in `seminormVal` (outer-disk sup) requires
the multi-chart density / cocycle bound. Using the *inner*-disk
seminorm sidesteps that bridge: norm convergence on the
inner-disk-seminormed space is exactly the BCF convergence produced by
`extract_diagonal_subseq`.

The two seminorms are equivalent (and seminormValInner ≤ seminormVal
trivially, since the inner closed disk is contained in the outer
closed disk).

This file mirrors `DiskChartCoverSeminorm.lean` and
`DiskChartCoverSeminormAggregate.lean` axiom-for-axiom but over the
inner radius.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff Pointwise
open Set Metric HolomorphicOneForm

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-! ## Continuity of `localCoeff` on the inner closed disk -/

omit [IsManifold 𝓘(ℂ) ω X] in
private lemma inner_closedBall_subset_target (cover : DiskChartCover X)
    {x : X} (hx : x ∈ cover.basePoints) :
    closedBall ((chartAt ℂ x) x) (cover.innerRadius x) ⊆ (chartAt ℂ x).target := by
  intro w hw
  have h_inner_le_outer : cover.innerRadius x ≤ cover.outerRadius x :=
    (cover.innerRadius_lt_outerRadius x hx).le
  have hw_outer : w ∈ closedBall ((chartAt ℂ x) x) (cover.outerRadius x) :=
    (closedBall_subset_closedBall h_inner_le_outer) hw
  exact cover.closedDisk_in_target x hx hw_outer

private lemma localCoeff_continuousOn_innerDisk' (cover : DiskChartCover X)
    (om : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints) :
    ContinuousOn (localCoeff om x)
      (closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :=
  ((localCoeff_differentiableOn om x).continuousOn).mono
    (inner_closedBall_subset_target cover hx)

private lemma norm_localCoeff_continuousOn_innerDisk
    (cover : DiskChartCover X) (om : HolomorphicOneForm X)
    {x : X} (hx : x ∈ cover.basePoints) :
    ContinuousOn (fun w => ‖localCoeff om x w‖)
      (closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :=
  continuous_norm.continuousOn.comp
    (localCoeff_continuousOn_innerDisk' cover om hx) (mapsTo_image _ _)

/-! ## Compactness + non-emptiness of the inner closed disk -/

omit [IsManifold 𝓘(ℂ) ω X] in
private lemma innerDisk_nonempty (cover : DiskChartCover X) {x : X}
    (hx : x ∈ cover.basePoints) :
    (closedBall ((chartAt ℂ x) x) (cover.innerRadius x)).Nonempty :=
  ⟨(chartAt ℂ x) x, mem_closedBall_self
    (le_of_lt (cover.innerRadius_pos x hx))⟩

omit [IsManifold 𝓘(ℂ) ω X] in
private lemma innerDisk_isCompact (cover : DiskChartCover X) (x : X) :
    IsCompact (closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :=
  isCompact_closedBall _ _

/-! ## Bounded image of `‖localCoeff om x ·‖` over the inner disk -/

private lemma norm_localCoeff_inner_image_bddAbove
    (cover : DiskChartCover X) (om : HolomorphicOneForm X)
    {x : X} (hx : x ∈ cover.basePoints) :
    BddAbove ((fun w => ‖localCoeff om x w‖) ''
      closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) := by
  have h_compact := innerDisk_isCompact cover x
  have h_ne := innerDisk_nonempty cover hx
  have h_cont := norm_localCoeff_continuousOn_innerDisk cover om hx
  rcases h_compact.exists_isMaxOn h_ne h_cont with ⟨w_max, hw_max_mem, hw_max⟩
  refine ⟨‖localCoeff om x w_max‖, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact hw_max hw

private lemma norm_localCoeff_inner_image_nonempty
    (cover : DiskChartCover X) (om : HolomorphicOneForm X)
    {x : X} (hx : x ∈ cover.basePoints) :
    ((fun w => ‖localCoeff om x w‖) ''
      closedBall ((chartAt ℂ x) x) (cover.innerRadius x)).Nonempty := by
  obtain ⟨w, hw⟩ := innerDisk_nonempty cover hx
  exact ⟨_, w, hw, rfl⟩

/-! ## Definition of `localCoeffMaxInner` -/

/-- Sup of `‖localCoeff om x ·‖` over the *inner* closed disk at `x`. -/
def localCoeffMaxInner (cover : DiskChartCover X) (x : X)
    (om : HolomorphicOneForm X) : ℝ :=
  sSup ((fun w => ‖localCoeff om x w‖) ''
    closedBall ((chartAt ℂ x) x) (cover.innerRadius x))

theorem norm_localCoeff_le_localCoeffMaxInner (cover : DiskChartCover X)
    (om : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints)
    {w : ℂ} (hw : w ∈ closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :
    ‖localCoeff om x w‖ ≤ localCoeffMaxInner cover x om := by
  unfold localCoeffMaxInner
  exact le_csSup (norm_localCoeff_inner_image_bddAbove cover om hx) ⟨w, hw, rfl⟩

theorem localCoeffMaxInner_nonneg (cover : DiskChartCover X)
    (om : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints) :
    0 ≤ localCoeffMaxInner cover x om := by
  obtain ⟨w, hw⟩ := innerDisk_nonempty cover hx
  exact (norm_nonneg _).trans
    (norm_localCoeff_le_localCoeffMaxInner cover om hx hw)

@[simp]
theorem localCoeffMaxInner_zero (cover : DiskChartCover X) {x : X}
    (hx : x ∈ cover.basePoints) :
    localCoeffMaxInner cover x (0 : HolomorphicOneForm X) = 0 := by
  unfold localCoeffMaxInner
  rw [HolomorphicOneForm.localCoeff_zero]
  have h_image : ((fun w => ‖(0 : ℂ → ℂ) w‖) ''
      closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) = {(0 : ℝ)} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · obtain ⟨w, hw⟩ := innerDisk_nonempty cover hx
      exact ⟨w, hw, by simp⟩
    · rintro y ⟨w, _hw, rfl⟩
      simp
  rw [h_image]
  exact csSup_singleton (0 : ℝ)

private lemma localCoeffMaxInner_le_of_norm_le (cover : DiskChartCover X)
    (om₁ om₂ : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints)
    (h : ∀ w ∈ closedBall ((chartAt ℂ x) x) (cover.innerRadius x),
      ‖localCoeff om₁ x w‖ ≤ ‖localCoeff om₂ x w‖) :
    localCoeffMaxInner cover x om₁ ≤ localCoeffMaxInner cover x om₂ := by
  unfold localCoeffMaxInner
  refine csSup_le (norm_localCoeff_inner_image_nonempty cover om₁ hx) ?_
  rintro y ⟨w, hw, rfl⟩
  exact (h w hw).trans
    (norm_localCoeff_le_localCoeffMaxInner cover om₂ hx hw)

theorem localCoeffMaxInner_add_le (cover : DiskChartCover X)
    (om₁ om₂ : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints) :
    localCoeffMaxInner cover x (om₁ + om₂)
      ≤ localCoeffMaxInner cover x om₁ + localCoeffMaxInner cover x om₂ := by
  unfold localCoeffMaxInner
  refine csSup_le (norm_localCoeff_inner_image_nonempty cover (om₁ + om₂) hx) ?_
  rintro y ⟨w, hw, rfl⟩
  show ‖localCoeff (om₁ + om₂) x w‖ ≤ _
  have h_pt : localCoeff (om₁ + om₂) x w
      = localCoeff om₁ x w + localCoeff om₂ x w := by
    have := HolomorphicOneForm.localCoeff_add om₁ om₂ x
    rw [this]; rfl
  rw [h_pt]
  refine (norm_add_le _ _).trans ?_
  exact add_le_add
    (norm_localCoeff_le_localCoeffMaxInner cover om₁ hx hw)
    (norm_localCoeff_le_localCoeffMaxInner cover om₂ hx hw)

theorem localCoeffMaxInner_neg (cover : DiskChartCover X)
    (om : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints) :
    localCoeffMaxInner cover x (-om) = localCoeffMaxInner cover x om := by
  have h_pt : ∀ w, localCoeff (-om) x w = -localCoeff om x w := by
    intro w
    have := HolomorphicOneForm.localCoeff_neg om x
    rw [this]; rfl
  apply le_antisymm
  · refine localCoeffMaxInner_le_of_norm_le cover (-om) om hx ?_
    intro w _hw
    rw [h_pt, norm_neg]
  · refine localCoeffMaxInner_le_of_norm_le cover om (-om) hx ?_
    intro w _hw
    rw [h_pt, norm_neg]

theorem localCoeffMaxInner_smul (cover : DiskChartCover X)
    (c : ℂ) (om : HolomorphicOneForm X) {x : X}
    (_hx : x ∈ cover.basePoints) :
    localCoeffMaxInner cover x (c • om) = ‖c‖ * localCoeffMaxInner cover x om := by
  unfold localCoeffMaxInner
  have h_pt : ∀ w, ‖localCoeff (c • om) x w‖ = ‖c‖ * ‖localCoeff om x w‖ := by
    intro w
    have hsmul := HolomorphicOneForm.localCoeff_smul c om x
    have : localCoeff (c • om) x w = c • localCoeff om x w := by rw [hsmul]; rfl
    rw [this]
    simp [smul_eq_mul]
  have h_image_smul :
      ((fun w => ‖localCoeff (c • om) x w‖) ''
        closedBall ((chartAt ℂ x) x) (cover.innerRadius x))
      = ((‖c‖ : ℝ) • ((fun w => ‖localCoeff om x w‖) ''
          closedBall ((chartAt ℂ x) x) (cover.innerRadius x))) := by
    ext y
    simp only [mem_image, mem_smul_set]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨‖localCoeff om x w‖, ⟨w, hw, rfl⟩, ?_⟩
      rw [h_pt]; ring
    · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨w, hw, ?_⟩
      rw [h_pt]; ring
  rw [h_image_smul, Real.sSup_smul_of_nonneg (norm_nonneg c)]
  rfl

/-! ## `seminormValInner`: aggregate over base points -/

/-- The inner-disk variant of the disk-cover seminorm: the maximum of
`localCoeffMaxInner` over the cover's base points. -/
def seminormValInner (cover : DiskChartCover X) [Nonempty X]
    (om : HolomorphicOneForm X) : ℝ :=
  cover.basePoints.sup' (cover.basePoints_nonempty)
    (fun x => localCoeffMaxInner cover x om)

theorem seminormValInner_nonneg (cover : DiskChartCover X) [Nonempty X]
    (om : HolomorphicOneForm X) :
    0 ≤ seminormValInner cover om := by
  unfold seminormValInner
  obtain ⟨x, hx⟩ := cover.basePoints_nonempty
  have h_le : localCoeffMaxInner cover x om
      ≤ cover.basePoints.sup' cover.basePoints_nonempty
          (fun y => localCoeffMaxInner cover y om) :=
    Finset.le_sup' (fun y => localCoeffMaxInner cover y om) hx
  exact (localCoeffMaxInner_nonneg cover om hx).trans h_le

@[simp]
theorem seminormValInner_zero (cover : DiskChartCover X) [Nonempty X] :
    seminormValInner cover (0 : HolomorphicOneForm X) = 0 := by
  unfold seminormValInner
  refine le_antisymm ?_ (seminormValInner_nonneg cover 0)
  refine Finset.sup'_le _ _ ?_
  intro x hx
  exact (localCoeffMaxInner_zero cover hx).le

theorem seminormValInner_neg (cover : DiskChartCover X) [Nonempty X]
    (om : HolomorphicOneForm X) :
    seminormValInner cover (-om) = seminormValInner cover om := by
  unfold seminormValInner
  exact Finset.sup'_congr cover.basePoints_nonempty rfl
    (fun x hx => localCoeffMaxInner_neg cover om hx)

theorem seminormValInner_add_le (cover : DiskChartCover X) [Nonempty X]
    (om₁ om₂ : HolomorphicOneForm X) :
    seminormValInner cover (om₁ + om₂)
      ≤ seminormValInner cover om₁ + seminormValInner cover om₂ := by
  unfold seminormValInner
  refine Finset.sup'_le _ _ ?_
  intro x hx
  have h_le := localCoeffMaxInner_add_le cover om₁ om₂ hx
  refine h_le.trans (add_le_add ?_ ?_)
  · exact Finset.le_sup' (fun y => localCoeffMaxInner cover y om₁) hx
  · exact Finset.le_sup' (fun y => localCoeffMaxInner cover y om₂) hx

theorem seminormValInner_smul (cover : DiskChartCover X) [Nonempty X]
    (c : ℂ) (om : HolomorphicOneForm X) :
    seminormValInner cover (c • om) = ‖c‖ * seminormValInner cover om := by
  unfold seminormValInner
  rw [show cover.basePoints.sup' cover.basePoints_nonempty
        (fun x => localCoeffMaxInner cover x (c • om))
        = cover.basePoints.sup' cover.basePoints_nonempty
          (fun x => ‖c‖ * localCoeffMaxInner cover x om) from
    Finset.sup'_congr cover.basePoints_nonempty rfl (fun x hx =>
      localCoeffMaxInner_smul cover c om hx)]
  exact (Finset.mul₀_sup' (norm_nonneg c)
    (fun x => localCoeffMaxInner cover x om) cover.basePoints
    cover.basePoints_nonempty).symm

/-! ## Inner ≤ outer (trivial, used for sequential-compactness input) -/

theorem localCoeffMaxInner_le_localCoeffMax (cover : DiskChartCover X)
    (om : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints) :
    localCoeffMaxInner cover x om ≤ localCoeffMax cover x om := by
  unfold localCoeffMaxInner
  refine csSup_le (norm_localCoeff_inner_image_nonempty cover om hx) ?_
  rintro y ⟨w, hw, rfl⟩
  have h_inner_le_outer : cover.innerRadius x ≤ cover.outerRadius x :=
    (cover.innerRadius_lt_outerRadius x hx).le
  have hw_outer : w ∈ closedBall ((chartAt ℂ x) x) (cover.outerRadius x) :=
    (closedBall_subset_closedBall h_inner_le_outer) hw
  exact norm_localCoeff_le_localCoeffMax cover om hx hw_outer

theorem seminormValInner_le_seminormVal (cover : DiskChartCover X) [Nonempty X]
    (om : HolomorphicOneForm X) :
    seminormValInner cover om ≤ seminormVal cover om := by
  unfold seminormValInner seminormVal
  refine Finset.sup'_le _ _ ?_
  intro x hx
  exact (localCoeffMaxInner_le_localCoeffMax cover om hx).trans
    (Finset.le_sup' (fun y => localCoeffMax cover y om) hx)

/-! ## Separating: inner-disk version -/

theorem seminormValInner_eq_zero_iff_zero (cover : DiskChartCover X) [Nonempty X]
    (om : HolomorphicOneForm X) :
    seminormValInner cover om = 0 ↔ om = 0 := by
  refine ⟨fun h => ?_, fun h => by subst h; exact seminormValInner_zero cover⟩
  -- Reduce to `∀ y, om.toFun y = 0`.
  apply ContMDiffSection.ext
  intro y
  -- Pick a base point whose chart contains `y` in the inner open ball.
  obtain ⟨x, hx_base, hy_source, hy_ball⟩ := cover.covers y
  -- The per-chart sup `localCoeffMaxInner x om` is at most `seminormValInner = 0`.
  have h_max_nonneg := localCoeffMaxInner_nonneg cover om hx_base
  have h_max_le : localCoeffMaxInner cover x om ≤ seminormValInner cover om := by
    unfold seminormValInner
    exact Finset.le_sup' (fun y => localCoeffMaxInner cover y om) hx_base
  rw [h] at h_max_le
  have h_max_zero : localCoeffMaxInner cover x om = 0 :=
    le_antisymm h_max_le h_max_nonneg
  -- `(chartAt ℂ x) y ∈ ball ((chartAt ℂ x) x) (innerRadius x) ⊆ closed ball`.
  have h_chart_y_in_inner :
      (chartAt ℂ x) y ∈ closedBall ((chartAt ℂ x) x) (cover.innerRadius x) :=
    ball_subset_closedBall hy_ball
  have h_norm_le :=
    norm_localCoeff_le_localCoeffMaxInner cover om hx_base h_chart_y_in_inner
  rw [h_max_zero] at h_norm_le
  have h_norm_zero : ‖localCoeff om x ((chartAt ℂ x) y)‖ = 0 :=
    le_antisymm h_norm_le (norm_nonneg _)
  have h_lc_zero : localCoeff om x ((chartAt ℂ x) y) = 0 :=
    norm_eq_zero.mp h_norm_zero
  -- Reuse the chart-image bridge from `DiskChartCoverSeminormSeparating.lean`.
  -- We replay its argument inline (the helper is `private` to that file).
  have h_chart : (chartAt ℂ x).symm ((chartAt ℂ x) y) = y :=
    (chartAt ℂ x).left_inv hy_source
  have h_unfold :
      ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ y) (achart ℂ x) y (om.toFun y)) 1 = 0 := by
    have h_eq : localCoeff om x ((chartAt ℂ x) y) =
        ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ y) (achart ℂ x) y (om.toFun y)) 1 := by
      show ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
              (achart ℂ ((chartAt ℂ x).symm ((chartAt ℂ x) y)))
              (achart ℂ x)
              ((chartAt ℂ x).symm ((chartAt ℂ x) y))
              (om.toFun ((chartAt ℂ x).symm ((chartAt ℂ x) y)))) 1 = _
      rw [h_chart]
    rw [h_eq] at h_lc_zero
    exact h_lc_zero
  -- CLM eval-at-`1` plus cotangent coord-change injectivity.
  have h_clm : (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
      (achart ℂ y) (achart ℂ x) y (om.toFun y) = 0 :=
    ContinuousLinearMap.ext_ring
      (h_unfold.trans (ContinuousLinearMap.zero_apply 1).symm)
  -- Inverse cocycle: `coordChange x→y ∘ coordChange y→x = coordChange y→y = id`.
  have hy_in_x : y ∈ (cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ x) :=
    hy_source
  have hy_in_y : y ∈ (cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ y) :=
    mem_chart_source _ y
  have h_comp := (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange_comp
    (achart ℂ y) (achart ℂ x) (achart ℂ y) y
    ⟨⟨hy_in_y, hy_in_x⟩, hy_in_y⟩ (om.toFun y)
  -- `coordChange c c x 0 = 0` and `coordChange y y y v = v`.
  have h_zero : (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
      (achart ℂ x) (achart ℂ y) y 0 = 0 := by
    rw [cotangentBundleCore_coordChange_apply]
    exact ContinuousLinearMap.zero_comp _
  rw [h_clm, h_zero,
      (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange_self
        (achart ℂ y) y hy_in_y (om.toFun y)] at h_comp
  change om.toFun y = 0
  exact h_comp.symm

end DiskChartCover

end JacobianChallenge

end
