/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormChartCoeffOnTarget
import JacobianChallenge.Manifold.CompactDiskChartCover
import Mathlib.Data.Real.Pointwise
import Mathlib.Algebra.Group.Pointwise.Set.Scalar

set_option diagnostics.threshold 100

/-! # Per-chart sup of `‖localCoeff om x ·‖` on the outer closed disk

For each base point `x` in a `DiskChartCover X` and each holomorphic
1-form `om : HolomorphicOneForm X`, define

```
DiskChartCover.localCoeffMax cover x om := sSup ‖localCoeff om x ·‖ '' closedBall ((chartAt ℂ x) x) (outerRadius x)
```

This per-chart sup is well-defined (image is bounded above since
`localCoeff om x` is continuous on the chart target, which contains
the outer closed disk, and the closed disk is compact), non-negative,
and pointwise linear in `om`:

* `localCoeffMax_zero` — zero form gives 0.
* `localCoeffMax_add_le` — subadditivity.
* `localCoeffMax_neg` — sign-invariance.
* `localCoeffMax_smul` — scalar homogeneity.

The seminorm `seminormVal cover om` defined as
`Finset.sup' basePoints _ (fun x => localCoeffMax cover x om)` and its
properties (separating, subadditive, ...) live in a downstream chip;
this file is just the per-chart sup foundation.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff Pointwise
open Set Metric HolomorphicOneForm

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-! ## Continuity of the local coefficient on the outer closed disk -/

/-- `localCoeff om x` is continuous on `(chartAt ℂ x).target`. -/
private lemma localCoeff_continuousOn_target (om : HolomorphicOneForm X) (x : X) :
    ContinuousOn (localCoeff om x) (chartAt ℂ x).target :=
  (localCoeff_differentiableOn om x).continuousOn

/-- For a base point `x` in the cover, the outer closed disk is in the
chart target, hence `localCoeff om x` is continuous on the outer
closed disk. -/
private lemma localCoeff_continuousOn_outerDisk (cover : DiskChartCover X)
    (om : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints) :
    ContinuousOn (localCoeff om x)
      (closedBall ((chartAt ℂ x) x) (cover.outerRadius x)) :=
  (localCoeff_continuousOn_target om x).mono (cover.closedDisk_in_target x hx)

/-- The norm composed with `localCoeff om x` is continuous on the
outer closed disk. -/
private lemma norm_localCoeff_continuousOn_outerDisk
    (cover : DiskChartCover X) (om : HolomorphicOneForm X)
    {x : X} (hx : x ∈ cover.basePoints) :
    ContinuousOn (fun w => ‖localCoeff om x w‖)
      (closedBall ((chartAt ℂ x) x) (cover.outerRadius x)) :=
  continuous_norm.continuousOn.comp
    (localCoeff_continuousOn_outerDisk cover om hx) (mapsTo_image _ _)

/-! ## The outer closed disk is compact and nonempty -/

omit [IsManifold 𝓘(ℂ) ω X] in
private lemma outerDisk_nonempty (cover : DiskChartCover X) {x : X}
    (hx : x ∈ cover.basePoints) :
    (closedBall ((chartAt ℂ x) x) (cover.outerRadius x)).Nonempty :=
  ⟨(chartAt ℂ x) x, mem_closedBall_self
    (le_of_lt (cover.outerRadius_pos x hx))⟩

omit [IsManifold 𝓘(ℂ) ω X] in
private lemma outerDisk_isCompact (cover : DiskChartCover X) (x : X) :
    IsCompact (closedBall ((chartAt ℂ x) x) (cover.outerRadius x)) :=
  isCompact_closedBall _ _

/-! ## Boundedness of the image of `‖localCoeff om x ·‖` -/

private lemma norm_localCoeff_image_bddAbove (cover : DiskChartCover X)
    (om : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints) :
    BddAbove ((fun w => ‖localCoeff om x w‖) ''
      closedBall ((chartAt ℂ x) x) (cover.outerRadius x)) := by
  have h_compact := outerDisk_isCompact cover x
  have h_ne := outerDisk_nonempty cover hx
  have h_cont := norm_localCoeff_continuousOn_outerDisk cover om hx
  rcases h_compact.exists_isMaxOn h_ne h_cont with ⟨w_max, hw_max_mem, hw_max⟩
  refine ⟨‖localCoeff om x w_max‖, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact hw_max hw

private lemma norm_localCoeff_image_nonempty (cover : DiskChartCover X)
    (om : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints) :
    ((fun w => ‖localCoeff om x w‖) ''
      closedBall ((chartAt ℂ x) x) (cover.outerRadius x)).Nonempty := by
  obtain ⟨w, hw⟩ := outerDisk_nonempty cover hx
  exact ⟨_, w, hw, rfl⟩

/-! ## Definition of `localCoeffMax` -/

/-- The sup of `‖localCoeff om x ·‖` over the outer closed disk at `x`. -/
def localCoeffMax (cover : DiskChartCover X) (x : X)
    (om : HolomorphicOneForm X) : ℝ :=
  sSup ((fun w => ‖localCoeff om x w‖) '' closedBall ((chartAt ℂ x) x)
    (cover.outerRadius x))

/-! ## Sup is a pointwise upper bound -/

/-- For any `w` in the outer closed disk, the local coefficient's norm
is bounded above by `localCoeffMax`. -/
theorem norm_localCoeff_le_localCoeffMax (cover : DiskChartCover X)
    (om : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints)
    {w : ℂ} (hw : w ∈ closedBall ((chartAt ℂ x) x) (cover.outerRadius x)) :
    ‖localCoeff om x w‖ ≤ localCoeffMax cover x om := by
  unfold localCoeffMax
  exact le_csSup (norm_localCoeff_image_bddAbove cover om hx) ⟨w, hw, rfl⟩

/-! ## Properties of `localCoeffMax` -/

/-- The per-chart sup is non-negative. -/
theorem localCoeffMax_nonneg (cover : DiskChartCover X)
    (om : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints) :
    0 ≤ localCoeffMax cover x om := by
  obtain ⟨w, hw⟩ := outerDisk_nonempty cover hx
  exact (norm_nonneg _).trans
    (norm_localCoeff_le_localCoeffMax cover om hx hw)

/-- The per-chart sup of the zero form is zero. -/
@[simp]
theorem localCoeffMax_zero (cover : DiskChartCover X) {x : X}
    (hx : x ∈ cover.basePoints) :
    localCoeffMax cover x (0 : HolomorphicOneForm X) = 0 := by
  unfold localCoeffMax
  -- `localCoeff (0 : HolomorphicOneForm X) x = 0` (as a function),
  -- so `‖localCoeff 0 x w‖ = 0` for all w; image is constant.
  rw [HolomorphicOneForm.localCoeff_zero]
  -- Goal: sSup ((fun w => ‖(0 : ℂ → ℂ) w‖) '' closedBall ...) = 0
  have h_image : ((fun w => ‖(0 : ℂ → ℂ) w‖) ''
      closedBall ((chartAt ℂ x) x) (cover.outerRadius x)) = {(0 : ℝ)} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · obtain ⟨w, hw⟩ := outerDisk_nonempty cover hx
      exact ⟨w, hw, by simp⟩
    · rintro y ⟨w, _hw, rfl⟩
      simp
  rw [h_image]
  exact csSup_singleton (0 : ℝ)

/-- Per-chart sup is monotone in the form: if `‖localCoeff om₁ x w‖ ≤
‖localCoeff om₂ x w‖` for all `w` in the outer closed disk, the same
inequality holds for the sup. -/
private lemma localCoeffMax_le_of_norm_le (cover : DiskChartCover X)
    (om₁ om₂ : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints)
    (h : ∀ w ∈ closedBall ((chartAt ℂ x) x) (cover.outerRadius x),
      ‖localCoeff om₁ x w‖ ≤ ‖localCoeff om₂ x w‖) :
    localCoeffMax cover x om₁ ≤ localCoeffMax cover x om₂ := by
  unfold localCoeffMax
  refine csSup_le (norm_localCoeff_image_nonempty cover om₁ hx) ?_
  rintro y ⟨w, hw, rfl⟩
  exact (h w hw).trans
    (norm_localCoeff_le_localCoeffMax cover om₂ hx hw)

/-- Subadditivity of `localCoeffMax`. -/
theorem localCoeffMax_add_le (cover : DiskChartCover X)
    (om₁ om₂ : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints) :
    localCoeffMax cover x (om₁ + om₂)
      ≤ localCoeffMax cover x om₁ + localCoeffMax cover x om₂ := by
  unfold localCoeffMax
  refine csSup_le (norm_localCoeff_image_nonempty cover (om₁ + om₂) hx) ?_
  rintro y ⟨w, hw, rfl⟩
  -- Goal: `(fun w => ‖(om₁ + om₂).localCoeff x w‖) w ≤ sSup ... + sSup ...`
  -- Beta-reduce the lambda application.
  show ‖localCoeff (om₁ + om₂) x w‖ ≤ _
  -- localCoeff (om₁ + om₂) x = localCoeff om₁ x + localCoeff om₂ x (function eq).
  have h_pt : localCoeff (om₁ + om₂) x w
      = localCoeff om₁ x w + localCoeff om₂ x w := by
    have := HolomorphicOneForm.localCoeff_add om₁ om₂ x
    -- `this : localCoeff (om₁ + om₂) x = localCoeff om₁ x + localCoeff om₂ x`
    rw [this]; rfl
  rw [h_pt]
  refine (norm_add_le _ _).trans ?_
  exact add_le_add
    (norm_localCoeff_le_localCoeffMax cover om₁ hx hw)
    (norm_localCoeff_le_localCoeffMax cover om₂ hx hw)

/-- Sign-invariance of `localCoeffMax`. -/
theorem localCoeffMax_neg (cover : DiskChartCover X)
    (om : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints) :
    localCoeffMax cover x (-om) = localCoeffMax cover x om := by
  have h_pt : ∀ w, localCoeff (-om) x w = -localCoeff om x w := by
    intro w
    have := HolomorphicOneForm.localCoeff_neg om x
    rw [this]; rfl
  apply le_antisymm
  · refine localCoeffMax_le_of_norm_le cover (-om) om hx ?_
    intro w _hw
    rw [h_pt, norm_neg]
  · refine localCoeffMax_le_of_norm_le cover om (-om) hx ?_
    intro w _hw
    rw [h_pt, norm_neg]

/-- Scalar homogeneity of `localCoeffMax`. -/
theorem localCoeffMax_smul (cover : DiskChartCover X)
    (c : ℂ) (om : HolomorphicOneForm X) {x : X} (_hx : x ∈ cover.basePoints) :
    localCoeffMax cover x (c • om) = ‖c‖ * localCoeffMax cover x om := by
  unfold localCoeffMax
  -- localCoeff (c • om) x w = c • localCoeff om x w (pointwise).
  have h_pt : ∀ w, ‖localCoeff (c • om) x w‖ = ‖c‖ * ‖localCoeff om x w‖ := by
    intro w
    have hsmul := HolomorphicOneForm.localCoeff_smul c om x
    -- `hsmul : localCoeff (c • om) x = c • localCoeff om x` (functions).
    have : localCoeff (c • om) x w = c • localCoeff om x w := by rw [hsmul]; rfl
    rw [this]
    simp [smul_eq_mul]
  -- Rewrite the image as `‖c‖ • (norm-of-localCoeff image)`.
  have h_image_smul :
      ((fun w => ‖localCoeff (c • om) x w‖) ''
        closedBall ((chartAt ℂ x) x) (cover.outerRadius x))
      = ((‖c‖ : ℝ) • ((fun w => ‖localCoeff om x w‖) ''
          closedBall ((chartAt ℂ x) x) (cover.outerRadius x))) := by
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
  -- Goal: ‖c‖ • sSup (...) = ‖c‖ * sSup (...). On ℝ, `•` is `*`.
  rfl

end DiskChartCover

end JacobianChallenge

end
