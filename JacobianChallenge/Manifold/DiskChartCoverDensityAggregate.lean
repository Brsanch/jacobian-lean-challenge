/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverDensityPerX

set_option linter.unusedSectionVars false

/-! # Aggregate density bound: `seminormVal ≤ M · seminormValInner`

Aggregating the per-`y` density bound across all `y ∈ basePoints` and
then across all `x ∈ basePoints`, we obtain the **outer-bounded-by-inner
density inequality**:

```
∃ M ≥ 0, ∀ om, seminormVal cover om ≤ M · seminormValInner cover om
```

This is the Forster (i) multi-chart density bound headline. Applied
to `om := om_n - om_lim` (linearity), it transfers inner-norm
convergence to outer-norm convergence — the bridge needed for the closed
outer ball to be sequentially compact in outer norm (and thus, via
Riesz, `FiniteDimensional ℂ HolomorphicOneFormCovered`).

No `sorry`, no `axiom`.
-/

open Set Metric

open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **Per-`x` density bound (existential form).** For each base point
`x`, there exists a nonneg constant `M_x` such that for every `om` and
every `w ∈ closedBall outerRadius` at `x`:
`‖localCoeff om x w‖ ≤ M_x · seminormValInner cover om`. -/
theorem exists_perX_density_bound
    [T2Space X] (cover : DiskChartCover X) [Nonempty X]
    {x : X} (hx : x ∈ cover.basePoints) :
    ∃ M_x : ℝ, 0 ≤ M_x ∧ ∀ (om : HolomorphicOneForm X)
        (w : ℂ), w ∈ closedBall ((chartAt ℂ x) x) (cover.outerRadius x) →
      ‖HolomorphicOneForm.localCoeff om x w‖
        ≤ M_x * seminormValInner cover om := by
  classical
  -- Per-y constants (om-independent).
  let C_of : (y : X) → y ∈ cover.basePoints → ℝ := fun y hy =>
    (cover.norm_localCoeff_le_seminormValInner_bound hx hy).choose
  have C_of_spec : ∀ (y : X) (hy : y ∈ cover.basePoints),
      0 ≤ C_of y hy ∧
      ∀ (om : HolomorphicOneForm X) (q : X),
        q ∈ cover.outerDiskX x ∩ cover.closedInnerDiskX y →
        ‖HolomorphicOneForm.localCoeff om x ((chartAt ℂ x) q)‖
          ≤ C_of y hy * seminormValInner cover om :=
    fun y hy =>
      (cover.norm_localCoeff_le_seminormValInner_bound hx hy).choose_spec
  -- Take M_x := sup of C_of over basePoints (finite Finset).
  set M_x : ℝ := cover.basePoints.attach.sup'
    (cover.basePoints_nonempty.attach)
    (fun y => C_of y.val y.property) with hMx_def
  have M_x_nonneg : 0 ≤ M_x := by
    -- M_x ≥ C_of for some y in basePoints ≥ 0.
    obtain ⟨y0, hy0⟩ := cover.basePoints_nonempty
    refine le_trans (C_of_spec y0 hy0).1 ?_
    rw [hMx_def]
    exact Finset.le_sup'
      (f := fun z : {y // y ∈ cover.basePoints} => C_of z.val z.property)
      (s := cover.basePoints.attach) (Finset.mem_attach _ ⟨y0, hy0⟩)
  refine ⟨M_x, M_x_nonneg, fun om w hw => ?_⟩
  -- Set q := (chartAt x).symm w ∈ outerDiskX x.
  have hw_in_target : w ∈ (chartAt ℂ x).target :=
    cover.closedDisk_in_target x hx hw
  set q : X := (chartAt ℂ x).symm w with hq_def
  have hq_outer : q ∈ cover.outerDiskX x :=
    ⟨w, hw, rfl⟩
  have h_chart_q : (chartAt ℂ x) q = w := by
    rw [hq_def, (chartAt ℂ x).right_inv hw_in_target]
  -- Find y(q) ∈ basePoints with q ∈ closedInnerDiskX y(q).
  obtain ⟨y, hy_base, hy_mem⟩ := mem_iUnion₂.mp
    (cover.outerDiskX_subset_iUnion_closedInnerDiskX x hq_outer)
  -- Apply per-y bound.
  have h_inner : q ∈ cover.outerDiskX x ∩ cover.closedInnerDiskX y :=
    ⟨hq_outer, hy_mem⟩
  have h_bd := (C_of_spec y hy_base).2 om q h_inner
  -- Replace `(chartAt x) q` with `w`.
  rw [h_chart_q] at h_bd
  -- And bound C_of y hy_base ≤ M_x.
  have h_C_le_M : C_of y hy_base ≤ M_x := by
    rw [hMx_def]
    exact Finset.le_sup'
      (f := fun z : {y // y ∈ cover.basePoints} => C_of z.val z.property)
      (s := cover.basePoints.attach) (Finset.mem_attach _ ⟨y, hy_base⟩)
  -- Combine.
  refine h_bd.trans ?_
  exact mul_le_mul_of_nonneg_right h_C_le_M
    (seminormValInner_nonneg cover om)

/-- **Aggregate density headline: `seminormVal ≤ M · seminormValInner`.** -/
theorem exists_density_bound
    [T2Space X] (cover : DiskChartCover X) [Nonempty X] :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (om : HolomorphicOneForm X),
      seminormVal cover om ≤ M * seminormValInner cover om := by
  classical
  -- Per-x constants.
  let M_of : (x : X) → x ∈ cover.basePoints → ℝ := fun x hx =>
    (cover.exists_perX_density_bound hx).choose
  have M_of_spec : ∀ (x : X) (hx : x ∈ cover.basePoints),
      0 ≤ M_of x hx ∧
      ∀ (om : HolomorphicOneForm X)
        (w : ℂ), w ∈ closedBall ((chartAt ℂ x) x) (cover.outerRadius x) →
        ‖HolomorphicOneForm.localCoeff om x w‖
          ≤ M_of x hx * seminormValInner cover om :=
    fun x hx => (cover.exists_perX_density_bound hx).choose_spec
  -- Take M := sup of M_of over basePoints.
  set M : ℝ := cover.basePoints.attach.sup'
    (cover.basePoints_nonempty.attach)
    (fun x => M_of x.val x.property) with hM_def
  have M_nonneg : 0 ≤ M := by
    obtain ⟨x0, hx0⟩ := cover.basePoints_nonempty
    refine le_trans (M_of_spec x0 hx0).1 ?_
    rw [hM_def]
    exact Finset.le_sup'
      (f := fun z : {x // x ∈ cover.basePoints} => M_of z.val z.property)
      (s := cover.basePoints.attach) (Finset.mem_attach _ ⟨x0, hx0⟩)
  refine ⟨M, M_nonneg, fun om => ?_⟩
  -- seminormVal cover om = max over x ∈ basePoints of localCoeffMax cover x om.
  -- Need: localCoeffMax cover x om ≤ M_of x · seminormValInner ≤ M · seminormValInner.
  -- Then sup' on LHS ≤ M · seminormValInner.
  unfold seminormVal
  refine Finset.sup'_le _ _ ?_
  intro x hx
  -- Goal: localCoeffMax cover x om ≤ M · seminormValInner cover om.
  -- localCoeffMax is sSup over the outer closed ball.
  have h_perX_bound :
      ∀ w ∈ closedBall ((chartAt ℂ x) x) (cover.outerRadius x),
        ‖HolomorphicOneForm.localCoeff om x w‖
          ≤ M * seminormValInner cover om := by
    intro w hw
    refine ((M_of_spec x hx).2 om w hw).trans ?_
    -- M_of x hx ≤ M.
    have h_M_of_le_M : M_of x hx ≤ M := by
      rw [hM_def]
      exact Finset.le_sup'
        (f := fun z : {x // x ∈ cover.basePoints} => M_of z.val z.property)
        (s := cover.basePoints.attach) (Finset.mem_attach _ ⟨x, hx⟩)
    exact mul_le_mul_of_nonneg_right h_M_of_le_M
      (seminormValInner_nonneg cover om)
  -- Now localCoeffMax cover x om = sSup of ‖localCoeff om x ·‖ on outer disk ≤ M · ....
  unfold localCoeffMax
  refine csSup_le ?_ ?_
  · -- Nonempty image: chart center is in its own outer ball.
    refine ⟨_, (chartAt ℂ x) x, ?_, rfl⟩
    rw [mem_closedBall, dist_self]
    exact (cover.outerRadius_pos x hx).le
  · rintro y ⟨w, hw, rfl⟩
    exact h_perX_bound w hw

end DiskChartCover

end JacobianChallenge

end
