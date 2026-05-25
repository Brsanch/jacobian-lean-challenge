/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalPompeiuSolutionGlobalPartialZBar
import JacobianChallenge.Manifold.ChartPompeiuKernel
import JacobianChallenge.Manifold.PartialZBarChainRule

/-! # Chip 5.4c-final — manifold-side identity for `chartPompeiuSolution`

The cutoff-free Pompeiu solution

```
chartPompeiuSolution i P α y :=
  pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α)) ((chartAt ℂ i.val) y)
```

(introduced in Sub-chip 5.4c-prep) is the chart-x_i view of a global
Pompeiu inverse. This file derives the manifold-side identity:

```
partialZBarManifold (chartPompeiuSolution i P α) y *
    conj(deriv (chart_y ∘ chart_xi.symm) ((chart_xi) y))
  = (P.rhoC i * α) y
```

for `y ∈ (chartAt ℂ i.val).source`. The structure mirrors Chip 4's
`partialZBarManifold_pompeiuKernelChart_eq_α_mul_transition`, but
applied to the `chartPullbackZero`-fed Pompeiu kernel instead of the
bare-composition input.

Strategy: use Chip 4's **content-agnostic** bridge
`partialZBar_chart_x_eq_manifold_mul_transition`, which relates the
chart-x view ∂̄ to the manifold-side ∂̄ via the transition factor for
any `f` with appropriate differentiability. We instantiate it with
`f := chartPompeiuSolution i P α`. The chart-x view ∂̄ collapses via
Chip 3c-F-4 + Sub-chip 5.3a's `chartPullbackZero_eq_α_chartSymm_on_target`
+ `chart_xi.left_inv`, giving `(P.rhoC i * α) y`.

The required differentiability `DifferentiableAt ℝ
(chartPompeiuSolution i P α ∘ chart_y.symm) (chart_y y)` follows from
composing the global `C^∞` smoothness of `pompeiuKernel (chartPullbackZero …)`
(Chip 2d + Sub-chips 5.3a/5.3b) with the chart transition
`chart_xi ∘ chart_y.symm` (analytic via `analyticAt_chart_transition_of_isManifold`,
needing `[IsManifold 𝓘(ℂ, ℂ) ω X]`).

## Main result

* `partialZBarManifold_chartPompeiuSolution_eq_α_mul_transition` — the
  headline identity.

No `sorry`, no `axiom`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open scoped Manifold Topology ContDiff
open Set Function Filter
open JacobianChallenge.PompeiuKernel

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℝ, ℂ) ⊤ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  {cover : FiniteChartCover X}

/-! ## Local scalar-tower workaround (mirrors Chip 4) -/

@[reducible] private def isScalarTower_R_C_C_local : IsScalarTower ℝ ℂ ℂ :=
  ⟨fun (r : ℝ) (c c' : ℂ) => by
    show (r • c) • c' = r • c • c'
    rw [smul_assoc]⟩

private theorem differentiableAt_restrictScalars_R_C_C_local
    {f : ℂ → ℂ} {x : ℂ} (h : DifferentiableAt ℂ f x) :
    DifferentiableAt ℝ f x :=
  @DifferentiableAt.restrictScalars ℝ _ ℂ _ _ ℂ _ _ _ isScalarTower_R_C_C_local
    ℂ _ _ _ isScalarTower_R_C_C_local _ _ h

/-! ## Differentiability of `chartPompeiuSolution ∘ chart_y.symm` at `chart_y y` -/

/-- Differentiability of the chart-pullback of `chartPompeiuSolution` at
the chart-y view of `y`, for `y ∈ (chartAt ℂ i.val).source`. The
composition is `pompeiuKernel (chartPullbackZero …) ∘ chart_xi ∘ chart_y.symm`,
which is differentiable at `chart_y y` because:

* `pompeiuKernel (chartPullbackZero …)` is `C^∞` globally on `ℂ`
  (Chip 2d + Sub-chips 5.3a/5.3b);
* `chart_xi ∘ chart_y.symm` is the chart-transition map, ℂ-analytic
  at `chart_y y` (`analyticAt_chart_transition_of_isManifold`),
  hence `ℝ`-differentiable. -/
theorem differentiableAt_chartPompeiuSolution_chart_y_symm
    [CompactSpace X] (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints}) (α : X → ℂ)
    (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α)
    {y : X} (hy : y ∈ (chartAt ℂ i.val).source) :
    DifferentiableAt ℝ
      ((chartPompeiuSolution i P α) ∘ (chartAt ℂ y).symm)
      ((chartAt ℂ y) y) := by
  -- pompeiuKernel input is ContDiff ℝ ∞ + HasCompactSupport.
  have h_tsupport :
      tsupport (P.rhoC i * α) ⊆ (chartAt ℂ i.val).source :=
    tsupport_partition_mul_subset_chart_source P i α
  have h_prod_smooth :
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (P.rhoC i * α) :=
    contMDiff_partition_mul P i α h_α
  have h_cpz_smooth :
      ContDiff ℝ ∞ (chartPullbackZero i.val (P.rhoC i * α)) :=
    contDiff_chartPullbackZero i.val (P.rhoC i * α) h_prod_smooth h_tsupport
  have h_cpz_cs :
      HasCompactSupport (chartPullbackZero i.val (P.rhoC i * α)) :=
    hasCompactSupport_chartPullbackZero i.val h_tsupport
  -- pompeiuKernel (chartPullbackZero …) is C^∞ globally on ℂ.
  have h_pk_smooth :
      ContDiff ℝ ∞ (pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))) :=
    contDiff_pompeiuKernel_infty h_cpz_smooth h_cpz_cs
  -- Differentiable at chart_xi (chart_y.symm (chart_y y)).
  have h_pk_diff_at : DifferentiableAt ℝ
      (pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α)))
      (((chartAt ℂ i.val) ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y)) := by
    have h_one_ne : ((1 : ℕ) : WithTop ℕ∞) ≠ 0 := by decide
    -- Reduce ContDiff ℝ ∞ ⇒ Differentiable at any point.
    have h_diff : Differentiable ℝ
        (pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))) :=
      (h_pk_smooth.of_le (by exact_mod_cast le_top : (1 : ℕ∞) ≤ ∞)).differentiable h_one_ne
    exact h_diff.differentiableAt
  -- Chart transition chart_xi ∘ chart_y.symm is ℂ-analytic at chart_y y.
  have h_xi_atlas : chartAt ℂ i.val ∈ atlas ℂ X := chart_mem_atlas ℂ i.val
  have h_y_atlas : chartAt ℂ y ∈ atlas ℂ X := chart_mem_atlas ℂ y
  have h_y_in_ysrc : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  have h_an_trans : AnalyticAt ℂ ((chartAt ℂ i.val) ∘ (chartAt ℂ y).symm)
      ((chartAt ℂ y) y) :=
    JacobianChallenge.analyticAt_chart_transition_of_isManifold
      h_y_atlas h_xi_atlas h_y_in_ysrc hy
  have h_trans_diff_at_R : DifferentiableAt ℝ
      ((chartAt ℂ i.val) ∘ (chartAt ℂ y).symm)
      ((chartAt ℂ y) y) :=
    differentiableAt_restrictScalars_R_C_C_local h_an_trans.differentiableAt
  -- Compose.
  exact h_pk_diff_at.comp ((chartAt ℂ y) y) h_trans_diff_at_R

/-! ## Chart-x view of `partialZBar` evaluates to `(P.rhoC i * α) y` -/

/-- The chart-x_i view `partialZBar` of `chartPompeiuSolution i P α`,
evaluated at the chart image of `y ∈ chart_xi.source`, recovers
`(P.rhoC i * α) y`.

Reduces to: `chartPompeiuSolution i P α ∘ chart_xi.symm` agrees with
`pompeiuKernel (chartPullbackZero …)` on an open neighborhood of
`chart_xi y` (specifically on `chart_xi.target`, via
`chart_xi.right_inv`), so the chart-x view `partialZBar` equals
`partialZBar (pompeiuKernel (chartPullbackZero …)) (chart_xi y)`
(germ-dependence), which equals `chartPullbackZero … (chart_xi y) =
(P.rhoC i * α) y` by Chip 3c-F-4 + Sub-chip 5.3a + `chart_xi.left_inv`. -/
theorem partialZBar_chartPompeiuSolution_chart_xi_symm_eq
    [CompactSpace X] (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints}) (α : X → ℂ)
    (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α)
    {y : X} (hy : y ∈ (chartAt ℂ i.val).source) :
    partialZBar ((chartPompeiuSolution i P α) ∘ (chartAt ℂ i.val).symm)
        ((chartAt ℂ i.val) y)
      = (P.rhoC i * α) y := by
  -- Local agreement on chart_xi.target via chart_xi.right_inv.
  have h_target_open : IsOpen (chartAt ℂ i.val).target :=
    (chartAt ℂ i.val).open_target
  have h_chart_xi_y_target : (chartAt ℂ i.val) y ∈ (chartAt ℂ i.val).target :=
    (chartAt ℂ i.val).map_source hy
  have h_evEq :
      ((chartPompeiuSolution i P α) ∘ (chartAt ℂ i.val).symm)
        =ᶠ[𝓝 ((chartAt ℂ i.val) y)]
        (pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))) := by
    filter_upwards [h_target_open.mem_nhds h_chart_xi_y_target] with ζ hζ
    -- chartPompeiuSolution z := pompeiuKernel ... (chart_xi z); applied at chart_xi.symm ζ.
    -- chart_xi (chart_xi.symm ζ) = ζ by right_inv (for ζ ∈ chart_xi.target).
    show pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))
            ((chartAt ℂ i.val) ((chartAt ℂ i.val).symm ζ))
        = pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α)) ζ
    rw [(chartAt ℂ i.val).right_inv hζ]
  -- Germ-dependence of partialZBar via fderiv_eq.
  have h_pZ_congr :
      partialZBar ((chartPompeiuSolution i P α) ∘ (chartAt ℂ i.val).symm)
          ((chartAt ℂ i.val) y)
        = partialZBar (pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α)))
            ((chartAt ℂ i.val) y) := by
    unfold partialZBar
    rw [Filter.EventuallyEq.fderiv_eq h_evEq]
  rw [h_pZ_congr]
  -- Chip 3c-F-4 (with hypotheses derived from 5.3a/5.3b).
  have h_tsupport :
      tsupport (P.rhoC i * α) ⊆ (chartAt ℂ i.val).source :=
    tsupport_partition_mul_subset_chart_source P i α
  have h_prod_smooth :
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (P.rhoC i * α) :=
    contMDiff_partition_mul P i α h_α
  have h_cpz_smooth :
      ContDiff ℝ ∞ (chartPullbackZero i.val (P.rhoC i * α)) :=
    contDiff_chartPullbackZero i.val (P.rhoC i * α) h_prod_smooth h_tsupport
  have h_cpz_C1 :
      ContDiff ℝ 1 (chartPullbackZero i.val (P.rhoC i * α)) :=
    h_cpz_smooth.of_le (by exact_mod_cast le_top)
  have h_cpz_cs :
      HasCompactSupport (chartPullbackZero i.val (P.rhoC i * α)) :=
    hasCompactSupport_chartPullbackZero i.val h_tsupport
  rw [partialZBar_pompeiuKernel_eq_self h_cpz_C1 h_cpz_cs ((chartAt ℂ i.val) y)]
  -- chartPullbackZero on target = (P.rhoC i * α) ∘ chart_xi.symm.
  rw [chartPullbackZero_eq_α_chartSymm_on_target i.val (P.rhoC i * α) h_chart_xi_y_target]
  -- chart_xi.symm (chart_xi y) = y via left_inv.
  show (P.rhoC i * α) ((chartAt ℂ i.val).symm ((chartAt ℂ i.val) y))
      = (P.rhoC i * α) y
  rw [(chartAt ℂ i.val).left_inv hy]

/-! ## Headline: manifold-side identity with chart-transition factor -/

/-- **Chip 5.4c-final.** Manifold-side `∂̄` identity for
`chartPompeiuSolution`, with the chart-transition factor:

```
partialZBarManifold (chartPompeiuSolution i P α) y *
    conj(deriv (chartAt ℂ y ∘ (chartAt ℂ i.val).symm) ((chartAt ℂ i.val) y))
  = (P.rhoC i * α) y.
```

Combines `partialZBar_chartPompeiuSolution_chart_xi_symm_eq` (LHS of
the bridge, equals `(P.rhoC i * α) y`) with Chip 4's content-agnostic
`partialZBar_chart_x_eq_manifold_mul_transition` (RHS rewrite, picks
up the transition factor). The required differentiability of
`chartPompeiuSolution ∘ chart_y.symm` at `chart_y y` is supplied by
`differentiableAt_chartPompeiuSolution_chart_y_symm`. -/
theorem partialZBarManifold_chartPompeiuSolution_eq_α_mul_transition
    [CompactSpace X] (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints}) (α : X → ℂ)
    (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α)
    {y : X} (hy : y ∈ (chartAt ℂ i.val).source) :
    JacobianChallenge.partialZBarManifold (chartPompeiuSolution i P α) y *
      (starRingEnd ℂ)
        (deriv ((chartAt ℂ y) ∘ (chartAt ℂ i.val).symm) ((chartAt ℂ i.val) y))
      = (P.rhoC i * α) y := by
  -- Differentiability for the bridge.
  have h_diff :
      DifferentiableAt ℝ
        ((chartPompeiuSolution i P α) ∘ (chartAt ℂ y).symm)
        ((chartAt ℂ y) y) :=
    differentiableAt_chartPompeiuSolution_chart_y_symm P i α h_α hy
  -- Apply the Chip 4 bridge (content-agnostic).
  have h_bridge :=
    JacobianChallenge.PompeiuKernel.partialZBar_chart_x_eq_manifold_mul_transition
      (f := chartPompeiuSolution i P α) (x := i.val) (y := y) hy h_diff
  -- h_bridge : partialZBar (chartPompeiuSolution ∘ chart_xi.symm) (chart_xi y) =
  --            partialZBarManifold (chartPompeiuSolution) y * conj(...)
  -- The LHS equals (P.rhoC i * α) y by `partialZBar_chartPompeiuSolution_chart_xi_symm_eq`.
  rw [partialZBar_chartPompeiuSolution_chart_xi_symm_eq P i α h_α hy] at h_bridge
  exact h_bridge.symm

end JacobianChallenge

end
