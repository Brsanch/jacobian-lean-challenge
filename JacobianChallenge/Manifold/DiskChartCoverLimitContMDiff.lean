/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverLimitSmooth
import JacobianChallenge.Manifold.DiskChartCoverLimitAnalytic

set_option diagnostics.threshold 100

/-! # Smoothness of the chart-frame representative on the inner ball

For each base point `x ∈ basePoints`, the chart-`x`-frame representative
of the limit section `y' ↦ coordChange (achart y') (achart x) y'
(limitSectionToFun y')` is `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω` at every
`y` in chart-`x` preimage of the *open* inner ball `ball ((chartAt ℂ x)
x) (innerRadius x)`.

The proof composes:
1. Chip 5h's chart-frame CLM identification: on chart-`x` preimage of
   the *closed* inner disk, the chart-`x`-frame value of the limit
   section equals `smulRight 1 (bcfExtend cover g_lim_x (chart-x y'))`.
2. Chip 5f's analyticity: `bcfExtend cover g_lim_x` is `AnalyticOn ℂ`
   on the open ball.
3. Smoothness of `chart-x : X → ℂ` on `chart-x.source`.
4. ContMDiff composition.

This is the analytic-smoothness input for the section-level smoothness
via mathlib's `Trivialization.contMDiffAt_section_iff`.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff Pointwise
open Set Metric HolomorphicOneForm Filter

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

omit [IsManifold 𝓘(ℂ) ω X] in
/-- `c ↦ smulRight 1 c : ℂ → (ℂ →L[ℂ] ℂ)` is `ContMDiff`. -/
private lemma smulRightOne_contMDiff :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun c : ℂ => ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c) :=
  (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (1 : ℂ →L[ℂ] ℂ)).contMDiff

/-- For each base point `x ∈ basePoints` and `y` in chart-`x` preimage
of the *open* inner ball, the composed function `y' ↦ smulRight 1
(bcfExtend cover g_lim_x ((chartAt ℂ x) y'))` is `ContMDiffAt
𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω` at `y`. -/
theorem composed_smulRight_bcfExtend_contMDiffAt
    (cover : DiskChartCover X) [Nonempty X]
    (om_n : ℕ → HolomorphicOneForm X)
    {x : X} (hx : x ∈ cover.basePoints)
    {g_lim_x : BoundedContinuousFunction
        ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ}
    (h_tendsto :
      Tendsto (fun k => localCoeffBcf cover (om_n k) hx) atTop (𝓝 g_lim_x))
    {y : X} (hy_source : y ∈ (chartAt ℂ x).source)
    (hy_in_ball : (chartAt ℂ x) y ∈
      ball ((chartAt ℂ x) x) (cover.innerRadius x)) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun y' : X => ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        (bcfExtend cover g_lim_x ((chartAt ℂ x) y'))) y := by
  -- Step 1: chart-x is ContMDiffAt y.
  have h_chart_smooth : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      ((chartAt ℂ x) : X → ℂ) y := by
    have hi_max : (chartAt ℂ x) ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X :=
      IsManifold.chart_mem_maximalAtlas x
    have h_on : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (chartAt ℂ x : X → ℂ)
        (chartAt ℂ x).source :=
      contMDiffOn_of_mem_maximalAtlas hi_max
    exact h_on.contMDiffAt ((chartAt ℂ x).open_source.mem_nhds hy_source)
  -- Step 2: bcfExtend is DifferentiableAt (and hence ContMDiffAt) at chart-x y.
  have h_bcfExtend_diff_at :
      DifferentiableAt ℂ (bcfExtend cover g_lim_x) ((chartAt ℂ x) y) := by
    have h_diff_on :=
      limit_differentiableOn_innerBall cover om_n hx h_tendsto
    exact h_diff_on.differentiableAt (isOpen_ball.mem_nhds hy_in_ball)
  -- Convert DifferentiableAt to ContMDiffAt at regularity ω.
  -- AnalyticAt ⇒ ContDiffAt ω ⇒ ContMDiffAt ω.
  have h_analyticAt :
      AnalyticAt ℂ (bcfExtend cover g_lim_x) ((chartAt ℂ x) y) := by
    have h_analytic_on := limit_analyticOn_innerBall cover om_n hx h_tendsto
    exact h_analytic_on.analyticAt (isOpen_ball.mem_nhds hy_in_ball)
  have h_contDiffAt : ContDiffAt ℂ ω (bcfExtend cover g_lim_x)
      ((chartAt ℂ x) y) :=
    h_analyticAt.contDiffAt
  have h_bcfExtend_smooth : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (bcfExtend cover g_lim_x) ((chartAt ℂ x) y) :=
    contMDiffAt_iff_contDiffAt.mpr h_contDiffAt
  -- Step 3: Compose chart-x with bcfExtend.
  have h_comp : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun y' : X => bcfExtend cover g_lim_x ((chartAt ℂ x) y')) y :=
    h_bcfExtend_smooth.comp y h_chart_smooth
  -- Step 4: Apply smulRight 1 (continuous linear).
  exact smulRightOne_contMDiff.contMDiffAt.comp y h_comp

end DiskChartCover

end JacobianChallenge

end
