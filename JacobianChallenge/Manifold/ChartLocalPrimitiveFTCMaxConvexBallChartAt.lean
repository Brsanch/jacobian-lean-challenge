/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartLocalPrimitiveSmoothExtMaxConvexBallChartAt
import JacobianChallenge.Manifold.ChartLocalPrimitiveFTCChartAt
import JacobianChallenge.Manifold.ChartLocalIntegrandHasMFDerivAtParam
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # `ChartLocalPrimitiveFTCMax` at `convexBallChartAt y` UNCONDITIONALLY

Discharges the maximal-atlas chart-local FTC named hypothesis

  `ChartLocalPrimitiveFTCMax (convexBallChartAt y) … y …`

unconditionally on arbitrary compact connected complex 1-manifold X.
Companion of `ChartLocalPrimitiveSmoothExtMaxConvexBallChartAt.lean`.

Architecture:
* **D4 Max** (`mfderiv_chartLocalPrimitiveExtendMax_convexBallChartAt`)
  — chain-rule closed form for `mfderiv chartLocalPrimitiveExtendMax`
  at `convexBallChartAt y`. Body parallels the atlas-form D4
  (`mfderiv_chartLocalPrimitiveExtend_chartAt`):
  - `chartLocalPrimitiveExtendMax = g ∘ convexBallChartAt y` on the
    chart source (via the chartCoord-integral bridge from the
    SmoothExt chip);
  - `Filter.EventuallyEq.mfderiv_eq` upgrades the set-level equality
    to mfderiv equality at the point;
  - chain rule `mfderiv_comp` splits the composition's derivative;
  - D3 (`mfderiv_chartLocalIntegrand_param`) gives the closed form for
    `mfderiv g (convexBallChartAt y x)` on the convex ball target;
  - the chart side uses `contMDiffOn_of_mem_maximalAtlas` →
    `contMDiffAt` → `mdifferentiableAt`.
* **D5 reuse** — the existing atlas-form
  `om_eval_eq_chartCoord_smulRight_mfderiv_chartAt` applies as-is: it
  uses `chartAt ℂ y`, and `(convexBallChartAt y : X → ℂ) = (chartAt ℂ y)`
  is `rfl`, so the mfderivs and chart-image coords coincide.
* **Headline composition**: combines D4 Max with D5 (the rfl chart-map
  equality matches up the two `toSpanSingleton`s).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## D4 Max: chain-rule closed form -/

/-- **D4 Max: closed-form `mfderiv` of `chartLocalPrimitiveExtendMax` at
`convexBallChartAt y`** for every `x ∈ (convexBallChartAt y).source`. -/
theorem mfderiv_chartLocalPrimitiveExtendMax_convexBallChartAt
    (y : X) (om : HolomorphicOneForm X)
    (x : X) (hx : x ∈ (convexBallChartAt y).source) :
    mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (chartLocalPrimitiveExtendMax (convexBallChartAt y)
          (convexBallChartAt_mem_maximalAtlas_real y)
          (convexBallChartAt_target_convex y)
          y (convexBallChartAt_x_mem_source y) om) x
      = (ContinuousLinearMap.toSpanSingleton ℂ
            (om.localCoeff y ((chartAt ℂ y) x))).comp
          (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (convexBallChartAt y : X → ℂ) x) := by
  set φ : OpenPartialHomeomorph X ℂ := convexBallChartAt y with hφ
  set h_max := convexBallChartAt_mem_maximalAtlas_real y
  set hy_ball : y ∈ φ.source := convexBallChartAt_x_mem_source y
  set h_target_convex_ball := convexBallChartAt_target_convex y
  let z₀ : ℂ := (chartAt ℂ y) y
  have hz₀_target : z₀ ∈ φ.target := by
    show (chartAt ℂ y) y ∈ (convexBallChartAt y).target
    rw [← convexBallChartAt_coe]
    exact φ.map_source hy_ball
  have hz_target : (chartAt ℂ y) x ∈ φ.target := by
    show (chartAt ℂ y) x ∈ (convexBallChartAt y).target
    rw [← convexBallChartAt_coe]
    exact φ.map_source hx
  -- The chart-coord parametric integral as a function `g : ℂ → ℂ`.
  let g : ℂ → ℂ := fun z : ℂ => ∫ t in (0 : ℝ)..1,
      om.localCoeff y (bumpedSegment z₀ z t) * chartCoordVelocity z₀ z t
  -- Step 1: `chartLocalPrimitiveExtendMax = g ∘ convexBallChartAt y` on `φ.source`.
  have h_eqOn : Set.EqOn
      (chartLocalPrimitiveExtendMax φ h_max h_target_convex_ball y hy_ball om)
      (g ∘ (convexBallChartAt y : X → ℂ)) φ.source := by
    intro x' hx'
    show chartLocalPrimitiveExtendMax φ h_max h_target_convex_ball y hy_ball om x' = g _
    rw [chartLocalPrimitiveExtendMax_eq_chartLocalPrimitiveMax
      φ h_max h_target_convex_ball y hy_ball om x' hx']
    show chartLocalPrimitiveMax (convexBallChartAt y)
        (convexBallChartAt_mem_maximalAtlas_real y)
        (convexBallChartAt_target_convex y) y hy_ball om x' hx'
      = g ((convexBallChartAt y) x')
    rw [show ((convexBallChartAt y) x' : ℂ) = ((chartAt ℂ y) x' : ℂ) from rfl]
    -- The basepoint here uses hy_ball = convexBallChartAt_x_mem_source y by defn.
    have h_unify_hy :
        hy_ball = convexBallChartAt_x_mem_source y := rfl
    rw [h_unify_hy]
    exact chartLocalPrimitiveMax_convexBallChartAt_eq_chartCoordIntegral y x' hx' om
  -- Step 2: EventuallyEq via open source, then mfderiv_eq.
  have h_open : IsOpen (φ.source : Set X) := φ.open_source
  have h_eventually : (chartLocalPrimitiveExtendMax φ h_max h_target_convex_ball y hy_ball om)
      =ᶠ[𝓝 x] (g ∘ (convexBallChartAt y : X → ℂ)) := by
    filter_upwards [h_open.mem_nhds hx] with x' hx'
    exact h_eqOn hx'
  have h_mfderiv_eq : mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (chartLocalPrimitiveExtendMax φ h_max h_target_convex_ball y hy_ball om) x
      = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (g ∘ (convexBallChartAt y : X → ℂ)) x :=
    Filter.EventuallyEq.mfderiv_eq h_eventually
  -- Step 3: chain rule.
  have h_target_open : IsOpen (φ.target : Set ℂ) := φ.open_target
  have h_loc_anal_full : AnalyticOn ℂ (om.localCoeff y) ((chartAt ℂ y).target) :=
    HolomorphicOneForm.localCoeff_analyticOn om y
  have h_loc_anal : AnalyticOn ℂ (om.localCoeff y) φ.target :=
    h_loc_anal_full.mono (convexBallChartAt_target_subset y)
  have h_mdiff_g : MDifferentiableAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) g ((convexBallChartAt y) x) := by
    have := hasMFDerivAt_chartLocalIntegrand_param h_target_open h_target_convex_ball
      h_loc_anal hz₀_target hz_target
    exact this.mdifferentiableAt
  have h_chart_smooth : ContMDiffOn (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (convexBallChartAt y : X → ℂ) (convexBallChartAt y).source :=
    contMDiffOn_of_mem_maximalAtlas (convexBallChartAt_mem_maximalAtlas y)
  have h_mdiff_φ : MDifferentiableAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
      (convexBallChartAt y : X → ℂ) x := by
    have h_chartAt := (h_chart_smooth x hx).contMDiffAt (h_open.mem_nhds hx)
    exact h_chartAt.mdifferentiableAt (by decide)
  have h_chain : mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (g ∘ (convexBallChartAt y : X → ℂ)) x
      = (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) g ((convexBallChartAt y) x)).comp
          (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (convexBallChartAt y : X → ℂ) x) :=
    mfderiv_comp x h_mdiff_g h_mdiff_φ
  -- Step 4: D3 closed form.
  have h_mfderiv_g : mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) g ((convexBallChartAt y) x)
      = ContinuousLinearMap.toSpanSingleton ℂ (om.localCoeff y ((convexBallChartAt y) x)) :=
    mfderiv_chartLocalIntegrand_param h_target_open h_target_convex_ball
      h_loc_anal hz₀_target hz_target
  rw [h_mfderiv_eq, h_chain, h_mfderiv_g]
  -- Final shape: chart-image coord coincides with chartAt y x by rfl.
  rfl

/-! ## Headline: `ChartLocalPrimitiveFTCMax` at `convexBallChartAt y` -/

/-- **`ChartLocalPrimitiveFTCMax` at `convexBallChartAt y`
UNCONDITIONALLY on arbitrary X.** Composes D4 Max (chain-rule closed
form) with D5 (chart-cotangent identity, atlas form — reused via the
rfl identification of `(convexBallChartAt y : X → ℂ)` with
`(chartAt ℂ y : X → ℂ)`). -/
theorem chartLocalPrimitiveFTCMax_convexBallChartAt
    (y : X) (om : HolomorphicOneForm X) :
    ChartLocalPrimitiveFTCMax (convexBallChartAt y)
      (convexBallChartAt_mem_maximalAtlas_real y)
      (convexBallChartAt_target_convex y)
      y (convexBallChartAt_x_mem_source y) om := by
  intro x hx
  -- D4 Max: mfderiv closed form via convexBallChartAt y.
  have h_d4 :=
    mfderiv_chartLocalPrimitiveExtendMax_convexBallChartAt y om x hx
  -- D5: chart-cotangent identity for om.eval x using chartAt y.
  have hx_chartAt : x ∈ (chartAt ℂ y).source := by
    have h_source_subset :
        (convexBallChartAt y).source ⊆ (chartAt ℂ y).source := by
      intro p hp
      rw [convexBallChartAt_source_eq] at hp
      exact hp.1
    exact h_source_subset hx
  have h_d5 := om_eval_eq_chartCoord_smulRight_mfderiv_chartAt om hx_chartAt
  rw [h_d4]
  exact h_d5

end JacobianChallenge

end
