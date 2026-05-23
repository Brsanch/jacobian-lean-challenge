/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartLocalIntegrandHasMFDerivAtParam
import JacobianChallenge.Manifold.ChartLocalPrimitiveChartIntegral
import JacobianChallenge.Manifold.ChartLocalPrimitiveExtend
import JacobianChallenge.Manifold.HolomorphicOneFormChartCoeffOnTarget

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # D4: Chain-rule closed form for `mfderiv chartLocalPrimitiveExtend`

Combines chip B3 (`chartLocalPrimitive = g ∘ chartAt y` on `φ.source`)
with chip D3 (`mfderiv g (φ x) = toSpanSingleton ℂ (om.localCoeff y (φ x))`)
and the manifold chain rule (`mfderiv_comp`) to give

  `mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartLocalPrimitiveExtend (chartAt ℂ y) … y … om) x
     = (ContinuousLinearMap.toSpanSingleton ℂ
          (om.localCoeff y ((chartAt ℂ y) x))).comp
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ y) x)`

at every `x ∈ (chartAt ℂ y).source`, unconditionally (modulo the
convex chart-target hypothesis already in `chartLocalPrimitiveExtend`).

This is the **D4 sub-atom** of chip D (`ChartLocalPrimitiveFTC`). D5
identifies the RHS with `om.eval x` via the chart-cotangent algebra
(same content as chip B2's `pointwiseChartEval_path` applied
pointwise) to discharge the named hypothesis.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open MeasureTheory Set

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **D4: chain-rule closed form for `mfderiv chartLocalPrimitiveExtend`** at
the natural chart `chartAt ℂ y`, at every `x ∈ (chartAt ℂ y).source`. -/
theorem mfderiv_chartLocalPrimitiveExtend_chartAt
    (y : X) (h_target_convex : Convex ℝ (chartAt ℂ y).target)
    (om : HolomorphicOneForm X)
    (x : X) (hx : x ∈ (chartAt ℂ y).source) :
    mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (chartLocalPrimitiveExtend (chartAt ℂ y) (chart_mem_atlas ℂ y)
          h_target_convex y (mem_chart_source ℂ y) om) x
      = (ContinuousLinearMap.toSpanSingleton ℂ
            (om.localCoeff y ((chartAt ℂ y) x))).comp
          (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (chartAt ℂ y) x) := by
  let φ : OpenPartialHomeomorph X ℂ := chartAt ℂ y
  let h_atlas : φ ∈ atlas ℂ X := chart_mem_atlas ℂ y
  let hy : y ∈ φ.source := mem_chart_source ℂ y
  let z₀ : ℂ := φ y
  let hz₀_target : z₀ ∈ φ.target := φ.map_source hy
  let hz_target : φ x ∈ φ.target := φ.map_source hx
  -- The parametric-integral function `g : ℂ → ℂ`.
  let g : ℂ → ℂ := fun z : ℂ => ∫ t in (0 : ℝ)..1,
      om.localCoeff y (bumpedSegment z₀ z t) *
        chartCoordVelocity z₀ z t
  -- Step 1: `chartLocalPrimitiveExtend = g ∘ φ` on `φ.source`.
  have h_eqOn : Set.EqOn
      (chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om)
      (g ∘ φ) φ.source := by
    intro x' hx'
    show chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om x' = g (φ x')
    rw [chartLocalPrimitiveExtend_eq_chartLocalPrimitive φ h_atlas
      h_target_convex y hy om x' hx']
    exact chartLocalPrimitive_eq_chartCoordIntegral y h_target_convex om x' hx'
  -- Step 2: `mfderiv chartLocalPrimitiveExtend x = mfderiv (g ∘ φ) x` via
  -- the `=ᶠ[𝓝 x]` derived from agreement on the open nbhd `φ.source ∋ x`.
  have h_open : IsOpen (φ.source : Set X) := φ.open_source
  have h_eventually : (chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om)
      =ᶠ[𝓝 x] (g ∘ φ) := by
    filter_upwards [h_open.mem_nhds hx] with x' hx'
    exact h_eqOn hx'
  have h_mfderiv_eq : mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om) x
      = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (g ∘ φ) x :=
    Filter.EventuallyEq.mfderiv_eq h_eventually
  -- Step 3: chain rule.
  -- Need: MDifferentiableAt g (φ x), MDifferentiableAt φ x.
  -- Analyticity of `localCoeff` on the target makes the chip-A setup fire.
  have h_loc_anal : AnalyticOn ℂ (om.localCoeff y) φ.target :=
    HolomorphicOneForm.localCoeff_analyticOn om y
  have h_target_open : IsOpen (φ.target : Set ℂ) := φ.open_target
  have h_mdiff_g : MDifferentiableAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) g (φ x) :=
    (hasMFDerivAt_chartLocalIntegrand_param h_target_open h_target_convex
      h_loc_anal hz₀_target hz_target).mdifferentiableAt
  have h_mdiff_φ : MDifferentiableAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (φ : X → ℂ) x :=
    mdifferentiableAt_atlas h_atlas hx
  have h_chain : mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (g ∘ φ) x
      = (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) g (φ x)).comp
          (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (φ : X → ℂ) x) :=
    mfderiv_comp x h_mdiff_g h_mdiff_φ
  -- Step 4: D3 closes the form for `mfderiv g (φ x)`.
  have h_mfderiv_g : mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) g (φ x)
      = ContinuousLinearMap.toSpanSingleton ℂ (om.localCoeff y (φ x)) :=
    mfderiv_chartLocalIntegrand_param h_target_open h_target_convex
      h_loc_anal hz₀_target hz_target
  rw [h_mfderiv_eq, h_chain, h_mfderiv_g]
  rfl

end JacobianChallenge

end
