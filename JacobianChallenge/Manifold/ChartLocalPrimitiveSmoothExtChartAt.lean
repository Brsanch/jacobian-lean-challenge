/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AnalyticOnChartLocalIntegrand
import JacobianChallenge.Manifold.ChartLocalPrimitiveChartIntegral
import JacobianChallenge.Manifold.ChartLocalPrimitiveExtend
import JacobianChallenge.Manifold.PathPrimitiveLocalSmoothFTCNamed
import JacobianChallenge.Manifold.HolomorphicOneFormChartCoeffOnTarget

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # `ChartLocalPrimitiveSmoothExt` at the natural chart `chartAt ℂ y`

Combines chip A (`AnalyticOn ℂ` of chart-coord parametric integral),
chip B3 (chart-coord-integral identity for `chartLocalPrimitive`), and
the standard `AnalyticOn → ContMDiffOn ω` + chart smoothness compose to
discharge the named hypothesis

  `ChartLocalPrimitiveSmoothExt (chartAt ℂ y) … y … om`

unconditionally for any `om : HolomorphicOneForm X` (with the chart
target convex).

Architecture:
* Chip A applied with `f := om.localCoeff y` (analytic on
  `(chartAt y).target` via `localCoeff_analyticOn`) gives an
  `AnalyticOn ℂ` of the chart-coord parametric integral
  `g(z) := ∫ t in 0..1, om.localCoeff y (B(z, t)) * V(z, t)` on
  `(chartAt y).target`.
* `AnalyticOn.contDiffOn` ⟹ `ContDiffOn ℂ ω g (chartAt y).target` (uses
  `chartTarget_uniqueDiffOn`).
* `ContDiffOn.contMDiffOn` ⟹ `ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω g (chartAt y).target`.
* `contMDiffOn_chart` ⟹ `ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (chartAt y) (chartAt y).source`.
* Composition (`ContMDiffOn.comp` with `MapsTo` from `φ.map_source`) ⟹
  `ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (g ∘ chartAt y) (chartAt y).source`.
* Chip B3 says `chartLocalPrimitive (chartAt y) … = g ∘ chartAt y` on
  `(chartAt y).source` ⟹ `ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω chartLocalPrimitive`.
* Agreement `chartLocalPrimitiveExtend = chartLocalPrimitive` on
  `(chartAt y).source` (`chartLocalPrimitiveExtend_eq_chartLocalPrimitive`)
  + `ContMDiffOn.congr` ⟹ the named `ChartLocalPrimitiveSmoothExt`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set MeasureTheory

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## The chart-coord parametric integral as a `ContMDiffOn ω` function -/

/-- The chart-coord parametric integral

  `g(z) := ∫ t in 0..1, om.localCoeff y (bumpedSegment ((chartAt y) y) z t)
                          * chartCoordVelocity ((chartAt y) y) z t`

is `ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω` on `(chartAt y).target`. -/
theorem chartCoordIntegral_contMDiffOn_target
    (y : X) (h_target_convex : Convex ℝ (chartAt ℂ y).target)
    (om : HolomorphicOneForm X) :
    ContMDiffOn (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (fun z : ℂ => ∫ t in (0 : ℝ)..1,
          om.localCoeff y
              (bumpedSegment ((chartAt ℂ y) y) z t) *
            chartCoordVelocity ((chartAt ℂ y) y) z t)
      (chartAt ℂ y).target := by
  -- Chip A with `f := om.localCoeff y, z₀ := (chartAt ℂ y) y`.
  have h_target_open : IsOpen ((chartAt ℂ y).target) := (chartAt ℂ y).open_target
  have hy : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  have hz₀_mem : (chartAt ℂ y) y ∈ (chartAt ℂ y).target :=
    (chartAt ℂ y).map_source hy
  have h_loc_anal : AnalyticOn ℂ (om.localCoeff y) ((chartAt ℂ y).target) :=
    HolomorphicOneForm.localCoeff_analyticOn om y
  have h_anal : AnalyticOn ℂ
      (fun z : ℂ => ∫ t in (0 : ℝ)..1,
          om.localCoeff y
              (bumpedSegment ((chartAt ℂ y) y) z t) *
            chartCoordVelocity ((chartAt ℂ y) y) z t)
      ((chartAt ℂ y).target) :=
    analyticOn_chartLocalIntegrand_param h_target_open h_target_convex
      h_loc_anal hz₀_mem
  -- Analytic on open set ⟹ ContDiff ω ⟹ ContMDiff ω.
  have h_unique : UniqueDiffOn ℂ ((chartAt ℂ y).target) :=
    h_target_open.uniqueDiffOn
  have h_contDiff : ContDiffOn ℂ ω _ ((chartAt ℂ y).target) :=
    h_anal.contDiffOn h_unique
  exact h_contDiff.contMDiffOn

/-! ## Compose with the chart on the manifold side -/

/-- `chartLocalPrimitive (chartAt ℂ y) … y … om` is `ContMDiffOn ω` on
`(chartAt ℂ y).source`. -/
theorem chartLocalPrimitive_contMDiffOn_chartAt
    (y : X) (h_target_convex : Convex ℝ (chartAt ℂ y).target)
    (om : HolomorphicOneForm X) :
    ContMDiffOn (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (chartLocalPrimitiveExtend (chartAt ℂ y) (chart_mem_atlas ℂ y)
        h_target_convex y (mem_chart_source ℂ y) om)
      (chartAt ℂ y).source := by
  set φ : OpenPartialHomeomorph X ℂ := chartAt ℂ y with hφ
  set h_atlas := chart_mem_atlas ℂ y
  set hy := mem_chart_source ℂ y
  -- ContMDiffOn ω of the chart-coord parametric integral on φ.target.
  have h_int_smooth := chartCoordIntegral_contMDiffOn_target y h_target_convex om
  -- ContMDiffOn ω of chartAt on its source.
  have h_chart_smooth : ContMDiffOn (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (chartAt ℂ y) (chartAt ℂ y).source :=
    contMDiffOn_chart
  -- Compose: ContMDiffOn ω of g ∘ chartAt y on (chartAt y).source.
  have h_maps : MapsTo (chartAt ℂ y) (chartAt ℂ y).source (chartAt ℂ y).target :=
    fun x hx => (chartAt ℂ y).map_source hx
  have h_comp : ContMDiffOn (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      ((fun z : ℂ => ∫ t in (0 : ℝ)..1,
          om.localCoeff y
              (bumpedSegment ((chartAt ℂ y) y) z t) *
            chartCoordVelocity ((chartAt ℂ y) y) z t)
        ∘ (chartAt ℂ y))
      (chartAt ℂ y).source :=
    h_int_smooth.comp h_chart_smooth h_maps
  -- Transfer via chip B3 + the extend-agreement to `chartLocalPrimitiveExtend`.
  apply h_comp.congr
  intro x hx
  -- Goal: chartLocalPrimitiveExtend (…) x = (parametric integral ∘ chartAt y) x.
  rw [chartLocalPrimitiveExtend_eq_chartLocalPrimitive (chartAt ℂ y) h_atlas
    h_target_convex y hy om x hx]
  -- Goal: chartLocalPrimitive (…) x hx = (parametric integral) ((chartAt y) x).
  exact chartLocalPrimitive_eq_chartCoordIntegral y h_target_convex om x hx

/-! ## Headline: `ChartLocalPrimitiveSmoothExt` at the natural chart -/

/-- **`ChartLocalPrimitiveSmoothExt` at `chartAt ℂ y` UNCONDITIONALLY**
(modulo the convex chart-target hypothesis already required by the
definition). -/
theorem chartLocalPrimitiveSmoothExt_chartAt
    (y : X) (h_target_convex : Convex ℝ (chartAt ℂ y).target)
    (om : HolomorphicOneForm X) :
    ChartLocalPrimitiveSmoothExt (chartAt ℂ y) (chart_mem_atlas ℂ y)
      h_target_convex y (mem_chart_source ℂ y) om :=
  chartLocalPrimitive_contMDiffOn_chartAt y h_target_convex om

end JacobianChallenge

end
