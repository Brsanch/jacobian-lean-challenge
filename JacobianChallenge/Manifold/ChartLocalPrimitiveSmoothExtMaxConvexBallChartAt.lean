/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartLocalPrimitiveMaxConvexBallChartAt
import JacobianChallenge.Manifold.ChartLocalPrimitiveChartIntegral
import JacobianChallenge.Manifold.AnalyticOnChartLocalIntegrand
import JacobianChallenge.Manifold.PathPrimitiveLocalSmoothFTCNamedMax
import JacobianChallenge.Manifold.HolomorphicOneFormChartCoeffOnTarget
import JacobianChallenge.Manifold.ChartLocalPrimitiveSmoothExtChartAt

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # `ChartLocalPrimitiveSmoothExtMax` at `convexBallChartAt y` UNCONDITIONALLY

Discharges the maximal-atlas chart-local smoothness named hypothesis

  `ChartLocalPrimitiveSmoothExtMax (convexBallChartAt y) … y …`

unconditionally on arbitrary compact connected complex 1-manifold X.
This is the genuine analytic step that converts the maxAtlas cascade
into an arbitrary-X discharge: `convexBallChartAt y` has convex target
unconditionally (the chart-image ball), so the chart-coord parametric
integral chip A can be applied with the ball as the convex region, then
composed with the chart smoothness from `contMDiffOn_of_mem_maximalAtlas`.

Architecture:
* **Generalised chip B3** (`complexChainPeriod_linearInChartSegment_chartAt_eq_chartCoordIntegral`)
  — reformulates the atlas-form chartLocalPrimitive ↔ chartCoord-integral
  identity to take `h_seg` directly (not `h_target_convex`). The proof
  body is a direct port of `chartLocalPrimitive_eq_chartCoordIntegral`
  (which is exactly the chip-B3 body modulo the outer `chartLocalPrimitive`
  wrapper).
* **Chip A on the ball** (`chartCoordIntegral_contMDiffOn_convexBallChartAt_target`)
  — applies `analyticOn_chartLocalIntegrand_param` with `S` = the
  convex-ball target of `convexBallChartAt y`. Needs only that
  `om.localCoeff y` is analytic on the ball (restriction of the
  chartAt-target analyticity).
* **Bridge to chartLocalPrimitiveMax** (rfl chain from
  `ChartLocalPrimitiveMaxConvexBallChartAt.lean` ⇒
  `chartLocalPrimitiveMax (convexBallChartAt y) … = complexChainPeriod
  (single (linearInChartSegment (chartAt y) (chart_mem_atlas) …)) om`).
* **Headline composition**: chart smoothness on source +
  chart-coord integral smoothness on target + `MapsTo` + `ContMDiffOn.comp`
  + `ContMDiffOn.congr` via the chartLocalPrimitiveExtendMax agreement.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set MeasureTheory

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Subset relation: `(convexBallChartAt y).target ⊆ (chartAt ℂ y).target` -/

/-- The target of `convexBallChartAt y` is a subset of `(chartAt ℂ y).target`.
Direct from `convexBallChartAt y = (chartAt y).restr (...)` and
`PartialEquiv.restr_target`. -/
lemma convexBallChartAt_target_subset (y : X) :
    (convexBallChartAt y).target ⊆ (chartAt ℂ y).target := by
  intro z hz
  have hz_symm : (convexBallChartAt y).symm z ∈ (convexBallChartAt y).source :=
    (convexBallChartAt y).map_target hz
  -- Source of the restricted chart sits inside (chartAt y).source.
  have h_source_subset :
      (convexBallChartAt y).source ⊆ (chartAt ℂ y).source := by
    intro p hp
    rw [convexBallChartAt_source_eq] at hp
    exact hp.1
  have hz_symm_in_chart : (chartAt ℂ y).symm z ∈ (chartAt ℂ y).source := by
    rw [← convexBallChartAt_coe_symm]
    exact h_source_subset hz_symm
  -- right_inv via convexBallChartAt z ∈ target.
  have h_right_inv : (convexBallChartAt y) ((convexBallChartAt y).symm z) = z :=
    (convexBallChartAt y).right_inv hz
  rw [convexBallChartAt_coe_symm, convexBallChartAt_coe] at h_right_inv
  rw [← h_right_inv]
  exact (chartAt ℂ y).map_source hz_symm_in_chart

/-! ## Chip A applied to the convex-ball target -/

/-- **Chart-coord parametric integral is `ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω` on the
ball `(convexBallChartAt y).target`.** Applies `analyticOn_chartLocalIntegrand_param`
with the ball as the convex open region, using
`HolomorphicOneForm.localCoeff_analyticOn` restricted to the ball. -/
theorem chartCoordIntegral_contMDiffOn_convexBallChartAt_target
    (y : X) (om : HolomorphicOneForm X) :
    ContMDiffOn (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (fun z : ℂ => ∫ t in (0 : ℝ)..1,
          om.localCoeff y
              (bumpedSegment ((chartAt ℂ y) y) z t) *
            chartCoordVelocity ((chartAt ℂ y) y) z t)
      (convexBallChartAt y).target := by
  have hS_open : IsOpen (convexBallChartAt y).target := (convexBallChartAt y).open_target
  have hS_conv : Convex ℝ (convexBallChartAt y).target := convexBallChartAt_target_convex y
  have h_loc_anal_full : AnalyticOn ℂ (om.localCoeff y) ((chartAt ℂ y).target) :=
    HolomorphicOneForm.localCoeff_analyticOn om y
  have h_loc_anal : AnalyticOn ℂ (om.localCoeff y) ((convexBallChartAt y).target) :=
    h_loc_anal_full.mono (convexBallChartAt_target_subset y)
  have hy_ball : y ∈ (convexBallChartAt y).source := convexBallChartAt_x_mem_source y
  have hz₀_mem : (chartAt ℂ y) y ∈ (convexBallChartAt y).target := by
    rw [← convexBallChartAt_coe]
    exact (convexBallChartAt y).map_source hy_ball
  have h_anal := analyticOn_chartLocalIntegrand_param hS_open hS_conv h_loc_anal hz₀_mem
  have h_unique : UniqueDiffOn ℂ ((convexBallChartAt y).target) := hS_open.uniqueDiffOn
  exact (h_anal.contDiffOn h_unique).contMDiffOn

/-! ## Generalised chip B3 — takes `h_seg` directly -/

/-- **Generalised chip B3: `complexChainPeriod` of a chartAt-chart-line
segment equals the chartCoord parametric integral.** Parameterised by
`h_seg` directly rather than `h_target_convex`, allowing application
when only the segment-in-target fact is available (e.g. when only
restricted sub-targets are convex). The proof body is the inner content
of `chartLocalPrimitive_eq_chartCoordIntegral`. -/
theorem complexChainPeriod_linearInChartSegment_chartAt_eq_chartCoordIntegral
    (y x : X) (hy : y ∈ (chartAt ℂ y).source) (hx : x ∈ (chartAt ℂ y).source)
    (h_seg : segment ℝ ((chartAt ℂ y) y) ((chartAt ℂ y) x) ⊆ (chartAt ℂ y).target)
    (om : HolomorphicOneForm X) :
    complexChainPeriod (SmoothChain.single
        (SmoothPath.linearInChartSegment (chartAt ℂ y) (chart_mem_atlas ℂ y)
          y x hy hx h_seg)) om
      = ∫ t in (0 : ℝ)..1,
          om.localCoeff y
              (bumpedSegment ((chartAt ℂ y) y) ((chartAt ℂ y) x) t) *
            chartCoordVelocity ((chartAt ℂ y) y) ((chartAt ℂ y) x) t := by
  set φ : OpenPartialHomeomorph X ℂ := chartAt ℂ y with hφ
  set γ : SmoothPath 𝓘(ℝ, ℂ) X :=
    SmoothPath.linearInChartSegment φ (chart_mem_atlas ℂ y) y x hy hx h_seg with hγ_def
  have h_cont : ContinuousOn
      (fun t : ℝ => (om.eval (γ.ambient t)) (γ.velocity t))
      (Set.Icc (0 : ℝ) 1) :=
    (ChartContainedClosedLoop.complexEvalIntegrand_continuous γ om).continuousOn
  rw [complexChainPeriod_single_eq_complex_integral_of_path γ om h_cont]
  refine intervalIntegral.integral_congr_ae ?_
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have h_eq_on_ioo : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      (om.eval (γ.ambient t)) (γ.velocity t)
        = om.localCoeff y
            (bumpedSegment ((chartAt ℂ y) y) ((chartAt ℂ y) x) t) *
          chartCoordVelocity ((chartAt ℂ y) y) ((chartAt ℂ y) x) t := by
    intro t ht
    have ht_icc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h_amb_src : γ.ambient t ∈ φ.source := by
      have h_bs_mem : bumpedSegment (φ y) (φ x) t ∈ φ.target :=
        h_seg (bumpedSegment_mem_segment _ _ _)
      have h_amb_eq := γ.ambient_eq_on_unitInterval ⟨t, ht_icc⟩
      rw [show ((⟨t, ht_icc⟩ : unitInterval) : ℝ) = t from rfl] at h_amb_eq
      rw [h_amb_eq]
      show φ.symm (bumpedSegment (φ y) (φ x) t) ∈ φ.source
      exact φ.map_target h_bs_mem
    have h_chip_b2 := SmoothPath.pointwiseChartEval_path γ y om h_amb_src
    rw [h_chip_b2]
    rw [chartAt_y_comp_linearInChartSegment_ambient_eq
      φ (chart_mem_atlas ℂ y) y x hy hx h_seg ht_icc]
    have h_eventually := chartAt_y_comp_linearInChartSegment_ambient_eventuallyEq
      φ (chart_mem_atlas ℂ y) y x hy hx h_seg ht
    have h_deriv_eq : deriv ((φ : X → ℂ) ∘ γ.ambient) t
        = deriv (fun s : ℝ => bumpedSegment (φ y) (φ x) s) t :=
      Filter.EventuallyEq.deriv_eq h_eventually
    show om.localCoeff y (bumpedSegment (φ y) (φ x) t)
            * deriv ((φ : X → ℂ) ∘ γ.ambient) t
        = om.localCoeff y (bumpedSegment ((chartAt ℂ y) y) ((chartAt ℂ y) x) t)
            * chartCoordVelocity ((chartAt ℂ y) y) ((chartAt ℂ y) x) t
    rw [h_deriv_eq, deriv_bumpedSegment_eq_chartCoordVelocity]
  have h_subset : {a : ℝ | ¬ (a ∈ Set.Ioc (0 : ℝ) 1 →
        (om.eval (γ.ambient a)) (γ.velocity a) =
          om.localCoeff y
              (bumpedSegment ((chartAt ℂ y) y) ((chartAt ℂ y) x) a) *
            chartCoordVelocity ((chartAt ℂ y) y) ((chartAt ℂ y) x) a)}
      ⊆ ({1} : Set ℝ) := by
    intro t ht_not
    rw [Set.mem_setOf_eq, Classical.not_imp] at ht_not
    obtain ⟨ht_ioc, ht_neq⟩ := ht_not
    rw [Set.mem_singleton_iff]
    by_contra h_t_neq_one
    have ht_lt_one : t < 1 := lt_of_le_of_ne ht_ioc.2 h_t_neq_one
    have ht_ioo : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht_ioc.1, ht_lt_one⟩
    exact ht_neq (h_eq_on_ioo t ht_ioo)
  refine MeasureTheory.ae_iff.mpr ?_
  exact MeasureTheory.measure_mono_null h_subset Real.volume_singleton

/-! ## Bridge: `chartLocalPrimitiveMax (convexBallChartAt y) …` = chartCoord integral -/

/-- **The chartLocalPrimitiveMax at `convexBallChartAt y` equals the
chartCoord parametric integral.** Combines the rfl path-bridge with the
generalised chip B3 above. -/
theorem chartLocalPrimitiveMax_convexBallChartAt_eq_chartCoordIntegral
    (y x : X) (hx : x ∈ (convexBallChartAt y).source)
    (om : HolomorphicOneForm X) :
    chartLocalPrimitiveMax (convexBallChartAt y)
        (convexBallChartAt_mem_maximalAtlas_real y)
        (convexBallChartAt_target_convex y) y
        (convexBallChartAt_x_mem_source y) om x hx
      = ∫ t in (0 : ℝ)..1,
          om.localCoeff y
              (bumpedSegment ((chartAt ℂ y) y) ((chartAt ℂ y) x) t) *
            chartCoordVelocity ((chartAt ℂ y) y) ((chartAt ℂ y) x) t := by
  have hy_chartAt : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  have hx_chartAt : x ∈ (chartAt ℂ y).source := by
    have h_source_subset :
        (convexBallChartAt y).source ⊆ (chartAt ℂ y).source := by
      intro p hp
      rw [convexBallChartAt_source_eq] at hp
      exact hp.1
    exact h_source_subset hx
  have hy_ball : y ∈ (convexBallChartAt y).source := convexBallChartAt_x_mem_source y
  have h_seg_ball : segment ℝ ((convexBallChartAt y) y) ((convexBallChartAt y) x)
        ⊆ (convexBallChartAt y).target :=
    Convex.segment_subset (convexBallChartAt_target_convex y)
      ((convexBallChartAt y).map_source hy_ball)
      ((convexBallChartAt y).map_source hx)
  have h_seg_chartAt : segment ℝ ((chartAt ℂ y) y) ((chartAt ℂ y) x)
        ⊆ (chartAt ℂ y).target := by
    rw [show segment ℝ ((chartAt ℂ y) y) ((chartAt ℂ y) x)
          = segment ℝ ((convexBallChartAt y) y) ((convexBallChartAt y) x) from rfl]
    exact h_seg_ball.trans (convexBallChartAt_target_subset y)
  -- Unfold chartLocalPrimitiveMax to expose complexChainPeriod (single γ_max).
  unfold chartLocalPrimitiveMax
  -- Apply the path-level rfl bridge to switch γ_max to the chartAt-atlas path.
  rw [SmoothPath.linearInChartSegmentMax_convexBallChartAt_eq_chartAt_atlas
      y x hy_ball hx hy_chartAt hx_chartAt _ h_seg_chartAt]
  -- Apply the generalised chip B3.
  exact complexChainPeriod_linearInChartSegment_chartAt_eq_chartCoordIntegral
    y x hy_chartAt hx_chartAt h_seg_chartAt om

/-! ## Headline: `ChartLocalPrimitiveSmoothExtMax (convexBallChartAt y)` discharge -/

/-- **`ChartLocalPrimitiveSmoothExtMax` at `convexBallChartAt y`
UNCONDITIONALLY on arbitrary X.** Composes chart-coord-integral smoothness
on the convex ball with chart smoothness on the chart source (via
`contMDiffOn_of_mem_maximalAtlas`), and matches the composite to
`chartLocalPrimitiveExtendMax` via the chartCoord-integral bridge. -/
theorem chartLocalPrimitiveSmoothExtMax_convexBallChartAt
    (y : X) (om : HolomorphicOneForm X) :
    ChartLocalPrimitiveSmoothExtMax (convexBallChartAt y)
      (convexBallChartAt_mem_maximalAtlas_real y)
      (convexBallChartAt_target_convex y)
      y (convexBallChartAt_x_mem_source y) om := by
  unfold ChartLocalPrimitiveSmoothExtMax
  -- Step 1: chartCoord integral is ContMDiffOn ω on the ball.
  have h_int_smooth := chartCoordIntegral_contMDiffOn_convexBallChartAt_target y om
  -- Step 2: chart map is ContMDiffOn ω on its source.
  have h_chart_smooth : ContMDiffOn (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (convexBallChartAt y) (convexBallChartAt y).source :=
    contMDiffOn_of_mem_maximalAtlas (convexBallChartAt_mem_maximalAtlas y)
  -- Step 3: MapsTo for composition.
  have h_maps : Set.MapsTo (convexBallChartAt y : X → ℂ)
      (convexBallChartAt y).source (convexBallChartAt y).target :=
    fun p hp => (convexBallChartAt y).map_source hp
  -- Step 4: compose to get g ∘ convexBallChartAt y ContMDiffOn ω on source.
  have h_comp : ContMDiffOn (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      ((fun z : ℂ => ∫ t in (0 : ℝ)..1,
          om.localCoeff y
              (bumpedSegment ((chartAt ℂ y) y) z t) *
            chartCoordVelocity ((chartAt ℂ y) y) z t)
        ∘ (convexBallChartAt y : X → ℂ))
      (convexBallChartAt y).source :=
    h_int_smooth.comp h_chart_smooth h_maps
  -- Step 5: congr to chartLocalPrimitiveExtendMax via the chartCoord bridge.
  apply h_comp.congr
  intro x hx
  rw [chartLocalPrimitiveExtendMax_eq_chartLocalPrimitiveMax
      (convexBallChartAt y) _ _ y _ om x hx]
  -- Goal: chartLocalPrimitiveMax … = (chartCoord integral ∘ convexBallChartAt y) x.
  -- The composition unfolds; chart map = chartAt y (rfl).
  show chartLocalPrimitiveMax _ _ _ _ _ _ _ _
      = ∫ t in (0 : ℝ)..1,
          om.localCoeff y
              (bumpedSegment ((chartAt ℂ y) y) ((convexBallChartAt y) x) t) *
            chartCoordVelocity ((chartAt ℂ y) y) ((convexBallChartAt y) x) t
  rw [show ((convexBallChartAt y) x : ℂ) = ((chartAt ℂ y) x : ℂ) from rfl]
  exact chartLocalPrimitiveMax_convexBallChartAt_eq_chartCoordIntegral y x hx om

end JacobianChallenge

end
