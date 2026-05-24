/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.UniformPathChartBallDepth
import JacobianChallenge.Manifold.ComplexManifoldRealification
import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.Geometry.Manifold.IsManifold.Basic

set_option linter.unusedSectionVars false

/-! # Convex-target sub-chart at every point, in the maximal atlas

For every point `x : X` of a complex 1-manifold, the restriction
`(chartAt ℂ x).restr (chartBallSourcePreimage x)` is an
`OpenPartialHomeomorph X ℂ` in the maximal atlas of `X` whose target
is the open ball `Metric.ball ((chartAt ℂ x) x) (chartBallRadius x)`
— which is convex.

This packages the per-point convex-target chart needed by the
`PathPrimitiveAdmissibleChartCover` chain, except it lives in the
**maximal atlas** rather than the **underlying atlas**. On arbitrary
`X`, the canonical `chartAt ℂ x` does not in general have convex
target, so the `HasConvexChartAtTarget X` typeclass instance is
unavailable. The maximal-atlas refinement here exposes a uniformly-
convex-target chart cover that any future maximal-atlas-generalised
admissibility chain can consume.

## What this file ships

* `convexBallChartAt x : OpenPartialHomeomorph X ℂ` — the restricted
  chart at `x` with convex (ball) target.
* `convexBallChartAt_source_eq`, `convexBallChartAt_target_eq` —
  identifications of source and target.
* `convexBallChartAt_target_convex` — the target is convex.
* `convexBallChartAt_x_mem_source` — `x` lies in its own restricted
  source.
* `convexBallChartAt_mem_maximalAtlas` — the restricted chart is in
  `IsManifold.maximalAtlas (𝓘(ℂ, ℂ)) ω X`. Direct corollary of
  mathlib's `StructureGroupoid.restr_mem_maximalAtlas` +
  `ClosedUnderRestriction (contDiffGroupoid ω 𝓘(ℂ, ℂ))` (mathlib
  instance).

## Why this is useful

The existing `PathPrimitiveAdmissibleChartCover om` predicate
(`Manifold/PathPrimitiveGlobalSmoothFTC.lean`) requires a chart cover
where every chart is in `atlas ℂ X` AND has convex target. On RS
this is supplied via the two-chart atlas (both targets are `Set.univ`,
trivially convex). On arbitrary X, no chart in the underlying atlas is
guaranteed convex. The maximal-atlas version of the admissibility
chain — a future refactor — will consume `convexBallChartAt` directly.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Metric Filter Topology
open scoped Manifold ContDiff

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Convex-target sub-chart at `x`.** Restriction of `chartAt ℂ x`
to `chartBallSourcePreimage x` (the points whose chart-image lies in
the canonical chart-ball at `x`). The result is in the maximal atlas
(see `convexBallChartAt_mem_maximalAtlas`) and has target equal to the
open ball, which is convex. -/
noncomputable def convexBallChartAt (x : X) : OpenPartialHomeomorph X ℂ :=
  (chartAt ℂ x).restr (chartBallSourcePreimage x)

/-! ## Source / target identifications -/

lemma convexBallChartAt_source_eq (x : X) :
    (convexBallChartAt x).source = chartBallSourcePreimage x := by
  have h_open : IsOpen (chartBallSourcePreimage x) :=
    chartBallSourcePreimage_isOpen x
  unfold convexBallChartAt
  rw [(chartAt ℂ x).restr_source' (chartBallSourcePreimage x) h_open]
  exact Set.inter_eq_right.mpr (fun y hy => hy.1)

lemma convexBallChartAt_x_mem_source (x : X) :
    x ∈ (convexBallChartAt x).source := by
  rw [convexBallChartAt_source_eq]
  exact chartBallSourcePreimage_mem_self x

@[simp] lemma convexBallChartAt_coe (x : X) :
    (convexBallChartAt x : X → ℂ) = (chartAt ℂ x : X → ℂ) := rfl

@[simp] lemma convexBallChartAt_coe_symm (x : X) :
    ((convexBallChartAt x).symm : ℂ → X) = ((chartAt ℂ x).symm : ℂ → X) := rfl

lemma convexBallChartAt_target_eq (x : X) :
    (convexBallChartAt x).target =
      Metric.ball ((chartAt ℂ x) x) (chartBallRadius x) := by
  have h_open : IsOpen (chartBallSourcePreimage x) :=
    chartBallSourcePreimage_isOpen x
  have h_target_def :
      (convexBallChartAt x).target
        = (chartAt ℂ x).target ∩
            (chartAt ℂ x).symm ⁻¹' chartBallSourcePreimage x := by
    unfold convexBallChartAt
    show ((chartAt ℂ x).restr (chartBallSourcePreimage x)).toPartialEquiv.target = _
    rw [OpenPartialHomeomorph.restr_toPartialEquiv' _ _ h_open]
    rfl
  rw [h_target_def]
  ext z
  constructor
  · rintro ⟨hz_tar, hz_pre⟩
    -- hz_pre : (chartAt ℂ x).symm z ∈ chartBallSourcePreimage x
    -- chartBallSourcePreimage x = source ∩ chart ⁻¹' ball
    have hz_symm_in_source : (chartAt ℂ x).symm z ∈ (chartAt ℂ x).source := hz_pre.1
    have hz_chart_eq : (chartAt ℂ x) ((chartAt ℂ x).symm z) = z :=
      (chartAt ℂ x).right_inv hz_tar
    have hz_in_ball :
        (chartAt ℂ x) ((chartAt ℂ x).symm z) ∈
          Metric.ball ((chartAt ℂ x) x) (chartBallRadius x) := hz_pre.2
    rw [hz_chart_eq] at hz_in_ball
    exact hz_in_ball
  · intro hz_ball
    -- z ∈ ball ⊆ target.
    have hz_tar : z ∈ (chartAt ℂ x).target :=
      chartBallRadius_subset_target x hz_ball
    refine ⟨hz_tar, ?_, ?_⟩
    · exact (chartAt ℂ x).map_target hz_tar
    · show (chartAt ℂ x) ((chartAt ℂ x).symm z) ∈
        Metric.ball ((chartAt ℂ x) x) (chartBallRadius x)
      rw [(chartAt ℂ x).right_inv hz_tar]
      exact hz_ball

lemma convexBallChartAt_target_convex (x : X) :
    Convex ℝ (convexBallChartAt x).target := by
  rw [convexBallChartAt_target_eq]
  exact convex_ball _ _

/-! ## Maximal-atlas membership -/

/-- **The convex-target sub-chart lies in `IsManifold.maximalAtlas`.**
Direct application of `StructureGroupoid.restr_mem_maximalAtlas` for
the `contDiffGroupoid ω 𝓘(ℂ, ℂ)` groupoid, whose
`ClosedUnderRestriction` instance is in mathlib. -/
lemma convexBallChartAt_mem_maximalAtlas (x : X) :
    convexBallChartAt x ∈ IsManifold.maximalAtlas (𝓘(ℂ, ℂ)) ω X := by
  have h_open : IsOpen (chartBallSourcePreimage x) :=
    chartBallSourcePreimage_isOpen x
  have h_chart_in_max :
      chartAt ℂ x ∈ IsManifold.maximalAtlas (𝓘(ℂ, ℂ)) ω X :=
    IsManifold.chart_mem_maximalAtlas x
  exact restr_mem_maximalAtlas
    (contDiffGroupoid ω (𝓘(ℂ, ℂ))) h_chart_in_max h_open

/-! ## Headline: structural typeclass-like access

The five lemmas above package, for every `x : X`, a chart in the
maximal atlas with:

* convex target (an open ball),
* `x` in its source,
* underlying function = `chartAt ℂ x`.

A future chip generalising `PathPrimitiveAdmissibleChartCover` from
`atlas ℂ X` to `IsManifold.maximalAtlas (𝓘(ℂ, ℂ)) ω X` will consume
`convexBallChartAt` to discharge the convex-target chart-cover
admissibility on arbitrary `X` (no `[HasConvexChartAtTarget X]`
typeclass needed). -/

end JacobianChallenge

end
