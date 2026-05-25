/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AffineChartTriangleSimplexBall
import JacobianChallenge.Manifold.ChartStraightLinePath

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Chart-straight-line `SmoothPath` (chart-image-in-ball case)

Variant of `chartStraightLinePath_univ` that drops the
`(chartAt ℂ q).target = Set.univ` hypothesis in exchange for
chart-image-in-ball data (`Metric.ball z_c r ⊆ (chartAt ℂ q).target`
plus `z₀ z₁ ∈ Metric.ball z_c r`).

Defined canonically as `face2` of the degenerate ball triangle
`(z₀, z₁, z₀)`. This makes the spoke-cancellation in fan-triangulation
work definitionally: every "spoke" from a fan apex to a polygonal
vertex is the same canonical `chartStraightLinePath_ball` regardless
of which fan triangle it appears in.

## What this file ships

* `chartStraightLinePath_ball q z_c r hr hB z₀ z₁ h0 h1 :
    SmoothPath 𝓘(ℝ, ℂ) X` — the canonical chart-straight-line path.
* `chartStraightLinePath_ball_src / _tgt` (`@[simp]`).
* `face_i_eq_chartStraightLinePath_ball` (i = 0, 1, 2) — the
  three faces of `affineChartTriangleSimplex_ball q ... z₀ z₁ z₂ ...`
  are the canonical chart-straight-line paths between the appropriate
  pairs.
* `affineChartTriangleSimplex_ball_boundary` — the boundary identity
  in terms of `chartStraightLinePath_ball`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## The canonical chart-straight-line path -/

/-- **Chart-straight-line `SmoothPath` (chart-image-in-ball version).**

Defined via `face2` of the degenerate ball triangle `(z₀, z₁, z₀)`.
Pointwise on the unit interval, the path traces
`t ↦ (chartAt ℂ q).symm ((1 - t) • z₀ + t • z₁)`. -/
noncomputable def chartStraightLinePath_ball
    (q : X) (z_c : ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z_c r ⊆ (chartAt ℂ q).target)
    (z₀ z₁ : ℂ)
    (h0 : z₀ ∈ Metric.ball z_c r) (h1 : z₁ ∈ Metric.ball z_c r) :
    SmoothPath (𝓘(ℝ, ℂ)) X :=
  Smooth2Simplex.face2
    (affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₁ z₀ h0 h1 h0)

@[simp] lemma chartStraightLinePath_ball_src
    (q : X) (z_c : ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z_c r ⊆ (chartAt ℂ q).target)
    (z₀ z₁ : ℂ)
    (h0 : z₀ ∈ Metric.ball z_c r) (h1 : z₁ ∈ Metric.ball z_c r) :
    (chartStraightLinePath_ball q z_c r hr hB z₀ z₁ h0 h1).src
      = (chartAt ℂ q).symm z₀ := by
  change (affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₁ z₀ h0 h1 h0).toFun
      Smooth2Simplex.v0 = (chartAt ℂ q).symm z₀
  exact affineChartTriangleSimplex_ball_toFun_v0 q z_c r hr hB z₀ z₁ z₀ h0 h1 h0

@[simp] lemma chartStraightLinePath_ball_tgt
    (q : X) (z_c : ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z_c r ⊆ (chartAt ℂ q).target)
    (z₀ z₁ : ℂ)
    (h0 : z₀ ∈ Metric.ball z_c r) (h1 : z₁ ∈ Metric.ball z_c r) :
    (chartStraightLinePath_ball q z_c r hr hB z₀ z₁ h0 h1).tgt
      = (chartAt ℂ q).symm z₁ := by
  change (affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₁ z₀ h0 h1 h0).toFun
      Smooth2Simplex.v1 = (chartAt ℂ q).symm z₁
  exact affineChartTriangleSimplex_ball_toFun_v1 q z_c r hr hB z₀ z₁ z₀ h0 h1 h0

/-! ## Pointwise toPath identification on the unit interval -/

/-- The `face_jParam`-coordinates of the three face parameterizations
all lie in `standardSimplex2` for any `t : unitInterval`. -/
private lemma face0Param_val_mem_standardSimplex2 (t : unitInterval) :
    Smooth2Simplex.face0Param t.val ∈ standardSimplex2 :=
  face0Param_mem_standardSimplex2 (Set.mem_Icc.mpr ⟨t.2.1, t.2.2⟩)

private lemma face1Param_val_mem_standardSimplex2 (t : unitInterval) :
    Smooth2Simplex.face1Param t.val ∈ standardSimplex2 :=
  face1Param_mem_standardSimplex2 (Set.mem_Icc.mpr ⟨t.2.1, t.2.2⟩)

private lemma face2Param_val_mem_standardSimplex2 (t : unitInterval) :
    Smooth2Simplex.face2Param t.val ∈ standardSimplex2 :=
  face2Param_mem_standardSimplex2 (Set.mem_Icc.mpr ⟨t.2.1, t.2.2⟩)

/-! ## Face identifications

Each face of `affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₁ z₂ h0 h1 h2`
equals the canonical chart-straight-line path between the appropriate
two corners (independent of the third corner). Proved via
`smoothPath_ext_of_toPath_apply` after a pointwise calculation on Δ²
using `affineChartTriangleSimplex_ball_toFun_on_simplex`. -/

/-- Face-2 (v₀ → v₁) of the ball triangle `(z₀, z₁, z₂)` equals
`chartStraightLinePath_ball … z₀ z₁`. -/
lemma face2_eq_chartStraightLinePath_ball
    (q : X) (z_c : ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z_c r ⊆ (chartAt ℂ q).target)
    (z₀ z₁ z₂ : ℂ)
    (h0 : z₀ ∈ Metric.ball z_c r) (h1 : z₁ ∈ Metric.ball z_c r)
    (h2 : z₂ ∈ Metric.ball z_c r) :
    Smooth2Simplex.face2
        (affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₁ z₂ h0 h1 h2)
      = chartStraightLinePath_ball q z_c r hr hB z₀ z₁ h0 h1 := by
  refine smoothPath_ext_of_toPath_apply ?_ ?_ ?_
  · -- src
    change (affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₁ z₂ h0 h1 h2).toFun
            Smooth2Simplex.v0
        = (chartStraightLinePath_ball q z_c r hr hB z₀ z₁ h0 h1).src
    rw [affineChartTriangleSimplex_ball_toFun_v0,
        chartStraightLinePath_ball_src]
  · -- tgt
    change (affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₁ z₂ h0 h1 h2).toFun
            Smooth2Simplex.v1
        = (chartStraightLinePath_ball q z_c r hr hB z₀ z₁ h0 h1).tgt
    rw [affineChartTriangleSimplex_ball_toFun_v1,
        chartStraightLinePath_ball_tgt]
  · -- toPath: pointwise on the unit interval.
    intro t
    -- LHS = σ_ball(z₀, z₁, z₂).toFun(face2Param t.val)
    -- RHS = σ_ball(z₀, z₁, z₀).toFun(face2Param t.val)
    -- Both equal chart.symm((1 - t.val) z₀ + t.val z₁) since
    -- face2Param t.val = (t.val, 0) ∈ Δ² and the bump = 1 there.
    have h_mem := face2Param_val_mem_standardSimplex2 t
    have h_lhs := affineChartTriangleSimplex_ball_toFun_on_simplex q z_c r hr hB
      z₀ z₁ z₂ h0 h1 h2 h_mem
    have h_rhs := affineChartTriangleSimplex_ball_toFun_on_simplex q z_c r hr hB
      z₀ z₁ z₀ h0 h1 h0 h_mem
    show (affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₁ z₂ h0 h1 h2).toFun
            (Smooth2Simplex.face2Param t.val)
        = (affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₁ z₀ h0 h1 h0).toFun
            (Smooth2Simplex.face2Param t.val)
    rw [h_lhs, h_rhs]
    -- Reduce affineChartTriangle equality.
    congr 1
    unfold affineChartTriangle Smooth2Simplex.face2Param
    show (1 - t.val - 0) • z₀ + t.val • z₁ + (0 : ℝ) • z₂
        = (1 - t.val - 0) • z₀ + t.val • z₁ + (0 : ℝ) • z₀
    module

/-- Face-1 (v₀ → v₂) of the ball triangle `(z₀, z₁, z₂)` equals
`chartStraightLinePath_ball … z₀ z₂`. -/
lemma face1_eq_chartStraightLinePath_ball
    (q : X) (z_c : ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z_c r ⊆ (chartAt ℂ q).target)
    (z₀ z₁ z₂ : ℂ)
    (h0 : z₀ ∈ Metric.ball z_c r) (h1 : z₁ ∈ Metric.ball z_c r)
    (h2 : z₂ ∈ Metric.ball z_c r) :
    Smooth2Simplex.face1
        (affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₁ z₂ h0 h1 h2)
      = chartStraightLinePath_ball q z_c r hr hB z₀ z₂ h0 h2 := by
  refine smoothPath_ext_of_toPath_apply ?_ ?_ ?_
  · change (affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₁ z₂ h0 h1 h2).toFun
            Smooth2Simplex.v0
        = (chartStraightLinePath_ball q z_c r hr hB z₀ z₂ h0 h2).src
    rw [affineChartTriangleSimplex_ball_toFun_v0,
        chartStraightLinePath_ball_src]
  · change (affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₁ z₂ h0 h1 h2).toFun
            Smooth2Simplex.v2
        = (chartStraightLinePath_ball q z_c r hr hB z₀ z₂ h0 h2).tgt
    rw [affineChartTriangleSimplex_ball_toFun_v2,
        chartStraightLinePath_ball_tgt]
  · intro t
    have h_mem1 := face1Param_val_mem_standardSimplex2 t
    have h_mem2 := face2Param_val_mem_standardSimplex2 t
    have h_lhs := affineChartTriangleSimplex_ball_toFun_on_simplex q z_c r hr hB
      z₀ z₁ z₂ h0 h1 h2 h_mem1
    have h_rhs := affineChartTriangleSimplex_ball_toFun_on_simplex q z_c r hr hB
      z₀ z₂ z₀ h0 h2 h0 h_mem2
    show (affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₁ z₂ h0 h1 h2).toFun
            (Smooth2Simplex.face1Param t.val)
        = (affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₂ z₀ h0 h2 h0).toFun
            (Smooth2Simplex.face2Param t.val)
    rw [h_lhs, h_rhs]
    congr 1
    unfold affineChartTriangle Smooth2Simplex.face1Param Smooth2Simplex.face2Param
    show (1 - 0 - t.val) • z₀ + (0 : ℝ) • z₁ + t.val • z₂
        = (1 - t.val - 0) • z₀ + t.val • z₂ + (0 : ℝ) • z₀
    module

/-- Face-0 (v₁ → v₂) of the ball triangle `(z₀, z₁, z₂)` equals
`chartStraightLinePath_ball … z₁ z₂`. -/
lemma face0_eq_chartStraightLinePath_ball
    (q : X) (z_c : ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z_c r ⊆ (chartAt ℂ q).target)
    (z₀ z₁ z₂ : ℂ)
    (h0 : z₀ ∈ Metric.ball z_c r) (h1 : z₁ ∈ Metric.ball z_c r)
    (h2 : z₂ ∈ Metric.ball z_c r) :
    Smooth2Simplex.face0
        (affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₁ z₂ h0 h1 h2)
      = chartStraightLinePath_ball q z_c r hr hB z₁ z₂ h1 h2 := by
  refine smoothPath_ext_of_toPath_apply ?_ ?_ ?_
  · change (affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₁ z₂ h0 h1 h2).toFun
            Smooth2Simplex.v1
        = (chartStraightLinePath_ball q z_c r hr hB z₁ z₂ h1 h2).src
    rw [affineChartTriangleSimplex_ball_toFun_v1,
        chartStraightLinePath_ball_src]
  · change (affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₁ z₂ h0 h1 h2).toFun
            Smooth2Simplex.v2
        = (chartStraightLinePath_ball q z_c r hr hB z₁ z₂ h1 h2).tgt
    rw [affineChartTriangleSimplex_ball_toFun_v2,
        chartStraightLinePath_ball_tgt]
  · intro t
    have h_mem0 := face0Param_val_mem_standardSimplex2 t
    have h_mem2 := face2Param_val_mem_standardSimplex2 t
    have h_lhs := affineChartTriangleSimplex_ball_toFun_on_simplex q z_c r hr hB
      z₀ z₁ z₂ h0 h1 h2 h_mem0
    have h_rhs := affineChartTriangleSimplex_ball_toFun_on_simplex q z_c r hr hB
      z₁ z₂ z₁ h1 h2 h1 h_mem2
    show (affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₁ z₂ h0 h1 h2).toFun
            (Smooth2Simplex.face0Param t.val)
        = (affineChartTriangleSimplex_ball q z_c r hr hB z₁ z₂ z₁ h1 h2 h1).toFun
            (Smooth2Simplex.face2Param t.val)
    rw [h_lhs, h_rhs]
    congr 1
    unfold affineChartTriangle Smooth2Simplex.face0Param Smooth2Simplex.face2Param
    show (1 - (1 - t.val) - t.val) • z₀ + (1 - t.val) • z₁ + t.val • z₂
        = (1 - t.val - 0) • z₁ + t.val • z₂ + (0 : ℝ) • z₁
    module

/-! ## Boundary of the ball triangle as an explicit chain of canonical paths -/

/-- **Boundary of `affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₁ z₂ h0 h1 h2`**
as an explicit `SmoothChain` of three `chartStraightLinePath_ball`s
with alternating signs:
`single (z₁→z₂) - single (z₀→z₂) + single (z₀→z₁)`. -/
theorem affineChartTriangleSimplex_ball_boundary
    (q : X) (z_c : ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z_c r ⊆ (chartAt ℂ q).target)
    (z₀ z₁ z₂ : ℂ)
    (h0 : z₀ ∈ Metric.ball z_c r) (h1 : z₁ ∈ Metric.ball z_c r)
    (h2 : z₂ ∈ Metric.ball z_c r) :
    Smooth2Simplex.boundary
        (affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₁ z₂ h0 h1 h2)
      = SmoothChain.single (chartStraightLinePath_ball q z_c r hr hB z₁ z₂ h1 h2)
        - SmoothChain.single (chartStraightLinePath_ball q z_c r hr hB z₀ z₂ h0 h2)
        + SmoothChain.single (chartStraightLinePath_ball q z_c r hr hB z₀ z₁ h0 h1) := by
  unfold Smooth2Simplex.boundary
  rw [face0_eq_chartStraightLinePath_ball,
      face1_eq_chartStraightLinePath_ball,
      face2_eq_chartStraightLinePath_ball]

end JacobianChallenge

end
