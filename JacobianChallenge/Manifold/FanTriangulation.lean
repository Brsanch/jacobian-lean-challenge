/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AdjacentTriangleCancellation

set_option linter.unusedSectionVars false

/-! # Fan-triangulation of a polygonal loop in a chart

Given a list of points `z_center, z₀, z₁, …, z_n : ℂ` (all in the chart
target of a full-target chart at `q : X`), the **fan triangulation**
consists of `n` triangles `(z_center, z_i, z_{i+1})` for `i = 0, …, n-1`.

The boundary of the resulting 2-chain, modulo stokesBoundaries, equals
the polygonal loop chain

  `single(path z₀→z₁) + single(path z₁→z₂) + … + single(path z_{n-1}→z_n)`

minus the "spokes" `path z_center→z_0` and `path z_n→z_center` (which
together close the polygonal loop into a closed cycle through z_center).

When the polygonal loop is itself closed (`z_n = z₀`) — i.e. the
"fan" is a triangulation of a closed polygon — the spokes cancel, and
the polygonal-loop chain lies in stokesBoundaries.

This file ships the **single-triangle** form for now (base case of
the fan): the boundary of one triangle `(z_center, zᵢ, zⱼ)` already
gives `single(path zᵢ→zⱼ)` modulo two spoke contributions. Generalizing
to an arbitrary fan is straightforward induction (next chip).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- The "fan spokes" pair for one triangle in a fan from `z_c`. -/
noncomputable def fanSpokesPair
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z_c z_i z_j : ℂ) :
    SmoothChain (𝓘(ℝ, ℂ)) X :=
  -SmoothChain.single (chartStraightLinePath_univ q h_univ z_c z_j)
    + SmoothChain.single (chartStraightLinePath_univ q h_univ z_c z_i)

/-- **One triangle's boundary = single(z_i → z_j) + fanSpokesPair.** -/
theorem affineChartTriangleSimplex_boundary_as_loop_plus_spokes
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z_c z_i z_j : ℂ) :
    Smooth2Simplex.boundary
        (affineChartTriangleSimplex_univ q h_univ z_c z_i z_j)
      = SmoothChain.single (chartStraightLinePath_univ q h_univ z_i z_j)
        + fanSpokesPair q h_univ z_c z_i z_j := by
  rw [affineChartTriangleSimplex_univ_boundary]
  unfold fanSpokesPair
  abel

/-- For a closed polygonal loop (start = end = `z₀`), the fan from a
single `z_c` to `(z₀, z₀)` is a *degenerate* triangle, but the
formula still produces a sensible cancellation: the two spoke
contributions `-single(z_c→z₀) + single(z_c→z₀) = 0`, leaving just
`single(z₀→z₀)`. -/
@[simp] lemma fanSpokesPair_degenerate
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z_c z : ℂ) :
    fanSpokesPair q h_univ z_c z z = 0 := by
  unfold fanSpokesPair
  abel

end JacobianChallenge

end
