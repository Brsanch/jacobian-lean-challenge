/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartStraightLinePath
import JacobianChallenge.Manifold.SmoothPathReverseStokesBoundary

set_option linter.unusedSectionVars false

/-! # Adjacent chart-triangle cancellation

When two affine chart-triangles share an edge in opposite orientations,
the shared chart-straight-line contributions cancel modulo
`stokesBoundaries`. Concretely, for σ₁ = (a, b, c) and σ₂ = (c, b, d)
(both using the same full-target chart), the shared edge is `(b, c)`
which appears as `path(b→c)` in `∂σ₁` and as `path(c→b)` in `∂σ₂`.
Since `path(c→b) = path(b→c).reverse` (chip
`chartStraightLinePath_univ_reverse`), the sum `single(path(b→c)) +
single(path(c→b))` lies in stokesBoundaries (chip
`single_smoothPath_plus_reverse_mem_stokesBoundaries`).

This file ships the SmoothCycle-level cancellation: the chain
`∂σ₁ + ∂σ₂` differs from the outer-boundary chain `outerBoundary` by
the cycle `single(path(b→c)) + single(path(c→b))`, which is in
stokesBoundaries.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- The sum of two chart-straight-line `single`s with reversed
orientation equals the SmoothCycle of forward-plus-reverse, which is
in `stokesBoundaries`. -/
lemma chartStraightLinePath_pair_eq_reverseSum
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z₀ z₁ : ℂ) :
    SmoothChain.single (chartStraightLinePath_univ q h_univ z₀ z₁)
        + SmoothChain.single (chartStraightLinePath_univ q h_univ z₁ z₀)
      = (single_smoothPath_plus_reverse_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := X)
            (chartStraightLinePath_univ q h_univ z₀ z₁)
          : SmoothChain (𝓘(ℝ, ℂ)) X) := by
  rw [single_smoothPath_plus_reverse_smoothCycle_coe]
  congr 2
  exact (chartStraightLinePath_univ_reverse q h_univ z₀ z₁).symm

/-- **Chart-straight-line pair-as-SmoothCycle is in stokesBoundaries.**
Combines the equality above with
`single_smoothPath_plus_reverse_mem_stokesBoundaries`. -/
lemma chartStraightLinePath_pair_smoothCycle_mem_stokesBoundaries
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z₀ z₁ : ℂ) :
    (single_smoothPath_plus_reverse_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := X)
        (chartStraightLinePath_univ q h_univ z₀ z₁))
      ∈ stokesBoundaries (𝓘(ℝ, ℂ)) X :=
  single_smoothPath_plus_reverse_mem_stokesBoundaries
    (chartStraightLinePath_univ q h_univ z₀ z₁)

/-! ## Two-triangle boundary as outer-edge chain + stokes-pair

For σ₁ = `affineChartTriangleSimplex_univ q hu a b c` (corners a, b, c)
and σ₂ = `affineChartTriangleSimplex_univ q hu c b d` (corners c, b, d
— note: σ₂ uses the b-c edge in reverse orientation: face2(σ₂) traces
c→b not b→c), the sum

  `∂σ₁ + ∂σ₂`

equals the outer-edge chain plus `single (path b→c) + single (path c→b)`.
The latter is a stokes-boundary cycle, so modulo stokes it equals the
outer-edge chain alone. -/

/-- **Explicit two-triangle boundary expansion** (no orientation
choice — both triangles use the same `face0 - face1 + face2` formula). -/
theorem two_chart_triangle_boundary_eq
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (a b c d : ℂ) :
    Smooth2Simplex.boundary (affineChartTriangleSimplex_univ q h_univ a b c)
      + Smooth2Simplex.boundary (affineChartTriangleSimplex_univ q h_univ c b d)
    = -- σ₁ boundary: single(b→c) - single(a→c) + single(a→b)
      SmoothChain.single (chartStraightLinePath_univ q h_univ b c)
      - SmoothChain.single (chartStraightLinePath_univ q h_univ a c)
      + SmoothChain.single (chartStraightLinePath_univ q h_univ a b)
      + (-- σ₂ boundary: single(b→d) - single(c→d) + single(c→b)
        SmoothChain.single (chartStraightLinePath_univ q h_univ b d)
        - SmoothChain.single (chartStraightLinePath_univ q h_univ c d)
        + SmoothChain.single (chartStraightLinePath_univ q h_univ c b)) := by
  rw [affineChartTriangleSimplex_univ_boundary,
      affineChartTriangleSimplex_univ_boundary]

end JacobianChallenge

end
