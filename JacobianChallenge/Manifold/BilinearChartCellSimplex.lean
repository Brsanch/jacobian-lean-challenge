/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Complex.Basic

set_option linter.unusedSectionVars false

/-! # Bilinear chart-cell convex containment (definition + convex coefficients)

Foundation for chart-cell smooth 2-simplex constructions used in the
smooth-Hurewicz step of item 14's reverse leg. Given a complex
1-manifold `X` and a chart `φ : X → ℂ` with **convex target**, four
points `p_{ij} ∈ φ.source` (`i, j ∈ {0, 1}`) lift to
`z_{ij} := φ p_{ij} ∈ φ.target`. The **bilinear interpolation** on
the unit square

```
B(s, t) := ((1-s)(1-t)) · z₀₀ + ((1-s) t) · z₀₁ + (s (1-t)) · z₁₀ + (s t) · z₁₁
```

is a convex combination of the four corner values whenever
`(s, t) ∈ [0, 1]²`.

This file ships:

* `bilinearChartInterp` — the definition.
* `bilinearChartInterp_coeffs_nonneg` — non-negativity of the four
  coefficients on `[0, 1]²`.
* `bilinearChartInterp_coeffs_sum` — coefficients sum to `1`.

These are the convex-combination ingredients underlying chart-cell
smooth-2-simplex constructions. The convex-containment conclusion
(`B(s, t) ∈ φ.target` under `Convex ℝ φ.target` + corners in
`φ.source`) and smoothness of `B` are separate follow-up chips.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology
open Set

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- The bilinear interpolation in `ℂ` of four corner values. -/
def bilinearChartInterp (z₀₀ z₀₁ z₁₀ z₁₁ : ℂ) (s t : ℝ) : ℂ :=
  ((1 - s) * (1 - t)) • z₀₀
    + ((1 - s) * t) • z₀₁
    + (s * (1 - t)) • z₁₀
    + (s * t) • z₁₁

/-- The four bilinear coefficients are non-negative on `[0,1]²`. -/
lemma bilinearChartInterp_coeffs_nonneg
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ (1 - s) * (1 - t) ∧ 0 ≤ (1 - s) * t ∧
      0 ≤ s * (1 - t) ∧ 0 ≤ s * t := by
  obtain ⟨hs_lb, hs_ub⟩ := hs
  obtain ⟨ht_lb, ht_ub⟩ := ht
  refine ⟨mul_nonneg ?_ ?_, mul_nonneg ?_ ht_lb,
         mul_nonneg hs_lb ?_, mul_nonneg hs_lb ht_lb⟩ <;> linarith

/-- The four bilinear coefficients sum to `1`. -/
lemma bilinearChartInterp_coeffs_sum (s t : ℝ) :
    (1 - s) * (1 - t) + (1 - s) * t + s * (1 - t) + s * t = 1 := by ring

end JacobianChallenge

end
