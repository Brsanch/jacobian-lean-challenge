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

/-- On `[0, 1]²` with convex `φ.target` containing all four corner
images, `bilinearChartInterp` lands in `φ.target`. -/
lemma bilinearChartInterp_in_target_on_unit_square
    {p₀₀ p₀₁ p₁₀ p₁₁ : X}
    (φ : OpenPartialHomeomorph X ℂ) (hφ_convex : Convex ℝ φ.target)
    (h00 : p₀₀ ∈ φ.source) (h01 : p₀₁ ∈ φ.source)
    (h10 : p₁₀ ∈ φ.source) (h11 : p₁₁ ∈ φ.source)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    bilinearChartInterp (φ p₀₀) (φ p₀₁) (φ p₁₀) (φ p₁₁) s t ∈ φ.target := by
  -- Package as a Finset sum over `Fin 4`, then apply `Convex.sum_mem`.
  let w : Fin 4 → ℝ := ![(1 - s) * (1 - t), (1 - s) * t, s * (1 - t), s * t]
  let z : Fin 4 → ℂ := ![φ p₀₀, φ p₀₁, φ p₁₀, φ p₁₁]
  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ w i := by
    intro i _
    obtain ⟨ha, hb, hc, hd⟩ := bilinearChartInterp_coeffs_nonneg hs ht
    fin_cases i <;> simp [w] <;> assumption
  have h_sum : ∑ i ∈ Finset.univ, w i = 1 := by
    have : (∑ i : Fin 4, w i) = w 0 + w 1 + w 2 + w 3 := by
      simp [Fin.sum_univ_four]
    rw [show (∑ i ∈ Finset.univ, w i) = (∑ i : Fin 4, w i) from rfl, this]
    show (1 - s) * (1 - t) + (1 - s) * t + s * (1 - t) + s * t = 1
    ring
  have h_mem : ∀ i ∈ Finset.univ, z i ∈ φ.target := by
    intro i _
    fin_cases i
    · exact φ.map_source h00
    · exact φ.map_source h01
    · exact φ.map_source h10
    · exact φ.map_source h11
  have h := hφ_convex.sum_mem h_nonneg h_sum h_mem
  -- Reduce the sum to the bilinear formula by Fin.sum_univ_four.
  simp only [Fin.sum_univ_four] at h
  show bilinearChartInterp (φ p₀₀) (φ p₀₁) (φ p₁₀) (φ p₁₁) s t ∈ φ.target
  unfold bilinearChartInterp
  convert h using 2 <;> simp [w, z]

end JacobianChallenge

end
