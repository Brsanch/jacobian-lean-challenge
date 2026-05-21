/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2Simplex
import JacobianChallenge.Manifold.ComplexManifoldRealification
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike

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

open scoped Manifold Topology ContDiff
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

/-- **Smoothness of `bilinearChartInterp` as `(s, t) : ℝ²`.**
`bilinearChartInterp z₀₀ z₀₁ z₁₀ z₁₁` is `C^∞` jointly in `(s, t)`. -/
lemma contDiff_bilinearChartInterp (z₀₀ z₀₁ z₁₀ z₁₁ : ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (bilinearChartInterp z₀₀ z₀₁ z₁₀ z₁₁)) := by
  -- `B(s, t) = polynomial(s, t) · constants`. All smooth.
  unfold Function.uncurry bilinearChartInterp
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => p.1) := contDiff_fst
  have ht : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => p.2) := contDiff_snd
  have h1ms : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => 1 - p.1) := contDiff_const.sub hs
  have h1mt : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => 1 - p.2) := contDiff_const.sub ht
  have h00 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (1 - p.1) * (1 - p.2)) := h1ms.mul h1mt
  have h01 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (1 - p.1) * p.2) := h1ms.mul ht
  have h10 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => p.1 * (1 - p.2)) := hs.mul h1mt
  have h11 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => p.1 * p.2) := hs.mul ht
  exact (((h00.smul contDiff_const).add (h01.smul contDiff_const)).add
    (h10.smul contDiff_const)).add (h11.smul contDiff_const)

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

/-! ## Chart-cell `Smooth2Simplex` from a full-target chart

When the chart `φ` has `φ.target = univ` (e.g. the standard
`chartN`/`chartS` on `RiemannSphere`), the bilinear interpolation
`B : ℝ² → ℂ` lands in `φ.target = ℂ` automatically, and the lifted
map `φ.symm ∘ B` is smooth globally as a `(Fin 2 → ℝ) → X` map. -/

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- Convert a `Function.uncurry`-style `ℝ × ℝ → ℂ` smooth map into a
`(Fin 2 → ℝ) → ℂ` smooth map by reindexing. -/
private lemma contDiff_of_uncurry_finTwo {f : ℝ → ℝ → ℂ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry f)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Fin 2 → ℝ => f (x 0) (x 1)) := by
  have h_reindex : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Fin 2 → ℝ => (x 0, x 1)) := by
    refine ContDiff.prodMk ?_ ?_
    · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).contDiff
    · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).contDiff
  exact hf.comp h_reindex

/-- **Smoothness of `bilinearChartInterp` as `(Fin 2 → ℝ) → ℂ`** —
the `Smooth2Simplex`-shape version. -/
lemma contMDiff_bilinearChartInterp_fin2 (z₀₀ z₀₁ z₁₀ z₁₁ : ℂ) :
    ContMDiff (𝓘(ℝ, Fin 2 → ℝ)) (𝓘(ℝ, ℂ)) ∞
      (fun x : Fin 2 → ℝ => bilinearChartInterp z₀₀ z₀₁ z₁₀ z₁₁ (x 0) (x 1)) :=
  (contDiff_of_uncurry_finTwo (contDiff_bilinearChartInterp z₀₀ z₀₁ z₁₀ z₁₁)).contMDiff

/-! ## Chart-cell `Smooth2Simplex` from a `chart.target = univ` chart

The scalar-tower bridge from `[IsManifold 𝓘(ℂ, ℂ) ω X]` to
`[IsManifold 𝓘(ℝ, ℂ) ⊤ X]` is supplied by the in-tree
`complexManifoldRealification` instance. With that automatic, the
construction below combines:

* `contMDiff_bilinearChartInterp_fin2` (smoothness of bilinear
  interpolation as `(Fin 2 → ℝ) → ℂ`);
* `contMDiffOn_chart_symm` for `chart.symm` on `chart.target`
  (restricted to `univ` when `chart.target = univ`);
* `ContMDiff.comp` to compose.

The result is a `Smooth2Simplex 𝓘(ℝ, ℂ) X`. -/

/-- **Bilinear chart-cell `Smooth2Simplex`** under
`(chartAt ℂ q).target = univ`. The map
`x ↦ (chartAt ℂ q).symm (bilinearChartInterp z₀₀ z₀₁ z₁₀ z₁₁ (x 0) (x 1))`
is a `Smooth2Simplex 𝓘(ℝ, ℂ) X`. -/
noncomputable def bilinearChartCellSimplex_univ
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ)
    (z₀₀ z₀₁ z₁₀ z₁₁ : ℂ) :
    Smooth2Simplex (𝓘(ℝ, ℂ)) X where
  toFun := fun x : Fin 2 → ℝ =>
    (chartAt ℂ q).symm
      (bilinearChartInterp z₀₀ z₀₁ z₁₀ z₁₁ (x 0) (x 1))
  smooth := by
    have h_inner :
        ContMDiff (𝓘(ℝ, Fin 2 → ℝ)) (𝓘(ℝ, ℂ)) ∞
          (fun x : Fin 2 → ℝ =>
            bilinearChartInterp z₀₀ z₀₁ z₁₀ z₁₁ (x 0) (x 1)) :=
      contMDiff_bilinearChartInterp_fin2 _ _ _ _
    -- `chart.symm` is `ContMDiffOn` on `chart.target = univ`. Hence
    -- `ContMDiff` everywhere — under the ℝ-model brought in by
    -- `complexManifoldRealification`.
    have h_symm_on : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (chartAt ℂ q).symm
        (chartAt ℂ q).target :=
      contMDiffOn_chart_symm
    have h_symm : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (chartAt ℂ q).symm := by
      rw [show (chartAt ℂ q).target = Set.univ from h_univ] at h_symm_on
      exact (contMDiffOn_univ).mp h_symm_on
    exact h_symm.comp h_inner

end JacobianChallenge

end
