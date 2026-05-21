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

set_option linter.unusedSectionVars false

/-! # Affine chart-triangle smooth 2-simplex

The standard 2-simplex `Δ² = {(s, t) : s ≥ 0 ∧ t ≥ 0 ∧ s + t ≤ 1}` with
vertices `v₀ = (0, 0)`, `v₁ = (1, 0)`, `v₂ = (0, 1)`. For three points
`z₀, z₁, z₂ : ℂ`, the **affine interpolation** on the unit square is

```
A(s, t) := (1 - s - t) • z₀ + s • z₁ + t • z₂
```

extended affinely from Δ² to all of `ℝ²` (the formula is well-defined
on `ℝ²`; on Δ² it lies in the convex hull of `{z₀, z₁, z₂}`).

Lifted through a chart `(chartAt ℂ q).symm` with `target = univ`, this
yields a `Smooth2Simplex 𝓘(ℝ, ℂ) X` whose three boundary edges are
the chart-straight-line paths

* `v₀ → v₁`:  `t ↦ chart.symm((1 - t) • z₀ + t • z₁)`
* `v₀ → v₂`:  `t ↦ chart.symm((1 - t) • z₀ + t • z₂)`
* `v₁ → v₂` (diagonal):  `t ↦ chart.symm((1 - t) • z₁ + t • z₂)`

This is the natural chart-cell building block: each affine triangle in
the chart-target lifts to a smooth 2-simplex whose boundary consists of
three chart-straight-line paths. Summing such triangles over a chart-
cover-aware triangulation of a continuous null-homotopy gives a smooth
2-chain whose boundary is the polygonal-approximation loop of γ — the
smooth-Hurewicz step.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- The affine interpolation in `ℂ` of three corner values. -/
def affineChartTriangle (z₀ z₁ z₂ : ℂ) (s t : ℝ) : ℂ :=
  (1 - s - t) • z₀ + s • z₁ + t • z₂

/-- **Smoothness of `affineChartTriangle`** as a function `ℝ × ℝ → ℂ`. -/
lemma contDiff_affineChartTriangle (z₀ z₁ z₂ : ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (affineChartTriangle z₀ z₁ z₂)) := by
  unfold Function.uncurry affineChartTriangle
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => p.1) := contDiff_fst
  have ht : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => p.2) := contDiff_snd
  have h_w₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => 1 - p.1 - p.2) := (contDiff_const.sub hs).sub ht
  exact ((h_w₀.smul contDiff_const).add (hs.smul contDiff_const)).add
    (ht.smul contDiff_const)

/-- Reindexing `ℝ × ℝ → ℂ` to `(Fin 2 → ℝ) → ℂ`. -/
lemma contMDiff_affineChartTriangle_fin2 (z₀ z₁ z₂ : ℂ) :
    ContMDiff (𝓘(ℝ, Fin 2 → ℝ)) (𝓘(ℝ, ℂ)) ∞
      (fun x : Fin 2 → ℝ => affineChartTriangle z₀ z₁ z₂ (x 0) (x 1)) := by
  have h_reindex : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Fin 2 → ℝ => (x 0, x 1)) := by
    refine ContDiff.prodMk ?_ ?_
    · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).contDiff
    · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).contDiff
  have h_comp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Fin 2 → ℝ => affineChartTriangle z₀ z₁ z₂ (x 0) (x 1)) :=
    (contDiff_affineChartTriangle z₀ z₁ z₂).comp h_reindex
  exact h_comp.contMDiff

/-- The three affine coefficients are non-negative on `Δ²`. -/
lemma affineChartTriangle_coeffs_nonneg_on_simplex
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t ≤ 1) :
    0 ≤ 1 - s - t ∧ 0 ≤ s ∧ 0 ≤ t := by
  refine ⟨by linarith, hs, ht⟩

/-- The three affine coefficients sum to `1`. -/
lemma affineChartTriangle_coeffs_sum (s t : ℝ) :
    (1 - s - t) + s + t = 1 := by ring

/-- **`affineChartTriangle` lands in the convex hull of the corners** on
`Δ²`. -/
lemma affineChartTriangle_in_target_on_simplex
    {p₀ p₁ p₂ : X}
    (φ : OpenPartialHomeomorph X ℂ) (hφ_convex : Convex ℝ φ.target)
    (h0 : p₀ ∈ φ.source) (h1 : p₁ ∈ φ.source) (h2 : p₂ ∈ φ.source)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t ≤ 1) :
    affineChartTriangle (φ p₀) (φ p₁) (φ p₂) s t ∈ φ.target := by
  have hz0 : φ p₀ ∈ φ.target := φ.map_source h0
  have hz1 : φ p₁ ∈ φ.target := φ.map_source h1
  have hz2 : φ p₂ ∈ φ.target := φ.map_source h2
  -- Apply 3-point convexity via a Finset sum over `Fin 3`.
  let w : Fin 3 → ℝ := ![1 - s - t, s, t]
  let z : Fin 3 → ℂ := ![φ p₀, φ p₁, φ p₂]
  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ w i := by
    intro i _
    obtain ⟨ha, hb, hc⟩ := affineChartTriangle_coeffs_nonneg_on_simplex hs ht hst
    fin_cases i
    · show (0 : ℝ) ≤ 1 - s - t
      exact ha
    · show (0 : ℝ) ≤ s
      exact hb
    · show (0 : ℝ) ≤ t
      exact hc
  have h_sum : ∑ i ∈ Finset.univ, w i = 1 := by
    simp [Fin.sum_univ_three, w]; ring
  have h_mem : ∀ i ∈ Finset.univ, z i ∈ φ.target := by
    intro i _
    fin_cases i
    · exact hz0
    · exact hz1
    · exact hz2
  have h := hφ_convex.sum_mem h_nonneg h_sum h_mem
  simp only [Fin.sum_univ_three] at h
  show affineChartTriangle (φ p₀) (φ p₁) (φ p₂) s t ∈ φ.target
  unfold affineChartTriangle
  convert h using 2 <;> simp [w, z]

/-! ## Chart-triangle `Smooth2Simplex` (full-target case)

When `(chartAt ℂ q).target = univ`, the lifted map is globally smooth
and gives a `Smooth2Simplex 𝓘(ℝ, ℂ) X` directly. -/

/-- **Affine chart-triangle `Smooth2Simplex`** under
`(chartAt ℂ q).target = univ`. -/
noncomputable def affineChartTriangleSimplex_univ
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ)
    (z₀ z₁ z₂ : ℂ) :
    Smooth2Simplex (𝓘(ℝ, ℂ)) X where
  toFun := fun x : Fin 2 → ℝ =>
    (chartAt ℂ q).symm (affineChartTriangle z₀ z₁ z₂ (x 0) (x 1))
  smooth := by
    have h_inner :
        ContMDiff (𝓘(ℝ, Fin 2 → ℝ)) (𝓘(ℝ, ℂ)) ∞
          (fun x : Fin 2 → ℝ => affineChartTriangle z₀ z₁ z₂ (x 0) (x 1)) :=
      contMDiff_affineChartTriangle_fin2 _ _ _
    have h_symm_on : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (chartAt ℂ q).symm
        (chartAt ℂ q).target := contMDiffOn_chart_symm
    have h_symm : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (chartAt ℂ q).symm := by
      rw [show (chartAt ℂ q).target = Set.univ from h_univ] at h_symm_on
      exact (contMDiffOn_univ).mp h_symm_on
    exact h_symm.comp h_inner

/-! ## Sanity properties of the chart-triangle simplex -/

/-- The chart-triangle simplex's `toFun` at the three Δ²-vertices
recovers the three corner manifold points. -/
@[simp] lemma affineChartTriangleSimplex_univ_toFun_v0
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z₀ z₁ z₂ : ℂ) :
    (affineChartTriangleSimplex_univ q h_univ z₀ z₁ z₂).toFun
        Smooth2Simplex.v0 = (chartAt ℂ q).symm z₀ := by
  show (chartAt ℂ q).symm
      (affineChartTriangle z₀ z₁ z₂
        (Smooth2Simplex.v0 0) (Smooth2Simplex.v0 1))
    = (chartAt ℂ q).symm z₀
  congr 1
  unfold affineChartTriangle Smooth2Simplex.v0
  simp

@[simp] lemma affineChartTriangleSimplex_univ_toFun_v1
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z₀ z₁ z₂ : ℂ) :
    (affineChartTriangleSimplex_univ q h_univ z₀ z₁ z₂).toFun
        Smooth2Simplex.v1 = (chartAt ℂ q).symm z₁ := by
  show (chartAt ℂ q).symm
      (affineChartTriangle z₀ z₁ z₂
        (Smooth2Simplex.v1 0) (Smooth2Simplex.v1 1))
    = (chartAt ℂ q).symm z₁
  congr 1
  unfold affineChartTriangle Smooth2Simplex.v1
  simp

@[simp] lemma affineChartTriangleSimplex_univ_toFun_v2
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z₀ z₁ z₂ : ℂ) :
    (affineChartTriangleSimplex_univ q h_univ z₀ z₁ z₂).toFun
        Smooth2Simplex.v2 = (chartAt ℂ q).symm z₂ := by
  show (chartAt ℂ q).symm
      (affineChartTriangle z₀ z₁ z₂
        (Smooth2Simplex.v2 0) (Smooth2Simplex.v2 1))
    = (chartAt ℂ q).symm z₂
  congr 1
  unfold affineChartTriangle Smooth2Simplex.v2
  simp

end JacobianChallenge

end
