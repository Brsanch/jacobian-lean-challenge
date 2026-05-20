/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexMidpointSubdivision
import JacobianChallenge.Manifold.ChartContainedSmooth2SimplexFromSimplexImage

set_option linter.unusedSectionVars false

/-! # Chart-containment of midpoint sub-triangles inherits from σ

If `σ : Smooth2Simplex 𝓘(ℝ, ℂ) X` is chart-contained on
`standardSimplex2` (i.e. `σ.toFun '' standardSimplex2 ⊆ chart-source`
and chart-image `⊆ ball`), then each sub-triangle of
`midpointSubdivision σ` is also chart-contained on
`standardSimplex2`.

The geometric content: convexity of `standardSimplex2`. Each
sub-triangle is built via `affineReparam σ v0' v1' v2'` with
`vᵢ' ∈ standardSimplex2`. For any `p ∈ standardSimplex2`,
`affineCombo v0' v1' v2' p` is a convex combination of `v0', v1', v2'`
with **non-negative weights summing to 1**, hence lies in
`standardSimplex2`. So
`(midpointSubdivision σ i).toFun p = σ.toFun (affineCombo … p)
  ∈ σ.toFun '' standardSimplex2 ⊆ chart-source`.

## What this file ships

* `Smooth2Simplex.midpoint01_mem_standardSimplex2`, `12`, `02` — the
  three midpoints lie in `Δ²`.
* `Smooth2Simplex.v0_mem_standardSimplex2`, `v1`, `v2` — the three
  vertices lie in `Δ²`.
* `Smooth2Simplex.affineCombo_mem_standardSimplex2` — if the three
  target vertices are in `Δ²` and the input is in `Δ²`, the output is
  in `Δ²`.
* `Smooth2Simplex.midpointSubdivision_image_in_source` — chart-source
  containment of each sub-triangle's image under `σ`.
* `Smooth2Simplex.midpointSubdivision_chart_image_in_ball` — same for
  ball.
* `Smooth2Simplex.midpointSubdivision_complexChainPeriod_zero` —
  composition: each sub-triangle has zero boundary period when σ is
  chart-contained.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace Smooth2Simplex

/-! ## Vertices and midpoints lie in `Δ²` -/

lemma v0_mem_standardSimplex2 : Smooth2Simplex.v0 ∈ standardSimplex2 := by
  unfold standardSimplex2 Smooth2Simplex.v0
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ℝ) ≤ ![0, 0] 0; simp
  · show (0 : ℝ) ≤ ![0, 0] 1; simp
  · show (![0, 0] 0 + ![0, 0] 1 : ℝ) ≤ 1; simp

lemma v1_mem_standardSimplex2 : Smooth2Simplex.v1 ∈ standardSimplex2 := by
  unfold standardSimplex2 Smooth2Simplex.v1
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ℝ) ≤ ![1, 0] 0; simp
  · show (0 : ℝ) ≤ ![1, 0] 1; simp
  · show (![1, 0] 0 + ![1, 0] 1 : ℝ) ≤ 1; simp

lemma v2_mem_standardSimplex2 : Smooth2Simplex.v2 ∈ standardSimplex2 := by
  unfold standardSimplex2 Smooth2Simplex.v2
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ℝ) ≤ ![0, 1] 0; simp
  · show (0 : ℝ) ≤ ![0, 1] 1; simp
  · show (![0, 1] 0 + ![0, 1] 1 : ℝ) ≤ 1; simp

lemma midpoint01_mem_standardSimplex2 :
    midpoint01 ∈ standardSimplex2 := by
  unfold standardSimplex2 midpoint01
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ℝ) ≤ ![1/2, 0] 0; simp
  · show (0 : ℝ) ≤ ![1/2, 0] 1; simp
  · show (![1/2, 0] 0 + ![1/2, 0] 1 : ℝ) ≤ 1; simp; norm_num

lemma midpoint12_mem_standardSimplex2 :
    midpoint12 ∈ standardSimplex2 := by
  unfold standardSimplex2 midpoint12
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ℝ) ≤ ![1/2, 1/2] 0; simp
  · show (0 : ℝ) ≤ ![1/2, 1/2] 1; simp
  · show (![1/2, 1/2] 0 + ![1/2, 1/2] 1 : ℝ) ≤ 1; simp; norm_num

lemma midpoint02_mem_standardSimplex2 :
    midpoint02 ∈ standardSimplex2 := by
  unfold standardSimplex2 midpoint02
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ℝ) ≤ ![0, 1/2] 0; simp
  · show (0 : ℝ) ≤ ![0, 1/2] 1; simp
  · show (![0, 1/2] 0 + ![0, 1/2] 1 : ℝ) ≤ 1; simp; norm_num

/-! ## Convex closure of `standardSimplex2` under `affineCombo` -/

/-- **`affineCombo` preserves `standardSimplex2`.**

If `v0' v1' v2' ∈ standardSimplex2` and `p ∈ standardSimplex2`, then
`affineCombo v0' v1' v2' p ∈ standardSimplex2`.

Geometrically: `standardSimplex2` is convex, and `affineCombo … p`
is a convex combination of `v0' v1' v2'` with weights
`(1 - p 0 - p 1, p 0, p 1)`, all `≥ 0` and summing to `1`. -/
lemma affineCombo_mem_standardSimplex2
    {v0' v1' v2' : Fin 2 → ℝ}
    (hv0 : v0' ∈ standardSimplex2)
    (hv1 : v1' ∈ standardSimplex2)
    (hv2 : v2' ∈ standardSimplex2)
    {p : Fin 2 → ℝ} (hp : p ∈ standardSimplex2) :
    affineCombo v0' v1' v2' p ∈ standardSimplex2 := by
  obtain ⟨hp0, hp1, hp_sum⟩ := hp
  obtain ⟨hv0_0, hv0_1, hv0_sum⟩ := hv0
  obtain ⟨hv1_0, hv1_1, hv1_sum⟩ := hv1
  obtain ⟨hv2_0, hv2_1, hv2_sum⟩ := hv2
  unfold standardSimplex2 affineCombo
  have h_coeff0 : (0 : ℝ) ≤ 1 - p 0 - p 1 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · -- 0 ≤ ((1 - p 0 - p 1) • v0' + p 0 • v1' + p 1 • v2') 0
    show (0 : ℝ) ≤ ((1 - p 0 - p 1) • v0' + p 0 • v1' + p 1 • v2') 0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : 0 ≤ (1 - p 0 - p 1) * v0' 0 := mul_nonneg h_coeff0 hv0_0
    have h2 : 0 ≤ p 0 * v1' 0 := mul_nonneg hp0 hv1_0
    have h3 : 0 ≤ p 1 * v2' 0 := mul_nonneg hp1 hv2_0
    linarith
  · show (0 : ℝ) ≤ ((1 - p 0 - p 1) • v0' + p 0 • v1' + p 1 • v2') 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : 0 ≤ (1 - p 0 - p 1) * v0' 1 := mul_nonneg h_coeff0 hv0_1
    have h2 : 0 ≤ p 0 * v1' 1 := mul_nonneg hp0 hv1_1
    have h3 : 0 ≤ p 1 * v2' 1 := mul_nonneg hp1 hv2_1
    linarith
  · -- sum ≤ 1: (a • v0' + b • v1' + c • v2') 0 + (...) 1
    -- = a (v0' 0 + v0' 1) + b (v1' 0 + v1' 1) + c (v2' 0 + v2' 1)
    -- ≤ a + b + c = 1.
    show (((1 - p 0 - p 1) • v0' + p 0 • v1' + p 1 • v2') 0
        + ((1 - p 0 - p 1) • v0' + p 0 • v1' + p 1 • v2') 1) ≤ 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    -- Rearrange: ((1-p0-p1)·(v0'0+v0'1)) + (p0·(v1'0+v1'1)) + (p1·(v2'0+v2'1)) ≤ 1.
    have h0_combined :
        (1 - p 0 - p 1) * v0' 0 + (1 - p 0 - p 1) * v0' 1
          = (1 - p 0 - p 1) * (v0' 0 + v0' 1) := by ring
    have h1_combined :
        p 0 * v1' 0 + p 0 * v1' 1 = p 0 * (v1' 0 + v1' 1) := by ring
    have h2_combined :
        p 1 * v2' 0 + p 1 * v2' 1 = p 1 * (v2' 0 + v2' 1) := by ring
    have hb0 : (1 - p 0 - p 1) * (v0' 0 + v0' 1) ≤ (1 - p 0 - p 1) * 1 :=
      mul_le_mul_of_nonneg_left hv0_sum h_coeff0
    have hb1 : p 0 * (v1' 0 + v1' 1) ≤ p 0 * 1 :=
      mul_le_mul_of_nonneg_left hv1_sum hp0
    have hb2 : p 1 * (v2' 0 + v2' 1) ≤ p 1 * 1 :=
      mul_le_mul_of_nonneg_left hv2_sum hp1
    linarith

/-! ## Each sub-triangle's `Δ²`-image lies in `σ`'s `Δ²`-image -/

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-- For each sub-triangle's target vertices, the convex hull
`affineCombo`'d at any `p ∈ standardSimplex2` lies in `standardSimplex2`. -/
private lemma midpointSubdivision_affineCombo_in_standardSimplex2
    (i : Fin 4) {p : Fin 2 → ℝ} (hp : p ∈ standardSimplex2) :
    match i with
    | ⟨0, _⟩ => affineCombo Smooth2Simplex.v0 midpoint01 midpoint02 p
                  ∈ standardSimplex2
    | ⟨1, _⟩ => affineCombo midpoint01 Smooth2Simplex.v1 midpoint12 p
                  ∈ standardSimplex2
    | ⟨2, _⟩ => affineCombo midpoint02 midpoint12 Smooth2Simplex.v2 p
                  ∈ standardSimplex2
    | ⟨3, _⟩ => affineCombo midpoint12 midpoint02 midpoint01 p
                  ∈ standardSimplex2 := by
  match i with
  | ⟨0, _⟩ =>
    exact affineCombo_mem_standardSimplex2
      v0_mem_standardSimplex2 midpoint01_mem_standardSimplex2
      midpoint02_mem_standardSimplex2 hp
  | ⟨1, _⟩ =>
    exact affineCombo_mem_standardSimplex2
      midpoint01_mem_standardSimplex2 v1_mem_standardSimplex2
      midpoint12_mem_standardSimplex2 hp
  | ⟨2, _⟩ =>
    exact affineCombo_mem_standardSimplex2
      midpoint02_mem_standardSimplex2 midpoint12_mem_standardSimplex2
      v2_mem_standardSimplex2 hp
  | ⟨3, _⟩ =>
    exact affineCombo_mem_standardSimplex2
      midpoint12_mem_standardSimplex2 midpoint02_mem_standardSimplex2
      midpoint01_mem_standardSimplex2 hp

/-! ## Chart-source containment of midpointSubdivision sub-triangles -/

/-- **Each midpointSubdivision sub-triangle inherits chart-source
containment from σ on `standardSimplex2`.** -/
theorem midpointSubdivision_image_in_source
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X) (basePoint : X)
    (h_σ : ∀ p ∈ standardSimplex2, σ.toFun p ∈ (chartAt ℂ basePoint).source)
    (i : Fin 4) :
    ∀ p ∈ standardSimplex2,
      (midpointSubdivision σ i).toFun p ∈ (chartAt ℂ basePoint).source := by
  intro p hp
  -- Unfold midpointSubdivision i to its affineReparam form, then apply h_σ.
  match i with
  | ⟨0, _⟩ =>
    show (affineReparam σ Smooth2Simplex.v0 midpoint01 midpoint02).toFun p
          ∈ (chartAt ℂ basePoint).source
    rw [affineReparam_apply]
    exact h_σ _ (affineCombo_mem_standardSimplex2
      v0_mem_standardSimplex2 midpoint01_mem_standardSimplex2
      midpoint02_mem_standardSimplex2 hp)
  | ⟨1, _⟩ =>
    show (affineReparam σ midpoint01 Smooth2Simplex.v1 midpoint12).toFun p
          ∈ (chartAt ℂ basePoint).source
    rw [affineReparam_apply]
    exact h_σ _ (affineCombo_mem_standardSimplex2
      midpoint01_mem_standardSimplex2 v1_mem_standardSimplex2
      midpoint12_mem_standardSimplex2 hp)
  | ⟨2, _⟩ =>
    show (affineReparam σ midpoint02 midpoint12 Smooth2Simplex.v2).toFun p
          ∈ (chartAt ℂ basePoint).source
    rw [affineReparam_apply]
    exact h_σ _ (affineCombo_mem_standardSimplex2
      midpoint02_mem_standardSimplex2 midpoint12_mem_standardSimplex2
      v2_mem_standardSimplex2 hp)
  | ⟨3, _⟩ =>
    show (affineReparam σ midpoint12 midpoint02 midpoint01).toFun p
          ∈ (chartAt ℂ basePoint).source
    rw [affineReparam_apply]
    exact h_σ _ (affineCombo_mem_standardSimplex2
      midpoint12_mem_standardSimplex2 midpoint02_mem_standardSimplex2
      midpoint01_mem_standardSimplex2 hp)

/-- **Each midpointSubdivision sub-triangle inherits chart-image-in-ball
containment from σ on `standardSimplex2`.** -/
theorem midpointSubdivision_chart_image_in_ball
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X) (basePoint : X)
    (ballCentre : ℂ) (ballRadius : ℝ)
    (h_σ : ∀ p ∈ standardSimplex2,
      (chartAt ℂ basePoint) (σ.toFun p) ∈ Metric.ball ballCentre ballRadius)
    (i : Fin 4) :
    ∀ p ∈ standardSimplex2,
      (chartAt ℂ basePoint) ((midpointSubdivision σ i).toFun p)
        ∈ Metric.ball ballCentre ballRadius := by
  intro p hp
  match i with
  | ⟨0, _⟩ =>
    show (chartAt ℂ basePoint)
        ((affineReparam σ Smooth2Simplex.v0 midpoint01 midpoint02).toFun p)
        ∈ Metric.ball ballCentre ballRadius
    rw [affineReparam_apply]
    exact h_σ _ (affineCombo_mem_standardSimplex2
      v0_mem_standardSimplex2 midpoint01_mem_standardSimplex2
      midpoint02_mem_standardSimplex2 hp)
  | ⟨1, _⟩ =>
    show (chartAt ℂ basePoint)
        ((affineReparam σ midpoint01 Smooth2Simplex.v1 midpoint12).toFun p)
        ∈ Metric.ball ballCentre ballRadius
    rw [affineReparam_apply]
    exact h_σ _ (affineCombo_mem_standardSimplex2
      midpoint01_mem_standardSimplex2 v1_mem_standardSimplex2
      midpoint12_mem_standardSimplex2 hp)
  | ⟨2, _⟩ =>
    show (chartAt ℂ basePoint)
        ((affineReparam σ midpoint02 midpoint12 Smooth2Simplex.v2).toFun p)
        ∈ Metric.ball ballCentre ballRadius
    rw [affineReparam_apply]
    exact h_σ _ (affineCombo_mem_standardSimplex2
      midpoint02_mem_standardSimplex2 midpoint12_mem_standardSimplex2
      v2_mem_standardSimplex2 hp)
  | ⟨3, _⟩ =>
    show (chartAt ℂ basePoint)
        ((affineReparam σ midpoint12 midpoint02 midpoint01).toFun p)
        ∈ Metric.ball ballCentre ballRadius
    rw [affineReparam_apply]
    exact h_σ _ (affineCombo_mem_standardSimplex2
      midpoint12_mem_standardSimplex2 midpoint02_mem_standardSimplex2
      midpoint01_mem_standardSimplex2 hp)

/-! ## Headline: each sub-triangle's boundary period vanishes -/

/-- **If `σ` is chart-contained on `standardSimplex2`, then each
sub-triangle of `midpointSubdivision σ` has zero complex boundary
period against every holomorphic 1-form.** -/
theorem midpointSubdivision_complexChainPeriod_zero
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X)
    (basePoint : X) (ballCentre : ℂ) (ballRadius : ℝ)
    (radius_pos : 0 < ballRadius)
    (ball_sub_target :
      Metric.ball ballCentre ballRadius ⊆ (chartAt ℂ basePoint).target)
    (h_image_in_source :
      ∀ p ∈ standardSimplex2, σ.toFun p ∈ (chartAt ℂ basePoint).source)
    (h_chart_image_in_ball :
      ∀ p ∈ standardSimplex2,
        (chartAt ℂ basePoint) (σ.toFun p) ∈ Metric.ball ballCentre ballRadius)
    (i : Fin 4) (α : HolomorphicOneForm X) :
    complexChainPeriod (Smooth2Simplex.boundary (midpointSubdivision σ i)) α = 0 :=
  complexChainPeriod_boundary_eq_zero_of_simplex_chartContained
    (midpointSubdivision σ i)
    basePoint ballCentre ballRadius radius_pos ball_sub_target
    (midpointSubdivision_image_in_source σ basePoint h_image_in_source i)
    (midpointSubdivision_chart_image_in_ball σ basePoint ballCentre ballRadius
      h_chart_image_in_ball i)
    α

end Smooth2Simplex

end JacobianChallenge

end
