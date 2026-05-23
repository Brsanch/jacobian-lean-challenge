/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AffineChartTriangleSimplex
import JacobianChallenge.Manifold.ChartContainedSmooth2SimplexFromSimplexImage
import JacobianChallenge.Manifold.UniformChartContainmentDepth
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Normed.Module.Convex

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Affine chart-triangle `Smooth2Simplex` from chart-image-in-ball

Variant of `affineChartTriangleSimplex_univ` that drops the global
`(chartAt ℂ q).target = Set.univ` hypothesis in exchange for a
chart-image-in-ball assumption (`Metric.ball z_c r ⊆ (chartAt ℂ q).target`
plus `z₀ z₁ z₂ ∈ Metric.ball z_c r`).

On arbitrary compact connected complex 1-manifolds, chart-targets are
open subsets of `ℂ` rather than all of `ℂ`. The univ-version cannot
produce per-chart triangle simplices for such manifolds; this ball-
version can.

## Construction

The affine map
`A(x) = (1 - x_0 - x_1) • z₀ + x_0 • z₁ + x_1 • z₂`
maps `standardSimplex2` into the ball `B = Metric.ball z_c r`
(convex combination of three points in `B`). It can leave `B`
elsewhere, so we tame it by a smooth bump:

* `bumpΔ₂ z_c r z₀ z₁ z₂ h0 h1 h2 : (Fin 2 → ℝ) → ℝ` — smooth,
  `0 ≤ bump ≤ 1`, `bump = 1` on `standardSimplex2`, supported
  where `A` maps into the ball.

* `tamedAffine bump z_c z₀ z₁ z₂ x := bump x • A x + (1 - bump x) • z_c`.
  Smooth `ℝ² → ℂ`, lands in the ball (convex combination), and
  equals `A` on `standardSimplex2`.

* `affineChartTriangleSimplex_ball.toFun := chartAt q . symm ∘ tamedAffine`.
  ContMDiff `ℝ² → X` by `ContMDiffOn.comp_contMDiff` with
  `(chartAt ℂ q).symm` ContMDiffOn on the chart-target.

## What this file ships

* `affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₁ z₂ h0 h1 h2 :
    Smooth2Simplex (𝓘(ℝ, ℂ)) X` — the headline constructor.
* `affineChartTriangleSimplex_ball_toFun_v0/v1/v2` — vertex
  evaluations (`@[simp]`), matching the univ-version.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Step 1 — `standardSimplex2 ⊆ A⁻¹(ball z_c r)` -/

/-- The affine map `A` maps `standardSimplex2` into any ball that
contains the three corner points. -/
private lemma affineChartTriangle_mem_ball_on_simplex
    {z_c : ℂ} {r : ℝ}
    {z₀ z₁ z₂ : ℂ}
    (h0 : z₀ ∈ Metric.ball z_c r) (h1 : z₁ ∈ Metric.ball z_c r)
    (h2 : z₂ ∈ Metric.ball z_c r)
    {p : Fin 2 → ℝ} (hp : p ∈ standardSimplex2) :
    affineChartTriangle z₀ z₁ z₂ (p 0) (p 1) ∈ Metric.ball z_c r := by
  obtain ⟨hp0, hp1, hp_sum⟩ := hp
  have h_cv : Convex ℝ (Metric.ball z_c r) := convex_ball z_c r
  let w : Fin 3 → ℝ := ![1 - p 0 - p 1, p 0, p 1]
  let z : Fin 3 → ℂ := ![z₀, z₁, z₂]
  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ w i := by
    intro i _
    fin_cases i
    · show (0 : ℝ) ≤ 1 - p 0 - p 1; linarith
    · exact hp0
    · exact hp1
  have h_sum : ∑ i ∈ Finset.univ, w i = 1 := by
    simp [Fin.sum_univ_three, w]; ring
  have h_mem : ∀ i ∈ Finset.univ, z i ∈ Metric.ball z_c r := by
    intro i _
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have h := h_cv.sum_mem h_nonneg h_sum h_mem
  simp only [Fin.sum_univ_three] at h
  show affineChartTriangle z₀ z₁ z₂ (p 0) (p 1) ∈ Metric.ball z_c r
  unfold affineChartTriangle
  convert h using 1

/-! ## Step 2 — Smooth bump = 1 on `standardSimplex2`, supported in a given open set -/

/-- **Smooth cutoff for `standardSimplex2` inside an open superset.**

Given any open set `V ⊆ Fin 2 → ℝ` containing `standardSimplex2`,
there exists a smooth function `ρ : (Fin 2 → ℝ) → ℝ` with values
in `[0, 1]`, equal to `1` on `standardSimplex2`, and with
`tsupport ρ ⊆ V`. -/
private lemma exists_smoothBump_standardSimplex2_subset
    {V : Set (Fin 2 → ℝ)} (hV : IsOpen V)
    (hΔV : (standardSimplex2 : Set (Fin 2 → ℝ)) ⊆ V) :
    ∃ ρ : (Fin 2 → ℝ) → ℝ,
      ContMDiff (𝓘(ℝ, Fin 2 → ℝ)) (𝓘(ℝ)) ∞ ρ ∧
      (∀ x, ρ x ∈ Icc (0 : ℝ) 1) ∧
      EqOn ρ 1 standardSimplex2 ∧
      tsupport ρ ⊆ V := by
  -- Pick an open `W` with `standardSimplex2 ⊆ W ⊆ closure W ⊆ V`.
  obtain ⟨W, hW_open, hΔW, hWV⟩ :=
    normal_exists_closure_subset isClosed_standardSimplex2 hV hΔV
  have h_closed_compl : IsClosed (W : Set (Fin 2 → ℝ))ᶜ :=
    isClosed_compl_iff.mpr hW_open
  have h_disjoint :
      Disjoint ((W : Set (Fin 2 → ℝ))ᶜ) standardSimplex2 := by
    rw [Set.disjoint_left]
    intro x hx_compl hx_Δ
    exact hx_compl (hΔW hx_Δ)
  obtain ⟨f, hf_zero, hf_one, hf_Icc⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed (I := 𝓘(ℝ, Fin 2 → ℝ))
      (M := Fin 2 → ℝ) (n := (⊤ : ℕ∞)) h_closed_compl isClosed_standardSimplex2
      h_disjoint
  refine ⟨f, f.contMDiff, hf_Icc, hf_one, ?_⟩
  -- `support f ⊆ W` (from `ρ = 0` on `Wᶜ`), so `tsupport f ⊆ closure W ⊆ V`.
  have h_supp : Function.support (f : (Fin 2 → ℝ) → ℝ) ⊆ W := by
    intro x hx
    by_contra h_notin
    exact hx (hf_zero h_notin)
  have h_tsupp : tsupport (f : (Fin 2 → ℝ) → ℝ) ⊆ closure W := by
    unfold tsupport
    exact closure_mono h_supp
  exact h_tsupp.trans hWV

/-! ## Step 3 — Concrete bump tied to `(z₀, z₁, z₂)` data -/

/-- The existence package used by `bumpΔ₂` and its accessors. Pinning
the open set `V` and the membership proof here lets the accessors
share the same `Classical.choose` instance. -/
private noncomputable def bumpΔ₂_pack
    (z_c : ℂ) (r : ℝ) (z₀ z₁ z₂ : ℂ)
    (h0 : z₀ ∈ Metric.ball z_c r)
    (h1 : z₁ ∈ Metric.ball z_c r)
    (h2 : z₂ ∈ Metric.ball z_c r) :
    {ρ : (Fin 2 → ℝ) → ℝ //
      ContMDiff (𝓘(ℝ, Fin 2 → ℝ)) (𝓘(ℝ)) ∞ ρ ∧
      (∀ x, ρ x ∈ Icc (0 : ℝ) 1) ∧
      EqOn ρ 1 standardSimplex2 ∧
      tsupport ρ ⊆
        (fun x : Fin 2 → ℝ => affineChartTriangle z₀ z₁ z₂ (x 0) (x 1)) ⁻¹'
          Metric.ball z_c r} := by
  let h_exists :=
    exists_smoothBump_standardSimplex2_subset
      (V := (fun x : Fin 2 → ℝ => affineChartTriangle z₀ z₁ z₂ (x 0) (x 1)) ⁻¹'
          Metric.ball z_c r)
      (Metric.isOpen_ball.preimage
        (contMDiff_affineChartTriangle_fin2 z₀ z₁ z₂).continuous)
      (fun p hp => affineChartTriangle_mem_ball_on_simplex h0 h1 h2 hp)
  exact ⟨Classical.choose h_exists, Classical.choose_spec h_exists⟩

/-- The bump function used by `affineChartTriangleSimplex_ball`. -/
private noncomputable def bumpΔ₂
    (z_c : ℂ) (r : ℝ)
    (z₀ z₁ z₂ : ℂ)
    (h0 : z₀ ∈ Metric.ball z_c r)
    (h1 : z₁ ∈ Metric.ball z_c r)
    (h2 : z₂ ∈ Metric.ball z_c r) :
    (Fin 2 → ℝ) → ℝ :=
  (bumpΔ₂_pack z_c r z₀ z₁ z₂ h0 h1 h2).1

private lemma bumpΔ₂_smooth
    (z_c : ℂ) (r : ℝ) (z₀ z₁ z₂ : ℂ)
    (h0 : z₀ ∈ Metric.ball z_c r) (h1 : z₁ ∈ Metric.ball z_c r)
    (h2 : z₂ ∈ Metric.ball z_c r) :
    ContMDiff (𝓘(ℝ, Fin 2 → ℝ)) (𝓘(ℝ)) ∞
      (bumpΔ₂ z_c r z₀ z₁ z₂ h0 h1 h2) :=
  (bumpΔ₂_pack z_c r z₀ z₁ z₂ h0 h1 h2).2.1

private lemma bumpΔ₂_Icc
    (z_c : ℂ) (r : ℝ) (z₀ z₁ z₂ : ℂ)
    (h0 : z₀ ∈ Metric.ball z_c r) (h1 : z₁ ∈ Metric.ball z_c r)
    (h2 : z₂ ∈ Metric.ball z_c r) :
    ∀ x, bumpΔ₂ z_c r z₀ z₁ z₂ h0 h1 h2 x ∈ Icc (0 : ℝ) 1 :=
  (bumpΔ₂_pack z_c r z₀ z₁ z₂ h0 h1 h2).2.2.1

private lemma bumpΔ₂_one_on_simplex
    (z_c : ℂ) (r : ℝ) (z₀ z₁ z₂ : ℂ)
    (h0 : z₀ ∈ Metric.ball z_c r) (h1 : z₁ ∈ Metric.ball z_c r)
    (h2 : z₂ ∈ Metric.ball z_c r) :
    EqOn (bumpΔ₂ z_c r z₀ z₁ z₂ h0 h1 h2) 1 standardSimplex2 :=
  (bumpΔ₂_pack z_c r z₀ z₁ z₂ h0 h1 h2).2.2.2.1

private lemma bumpΔ₂_tsupport_subset
    (z_c : ℂ) (r : ℝ) (z₀ z₁ z₂ : ℂ)
    (h0 : z₀ ∈ Metric.ball z_c r) (h1 : z₁ ∈ Metric.ball z_c r)
    (h2 : z₂ ∈ Metric.ball z_c r) :
    tsupport (bumpΔ₂ z_c r z₀ z₁ z₂ h0 h1 h2) ⊆
      (fun x : Fin 2 → ℝ => affineChartTriangle z₀ z₁ z₂ (x 0) (x 1)) ⁻¹'
        Metric.ball z_c r :=
  (bumpΔ₂_pack z_c r z₀ z₁ z₂ h0 h1 h2).2.2.2.2

/-! ## Step 4 — The smooth global ambient extension `g : ℝ² → ℂ` -/

/-- The tamed affine extension: smooth `ℝ² → ℂ` map that equals
`affineChartTriangle z₀ z₁ z₂ (x 0) (x 1)` on `standardSimplex2`
and equals `z_c` off the bump's support. Always lands in
`Metric.ball z_c r`. -/
private noncomputable def tamedAffine
    (z_c : ℂ) (r : ℝ)
    (z₀ z₁ z₂ : ℂ)
    (h0 : z₀ ∈ Metric.ball z_c r) (h1 : z₁ ∈ Metric.ball z_c r)
    (h2 : z₂ ∈ Metric.ball z_c r) (x : Fin 2 → ℝ) : ℂ :=
  bumpΔ₂ z_c r z₀ z₁ z₂ h0 h1 h2 x •
      affineChartTriangle z₀ z₁ z₂ (x 0) (x 1)
    + (1 - bumpΔ₂ z_c r z₀ z₁ z₂ h0 h1 h2 x) • z_c

private lemma tamedAffine_smooth
    (z_c : ℂ) (r : ℝ) (z₀ z₁ z₂ : ℂ)
    (h0 : z₀ ∈ Metric.ball z_c r) (h1 : z₁ ∈ Metric.ball z_c r)
    (h2 : z₂ ∈ Metric.ball z_c r) :
    ContMDiff (𝓘(ℝ, Fin 2 → ℝ)) (𝓘(ℝ, ℂ)) ∞
      (tamedAffine z_c r z₀ z₁ z₂ h0 h1 h2) := by
  set ρ := bumpΔ₂ z_c r z₀ z₁ z₂ h0 h1 h2
  have hρ : ContMDiff (𝓘(ℝ, Fin 2 → ℝ)) (𝓘(ℝ)) ∞ ρ :=
    bumpΔ₂_smooth z_c r z₀ z₁ z₂ h0 h1 h2
  have hA : ContMDiff (𝓘(ℝ, Fin 2 → ℝ)) (𝓘(ℝ, ℂ)) ∞
      (fun x : Fin 2 → ℝ => affineChartTriangle z₀ z₁ z₂ (x 0) (x 1)) :=
    contMDiff_affineChartTriangle_fin2 z₀ z₁ z₂
  have h1ρ : ContMDiff (𝓘(ℝ, Fin 2 → ℝ)) (𝓘(ℝ)) ∞
      (fun x : Fin 2 → ℝ => 1 - ρ x) := contMDiff_const.sub hρ
  have h_zc : ContMDiff (𝓘(ℝ, Fin 2 → ℝ)) (𝓘(ℝ, ℂ)) ∞
      (fun _ : Fin 2 → ℝ => z_c) := contMDiff_const
  exact (hρ.smul hA).add (h1ρ.smul h_zc)

private lemma tamedAffine_eq_on_simplex
    (z_c : ℂ) (r : ℝ) (z₀ z₁ z₂ : ℂ)
    (h0 : z₀ ∈ Metric.ball z_c r) (h1 : z₁ ∈ Metric.ball z_c r)
    (h2 : z₂ ∈ Metric.ball z_c r)
    {x : Fin 2 → ℝ} (hx : x ∈ standardSimplex2) :
    tamedAffine z_c r z₀ z₁ z₂ h0 h1 h2 x =
      affineChartTriangle z₀ z₁ z₂ (x 0) (x 1) := by
  have hρx : bumpΔ₂ z_c r z₀ z₁ z₂ h0 h1 h2 x = 1 := by
    have := bumpΔ₂_one_on_simplex z_c r z₀ z₁ z₂ h0 h1 h2 hx
    simpa using this
  unfold tamedAffine
  rw [hρx]
  simp

private lemma tamedAffine_mem_ball
    (z_c : ℂ) (r : ℝ) (hr : 0 < r) (z₀ z₁ z₂ : ℂ)
    (h0 : z₀ ∈ Metric.ball z_c r) (h1 : z₁ ∈ Metric.ball z_c r)
    (h2 : z₂ ∈ Metric.ball z_c r) :
    ∀ x, tamedAffine z_c r z₀ z₁ z₂ h0 h1 h2 x ∈ Metric.ball z_c r := by
  intro x
  set ρ := bumpΔ₂ z_c r z₀ z₁ z₂ h0 h1 h2
  have h_Icc : ∀ y, ρ y ∈ Icc (0 : ℝ) 1 :=
    bumpΔ₂_Icc z_c r z₀ z₁ z₂ h0 h1 h2
  have h_supp :
      tsupport ρ ⊆
        (fun y : Fin 2 → ℝ => affineChartTriangle z₀ z₁ z₂ (y 0) (y 1)) ⁻¹'
          Metric.ball z_c r :=
    bumpΔ₂_tsupport_subset z_c r z₀ z₁ z₂ h0 h1 h2
  have h_zc : z_c ∈ Metric.ball z_c r := Metric.mem_ball_self hr
  by_cases hx : x ∈ tsupport ρ
  · -- On `tsupport ρ`, the affine value is in the ball; convex combo with `z_c`.
    have h_A : affineChartTriangle z₀ z₁ z₂ (x 0) (x 1) ∈ Metric.ball z_c r := h_supp hx
    have h_cv : Convex ℝ (Metric.ball z_c r) := convex_ball z_c r
    rw [convex_iff_add_mem] at h_cv
    have h_sum : ρ x + (1 - ρ x) = 1 := by ring
    exact h_cv h_A h_zc (h_Icc x).1 (by linarith [(h_Icc x).2]) h_sum
  · -- Off `tsupport ρ`, `ρ x = 0` so `tamedAffine = z_c`.
    have hρ0 : ρ x = 0 := by
      have hns : x ∉ Function.support ρ := fun h => hx (subset_tsupport ρ h)
      simpa [Function.support] using hns
    show ρ x • affineChartTriangle z₀ z₁ z₂ (x 0) (x 1) + (1 - ρ x) • z_c ∈
      Metric.ball z_c r
    rw [hρ0]
    simp [h_zc]

/-! ## Step 5 — The chart-image-in-ball `Smooth2Simplex` constructor -/

/-- **Affine chart-triangle `Smooth2Simplex` (chart-image-in-ball
version).**

Given `q : X`, an open ball `Metric.ball z_c r ⊆ (chartAt ℂ q).target`
and three points `z₀ z₁ z₂ ∈ Metric.ball z_c r`, produces a
`Smooth2Simplex 𝓘(ℝ, ℂ) X` whose three Δ²-vertex values are
`(chartAt ℂ q).symm z_i`.

No `(chartAt ℂ q).target = univ` hypothesis. Replaces it with
chart-image-in-ball, which is exactly the data produced by
`UniformChartContainmentDepth_named` (already unconditional in tree)
for subdivision sub-simplices on arbitrary compact connected
complex 1-manifolds. -/
noncomputable def affineChartTriangleSimplex_ball
    (q : X) (z_c : ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z_c r ⊆ (chartAt ℂ q).target)
    (z₀ z₁ z₂ : ℂ)
    (h0 : z₀ ∈ Metric.ball z_c r) (h1 : z₁ ∈ Metric.ball z_c r)
    (h2 : z₂ ∈ Metric.ball z_c r) :
    Smooth2Simplex (𝓘(ℝ, ℂ)) X where
  toFun := fun x => (chartAt ℂ q).symm (tamedAffine z_c r z₀ z₁ z₂ h0 h1 h2 x)
  smooth := by
    have hg : ContMDiff (𝓘(ℝ, Fin 2 → ℝ)) (𝓘(ℝ, ℂ)) ∞
        (tamedAffine z_c r z₀ z₁ z₂ h0 h1 h2) :=
      tamedAffine_smooth z_c r z₀ z₁ z₂ h0 h1 h2
    have hg_target : ∀ x,
        tamedAffine z_c r z₀ z₁ z₂ h0 h1 h2 x ∈ (chartAt ℂ q).target := fun x =>
      hB (tamedAffine_mem_ball z_c r hr z₀ z₁ z₂ h0 h1 h2 x)
    have h_symm : ContMDiffOn (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ∞
        ((chartAt ℂ q).symm) ((chartAt ℂ q).target) := contMDiffOn_chart_symm
    exact h_symm.comp_contMDiff hg hg_target

/-! ## Step 6 — Vertex-evaluation `@[simp]` lemmas -/

@[simp] lemma affineChartTriangleSimplex_ball_toFun_v0
    (q : X) (z_c : ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z_c r ⊆ (chartAt ℂ q).target)
    (z₀ z₁ z₂ : ℂ)
    (h0 : z₀ ∈ Metric.ball z_c r) (h1 : z₁ ∈ Metric.ball z_c r)
    (h2 : z₂ ∈ Metric.ball z_c r) :
    (affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₁ z₂ h0 h1 h2).toFun
        Smooth2Simplex.v0 = (chartAt ℂ q).symm z₀ := by
  change (chartAt ℂ q).symm (tamedAffine z_c r z₀ z₁ z₂ h0 h1 h2
      Smooth2Simplex.v0) = (chartAt ℂ q).symm z₀
  congr 1
  rw [tamedAffine_eq_on_simplex z_c r z₀ z₁ z₂ h0 h1 h2
        Smooth2Simplex.v0_mem_standardSimplex2]
  unfold affineChartTriangle Smooth2Simplex.v0
  simp

@[simp] lemma affineChartTriangleSimplex_ball_toFun_v1
    (q : X) (z_c : ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z_c r ⊆ (chartAt ℂ q).target)
    (z₀ z₁ z₂ : ℂ)
    (h0 : z₀ ∈ Metric.ball z_c r) (h1 : z₁ ∈ Metric.ball z_c r)
    (h2 : z₂ ∈ Metric.ball z_c r) :
    (affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₁ z₂ h0 h1 h2).toFun
        Smooth2Simplex.v1 = (chartAt ℂ q).symm z₁ := by
  change (chartAt ℂ q).symm (tamedAffine z_c r z₀ z₁ z₂ h0 h1 h2
      Smooth2Simplex.v1) = (chartAt ℂ q).symm z₁
  congr 1
  rw [tamedAffine_eq_on_simplex z_c r z₀ z₁ z₂ h0 h1 h2
        Smooth2Simplex.v1_mem_standardSimplex2]
  unfold affineChartTriangle Smooth2Simplex.v1
  simp

@[simp] lemma affineChartTriangleSimplex_ball_toFun_v2
    (q : X) (z_c : ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z_c r ⊆ (chartAt ℂ q).target)
    (z₀ z₁ z₂ : ℂ)
    (h0 : z₀ ∈ Metric.ball z_c r) (h1 : z₁ ∈ Metric.ball z_c r)
    (h2 : z₂ ∈ Metric.ball z_c r) :
    (affineChartTriangleSimplex_ball q z_c r hr hB z₀ z₁ z₂ h0 h1 h2).toFun
        Smooth2Simplex.v2 = (chartAt ℂ q).symm z₂ := by
  change (chartAt ℂ q).symm (tamedAffine z_c r z₀ z₁ z₂ h0 h1 h2
      Smooth2Simplex.v2) = (chartAt ℂ q).symm z₂
  congr 1
  rw [tamedAffine_eq_on_simplex z_c r z₀ z₁ z₂ h0 h1 h2
        Smooth2Simplex.v2_mem_standardSimplex2]
  unfold affineChartTriangle Smooth2Simplex.v2
  simp

end JacobianChallenge

end
