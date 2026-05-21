/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AffineChartTriangleSimplex
import JacobianChallenge.Manifold.SmoothChain
import JacobianChallenge.Manifold.SmoothPathReverse
import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option linter.unusedSectionVars false

/-! # Chart-straight-line `SmoothPath` (full-target chart case)

Given a chart `(chartAt ℂ q)` with `target = univ` and two chart-image
endpoints `z₀ z₁ : ℂ`, the straight-line path

  `t ↦ chartAt q . symm ((1 - t) • z₀ + t • z₁)`

is a smooth path on `X` from `chart.symm z₀` to `chart.symm z₁`. This
file ships:

* `chartStraightLineMap` — the underlying ambient `ℝ → X` map.
* `chartStraightLineMap_contMDiff` — its `C^∞` smoothness.
* `chartStraightLinePath_univ` — a `SmoothPath 𝓘(ℝ, ℂ) X`.
* `chartStraightLinePath_univ_src` / `_tgt` — endpoint identifications.

These are the natural 1-simplex building blocks pairing with
`affineChartTriangleSimplex_univ`: the three faces of an affine
chart-triangle simplex are precisely chart-straight-line paths between
the three corner chart-images.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- The ambient `ℝ → X` map for the chart-straight-line path. -/
def chartStraightLineMap (q : X) (z₀ z₁ : ℂ) (t : ℝ) : X :=
  (chartAt ℂ q).symm ((1 - t) • z₀ + t • z₁)

/-- Smoothness of `chartStraightLineMap` under full-target chart. -/
lemma chartStraightLineMap_contMDiff (q : X) (h_univ : (chartAt ℂ q).target = Set.univ)
    (z₀ z₁ : ℂ) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) ∞ (chartStraightLineMap q z₀ z₁) := by
  unfold chartStraightLineMap
  -- Inner: ℝ → ℂ, t ↦ (1 - t) • z₀ + t • z₁ is smooth.
  have h_inner_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => (1 - t) • z₀ + t • z₁) := by
    have h_id : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => t) := contDiff_id
    have h_1mt : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => 1 - t) := contDiff_const.sub h_id
    exact (h_1mt.smul contDiff_const).add (h_id.smul contDiff_const)
  have h_inner : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) ∞
      (fun t : ℝ => (1 - t) • z₀ + t • z₁) := h_inner_cd.contMDiff
  -- chart.symm smooth on full target = univ.
  have h_symm_on : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (chartAt ℂ q).symm
      (chartAt ℂ q).target := contMDiffOn_chart_symm
  have h_symm : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (chartAt ℂ q).symm := by
    rw [show (chartAt ℂ q).target = Set.univ from h_univ] at h_symm_on
    exact (contMDiffOn_univ).mp h_symm_on
  exact h_symm.comp h_inner

/-- The chart-straight-line path's `src` (`t = 0`) lands at `chart.symm z₀`. -/
lemma chartStraightLineMap_zero (q : X) (z₀ z₁ : ℂ) :
    chartStraightLineMap q z₀ z₁ 0 = (chartAt ℂ q).symm z₀ := by
  unfold chartStraightLineMap
  simp

/-- The chart-straight-line path's `tgt` (`t = 1`) lands at `chart.symm z₁`. -/
lemma chartStraightLineMap_one (q : X) (z₀ z₁ : ℂ) :
    chartStraightLineMap q z₀ z₁ 1 = (chartAt ℂ q).symm z₁ := by
  unfold chartStraightLineMap
  simp

/-- **Chart-straight-line `SmoothPath`** under `(chartAt ℂ q).target = univ`. -/
noncomputable def chartStraightLinePath_univ
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z₀ z₁ : ℂ) :
    SmoothPath (𝓘(ℝ, ℂ)) X where
  src := (chartAt ℂ q).symm z₀
  tgt := (chartAt ℂ q).symm z₁
  toPath := {
    toContinuousMap :=
      ⟨fun t : unitInterval => chartStraightLineMap q z₀ z₁ t.val,
        ((chartStraightLineMap_contMDiff q h_univ z₀ z₁).continuous).comp
          continuous_subtype_val⟩
    source' := by simp [chartStraightLineMap_zero]
    target' := by simp [chartStraightLineMap_one]
  }
  smooth := by
    refine ⟨chartStraightLineMap q z₀ z₁, ?_, ?_⟩
    · exact chartStraightLineMap_contMDiff q h_univ z₀ z₁
    · intro t; rfl

@[simp] lemma chartStraightLinePath_univ_src
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z₀ z₁ : ℂ) :
    (chartStraightLinePath_univ q h_univ z₀ z₁).src = (chartAt ℂ q).symm z₀ := rfl

@[simp] lemma chartStraightLinePath_univ_tgt
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z₀ z₁ : ℂ) :
    (chartStraightLinePath_univ q h_univ z₀ z₁).tgt = (chartAt ℂ q).symm z₁ := rfl

/-! ## Faces of `affineChartTriangleSimplex_univ` as chart-straight-line paths

`Smooth2Simplex.boundary` of `affineChartTriangleSimplex_univ q hu z₀ z₁ z₂`
equals `single (face from v₁ to v₂) - single (face from v₀ to v₂) +
single (face from v₀ to v₁)`. Each face evaluates a chart-target
straight line; we identify each face's `toFun` with the corresponding
`chartStraightLineMap`. -/

private lemma face2_toFun_eq
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z₀ z₁ z₂ : ℂ) (t : ℝ) :
    (affineChartTriangleSimplex_univ q h_univ z₀ z₁ z₂).toFun
        (Smooth2Simplex.face2Param t)
      = chartStraightLineMap q z₀ z₁ t := by
  show (chartAt ℂ q).symm
      (affineChartTriangle z₀ z₁ z₂
        ((Smooth2Simplex.face2Param t) 0)
        ((Smooth2Simplex.face2Param t) 1))
    = (chartAt ℂ q).symm ((1 - t) • z₀ + t • z₁)
  congr 1
  show affineChartTriangle z₀ z₁ z₂ t 0 = (1 - t) • z₀ + t • z₁
  unfold affineChartTriangle
  show (1 - t - 0) • z₀ + t • z₁ + (0 : ℝ) • z₂ = (1 - t) • z₀ + t • z₁
  module

private lemma face1_toFun_eq
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z₀ z₁ z₂ : ℂ) (t : ℝ) :
    (affineChartTriangleSimplex_univ q h_univ z₀ z₁ z₂).toFun
        (Smooth2Simplex.face1Param t)
      = chartStraightLineMap q z₀ z₂ t := by
  show (chartAt ℂ q).symm
      (affineChartTriangle z₀ z₁ z₂
        ((Smooth2Simplex.face1Param t) 0)
        ((Smooth2Simplex.face1Param t) 1))
    = (chartAt ℂ q).symm ((1 - t) • z₀ + t • z₂)
  congr 1
  show affineChartTriangle z₀ z₁ z₂ 0 t = (1 - t) • z₀ + t • z₂
  unfold affineChartTriangle
  show (1 - 0 - t) • z₀ + (0 : ℝ) • z₁ + t • z₂ = (1 - t) • z₀ + t • z₂
  module

private lemma face0_toFun_eq
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z₀ z₁ z₂ : ℂ) (t : ℝ) :
    (affineChartTriangleSimplex_univ q h_univ z₀ z₁ z₂).toFun
        (Smooth2Simplex.face0Param t)
      = chartStraightLineMap q z₁ z₂ t := by
  show (chartAt ℂ q).symm
      (affineChartTriangle z₀ z₁ z₂
        ((Smooth2Simplex.face0Param t) 0)
        ((Smooth2Simplex.face0Param t) 1))
    = (chartAt ℂ q).symm ((1 - t) • z₁ + t • z₂)
  congr 1
  show affineChartTriangle z₀ z₁ z₂ (1 - t) t = (1 - t) • z₁ + t • z₂
  unfold affineChartTriangle
  show (1 - (1 - t) - t) • z₀ + (1 - t) • z₁ + t • z₂
      = (1 - t) • z₁ + t • z₂
  module

/-! ## Face-toFun equality: chip 14 lemmas are exported

The private `face_i_toFun_eq` lemmas above identify the toFun values of
each face with the corresponding `chartStraightLineMap`. Promoting
these to full `SmoothPath` equality requires an extensionality lemma
for `SmoothPath` which is not yet registered in tree; the toFun-level
identification is sufficient for downstream chain-level reasoning
that integrates over paths (since `complexChainPeriod` factors through
the toFun). -/

/-- Public re-export of `face2_toFun_eq` (pointwise on `ℝ`). -/
lemma affineChartTriangleSimplex_face2_toFun
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z₀ z₁ z₂ : ℂ) (t : ℝ) :
    (affineChartTriangleSimplex_univ q h_univ z₀ z₁ z₂).toFun
        (Smooth2Simplex.face2Param t)
      = chartStraightLineMap q z₀ z₁ t :=
  face2_toFun_eq q h_univ z₀ z₁ z₂ t

/-- Public re-export of `face1_toFun_eq`. -/
lemma affineChartTriangleSimplex_face1_toFun
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z₀ z₁ z₂ : ℂ) (t : ℝ) :
    (affineChartTriangleSimplex_univ q h_univ z₀ z₁ z₂).toFun
        (Smooth2Simplex.face1Param t)
      = chartStraightLineMap q z₀ z₂ t :=
  face1_toFun_eq q h_univ z₀ z₁ z₂ t

/-- Public re-export of `face0_toFun_eq`. -/
lemma affineChartTriangleSimplex_face0_toFun
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z₀ z₁ z₂ : ℂ) (t : ℝ) :
    (affineChartTriangleSimplex_univ q h_univ z₀ z₁ z₂).toFun
        (Smooth2Simplex.face0Param t)
      = chartStraightLineMap q z₁ z₂ t :=
  face0_toFun_eq q h_univ z₀ z₁ z₂ t

/-! ## SmoothPath equality lemma

The repository's `SmoothPath` structure has no `[ext]` lemma. We provide
one here, keyed on `src`/`tgt` equality + pointwise `toPath`-coercion
equality, sufficient for downstream identification of chart-triangle
faces as chart-straight-line paths. -/

/-- **Extensionality for `SmoothPath`.** Two smooth paths with equal
endpoints and equal underlying continuous maps are equal. -/
lemma smoothPath_ext_of_toPath_apply
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold (𝓘(ℝ, ℂ)) ⊤ Y]
    {γ₁ γ₂ : SmoothPath (𝓘(ℝ, ℂ)) Y}
    (h_src : γ₁.src = γ₂.src) (h_tgt : γ₁.tgt = γ₂.tgt)
    (h_toPath : ∀ t : unitInterval,
      (γ₁.toPath : unitInterval → Y) t = (γ₂.toPath : unitInterval → Y) t) :
    γ₁ = γ₂ := by
  rcases γ₁ with ⟨s₁, t₁, p₁, sm₁⟩
  rcases γ₂ with ⟨s₂, t₂, p₂, sm₂⟩
  obtain rfl : s₁ = s₂ := h_src
  obtain rfl : t₁ = t₂ := h_tgt
  congr 1
  exact Path.ext (funext h_toPath)

/-! ## Full SmoothPath identification of triangle faces

Using the ext lemma, we identify each face of `affineChartTriangleSimplex_univ`
as the corresponding `chartStraightLinePath_univ`. -/

/-- Face-2 (v₀ → v₁) equals `chartStraightLinePath_univ q hu z₀ z₁`. -/
lemma face2_eq_chartStraightLinePath_univ
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z₀ z₁ z₂ : ℂ) :
    Smooth2Simplex.face2
        (affineChartTriangleSimplex_univ q h_univ z₀ z₁ z₂)
      = chartStraightLinePath_univ q h_univ z₀ z₁ := by
  refine smoothPath_ext_of_toPath_apply ?_ ?_ ?_
  · -- src
    show (affineChartTriangleSimplex_univ q h_univ z₀ z₁ z₂).toFun
            Smooth2Simplex.v0
        = (chartAt ℂ q).symm z₀
    exact affineChartTriangleSimplex_univ_toFun_v0 q h_univ z₀ z₁ z₂
  · -- tgt
    show (affineChartTriangleSimplex_univ q h_univ z₀ z₁ z₂).toFun
            Smooth2Simplex.v1
        = (chartAt ℂ q).symm z₁
    exact affineChartTriangleSimplex_univ_toFun_v1 q h_univ z₀ z₁ z₂
  · -- toPath
    intro t
    exact affineChartTriangleSimplex_face2_toFun q h_univ z₀ z₁ z₂ t.val

/-- Face-1 (v₀ → v₂) equals `chartStraightLinePath_univ q hu z₀ z₂`. -/
lemma face1_eq_chartStraightLinePath_univ
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z₀ z₁ z₂ : ℂ) :
    Smooth2Simplex.face1
        (affineChartTriangleSimplex_univ q h_univ z₀ z₁ z₂)
      = chartStraightLinePath_univ q h_univ z₀ z₂ := by
  refine smoothPath_ext_of_toPath_apply ?_ ?_ ?_
  · show (affineChartTriangleSimplex_univ q h_univ z₀ z₁ z₂).toFun
            Smooth2Simplex.v0
        = (chartAt ℂ q).symm z₀
    exact affineChartTriangleSimplex_univ_toFun_v0 q h_univ z₀ z₁ z₂
  · show (affineChartTriangleSimplex_univ q h_univ z₀ z₁ z₂).toFun
            Smooth2Simplex.v2
        = (chartAt ℂ q).symm z₂
    exact affineChartTriangleSimplex_univ_toFun_v2 q h_univ z₀ z₁ z₂
  · intro t
    exact affineChartTriangleSimplex_face1_toFun q h_univ z₀ z₁ z₂ t.val

/-- Face-0 (v₁ → v₂) equals `chartStraightLinePath_univ q hu z₁ z₂`. -/
lemma face0_eq_chartStraightLinePath_univ
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z₀ z₁ z₂ : ℂ) :
    Smooth2Simplex.face0
        (affineChartTriangleSimplex_univ q h_univ z₀ z₁ z₂)
      = chartStraightLinePath_univ q h_univ z₁ z₂ := by
  refine smoothPath_ext_of_toPath_apply ?_ ?_ ?_
  · show (affineChartTriangleSimplex_univ q h_univ z₀ z₁ z₂).toFun
            Smooth2Simplex.v1
        = (chartAt ℂ q).symm z₁
    exact affineChartTriangleSimplex_univ_toFun_v1 q h_univ z₀ z₁ z₂
  · show (affineChartTriangleSimplex_univ q h_univ z₀ z₁ z₂).toFun
            Smooth2Simplex.v2
        = (chartAt ℂ q).symm z₂
    exact affineChartTriangleSimplex_univ_toFun_v2 q h_univ z₀ z₁ z₂
  · intro t
    exact affineChartTriangleSimplex_face0_toFun q h_univ z₀ z₁ z₂ t.val

/-! ## Reverse of a chart-straight-line path -/

/-- **`(chartStraightLinePath q hu z₀ z₁).reverse = chartStraightLinePath q hu z₁ z₀`.**

The reverse path traces the straight line backward, which is the same
as the straight-line interpolation between `z₁` (start) and `z₀` (end). -/
lemma chartStraightLinePath_univ_reverse
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z₀ z₁ : ℂ) :
    (chartStraightLinePath_univ q h_univ z₀ z₁).reverse
      = chartStraightLinePath_univ q h_univ z₁ z₀ := by
  refine smoothPath_ext_of_toPath_apply ?_ ?_ ?_
  · -- src of reverse = tgt of original = chart.symm z₁ = src of reversed.
    show (chartStraightLinePath_univ q h_univ z₀ z₁).tgt
        = (chartAt ℂ q).symm z₁
    rfl
  · show (chartStraightLinePath_univ q h_univ z₀ z₁).src
        = (chartAt ℂ q).symm z₀
    rfl
  · intro t
    -- Reverse's toPath = symm of original. unitInterval.symm sends t to ⟨1-t.val, _⟩.
    -- Both sides reduce to chart.symm(s·z₀ + (1-s)·z₁) where s = t.val.
    show ((chartStraightLinePath_univ q h_univ z₀ z₁).reverse.toPath
            : unitInterval → X) t
        = ((chartStraightLinePath_univ q h_univ z₁ z₀).toPath
            : unitInterval → X) t
    -- Unfold reverse.toPath = original.toPath.symm
    have h_lhs :
        ((chartStraightLinePath_univ q h_univ z₀ z₁).reverse.toPath
            : unitInterval → X) t
        = chartStraightLineMap q z₀ z₁ (1 - t.val) := by
      show ((chartStraightLinePath_univ q h_univ z₀ z₁).toPath.symm
              : unitInterval → X) t
          = chartStraightLineMap q z₀ z₁ (1 - t.val)
      have : ((chartStraightLinePath_univ q h_univ z₀ z₁).toPath.symm
                : unitInterval → X) t
            = chartStraightLineMap q z₀ z₁ (unitInterval.symm t).val := rfl
      rw [this]
      rfl
    have h_rhs :
        ((chartStraightLinePath_univ q h_univ z₁ z₀).toPath
            : unitInterval → X) t
        = chartStraightLineMap q z₁ z₀ t.val := rfl
    rw [h_lhs, h_rhs]
    unfold chartStraightLineMap
    congr 1
    -- (1 - (1-s))·z₀ + (1-s)·z₁ = (1 - s)·z₁ + s·z₀
    show (1 - (1 - t.val)) • z₀ + (1 - t.val) • z₁
        = (1 - t.val) • z₁ + t.val • z₀
    module

/-! ## Boundary of the chart-triangle simplex as an explicit chain -/

/-- **The boundary of `affineChartTriangleSimplex_univ q hu z₀ z₁ z₂`** as
an explicit `SmoothChain` of three chart-straight-line paths with
alternating signs: `single(z₁→z₂) - single(z₀→z₂) + single(z₀→z₁)`. -/
theorem affineChartTriangleSimplex_univ_boundary
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z₀ z₁ z₂ : ℂ) :
    Smooth2Simplex.boundary
        (affineChartTriangleSimplex_univ q h_univ z₀ z₁ z₂)
      = SmoothChain.single (chartStraightLinePath_univ q h_univ z₁ z₂)
        - SmoothChain.single (chartStraightLinePath_univ q h_univ z₀ z₂)
        + SmoothChain.single (chartStraightLinePath_univ q h_univ z₀ z₁) := by
  unfold Smooth2Simplex.boundary
  rw [face0_eq_chartStraightLinePath_univ,
      face1_eq_chartStraightLinePath_univ,
      face2_eq_chartStraightLinePath_univ]

end JacobianChallenge

end
