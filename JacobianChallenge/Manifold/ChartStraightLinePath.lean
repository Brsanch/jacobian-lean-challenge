/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AffineChartTriangleSimplex
import JacobianChallenge.Manifold.SmoothChain
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

end JacobianChallenge

end
