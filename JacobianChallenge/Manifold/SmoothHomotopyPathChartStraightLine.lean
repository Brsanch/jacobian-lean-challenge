/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothHomotopyPathDiagonalSplit
import JacobianChallenge.Manifold.ChartStraightLinePath

set_option linter.unusedSectionVars false

/-! # `SmoothHomotopyPath` from a chart-contained path to its chart-straight-line

Given a smooth path `γ : SmoothPath 𝓘(ℝ, ℂ) Y` with global containment
in `(chartAt ℂ q).source` (full-target chart), the chart-target straight-
line interpolation between `γ.amb` and the chart-straight-line between
γ's endpoints packages into a `SmoothHomotopyPath γ γ_line`.

We use a **direct** homotopy ambient that inlines the chart-straight-
line formula (avoiding `γ_line.ambient`, which is `Classical.choose`
and opaque outside the unit interval):

```
H(s, t) := chart.symm(
  (1 - s) • chart(γ.amb t)
    + s • ((1 - t) • chart(γ.src) + t • chart(γ.tgt)))
```

When chart.target = univ, smoothness is global. The unit-interval
edge identities `left_edge`, `right_edge` then trace `γ.toPath` and
`γ_line.toPath` respectively (via `ambient_eq_on_unitInterval` and
the construction of `γ_line.toPath`).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-- The **direct** chart-target straight-line homotopy ambient: a smooth
`(Fin 2 → ℝ) → Y` map inlining the chart-straight-line formula (no
`γ_line.ambient` used). -/
noncomputable def chartHomotopyMapDirect
    (q : Y) (γ : SmoothPath (𝓘(ℝ, ℂ)) Y) (x : Fin 2 → ℝ) : Y :=
  (chartAt ℂ q).symm
    ((1 - x 0) • (chartAt ℂ q) (γ.ambient (x 1))
      + x 0 • ((1 - x 1) • (chartAt ℂ q) γ.src
                + x 1 • (chartAt ℂ q) γ.tgt))

/-- **Smoothness of `chartHomotopyMapDirect`** under full-target chart +
global γ-containment hypothesis. -/
lemma contMDiff_chartHomotopyMapDirect_univ
    (q : Y) (h_univ : (chartAt ℂ q).target = Set.univ)
    (γ : SmoothPath (𝓘(ℝ, ℂ)) Y)
    (h_in : ∀ t : ℝ, γ.ambient t ∈ (chartAt ℂ q).source) :
    ContMDiff (𝓘(ℝ, Fin 2 → ℝ)) (𝓘(ℝ, ℂ)) ∞
      (chartHomotopyMapDirect q γ) := by
  unfold chartHomotopyMapDirect
  -- Build piece by piece.
  have hproj0 : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun x : Fin 2 → ℝ => x 0) :=
    ((ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff).contMDiff
  have hproj1 : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun x : Fin 2 → ℝ => x 1) :=
    ((ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff).contMDiff
  have h1ms : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun x : Fin 2 → ℝ => 1 - x 0) := contMDiff_const.sub hproj0
  have h1mt : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun x : Fin 2 → ℝ => 1 - x 1) := contMDiff_const.sub hproj1
  -- chart ∘ γ.ambient is smooth on the set where γ.ambient ∈ chart.source —
  -- which is everywhere by hypothesis.
  have h_chart_on : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (chartAt ℂ q)
      (chartAt ℂ q).source := contMDiffOn_chart
  have h_chart_γ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
      (fun t : ℝ => (chartAt ℂ q) (γ.ambient t)) :=
    h_chart_on.comp_contMDiff γ.ambient_contMDiff h_in
  have h_chart_γ_x : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => (chartAt ℂ q) (γ.ambient (x 1))) :=
    h_chart_γ.comp hproj1
  -- Inner second component (straight-line of γ.src/tgt in chart-target):
  have h_inner_line : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => (1 - x 1) • (chartAt ℂ q) γ.src
                              + x 1 • (chartAt ℂ q) γ.tgt) :=
    (h1mt.smul contMDiff_const).add (hproj1.smul contMDiff_const)
  -- Full inner straight-line interpolation:
  have h_inner : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => (1 - x 0) • (chartAt ℂ q) (γ.ambient (x 1))
                              + x 0 • ((1 - x 1) • (chartAt ℂ q) γ.src
                                        + x 1 • (chartAt ℂ q) γ.tgt)) :=
    (h1ms.smul h_chart_γ_x).add (hproj0.smul h_inner_line)
  -- chart.symm smooth globally.
  have h_symm_on : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (chartAt ℂ q).symm
      (chartAt ℂ q).target := contMDiffOn_chart_symm
  have h_symm : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (chartAt ℂ q).symm := by
    rw [show (chartAt ℂ q).target = Set.univ from h_univ] at h_symm_on
    exact (contMDiffOn_univ).mp h_symm_on
  exact h_symm.comp h_inner

/-- **The full `SmoothHomotopyPath` constructor.** Given a smooth path
`γ` globally chart-contained in a full-target chart `(chartAt ℂ q)`,
build a `SmoothHomotopyPath γ γ_line` where γ_line is the chart-
straight-line path between γ's endpoints. -/
noncomputable def chartStraightLineHomotopy
    (q : Y) (h_univ : (chartAt ℂ q).target = Set.univ)
    (γ : SmoothPath (𝓘(ℝ, ℂ)) Y)
    (h_in : ∀ t : ℝ, γ.ambient t ∈ (chartAt ℂ q).source)
    (h_src_in : γ.src ∈ (chartAt ℂ q).source)
    (h_tgt_in : γ.tgt ∈ (chartAt ℂ q).source)
    (h0_amb : γ.ambient 0 = γ.src) (h1_amb : γ.ambient 1 = γ.tgt) :
    SmoothHomotopyPath γ
      (chartStraightLinePath_univ q h_univ ((chartAt ℂ q) γ.src)
        ((chartAt ℂ q) γ.tgt))
      (by exact (OpenPartialHomeomorph.left_inv _ h_src_in).symm)
      (by exact (OpenPartialHomeomorph.left_inv _ h_tgt_in).symm) := by
  refine
    { toFun := chartHomotopyMapDirect q γ
      smooth := contMDiff_chartHomotopyMapDirect_univ q h_univ γ h_in
      left_edge := ?_
      right_edge := ?_
      bottom_edge := ?_
      top_edge := ?_ }
  · -- left_edge: at s=0, H = chart.symm(chart(γ.amb t.val)) = γ.amb t.val = γ.toPath t.
    intro t
    show chartHomotopyMapDirect q γ ![0, t.val] = γ.toPath t
    unfold chartHomotopyMapDirect
    have h_idx : (![0, t.val] : Fin 2 → ℝ) 0 = 0 := rfl
    have h_idx2 : (![0, t.val] : Fin 2 → ℝ) 1 = t.val := rfl
    rw [h_idx, h_idx2]
    -- (1-0) • chart(γ.amb t.val) + 0 • (...) = chart(γ.amb t.val).
    have h_collapse :
        (1 - (0 : ℝ)) • (chartAt ℂ q) (γ.ambient t.val)
          + (0 : ℝ) • ((1 - t.val) • (chartAt ℂ q) γ.src
                        + t.val • (chartAt ℂ q) γ.tgt)
        = (chartAt ℂ q) (γ.ambient t.val) := by module
    rw [h_collapse]
    -- chart.symm(chart(γ.amb t.val)) = γ.amb t.val.
    rw [OpenPartialHomeomorph.left_inv _ (h_in t.val)]
    -- γ.amb t.val = γ.toPath t.
    exact γ.ambient_eq_on_unitInterval t
  · -- right_edge: at s=1, H = chart.symm((1-t.val) • chart γ.src + t.val • chart γ.tgt)
    --                    = chartStraightLineMap q (chart γ.src) (chart γ.tgt) t.val
    --                    = γ_line.toPath t.
    intro t
    show chartHomotopyMapDirect q γ ![1, t.val]
        = (chartStraightLinePath_univ q h_univ ((chartAt ℂ q) γ.src)
            ((chartAt ℂ q) γ.tgt)).toPath t
    unfold chartHomotopyMapDirect
    have h_idx : (![1, t.val] : Fin 2 → ℝ) 0 = 1 := rfl
    have h_idx2 : (![1, t.val] : Fin 2 → ℝ) 1 = t.val := rfl
    rw [h_idx, h_idx2]
    -- (1-1) • _ + 1 • (...) = (...).
    have h_collapse :
        (1 - (1 : ℝ)) • (chartAt ℂ q) (γ.ambient t.val)
          + (1 : ℝ) • ((1 - t.val) • (chartAt ℂ q) γ.src
                        + t.val • (chartAt ℂ q) γ.tgt)
        = (1 - t.val) • (chartAt ℂ q) γ.src
          + t.val • (chartAt ℂ q) γ.tgt := by module
    rw [h_collapse]
    -- Match against γ_line.toPath t = chartStraightLineMap q (chart γ.src) (chart γ.tgt) t.val
    -- = chart.symm((1-t.val) • chart γ.src + t.val • chart γ.tgt).
    rfl
  · -- bottom_edge: at t=0, H = chart.symm((1-s) • chart(γ.amb 0) + s • ((1-0) • chart γ.src + 0 • chart γ.tgt))
    --                       = chart.symm((1-s) • chart γ.src + s • chart γ.src)
    --                       = chart.symm(chart γ.src) = γ.src.
    intro s
    show chartHomotopyMapDirect q γ ![s, 0] = γ.src
    unfold chartHomotopyMapDirect
    have h_idx : (![s, (0 : ℝ)] : Fin 2 → ℝ) 0 = s := rfl
    have h_idx2 : (![s, (0 : ℝ)] : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h_idx, h_idx2, h0_amb]
    have h_collapse :
        (1 - s) • (chartAt ℂ q) γ.src
          + s • ((1 - (0 : ℝ)) • (chartAt ℂ q) γ.src
                  + (0 : ℝ) • (chartAt ℂ q) γ.tgt)
        = (chartAt ℂ q) γ.src := by module
    rw [h_collapse]
    exact OpenPartialHomeomorph.left_inv _ h_src_in
  · -- top_edge: at t=1, similarly = γ.tgt.
    intro s
    show chartHomotopyMapDirect q γ ![s, 1] = γ.tgt
    unfold chartHomotopyMapDirect
    have h_idx : (![s, (1 : ℝ)] : Fin 2 → ℝ) 0 = s := rfl
    have h_idx2 : (![s, (1 : ℝ)] : Fin 2 → ℝ) 1 = 1 := rfl
    rw [h_idx, h_idx2, h1_amb]
    have h_collapse :
        (1 - s) • (chartAt ℂ q) γ.tgt
          + s • ((1 - (1 : ℝ)) • (chartAt ℂ q) γ.src
                  + (1 : ℝ) • (chartAt ℂ q) γ.tgt)
        = (chartAt ℂ q) γ.tgt := by module
    rw [h_collapse]
    exact OpenPartialHomeomorph.left_inv _ h_tgt_in

/-! ## Headline: chart-contained γ is smoothly bordant to its chart-straight-line -/

/-- **Chart-local polygonal-approximation bordism.** For any smooth
path `γ` globally chart-contained in a full-target chart, the
SmoothCycle `single (chartStraightLinePath γ.src γ.tgt) - single γ`
lies in `stokesBoundaries`. -/
theorem chartStraightLine_singleSub_mem_stokesBoundaries
    (q : Y) (h_univ : (chartAt ℂ q).target = Set.univ)
    (γ : SmoothPath (𝓘(ℝ, ℂ)) Y)
    (h_in : ∀ t : ℝ, γ.ambient t ∈ (chartAt ℂ q).source)
    (h_src_in : γ.src ∈ (chartAt ℂ q).source)
    (h_tgt_in : γ.tgt ∈ (chartAt ℂ q).source)
    (h0_amb : γ.ambient 0 = γ.src) (h1_amb : γ.ambient 1 = γ.tgt) :
    (⟨SmoothChain.single
          (chartStraightLinePath_univ q h_univ ((chartAt ℂ q) γ.src)
            ((chartAt ℂ q) γ.tgt))
        - SmoothChain.single γ,
        SmoothHomotopyPath.single_sub_single_mem_smoothCycle
          (by exact (OpenPartialHomeomorph.left_inv _ h_src_in).symm)
          (by exact (OpenPartialHomeomorph.left_inv _ h_tgt_in).symm)⟩
        : SmoothCycle (𝓘(ℝ, ℂ)) Y)
      ∈ stokesBoundaries (𝓘(ℝ, ℂ)) Y :=
  SmoothHomotopyPath.singleSub_smoothCycle_mem_stokesBoundaries
    (chartStraightLineHomotopy q h_univ γ h_in h_src_in h_tgt_in h0_amb h1_amb)

end JacobianChallenge

end
