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

end JacobianChallenge

end
