/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothBordantOfSmoothHomotopy
import JacobianChallenge.Manifold.SmoothChain

set_option linter.unusedSectionVars false

/-! # Smooth homotopy between two paths with the same endpoints

Companion to `SmoothHomotopyBasedLoop` (which is for two loops based at
a common point `p₀`). This file defines `SmoothHomotopyPath γ₀ γ₁` for
two `SmoothPath I X` with the same `src` and `tgt` — i.e., a smooth
map `H : ℝ² → X` such that on the unit square:
- `H(0, t) = γ₀(t)`
- `H(1, t) = γ₁(t)`
- `H(s, 0) = γ₀.src = γ₁.src` (constant)
- `H(s, 1) = γ₀.tgt = γ₁.tgt` (constant)

This is the natural homotopy structure for the polygonal-approximation
step: γ₀ is the original smooth path inside a chart, γ₁ is the chart-
straight-line approximation between the same endpoints, and `H` is
the chart-target straight-line interpolation pulled back through
`chart.symm`.

This file ships only the structure definition (with the basic edge
identities); the diagonal-split-into-two-triangles construction
(producing a `Smooth2Chain` whose boundary realizes the chain
difference `single γ₁ - single γ₀` modulo two constant-loop residues)
is a follow-up chip.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℝ, ℂ)) ⊤ X]

/-- **A smooth homotopy between two paths with the same endpoints.**

The left/right edges are restricted to `unitInterval` and identified
against `γ_i.toPath` (not `γ_i.ambient`). This avoids the
`Classical.choose`-opacity issue that would arise if we required the
identity for all `t : ℝ`: the path `γ_i.ambient` is `Classical.choose`
of the smooth witness and is only fixed by the structure on
`unitInterval`. -/
structure SmoothHomotopyPath
    (γ₀ γ₁ : SmoothPath (𝓘(ℝ, ℂ)) X)
    (_h_src : γ₀.src = γ₁.src) (_h_tgt : γ₀.tgt = γ₁.tgt) where
  /-- Ambient smooth extension to `Fin 2 → ℝ`. -/
  toFun : (Fin 2 → ℝ) → X
  /-- Smoothness witness. -/
  smooth : ContMDiff (𝓘(ℝ, Fin 2 → ℝ)) (𝓘(ℝ, ℂ)) ∞ toFun
  /-- Left edge (`s = 0`, on the unit interval) traces `γ₀.toPath`. -/
  left_edge : ∀ t : unitInterval, toFun ![0, t.val] = γ₀.toPath t
  /-- Right edge (`s = 1`, on the unit interval) traces `γ₁.toPath`. -/
  right_edge : ∀ t : unitInterval, toFun ![1, t.val] = γ₁.toPath t
  /-- Bottom edge (`t = 0`) constant at the common src. -/
  bottom_edge : ∀ s : ℝ, toFun ![s, 0] = γ₀.src
  /-- Top edge (`t = 1`) constant at the common tgt. -/
  top_edge : ∀ s : ℝ, toFun ![s, 1] = γ₀.tgt

/-! ## Chart-target straight-line homotopy between two chart-contained paths

When both paths live globally in a full-target chart's source and have
the same endpoints, the chart-target straight-line interpolation gives
a `SmoothHomotopyPath`. -/

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-- The chart-target straight-line homotopy map: combines two paths
both globally in `chart.source` by linear interpolation in `chart.target`. -/
noncomputable def chartHomotopyMap
    (q : Y) (γ₀ γ₁ : SmoothPath (𝓘(ℝ, ℂ)) Y) (x : Fin 2 → ℝ) : Y :=
  (chartAt ℂ q).symm
    ((1 - x 0) • (chartAt ℂ q) (γ₀.ambient (x 1))
      + x 0 • (chartAt ℂ q) (γ₁.ambient (x 1)))

/-- **Bottom edge** (`x 0 = 0`): the homotopy traces `γ₀`'s ambient. -/
@[simp] lemma chartHomotopyMap_left_edge
    (q : Y) (γ₀ γ₁ : SmoothPath (𝓘(ℝ, ℂ)) Y) (t : ℝ)
    (h_in : γ₀.ambient t ∈ (chartAt ℂ q).source) :
    chartHomotopyMap q γ₀ γ₁ ![0, t] = γ₀.ambient t := by
  unfold chartHomotopyMap
  simp
  exact OpenPartialHomeomorph.left_inv _ h_in

/-- **Right edge** (`x 0 = 1`): the homotopy traces `γ₁`'s ambient. -/
@[simp] lemma chartHomotopyMap_right_edge
    (q : Y) (γ₀ γ₁ : SmoothPath (𝓘(ℝ, ℂ)) Y) (t : ℝ)
    (h_in : γ₁.ambient t ∈ (chartAt ℂ q).source) :
    chartHomotopyMap q γ₀ γ₁ ![1, t] = γ₁.ambient t := by
  unfold chartHomotopyMap
  simp
  exact OpenPartialHomeomorph.left_inv _ h_in

/-- **Bottom edge** (`x 1 = 0`): the homotopy is constant at the
common src. Both `γ₀.ambient 0` and `γ₁.ambient 0` equal the shared
`src` value; their chart-target interpolation is the same chart point. -/
lemma chartHomotopyMap_bottom_edge
    (q : Y) (γ₀ γ₁ : SmoothPath (𝓘(ℝ, ℂ)) Y)
    (h_src : γ₀.src = γ₁.src) (h_src_in : γ₀.src ∈ (chartAt ℂ q).source)
    (h0₀_amb : γ₀.ambient 0 = γ₀.src) (h0₁_amb : γ₁.ambient 0 = γ₁.src)
    (s : ℝ) :
    chartHomotopyMap q γ₀ γ₁ ![s, 0] = γ₀.src := by
  unfold chartHomotopyMap
  show (chartAt ℂ q).symm
      ((1 - (![s, 0] : Fin 2 → ℝ) 0)
        • (chartAt ℂ q) (γ₀.ambient ((![s, 0] : Fin 2 → ℝ) 1))
        + (![s, 0] : Fin 2 → ℝ) 0
          • (chartAt ℂ q) (γ₁.ambient ((![s, 0] : Fin 2 → ℝ) 1)))
    = γ₀.src
  -- ![s, 0] 0 = s, ![s, 0] 1 = 0. γ₀.ambient 0 = γ₀.src, γ₁.ambient 0 = γ₁.src = γ₀.src.
  have h_amb_eq : γ₀.ambient ((![s, 0] : Fin 2 → ℝ) 1) = γ₀.src := by
    show γ₀.ambient 0 = γ₀.src
    exact h0₀_amb
  have h_amb_eq' : γ₁.ambient ((![s, 0] : Fin 2 → ℝ) 1) = γ₀.src := by
    show γ₁.ambient 0 = γ₀.src
    rw [h0₁_amb, ← h_src]
  rw [h_amb_eq, h_amb_eq']
  -- Now: chart.symm ((1 - s) • chart γ₀.src + s • chart γ₀.src) = γ₀.src.
  have h_idx : (![s, 0] : Fin 2 → ℝ) 0 = s := rfl
  rw [h_idx]
  -- The interpolation is constant: (1-s) • c + s • c = c.
  have h_combo : ((1 - s) : ℝ) • (chartAt ℂ q) γ₀.src
                  + (s : ℝ) • (chartAt ℂ q) γ₀.src
                = (chartAt ℂ q) γ₀.src := by
    module
  rw [h_combo]
  exact OpenPartialHomeomorph.left_inv _ h_src_in

/-- **Smoothness of `chartHomotopyMap`** under the chart-containment
hypotheses on both paths and the chart-target convexity / full-target
property keeping the interpolation inside `chart.target`.

When `chart.target = univ`, the chart-target straight-line stays in
chart.target trivially, and `chart.symm` is smooth globally, so the
homotopy map is `C^∞` everywhere. -/
lemma contMDiff_chartHomotopyMap_univ
    (q : Y) (h_univ : (chartAt ℂ q).target = Set.univ)
    (γ₀ γ₁ : SmoothPath (𝓘(ℝ, ℂ)) Y)
    (h_in₀ : ∀ t : ℝ, γ₀.ambient t ∈ (chartAt ℂ q).source)
    (h_in₁ : ∀ t : ℝ, γ₁.ambient t ∈ (chartAt ℂ q).source) :
    ContMDiff (𝓘(ℝ, Fin 2 → ℝ)) (𝓘(ℝ, ℂ)) ∞
      (chartHomotopyMap q γ₀ γ₁) := by
  -- The inner straight-line `(s, t) ↦ (1-s)•ψγ₀(t) + s•ψγ₁(t)` is smooth.
  have hproj0 : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun x : Fin 2 → ℝ => x 0) :=
    ((ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff).contMDiff
  have hproj1 : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun x : Fin 2 → ℝ => x 1) :=
    ((ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff).contMDiff
  have h1ms : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun x : Fin 2 → ℝ => 1 - x 0) := contMDiff_const.sub hproj0
  -- chart ∘ γᵢ.ambient is smooth on the cylinder where γᵢ.ambient ∈ chart.source.
  have h_chart_on : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (chartAt ℂ q)
      (chartAt ℂ q).source := contMDiffOn_chart
  have h_chart_γ₀ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
      (fun t : ℝ => (chartAt ℂ q) (γ₀.ambient t)) :=
    h_chart_on.comp_contMDiff γ₀.ambient_contMDiff h_in₀
  have h_chart_γ₁ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
      (fun t : ℝ => (chartAt ℂ q) (γ₁.ambient t)) :=
    h_chart_on.comp_contMDiff γ₁.ambient_contMDiff h_in₁
  -- Compose with x ↦ x 1 to get `(Fin 2 → ℝ) → ℂ` smooth.
  have h_chart_γ₀_x : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => (chartAt ℂ q) (γ₀.ambient (x 1))) :=
    h_chart_γ₀.comp hproj1
  have h_chart_γ₁_x : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => (chartAt ℂ q) (γ₁.ambient (x 1))) :=
    h_chart_γ₁.comp hproj1
  -- Inner straight-line: (1 - x 0) • h_γ₀_x + (x 0) • h_γ₁_x.
  have h_inner : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => (1 - x 0) • (chartAt ℂ q) (γ₀.ambient (x 1))
                              + x 0 • (chartAt ℂ q) (γ₁.ambient (x 1))) :=
    (h1ms.smul h_chart_γ₀_x).add (hproj0.smul h_chart_γ₁_x)
  -- chart.symm smooth globally (chart.target = univ).
  have h_symm_on : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (chartAt ℂ q).symm
      (chartAt ℂ q).target := contMDiffOn_chart_symm
  have h_symm : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (chartAt ℂ q).symm := by
    rw [show (chartAt ℂ q).target = Set.univ from h_univ] at h_symm_on
    exact (contMDiffOn_univ).mp h_symm_on
  -- Compose.
  exact h_symm.comp h_inner

/-- **Top edge** (`x 1 = 1`): the homotopy is constant at the
common tgt. -/
lemma chartHomotopyMap_top_edge
    (q : Y) (γ₀ γ₁ : SmoothPath (𝓘(ℝ, ℂ)) Y)
    (h_tgt : γ₀.tgt = γ₁.tgt) (h_tgt_in : γ₀.tgt ∈ (chartAt ℂ q).source)
    (h1₀_amb : γ₀.ambient 1 = γ₀.tgt) (h1₁_amb : γ₁.ambient 1 = γ₁.tgt)
    (s : ℝ) :
    chartHomotopyMap q γ₀ γ₁ ![s, 1] = γ₀.tgt := by
  unfold chartHomotopyMap
  show (chartAt ℂ q).symm
      ((1 - (![s, 1] : Fin 2 → ℝ) 0)
        • (chartAt ℂ q) (γ₀.ambient ((![s, 1] : Fin 2 → ℝ) 1))
        + (![s, 1] : Fin 2 → ℝ) 0
          • (chartAt ℂ q) (γ₁.ambient ((![s, 1] : Fin 2 → ℝ) 1)))
    = γ₀.tgt
  have h_amb_eq : γ₀.ambient ((![s, 1] : Fin 2 → ℝ) 1) = γ₀.tgt := by
    show γ₀.ambient 1 = γ₀.tgt
    exact h1₀_amb
  have h_amb_eq' : γ₁.ambient ((![s, 1] : Fin 2 → ℝ) 1) = γ₀.tgt := by
    show γ₁.ambient 1 = γ₀.tgt
    rw [h1₁_amb, ← h_tgt]
  rw [h_amb_eq, h_amb_eq']
  have h_idx : (![s, 1] : Fin 2 → ℝ) 0 = s := rfl
  rw [h_idx]
  have h_combo : ((1 - s) : ℝ) • (chartAt ℂ q) γ₀.tgt
                  + (s : ℝ) • (chartAt ℂ q) γ₀.tgt
                = (chartAt ℂ q) γ₀.tgt := by
    module
  rw [h_combo]
  exact OpenPartialHomeomorph.left_inv _ h_tgt_in

end JacobianChallenge

end
