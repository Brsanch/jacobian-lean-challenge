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

/-- **A smooth homotopy between two paths with the same endpoints.** -/
structure SmoothHomotopyPath
    (γ₀ γ₁ : SmoothPath (𝓘(ℝ, ℂ)) X)
    (_h_src : γ₀.src = γ₁.src) (_h_tgt : γ₀.tgt = γ₁.tgt) where
  /-- Ambient smooth extension to `Fin 2 → ℝ`. -/
  toFun : (Fin 2 → ℝ) → X
  /-- Smoothness witness. -/
  smooth : ContMDiff (𝓘(ℝ, Fin 2 → ℝ)) (𝓘(ℝ, ℂ)) ∞ toFun
  /-- Left edge (`s = 0`) equals `γ₀`'s ambient. -/
  left_edge : ∀ t : ℝ, toFun ![0, t] = γ₀.ambient t
  /-- Right edge (`s = 1`) equals `γ₁`'s ambient. -/
  right_edge : ∀ t : ℝ, toFun ![1, t] = γ₁.ambient t
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

end JacobianChallenge

end
