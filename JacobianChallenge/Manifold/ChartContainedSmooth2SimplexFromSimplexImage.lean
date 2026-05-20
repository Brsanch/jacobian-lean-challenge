/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartContainedSmooth2SimplexBoundaryDirect

set_option linter.unusedSectionVars false

/-! # `complexChainPeriod (∂σ) α = 0` from σ-image-on-Δ²-in-chart

A cleaner surface than the per-face constructor: provide just two
**single** conditions on `σ.toFun '' standardSimplex2`, and the
per-face data is derived automatically using the fact that
`face_iParam([0, 1]) ⊆ Δ²` for `i ∈ {0, 1, 2}`.

## What this file ships

* `standardSimplex2` — the standard topological 2-simplex
  `{(x, y) : 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ 1}` as a `Set (Fin 2 → ℝ)`.
* `face0Param_mem_standardSimplex2`, `face1Param_mem_standardSimplex2`,
  `face2Param_mem_standardSimplex2` — face-parameter membership.
* `complexChainPeriod_boundary_eq_zero_of_simplex_chartContained` —
  the headline: σ-image-on-Δ²-in-chart-source + chart-image-in-ball ⇒
  `complexChainPeriod (∂σ) α = 0`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- The standard topological 2-simplex in `Fin 2 → ℝ`:
`{(x, y) : 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ 1}`. -/
def standardSimplex2 : Set (Fin 2 → ℝ) :=
  {p | 0 ≤ p 0 ∧ 0 ≤ p 1 ∧ p 0 + p 1 ≤ 1}

/-- `face0Param([0, 1]) ⊆ standardSimplex2`. For `s ∈ [0, 1]`,
`(1 - s, s)` satisfies the simplex inequalities. -/
lemma face0Param_mem_standardSimplex2 {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Smooth2Simplex.face0Param s ∈ standardSimplex2 := by
  obtain ⟨h0, h1⟩ := hs
  unfold standardSimplex2 Smooth2Simplex.face0Param
  refine ⟨?_, ?_, ?_⟩
  · show (1 - s : ℝ) ≥ 0
    linarith
  · show (s : ℝ) ≥ 0
    exact h0
  · show (1 - s + s : ℝ) ≤ 1
    linarith

/-- `face1Param([0, 1]) ⊆ standardSimplex2`. -/
lemma face1Param_mem_standardSimplex2 {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Smooth2Simplex.face1Param s ∈ standardSimplex2 := by
  obtain ⟨h0, h1⟩ := hs
  unfold standardSimplex2 Smooth2Simplex.face1Param
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ℝ) ≤ 0
    exact le_refl 0
  · show (0 : ℝ) ≤ s
    exact h0
  · show (0 + s : ℝ) ≤ 1
    linarith

/-- `face2Param([0, 1]) ⊆ standardSimplex2`. -/
lemma face2Param_mem_standardSimplex2 {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Smooth2Simplex.face2Param s ∈ standardSimplex2 := by
  obtain ⟨h0, h1⟩ := hs
  unfold standardSimplex2 Smooth2Simplex.face2Param
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ℝ) ≤ s
    exact h0
  · show (0 : ℝ) ≤ 0
    exact le_refl 0
  · show (s + 0 : ℝ) ≤ 1
    linarith

/-- **Boundary-period-zero from σ-image-on-Δ² chart-containment.**

For a `Smooth2Simplex 𝓘(ℝ, ℂ) X` whose image on `standardSimplex2` is
contained in a chart-source, and chart-image of that is contained in
a ball, the complex period of the boundary against every holomorphic
1-form vanishes.

A user-cleaner surface than
`complexChainPeriod_boundary_eq_zero_of_chartContainedFaces`: only
two conditions (instead of six) — `σ '' Δ² ⊆ chart-source` and
`chart ∘ σ '' Δ² ⊆ ball`. The per-face data is derived via
`face_iParam([0, 1]) ⊆ standardSimplex2`. -/
theorem complexChainPeriod_boundary_eq_zero_of_simplex_chartContained
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
    (α : HolomorphicOneForm X) :
    complexChainPeriod (Smooth2Simplex.boundary σ) α = 0 :=
  complexChainPeriod_boundary_eq_zero_of_chartContainedFaces
    σ basePoint ballCentre ballRadius radius_pos ball_sub_target
    (fun s hs =>
      h_image_in_source (Smooth2Simplex.face0Param s)
        (face0Param_mem_standardSimplex2 hs))
    (fun s hs =>
      h_image_in_source (Smooth2Simplex.face1Param s)
        (face1Param_mem_standardSimplex2 hs))
    (fun s hs =>
      h_image_in_source (Smooth2Simplex.face2Param s)
        (face2Param_mem_standardSimplex2 hs))
    (fun s hs =>
      h_chart_image_in_ball (Smooth2Simplex.face0Param s)
        (face0Param_mem_standardSimplex2 hs))
    (fun s hs =>
      h_chart_image_in_ball (Smooth2Simplex.face1Param s)
        (face1Param_mem_standardSimplex2 hs))
    (fun s hs =>
      h_chart_image_in_ball (Smooth2Simplex.face2Param s)
        (face2Param_mem_standardSimplex2 hs)) α

end JacobianChallenge
