/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MidpointSubdivisionChartContained

set_option linter.unusedSectionVars false

/-! # Midpoint-subdivision telescoping headline

This file ships the **named telescoping hypothesis** for the 4-way
midpoint subdivision of a `Smooth2Simplex 𝓘(ℝ, ℂ) X`:

```
MidpointSubdivisionTelescoping σ α :=
  complexChainPeriod (Smooth2Simplex.boundary σ) α
    = ∑ i : Fin 4, complexChainPeriod
        (Smooth2Simplex.boundary (Smooth2Simplex.midpointSubdivision σ i)) α
```

Geometric content: the boundary of `σ` equals the sum of boundaries
of the four sub-triangles, **modulo interior-edge cancellations on
shared edges**. Each pair of interior-edge integrals (between two
sub-triangles, parameterised in opposite directions) cancels — but
proving this at the SmoothPath level is the deep orientation-
cancellation chip (the `T0.face0` ↔ `T3.face0` reverse-equality
in the chain-homology sense).

Surfaced as a `Prop`-valued hypothesis here so the structural
discharge composes cleanly:

* If `σ` is chart-contained on `Δ²`, each sub-triangle has zero
  boundary period (`midpointSubdivision_complexChainPeriod_zero`).
* If `MidpointSubdivisionTelescoping σ α` holds, the boundary period
  of `σ` equals the sum of these zeros = `0`.

So under chart-containment of `σ` + the telescoping hypothesis, we
get `complexChainPeriod (∂σ) α = 0`. This is the **chart-contained
1-step subdivision** discharge of the third atomic period-lattice
input — a building block toward the full
`SubdivisionTelescopingTo2Simplex_named X` content.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace Smooth2Simplex

/-- **Named midpoint-subdivision telescoping hypothesis.** -/
def MidpointSubdivisionTelescoping
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X) (α : HolomorphicOneForm X) : Prop :=
  complexChainPeriod (Smooth2Simplex.boundary σ) α
    = ∑ i : Fin 4,
        complexChainPeriod (Smooth2Simplex.boundary (midpointSubdivision σ i)) α

/-- **`complexChainPeriod (∂σ) α = 0` from chart-contained σ + midpoint
telescoping hypothesis.**

Composes:
* `midpointSubdivision_complexChainPeriod_zero` — each sub-triangle's
  boundary period vanishes when σ is chart-contained on Δ².
* the named telescoping hypothesis — the sum equals `complexChainPeriod (∂σ) α`. -/
theorem complexChainPeriod_boundary_eq_zero_of_chartContained_and_telescoping
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X) (α : HolomorphicOneForm X)
    (basePoint : X) (ballCentre : ℂ) (ballRadius : ℝ)
    (radius_pos : 0 < ballRadius)
    (ball_sub_target :
      Metric.ball ballCentre ballRadius ⊆ (chartAt ℂ basePoint).target)
    (h_image_in_source :
      ∀ p ∈ standardSimplex2, σ.toFun p ∈ (chartAt ℂ basePoint).source)
    (h_chart_image_in_ball :
      ∀ p ∈ standardSimplex2,
        (chartAt ℂ basePoint) (σ.toFun p) ∈ Metric.ball ballCentre ballRadius)
    (h_telescope : MidpointSubdivisionTelescoping σ α) :
    complexChainPeriod (Smooth2Simplex.boundary σ) α = 0 := by
  rw [h_telescope]
  -- Each summand is `0`.
  apply Finset.sum_eq_zero
  intro i _
  exact midpointSubdivision_complexChainPeriod_zero
    σ basePoint ballCentre ballRadius radius_pos ball_sub_target
    h_image_in_source h_chart_image_in_ball i α

/-! ## Iterative refinement: chart-contained σ ⇒ midpoint telescoping ⇒ 0

If the telescoping hypothesis holds for `σ`, the boundary period
vanishes when `σ` itself fits in a chart-ball. For more general
`σ`, one would iterate: subdivide until each sub-triangle fits in
a chart-ball (Lebesgue-number argument), apply this discharge per
sub-triangle, and sum.

The iterative refinement step (one level of midpointSubdivision)
preserves chart-containment trivially — the convexity of
`standardSimplex2` keeps every sub-triangle's image inside σ's
image, so chart-containment is closed under midpointSubdivision.
Combined with this single-level discharge, the iterative chip
becomes a finite induction once Lebesgue-number subdivision data
is in tree. -/

/-- **Direct corollary: chart-contained σ on `Δ²` + midpoint
telescoping ⇒ `complexChainPeriod (∂σ) α = 0`.**

A pragma-friendly cleaner-API variant of the previous theorem. -/
theorem complexChainPeriod_boundary_zero_chartContained_midpointTelescoping
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X) (α : HolomorphicOneForm X)
    (basePoint : X) (ballCentre : ℂ) (ballRadius : ℝ)
    (radius_pos : 0 < ballRadius)
    (ball_sub_target :
      Metric.ball ballCentre ballRadius ⊆ (chartAt ℂ basePoint).target)
    (h_image_in_source :
      ∀ p ∈ standardSimplex2, σ.toFun p ∈ (chartAt ℂ basePoint).source)
    (h_chart_image_in_ball :
      ∀ p ∈ standardSimplex2,
        (chartAt ℂ basePoint) (σ.toFun p) ∈ Metric.ball ballCentre ballRadius)
    (h_telescope : MidpointSubdivisionTelescoping σ α) :
    complexChainPeriod (Smooth2Simplex.boundary σ) α = 0 :=
  complexChainPeriod_boundary_eq_zero_of_chartContained_and_telescoping
    σ α basePoint ballCentre ballRadius radius_pos ball_sub_target
    h_image_in_source h_chart_image_in_ball h_telescope

end Smooth2Simplex

end JacobianChallenge

end
