/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PointwiseChartEvalUnconditional
import JacobianChallenge.Manifold.Smooth2SimplexBoundaryLoop
import JacobianChallenge.Manifold.HolomorphicStokesFromComplexBoundary
import JacobianChallenge.Manifold.SmoothPathIntegral
import JacobianChallenge.Manifold.HolomorphicOneFormRealification

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Chart-contained `Smooth2Simplex` → boundary period vanishes

If `σ : Smooth2Simplex 𝓘(ℝ, ℂ) X` has the property that its
`boundaryLoop` packages as a `ChartContainedClosedLoop` (i.e. the
ambient extension of `face2 ⋆ face0 ⋆ face1.reverse` stays in a single
chart-source with chart-image in a ball), then for every holomorphic
1-form `α : HolomorphicOneForm X`,

```
complexChainPeriod (Smooth2Simplex.boundary σ) α = 0.
```

This is the chart-contained-2-simplex piece of
`HolomorphicComplexBoundaryVanishingHypothesis X`, fully unconditional
modulo the chart-containment data being available (which is itself a
Whitney-smoothing / subdivision question).

The chip composes:
* `Smooth2Simplex.boundaryLoop_integrate_eq` — chain integral equals
  path integral over the boundary loop.
* `chartContainedLoopVanishingHypothesis_holds_unconditional`
  (`PointwiseChartEvalUnconditional.lean`) — chart-contained closed
  loops have zero complex period against any holomorphic 1-form.

## What this file ships

* `ChartContainedSmooth2Simplex X` — a `Smooth2Simplex 𝓘(ℝ, ℂ) X`
  together with an explicit `ChartContainedClosedLoop` whose path is
  `Smooth2Simplex.boundaryLoop σ`.
* `complexChainPeriod_boundary_eq_zero` — the headline: for every
  chart-contained 2-simplex, the complex period of its boundary
  vanishes against every holomorphic 1-form.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Chart-contained smooth 2-simplex.**

A `Smooth2Simplex 𝓘(ℝ, ℂ) X` together with an explicit packaging of
its `boundaryLoop` as a `ChartContainedClosedLoop`. The packaging
encodes the chart-containment data:

* `basePoint : X` — the chart base point.
* `ballCentre`, `ballRadius` — the ball in chart-target.
* The ambient extension of `boundaryLoop σ` stays in
  `(chartAt ℂ basePoint).source` on `[0, 1]`, with chart-image in
  the ball.

For chart-contained `σ` (image of `Δ²` under `σ.toFun` inside a single
chart-source, chart-image inside a ball), the boundary-loop ambient
extension automatically satisfies these — but constructing that
extension from raw chart-containment of `σ` requires careful tracking
of the `concatAmbient` smoothing through `(face2 ⋆ face0) ⋆ face1.reverse`.

This structure abstracts away that construction by taking the
packaged `ChartContainedClosedLoop` as data, leaving the construction
for an upstream subdivision-of-`Δ²` chip. -/
structure ChartContainedSmooth2Simplex (X : Type u)
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X] where
  /-- The underlying smooth 2-simplex. -/
  σ : Smooth2Simplex 𝓘(ℝ, ℂ) X
  /-- The chart-contained boundary loop. -/
  boundaryData : ChartContainedClosedLoop (X := X)
  /-- The chart-contained loop's path is the boundary loop of `σ`. -/
  boundaryData_γ : boundaryData.γ = Smooth2Simplex.boundaryLoop σ

namespace ChartContainedSmooth2Simplex

/-- **Boundary chain integral against a real 1-form equals path
integral over the boundary loop.** Direct rewrite via the underlying
`Smooth2Simplex.boundaryLoop_integrate_eq` plus the `boundaryData_γ`
identification. -/
private lemma chain_integrate_eq_boundaryData_integrate
    (data : ChartContainedSmooth2Simplex X)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X) :
    SmoothChain.integrate (Smooth2Simplex.boundary data.σ) om
      = SmoothPath.integrate data.boundaryData.γ om := by
  rw [data.boundaryData_γ]
  exact (Smooth2Simplex.boundaryLoop_integrate_eq data.σ om).symm

/-- **`complexChainPeriod` of the boundary equals `complexChainPeriod`
of the chart-contained boundary loop.** Splits the complex-valued
chain period into real and imaginary parts, applies the integrate
identity on each. -/
private lemma complexChainPeriod_boundary_eq
    (data : ChartContainedSmooth2Simplex X)
    (α : HolomorphicOneForm X) :
    complexChainPeriod (Smooth2Simplex.boundary data.σ) α
      = complexChainPeriod (SmoothChain.single data.boundaryData.γ) α := by
  unfold complexChainPeriod
  have h_re := chain_integrate_eq_boundaryData_integrate data (realComponent α)
  have h_im := chain_integrate_eq_boundaryData_integrate data (imagComponent α)
  -- `SmoothChain.integrate (single γ) = γ.integrate` by `integrate_single`.
  rw [h_re, h_im, SmoothChain.integrate_single, SmoothChain.integrate_single]

/-- **Headline: boundary period of a chart-contained 2-simplex vanishes.**

For every `ChartContainedSmooth2Simplex` and every
`HolomorphicOneForm`, the complex-valued boundary period
`complexChainPeriod (∂σ) α` is `0`.

The proof composes `complexChainPeriod_boundary_eq` (split into the
chart-contained boundary loop's period) with the unconditional
chart-contained-loop discharge
`chartContainedLoopVanishingHypothesis_holds_unconditional`. -/
theorem complexChainPeriod_boundary_eq_zero
    (data : ChartContainedSmooth2Simplex X)
    (α : HolomorphicOneForm X) :
    complexChainPeriod (Smooth2Simplex.boundary data.σ) α = 0 := by
  rw [complexChainPeriod_boundary_eq data α]
  exact
    ChartContainedClosedLoop.chartContainedLoopVanishingHypothesis_holds_unconditional
      data.boundaryData α

end ChartContainedSmooth2Simplex

/-! ## Subdivision-telescoping → `HolomorphicComplexBoundaryVanishingHypothesis` -/

/-- **Subdivision-telescoping for 2-simplices.**

For every `Smooth2Simplex 𝓘(ℝ, ℂ) X`, there exists a finite list of
`ChartContainedSmooth2Simplex`es whose `complexChainPeriod`-of-boundary
sum equals `complexChainPeriod (∂σ) α` for every holomorphic 1-form
`α`.

Geometrically: barycentric subdivision of `Δ²` enough times so each
sub-2-simplex's image is inside a chart-source; with appropriate
Whitney smoothing of the sub-boundaries, the sum telescopes via
orientation-cancellation on interior edges.

Like `SubdivisionTelescopingToLoop_named` this is a deep classical
content (Whitney smoothing + Lebesgue-number subdivision), surfaced
here as a named hypothesis. -/
def SubdivisionTelescopingTo2Simplex_named : Prop :=
  ∀ (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X) (α : HolomorphicOneForm X),
    ∃ (sublist : List (ChartContainedSmooth2Simplex X)),
      complexChainPeriod (Smooth2Simplex.boundary σ) α
        = (sublist.map
            (fun s =>
              complexChainPeriod (Smooth2Simplex.boundary s.σ) α)).sum

/-- **`HolomorphicComplexBoundaryVanishingHypothesis X` from
`SubdivisionTelescopingTo2Simplex_named X`.**

Composes the chart-contained 2-simplex headline
`ChartContainedSmooth2Simplex.complexChainPeriod_boundary_eq_zero`
with the subdivision-telescoping ingredient (sum of zeros is zero). -/
theorem holomorphicComplexBoundaryVanishingHypothesis_of_subdivisionTo2Simplex
    (h_subdiv : SubdivisionTelescopingTo2Simplex_named (X := X)) :
    HolomorphicComplexBoundaryVanishingHypothesis X := by
  intro σ α
  obtain ⟨sublist, h_sum⟩ := h_subdiv σ α
  rw [h_sum]
  apply List.sum_eq_zero
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨data, _hdata_mem, rfl⟩ := hx
  exact data.complexChainPeriod_boundary_eq_zero α

/-- **`HolomorphicStokesHypothesis X` from
`SubdivisionTelescopingTo2Simplex_named X`.** Composes with the
biconditional `holomorphicStokesHypothesis_iff_complexBoundary`. -/
theorem holomorphicStokesHypothesis_of_subdivisionTo2Simplex
    (h_subdiv : SubdivisionTelescopingTo2Simplex_named (X := X)) :
    HolomorphicStokesHypothesis X :=
  HolomorphicStokesHypothesis_of_complexBoundary
    (holomorphicComplexBoundaryVanishingHypothesis_of_subdivisionTo2Simplex h_subdiv)

/-- **`HolomorphicComponentsCanonicalClosed X` from
`SubdivisionTelescopingTo2Simplex_named X`.** Composes with
`HolomorphicComponentsCanonicalClosed.of_hypothesis`. -/
theorem holomorphicComponentsCanonicalClosed_of_subdivisionTo2Simplex
    (h_subdiv : SubdivisionTelescopingTo2Simplex_named (X := X)) :
    HolomorphicComponentsCanonicalClosed X :=
  HolomorphicComponentsCanonicalClosed.of_hypothesis
    (holomorphicStokesHypothesis_of_subdivisionTo2Simplex h_subdiv)

end JacobianChallenge

end
