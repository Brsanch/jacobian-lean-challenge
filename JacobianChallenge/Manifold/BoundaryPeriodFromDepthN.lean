/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.IteratedMidpointSubdivision
import JacobianChallenge.Manifold.ChartContainedSmooth2SimplexFromSimplexImage

set_option linter.unusedSectionVars false

/-! # Boundary period vanishes from depth-n iterated chart-containment

Compose the iterated midpoint-subdivision identity with the
chart-contained σ discharge. If every element of `iteratedMidpointList σ n`
is chart-contained on Δ² for some `n`, then the boundary period of σ
vanishes against every holomorphic 1-form.

## Headline

```
∃ n,
  ∀ T ∈ iteratedMidpointList σ n,
    ∃ basePoint ballCentre ballRadius,
      0 < ballRadius ∧
      Metric.ball ballCentre ballRadius ⊆ (chartAt ℂ basePoint).target ∧
      (∀ p ∈ standardSimplex2, T.toFun p ∈ (chartAt ℂ basePoint).source) ∧
      (∀ p ∈ standardSimplex2,
        chartAt ℂ basePoint (T.toFun p) ∈ Metric.ball ballCentre ballRadius)
⇒  complexChainPeriod (∂σ) α = 0
```

## Strategy

By `complexChainPeriod_boundary_eq_iteratedMidpointList_sum`, the
boundary period of σ equals the sum over `iteratedMidpointList σ n` of
the per-element boundary periods. By
`complexChainPeriod_boundary_eq_zero_of_simplex_chartContained`, each
chart-contained element contributes `0`. Hence the sum is `0`.

This composition closes
`HolomorphicComplexBoundaryVanishingHypothesis X` (and hence
`HolomorphicStokesHypothesis X` and
`HolomorphicComponentsCanonicalClosed X`) for any σ admitting fine
subdivision, reducing the open content of
`SubdivisionTelescopingTo2Simplex_named X` at general genus to a
single classical existence: every smooth 2-simplex admits some finite
iterated midpoint depth at which each sub-simplex is chart-contained
on Δ². This is precisely the Lebesgue-number content for the cover
of `Δ²` by `σ`-preimages of chart sources (intersected with the
chart-radius-balls), and is the genuine open classical question.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Per-element chart-containment witness** for an element of an iterated
midpoint subdivision list. Carries the chart base point, ball centre/radius,
and the source/ball containment proofs. -/
structure ChartContainmentWitness (T : Smooth2Simplex 𝓘(ℝ, ℂ) X) where
  basePoint : X
  ballCentre : ℂ
  ballRadius : ℝ
  radius_pos : 0 < ballRadius
  ball_sub_target : Metric.ball ballCentre ballRadius ⊆ (chartAt ℂ basePoint).target
  image_in_source :
    ∀ p ∈ standardSimplex2, T.toFun p ∈ (chartAt ℂ basePoint).source
  chart_image_in_ball :
    ∀ p ∈ standardSimplex2,
      (chartAt ℂ basePoint) (T.toFun p) ∈ Metric.ball ballCentre ballRadius

/-- **Boundary period of a chart-contained σ vanishes.** Direct
reformulation of `complexChainPeriod_boundary_eq_zero_of_simplex_chartContained`
in terms of the witness structure. -/
lemma complexChainPeriod_boundary_eq_zero_of_witness
    {T : Smooth2Simplex 𝓘(ℝ, ℂ) X} (h : ChartContainmentWitness T)
    (α : HolomorphicOneForm X) :
    complexChainPeriod (Smooth2Simplex.boundary T) α = 0 :=
  complexChainPeriod_boundary_eq_zero_of_simplex_chartContained
    T h.basePoint h.ballCentre h.ballRadius h.radius_pos h.ball_sub_target
    h.image_in_source h.chart_image_in_ball α

/-- **Boundary period vanishes from depth-n uniform chart-containment.**

If every element of `iteratedMidpointList σ n` admits a chart-containment
witness (`Nonempty`), then the boundary period of σ vanishes against every
holomorphic 1-form. -/
theorem complexChainPeriod_boundary_eq_zero_of_uniformly_chartContained_at_depth
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X) (α : HolomorphicOneForm X) (n : ℕ)
    (h : ∀ T ∈ Smooth2Simplex.iteratedMidpointList σ n,
            Nonempty (ChartContainmentWitness T)) :
    complexChainPeriod (Smooth2Simplex.boundary σ) α = 0 := by
  rw [Smooth2Simplex.complexChainPeriod_boundary_eq_iteratedMidpointList_sum
        σ α n]
  apply List.sum_eq_zero
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨T, hT_mem, hx_eq⟩ := hx
  rw [← hx_eq]
  exact complexChainPeriod_boundary_eq_zero_of_witness (h T hT_mem).some α

/-- **Existential-depth form.** If there exists `n` such that every
element of the depth-`n` iterated midpoint subdivision is chart-contained,
then `complexChainPeriod (∂σ) α = 0` for every α. -/
theorem complexChainPeriod_boundary_eq_zero_of_exists_uniform_chartContained_depth
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X)
    (h : ∃ n, ∀ T ∈ Smooth2Simplex.iteratedMidpointList σ n,
            Nonempty (ChartContainmentWitness T))
    (α : HolomorphicOneForm X) :
    complexChainPeriod (Smooth2Simplex.boundary σ) α = 0 := by
  obtain ⟨n, h_n⟩ := h
  exact complexChainPeriod_boundary_eq_zero_of_uniformly_chartContained_at_depth
    σ α n h_n

/-! ## Named hypothesis: existence of a uniform-chart-containment depth

This is the classical content that closes the iterative-subdivision
chain. For any σ on a compact connected complex 1-manifold, the
Lebesgue-number lemma + uniform continuity of σ on `Δ²` guarantee
such an `n` exists. -/

/-- **Uniform chart-containment at some depth hypothesis.** -/
def UniformChartContainmentDepth_named (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] :
    Prop :=
  ∀ σ : Smooth2Simplex 𝓘(ℝ, ℂ) X,
    ∃ n, ∀ T ∈ Smooth2Simplex.iteratedMidpointList σ n,
      Nonempty (ChartContainmentWitness T)

/-- **From the uniform-depth named hypothesis to
`HolomorphicComplexBoundaryVanishingHypothesis X`.** -/
theorem holomorphicComplexBoundaryVanishingHypothesis_of_uniformChartContainmentDepth
    (h : UniformChartContainmentDepth_named X) :
    HolomorphicComplexBoundaryVanishingHypothesis X := by
  intro σ α
  obtain ⟨n, h_n⟩ := h σ
  exact complexChainPeriod_boundary_eq_zero_of_uniformly_chartContained_at_depth
    σ α n h_n

/-- **From the uniform-depth named hypothesis to
`HolomorphicStokesHypothesis X`.** -/
theorem holomorphicStokesHypothesis_of_uniformChartContainmentDepth
    (h : UniformChartContainmentDepth_named X) :
    HolomorphicStokesHypothesis X :=
  HolomorphicStokesHypothesis_of_complexBoundary
    (holomorphicComplexBoundaryVanishingHypothesis_of_uniformChartContainmentDepth h)

/-- **From the uniform-depth named hypothesis to
`HolomorphicComponentsCanonicalClosed X`.** -/
theorem holomorphicComponentsCanonicalClosed_of_uniformChartContainmentDepth
    (h : UniformChartContainmentDepth_named X) :
    HolomorphicComponentsCanonicalClosed X :=
  HolomorphicComponentsCanonicalClosed.of_hypothesis
    (holomorphicStokesHypothesis_of_uniformChartContainmentDepth h)

end JacobianChallenge

end
