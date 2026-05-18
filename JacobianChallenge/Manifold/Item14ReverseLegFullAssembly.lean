/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartContainedLoopVanishingDischarge
import JacobianChallenge.Manifold.NullHomotopyChartSubdivision
import JacobianChallenge.Manifold.PrimitiveOnSmoothPathConnected

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Item 14 reverse leg — architectural assembly toward `LoopPeriodVanishes`

The architectural assembly of the chips in the item-14 reverse-leg arc.
Composes the chart-contained-loop vanishing hypothesis (discharged via
`chartContainedLoopVanishingHypothesis_of_ingredients`) with a
subdivision-telescoping named ingredient to derive `LoopPeriodVanishes`
for smooth loops on simply-connected `X`.

## Three named ingredients remaining

* `DerivChartPathContinuousOn_named` — continuity of `deriv chartPath`
  on `[0, 1]`. Needs real-scalars restrictScalars on the chart.

* `ComplexChainPeriodEqChartIntegral_named` — `complexChainPeriod` of
  a single-path chain equals the chart-coord complex integral. Chart-
  pullback realComponent/imagComponent identification.

* `SubdivisionTelescopingToLoop_named` — sum of chart-contained
  sub-loops' integrals = original loop's integral. Combines the
  unit-square subdivision (chip 1) with smooth-boundary Whitney
  approximation + orientation-cancellation telescoping.

Once those three are discharged, this file's
`loopPeriodVanishes_from_ingredients` gives `LoopPeriodVanishes` for
every smooth loop on simply-connected `X`. Combined with the in-tree
`holomorphicOneFormSubsingletonOfSimplyConnected_of_primitiveExistence`
(through path-primitive smoothness + FTC), that yields item-14 reverse
leg.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Named ingredient: telescoping from chart-contained subdivision to
the original smooth loop.**

For any smooth loop `γ` on a simply-connected `X` and any holomorphic
1-form `α`, there exists a finite collection of `ChartContainedClosedLoop`s
whose `complexChainPeriod` sum equals `complexChainPeriod (single γ) α`.

Classical content: subdivide a continuous null-homotopy of `γ` via
`subdivide_continuous_through_charts`; for each sub-cell, the boundary
gives a chart-contained smooth loop (via Whitney smoothing of
cell-edges); the sum telescopes by orientation-cancellation on shared
edges. -/
def SubdivisionTelescopingToLoop_named : Prop :=
  ∀ [SimplyConnectedSpace X]
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) (_h_loop : γ.src = γ.tgt)
    (α : HolomorphicOneForm X),
    ∃ (data_list : List (ChartContainedClosedLoop (X := X))),
      complexChainPeriod (SmoothChain.single γ) α
        = (data_list.map
            (fun data => complexChainPeriod (SmoothChain.single data.γ) α)).sum

/-- **`LoopPeriodVanishes` from the three named ingredients.**

Composes:
* `chartContainedLoopVanishingHypothesis_of_ingredients` (two
  ingredients) — every chart-contained loop has zero period.
* `SubdivisionTelescopingToLoop_named` — the original loop integrates
  to the sum of chart-contained sub-loop integrals.

The sum of zeros is zero, giving `LoopPeriodVanishes`. -/
theorem loopPeriodVanishes_from_ingredients
    [SimplyConnectedSpace X]
    (h_deriv :
      ∀ data : ChartContainedClosedLoop (X := X),
        ChartContainedClosedLoop.DerivChartPathContinuousOn_named data)
    (h_bridge :
      ∀ (data : ChartContainedClosedLoop (X := X)) (α : HolomorphicOneForm X),
        ChartContainedClosedLoop.ComplexChainPeriodEqChartIntegral_named data α)
    (h_telescoping : SubdivisionTelescopingToLoop_named (X := X))
    (α : HolomorphicOneForm X) (x₀ : X) :
    LoopPeriodVanishes α x₀ := by
  intro γ h_src h_tgt
  have h_loop : γ.src = γ.tgt := h_src.trans h_tgt.symm
  obtain ⟨data_list, h_sum⟩ := h_telescoping γ h_loop α
  have h_vanishes :=
    ChartContainedClosedLoop.chartContainedLoopVanishingHypothesis_of_ingredients
      (X := X) h_deriv h_bridge
  rw [h_sum]
  have h_each_zero :
      ∀ data ∈ data_list,
        complexChainPeriod (SmoothChain.single data.γ) α = 0 := by
    intro data _
    exact h_vanishes data α
  apply List.sum_eq_zero
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨data, hdata_mem, rfl⟩ := hx
  exact h_each_zero data hdata_mem

end JacobianChallenge

end
