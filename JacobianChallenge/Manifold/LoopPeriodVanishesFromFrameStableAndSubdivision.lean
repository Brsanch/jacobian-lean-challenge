/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Item14ReverseLegFullAssembly
import JacobianChallenge.Manifold.PointwiseChartEvalFromFrameStability

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # `LoopPeriodVanishes` from per-loop frame stability + subdivision

`Item14ReverseLegFullAssembly.loopPeriodVanishes_from_ingredients`
takes three ingredients:

1. `DerivChartPathContinuousOn_named` per chart-contained loop —
   already discharged in tree via `derivChartPathContinuousOn_holds`.
2. `ComplexChainPeriodEqChartIntegral_named` per (loop, form) — open;
   in tree via `complexChainPeriodEqChartIntegral_from_pointwise` given
   `PointwiseChartEvalIdentity` + integrand continuity.
3. `SubdivisionTelescopingToLoop_named` — the deep classical content
   (Whitney smoothing of null-homotopy subdivision + orientation
   cancellation).

This file consolidates ingredients 1 and 2 into a single per-loop
**frame-stability** hypothesis (`CotangentChartFrameStable`) and
ships:

```
loopPeriodVanishes_from_frameStable_and_subdivision :
  (∀ data, CotangentChartFrameStable data) →
  SubdivisionTelescopingToLoop_named X →
  ∀ α x₀, LoopPeriodVanishes α x₀
```

The remaining open input for general `X` is therefore (frame stability
+ subdivision telescoping). Frame stability is automatic on
`RiemannSphere` for chart-contained loops with `basePoint ≠ ∞`
(`cotangentChartFrameStable_RiemannSphere`), and on any manifold
whose `chartAt` is constant on each chart-source. Subdivision
telescoping is the genuine deep content.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`LoopPeriodVanishes` from per-loop frame stability + subdivision
telescoping.**

For any compact connected complex 1-manifold `X` that is simply
connected, given:

* `h_frame`: every chart-contained closed loop on `X` is
  cotangent-frame-stable (so `chartAt` is constant on its chart-source
  along the loop's path);
* `h_subdiv`: the subdivision-telescoping hypothesis (any smooth loop's
  integral equals the sum of chart-contained sub-loop integrals);

then every smooth loop's complex period against every holomorphic
1-form vanishes.

The proof composes
`chartContainedLoopVanishingHypothesis_of_frameStable` (which
discharges ingredients 1 and 2 of `loopPeriodVanishes_from_ingredients`
under frame stability) with the subdivision-telescoping
sum-of-zeros-is-zero. -/
theorem loopPeriodVanishes_from_frameStable_and_subdivision
    [SimplyConnectedSpace X]
    (h_frame : ∀ data : ChartContainedClosedLoop (X := X),
      ChartContainedClosedLoop.CotangentChartFrameStable data)
    (h_subdiv : SubdivisionTelescopingToLoop_named (X := X))
    (α : HolomorphicOneForm X) (x₀ : X) :
    LoopPeriodVanishes α x₀ := by
  intro γ h_src h_tgt
  have h_loop : γ.src = γ.tgt := h_src.trans h_tgt.symm
  obtain ⟨data_list, h_sum⟩ := h_subdiv γ h_loop α
  have h_vanishes : ChartContainedLoopVanishingHypothesis (X := X) :=
    ChartContainedClosedLoop.chartContainedLoopVanishingHypothesis_of_frameStable
      h_frame
  rw [h_sum]
  apply List.sum_eq_zero
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨data, _hdata_mem, rfl⟩ := hx
  exact h_vanishes data α

end JacobianChallenge

end
