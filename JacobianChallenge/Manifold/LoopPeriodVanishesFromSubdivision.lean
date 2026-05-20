/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Item14ReverseLegFullAssembly
import JacobianChallenge.Manifold.PointwiseChartEvalUnconditional

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # `LoopPeriodVanishes` from subdivision alone (no frame stability)

`LoopPeriodVanishesFromFrameStableAndSubdivision.lean` derived
`LoopPeriodVanishes` from per-loop frame stability + subdivision
telescoping. The frame-stability ingredient is now discharged
**unconditionally** for every chart-contained loop on every compact
complex 1-manifold (`PointwiseChartEvalUnconditional.lean`).

This file ships the simplified composite:

```
loopPeriodVanishes_from_subdivision_alone :
  SubdivisionTelescopingToLoop_named X →
  ∀ α x₀, LoopPeriodVanishes α x₀
```

i.e. `SubdivisionTelescopingToLoop_named` is the *single* remaining
open input for the reverse leg of item 14 on simply-connected `X`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`LoopPeriodVanishes` from subdivision telescoping alone.**

For any compact connected complex 1-manifold `X` that is simply
connected, given the subdivision-telescoping ingredient, every smooth
loop's complex period against every holomorphic 1-form vanishes.

The chart-contained-loop vanishing ingredient is supplied
unconditionally by
`ChartContainedClosedLoop.chartContainedLoopVanishingHypothesis_holds_unconditional`. -/
theorem loopPeriodVanishes_from_subdivision_alone
    [SimplyConnectedSpace X]
    (h_subdiv : SubdivisionTelescopingToLoop_named (X := X))
    (α : HolomorphicOneForm X) (x₀ : X) :
    LoopPeriodVanishes α x₀ := by
  intro γ h_src h_tgt
  have h_loop : γ.src = γ.tgt := h_src.trans h_tgt.symm
  obtain ⟨data_list, h_sum⟩ := h_subdiv γ h_loop α
  have h_vanishes :
      ChartContainedLoopVanishingHypothesis (X := X) :=
    ChartContainedClosedLoop.chartContainedLoopVanishingHypothesis_holds_unconditional
  rw [h_sum]
  apply List.sum_eq_zero
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨data, _hdata_mem, rfl⟩ := hx
  exact h_vanishes data α

end JacobianChallenge

end
