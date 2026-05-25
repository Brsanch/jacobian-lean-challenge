/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.S2ImpliesGenus0FromLoopPeriodVanishesUnconditional
import JacobianChallenge.Manifold.LoopPeriodVanishesFromSubdivision

set_option linter.unusedSectionVars false

/-! # `S2ImpliesGenus0 X` from `SubdivisionTelescopingToLoop_named X` UNCONDITIONALLY

Composes the chartLocalPrimitive maxAtlas cascade (steps 1–7) with the
in-tree `LoopPeriodVanishesFromSubdivision.lean` to reduce
`S2ImpliesGenus0 X` on arbitrary compact connected complex 1-manifold
X to **a single named classical hypothesis**:

  `SubdivisionTelescopingToLoop_named X` — every smooth loop on X is
  a sum of chart-contained sub-loops, with internal-edge cancellation
  giving `∫_loop ω = Σ ∫_subcell ω` for every holomorphic 1-form ω.

What's discharged unconditionally by the cascade + this composition:

* **chart-contained loop period vanishing** (in tree, unconditional via
  `ChartContainedClosedLoop.chartContainedLoopVanishingHypothesis_holds_unconditional`).
* **globally-smooth primitive of ω** under `LoopPeriodVanishes`
  (cascade payoff: `pathPrimitive_contMDiff_unconditional` +
  `pathPrimitive_eval_eq_mfderiv_unconditional`).
* **`SimplyConnectedS2`** (in tree, unconditional via
  `simplyConnectedS2_holds`).
* **`SmoothPathConnected`** (in tree, unconditional via
  `smoothPathConnected_of_preconnected`).

What's NOT discharged here:

* `SubdivisionTelescopingToLoop_named X` — the Whitney smoothing of a
  null-homotopy subdivision + orientation cancellation. Per
  `SubdivisionTelescopingToLoopFromBSLB.lean` this further reduces to
  universal `BasedSmoothLoopsBoundHypothesis` (every smooth based loop
  bounds a smooth 2-chain), which on simply-connected X is the
  genuine remaining classical content (chart-by-chart monodromy or
  missed-point + Sard route generalised beyond `RiemannSphere`).

## What this file ships

* `s2ImpliesGenus0_of_subdivisionTelescoping` — closes
  `S2ImpliesGenus0 X` from a single named hypothesis on X.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`S2ImpliesGenus0 X` from `SubdivisionTelescopingToLoop_named X`.**

This is the strongest arbitrary-X reduction enabled by the cascade
composed with the in-tree unconditional chart-contained-loop
vanishing. The reverse leg of Item 14 reduces to **one** named
classical input on arbitrary X: subdivision telescoping. -/
theorem s2ImpliesGenus0_of_subdivisionTelescoping
    (x₀ : X)
    (h_subdiv : SubdivisionTelescopingToLoop_named (X := X)) :
    S2ImpliesGenus0 X :=
  s2ImpliesGenus0_of_loopPeriodVanishesOnSimplyConnected x₀ <| fun h_sc om =>
    letI : SimplyConnectedSpace X := h_sc
    loopPeriodVanishes_from_subdivision_alone h_subdiv om x₀

end JacobianChallenge

end
