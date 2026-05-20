/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PrimitiveOnSmoothPathConnected

set_option linter.unusedSectionVars false

/-! # `LoopPeriodVanishes` from `Subsingleton (HolomorphicOneForm X)`

For any `X` with `Subsingleton (HolomorphicOneForm X)`, the loop
period of any holomorphic 1-form (which must be `0`) vanishes
trivially against every smooth loop. This is the genus-0 analytic
discharge of `LoopPeriodVanishes`.

## What this file ships

* `loopPeriodVanishes_of_subsingleton` — for any `X` with subsingleton
  holomorphic 1-forms, every loop period vanishes.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **`LoopPeriodVanishes` from `Subsingleton (HolomorphicOneForm X)`.** -/
theorem loopPeriodVanishes_of_subsingleton
    [Subsingleton (HolomorphicOneForm X)]
    (om : HolomorphicOneForm X) (x₀ : X) :
    LoopPeriodVanishes om x₀ := by
  intro γ _h_src _h_tgt
  have h_om_zero : om = 0 := Subsingleton.elim _ _
  rw [h_om_zero]
  exact map_zero (complexChainPeriodHomRight (SmoothChain.single γ))

end JacobianChallenge

end
