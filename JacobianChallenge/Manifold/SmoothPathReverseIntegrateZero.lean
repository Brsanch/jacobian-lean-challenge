/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathReverseStokesBoundary
import JacobianChallenge.Manifold.SmoothPathIntegrateReverse

set_option linter.unusedSectionVars false

/-! # `single γ + single γ.reverse` integrates to zero against any form

Direct integration computation: combining `SmoothChain.integrate_single`
with `SmoothPath.integrate_reverse` (in tree), the chain
`SmoothChain.single γ + SmoothChain.single γ.reverse` integrates to
zero against ANY 1-form, without any closedness assumption.

This complements `single_smoothPath_plus_reverse_mem_stokesBoundaries`
(chip 18), which shows the same chain is in `stokesBoundaries`. The
stokesBoundaries membership only guarantees vanishing against
canonical-closed forms; the direct computation here is stronger:
vanishing against ANY form.

## What this file ships

* `integrate_single_smoothPath_plus_reverse_eq_zero` — direct
  integration computation.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-- **The chain `single γ + single γ.reverse` integrates to zero
against any smooth 1-form.** Direct from `integrate_single` and
`SmoothPath.integrate_reverse`. -/
theorem integrate_single_smoothPath_plus_reverse_eq_zero
    (γ : SmoothPath I X) (om : SmoothOneForm I X) :
    SmoothChain.integrate
      (SmoothChain.single γ + SmoothChain.single γ.reverse) om = 0 := by
  rw [SmoothChain.integrate_add, SmoothChain.integrate_single,
      SmoothChain.integrate_single, SmoothPath.integrate_reverse]
  ring

end JacobianChallenge

end
