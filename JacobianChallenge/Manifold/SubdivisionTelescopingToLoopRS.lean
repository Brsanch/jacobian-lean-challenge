/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Item14ReverseLegFullAssembly
import JacobianChallenge.Manifold.HolomorphicOneFormRiemannSphereInstances

set_option linter.unusedSectionVars false

/-! # `SubdivisionTelescopingToLoop_named RiemannSphere` UNCONDITIONAL

The Riemann sphere has `Subsingleton (HolomorphicOneForm RiemannSphere)`
(every holomorphic 1-form on `ℙ¹` is zero — classical fact, in tree).
So every `complexChainPeriod (single γ) α` is `0`, and the
subdivision-telescoping decomposition becomes trivial: the empty list
sums to `0`, matching the LHS `0`.

This is the **genus-0 discharge** of the loop-level subdivision
telescoping hypothesis. Combined with the unconditional
`chartContainedLoopVanishingHypothesis_holds_unconditional`
(`PointwiseChartEvalUnconditional.lean`) and the
`loopPeriodVanishes_from_subdivision_alone` composite
(`LoopPeriodVanishesFromSubdivision.lean`), this gives an alternate
route to `LoopPeriodVanishes` on `RS` that doesn't require the
genus-0 subsingleton at the LoopPeriodVanishes endpoint.

## What this file ships

* `subdivisionTelescopingToLoop_RS` — unconditional discharge for
  `X = RiemannSphere`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

/-- **`SubdivisionTelescopingToLoop_named RiemannSphere` UNCONDITIONAL.**

For every smooth loop on `RiemannSphere` and every holomorphic
1-form (which must be `0` by subsingleton), the loop period vanishes
trivially against the empty subdivision-list. -/
theorem subdivisionTelescopingToLoop_RS :
    SubdivisionTelescopingToLoop_named (X := RiemannSphere) := by
  intro _inst γ _h_loop α
  -- Use the empty list as the trivial subdivision.
  refine ⟨[], ?_⟩
  -- Both sides are `0`: LHS via subsingleton, RHS by definition of empty list sum.
  have h_α_zero : α = 0 := Subsingleton.elim _ _
  rw [h_α_zero]
  -- `complexChainPeriod c 0 = 0` for any chain c (Hom in α).
  have h_lhs : complexChainPeriod (SmoothChain.single γ) (0 : HolomorphicOneForm RiemannSphere)
        = 0 :=
    map_zero (complexChainPeriodHomRight (SmoothChain.single γ))
  rw [h_lhs]
  -- `([].map _).sum = 0`.
  simp

end JacobianChallenge

end
