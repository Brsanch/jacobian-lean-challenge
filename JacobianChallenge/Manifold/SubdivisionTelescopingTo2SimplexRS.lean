/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartContainedSmooth2Simplex
import JacobianChallenge.Manifold.HolomorphicOneFormRiemannSphereInstances

set_option linter.unusedSectionVars false

/-! # `SubdivisionTelescopingTo2Simplex_named RiemannSphere` UNCONDITIONAL

The Riemann sphere has `Subsingleton (HolomorphicOneForm RiemannSphere)`.
So for every smooth 2-simplex `σ` on `RS` and every holomorphic 1-form
`α` (which must be `0`), the complex period
`complexChainPeriod (∂σ) α = 0`, matching the empty-list trivial
subdivision sum.

Composed with `holomorphicComponentsCanonicalClosed_of_subdivisionTo2Simplex`,
this gives an alternate route to `HolomorphicComponentsCanonicalClosed RiemannSphere`
that flows through the named 2-simplex subdivision-telescoping atom
rather than the direct subsingleton-discharge.

## What this file ships

* `subdivisionTelescopingTo2Simplex_RS` — unconditional discharge.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

/-- **`SubdivisionTelescopingTo2Simplex_named RiemannSphere` UNCONDITIONAL.**

For every smooth 2-simplex on `RiemannSphere` and every holomorphic
1-form (which must be `0` by subsingleton), the boundary period
vanishes trivially against the empty subdivision-list. -/
theorem subdivisionTelescopingTo2Simplex_RS :
    SubdivisionTelescopingTo2Simplex_named (X := RiemannSphere) := by
  intro σ α
  refine ⟨[], ?_⟩
  have h_α_zero : α = 0 := Subsingleton.elim _ _
  rw [h_α_zero]
  have h_lhs : complexChainPeriod (Smooth2Simplex.boundary σ)
                  (0 : HolomorphicOneForm RiemannSphere) = 0 :=
    map_zero (complexChainPeriodHomRight (Smooth2Simplex.boundary σ))
  rw [h_lhs]
  simp

end JacobianChallenge

end
