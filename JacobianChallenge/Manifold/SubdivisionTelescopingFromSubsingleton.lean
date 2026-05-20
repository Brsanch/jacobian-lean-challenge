/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartContainedSmooth2Simplex
import JacobianChallenge.Manifold.Item14ReverseLegFullAssembly

set_option linter.unusedSectionVars false

/-! # Subdivision-telescoping atoms from `Subsingleton (HolomorphicOneForm X)`

Generalises the RS-specific discharges
(`SubdivisionTelescopingToLoopRS`, `SubdivisionTelescopingTo2SimplexRS`)
to any compact connected complex 1-manifold `X` with
`Subsingleton (HolomorphicOneForm X)`. Every such `X` is "genus 0
analytically": the only holomorphic 1-form is `0`, so both the loop
and 2-simplex period-decomposition hypotheses are trivially
dischargeable with an empty subdivision list.

## What this file ships

* `subdivisionTelescopingToLoop_of_subsingleton` — discharge of
  `SubdivisionTelescopingToLoop_named X` for `X` with subsingleton
  holomorphic 1-forms.
* `subdivisionTelescopingTo2Simplex_of_subsingleton` — analogue for
  the 2-simplex hypothesis.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`SubdivisionTelescopingToLoop_named X` from
`Subsingleton (HolomorphicOneForm X)`.** -/
theorem subdivisionTelescopingToLoop_of_subsingleton
    [Subsingleton (HolomorphicOneForm X)] :
    SubdivisionTelescopingToLoop_named (X := X) := by
  intro _inst γ _h_loop α
  refine ⟨[], ?_⟩
  have h_α_zero : α = 0 := Subsingleton.elim _ _
  rw [h_α_zero]
  have h_lhs : complexChainPeriod (SmoothChain.single γ)
                  (0 : HolomorphicOneForm X) = 0 :=
    map_zero (complexChainPeriodHomRight (SmoothChain.single γ))
  rw [h_lhs]
  simp

/-- **`SubdivisionTelescopingTo2Simplex_named X` from
`Subsingleton (HolomorphicOneForm X)`.** -/
theorem subdivisionTelescopingTo2Simplex_of_subsingleton
    [Subsingleton (HolomorphicOneForm X)] :
    SubdivisionTelescopingTo2Simplex_named (X := X) := by
  intro σ α
  refine ⟨[], ?_⟩
  have h_α_zero : α = 0 := Subsingleton.elim _ _
  rw [h_α_zero]
  have h_lhs : complexChainPeriod (Smooth2Simplex.boundary σ)
                  (0 : HolomorphicOneForm X) = 0 :=
    map_zero (complexChainPeriodHomRight (Smooth2Simplex.boundary σ))
  rw [h_lhs]
  simp

end JacobianChallenge

end
