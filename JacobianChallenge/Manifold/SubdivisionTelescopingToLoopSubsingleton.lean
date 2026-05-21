/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Item14ReverseLegFullAssembly

set_option linter.unusedSectionVars false

/-! # `SubdivisionTelescopingToLoop_named X` from `[Subsingleton (HolomorphicOneForm X)]`

Generalizes the RS-specific discharge `subdivisionTelescopingToLoop_RS`
(`Manifold/SubdivisionTelescopingToLoopRS.lean`) to **any** compact
connected complex 1-manifold `X` with `[Subsingleton (HolomorphicOneForm
X)]`. In that case every `α : HolomorphicOneForm X` is `0`, so the
loop's complex period is `0`, matched by the empty subdivision list
whose sum is `0`. Trivial — but useful because the subsingleton
hypothesis discharges via multiple routes (e.g. the chip-arc
`Topology/S2ImpliesGenus0FromSimplyConnected.lean` and downstream
typeclass instances on chart-cover-equipped X).

## What this file ships

* `subdivisionTelescopingToLoop_of_subsingleton_omega` — discharge of
  `SubdivisionTelescopingToLoop_named X` for any `X` with
  `[Subsingleton (HolomorphicOneForm X)]`.

This is a **typeclass generalization** of `subdivisionTelescopingToLoop_RS`:
RS is one such X (the canonical 2-chart genus-0 example), but the same
trivial argument works for any X with subsingleton holomorphic 1-forms.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`SubdivisionTelescopingToLoop_named X` from
`[Subsingleton (HolomorphicOneForm X)]`.**

Every `α : HolomorphicOneForm X` is `0` (by subsingleton), so the loop
period vanishes against `α`. The empty subdivision-list witnesses the
required `∃ data_list, period = sum`. -/
theorem subdivisionTelescopingToLoop_of_subsingleton_omega
    [Subsingleton (HolomorphicOneForm X)] :
    SubdivisionTelescopingToLoop_named (X := X) := by
  intro _inst γ _h_loop α
  refine ⟨[], ?_⟩
  have h_α_zero : α = 0 := Subsingleton.elim _ _
  rw [h_α_zero]
  have h_lhs : complexChainPeriod (SmoothChain.single γ) (0 : HolomorphicOneForm X) = 0 :=
    map_zero (complexChainPeriodHomRight (SmoothChain.single γ))
  rw [h_lhs]
  simp

end JacobianChallenge

end
