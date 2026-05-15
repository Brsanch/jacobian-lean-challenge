/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CotangentPullbackAt
import Mathlib.Geometry.Manifold.MFDeriv.Basic

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `cotangentPullbackAt` is germ-determined

The pointwise pullback `cotangentPullbackAt g y ω = ω(g y) ∘L mfderiv g y`
depends only on the germ of `g` at `y`. Two functions `g₁, g₂ : Y → X`
which are eventually equal in a neighbourhood of `y` therefore produce
the same cotangent pullback at `y`.

This is the foundational primitive for the trace identity at general
`t ∈ Icc 0 1`: on a sub-interval where two local sheets agree (one
based at the source fibre point `p`, one based at the corresponding
target fibre point `q := (sourceFiberPath p).toPath.extend t`), their
cotangent pullbacks at the shared regular value `β(σ t)` coincide.
This lets the source-indexed chain-rule sum
`∑_{p ∈ sourceFiber} cotangentPullbackAt sheet_p.g (β(σ t)) ω`
be re-indexed via the bijection
`sourceFiber ↔ fiberFinset (β(σ t))` to the target-indexed
`traceAt(f)(β(σ t))(ω)`.

## What ships

* `JacobianChallenge.cotangentPullbackAt_congr_of_eventuallyEq` —
  cotangent pullback is germ-determined.

* `JacobianChallenge.cotangentPullbackAt_congr` — pointwise consequence
  via `Filter.EventuallyEq.of_eq` upgraded by sheet-`U` membership.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff Topology

namespace JacobianChallenge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ⊤ Y]

/-- **`cotangentPullbackAt` respects germ-equality.** If `g₁ =ᶠ[𝓝 y] g₂`,
then their cotangent pullbacks at `y` coincide for any 1-form `ω`. -/
theorem cotangentPullbackAt_congr_of_eventuallyEq
    {g₁ g₂ : Y → X} {y : Y} (h : g₁ =ᶠ[𝓝 y] g₂)
    (om : SmoothOneForm I X) :
    cotangentPullbackAt (I := I) (I' := I') g₁ y om
      = cotangentPullbackAt (I := I) (I' := I') g₂ y om := by
  unfold cotangentPullbackAt
  -- Pointwise values agree at `y` itself.
  have h_pt : g₁ y = g₂ y := h.eq_of_nhds
  -- mfderiv depends only on germ.
  have h_mfd : mfderiv I' I g₁ y = mfderiv I' I g₂ y :=
    Filter.EventuallyEq.mfderiv_eq h
  rw [h_pt, h_mfd]

/-- **EqOn-form of the germ-congruence lemma.** If `g₁` and `g₂` agree
on an open set `U` containing `y`, their cotangent pullbacks at `y`
coincide. -/
theorem cotangentPullbackAt_congr_of_eqOn_open
    {g₁ g₂ : Y → X} {y : Y} {U : Set Y}
    (h_open : IsOpen U) (h_mem : y ∈ U) (h_eq : Set.EqOn g₁ g₂ U)
    (om : SmoothOneForm I X) :
    cotangentPullbackAt (I := I) (I' := I') g₁ y om
      = cotangentPullbackAt (I := I) (I' := I') g₂ y om := by
  apply cotangentPullbackAt_congr_of_eventuallyEq
  exact Filter.eventuallyEq_of_mem (h_open.mem_nhds h_mem) h_eq

end JacobianChallenge

end
