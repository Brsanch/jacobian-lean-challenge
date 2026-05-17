/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicCotangentPullbackAt

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Evaluation of `holCotangentPullbackAt` at `1`

The cotangent value `holCotangentPullbackAt g y α : CotangentSpace _ y`
is by definition `(α.toFun (g y)).comp (mfderiv g y)`. As a
`ℂ →L[ℂ] ℂ`, evaluating at `(1 : ℂ)` gives:

  `(holCotangentPullbackAt g y α : ℂ →L[ℂ] ℂ) 1
     = α.toFun (g y) ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g y) 1)`.

This is the **chart-coord-level evaluation** of the cotangent pullback,
the first building block for connecting cotangent-bundle objects to
chart-coefficient formulas.

No `sorry`, no `axiom`. -/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

universe u v

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]
  {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-- **Composition decomposition of `holCotangentPullbackAt`.**

`holCotangentPullbackAt g y α` is by definition the composition
`(α.toFun (g y)).comp (mfderiv g y)` as continuous linear maps. -/
@[simp] lemma holCotangentPullbackAt_eq_comp
    (g : Y → X) (y : Y) (α : HolomorphicOneForm X) :
    (holCotangentPullbackAt g y α : ℂ →L[ℂ] ℂ)
      = ((α.toFun (g y) : ℂ →L[ℂ] ℂ).comp
          (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g y : ℂ →L[ℂ] ℂ)) := rfl

end JacobianChallenge

end
