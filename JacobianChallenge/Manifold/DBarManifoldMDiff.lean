/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DBarManifold
import Mathlib.Geometry.Manifold.MFDeriv.Defs

set_option linter.unusedSectionVars false

/-! # Manifold-side `dbar = 0` for `MDifferentiableAt`-functions

Bridges the manifold-native `MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x`
hypothesis (i.e. `f : X → ℂ` is "smooth"/"holomorphic" in the manifold
sense) to the manifold-side `dbar f x = 0` from `DBarManifold.lean`.

The key reduction: under `[ChartedSpace ℂ X]`, the model with corners on
the target is `𝓘(ℂ, ℂ)`, whose range is all of `ℂ`; combined with
`extChartAt_self_apply` on the target side (since `ℂ` is its own model
chart), `writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x f = f ∘ (extChartAt _ x).symm`,
and `DifferentiableWithinAt _ _ (range 𝓘(ℂ, ℂ)) _ = DifferentiableAt _ _ _`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Manifold-side: a function ℂ-differentiable in the manifold sense at
`x` has vanishing `∂̄` there. -/
theorem dbar_eq_zero_of_mdifferentiableAt {f : X → ℂ} {x : X}
    (hf : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x) :
    dbar f x = 0 := by
  -- Extract chart-side ℂ-differentiability.
  have h_diff : DifferentiableWithinAt ℂ
      (writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x f) (Set.range 𝓘(ℂ, ℂ))
      ((extChartAt 𝓘(ℂ, ℂ) x) x) :=
    hf.differentiableWithinAt_writtenInExtChartAt
  -- `range 𝓘(ℂ, ℂ) = univ`, so DifferentiableWithinAt = DifferentiableAt.
  have h_range : Set.range (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ) = Set.univ := by
    rw [ModelWithCorners.range_eq_univ]
  rw [h_range, differentiableWithinAt_univ] at h_diff
  -- `writtenInExtChartAt` equals `f ∘ (extChartAt _ x).symm` modulo
  -- composing with the identity target chart.
  -- writtenInExtChartAt I I' x f = extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm
  -- For target `ℂ` with `𝓘(ℂ, ℂ)`, `extChartAt _ y = PartialEquiv.refl ℂ` ≡ id.
  have h_written :
      writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x f
        = f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm := by
    unfold writtenInExtChartAt
    ext z
    simp [Function.comp]
  rw [h_written] at h_diff
  exact dbar_eq_zero_of_chartPullback_differentiableAt h_diff

end JacobianChallenge

end
