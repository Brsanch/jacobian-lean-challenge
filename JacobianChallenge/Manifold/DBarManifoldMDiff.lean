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

/-- The chart-pullback identification underlying the bridge:
`writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x f = f ∘ (extChartAt _ x).symm`. -/
lemma writtenInExtChartAt_target_complex_eq_chartPullback (f : X → ℂ) (x : X) :
    writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x f
      = f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm := by
  unfold writtenInExtChartAt
  ext z
  simp [Function.comp]

/-- The chart-pullback ℂ-differentiability characterization underlying
`MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x` (target a `ChartedSpace ℂ ℂ`):
the model-with-corners range is all of `ℂ`, so within-range reduces to
plain `DifferentiableAt`. -/
lemma mdifferentiableAt_target_complex_iff_chartPullback_differentiableAt
    {f : X → ℂ} {x : X} :
    MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x ↔
      ContinuousAt f x ∧
      DifferentiableAt ℂ (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
        ((extChartAt 𝓘(ℂ, ℂ) x) x) := by
  rw [mdifferentiableAt_iff,
      writtenInExtChartAt_target_complex_eq_chartPullback,
      show Set.range (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ) = Set.univ from
        ModelWithCorners.range_eq_univ _,
      differentiableWithinAt_univ]

/-- Manifold-side: a function ℂ-differentiable in the manifold sense at
`x` has vanishing `∂̄` there. -/
theorem dbar_eq_zero_of_mdifferentiableAt {f : X → ℂ} {x : X}
    (hf : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x) :
    dbar f x = 0 :=
  dbar_eq_zero_of_chartPullback_differentiableAt
    ((mdifferentiableAt_target_complex_iff_chartPullback_differentiableAt).mp hf).2

/-! ## Manifold-side CR converse

If `f : X → ℂ` is real-MDifferentiableAt and `dbar f x = 0`, then `f` is
ℂ-MDifferentiableAt. Routes through the chart-side CR converse
(`differentiableAt_complex_of_dbarChart_eq_zero`) applied to the
chart pullback. -/

/-- **Manifold-side CR converse.** Under `[ChartedSpace ℂ X]`, if the
chart pullback `f ∘ (extChartAt _ x).symm` is real-differentiable at the
chart image of `x`, `f` is continuous at `x`, and the manifold-side
`dbar f x = 0`, then `f` is manifold-`MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)`
at `x`. -/
theorem mdifferentiableAt_of_chartPullback_differentiableAt_real_and_dbar_eq_zero
    {f : X → ℂ} {x : X}
    (hcont : ContinuousAt f x)
    (hreal : DifferentiableAt ℝ (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
              ((extChartAt 𝓘(ℂ, ℂ) x) x))
    (hdbar : dbar f x = 0) :
    MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x := by
  have hℂ : DifferentiableAt ℂ (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
              ((extChartAt 𝓘(ℂ, ℂ) x) x) := by
    apply differentiableAt_complex_of_dbarChart_eq_zero hreal
    -- `dbar f x = 0` is `dbarChart (f ∘ chart.symm) (chart x) = 0` by defn.
    exact hdbar
  exact mdifferentiableAt_target_complex_iff_chartPullback_differentiableAt.mpr
    ⟨hcont, hℂ⟩

/-- **Manifold-side biconditional**: under continuity + chart-side real
differentiability, manifold-`MDifferentiableAt` with target `𝓘(ℂ, ℂ)` is
equivalent to vanishing `dbar`. -/
theorem mdifferentiableAt_iff_dbar_eq_zero
    {f : X → ℂ} {x : X}
    (hcont : ContinuousAt f x)
    (hreal : DifferentiableAt ℝ (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
              ((extChartAt 𝓘(ℂ, ℂ) x) x)) :
    MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x ↔ dbar f x = 0 :=
  ⟨dbar_eq_zero_of_mdifferentiableAt,
   mdifferentiableAt_of_chartPullback_differentiableAt_real_and_dbar_eq_zero
     hcont hreal⟩

end JacobianChallenge

end
