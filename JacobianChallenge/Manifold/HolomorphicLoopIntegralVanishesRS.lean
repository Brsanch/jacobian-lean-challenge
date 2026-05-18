/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicStokesFromLoopHypothesis
import JacobianChallenge.Manifold.HolomorphicOneFormRiemannSphereInstances

set_option linter.unusedSectionVars false

/-! # `HolomorphicLoopIntegralVanishes RiemannSphere` UNCONDITIONAL

The Riemann sphere has `Subsingleton (HolomorphicOneForm RiemannSphere)`
(every holomorphic 1-form on `ℙ¹` is zero — classical fact, in tree).
So every loop integral against `realComponent ω` or `imagComponent ω`
is trivially zero (since `ω = 0`).

This is the "genus-0 discharge" of the loop-level hypothesis. For
genus ≥ 1, the discharge requires actual Cauchy's theorem
(mathlib's `DifferentiableOn.isExactOn_ball`) + chart-pullback of
integration.

## What this file ships

* `holomorphicLoopIntegralVanishes_RiemannSphere` — unconditional
  discharge for `X = RiemannSphere`.

No `sorry`, no `axiom`. -/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

/-- **`HolomorphicLoopIntegralVanishes RiemannSphere` UNCONDITIONAL.**
Every loop integral against the real/imaginary component of a
holomorphic 1-form on `RS` vanishes — because every holomorphic 1-form
on `RS` is zero (`Subsingleton (HolomorphicOneForm RiemannSphere)`). -/
theorem holomorphicLoopIntegralVanishes_RiemannSphere :
    HolomorphicLoopIntegralVanishes RiemannSphere := by
  intro σ om
  have hom_zero : om = 0 := Subsingleton.elim _ _
  refine ⟨?_, ?_⟩
  · rw [hom_zero, realComponent_zero]
    show SmoothPath.integrate (Smooth2Simplex.boundaryLoop σ)
      (0 : SmoothOneForm 𝓘(ℝ, ℂ) RiemannSphere) = 0
    rw [SmoothPath.integrate_zero]
  · rw [hom_zero, imagComponent_zero]
    show SmoothPath.integrate (Smooth2Simplex.boundaryLoop σ)
      (0 : SmoothOneForm 𝓘(ℝ, ℂ) RiemannSphere) = 0
    rw [SmoothPath.integrate_zero]

/-- **`HolomorphicStokesHypothesis RiemannSphere` UNCONDITIONAL**
via the loop-level reduction. (Equivalent to the existing genus-0
discharge via `Subsingleton`; this just routes it through the
new loop-level infrastructure.) -/
theorem holomorphicStokesHypothesis_RiemannSphere :
    HolomorphicStokesHypothesis RiemannSphere :=
  holomorphicStokesHypothesis_iff_loopIntegralVanishes.mpr
    holomorphicLoopIntegralVanishes_RiemannSphere

end JacobianChallenge

end
