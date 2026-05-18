/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexBoundaryLoop
import JacobianChallenge.Manifold.HolomorphicComponentsCanonicalClosed

set_option linter.unusedSectionVars false

/-! # `HolomorphicStokesHypothesis X` from a loop-level hypothesis

**Structural reduction toward `holomorphicCanonicalClosed`.** Defines

```
HolomorphicLoopIntegralVanishes X : Prop
```

saying: for every smooth path `γ : SmoothPath 𝓘(ℝ, ℂ) X` that is the
**boundary loop of some smooth 2-simplex on `X`**, and every
holomorphic 1-form `ω` on `X`, the integral
`SmoothPath.integrate γ (realComponent ω) = 0` (and the same for
`imagComponent`).

Headline: `HolomorphicLoopIntegralVanishes X` is **equivalent** to
`HolomorphicStokesHypothesis X` (via `boundaryLoop_integrate_eq`).

This reformulates the four-input bundle's `holomorphic_closed` clause
in terms of integrals over SMOOTH LOOPS rather than 2-simplex boundary
chains, which is the natural form for Cauchy's theorem (mathlib's
`DifferentiableOn.isExactOn_ball` and `IsConservativeOn` machinery).

## What this file ships

* `HolomorphicLoopIntegralVanishes X : Prop` — the loop-level hypothesis.
* `holomorphicStokesHypothesis_iff_loopIntegralVanishes` — the
  equivalence with `HolomorphicStokesHypothesis X`.
* `holomorphicComponentsCanonicalClosed_of_loopIntegralVanishes` —
  direct discharge of `HolomorphicComponentsCanonicalClosed X` from
  the loop-level hypothesis.

No `sorry`, no `axiom`. -/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **`HolomorphicLoopIntegralVanishes X`** — for every smooth
2-simplex `σ` on `X` (modelled real-wise as `𝓘(ℝ, ℂ)`) and every
holomorphic 1-form `om` on `X`, the integral of the real and imaginary
components of `om` along the boundary loop of `σ` vanishes.

This is the natural form for Cauchy's theorem: integrals of holomorphic
1-forms around closed loops bounding 2-simplices vanish. -/
def HolomorphicLoopIntegralVanishes (X : Type*)
    [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X] : Prop :=
  ∀ σ : Smooth2Simplex 𝓘(ℝ, ℂ) X, ∀ om : HolomorphicOneForm X,
    SmoothPath.integrate (Smooth2Simplex.boundaryLoop σ)
        (realComponent om) = 0 ∧
    SmoothPath.integrate (Smooth2Simplex.boundaryLoop σ)
        (imagComponent om) = 0

/-- **Equivalence with `HolomorphicStokesHypothesis X`.** -/
theorem holomorphicStokesHypothesis_iff_loopIntegralVanishes :
    HolomorphicStokesHypothesis X ↔ HolomorphicLoopIntegralVanishes X := by
  unfold HolomorphicStokesHypothesis HolomorphicLoopIntegralVanishes
  constructor
  · intro h σ om
    have h_σ := h σ om
    rw [Smooth2Simplex.boundaryLoop_integrate_eq,
        Smooth2Simplex.boundaryLoop_integrate_eq]
    exact h_σ
  · intro h σ om
    have h_σ := h σ om
    rw [← Smooth2Simplex.boundaryLoop_integrate_eq,
        ← Smooth2Simplex.boundaryLoop_integrate_eq]
    exact h_σ

/-- **From `HolomorphicLoopIntegralVanishes X`, directly discharge
`HolomorphicComponentsCanonicalClosed X`.** Composes with
`HolomorphicComponentsCanonicalClosed.of_hypothesis`. -/
theorem holomorphicComponentsCanonicalClosed_of_loopIntegralVanishes
    (h : HolomorphicLoopIntegralVanishes X) :
    HolomorphicComponentsCanonicalClosed X :=
  HolomorphicComponentsCanonicalClosed.of_hypothesis
    (holomorphicStokesHypothesis_iff_loopIntegralVanishes.mpr h)

end JacobianChallenge

end
