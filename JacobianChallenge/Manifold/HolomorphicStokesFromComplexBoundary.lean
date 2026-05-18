/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicComponentsCanonicalClosed
import JacobianChallenge.Manifold.AbelJacobiPath

set_option linter.unusedSectionVars false

/-! # `HolomorphicStokesHypothesis` from complex-valued boundary vanishing

`HolomorphicStokesHypothesis X` (`HolomorphicComponentsCanonicalClosed.lean`)
is stated as **two** real-valued vanishings: for every smooth 2-simplex
`σ` and every holomorphic 1-form `om`,
`∫_{∂σ} realComponent om = 0` AND `∫_{∂σ} imagComponent om = 0`.

By the algebraic identity
`complexChainPeriod c om := (∫_c realComponent om) + i · (∫_c imagComponent om)`,
these two vanishings together are equivalent to a single
**complex-valued vanishing**:
`complexChainPeriod (∂σ) om = 0`.

This file factors `HolomorphicStokesHypothesis X` through that single
complex-valued hypothesis, consolidating the user-facing input into
one statement and giving downstream chips a single complex-valued
predicate to discharge (e.g. via chart-contained 2-simplex Stokes +
holomorphic chart-local primitive).

## What this file ships

* `HolomorphicComplexBoundaryVanishingHypothesis X` — the single
  complex-valued predicate.
* `HolomorphicStokesHypothesis_of_complexBoundary` — derivation of the
  two real-valued vanishings from the complex-valued one.
* `complexBoundary_of_HolomorphicStokesHypothesis` — the reverse
  direction (the two real vanishings imply the complex vanishing).
* `HolomorphicComponentsCanonicalClosed.of_complexBoundary` —
  composition with `HolomorphicComponentsCanonicalClosed.of_hypothesis`
  giving a direct route from the complex predicate.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Complex

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **`HolomorphicComplexBoundaryVanishingHypothesis X`**.

For every smooth 2-simplex `σ` on `X` and every holomorphic 1-form
`om`, the complex period of the 2-simplex boundary against `om`
vanishes:

  `complexChainPeriod (Smooth2Simplex.boundary σ) om = 0`.

Geometrically: Stokes' theorem applied to `om` (which is `d`-closed as
a holomorphic 1-form via Cauchy-Riemann) gives `∫_{∂σ} om = ∫_σ dom = 0`. -/
def HolomorphicComplexBoundaryVanishingHypothesis (X : Type u)
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] : Prop :=
  ∀ σ : Smooth2Simplex 𝓘(ℝ, ℂ) X, ∀ om : HolomorphicOneForm X,
    complexChainPeriod (Smooth2Simplex.boundary σ) om = 0

/-- **`HolomorphicStokesHypothesis` from
`HolomorphicComplexBoundaryVanishingHypothesis`.** The two real-valued
vanishings follow by extracting `.re` and `.im` of the complex
identity `complexChainPeriod (∂σ) om = 0`. -/
theorem HolomorphicStokesHypothesis_of_complexBoundary
    (h : HolomorphicComplexBoundaryVanishingHypothesis X) :
    HolomorphicStokesHypothesis X := by
  intro σ om
  have h_zero : complexChainPeriod (Smooth2Simplex.boundary σ) om = 0 := h σ om
  have h_re :
      (complexChainPeriod (Smooth2Simplex.boundary σ) om).re = (0 : ℂ).re := by
    rw [h_zero]
  have h_im :
      (complexChainPeriod (Smooth2Simplex.boundary σ) om).im = (0 : ℂ).im := by
    rw [h_zero]
  -- Unfold complexChainPeriod = (∫_∂σ realComp) + i · (∫_∂σ imagComp).
  -- Its real part is ∫_∂σ realComp; its imaginary part is ∫_∂σ imagComp.
  refine ⟨?_, ?_⟩
  · -- Real part.
    have h_repr :
        (complexChainPeriod (Smooth2Simplex.boundary σ) om).re
          = SmoothChain.integrate (Smooth2Simplex.boundary σ)
              (realComponent om) := by
      unfold complexChainPeriod
      simp
    rw [h_repr] at h_re
    simpa using h_re
  · -- Imaginary part.
    have h_imrepr :
        (complexChainPeriod (Smooth2Simplex.boundary σ) om).im
          = SmoothChain.integrate (Smooth2Simplex.boundary σ)
              (imagComponent om) := by
      unfold complexChainPeriod
      simp
    rw [h_imrepr] at h_im
    simpa using h_im

/-- **`HolomorphicComplexBoundaryVanishingHypothesis` from
`HolomorphicStokesHypothesis`** (reverse direction). Reassembles the
complex period from its two real and imaginary parts. -/
theorem complexBoundary_of_HolomorphicStokesHypothesis
    (h : HolomorphicStokesHypothesis X) :
    HolomorphicComplexBoundaryVanishingHypothesis X := by
  intro σ om
  obtain ⟨h_re, h_im⟩ := h σ om
  -- complexChainPeriod = ∫ realComp + i · ∫ imagComp = 0 + i·0 = 0.
  unfold complexChainPeriod
  rw [h_re, h_im]
  push_cast
  ring

/-- **The biconditional.** -/
theorem holomorphicStokesHypothesis_iff_complexBoundary :
    HolomorphicStokesHypothesis X
      ↔ HolomorphicComplexBoundaryVanishingHypothesis X :=
  ⟨complexBoundary_of_HolomorphicStokesHypothesis,
    HolomorphicStokesHypothesis_of_complexBoundary⟩

/-! ## Direct route to `HolomorphicComponentsCanonicalClosed` -/

/-- **`HolomorphicComponentsCanonicalClosed` from the complex-valued
boundary vanishing hypothesis.** -/
theorem HolomorphicComponentsCanonicalClosed.of_complexBoundary
    (h : HolomorphicComplexBoundaryVanishingHypothesis X) :
    HolomorphicComponentsCanonicalClosed X :=
  HolomorphicComponentsCanonicalClosed.of_hypothesis
    (HolomorphicStokesHypothesis_of_complexBoundary h)

end JacobianChallenge

end
