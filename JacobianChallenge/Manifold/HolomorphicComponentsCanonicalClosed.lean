/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.StokesCanonicalClosedForms
import JacobianChallenge.Manifold.HolomorphicOneFormRealComponentLinear

set_option linter.unusedSectionVars false

/-! # `HolomorphicComponentsCanonicalClosed`: a named atomic predicate

The fourth atomic field of `C3PeriodLatticeStokesSpanTopInputs.ofCanonical`
(in `C3PeriodLatticeStokesCanonical.lean`) is:

```
holomorphicCanonicalClosed : ∀ om : HolomorphicOneForm X,
  realComponent om ∈ canonicalClosedForms 𝓘(ℝ, ℂ) X ∧
  imagComponent om ∈ canonicalClosedForms 𝓘(ℝ, ℂ) X
```

This file lifts that condition to a single named `Prop`,
`HolomorphicComponentsCanonicalClosed X`, and provides two clean
discharges:

* `HolomorphicStokesHypothesis X` — the classical content as a Prop:
  for every smooth 2-simplex `σ` and every holomorphic 1-form `om`,
  the real and imaginary components of `om` each integrate to zero
  around `∂σ`. Geometrically: Stokes' theorem `∫_{∂σ} α = ∫_σ dα`
  combined with `d(realComponent om) = 0` (and `d(imagComponent om)
  = 0`) — the well-known consequence of holomorphicity on a
  complex 1-manifold.
* `HolomorphicComponentsCanonicalClosed.of_hypothesis` — derivation
  of the canonical-closed predicate from the Stokes hypothesis.
* `HolomorphicComponentsCanonicalClosed.of_subsingleton` —
  trivial discharge when `HolomorphicOneForm X` is subsingleton
  (the genus-0 case, where every `om = 0`).

The structural value: the only remaining nontrivial classical input
on the holomorphic-side of the period-lattice bundle is
`HolomorphicStokesHypothesis X`, with the rest derivable mechanically.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Submodule

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-! ## Named predicate -/

/-- **Canonical-closedness of the real and imaginary components of every
holomorphic 1-form on `X`.** The four-input canonical-bundle form of
`C3PeriodLatticeStokesSpanTopInputs` factors `holomorphic_closed`
through this single named predicate. -/
def HolomorphicComponentsCanonicalClosed (X : Type*)
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] : Prop :=
  ∀ om : HolomorphicOneForm X,
    realComponent om ∈ canonicalClosedForms 𝓘(ℝ, ℂ) X ∧
    imagComponent om ∈ canonicalClosedForms 𝓘(ℝ, ℂ) X

/-! ## Stokes-hypothesis route -/

/-- **Stokes' theorem on smooth 2-simplices, applied to the real /
imaginary components of every holomorphic 1-form.** For each
`σ : Smooth2Simplex 𝓘(ℝ, ℂ) X` and each `om : HolomorphicOneForm X`,
the integrals of `realComponent om` and `imagComponent om` around the
boundary `∂σ` both vanish.

Geometrically this combines Stokes' theorem `∫_{∂σ} α = ∫_σ dα` with
the algebraic fact that real and imaginary components of holomorphic
1-forms on a complex 1-manifold are d-closed. -/
def HolomorphicStokesHypothesis (X : Type*)
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] : Prop :=
  ∀ σ : Smooth2Simplex 𝓘(ℝ, ℂ) X, ∀ om : HolomorphicOneForm X,
    SmoothChain.integrate (Smooth2Simplex.boundary σ)
        (realComponent om) = 0 ∧
    SmoothChain.integrate (Smooth2Simplex.boundary σ)
        (imagComponent om) = 0

/-- **From `HolomorphicStokesHypothesis` to
`HolomorphicComponentsCanonicalClosed`.** Re-shapes the universal-σ
statement into the canonical-closed-form membership predicate. -/
theorem HolomorphicComponentsCanonicalClosed.of_hypothesis
    (h : HolomorphicStokesHypothesis X) :
    HolomorphicComponentsCanonicalClosed X := by
  intro om
  refine ⟨?_, ?_⟩
  · intro σ
    exact (h σ om).1
  · intro σ
    exact (h σ om).2

/-! ## Subsingleton discharge (genus-0 case) -/

/-- **Subsingleton discharge.** If `HolomorphicOneForm X` is subsingleton
(the genus-0 case), every holomorphic 1-form is `0`, so its real and
imaginary components are both `0`, which lies in any submodule. No
analytic content needed. -/
theorem HolomorphicComponentsCanonicalClosed.of_subsingleton
    [Subsingleton (HolomorphicOneForm X)] :
    HolomorphicComponentsCanonicalClosed X := by
  intro om
  have hom_zero : om = 0 := Subsingleton.elim _ _
  refine ⟨?_, ?_⟩
  · rw [hom_zero, realComponent_zero]
    exact (canonicalClosedForms 𝓘(ℝ, ℂ) X).zero_mem
  · rw [hom_zero, imagComponent_zero]
    exact (canonicalClosedForms 𝓘(ℝ, ℂ) X).zero_mem

end JacobianChallenge

end
