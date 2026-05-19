/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusHolomorphicCanonicalClosedReduction

set_option linter.unusedSectionVars false

/-! # The two `dz`-component hypotheses on `T_L = ℂ ⧸ L`

This file packages the **two remaining classical inputs** for
`HolomorphicComponentsCanonicalClosed (ℂ ⧸ L)` as a single named
predicate, and combines them via
`holomorphicComponentsCanonicalClosed_of_dz_components` (from the
reduction chip) to give the conditional closure.

```
RealImagDzInCanonicalClosed L : Prop :=
  realComponent (dz L) ∈ canonicalClosedForms 𝓘(ℝ, ℂ) (ℂ ⧸ L) ∧
  imagComponent (dz L) ∈ canonicalClosedForms 𝓘(ℝ, ℂ) (ℂ ⧸ L)
```

These are the classical Stokes content on the constant `dx` / `dy`
1-forms on the complex torus: for every smooth 2-simplex
`σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)`,

```
SmoothChain.integrate (Smooth2Simplex.boundary σ) (realComponent (dz L)) = 0
SmoothChain.integrate (Smooth2Simplex.boundary σ) (imagComponent (dz L)) = 0
```

The argument relies on a **smooth 2-simplex lift**
`σ̃ : (Fin 2 → ℝ) → ℂ` of `σ : (Fin 2 → ℝ) → (ℂ ⧸ L)`, built by
integration of `mfderiv σ` along a path (e.g. horizontal-then-vertical)
from `0` to `(x, y)`. Then `mkQ ∘ σ̃ = σ` (by ODE uniqueness applied
fiber by fiber, using `mkQ.mfderiv = id`), the face-velocity integrals
equal `σ̃(v_j) - σ̃(v_i)` (FTC on the lifted face), and the three
boundary integrals telescope to `0` around the simplex.

## What this file ships

* `ComplexTorus.RealImagDzInCanonicalClosed` — the named predicate
  bundling the two Stokes-side hypotheses.
* `ComplexTorus.holomorphicComponentsCanonicalClosed_of_realImagDz` —
  composes the reduction `holomorphicComponentsCanonicalClosed_of_dz_components`
  with the named predicate.
* `ComplexTorus.holomorphicStokesHypothesis_of_realImagDz` —
  the equivalent `HolomorphicStokesHypothesis` form.

The classical discharge of `RealImagDzInCanonicalClosed L` is the
2D-lift content, which is being built in subsequent chips
(`ComplexTorusTwoSimplexLift.lean` and follow-ups).

No `sorry`, no `axiom`. -/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Named predicate for the two `dz`-component hypotheses -/

/-- **The bundled `dz`-component Stokes-closure hypothesis on `T_L`.**
Both the real-part component and the imaginary-part component of `dz`
lie in `canonicalClosedForms 𝓘(ℝ, ℂ) (ℂ ⧸ L)` — i.e. they
integrate to zero against the boundary of every smooth 2-simplex on
`T_L`. -/
def RealImagDzInCanonicalClosed : Prop :=
  realComponent (dz L) ∈ canonicalClosedForms 𝓘(ℝ, ℂ) (ℂ ⧸ L) ∧
  imagComponent (dz L) ∈ canonicalClosedForms 𝓘(ℝ, ℂ) (ℂ ⧸ L)

/-! ## Conditional closure of `HolomorphicComponentsCanonicalClosed` -/

/-- **From `RealImagDzInCanonicalClosed L` to
`HolomorphicComponentsCanonicalClosed (ℂ ⧸ L)`.** Direct composition of
the structural reduction `holomorphicComponentsCanonicalClosed_of_dz_components`. -/
theorem holomorphicComponentsCanonicalClosed_of_realImagDz
    (h : RealImagDzInCanonicalClosed L) :
    HolomorphicComponentsCanonicalClosed (ℂ ⧸ L) :=
  holomorphicComponentsCanonicalClosed_of_dz_components L h.1 h.2

/-- **From `RealImagDzInCanonicalClosed L` to
`HolomorphicStokesHypothesis (ℂ ⧸ L)`.** The universal-σ form on the
canonical bundle. -/
theorem holomorphicStokesHypothesis_of_realImagDz
    (h : RealImagDzInCanonicalClosed L) :
    HolomorphicStokesHypothesis (ℂ ⧸ L) := by
  intro σ α
  have h_closed : HolomorphicComponentsCanonicalClosed (ℂ ⧸ L) :=
    holomorphicComponentsCanonicalClosed_of_realImagDz L h
  have h_re_im := h_closed α
  refine ⟨?_, ?_⟩
  · exact h_re_im.1 σ
  · exact h_re_im.2 σ

end ComplexTorus

end JacobianChallenge

end
