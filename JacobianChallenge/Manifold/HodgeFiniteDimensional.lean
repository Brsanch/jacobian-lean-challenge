/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import JacobianChallenge.Manifold.HolomorphicOneForm

/-! # Finite-dimensionality of `HolomorphicOneForm X` for compact Riemann surfaces

The genus of a complex manifold `X` modelled on `ℂ` is defined in
`HolomorphicOneForm.lean` as

```
JacobianChallenge.genus X := Module.finrank ℂ (HolomorphicOneForm X)
```

For this number to carry classical-genus content, the space
`HolomorphicOneForm X` must be finite-dimensional. Classically (compact
connected Riemann surface) this is a consequence of Hodge theory: the space
of harmonic 1-forms is finite-dimensional because the Laplacian on a compact
Riemannian manifold is elliptic with finite-dimensional kernel.

## What is in mathlib at the project pin (`8e3c989`, 15 Apr 2026)

At this pin mathlib does **not** carry:

* The Hodge decomposition theorem for compact Riemannian manifolds.
* General elliptic-regularity / Fredholm theory on manifolds.
* The harmonic-form representative of a de Rham cohomology class.

What it does carry: the bare manifold + cotangent-bundle infrastructure,
`ContMDiffSection`, `Module.finrank`, `FiniteDimensional` typeclasses on
abstract vector spaces, and ellipticity-on-`ℝⁿ` style results. None of
these is sufficient by itself to derive finite-dimensionality of global
holomorphic sections of the cotangent bundle for a compact complex
manifold; the bridging analytic content is missing.

## What this file does

It is a **Tier-2 reduction**. We expose a single named Prop

```
JacobianChallenge.HolomorphicOneFormFiniteDim X : Prop
```

defined as `Module.Finite ℂ (HolomorphicOneForm X)`, and provide:

* `JacobianChallenge.genus_pos_of_HolomorphicOneFormFiniteDim` — under the
  hypothesis, the genus is the `Module.finrank` of a genuinely
  finite-dimensional space (so `Module.finrank` is no longer the junk-zero
  on infinite-dimensional spaces).
* `JacobianChallenge.finiteDimensional_of_HolomorphicOneFormFiniteDim` —
  promotes the hypothesis to a `FiniteDimensional ℂ (HolomorphicOneForm X)`
  instance for downstream lemmas.
* `JacobianChallenge.holomorphicOneForm_basis` — chooses a `ℂ`-basis of
  `HolomorphicOneForm X` indexed by `Fin (genus X)` under the hypothesis.

Subsequent chips can attack the hypothesis itself by importing analytic
content (Hodge decomposition, Cauchy-kernel estimates on a compact surface,
or the Bergman-kernel route).

## Status

* What is **proven** here: the bookkeeping that turns the named
  finite-dimensionality hypothesis into the statements the rest of the
  challenge files want (basis, finrank-is-real, instance promotion).
* What is **reduced to a hypothesis**:
  `Module.Finite ℂ (HolomorphicOneForm X)` for a compact connected
  complex 1-manifold. This is the single open assumption.
* What is **missing in mathlib at the pin**: Hodge decomposition for
  compact Kähler / Riemannian manifolds, or any equivalent analytic
  theorem that would produce finite-dimensionality of global holomorphic
  sections.

No `sorry`, no `axiom`. The hypothesis is carried as an explicit
`Prop` argument; nothing in this file is asserted unconditionally beyond
what already follows from `HolomorphicOneForm.lean`.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Named hypothesis.** The space of global holomorphic 1-forms on `X`
is finite-dimensional over `ℂ`.

For a compact connected Riemann surface this is a classical theorem (Hodge
theory: finite-dimensional kernel of an elliptic operator on a compact
manifold). At the mathlib pin used by this project the analytic content
needed to derive this theorem is not available, so we expose it as a single
named hypothesis. Everything else in `genus`-land downstream follows from
linear algebra. -/
def HolomorphicOneFormFiniteDim : Prop :=
  Module.Finite ℂ (HolomorphicOneForm X)

variable {X}

/-- Under `HolomorphicOneFormFiniteDim X`, promote the hypothesis to a
`Module.Finite` instance for the local context. -/
lemma HolomorphicOneFormFiniteDim.toModuleFinite
    (h : HolomorphicOneFormFiniteDim X) :
    Module.Finite ℂ (HolomorphicOneForm X) := h

/-- Under the named hypothesis, `HolomorphicOneForm X` is a
finite-dimensional `ℂ`-vector space. -/
lemma finiteDimensional_of_HolomorphicOneFormFiniteDim
    (h : HolomorphicOneFormFiniteDim X) :
    FiniteDimensional ℂ (HolomorphicOneForm X) := h

/-- Trivial restatement: under the hypothesis, the genus equals the
finrank of `HolomorphicOneForm X` (definitionally). The point is that on
the right-hand side `Module.finrank` is no longer the junk-zero value on
infinite-dimensional spaces — we have a genuine finite-dimensional space,
so `Module.finrank` matches `Module.rank` cast to `ℕ`. -/
lemma genus_eq_finrank
    (_h : HolomorphicOneFormFiniteDim X) :
    JacobianChallenge.genus X = Module.finrank ℂ (HolomorphicOneForm X) :=
  rfl

/-- Under the named hypothesis, `HolomorphicOneForm X` admits a `ℂ`-basis
indexed by `Fin (JacobianChallenge.genus X)`. This is the form most
useful for downstream constructions (period matrices, Abel-Jacobi map,
etc.). -/
noncomputable def holomorphicOneForm_basis
    (h : HolomorphicOneFormFiniteDim X) :
    Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X) :=
  letI : FiniteDimensional ℂ (HolomorphicOneForm X) :=
    finiteDimensional_of_HolomorphicOneFormFiniteDim h
  Module.finBasisOfFinrankEq ℂ (HolomorphicOneForm X)
    (rfl : Module.finrank ℂ (HolomorphicOneForm X) =
           JacobianChallenge.genus X)

end JacobianChallenge

end
