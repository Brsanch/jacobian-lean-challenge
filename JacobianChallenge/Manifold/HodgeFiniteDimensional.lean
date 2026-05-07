/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Finiteness.Defs
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
abstract vector spaces. None of these is sufficient by itself to derive
finite-dimensionality of global holomorphic sections of the cotangent
bundle for a compact complex manifold; the bridging analytic content is
missing.

## What this file does

It is a **Tier-2 reduction**. We expose a single named Prop

```
JacobianChallenge.HolomorphicOneFormFiniteDim X : Prop
```

defined as `Module.Finite ℂ (HolomorphicOneForm X)`, and provide:

* `JacobianChallenge.finiteDimensional_of_HolomorphicOneFormFiniteDim` —
  promotes the hypothesis to a `FiniteDimensional ℂ (HolomorphicOneForm X)`
  instance for downstream lemmas (so basis-extraction lemmas, dimension
  arithmetic, etc., all become available without being asserted here).
* `JacobianChallenge.genus_eq_finrank` — under the hypothesis, the genus
  equals `Module.finrank ℂ (HolomorphicOneForm X)` definitionally; the
  point is that the right-hand side is no longer the junk-zero on
  infinite-dimensional spaces.

Subsequent chips can attack the hypothesis itself by importing analytic
content (Hodge decomposition, Cauchy-kernel estimates on a compact surface,
or the Bergman-kernel route).

## Status

* What is **proven** here: the bookkeeping that turns the named
  finite-dimensionality hypothesis into the typeclass instance the rest of
  the challenge files want, plus the (definitional) compatibility between
  `JacobianChallenge.genus` and `Module.finrank`.
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

/-- Under `HolomorphicOneFormFiniteDim X`, expose the hypothesis as the
underlying `Module.Finite` typeclass term. -/
lemma HolomorphicOneFormFiniteDim.toModuleFinite
    (h : HolomorphicOneFormFiniteDim X) :
    Module.Finite ℂ (HolomorphicOneForm X) := h

/-- Under the named hypothesis, `HolomorphicOneForm X` is a
finite-dimensional `ℂ`-vector space. With this lemma in scope, every
mathlib basis-extraction / dimension-arithmetic lemma about
finite-dimensional spaces becomes available for `HolomorphicOneForm X`. -/
lemma finiteDimensional_of_HolomorphicOneFormFiniteDim
    (h : HolomorphicOneFormFiniteDim X) :
    FiniteDimensional ℂ (HolomorphicOneForm X) := h

/-- Trivial restatement: under the hypothesis, the genus equals the
finrank of `HolomorphicOneForm X` (definitionally). The point is that on
the right-hand side `Module.finrank` is no longer the junk-zero value on
infinite-dimensional spaces — under the hypothesis we have a genuinely
finite-dimensional space, so `Module.finrank` matches `Module.rank` cast
to `ℕ`. -/
lemma genus_eq_finrank
    (_h : HolomorphicOneFormFiniteDim X) :
    JacobianChallenge.genus X = Module.finrank ℂ (HolomorphicOneForm X) :=
  rfl

end JacobianChallenge

end
