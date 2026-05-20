/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.GenericGenusPeriodLatticeInputs
import JacobianChallenge.Manifold.ChartContainedSmooth2Simplex

set_option linter.unusedSectionVars false

/-! # `GenericGenusPeriodLatticeInputs` from the subdivision atom

`GenericGenusPeriodLatticeInputs basis` (the four atomic
canonical-bundle inputs at general genus) takes the third atom as the
raw predicate

```
holomorphicCanonicalClosed : ∀ om : HolomorphicOneForm X,
  realComponent om ∈ canonicalClosedForms 𝓘(ℝ, ℂ) X ∧
  imagComponent om ∈ canonicalClosedForms 𝓘(ℝ, ℂ) X
```

which is exactly `HolomorphicComponentsCanonicalClosed X`. With
`ChartContainedSmooth2Simplex.lean` reducing
`HolomorphicComponentsCanonicalClosed X` to
`SubdivisionTelescopingTo2Simplex_named X` (modulo the
`chartContainedLoopVanishingHypothesis_holds_unconditional` discharge),
this file ships a constructor that takes the **subdivision atom**
directly:

```
GenericGenusPeriodLatticeInputs.ofSubdivisionAtom :
  (cycleGens) → (riemannBilinear) →
  SubdivisionTelescopingTo2Simplex_named X →
  (H1_spans_top_canonical) →
  GenericGenusPeriodLatticeInputs basis
```

This makes the dependency on the deep classical content explicit at
the constructor level: the third atom is no longer the raw closed-form
predicate but the named subdivision-telescoping hypothesis.

No `sorry`, no `axiom`. -/

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace GenericGenusPeriodLatticeInputs

variable {basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}

/-- **Constructor from the subdivision atom.**

Build a `GenericGenusPeriodLatticeInputs basis` from
* a tuple of `2g` symplectic cycle generators,
* the Riemann bilinear ℝ-linear independence,
* the **subdivision-telescoping** atom for 2-simplices on `X`,
* the `H1_spans_top_canonical` atom.

The closed-form predicate `holomorphicCanonicalClosed` is derived
from the subdivision atom via
`holomorphicComponentsCanonicalClosed_of_subdivisionTo2Simplex`. -/
noncomputable def ofSubdivisionAtom
    (cycleGens :
      Fin (2 * JacobianChallenge.genus X) → (PeriodPairingData.ofSmoothCycle X).H1)
    (riemannBilinear :
      LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus X) =>
          periodVector (PeriodPairingData.ofSmoothCycle X) basis (cycleGens i)))
    (h_subdiv : SubdivisionTelescopingTo2Simplex_named (X := X))
    (H1_spans_top_canonical :
      (Submodule.span ℤ
        (Set.range (fun i : Fin (2 * JacobianChallenge.genus X) =>
          ((StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).proj (cycleGens i) :
            (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).H1)))) = ⊤) :
    GenericGenusPeriodLatticeInputs basis :=
  { cycleGens := cycleGens
    riemannBilinear := riemannBilinear
    holomorphicCanonicalClosed :=
      holomorphicComponentsCanonicalClosed_of_subdivisionTo2Simplex h_subdiv
    H1_spans_top_canonical := H1_spans_top_canonical }

end GenericGenusPeriodLatticeInputs

end JacobianChallenge
