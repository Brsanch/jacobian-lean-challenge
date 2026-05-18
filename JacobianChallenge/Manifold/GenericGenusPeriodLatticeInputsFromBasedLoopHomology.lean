/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.GenericGenusH1SpansTopFromLoopHomology
import JacobianChallenge.Manifold.GenericGenusPeriodLatticeInputs

set_option linter.unusedSectionVars false

/-! # `GenericGenusPeriodLatticeInputs` from the per-based-loop homology
hypothesis

`GenericGenusPeriodLatticeInputs basis` has four atomic fields:

1. `cycleGens` — 2g cycles;
2. `riemannBilinear` — ℝ-linear independence of period vectors;
3. `holomorphicCanonicalClosed` — real/imag components of holomorphic forms
   live in the canonical-closed submodule;
4. `H1_spans_top_canonical` — the projections of `cycleGens` ℤ-span the
   canonical Stokes-quotient.

The fourth field's structural content is replaced here by the
**per-based-loop homology decomposition hypothesis** + a smooth based
path family. The reduction is closed by
`H1_spans_top_canonical_of_basedLoopHomology`.

After this constructor, the user-visible atomic data for the period-
lattice side of the C3 cascade becomes (at generic genus):

* `cycleGens` (a tuple of 2g cycles),
* `riemannBilinear` (period-vector independence),
* `holomorphicCanonicalClosed` (Stokes' theorem applied to holomorphic
  forms' real/imag components),
* `basePoint p₀ : X` + `α : X → SmoothPath p₀ → x` (smooth-path-connectedness),
* `basedLoopHomology` (the genuine genus-≥1 hypothesis: every smooth based
  loop is a ℤ-combo of the cycleGens classes mod stokesBoundaries).

The first three are textbook content. The last two are also textbook:
smooth-path-connectedness on a connected smooth manifold (mathlib gap),
and Hurewicz / cellular-homology generation by symplectic basis classes
on a genus-g surface (smooth Hurewicz gap).

## What this file ships

* `GenericGenusPeriodLatticeInputs.ofBasedLoopHomology` — constructor
  taking the reduced atomic data and producing
  `GenericGenusPeriodLatticeInputs basis`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff
open Module Submodule

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **`GenericGenusPeriodLatticeInputs` from the per-based-loop homology
hypothesis.**

Replaces the fourth atomic field `H1_spans_top_canonical` (a statement
about the canonical Stokes-quotient) by the per-based-loop homology
decomposition hypothesis (a per-loop statement about ℤ-combinations of
`cycleGens` modulo `stokesBoundaries`) + a smooth based-path family
on `X` (smooth-path-connectedness).

The discharge of `H1_spans_top_canonical` is via
`H1_spans_top_canonical_of_basedLoopHomology`. -/
noncomputable def GenericGenusPeriodLatticeInputs.ofBasedLoopHomology
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens :
      Fin (2 * JacobianChallenge.genus X) →
        (PeriodPairingData.ofSmoothCycle X).H1)
    (riemannBilinear :
      LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus X) =>
          periodVector (PeriodPairingData.ofSmoothCycle X) basis (cycleGens i)))
    (holomorphicCanonicalClosed :
      ∀ om : HolomorphicOneForm X,
        realComponent om ∈ canonicalClosedForms 𝓘(ℝ, ℂ) X ∧
        imagComponent om ∈ canonicalClosedForms 𝓘(ℝ, ℂ) X)
    (p₀ : X) (α : X → SmoothPath 𝓘(ℝ, ℂ) X)
    (h_α_src : ∀ x, (α x).src = p₀) (h_α_tgt : ∀ x, (α x).tgt = x)
    (basedLoopHomology :
      BasedLoopHomologyDecompositionHypothesis cycleGens p₀) :
    GenericGenusPeriodLatticeInputs basis where
  cycleGens := cycleGens
  riemannBilinear := riemannBilinear
  holomorphicCanonicalClosed := holomorphicCanonicalClosed
  H1_spans_top_canonical :=
    H1_spans_top_canonical_of_basedLoopHomology
      cycleGens p₀ α h_α_src h_α_tgt basedLoopHomology

/-! ## Nonempty-style headline -/

/-- **Nonempty headline.** From `Nonempty` instances of the per-loop
homology data and smooth-path-connectedness, conclude
`Nonempty (GenericGenusPeriodLatticeInputs basis)`. -/
theorem nonempty_genericGenusPeriodLatticeInputs_ofBasedLoopHomology
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens :
      Fin (2 * JacobianChallenge.genus X) →
        (PeriodPairingData.ofSmoothCycle X).H1)
    (riemannBilinear :
      LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus X) =>
          periodVector (PeriodPairingData.ofSmoothCycle X) basis (cycleGens i)))
    (holomorphicCanonicalClosed :
      ∀ om : HolomorphicOneForm X,
        realComponent om ∈ canonicalClosedForms 𝓘(ℝ, ℂ) X ∧
        imagComponent om ∈ canonicalClosedForms 𝓘(ℝ, ℂ) X)
    (p₀ : X) (α : X → SmoothPath 𝓘(ℝ, ℂ) X)
    (h_α_src : ∀ x, (α x).src = p₀) (h_α_tgt : ∀ x, (α x).tgt = x)
    (basedLoopHomology :
      BasedLoopHomologyDecompositionHypothesis cycleGens p₀) :
    Nonempty (GenericGenusPeriodLatticeInputs basis) :=
  ⟨GenericGenusPeriodLatticeInputs.ofBasedLoopHomology
    basis cycleGens riemannBilinear holomorphicCanonicalClosed
    p₀ α h_α_src h_α_tgt basedLoopHomology⟩

/-- **Headline composition: `Nonempty (PeriodLatticeSymplecticBundle ...)`
from the reduced atomic data.** -/
theorem nonempty_periodLatticeSymplecticBundle_ofBasedLoopHomology
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens :
      Fin (2 * JacobianChallenge.genus X) →
        (PeriodPairingData.ofSmoothCycle X).H1)
    (riemannBilinear :
      LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus X) =>
          periodVector (PeriodPairingData.ofSmoothCycle X) basis (cycleGens i)))
    (holomorphicCanonicalClosed :
      ∀ om : HolomorphicOneForm X,
        realComponent om ∈ canonicalClosedForms 𝓘(ℝ, ℂ) X ∧
        imagComponent om ∈ canonicalClosedForms 𝓘(ℝ, ℂ) X)
    (p₀ : X) (α : X → SmoothPath 𝓘(ℝ, ℂ) X)
    (h_α_src : ∀ x, (α x).src = p₀) (h_α_tgt : ∀ x, (α x).tgt = x)
    (basedLoopHomology :
      BasedLoopHomologyDecompositionHypothesis cycleGens p₀) :
    Nonempty
      (PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) basis) :=
  nonempty_periodLatticeSymplecticBundle_of_genericGenus basis
    (nonempty_genericGenusPeriodLatticeInputs_ofBasedLoopHomology
      basis cycleGens riemannBilinear holomorphicCanonicalClosed
      p₀ α h_α_src h_α_tgt basedLoopHomology)

end JacobianChallenge

end
