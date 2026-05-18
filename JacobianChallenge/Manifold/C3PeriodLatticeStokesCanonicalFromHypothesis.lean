/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3PeriodLatticeStokesCanonical
import JacobianChallenge.Manifold.HolomorphicComponentsCanonicalClosed

set_option linter.unusedSectionVars false

/-! # `C3PeriodLatticeStokesSpanTopInputs` from `HolomorphicStokesHypothesis`

Chains `HolomorphicComponentsCanonicalClosed.of_hypothesis` and
`C3PeriodLatticeStokesSpanTopInputs.ofCanonical` into a single
constructor that takes the *most* atomic period-lattice classical
input shape:

* `cycleGens : Fin 2g → SmoothCycle 𝓘(ℝ, ℂ) X` — chosen symplectic
  homology basis tuple.
* `riemannBilinear` — ℝ-LI of the `2g` period vectors.
* `stokesHypothesis : HolomorphicStokesHypothesis X` — Stokes' theorem
  for the real and imaginary components of every holomorphic 1-form
  against every smooth 2-simplex boundary (the single classical
  Stokes-side input).
* `H1_spans_top_canonical` — H₁ generation via the canonical Stokes
  quotient.

The fully reduced classical input boundary for the period-lattice side
of `C3FullInput X`. The `boundaries` and `closedForms` choices are
canonical (no consumer choice); the `Stokes` content is the single
atomic hypothesis `HolomorphicStokesHypothesis`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **Most-atomic constructor** for `C3PeriodLatticeStokesSpanTopInputs`:
takes the symplectic-basis tuple, Riemann bilinear non-degeneracy, the
single `HolomorphicStokesHypothesis X` Stokes input, and the canonical
H₁ generation hypothesis. The `stokes` field is built from the
canonical bundle `StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X`. -/
noncomputable def C3PeriodLatticeStokesSpanTopInputs.ofStokesHypothesis
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens :
      Fin (2 * JacobianChallenge.genus X) →
        (PeriodPairingData.ofSmoothCycle X).H1)
    (riemannBilinear :
      LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus X) =>
          periodVector (PeriodPairingData.ofSmoothCycle X) basis (cycleGens i)))
    (stokesHypothesis : HolomorphicStokesHypothesis X)
    (H1_spans_top_canonical :
      (Submodule.span ℤ
        (Set.range (fun i : Fin (2 * JacobianChallenge.genus X) =>
          ((StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).proj
              (cycleGens i) :
            (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).H1)))) = ⊤) :
    C3PeriodLatticeStokesSpanTopInputs basis :=
  C3PeriodLatticeStokesSpanTopInputs.ofCanonical basis cycleGens
    riemannBilinear
    (HolomorphicComponentsCanonicalClosed.of_hypothesis stokesHypothesis)
    H1_spans_top_canonical

/-- **Constructor variant from a `Subsingleton (HolomorphicOneForm X)`
genus-0 manifold.** At genus 0 (with HolomorphicOneForm subsingleton),
the Stokes-side content is vacuous and only the H₁ generation
hypothesis remains. Note: at genus 0 the symplectic-basis tuple is
empty (`2 * 0 = 0`) and `riemannBilinear` is the trivial
`linearIndependent_empty_type`. -/
noncomputable def C3PeriodLatticeStokesSpanTopInputs.ofCanonicalGenusZero
    [Subsingleton (HolomorphicOneForm X)]
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens :
      Fin (2 * JacobianChallenge.genus X) →
        (PeriodPairingData.ofSmoothCycle X).H1)
    (riemannBilinear :
      LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus X) =>
          periodVector (PeriodPairingData.ofSmoothCycle X) basis (cycleGens i)))
    (H1_spans_top_canonical :
      (Submodule.span ℤ
        (Set.range (fun i : Fin (2 * JacobianChallenge.genus X) =>
          ((StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).proj
              (cycleGens i) :
            (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).H1)))) = ⊤) :
    C3PeriodLatticeStokesSpanTopInputs basis :=
  C3PeriodLatticeStokesSpanTopInputs.ofCanonical basis cycleGens
    riemannBilinear
    HolomorphicComponentsCanonicalClosed.of_subsingleton
    H1_spans_top_canonical

end JacobianChallenge

end
