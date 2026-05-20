/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3PeriodLatticeStokesCanonicalFromHypothesis
import JacobianChallenge.Manifold.UniformChartContainmentDepth

set_option linter.unusedSectionVars false

/-! # `C3PeriodLatticeStokesSpanTopInputs` constructor without the Stokes argument

Drop-one structural cleanup leveraging
`holomorphicStokesHypothesis_holds_unconditional` (chip D): the
existing
`C3PeriodLatticeStokesSpanTopInputs.ofStokesHypothesis` takes
`stokesHypothesis : HolomorphicStokesHypothesis X` as an argument
— this is now an unconditional theorem on every compact connected
complex 1-manifold, so the argument can be dropped from the
constructor's signature.

This file ships `ofStokesUnconditional`, a sibling of
`ofStokesHypothesis` that supplies the Stokes' theorem internally
via `holomorphicStokesHypothesis_holds_unconditional`. The remaining
three inputs (`basis`, `cycleGens`, `riemannBilinear`,
`H1_spans_top_canonical`) are the genuinely-open content.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`C3PeriodLatticeStokesSpanTopInputs` from three named inputs.**

Variant of `C3PeriodLatticeStokesSpanTopInputs.ofStokesHypothesis`
that drops the `stokesHypothesis : HolomorphicStokesHypothesis X`
argument: that hypothesis is now unconditional via
`holomorphicStokesHypothesis_holds_unconditional` (chip D).

The remaining three inputs are the genuinely-open period-lattice
content at general genus:
* `cycleGens` — choice of symplectic homology basis tuple.
* `riemannBilinear` — Hodge bilinear non-degeneracy.
* `H1_spans_top_canonical` — H₁ generation via the canonical
  Stokes quotient. -/
noncomputable def C3PeriodLatticeStokesSpanTopInputs.ofStokesUnconditional
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
  C3PeriodLatticeStokesSpanTopInputs.ofStokesHypothesis basis cycleGens
    riemannBilinear
    (holomorphicStokesHypothesis_holds_unconditional (X := X))
    H1_spans_top_canonical

end JacobianChallenge

end
