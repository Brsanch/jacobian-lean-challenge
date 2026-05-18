/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3PeriodLatticeStokesH1Generation
import JacobianChallenge.Manifold.StokesCanonicalClosedForms

set_option linter.unusedSectionVars false

/-! # `C3PeriodLatticeStokesSpanTopInputs` via the canonical Stokes bundle

`C3PeriodLatticeStokesSpanTopInputs basis` (in
`C3PeriodLatticeStokesH1Generation.lean`) takes a *consumer-supplied*
`StokesBoundaryInvariance 𝓘(ℝ, ℂ) X` bundle. With the canonical
`Smooth2Chain`-based Stokes data (`stokesBoundaries` for the boundary
subgroup, `canonicalClosedForms` for the closed-form submodule) now
available unconditionally via `StokesCanonicalClosedForms.lean`, we
can construct that bundle automatically and reduce the user-visible
data to four atomic fields:

* `cycleGens` — tuple of `2g` smooth cycle generators;
* `riemannBilinear` — ℝ-linear independence of period vectors;
* `holomorphicCanonicalClosed` — each holomorphic 1-form's real and
  imaginary components individually satisfy the single-simplex Stokes
  vanishing on every smooth 2-simplex boundary (Stokes' theorem for
  holomorphic 1-forms on `X`);
* `H1_spans_top_canonical` — H₁ generation against the canonical
  Stokes-quotient `SmoothCycle / stokesBoundaries`.

The `stokes` field is the canonical bundle `StokesBoundaryInvariance.canonical`
and the `holomorphic_closed` field is derived from the more-atomic
`holomorphicCanonicalClosed` directly.

## Significance

After this chip, the period-lattice side of `C3FullInput X` reduces to
**genuinely classical content** with no infrastructure-of-the-bundle
choices left to the consumer:

1. choice of `2g` cycle generators (symplectic homology basis);
2. ℝ-linear independence of their period vectors (Riemann bilinear);
3. Stokes' theorem for holomorphic 1-forms (the real / imaginary parts
   integrate to zero around every smooth 2-simplex boundary);
4. H₁ ℤ-generation by the chosen tuple (cellular homology / surface
   classification).

The `boundaries` and `closedForms` choices are canonical; the user
need not supply them.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-! ## Canonical-bundle constructor -/

/-- **`C3PeriodLatticeStokesSpanTopInputs` via the canonical Stokes
bundle.** Reduces the consumer-supplied data to four atomic fields by
fixing `stokes := StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X`.

The fourth input `H1_spans_top_canonical` quantifies over the canonical
quotient `SmoothCycle 𝓘(ℝ, ℂ) X ⧸ stokesBoundaries 𝓘(ℝ, ℂ) X`, which
is exactly `(StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).H1`. -/
noncomputable def C3PeriodLatticeStokesSpanTopInputs.ofCanonical
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
    (H1_spans_top_canonical :
      (Submodule.span ℤ
        (Set.range (fun i : Fin (2 * JacobianChallenge.genus X) =>
          ((StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).proj
              (cycleGens i) :
            (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).H1)))) = ⊤) :
    C3PeriodLatticeStokesSpanTopInputs basis where
  cycleGens := cycleGens
  riemannBilinear := riemannBilinear
  stokes := StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X
  holomorphic_closed := holomorphicCanonicalClosed
  H1_spans_top := H1_spans_top_canonical

@[simp] lemma C3PeriodLatticeStokesSpanTopInputs.ofCanonical_stokes
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
    (H1_spans_top_canonical :
      (Submodule.span ℤ
        (Set.range (fun i : Fin (2 * JacobianChallenge.genus X) =>
          ((StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).proj
              (cycleGens i) :
            (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).H1)))) = ⊤) :
    (C3PeriodLatticeStokesSpanTopInputs.ofCanonical basis cycleGens
      riemannBilinear holomorphicCanonicalClosed H1_spans_top_canonical).stokes
      = StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X := rfl

@[simp] lemma C3PeriodLatticeStokesSpanTopInputs.ofCanonical_cycleGens
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
    (H1_spans_top_canonical :
      (Submodule.span ℤ
        (Set.range (fun i : Fin (2 * JacobianChallenge.genus X) =>
          ((StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).proj
              (cycleGens i) :
            (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).H1)))) = ⊤) :
    (C3PeriodLatticeStokesSpanTopInputs.ofCanonical basis cycleGens
      riemannBilinear holomorphicCanonicalClosed H1_spans_top_canonical).cycleGens
      = cycleGens := rfl

end JacobianChallenge

end
