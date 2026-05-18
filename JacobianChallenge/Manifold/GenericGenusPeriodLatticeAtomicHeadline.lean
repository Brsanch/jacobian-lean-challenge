/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.GenericGenusPeriodLatticeInputsFromBasedLoopHomology
import JacobianChallenge.Manifold.HolomorphicStokesFromComplexBoundary

set_option linter.unusedSectionVars false

/-! # Most-atomic headline for the generic genus-≥1 period-lattice
construction

This file ships the most-reduced entry point currently available for
constructing `PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X)
basis` on a general compact connected complex 1-manifold `X`. The
construction takes:

1. `cycleGens : Fin (2g) → SmoothCycle 𝓘(ℝ, ℂ) X` — a chosen tuple of
   `2g` smooth 1-cycles (a "symplectic homology basis"). Geometric
   data, supplied by the user.
2. `riemannBilinear` — ℝ-linear independence of the `2g` period
   vectors against `basis` (Riemann bilinear non-degeneracy).
3. `holomorphicComplexBoundary` — `HolomorphicComplexBoundaryVanishingHypothesis X`
   (Stokes' theorem applied to every holomorphic 1-form on every
   smooth 2-simplex boundary, in a single complex-valued statement).
4. `(p₀, α, h_α_src, h_α_tgt)` — basepoint + smooth-path-connectedness
   data.
5. `basedLoopHomology` — `BasedLoopHomologyDecompositionHypothesis
   cycleGens p₀` (smooth-Hurewicz on `X`: every smooth based loop's
   class is a ℤ-combination of the symplectic basis classes in
   `H₁(X; ℤ)`).

This is the smallest atomic data list currently in tree that suffices
for the full period-lattice + symplectic-bundle construction.

The genus-0 case (`X = RS`) discharges (1) via `IsEmpty.elim`, (2)
vacuously, (3) via subsingleton-`HolomorphicOneForm`, (5) via the
unconditional `basedSmoothLoopsBoundHypothesis_RS_holds` (with all
coefficients 0), and (4) via `smoothPathConnected_RiemannSphere`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology Bundle ContDiff
open Module Submodule

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **Atomic headline.** Build `GenericGenusPeriodLatticeInputs basis`
from the most-reduced atomic data: cycleGens + Riemann bilinear +
complex-valued holomorphic Stokes + smooth-path-connectedness +
per-based-loop homology decomposition.

The holomorphic-Stokes input here is the **single** complex-valued
predicate `HolomorphicComplexBoundaryVanishingHypothesis X`, factored
through `HolomorphicComponentsCanonicalClosed.of_complexBoundary` to
the canonical-closed-form membership. -/
noncomputable def GenericGenusPeriodLatticeInputs.ofAtomicData
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens :
      Fin (2 * JacobianChallenge.genus X) →
        (PeriodPairingData.ofSmoothCycle X).H1)
    (riemannBilinear :
      LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus X) =>
          periodVector (PeriodPairingData.ofSmoothCycle X) basis (cycleGens i)))
    (holomorphicComplexBoundary :
      HolomorphicComplexBoundaryVanishingHypothesis X)
    (p₀ : X) (α : X → SmoothPath 𝓘(ℝ, ℂ) X)
    (h_α_src : ∀ x, (α x).src = p₀) (h_α_tgt : ∀ x, (α x).tgt = x)
    (basedLoopHomology :
      BasedLoopHomologyDecompositionHypothesis cycleGens p₀) :
    GenericGenusPeriodLatticeInputs basis :=
  GenericGenusPeriodLatticeInputs.ofBasedLoopHomology
    basis cycleGens riemannBilinear
    (HolomorphicComponentsCanonicalClosed.of_complexBoundary
      holomorphicComplexBoundary)
    p₀ α h_α_src h_α_tgt basedLoopHomology

/-- **Atomic-data Nonempty composition** through to the period-lattice
symplectic bundle. -/
theorem nonempty_periodLatticeSymplecticBundle_ofAtomicData
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens :
      Fin (2 * JacobianChallenge.genus X) →
        (PeriodPairingData.ofSmoothCycle X).H1)
    (riemannBilinear :
      LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus X) =>
          periodVector (PeriodPairingData.ofSmoothCycle X) basis (cycleGens i)))
    (holomorphicComplexBoundary :
      HolomorphicComplexBoundaryVanishingHypothesis X)
    (p₀ : X) (α : X → SmoothPath 𝓘(ℝ, ℂ) X)
    (h_α_src : ∀ x, (α x).src = p₀) (h_α_tgt : ∀ x, (α x).tgt = x)
    (basedLoopHomology :
      BasedLoopHomologyDecompositionHypothesis cycleGens p₀) :
    Nonempty
      (PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) basis) :=
  nonempty_periodLatticeSymplecticBundle_of_genericGenus basis
    ⟨GenericGenusPeriodLatticeInputs.ofAtomicData basis cycleGens
      riemannBilinear holomorphicComplexBoundary
      p₀ α h_α_src h_α_tgt basedLoopHomology⟩

end JacobianChallenge

end
