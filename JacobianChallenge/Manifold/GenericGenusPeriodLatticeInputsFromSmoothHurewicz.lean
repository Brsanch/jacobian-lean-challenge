/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.GenericGenusPeriodLatticeInputsFromBasedLoopHomology
import JacobianChallenge.Manifold.SmoothHurewiczHypothesis

set_option linter.unusedSectionVars false

/-! # `GenericGenusPeriodLatticeInputs` from a smooth symplectic basis +
smooth-Hurewicz hypothesis

The cleanest user-facing entry point for genus-≥1: takes a
`SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ (genus X)` (the chosen `2g` based
loops representing the symplectic homology basis) + a
`SmoothHurewiczHypothesis` (every smooth based loop is a ℤ-combination
of basis-loop classes modulo Stokes-boundary) + the three other
atomic inputs (`riemannBilinear`, `holomorphicCanonicalClosed`,
smooth-path-connectedness data), and produces the full
`GenericGenusPeriodLatticeInputs basis` structure.

The `cycleGens` field is derived automatically from the symplectic
basis via `SmoothSymplecticBasis.cycleGens`; the
per-loop-decomposition hypothesis is the smooth-Hurewicz hypothesis
applied to the same basis.

## What this file ships

* `GenericGenusPeriodLatticeInputs.ofSmoothHurewicz` — the
  constructor.
* `nonempty_periodLatticeSymplecticBundle_ofSmoothHurewicz` —
  `Nonempty` composition through to the symplectic bundle.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology Bundle ContDiff
open Module Submodule

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **`GenericGenusPeriodLatticeInputs` from a smooth symplectic basis +
smooth-Hurewicz hypothesis.** -/
noncomputable def GenericGenusPeriodLatticeInputs.ofSmoothHurewicz
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (p₀ : X)
    (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ (JacobianChallenge.genus X))
    (riemannBilinear :
      LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus X) =>
          periodVector (PeriodPairingData.ofSmoothCycle X) basis (sb.cycleGens i)))
    (holomorphicCanonicalClosed :
      ∀ om : HolomorphicOneForm X,
        realComponent om ∈ canonicalClosedForms 𝓘(ℝ, ℂ) X ∧
        imagComponent om ∈ canonicalClosedForms 𝓘(ℝ, ℂ) X)
    (α : X → SmoothPath 𝓘(ℝ, ℂ) X)
    (h_α_src : ∀ x, (α x).src = p₀) (h_α_tgt : ∀ x, (α x).tgt = x)
    (smoothHurewicz : SmoothHurewiczHypothesis sb) :
    GenericGenusPeriodLatticeInputs basis :=
  GenericGenusPeriodLatticeInputs.ofBasedLoopHomology
    basis sb.cycleGens riemannBilinear holomorphicCanonicalClosed
    p₀ α h_α_src h_α_tgt
    (SmoothHurewiczHypothesis.basedLoopHomology_of_smoothHurewicz smoothHurewicz)

/-- **Nonempty composition through to the symplectic bundle.** -/
theorem nonempty_periodLatticeSymplecticBundle_ofSmoothHurewicz
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (p₀ : X)
    (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ (JacobianChallenge.genus X))
    (riemannBilinear :
      LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus X) =>
          periodVector (PeriodPairingData.ofSmoothCycle X) basis (sb.cycleGens i)))
    (holomorphicCanonicalClosed :
      ∀ om : HolomorphicOneForm X,
        realComponent om ∈ canonicalClosedForms 𝓘(ℝ, ℂ) X ∧
        imagComponent om ∈ canonicalClosedForms 𝓘(ℝ, ℂ) X)
    (α : X → SmoothPath 𝓘(ℝ, ℂ) X)
    (h_α_src : ∀ x, (α x).src = p₀) (h_α_tgt : ∀ x, (α x).tgt = x)
    (smoothHurewicz : SmoothHurewiczHypothesis sb) :
    Nonempty
      (PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) basis) :=
  nonempty_periodLatticeSymplecticBundle_of_genericGenus basis
    ⟨GenericGenusPeriodLatticeInputs.ofSmoothHurewicz basis p₀ sb
      riemannBilinear holomorphicCanonicalClosed
      α h_α_src h_α_tgt smoothHurewicz⟩

end JacobianChallenge

end
