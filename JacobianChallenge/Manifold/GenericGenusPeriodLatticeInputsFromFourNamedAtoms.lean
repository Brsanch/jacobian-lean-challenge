/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.GenericGenusPeriodLatticeInputsFromSubdivision
import JacobianChallenge.Manifold.GenericGenusPeriodLatticeInputsFromSmoothHurewicz

set_option linter.unusedSectionVars false

/-! # `GenericGenusPeriodLatticeInputs` from the four named-atom inputs

The four atomic inputs of `GenericGenusPeriodLatticeInputs basis` at
general genus are:

1. **`cycleGens`** — chosen via `SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ g`
   (surface classification + choice of symplectic homology basis).
2. **`riemannBilinear`** — ℝ-linear independence of the `2g` period
   vectors (Hodge bilinear non-degeneracy).
3. **`holomorphicCanonicalClosed`** — reduced to
   `SubdivisionTelescopingTo2Simplex_named X` via
   `ChartContainedSmooth2Simplex.lean`
   (Whitney-smoothed barycentric subdivision of `Δ²`).
4. **`H1_spans_top_canonical`** — reduced to `SmoothHurewiczHypothesis sb`
   via `SmoothHurewiczHypothesis.lean` and
   `H1_spans_top_canonical_of_basedLoopHomology`
   (smooth-Hurewicz: every based loop is ℤ-homologous to a
   combination of basis loops modulo Stokes-boundary).

This file ships the composite constructor that takes the four atomic
inputs in their cleanest reduced/named form and produces the full
`GenericGenusPeriodLatticeInputs basis` (and `Nonempty
(PeriodLatticeSymplecticBundle ...)` composite).

## What this file ships

* `GenericGenusPeriodLatticeInputs.ofFourNamedAtoms` — the composite
  constructor.
* `nonempty_periodLatticeSymplecticBundle_ofFourNamedAtoms` — the
  `Nonempty (PeriodLatticeSymplecticBundle ...)` headline from the
  same four inputs.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Module Submodule

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`GenericGenusPeriodLatticeInputs` from the four named-atom inputs.**

Takes:
* `basis` — a ℂ-basis of `HolomorphicOneForm X` of dimension `g = genus X`.
* `p₀ : X` — the base point.
* `sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ (genus X)` — the chosen
  `2g` based loops (atom 1, via `sb.cycleGens`).
* `riemannBilinear` — ℝ-linear independence of period vectors (atom 2).
* `h_subdiv : SubdivisionTelescopingTo2Simplex_named X` — the
  2-simplex subdivision-telescoping atom (atom 3).
* `smoothHurewicz : SmoothHurewiczHypothesis sb` — the smooth-Hurewicz
  hypothesis on the chosen basis (atom 4).
* `α : X → SmoothPath 𝓘(ℝ, ℂ) X` — smooth-path-connectedness data
  (`α x` is a smooth path from `p₀` to `x`).

The `holomorphicCanonicalClosed` field is built from `h_subdiv` via
`holomorphicComponentsCanonicalClosed_of_subdivisionTo2Simplex`; the
`H1_spans_top_canonical` field is built from `smoothHurewicz` + `α`
via the `ofBasedLoopHomology` route. -/
noncomputable def GenericGenusPeriodLatticeInputs.ofFourNamedAtoms
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (p₀ : X)
    (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ (JacobianChallenge.genus X))
    (riemannBilinear :
      LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus X) =>
          periodVector (PeriodPairingData.ofSmoothCycle X) basis (sb.cycleGens i)))
    (h_subdiv : SubdivisionTelescopingTo2Simplex_named (X := X))
    (smoothHurewicz : SmoothHurewiczHypothesis sb)
    (α : X → SmoothPath 𝓘(ℝ, ℂ) X)
    (h_α_src : ∀ x, (α x).src = p₀) (h_α_tgt : ∀ x, (α x).tgt = x) :
    GenericGenusPeriodLatticeInputs basis :=
  GenericGenusPeriodLatticeInputs.ofSmoothHurewicz
    basis p₀ sb riemannBilinear
    (holomorphicComponentsCanonicalClosed_of_subdivisionTo2Simplex h_subdiv)
    α h_α_src h_α_tgt smoothHurewicz

/-- **`Nonempty` headline from the four named-atom inputs.** -/
theorem nonempty_genericGenusPeriodLatticeInputs_ofFourNamedAtoms
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (p₀ : X)
    (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ (JacobianChallenge.genus X))
    (riemannBilinear :
      LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus X) =>
          periodVector (PeriodPairingData.ofSmoothCycle X) basis (sb.cycleGens i)))
    (h_subdiv : SubdivisionTelescopingTo2Simplex_named (X := X))
    (smoothHurewicz : SmoothHurewiczHypothesis sb)
    (α : X → SmoothPath 𝓘(ℝ, ℂ) X)
    (h_α_src : ∀ x, (α x).src = p₀) (h_α_tgt : ∀ x, (α x).tgt = x) :
    Nonempty (GenericGenusPeriodLatticeInputs basis) :=
  ⟨GenericGenusPeriodLatticeInputs.ofFourNamedAtoms
    basis p₀ sb riemannBilinear h_subdiv smoothHurewicz α h_α_src h_α_tgt⟩

/-- **Headline composite: `Nonempty (PeriodLatticeSymplecticBundle ...)`
from the four named-atom inputs.**

This is the "everything reduced to named classical hypotheses"
composite. The deep classical content is bundled into the four
hypothesis arguments:
* `sb` — surface classification (existence of symplectic basis).
* `riemannBilinear` — Hodge theory (ℝ-linear independence).
* `h_subdiv` — 2-simplex subdivision telescoping (Whitney smoothing).
* `smoothHurewicz` — smooth-Hurewicz theorem.

`α` together with `h_α_src`/`h_α_tgt` is smooth-path-connectedness
data. -/
theorem nonempty_periodLatticeSymplecticBundle_ofFourNamedAtoms
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (p₀ : X)
    (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ (JacobianChallenge.genus X))
    (riemannBilinear :
      LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus X) =>
          periodVector (PeriodPairingData.ofSmoothCycle X) basis (sb.cycleGens i)))
    (h_subdiv : SubdivisionTelescopingTo2Simplex_named (X := X))
    (smoothHurewicz : SmoothHurewiczHypothesis sb)
    (α : X → SmoothPath 𝓘(ℝ, ℂ) X)
    (h_α_src : ∀ x, (α x).src = p₀) (h_α_tgt : ∀ x, (α x).tgt = x) :
    Nonempty
      (PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) basis) :=
  nonempty_periodLatticeSymplecticBundle_of_genericGenus basis
    (nonempty_genericGenusPeriodLatticeInputs_ofFourNamedAtoms
      basis p₀ sb riemannBilinear h_subdiv smoothHurewicz α h_α_src h_α_tgt)

end JacobianChallenge
