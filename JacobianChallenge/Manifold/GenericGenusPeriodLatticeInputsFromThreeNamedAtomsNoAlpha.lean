/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.GenericGenusPeriodLatticeInputsFromThreeNamedAtoms
import JacobianChallenge.Manifold.SmoothPathLocalConvex

set_option linter.unusedSectionVars false

/-! # `GenericGenusPeriodLatticeInputs` from three named atoms, no α-data

A further reduction of
`GenericGenusPeriodLatticeInputs.ofThreeNamedAtoms`: discharges the
smooth-path-connectedness data `(α, h_α_src, h_α_tgt)` from
`[ConnectedSpace X]` via `smoothPathConnected_of_preconnected` +
`Classical.choose`. On any compact connected complex 1-manifold the
α-data is therefore unconditional, leaving only the three substantive
named atoms:

* `sb` — `SmoothSymplecticBasis` (surface classification).
* `riemannBilinear` — Hodge ℝ-linear independence.
* `smoothHurewicz` — `SmoothHurewiczHypothesis sb`.

This collapses the inputs of `nonempty_periodLatticeSymplecticBundle_ofThreeNamedAtoms`
to *three* named atoms — no path-picker required.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex Module Submodule

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`GenericGenusPeriodLatticeInputs` from three named atoms, α-data
discharged.**

Compared to `ofThreeNamedAtoms`, the three smooth-path-connectedness
arguments `(α, h_α_src, h_α_tgt)` are absorbed into the discharge via
`smoothPathConnected_of_preconnected` (which is unconditional on any
preconnected complex 1-manifold) and `Classical.choose`. -/
noncomputable def GenericGenusPeriodLatticeInputs.ofThreeNamedAtomsNoAlpha
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (p₀ : X)
    (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ (JacobianChallenge.genus X))
    (riemannBilinear :
      LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus X) =>
          periodVector (PeriodPairingData.ofSmoothCycle X) basis
            (sb.cycleGens i)))
    (smoothHurewicz : SmoothHurewiczHypothesis sb) :
    GenericGenusPeriodLatticeInputs basis :=
  let hSPC : SmoothPathConnected 𝓘(ℝ, ℂ) X :=
    smoothPathConnected_of_preconnected
  GenericGenusPeriodLatticeInputs.ofThreeNamedAtoms
    basis p₀ sb riemannBilinear smoothHurewicz
    (fun x => Classical.choose (hSPC p₀ x))
    (fun x => (Classical.choose_spec (hSPC p₀ x)).1)
    (fun x => (Classical.choose_spec (hSPC p₀ x)).2)

/-- **`Nonempty` headline from three named atoms, α-data discharged.** -/
theorem nonempty_genericGenusPeriodLatticeInputs_ofThreeNamedAtomsNoAlpha
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (p₀ : X)
    (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ (JacobianChallenge.genus X))
    (riemannBilinear :
      LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus X) =>
          periodVector (PeriodPairingData.ofSmoothCycle X) basis
            (sb.cycleGens i)))
    (smoothHurewicz : SmoothHurewiczHypothesis sb) :
    Nonempty (GenericGenusPeriodLatticeInputs basis) :=
  ⟨GenericGenusPeriodLatticeInputs.ofThreeNamedAtomsNoAlpha
    basis p₀ sb riemannBilinear smoothHurewicz⟩

/-- **Headline composite: `Nonempty (PeriodLatticeSymplecticBundle ...)`
from three named atoms, α-data discharged.**

This is the *minimal-input* composite for the period-lattice side at
general genus on any compact connected complex 1-manifold: three named
classical hypotheses (surface classification + Hodge bilinear + smooth-
Hurewicz) and a chosen base point. Smooth-path-connectedness and the
holomorphic-Stokes/canonical-closed/depth-N atoms are all discharged
unconditionally upstream. -/
theorem nonempty_periodLatticeSymplecticBundle_ofThreeNamedAtomsNoAlpha
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (p₀ : X)
    (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ (JacobianChallenge.genus X))
    (riemannBilinear :
      LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus X) =>
          periodVector (PeriodPairingData.ofSmoothCycle X) basis
            (sb.cycleGens i)))
    (smoothHurewicz : SmoothHurewiczHypothesis sb) :
    Nonempty
      (PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) basis) :=
  let hSPC : SmoothPathConnected 𝓘(ℝ, ℂ) X :=
    smoothPathConnected_of_preconnected
  nonempty_periodLatticeSymplecticBundle_ofThreeNamedAtoms
    basis p₀ sb riemannBilinear smoothHurewicz
    (fun x => Classical.choose (hSPC p₀ x))
    (fun x => (Classical.choose_spec (hSPC p₀ x)).1)
    (fun x => (Classical.choose_spec (hSPC p₀ x)).2)

end JacobianChallenge

end
