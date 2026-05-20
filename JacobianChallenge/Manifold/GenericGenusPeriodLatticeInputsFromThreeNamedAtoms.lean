/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.GenericGenusPeriodLatticeInputsFromFourNamedAtoms
import JacobianChallenge.Manifold.UniformChartContainmentDepth
import JacobianChallenge.Manifold.SubdivisionTelescopingFromUniformDepth

set_option linter.unusedSectionVars false

/-! # `GenericGenusPeriodLatticeInputs` from three named-atom inputs

A drop-one variant of `GenericGenusPeriodLatticeInputs.ofFourNamedAtoms`:
discharges the third atomic input
(`SubdivisionTelescopingTo2Simplex_named X`) via the unconditional
`uniformChartContainmentDepth_named_holds` (chip D + bridge), leaving
only three named atoms:

* `sb` — `SmoothSymplecticBasis` (surface classification).
* `riemannBilinear` — Hodge ℝ-linear independence.
* `smoothHurewicz` — `SmoothHurewiczHypothesis sb`.

Plus the smooth-path-connectedness data `(α, h_α_src, h_α_tgt)`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex Module Submodule

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`GenericGenusPeriodLatticeInputs` from the three remaining named-atom
inputs.**

Drops the `h_subdiv : SubdivisionTelescopingTo2Simplex_named X` argument
from `ofFourNamedAtoms`: it is now unconditional via
`uniformChartContainmentDepth_named_holds` composed with
`subdivisionTelescopingTo2Simplex_named_of_uniformChartContainmentDepth`. -/
noncomputable def GenericGenusPeriodLatticeInputs.ofThreeNamedAtoms
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (p₀ : X)
    (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ (JacobianChallenge.genus X))
    (riemannBilinear :
      LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus X) =>
          periodVector (PeriodPairingData.ofSmoothCycle X) basis
            (sb.cycleGens i)))
    (smoothHurewicz : SmoothHurewiczHypothesis sb)
    (α : X → SmoothPath 𝓘(ℝ, ℂ) X)
    (h_α_src : ∀ x, (α x).src = p₀) (h_α_tgt : ∀ x, (α x).tgt = x) :
    GenericGenusPeriodLatticeInputs basis :=
  GenericGenusPeriodLatticeInputs.ofFourNamedAtoms
    basis p₀ sb riemannBilinear
    (subdivisionTelescopingTo2Simplex_named_of_uniformChartContainmentDepth
      uniformChartContainmentDepth_named_holds)
    smoothHurewicz α h_α_src h_α_tgt

/-- **`Nonempty` headline from the three remaining named-atom inputs.** -/
theorem nonempty_genericGenusPeriodLatticeInputs_ofThreeNamedAtoms
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (p₀ : X)
    (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ (JacobianChallenge.genus X))
    (riemannBilinear :
      LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus X) =>
          periodVector (PeriodPairingData.ofSmoothCycle X) basis
            (sb.cycleGens i)))
    (smoothHurewicz : SmoothHurewiczHypothesis sb)
    (α : X → SmoothPath 𝓘(ℝ, ℂ) X)
    (h_α_src : ∀ x, (α x).src = p₀) (h_α_tgt : ∀ x, (α x).tgt = x) :
    Nonempty (GenericGenusPeriodLatticeInputs basis) :=
  ⟨GenericGenusPeriodLatticeInputs.ofThreeNamedAtoms
    basis p₀ sb riemannBilinear smoothHurewicz α h_α_src h_α_tgt⟩

/-- **Headline composite: `Nonempty (PeriodLatticeSymplecticBundle ...)`
from the three remaining named-atom inputs.**

Compared to `nonempty_periodLatticeSymplecticBundle_ofFourNamedAtoms`,
the 2-simplex subdivision telescoping atom has been absorbed into the
unconditional discharge — it is no longer a named hypothesis. The three
remaining hypotheses are all surface-classification / Hodge-theory /
smooth-Hurewicz content. -/
theorem nonempty_periodLatticeSymplecticBundle_ofThreeNamedAtoms
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (p₀ : X)
    (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ (JacobianChallenge.genus X))
    (riemannBilinear :
      LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus X) =>
          periodVector (PeriodPairingData.ofSmoothCycle X) basis
            (sb.cycleGens i)))
    (smoothHurewicz : SmoothHurewiczHypothesis sb)
    (α : X → SmoothPath 𝓘(ℝ, ℂ) X)
    (h_α_src : ∀ x, (α x).src = p₀) (h_α_tgt : ∀ x, (α x).tgt = x) :
    Nonempty
      (PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) basis) :=
  nonempty_periodLatticeSymplecticBundle_ofFourNamedAtoms
    basis p₀ sb riemannBilinear
    (subdivisionTelescopingTo2Simplex_named_of_uniformChartContainmentDepth
      uniformChartContainmentDepth_named_holds)
    smoothHurewicz α h_α_src h_α_tgt

end JacobianChallenge

end
