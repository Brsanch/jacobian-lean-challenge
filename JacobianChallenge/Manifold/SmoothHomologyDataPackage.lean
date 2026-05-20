/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.GenericGenusPeriodLatticeInputsFromThreeNamedAtomsNoAlpha

set_option linter.unusedSectionVars false

/-! # `SmoothHomologyDataPackage`: the three named period-lattice atoms bundled

A single-structure packaging of the three remaining named atomic
inputs at general genus to the period-lattice symplectic bundle:

* `basePoint : X` (a chosen base point);
* `symplecticBasis` — a `SmoothSymplecticBasis 𝓘(ℝ, ℂ) X basePoint
  (genus X)` (surface classification + choice of symplectic homology
  basis representatives);
* `hurewicz` — `SmoothHurewiczHypothesis symplecticBasis`
  (every smooth based loop is a ℤ-combination of basis loops modulo
  Stokes-boundary);
* `bilinear` — ℝ-linear independence of the `2g` period vectors
  against the supplied holomorphic ω-basis (Hodge bilinear
  non-degeneracy).

On a compact connected complex 1-manifold, the smooth-path-
connectedness data and the three unconditional chip-D atoms
(`UniformChartContainmentDepth_named`,
`HolomorphicComplexBoundaryVanishingHypothesis`,
`HolomorphicStokesHypothesis`,
`HolomorphicComponentsCanonicalClosed`) are already discharged
upstream. Hence the open content of the period-lattice side of items
5/11/12/13/17/18/21 factors through this single structure: every
field is a substantive classical input (surface classification +
smooth-Hurewicz + Riemann bilinear non-degeneracy).

## What this file ships

* `SmoothHomologyDataPackage` — the structure bundling the three
  named atoms + base point.
* `SmoothHomologyDataPackage.toGenericGenusInputs` — feed-through to
  `GenericGenusPeriodLatticeInputs basis`.
* `nonempty_genericGenusPeriodLatticeInputs_of_smoothHomologyDataPackage`
  — `Nonempty (GenericGenusPeriodLatticeInputs basis)` from a single
  `SmoothHomologyDataPackage` input.
* `nonempty_periodLatticeSymplecticBundle_of_smoothHomologyDataPackage`
  — `Nonempty (PeriodLatticeSymplecticBundle data basis)` from a
  single `SmoothHomologyDataPackage` input. This is the headline
  one-input composite.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex Module Submodule

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`SmoothHomologyDataPackage X basis_ω`** — the single structure
bundling the three named period-lattice atoms at general genus, against
a fixed ℂ-basis `basis_ω : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)`. -/
structure SmoothHomologyDataPackage
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)) where
  /-- A chosen base point of `X`. -/
  basePoint : X
  /-- The tuple of `2g` based loops at `basePoint` (data of a symplectic
  homology basis). -/
  symplecticBasis :
    SmoothSymplecticBasis 𝓘(ℝ, ℂ) X basePoint (JacobianChallenge.genus X)
  /-- Smooth-Hurewicz: every smooth based loop at `basePoint` is a
  ℤ-combination of the basis loops modulo a Stokes-boundary. -/
  hurewicz : SmoothHurewiczHypothesis symplecticBasis
  /-- Riemann bilinear non-degeneracy: the `2g` period vectors against
  `basis_ω` are ℝ-linearly independent. -/
  bilinear :
    LinearIndependent ℝ
      (fun i : Fin (2 * JacobianChallenge.genus X) =>
        periodVector (PeriodPairingData.ofSmoothCycle X) basis_ω
          (symplecticBasis.cycleGens i))

namespace SmoothHomologyDataPackage

variable
  {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}

/-- **Feed-through to `GenericGenusPeriodLatticeInputs basis_ω`.**
Applies `GenericGenusPeriodLatticeInputs.ofThreeNamedAtomsNoAlpha`,
which dispatches the smooth-path-connectedness atom via
`smoothPathConnected_of_preconnected`. -/
noncomputable def toGenericGenusInputs
    (P : SmoothHomologyDataPackage basis_ω) :
    GenericGenusPeriodLatticeInputs basis_ω :=
  GenericGenusPeriodLatticeInputs.ofThreeNamedAtomsNoAlpha
    basis_ω P.basePoint P.symplecticBasis P.bilinear P.hurewicz

end SmoothHomologyDataPackage

/-- **`Nonempty (GenericGenusPeriodLatticeInputs basis_ω)` from a single
`SmoothHomologyDataPackage`.** -/
theorem nonempty_genericGenusPeriodLatticeInputs_of_smoothHomologyDataPackage
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    (P : SmoothHomologyDataPackage basis_ω) :
    Nonempty (GenericGenusPeriodLatticeInputs basis_ω) :=
  ⟨P.toGenericGenusInputs⟩

/-- **Headline composite: `Nonempty (PeriodLatticeSymplecticBundle ...)`
from a single `SmoothHomologyDataPackage`.**

The single-input form of the period-lattice side at general genus on
any compact connected complex 1-manifold. Compared to
`nonempty_periodLatticeSymplecticBundle_ofThreeNamedAtomsNoAlpha`, the
three separate atomic-hypothesis arguments + base point are folded into
the single structure `SmoothHomologyDataPackage basis_ω`. -/
theorem nonempty_periodLatticeSymplecticBundle_of_smoothHomologyDataPackage
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    (P : SmoothHomologyDataPackage basis_ω) :
    Nonempty
      (PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X)
        basis_ω) :=
  nonempty_periodLatticeSymplecticBundle_ofThreeNamedAtomsNoAlpha
    basis_ω P.basePoint P.symplecticBasis P.bilinear P.hurewicz

/-- **`Nonempty`-to-`Nonempty` lift.** From `Nonempty
(SmoothHomologyDataPackage basis_ω)` we obtain `Nonempty
(PeriodLatticeSymplecticBundle ...)`. -/
theorem nonempty_periodLatticeSymplecticBundle_of_nonempty_smoothHomologyDataPackage
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    (h : Nonempty (SmoothHomologyDataPackage basis_ω)) :
    Nonempty
      (PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X)
        basis_ω) :=
  h.elim nonempty_periodLatticeSymplecticBundle_of_smoothHomologyDataPackage

end JacobianChallenge

end
