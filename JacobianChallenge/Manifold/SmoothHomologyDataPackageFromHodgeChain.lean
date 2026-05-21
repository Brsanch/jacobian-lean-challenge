/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothHomologyDataPackage
import JacobianChallenge.Manifold.BilinearFromHodgeChain

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # `SmoothHomologyDataPackage` constructor from the Hodge–Riemann chain
(chip 4)

This file wires chip 3's `realLI_periodVector_of_completeHodgeRiemann`
into the `SmoothHomologyDataPackage` structure. The `bilinear` field of
`SmoothHomologyDataPackage` (= ℝ-linear independence of period
vectors) is discharged from a `CompleteHodgeRiemannHypothesis`
(bundled `(J, H, PD, first relation, bridge identity)`).

Net structural reduction: the period-lattice side of items
5/11/12/13/17/18/21 reduces (via `SmoothHomologyDataPackage` and the
typeclass wrappers) to **three** named classical inputs at general
genus on a compact connected complex 1-manifold:

* `SmoothSymplecticBasis` — data of 2g based loops at `basePoint`
  (surface classification);
* `SmoothHurewiczHypothesis` — every smooth based loop is a
  ℤ-combination of the basis loops modulo Stokes-boundary;
* `CompleteHodgeRiemannHypothesis` — `(J, H, PD, first, bridge)`.

All three are well-established classical theorems in topology and
Hodge theory.

## What this file ships

* `SmoothHomologyDataPackage.ofHodgeChain` — direct constructor.
* `nonempty_smoothHomologyDataPackage_of_hodgeChain` — `Nonempty`
  corollary.
* `nonempty_periodLatticeSymplecticBundle_of_hodgeChain` — full headline
  composite producing `Nonempty (PeriodLatticeSymplecticBundle ...)`
  from the three named hypotheses.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`SmoothHomologyDataPackage.ofHodgeChain`** — construct a
`SmoothHomologyDataPackage basis_ω` from (basePoint, symplecticBasis,
hurewicz) data + a `CompleteHodgeRiemannHypothesis`. The `bilinear`
field is discharged from the Hodge chain via chip 3. -/
noncomputable def SmoothHomologyDataPackage.ofHodgeChain
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    (basePoint : X)
    (symplecticBasis :
      SmoothSymplecticBasis 𝓘(ℝ, ℂ) X basePoint (JacobianChallenge.genus X))
    (hurewicz : SmoothHurewiczHypothesis symplecticBasis)
    (hHR : CompleteHodgeRiemannHypothesis
      (PeriodPairingData.ofSmoothCycle X) basis_ω symplecticBasis.cycleGens) :
    SmoothHomologyDataPackage basis_ω where
  basePoint := basePoint
  symplecticBasis := symplecticBasis
  hurewicz := hurewicz
  bilinear := realLI_periodVector_of_completeHodgeRiemann hHR

/-- **`Nonempty` corollary.** From `Nonempty` witnesses of all three
named classical hypotheses, obtain `Nonempty (SmoothHomologyDataPackage
basis_ω)`. -/
theorem nonempty_smoothHomologyDataPackage_of_hodgeChain
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    (basePoint : X)
    (symplecticBasis :
      SmoothSymplecticBasis 𝓘(ℝ, ℂ) X basePoint (JacobianChallenge.genus X))
    (hurewicz : SmoothHurewiczHypothesis symplecticBasis)
    (hHR : CompleteHodgeRiemannHypothesis
      (PeriodPairingData.ofSmoothCycle X) basis_ω symplecticBasis.cycleGens) :
    Nonempty (SmoothHomologyDataPackage basis_ω) :=
  ⟨SmoothHomologyDataPackage.ofHodgeChain basePoint symplecticBasis
    hurewicz hHR⟩

/-- **Full headline composite.** From the three named classical
hypotheses, conclude `Nonempty (PeriodLatticeSymplecticBundle ...)` —
the period-lattice side of items 5/11/12/13/17/18/21. -/
theorem nonempty_periodLatticeSymplecticBundle_of_hodgeChain
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    (basePoint : X)
    (symplecticBasis :
      SmoothSymplecticBasis 𝓘(ℝ, ℂ) X basePoint (JacobianChallenge.genus X))
    (hurewicz : SmoothHurewiczHypothesis symplecticBasis)
    (hHR : CompleteHodgeRiemannHypothesis
      (PeriodPairingData.ofSmoothCycle X) basis_ω symplecticBasis.cycleGens) :
    Nonempty
      (PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X)
        basis_ω) :=
  nonempty_periodLatticeSymplecticBundle_of_smoothHomologyDataPackage
    (SmoothHomologyDataPackage.ofHodgeChain basePoint symplecticBasis
      hurewicz hHR)

end JacobianChallenge

end
