/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodLatticeDiscretenessFromBilinear
import JacobianChallenge.Manifold.PeriodLatticeOfRankTwoG_Wiring
import JacobianChallenge.Manifold.PeriodLatticeOfRankTwoG_ComplexWiring
import Mathlib.LinearAlgebra.Basis.Defs

set_option diagnostics.threshold 100

/-! # Bundle-level discharge: `PeriodLatticeDiscretenessBundle` to all
`JacobianOfLattice` instances

Composes the two existing bridges:

* `PeriodLatticeAnalyticHypotheses.ofBundle` (PL-3-fin chip 1, just
  landed in `PeriodLatticeDiscretenessFromBilinear.lean`) — takes a
  `PeriodLatticeDiscretenessBundle` and produces the 4-field
  `PeriodLatticeAnalyticHypotheses`.

* `PeriodLatticeOfRankTwoG.ofPeriodPairing` + `_compactSpace` +
  `_chartedSpace` (existing) — take a `PeriodLatticeAnalyticHypotheses`
  and produce a `PeriodLatticeOfRankTwoG` term plus the
  `CompactSpace` / `ChartedSpace` discharges on the resulting
  `JacobianOfLattice X data`.

The result is a **single-input form**: given just a
`PeriodLatticeDiscretenessBundle`, downstream callers get the entire
analytic-Jacobian instance stack
(`AddCommGroup`, `TopologicalSpace`, `T2Space`, `CompactSpace`,
`ChartedSpace`, `IsManifold`, `LieAddGroup`) on
`JacobianOfLattice X (PeriodLatticeOfRankTwoG.ofBundle ...)`.

Strategic position: this chip is the **last step before rewiring
`Jacobian X = Pic0 X`** (in `Basic.lean`) to use `JacobianOfLattice`.
Once the H₁ basis (PL-3-fin-2) and period basis (PL-3-fin-3) are
discharged unconditionally, `Jacobian X := JacobianOfLattice X
(PeriodLatticeOfRankTwoG.ofBundle ...)` becomes a definitionally
honest construction, flipping items 4, 5, 10, 11, 12, 13 of OPEN.md
simultaneously.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff
open Submodule Module

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- **Bundle-form constructor for `PeriodLatticeOfRankTwoG`.** From
just a `PeriodLatticeDiscretenessBundle`, build the full
`PeriodLatticeOfRankTwoG X` term. Composes
`PeriodLatticeAnalyticHypotheses.ofBundle` with
`PeriodLatticeOfRankTwoG.ofPeriodPairing`. -/
noncomputable def PeriodLatticeOfRankTwoG.ofBundle
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeDiscretenessBundle data α) :
    PeriodLatticeOfRankTwoG X :=
  PeriodLatticeOfRankTwoG.ofPeriodPairing data α
    (PeriodLatticeAnalyticHypotheses.ofBundle h)

@[simp] lemma PeriodLatticeOfRankTwoG.ofBundle_lattice
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeDiscretenessBundle data α) :
    (PeriodLatticeOfRankTwoG.ofBundle data α h).lattice
      = periodLatticeImage data α := rfl

/-! ## Bundle-level instance discharges -/

/-- **Bundle-form item-11 discharge** (`CompactSpace
(JacobianOfLattice X (PeriodLatticeOfRankTwoG.ofBundle ...))`).
Composes `ofBundle` with the existing `ofPeriodPairing_compactSpace`. -/
theorem PeriodLatticeOfRankTwoG.ofBundle_compactSpace
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeDiscretenessBundle data α) :
    haveI := periodLatticeImage_discreteTopology_of_bundle h
    haveI := periodLatticeImage_isZLattice_of_bundle h
    JacobianOfLattice.CompactSpaceHypothesis
      (PeriodLatticeOfRankTwoG.ofBundle data α h) :=
  PeriodLatticeOfRankTwoG.ofPeriodPairing_compactSpace data α
    (PeriodLatticeAnalyticHypotheses.ofBundle h)

/-- **Bundle-form items 5 + 12 discharge** (`ChartedSpace` +
`IsManifold` on `JacobianOfLattice`). Composes `ofBundle` with the
existing `ofPeriodPairing_chartedSpace`. -/
noncomputable def PeriodLatticeOfRankTwoG.ofBundle_chartedSpace
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeDiscretenessBundle data α) :
    haveI := periodLatticeImage_discreteTopology_of_bundle h
    haveI := periodLatticeImage_isZLattice_of_bundle h
    JacobianOfLattice.ChartedSpaceHypothesis
      (PeriodLatticeOfRankTwoG.ofBundle data α h) :=
  PeriodLatticeOfRankTwoG.ofPeriodPairing_chartedSpace data α
    (PeriodLatticeAnalyticHypotheses.ofBundle h)

/-! ## Convenience: explicit `Type` access to the analytic Jacobian -/

/-- The **honest analytic Jacobian from a discreteness bundle**, as a
`Type`. -/
abbrev AnalyticJacobian
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeDiscretenessBundle data α) : Type :=
  JacobianOfLattice X (PeriodLatticeOfRankTwoG.ofBundle data α h)

end JacobianChallenge

end
