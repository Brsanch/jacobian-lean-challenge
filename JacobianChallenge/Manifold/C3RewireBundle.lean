/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodLatticeFromPairing
import JacobianChallenge.Manifold.PeriodPairingDataFromSmoothCycle
import JacobianChallenge.Manifold.DiskChartCoverFiniteDim
import Mathlib.LinearAlgebra.Basis.Defs

set_option linter.unusedSectionVars false

/-! # C3 rewire stage 1: the named classical input

The C3 rewire of `JacobianChallenge.Jacobian X` from `Pic⁰ X` to the
analytic Jacobian requires:

1. A basis of `HolomorphicOneForm X` (unconditional via item 1).
2. A `PeriodLatticeOfRankTwoG X` term constructed from period-pairing
   data + analytic hypotheses.

The analytic hypotheses (`PeriodLatticeAnalyticHypotheses`) are the
**single classical open input** — Riemann bilinear relations +
`H₁(X; ℤ) ≅ ℤ²ᵍ` discreteness. This file names the existence predicate
and shows how it composes with item 1 to give `PeriodLatticeOfRankTwoG X`.

No `sorry`, no `axiom`.
-/

open Set Module

open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

/-- **The single named classical input for the C3 rewire**: for some
basis of `HolomorphicOneForm X`, the smooth-cycle period-pairing data
has full `PeriodLatticeAnalyticHypotheses`. -/
def C3PeriodLatticeAnalyticInput (X : Type*) [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X] : Prop :=
  ∀ (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ
        (HolomorphicOneForm X)),
    Nonempty (PeriodLatticeAnalyticHypotheses
      (PeriodPairingData.ofSmoothCycle X) basis)

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- From the named classical input + the (unconditional)
`HolomorphicOneFormFiniteDim`, produce a `PeriodLatticeOfRankTwoG X`
term. -/
noncomputable def periodLatticeOfRankTwoG_of_input
    (h : C3PeriodLatticeAnalyticInput X) :
    PeriodLatticeOfRankTwoG X := by
  -- Step 1: use item 1's `HolomorphicOneFormFiniteDim_holds` to get a basis.
  haveI : FiniteDimensional ℂ (HolomorphicOneForm X) :=
    finiteDimensional_of_HolomorphicOneFormFiniteDim
      (DiskChartCover.holomorphicOneFormFiniteDim_holds (X := X))
  -- Pick a basis indexed by `Fin (finrank ℂ (HolomorphicOneForm X))`.
  let b₀ := Module.finBasis ℂ (HolomorphicOneForm X)
  -- This indexes by `Fin (Module.finrank ...)` which equals `Fin (genus X)` by definition.
  let basis : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X) := b₀
  -- Step 2: extract the analytic hypotheses for this basis from the input.
  let analytic : PeriodLatticeAnalyticHypotheses
      (PeriodPairingData.ofSmoothCycle X) basis := Classical.choice (h basis)
  -- Step 3: build the lattice.
  exact PeriodLatticeOfRankTwoG.ofPeriodPairing
    (PeriodPairingData.ofSmoothCycle X) basis analytic

end JacobianChallenge

end
