/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3PeriodLatticeStokesH1Generation

set_option linter.unusedSectionVars false

/-! # `Nonempty (PeriodLatticeSymplecticBundle ...)` from
`Nonempty (C3PeriodLatticeStokesSpanTopInputs basis)`

A `Nonempty`-style headline that promotes the refactored
classical-input bundle into a sufficient *named hypothesis* for
inhabiting the period-lattice symplectic bundle:

  `[Nonempty (C3PeriodLatticeStokesSpanTopInputs basis)]`
    ⇒ `Nonempty (PeriodLatticeSymplecticBundle
                  (PeriodPairingData.ofSmoothCycle X) basis)`.

The downstream period-lattice consumers (items 5, 11, 12, 13, plus
the full `C3FullInputExtSymp` chain through items 4, 10, 16, 17,
18, 21) all branch off `Nonempty (PeriodLatticeSymplecticBundle ...)`,
so this single Nonempty hypothesis is the cleanest external
boundary for the period-lattice side of the C3 cascade.

## What this file ships

* `Nonempty.periodLatticeSymplecticBundle_of_stokesSpanTop` —
  `Nonempty` projection from the refactored inputs to the bundle.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **From `Nonempty (C3PeriodLatticeStokesSpanTopInputs basis)` to
`Nonempty (PeriodLatticeSymplecticBundle data basis)`.** Promotes the
refactored bundle into a single named hypothesis sufficient for the
downstream period-lattice consumers. -/
theorem Nonempty.periodLatticeSymplecticBundle_of_stokesSpanTop
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    [hN : Nonempty (C3PeriodLatticeStokesSpanTopInputs basis)] :
    Nonempty
      (PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) basis) :=
  hN.map (fun inputs => inputs.toBundle)

end JacobianChallenge

end
