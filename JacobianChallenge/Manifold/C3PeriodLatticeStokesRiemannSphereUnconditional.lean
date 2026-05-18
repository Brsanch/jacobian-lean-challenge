/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3PeriodLatticeStokesCanonicalFromStokesBoundariesTop
import JacobianChallenge.Manifold.StokesBoundariesRiemannSphereTop
import JacobianChallenge.Manifold.HolomorphicOneFormRiemannSphereInstances

set_option linter.unusedSectionVars false

/-! # `C3PeriodLatticeStokesSpanTopInputs` on `RiemannSphere`, fully unconditional

Composes the unconditional inputs:

* `stokesBoundaries_RS_eq_top` — the SmoothCycle-level discharge
  (genus-0 H₁ vanishing) we just proved.
* `Subsingleton (HolomorphicOneForm RiemannSphere)` — the analytic
  side (Riemann sphere has no nonzero holomorphic 1-forms).
* `genus_RiemannSphere : genus RS = 0`.

The output is a `C3PeriodLatticeStokesSpanTopInputs basis` for any
basis of the (zero-dimensional) holomorphic 1-form space on RS,
without any classical-input hypothesis.

## What this file ships

* `C3PeriodLatticeStokesSpanTopInputs.RiemannSphere_unconditional`
* `nonempty_C3PeriodLatticeStokesSpanTopInputs_RiemannSphere`

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

namespace RiemannSphere

/-- **Unconditional canonical-bundle inputs on the Riemann sphere.**
Combines `stokesBoundaries_RS_eq_top` (SmoothCycle-level discharge)
with the analytic input `Subsingleton (HolomorphicOneForm RS)` and
`genus_RiemannSphere`. -/
noncomputable def
    C3PeriodLatticeStokesSpanTopInputs_RiemannSphere_unconditional
    (basis : Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
        (HolomorphicOneForm RiemannSphere)) :
    C3PeriodLatticeStokesSpanTopInputs basis :=
  C3PeriodLatticeStokesSpanTopInputs.trivial_at_genus_zero_canonical_of_stokesBoundaries_top
    stokesBoundaries_RS_eq_top
    basis
    genus_RiemannSphere_eq_zero

/-- **Nonempty version.** Useful for downstream consumers that just
want existence. -/
theorem nonempty_C3PeriodLatticeStokesSpanTopInputs_RiemannSphere
    (basis : Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
        (HolomorphicOneForm RiemannSphere)) :
    Nonempty (C3PeriodLatticeStokesSpanTopInputs basis) :=
  ⟨C3PeriodLatticeStokesSpanTopInputs_RiemannSphere_unconditional basis⟩

end RiemannSphere

end JacobianChallenge

end
