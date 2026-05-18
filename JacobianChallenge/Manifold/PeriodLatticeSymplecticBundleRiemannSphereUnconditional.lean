/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3PeriodLatticeStokesRiemannSphereUnconditional

set_option linter.unusedSectionVars false

/-! # `PeriodLatticeSymplecticBundle` on `RiemannSphere`, unconditional

Builds on `C3PeriodLatticeStokesSpanTopInputs_RiemannSphere_unconditional`
(canonical-bundle inputs on RS, unconditional after
`stokesBoundaries_RS_eq_top` + `genus_RiemannSphere_eq_zero`) by
extracting `.toBundle`. Result: a
`PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle RS) basis`
that requires no classical-input hypothesis.

## What this file ships

* `periodLatticeSymplecticBundle_RiemannSphere_unconditional`
* `nonempty_periodLatticeSymplecticBundle_RiemannSphere`

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

namespace RiemannSphere

/-- **Unconditional `PeriodLatticeSymplecticBundle` on `RiemannSphere`.**
Extracts `.toBundle` from
`C3PeriodLatticeStokesSpanTopInputs_RiemannSphere_unconditional`. -/
noncomputable def periodLatticeSymplecticBundle_RiemannSphere_unconditional
    (basis :
      Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
        (HolomorphicOneForm RiemannSphere)) :
    PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle RiemannSphere) basis :=
  (C3PeriodLatticeStokesSpanTopInputs_RiemannSphere_unconditional basis).toBundle

/-- **Nonempty version.** -/
theorem nonempty_periodLatticeSymplecticBundle_RiemannSphere
    (basis :
      Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
        (HolomorphicOneForm RiemannSphere)) :
    Nonempty
      (PeriodLatticeSymplecticBundle
        (PeriodPairingData.ofSmoothCycle RiemannSphere) basis) :=
  ⟨periodLatticeSymplecticBundle_RiemannSphere_unconditional basis⟩

end RiemannSphere

end JacobianChallenge

end
