/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathConnectedRiemannSphere
import JacobianChallenge.Manifold.SmoothPathConnectedSymp

set_option linter.unusedSectionVars false

/-! # `AbelJacobiInputSymp` existence on `RiemannSphere`

Symplectic parallel of `Manifold/SmoothPathConnectedRiemannSphere.lean`'s
`nonempty_abelJacobiInput_RiemannSphere`. Combines
`smoothPathConnected_RiemannSphere` (unconditional path-connectedness
on RS) with `AbelJacobiInputSymp.nonempty_of_smoothPathConnected` to
produce the existence of an `AbelJacobiInputSymp α h` bundle on RS,
unconditional, for any basis `α` and symplectic discreteness bundle `h`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

/-- **Unconditional existence of `AbelJacobiInputSymp` on
`RiemannSphere`.** Symplectic parallel of
`nonempty_abelJacobiInput_RiemannSphere`. -/
theorem nonempty_abelJacobiInputSymp_RiemannSphere
    (α : Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
      (HolomorphicOneForm RiemannSphere))
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle RiemannSphere) α) :
    Nonempty (AbelJacobiInputSymp (X := RiemannSphere) (α := α) (h := h)) :=
  AbelJacobiInputSymp.nonempty_of_smoothPathConnected
    smoothPathConnected_RiemannSphere

end JacobianChallenge

end
