/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathLocalConvex
import JacobianChallenge.Manifold.SmoothPathConnected
import JacobianChallenge.Manifold.AbelJacobiPoint

set_option linter.unusedSectionVars false

/-! # Unconditional `AbelJacobiInput` existence on a connected complex 1-manifold

Composes the two upstream results

* `smoothPathConnected_of_preconnected` (from
  `Manifold/SmoothPathLocalConvex.lean`): a preconnected complex
  1-manifold is smoothly path-connected.
* `AbelJacobiInput.nonempty_of_smoothPathConnected` (from
  `Manifold/SmoothPathConnected.lean`): a smoothly path-connected
  nonempty space admits an `AbelJacobiInput` bundle.

into a single statement: **on any nonempty preconnected complex
1-manifold, every basis `α` of holomorphic 1-forms and every
discreteness bundle `h` admit an `AbelJacobiInput α h`.** This
closes the C1 input of CLOSURE_MAP §F.3 unconditionally for the
general-`X` case; the analogous statement for `X = RiemannSphere`
lives in `Manifold/SmoothPathConnectedRiemannSphere.lean`.

No `sorry`, no `axiom`. -/

noncomputable section

open Module
open scoped Manifold

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ⊤ X]

/-- **Unconditional `AbelJacobiInput` on any preconnected complex
1-manifold.** Direct composition: preconnected + complex 1-manifold
⇒ smoothly path-connected (`smoothPathConnected_of_preconnected`),
which combined with `Nonempty X` discharges the bundle via
`AbelJacobiInput.nonempty_of_smoothPathConnected`. -/
theorem AbelJacobiInput.nonempty_of_preconnected
    [PreconnectedSpace X] [Nonempty X]
    (α : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeDiscretenessBundle
      (PeriodPairingData.ofSmoothCycle X) α) :
    Nonempty (AbelJacobiInput (X := X) (α := α) (h := h)) :=
  AbelJacobiInput.nonempty_of_smoothPathConnected
    smoothPathConnected_of_preconnected

/-- **Variant for `[ConnectedSpace X]`.** `ConnectedSpace` extends
`PreconnectedSpace + Nonempty`, so the typeclass picture is cleaner
when the user has `[ConnectedSpace X]` in scope. -/
theorem AbelJacobiInput.nonempty_of_connected
    [ConnectedSpace X]
    (α : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeDiscretenessBundle
      (PeriodPairingData.ofSmoothCycle X) α) :
    Nonempty (AbelJacobiInput (X := X) (α := α) (h := h)) :=
  AbelJacobiInput.nonempty_of_preconnected α h

end JacobianChallenge

end
