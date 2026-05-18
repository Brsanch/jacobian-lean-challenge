/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathLocalConvex
import JacobianChallenge.Manifold.SmoothPathConnected
import JacobianChallenge.Manifold.AbelJacobiPointSymp

set_option linter.unusedSectionVars false

/-! # `AbelJacobiInputSymp` existence from smooth-path-connectedness

Symplectic parallel of `Manifold/SmoothPathConnected.lean`'s
`AbelJacobiInput.ofSmoothPathConnected` / `nonempty_of_smoothPathConnected`
+ `Manifold/AbelJacobiInputFromConnected.lean`'s
`nonempty_of_preconnected` / `nonempty_of_connected`.

Same constructor (`Classical.choose` of `hSPC P₀ Q`), just typed
against `AbelJacobiInputSymp α h_symp` instead of `AbelJacobiInput α h_legacy`.

## What ships

* `AbelJacobiInputSymp.ofSmoothPathConnected` — concrete constructor.
* `AbelJacobiInputSymp.nonempty_of_smoothPathConnected`.
* `AbelJacobiInputSymp.nonempty_of_preconnected` — for preconnected
  complex 1-manifolds.
* `AbelJacobiInputSymp.nonempty_of_connected` — for connected
  complex 1-manifolds (typeclass-friendly form).

No `sorry`, no `axiom`. -/

noncomputable section

open Module
open scoped Manifold ContDiff

namespace JacobianChallenge

namespace AbelJacobiInputSymp

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) α}

/-- **Concrete constructor from smooth-path-connectedness + a base point
(symplectic).** Mirror of `AbelJacobiInput.ofSmoothPathConnected`. -/
noncomputable def ofSmoothPathConnected
    (hSPC : SmoothPathConnected 𝓘(ℝ, ℂ) X) (P₀ : X) :
    AbelJacobiInputSymp α h where
  basePoint := P₀
  pathFromBase := fun Q => Classical.choose (hSPC P₀ Q)
  src_eq := fun Q => (Classical.choose_spec (hSPC P₀ Q)).1
  tgt_eq := fun Q => (Classical.choose_spec (hSPC P₀ Q)).2

/-- **Existence from smooth-path-connectedness (symplectic).** Mirror of
`AbelJacobiInput.nonempty_of_smoothPathConnected`. -/
theorem nonempty_of_smoothPathConnected
    [Nonempty X] (hSPC : SmoothPathConnected 𝓘(ℝ, ℂ) X) :
    Nonempty (AbelJacobiInputSymp α h) :=
  ⟨ofSmoothPathConnected hSPC (Classical.arbitrary X)⟩

/-- **Unconditional `AbelJacobiInputSymp` on any preconnected complex
1-manifold (symplectic).** Mirror of
`AbelJacobiInput.nonempty_of_preconnected`. -/
theorem nonempty_of_preconnected
    [PreconnectedSpace X] [Nonempty X]
    (α : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle X) α) :
    Nonempty (AbelJacobiInputSymp (X := X) (α := α) (h := h)) :=
  nonempty_of_smoothPathConnected
    (h := h) smoothPathConnected_of_preconnected

/-- **Variant for `[ConnectedSpace X]` (symplectic).** Mirror of
`AbelJacobiInput.nonempty_of_connected`. -/
theorem nonempty_of_connected
    [ConnectedSpace X]
    (α : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle X) α) :
    Nonempty (AbelJacobiInputSymp (X := X) (α := α) (h := h)) :=
  nonempty_of_preconnected α h

end AbelJacobiInputSymp

end JacobianChallenge

end
