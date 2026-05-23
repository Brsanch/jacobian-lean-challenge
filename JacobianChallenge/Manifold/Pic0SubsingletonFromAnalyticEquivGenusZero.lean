/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasPic0AnalyticEquiv
import JacobianChallenge.Manifold.CanonicalAnalyticJacobianSubsingleton

set_option linter.unusedSectionVars false

/-! # `Subsingleton (Pic0 X)` from `[HasPic0AnalyticEquiv X]` + `genus = 0`

Under the keystone class `[HasPic0AnalyticEquiv X]` (the Abel-Jacobi
isomorphism `Pic0 X ≃+ CanonicalAnalyticJacobian basis_ω` packaged
as a Prop class), and a proof `genus X = 0`:

* `CanonicalAnalyticJacobian basis_ω` is subsingleton at genus 0
  (quotient of `Fin 0 → ℂ` by `QuotientAddGroup.mk_surjective`).
* The AddEquiv transfers subsingleton to `Pic0 X`.

Combined with the in-tree `JacobianGenusZeroInstancesAuto` chips, this
gives `CompactSpace`, `ChartedSpace`, `IsManifold`, `LieAddGroup` on
`Jacobian X` at any X with `[HasPic0AnalyticEquiv X] + genus X = 0`.

## What ships

* `subsingleton_pic0_of_hasPic0AnalyticEquiv_genus_zero` — the implication.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`Subsingleton (Pic0 X)` from `[HasPic0AnalyticEquiv X]` + `genus X = 0`.**

Composes:
* The Abel-Jacobi AddEquiv `Pic0 X ≃+ CanonicalAnalyticJacobian basis_ω`.
* `Subsingleton (CanonicalAnalyticJacobian basis_ω)` at genus 0 (via
  `canonicalAnalyticJacobian_subsingleton_of_subsingleton_omega`). -/
theorem subsingleton_pic0_of_hasPic0AnalyticEquiv_genus_zero
    [HasPic0AnalyticEquiv X]
    (h_genus : JacobianChallenge.genus X = 0) :
    Subsingleton (Pic0 X) := by
  -- Extract the canonical bundle and AddEquiv.
  let B := canonicalPic0AnalyticEquivBundle X
  letI : HasSmoothHomologyDataPackage (X := X) B.basis_ω := B.shdp
  -- At genus 0, CanonicalAnalyticJacobian basis_ω is subsingleton.
  haveI : Subsingleton (Fin (JacobianChallenge.genus X) → ℂ) := by
    rw [h_genus]; exact Pi.uniqueOfIsEmpty _ |>.instSubsingleton
  haveI : Subsingleton (CanonicalAnalyticJacobian (X := X) B.basis_ω) :=
    subsingleton_jacobianOfLattice_of_subsingleton_ambient
      (canonicalPeriodLatticeOfRankTwoG B.basis_ω)
  -- Transfer along the AddEquiv: Pic0 X ≃+ CanonicalAnalyticJacobian basis_ω
  -- gives Subsingleton (Pic0 X) via Equiv.subsingleton.
  exact Equiv.subsingleton B.equiv.toEquiv

end JacobianChallenge

end
