/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasPic0AnalyticEquiv
import JacobianChallenge.Manifold.SmoothHomologyDataPackageClass
import JacobianChallenge.Manifold.SmoothHomologyDataPackageSubsingleton
import JacobianChallenge.Manifold.DefaultHolomorphicOneFormBasis
import JacobianChallenge.Manifold.CanonicalAnalyticJacobianSubsingleton
import JacobianChallenge.Manifold.BasedSmoothLoopsBound

set_option linter.unusedSectionVars false

/-! # Direct `HasPic0AnalyticEquiv X` under `[Subsingleton ω] + [Subsingleton (Pic0 X)]` + BSLB

At genus 0 (`[Subsingleton (HolomorphicOneForm X)]`), both `Pic0 X`
(under `[Subsingleton (Pic0 X)]`) and `CanonicalAnalyticJacobian
basis_ω` are subsingleton, so any AddEquiv between them is automatic.

This gives a direct construction of `HasPic0AnalyticEquiv X` for any X
with the two subsingleton typeclass instances + a BSLB witness.

## What ships

* `hasPic0AnalyticEquiv_of_subsingleton_omega_subsingleton_pic0_BSLB` —
  direct construction.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Direct `HasPic0AnalyticEquiv X` at Subsingleton ω + Subsingleton Pic0 + BSLB.** -/
theorem hasPic0AnalyticEquiv_of_subsingleton_omega_subsingleton_pic0_BSLB
    [Subsingleton (HolomorphicOneForm X)]
    [Subsingleton (Pic0 X)]
    (basePoint : X)
    (h_BSLB : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X basePoint) :
    HasPic0AnalyticEquiv X := by
  -- Build the bundle data.
  set basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X) :=
    defaultHolomorphicOneFormBasis X
  -- SHDP on basis_ω from Subsingleton ω + BSLB.
  haveI : HasSmoothHomologyDataPackage (X := X) basis_ω :=
    { out := ⟨smoothHomologyDataPackage_of_subsingleton_and_BSLB
        basis_ω basePoint h_BSLB⟩ }
  -- CanonicalAnalyticJacobian basis_ω is subsingleton (genus 0).
  haveI : Subsingleton (Fin (JacobianChallenge.genus X) → ℂ) := by
    have h_genus : JacobianChallenge.genus X = 0 :=
      Module.finrank_zero_of_subsingleton (R := ℂ) (M := HolomorphicOneForm X)
    rw [h_genus]; exact Pi.uniqueOfIsEmpty _ |>.instSubsingleton
  haveI : Subsingleton (CanonicalAnalyticJacobian (X := X) basis_ω) :=
    subsingleton_jacobianOfLattice_of_subsingleton_ambient
      (canonicalPeriodLatticeOfRankTwoG basis_ω)
  -- Any AddEquiv between two subsingleton AddCommGroups exists.
  have h_equiv : Pic0 X ≃+ CanonicalAnalyticJacobian (X := X) basis_ω :=
    { toFun := fun _ => (0 : CanonicalAnalyticJacobian (X := X) basis_ω)
      invFun := fun _ => (0 : Pic0 X)
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _
      map_add' := fun _ _ => Subsingleton.elim _ _ }
  exact ⟨⟨basis_ω, inferInstance, h_equiv⟩⟩

end JacobianChallenge

end
