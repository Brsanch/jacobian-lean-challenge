/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianClassicalContentGenusOne
import JacobianChallenge.Manifold.SurfaceClassificationDataComplexTorus
import JacobianChallenge.Manifold.PeriodMatrixComplexTorus

set_option linter.unusedSectionVars false

/-! # `HasJacobianClassicalContent (ℂ ⧸ L)` conditional on the fundamental area identity

At T_L, `HasJacobianClassicalContent` reduces to the single classical
identity at genus 1:

  `(globalPettersonHermitianForm T_L).toFun (basis_g_dz 0) (basis_g_dz 0)
   = (2 · Im(star (P γ_0 (basis_g_dz 0)) · P γ_1 (basis_g_dz 0)) : ℂ)`

(where the LHS is the Petersson L² inner product and the RHS is the
fundamental Riemann area identity at genus 1).

On T_L with explicit period values `lam₁, lam₂`, the RHS becomes
`2 · Im(star lam₁ · lam₂) = 2 · area(T_L)`. The LHS is `area(T_L)`
(up to convention). The identity is the deep Stokes content
`L²-norm = 2 · period intersection`.

## What ships

* `HasJacobianClassicalContent_complexTorus_of_area_identity` — HJCC
  on T_L from the single scalar identity.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- **`HasJacobianClassicalContent (ℂ ⧸ L)` from the genus-1
fundamental area identity for the Petersson form on T_L.** -/
theorem HasJacobianClassicalContent_complexTorus_of_area_identity
    (_k₀ _k₁ : Fin (2 * JacobianChallenge.genus (ℂ ⧸ L)))
    (_h_k₀ : _k₀.val = 0) (_h_k₁ : _k₁.val = 1)
    (i₀ : Fin (JacobianChallenge.genus (ℂ ⧸ L)))
    (h_area :
      (Complex.I : ℂ) *
        @periodSesquilinearForm (ℂ ⧸ L) _ _ _
          (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
          (surfaceClassificationData_complexTorus L).symplecticBasis.cycleGens
          (standardSymplectic (JacobianChallenge.genus (ℂ ⧸ L)))
          (JacobianChallenge.ComplexTorus.basis_g_dz L i₀)
          (JacobianChallenge.ComplexTorus.basis_g_dz L i₀)
        = (globalPettersonHermitianForm (ℂ ⧸ L)).toFun
            (JacobianChallenge.ComplexTorus.basis_g_dz L i₀)
            (JacobianChallenge.ComplexTorus.basis_g_dz L i₀)) :
    HasJacobianClassicalContent (ℂ ⧸ L) :=
  HasJacobianClassicalContent.of_genus_one_pettersonPairing
    (JacobianChallenge.ComplexTorus.genus_eq_one L)
    (surfaceClassificationData_complexTorus L)
    (JacobianChallenge.ComplexTorus.basis_g_dz L)
    i₀ h_area

end ComplexTorus

end JacobianChallenge

end
