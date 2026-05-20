/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HodgeInnerProductHypothesis
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option linter.unusedSectionVars false

/-! # `HodgeFormMatrix`: matrix representation of the Hodge inner product

Given a basis `basis_ω : Basis (Fin g) ℂ (HolomorphicOneForm X)` and a
`HermitianOnHolomorphicOneForm X`, the **`HodgeFormMatrix`** is the
`g × g` complex matrix `H_ij = H(basis_ω i, basis_ω j)`.

This is the matrix-level realisation of the abstract Hermitian form;
the abstract form's positive-definiteness translates into matrix
positive-definiteness in the mathlib `Matrix.PosDef` sense (up to the
appropriate conjugation conventions).

This file is intermediate plumbing between the abstract
`HodgeInnerProductHypothesis` and the concrete matrix calculations
needed for Riemann's bilinear relations on the period matrix.

## What this file ships

* `HermitianOnHolomorphicOneForm.toMatrix basis_ω` — the `g × g`
  Hermitian matrix associated to a Hermitian form against a basis.
* `HermitianOnHolomorphicOneForm.toMatrix_conjTranspose` — the matrix
  is conjugate-symmetric (Hermitian in the matrix sense).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Matrix

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace HermitianOnHolomorphicOneForm

/-- **Matrix representation of a Hermitian form against a basis.** The
`g × g` complex matrix `H_ij = H(basis i, basis j)`.

This is the bridge between the abstract Hermitian form on
`HolomorphicOneForm X` and the matrix infrastructure of mathlib's
`Matrix.PosDef`. -/
noncomputable def toMatrix
    (H : HermitianOnHolomorphicOneForm X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)) :
    Matrix (Fin (JacobianChallenge.genus X))
      (Fin (JacobianChallenge.genus X)) ℂ :=
  fun i j => H.toFun (basis_ω i) (basis_ω j)

@[simp] lemma toMatrix_apply
    (H : HermitianOnHolomorphicOneForm X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (i j : Fin (JacobianChallenge.genus X)) :
    H.toMatrix basis_ω i j = H.toFun (basis_ω i) (basis_ω j) := rfl

/-- **The matrix representation is conjugate-symmetric.** Direct from
the `conjSymm` field of `HermitianOnHolomorphicOneForm`. -/
theorem toMatrix_conjTranspose
    (H : HermitianOnHolomorphicOneForm X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)) :
    (H.toMatrix basis_ω)ᴴ = H.toMatrix basis_ω := by
  funext i j
  -- LHS via `conjTranspose`: `star (H.toMatrix basis_ω j i)`.
  -- RHS: `H.toMatrix basis_ω i j = H.toFun (basis_ω i) (basis_ω j)`.
  -- `conjSymm` gives `H.toFun (basis_ω j) (basis_ω i) = star (H.toFun (basis_ω i) (basis_ω j))`.
  show star (H.toFun (basis_ω j) (basis_ω i)) = H.toFun (basis_ω i) (basis_ω j)
  rw [H.conjSymm (basis_ω j) (basis_ω i)]
  exact star_star _

/-- **Diagonal entry positivity from `IsPositiveDefinite`.** For each
basis vector, the diagonal entry of the matrix has zero imaginary part
and non-negative real part. -/
theorem toMatrix_diag_re_nonneg_of_isPositiveDefinite
    {H : HermitianOnHolomorphicOneForm X}
    (hH : H.IsPositiveDefinite)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (i : Fin (JacobianChallenge.genus X)) :
    (H.toMatrix basis_ω i i).im = 0 ∧ 0 ≤ (H.toMatrix basis_ω i i).re :=
  hH.1 (basis_ω i)

end HermitianOnHolomorphicOneForm

end JacobianChallenge

end
