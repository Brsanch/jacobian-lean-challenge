/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HodgeRiemannBridgeUpperTriangular
import JacobianChallenge.Manifold.PeriodSesquilinearForm

set_option linter.unusedSectionVars false

/-! # Bridge identity from upper-triangular sesquilinear pairing identities

Composition of `hodgeRiemannBridgeHypothesis_of_upperTriangular` (the
matrix bridge reduces to upper-triangular entries) with
`periodSesquilinearForm_eq_periodMatrixForm_apply` (the matrix entry
equals the sesquilinear pairing on a basis pair).

Result: at any genus, the bridge identity for `J = standardSymplectic g`
follows from a **finite set of scalar pairing identities**, indexed by
`(i, j)` with `i ≤ j`:

  `I · Q_sq cycleGens (standardSymplectic g) (basis_ω i) (basis_ω j)
   = H(basis_ω i, basis_ω j)`.

At `genus g`, the number of such identities is `g(g + 1)/2`. At `g = 1`
this collapses to one scalar identity (the diagonal), recovering
`hodgeRiemannBridgeHypothesis_of_genus_one_scalar` up to packaging.

## What ships

* `hodgeRiemannBridgeHypothesis_of_sesquilinearUpperTriangular` —
  constructive reduction: bridge ⟸ upper-triangular pairing identities.

## Significance

A user proving the deep Hodge–Riemann bridge identity at general genus
needs only verify `g(g + 1)/2` scalar pairing identities (the upper
triangle), each of which is a single complex equation between a
sesquilinear period pairing and a Hodge inner product value.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Bridge identity from upper-triangular sesquilinear pairing
identities.**

For any genus, the `HodgeRiemannBridgeHypothesis` at `J =
standardSymplectic g` is implied by the upper-triangular family of
scalar pairing identities

  `∀ i ≤ j, I · Q_sq cycleGens (standardSymplectic g) (basis_ω i) (basis_ω j)
   = H(basis_ω i, basis_ω j)`.

Compose `hodgeRiemannBridgeHypothesis_of_upperTriangular` (matrix
bridge ⟸ upper triangular matrix equality) with
`periodSesquilinearForm_eq_periodMatrixForm_apply` (matrix entry ↔
pairing value). -/
theorem hodgeRiemannBridgeHypothesis_of_sesquilinearUpperTriangular
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (H : HermitianOnHolomorphicOneForm X)
    (h_upper :
      ∀ i j : Fin (JacobianChallenge.genus X), i.val ≤ j.val →
        (Complex.I : ℂ) * periodSesquilinearForm cycleGens
          (standardSymplectic (JacobianChallenge.genus X))
          (basis_ω i) (basis_ω j)
          = H.toFun (basis_ω i) (basis_ω j)) :
    HodgeRiemannBridgeHypothesis data basis_ω cycleGens
      (standardSymplectic (JacobianChallenge.genus X)) H := by
  apply hodgeRiemannBridgeHypothesis_of_upperTriangular data basis_ω
    cycleGens H
  intro i j h_le
  -- Translate matrix entry to sesquilinear pairing.
  rw [show ((Complex.I : ℂ) •
        ((periodMatrix data basis_ω cycleGens)ᵀ
          * (standardSymplectic (JacobianChallenge.genus X)).map
              ((↑) : ℤ → ℂ)
          * (periodMatrix data basis_ω cycleGens).map star)) i j
      = (Complex.I : ℂ) * (periodMatrixForm
          (periodMatrix data basis_ω cycleGens)
          (standardSymplectic (JacobianChallenge.genus X))) i j from rfl]
  rw [← periodSesquilinearForm_eq_periodMatrixForm_apply
        (data := data) basis_ω cycleGens
        (standardSymplectic (JacobianChallenge.genus X)) i j]
  rw [HermitianOnHolomorphicOneForm.toMatrix_apply]
  exact h_upper i j h_le

end JacobianChallenge

end
