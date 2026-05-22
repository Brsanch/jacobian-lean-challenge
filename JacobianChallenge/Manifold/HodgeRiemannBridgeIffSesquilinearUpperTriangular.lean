/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HodgeRiemannBridgeSesquilinearUpperTriangular
import JacobianChallenge.Manifold.HodgeRiemannBridgeUpperTriangular

set_option linter.unusedSectionVars false

/-! # Bridge identity ⟺ upper-triangular sesquilinear pairing identities

Biconditional packaging: the matrix bridge identity for `J =
standardSymplectic g` IS equivalent to the family of `g(g + 1)/2`
upper-triangular sesquilinear pairing identities. Combines:

* forward — `hodgeRiemannBridgeHypothesis_of_sesquilinearUpperTriangular`
  (upper-tri pairings ⟹ matrix bridge);
* backward — directly extract the (i, j) entry of the matrix bridge,
  identify with the sesquilinear pairing via
  `periodSesquilinearForm_eq_periodMatrixForm_apply` +
  `iPeriodMatrixForm` definitional unfolds.

## What ships

* `hodgeRiemannBridgeHypothesis_iff_sesquilinearUpperTriangular` —
  biconditional.

## Significance

A clean restatement: the open analytic content of
`HodgeRiemannBridgeHypothesis` at `J = standardSymplectic g` is
EXACTLY a finite family of `g(g + 1)/2` scalar pairing identities (no
hidden symmetry, no redundancy). At any genus, verifying the bridge
identity is equivalent to verifying these `g(g + 1)/2` scalar
equations on a basis.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Bridge identity ⟺ upper-triangular sesquilinear pairing identities.** -/
theorem hodgeRiemannBridgeHypothesis_iff_sesquilinearUpperTriangular
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (H : HermitianOnHolomorphicOneForm X) :
    HodgeRiemannBridgeHypothesis data basis_ω cycleGens
        (standardSymplectic (JacobianChallenge.genus X)) H ↔
      ∀ i j : Fin (JacobianChallenge.genus X), i.val ≤ j.val →
        (Complex.I : ℂ) * periodSesquilinearForm cycleGens
          (standardSymplectic (JacobianChallenge.genus X))
          (basis_ω i) (basis_ω j)
          = H.toFun (basis_ω i) (basis_ω j) := by
  refine ⟨fun h_bridge i j _hij => ?_,
          hodgeRiemannBridgeHypothesis_of_sesquilinearUpperTriangular
            data basis_ω cycleGens H⟩
  -- Forward: from full matrix bridge, extract (i, j) entry as pairing.
  have h_entry := congrFun (congrFun h_bridge i) j
  rw [show ((Complex.I : ℂ) •
        ((periodMatrix data basis_ω cycleGens)ᵀ
          * (standardSymplectic (JacobianChallenge.genus X)).map
              ((↑) : ℤ → ℂ)
          * (periodMatrix data basis_ω cycleGens).map star)) i j
      = (Complex.I : ℂ) * (periodMatrixForm
          (periodMatrix data basis_ω cycleGens)
          (standardSymplectic (JacobianChallenge.genus X))) i j from rfl] at h_entry
  rw [← periodSesquilinearForm_eq_periodMatrixForm_apply
        (data := data) basis_ω cycleGens
        (standardSymplectic (JacobianChallenge.genus X)) i j] at h_entry
  rw [HermitianOnHolomorphicOneForm.toMatrix_apply] at h_entry
  exact h_entry

end JacobianChallenge

end
