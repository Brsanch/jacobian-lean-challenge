/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HodgeRiemannBridge
import JacobianChallenge.Manifold.HodgeFormMatrix

set_option linter.unusedSectionVars false

/-! # Uniqueness of the Hodge form satisfying the bridge identity

Given a fixed `data, basis_ω, cycleGens, J`, the bridge identity
`i · pmᵀ · J · pm.map star = H.toMatrix basis_ω` uniquely determines
the matrix `H.toMatrix basis_ω`. Hence **any two Hermitian forms `H₁,
H₂` satisfying the bridge identity (for the same `data, basis_ω,
cycleGens, J`) agree on basis pairs**.

(They may still differ on non-basis arguments only if they aren't
fully sesquilinear; but `HermitianOnHolomorphicOneForm`'s
sesquilinearity fields force agreement everywhere modulo the basis.)

## What ships

* `hodgeRiemannBridgeHypothesis_toMatrix_unique` — two bridge-satisfying
  Hermitian forms have equal `.toMatrix basis_ω` matrices.
* `hodgeRiemannBridgeHypothesis_basis_unique` — agreement on basis pairs.

## Significance

A structural uniqueness statement: the bridge identity at `J = J_std`
EXACTLY pins down the matrix representation of the Hodge form against
the chosen basis. So the Petersson form vs `canonicalHodgeFormFromAntiSymm`
must agree on basis pairs whenever both satisfy the bridge.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Uniqueness of the bridge-satisfying matrix.** Two Hermitian forms
satisfying the bridge identity (for the same data + basis + cycleGens
+ J) have equal `.toMatrix basis_ω` representations. -/
theorem hodgeRiemannBridgeHypothesis_toMatrix_unique
    {data : PeriodPairingData X}
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    {cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1}
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    {H₁ H₂ : HermitianOnHolomorphicOneForm X}
    (h₁ : HodgeRiemannBridgeHypothesis data basis_ω cycleGens J H₁)
    (h₂ : HodgeRiemannBridgeHypothesis data basis_ω cycleGens J H₂) :
    H₁.toMatrix basis_ω = H₂.toMatrix basis_ω := by
  unfold HodgeRiemannBridgeHypothesis at h₁ h₂
  -- Both H₁.toMatrix and H₂.toMatrix equal the same matrix.
  rw [← h₁, ← h₂]

/-- **Agreement on basis pairs.** Two bridge-satisfying Hermitian
forms produce the same value on every pair `(basis_ω i, basis_ω j)`. -/
theorem hodgeRiemannBridgeHypothesis_basis_unique
    {data : PeriodPairingData X}
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    {cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1}
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    {H₁ H₂ : HermitianOnHolomorphicOneForm X}
    (h₁ : HodgeRiemannBridgeHypothesis data basis_ω cycleGens J H₁)
    (h₂ : HodgeRiemannBridgeHypothesis data basis_ω cycleGens J H₂)
    (i j : Fin (JacobianChallenge.genus X)) :
    H₁.toFun (basis_ω i) (basis_ω j) = H₂.toFun (basis_ω i) (basis_ω j) := by
  have h_mat := hodgeRiemannBridgeHypothesis_toMatrix_unique h₁ h₂
  have h_entry := congrFun (congrFun h_mat i) j
  rw [HermitianOnHolomorphicOneForm.toMatrix_apply,
      HermitianOnHolomorphicOneForm.toMatrix_apply] at h_entry
  exact h_entry

end JacobianChallenge

end
