/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HodgeRiemannBridgeGenusTwo
import JacobianChallenge.Manifold.PeriodMatrixFormStandardSymplecticDiagonalGenusTwo

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Bridge identity at `g = 2` from real-part scalar equations at the diagonal

At `genus X = 2`, the diagonal entries (0, 0) and (1, 1) of `i •
periodMatrixForm pm (standardSymplectic 2)` are real numbers (chip
`_diagonal_im`). Similarly, the diagonal entries of `H.toMatrix
basis_ω` are real (Hermitian diagonal). So the diagonal equations of
the bridge identity reduce to **two real-valued equations**, one for
each diagonal index, plus a complex equation at the (0, 1) entry.

## What ships

* `hodgeRiemannBridgeHypothesis_of_genus_two_real_diagonal` — given:
  * `genus X = 2`;
  * real-valued equations for the diagonals (`.re` form);
  * a complex equation for the (0, 1) entry;

  the bridge identity holds.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Bridge identity at `genus X = 2` from real-part scalar
identities on the diagonal + one complex off-diagonal identity.** -/
theorem hodgeRiemannBridgeHypothesis_of_genus_two_real_diagonal
    (h_g : JacobianChallenge.genus X = 2)
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (H : HermitianOnHolomorphicOneForm X)
    (i₀ i₁ : Fin (JacobianChallenge.genus X))
    (k₀ k₁ k₂ k₃ : Fin (2 * JacobianChallenge.genus X))
    (h_i₀ : i₀.val = 0) (h_i₁ : i₁.val = 1)
    (h_k₀ : k₀.val = 0) (h_k₁ : k₁.val = 1)
    (h_k₂ : k₂.val = 2) (h_k₃ : k₃.val = 3)
    (h_diag_00_re :
      (H.toFun (basis_ω i₀) (basis_ω i₀)).re
        = 2 * ((star (periodMatrix data basis_ω cycleGens k₀ i₀)
                  * periodMatrix data basis_ω cycleGens k₂ i₀).im
              + (star (periodMatrix data basis_ω cycleGens k₁ i₀)
                  * periodMatrix data basis_ω cycleGens k₃ i₀).im))
    (h_diag_00_im :
      (H.toFun (basis_ω i₀) (basis_ω i₀)).im = 0)
    (h_diag_11_re :
      (H.toFun (basis_ω i₁) (basis_ω i₁)).re
        = 2 * ((star (periodMatrix data basis_ω cycleGens k₀ i₁)
                  * periodMatrix data basis_ω cycleGens k₂ i₁).im
              + (star (periodMatrix data basis_ω cycleGens k₁ i₁)
                  * periodMatrix data basis_ω cycleGens k₃ i₁).im))
    (h_diag_11_im :
      (H.toFun (basis_ω i₁) (basis_ω i₁)).im = 0)
    (h_offdiag_01 :
      ((Complex.I : ℂ) •
        ((periodMatrix data basis_ω cycleGens)ᵀ
          * (standardSymplectic (JacobianChallenge.genus X)).map
              ((↑) : ℤ → ℂ)
          * (periodMatrix data basis_ω cycleGens).map star)) i₀ i₁
        = H.toFun (basis_ω i₀) (basis_ω i₁)) :
    HodgeRiemannBridgeHypothesis data basis_ω cycleGens
      (standardSymplectic (JacobianChallenge.genus X)) H := by
  apply hodgeRiemannBridgeHypothesis_of_genus_two_three_scalars
    h_g data basis_ω cycleGens H i₀ i₁ h_i₀ h_i₁
  · -- (0, 0) diagonal: reconstruct from .re and .im.
    show ((Complex.I : ℂ) • periodMatrixForm
          (periodMatrix data basis_ω cycleGens)
          (standardSymplectic (JacobianChallenge.genus X))) i₀ i₀
        = H.toFun (basis_ω i₀) (basis_ω i₀)
    rw [iPeriodMatrixForm_standardSymplectic_diagonal_genus_two h_g
        (periodMatrix data basis_ω cycleGens) i₀ k₀ k₁ k₂ k₃
        h_k₀ h_k₁ h_k₂ h_k₃]
    apply Complex.ext
    · simp only [Complex.ofReal_re]
      exact h_diag_00_re.symm
    · simp only [Complex.ofReal_im]
      exact h_diag_00_im.symm
  · exact h_offdiag_01
  · -- (1, 1) diagonal.
    show ((Complex.I : ℂ) • periodMatrixForm
          (periodMatrix data basis_ω cycleGens)
          (standardSymplectic (JacobianChallenge.genus X))) i₁ i₁
        = H.toFun (basis_ω i₁) (basis_ω i₁)
    rw [iPeriodMatrixForm_standardSymplectic_diagonal_genus_two h_g
        (periodMatrix data basis_ω cycleGens) i₁ k₀ k₁ k₂ k₃
        h_k₀ h_k₁ h_k₂ h_k₃]
    apply Complex.ext
    · simp only [Complex.ofReal_re]
      exact h_diag_11_re.symm
    · simp only [Complex.ofReal_im]
      exact h_diag_11_im.symm

end JacobianChallenge

end
