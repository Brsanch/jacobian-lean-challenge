/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HodgeRiemannBridgeGenusTwoScalar
import JacobianChallenge.Manifold.HodgeRiemannBridge

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Bridge identity at `genus X = 2` from 3 scalar identities

Lifts `iPeriodMatrixForm_standardSymplectic_two_eq_of_three_scalars`
(literal Fin 4 / Fin 2 form) to the abstract `HodgeRiemannBridgeHypothesis`
at `genus X = 2` via `subst h_g` and Subsingleton-like fin
identifications.

At `genus X = 2`, the bridge identity for `J = standardSymplectic g`
reduces to 3 scalar entries at the upper triangle.

## What ships

* `hodgeRiemannBridgeHypothesis_of_genus_two_three_scalars` — the
  matrix bridge from 3 scalar identities at `g = 2`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Bridge identity at `genus X = 2` from 3 scalar identities.** -/
theorem hodgeRiemannBridgeHypothesis_of_genus_two_three_scalars
    (h_g : JacobianChallenge.genus X = 2)
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (H : HermitianOnHolomorphicOneForm X)
    (i₀ i₁ : Fin (JacobianChallenge.genus X))
    (h_i₀ : i₀.val = 0) (h_i₁ : i₁.val = 1)
    (h_00 :
      ((Complex.I : ℂ) •
        ((periodMatrix data basis_ω cycleGens)ᵀ
          * (standardSymplectic (JacobianChallenge.genus X)).map
              ((↑) : ℤ → ℂ)
          * (periodMatrix data basis_ω cycleGens).map star)) i₀ i₀
        = H.toFun (basis_ω i₀) (basis_ω i₀))
    (h_01 :
      ((Complex.I : ℂ) •
        ((periodMatrix data basis_ω cycleGens)ᵀ
          * (standardSymplectic (JacobianChallenge.genus X)).map
              ((↑) : ℤ → ℂ)
          * (periodMatrix data basis_ω cycleGens).map star)) i₀ i₁
        = H.toFun (basis_ω i₀) (basis_ω i₁))
    (h_11 :
      ((Complex.I : ℂ) •
        ((periodMatrix data basis_ω cycleGens)ᵀ
          * (standardSymplectic (JacobianChallenge.genus X)).map
              ((↑) : ℤ → ℂ)
          * (periodMatrix data basis_ω cycleGens).map star)) i₁ i₁
        = H.toFun (basis_ω i₁) (basis_ω i₁)) :
    HodgeRiemannBridgeHypothesis data basis_ω cycleGens
      (standardSymplectic (JacobianChallenge.genus X)) H := by
  unfold HodgeRiemannBridgeHypothesis
  funext i j
  -- At g = 2, Fin (genus X) ≃ Fin 2, but `genus X = 2` is a propositional
  -- equality. We don't have a direct Subsingleton reduction; instead, we
  -- case-split on i.val and j.val (both < genus X = 2).
  have hi_lt : i.val < 2 := by have := i.isLt; omega
  have hj_lt : j.val < 2 := by have := j.isLt; omega
  rcases (by omega : i.val = 0 ∨ i.val = 1) with hi_v | hi_v
  · have h_i_eq : i = i₀ := Fin.ext (hi_v.trans h_i₀.symm)
    rcases (by omega : j.val = 0 ∨ j.val = 1) with hj_v | hj_v
    · -- (i, j) = (i₀, i₀)
      have h_j_eq : j = i₀ := Fin.ext (hj_v.trans h_i₀.symm)
      rw [h_i_eq, h_j_eq, HermitianOnHolomorphicOneForm.toMatrix_apply]
      exact h_00
    · -- (i, j) = (i₀, i₁)
      have h_j_eq : j = i₁ := Fin.ext (hj_v.trans h_i₁.symm)
      rw [h_i_eq, h_j_eq, HermitianOnHolomorphicOneForm.toMatrix_apply]
      exact h_01
  · have h_i_eq : i = i₁ := Fin.ext (hi_v.trans h_i₁.symm)
    rcases (by omega : j.val = 0 ∨ j.val = 1) with hj_v | hj_v
    · -- (i, j) = (i₁, i₀): use Hermitian symmetry of both sides.
      have h_j_eq : j = i₀ := Fin.ext (hj_v.trans h_i₀.symm)
      rw [h_i_eq, h_j_eq]
      -- LHS is Hermitian, so LHS_{i₁, i₀} = star(LHS_{i₀, i₁}).
      have h_LHS_herm :
          ((Complex.I : ℂ) •
            ((periodMatrix data basis_ω cycleGens)ᵀ
              * (standardSymplectic (JacobianChallenge.genus X)).map
                  ((↑) : ℤ → ℂ)
              * (periodMatrix data basis_ω cycleGens).map star)).IsHermitian :=
        iPeriodMatrixForm_isHermitian (periodMatrix data basis_ω cycleGens)
          (standardSymplectic (JacobianChallenge.genus X))
          (standardSymplectic_antisymm (JacobianChallenge.genus X))
      have h_swap_LHS :
          ((Complex.I : ℂ) • ((periodMatrix data basis_ω cycleGens)ᵀ
            * (standardSymplectic (JacobianChallenge.genus X)).map
                ((↑) : ℤ → ℂ)
            * (periodMatrix data basis_ω cycleGens).map star)) i₁ i₀
          = star (((Complex.I : ℂ) • ((periodMatrix data basis_ω cycleGens)ᵀ
              * (standardSymplectic (JacobianChallenge.genus X)).map
                  ((↑) : ℤ → ℂ)
              * (periodMatrix data basis_ω cycleGens).map star)) i₀ i₁) := by
        have h := Matrix.IsHermitian.apply h_LHS_herm i₀ i₁
        -- h : star (M i₁ i₀) = M i₀ i₁
        rw [← h, star_star]
      rw [h_swap_LHS, h_01, H.toMatrix_apply, ← H.conjSymm]
    · -- (i, j) = (i₁, i₁)
      have h_j_eq : j = i₁ := Fin.ext (hj_v.trans h_i₁.symm)
      rw [h_i_eq, h_j_eq, HermitianOnHolomorphicOneForm.toMatrix_apply]
      exact h_11

end JacobianChallenge

end
