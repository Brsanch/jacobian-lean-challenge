/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodSesquilinearForm
import JacobianChallenge.Manifold.RiemannBilinearPeriodForm

set_option linter.unusedSectionVars false

/-! # Algebraic properties of `periodSesquilinearForm`

Routine sesquilinearity properties:

* `periodSesquilinearForm_add_left` — additivity in `ω₀`.
* `periodSesquilinearForm_smul_left` — ℂ-linearity in `ω₀`.
* `periodSesquilinearForm_add_right` — additivity in `ω₁`.
* `periodSesquilinearForm_smul_right` — conjugate-linearity in `ω₁`.
* `periodSesquilinearForm_zero_left` / `_zero_right` — zero on zero.
* `periodSesquilinearForm_conj_swap` — conjugate-swap when `Jᵀ = -J`:
  `Q_sq J cycleGens data ω₀ ω₁ = - star (Q_sq J cycleGens data ω₁ ω₀)`.
  (Anti-Hermitian symmetry; multiplied by `I` it becomes Hermitian.)

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace periodSesquilinearForm

variable {data : PeriodPairingData X}
  (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
  (J : Matrix (Fin (2 * JacobianChallenge.genus X))
        (Fin (2 * JacobianChallenge.genus X)) ℤ)

/-- **Additivity in the left argument.** -/
theorem add_left (ω₀ ω₀' ω₁ : HolomorphicOneForm X) :
    periodSesquilinearForm cycleGens J (ω₀ + ω₀') ω₁
      = periodSesquilinearForm cycleGens J ω₀ ω₁
        + periodSesquilinearForm cycleGens J ω₀' ω₁ := by
  unfold periodSesquilinearForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [PeriodPairing_add_right]
  ring

/-- **ℂ-linearity in the left argument.** -/
theorem smul_left (c : ℂ) (ω₀ ω₁ : HolomorphicOneForm X) :
    periodSesquilinearForm cycleGens J (c • ω₀) ω₁
      = c * periodSesquilinearForm cycleGens J ω₀ ω₁ := by
  unfold periodSesquilinearForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [PeriodPairing_smul_right]
  ring

/-- **Additivity in the right argument.** -/
theorem add_right (ω₀ ω₁ ω₁' : HolomorphicOneForm X) :
    periodSesquilinearForm cycleGens J ω₀ (ω₁ + ω₁')
      = periodSesquilinearForm cycleGens J ω₀ ω₁
        + periodSesquilinearForm cycleGens J ω₀ ω₁' := by
  unfold periodSesquilinearForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [PeriodPairing_add_right, star_add]
  ring

/-- **Conjugate-linearity in the right argument.** -/
theorem smul_right (c : ℂ) (ω₀ ω₁ : HolomorphicOneForm X) :
    periodSesquilinearForm cycleGens J ω₀ (c • ω₁)
      = star c * periodSesquilinearForm cycleGens J ω₀ ω₁ := by
  unfold periodSesquilinearForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [PeriodPairing_smul_right]
  rw [show (c • PeriodPairing data (cycleGens l) ω₁
        : ℂ) = c * PeriodPairing data (cycleGens l) ω₁ from rfl]
  rw [show (star (c * PeriodPairing data (cycleGens l) ω₁) : ℂ)
        = star c * star (PeriodPairing data (cycleGens l) ω₁) from by
      rw [StarMul.star_mul]; ring]
  ring

/-- **Zero on the left.** -/
theorem zero_left (ω₁ : HolomorphicOneForm X) :
    periodSesquilinearForm cycleGens J 0 ω₁ = 0 := by
  unfold periodSesquilinearForm
  simp [PeriodPairing_zero_right]

/-- **Zero on the right.** -/
theorem zero_right (ω₀ : HolomorphicOneForm X) :
    periodSesquilinearForm cycleGens J ω₀ 0 = 0 := by
  unfold periodSesquilinearForm
  simp [PeriodPairing_zero_right]

/-- **Anti-Hermitian symmetry: when `Jᵀ = -J`,
`Q_sq J cycleGens data ω₀ ω₁ = - star (Q_sq J cycleGens data ω₁ ω₀)`.**

This is the sesquilinear analog of the matrix-level identity
`periodMatrixForm_isAntiHermitian`. Multiplied by `i`, it becomes
Hermitian symmetric. -/
theorem conj_swap (hJ : Jᵀ = -J) (ω₀ ω₁ : HolomorphicOneForm X) :
    periodSesquilinearForm cycleGens J ω₀ ω₁
      = - star (periodSesquilinearForm cycleGens J ω₁ ω₀) := by
  unfold periodSesquilinearForm
  -- Unfold star (sum of sum of products), distribute.
  rw [star_sum]
  simp_rw [star_sum, StarMul.star_mul, star_intCast, star_star]
  -- RHS now: -∑ k, ∑ l, P(γ l, ω₀) · (star (P(γ k, ω₁)) · ↑(J k l)).
  -- (Note Lean swapped the multiplication order — that's fine for `ring`.)
  -- Strategy: rewrite LHS by `J k l = -(J l k)` (from hJ), then
  -- pull -1 out and commute the sum.
  have h_J_swap : ∀ k l, (J k l : ℂ) = -((J l k : ℂ)) := by
    intro k l
    have h_entry : J k l = -(J l k) := by
      have h_apply := congrFun (congrFun hJ l) k
      change J k l = -(J l k) at h_apply
      exact h_apply
    rw [h_entry]; push_cast; ring
  have h_lhs_rewrite :
      (∑ k, ∑ l, (J k l : ℂ) * PeriodPairing data (cycleGens k) ω₀
            * star (PeriodPairing data (cycleGens l) ω₁))
        = ∑ k, ∑ l, -((J l k : ℂ)) * PeriodPairing data (cycleGens k) ω₀
            * star (PeriodPairing data (cycleGens l) ω₁) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [h_J_swap k l]
  rw [h_lhs_rewrite]
  -- LHS: ∑ k, ∑ l, -(J l k : ℂ) · P(γ k, ω₀) · star (P(γ l, ω₁))
  -- Pull negation out and commute sums.
  rw [show (∑ k, ∑ l, -((J l k : ℂ)) * PeriodPairing data (cycleGens k) ω₀
              * star (PeriodPairing data (cycleGens l) ω₁))
        = -(∑ k, ∑ l, (J l k : ℂ) * PeriodPairing data (cycleGens k) ω₀
              * star (PeriodPairing data (cycleGens l) ω₁)) from by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring]
  rw [show (∑ k, ∑ l, (J l k : ℂ) * PeriodPairing data (cycleGens k) ω₀
              * star (PeriodPairing data (cycleGens l) ω₁))
        = ∑ l, ∑ k, (J l k : ℂ) * PeriodPairing data (cycleGens k) ω₀
              * star (PeriodPairing data (cycleGens l) ω₁) from
      Finset.sum_comm]
  -- LHS: -∑ l, ∑ k, (J l k : ℂ) · P(γ k, ω₀) · star (P(γ l, ω₁))
  -- RHS: -∑ k, ∑ l, P(γ l, ω₀) · (star (P(γ k, ω₁)) · ↑(J k l))
  -- Rename in RHS: outer k → l_RHS, inner l → k_RHS. Then both match after `ring`.
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

end periodSesquilinearForm

end JacobianChallenge

end
