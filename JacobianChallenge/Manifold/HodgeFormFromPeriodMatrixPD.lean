/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HodgeFormFromPeriodMatrix
import JacobianChallenge.Manifold.RiemannBilinearRelations

set_option linter.unusedSectionVars false

/-! # Positive-definiteness of `canonicalHodgeFormFromAntiSymm`
from the positivity conjunct of `RiemannBilinearSecondRelation` (chip 19d)

The canonical Hodge form `canonicalHodgeFormFromAntiSymm` defined in
`HodgeFormFromPeriodMatrix.lean` is positive definite iff the period
matrix's "i • Πᵀ J Π̄" satisfies the positivity conjunct of
`RiemannBilinearSecondRelation`.

The connection is via the conjugation substitution: with
`x i := star ((basis_ω.repr om) i)`, we have

  `H_can om om = star x ⬝ᵥ (M *ᵥ x)`.

(`star x ⬝ᵥ M *ᵥ x` is the standard Hermitian quadratic form;
`star x = basis_ω.repr om` after `star_star`.)

Hence `(H_can om om).re = (star x ⬝ᵥ M *ᵥ x).re` etc., and the PD
condition transfers through.

This eliminates the Hodge-form choice entirely: given anti-symmetric
`J` and the positivity conjunct of `RiemannBilinearSecondRelation`,
`CompleteHodgeRiemannHypothesis` follows.

## What this file ships

* `canonicalHodgeFormFromAntiSymm_toFun_self_eq` — `H om om = star x ⬝ᵥ (M *ᵥ x)`.
* `isPositiveDefinite_canonicalHodgeFormFromAntiSymm` — PD from
  positivity conjunct.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Matrix

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Diagonal identity for the canonical Hodge form.**
With `x i := star ((basis_ω.repr om) i)`, we have
`H_can.toFun om om = star x ⬝ᵥ (M *ᵥ x)` where
`M := (Complex.I) • periodMatrixForm pm J`. -/
theorem canonicalHodgeFormFromAntiSymm_toFun_self_eq
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    (hJ : Jᵀ = -J)
    (om : HolomorphicOneForm X) :
    (canonicalHodgeFormFromAntiSymm data basis_ω cycleGens hJ).toFun om om
      = star (fun i => star ((basis_ω.repr om) i))
          ⬝ᵥ
          (((Complex.I : ℂ) •
              periodMatrixForm (periodMatrix data basis_ω cycleGens) J)
            *ᵥ (fun i => star ((basis_ω.repr om) i))) := by
  unfold canonicalHodgeFormFromAntiSymm
  rw [hodgeFormFromMatrix_apply]
  -- LHS now: ∑ i, ∑ j, (basis_ω.repr om) i * M i j * star ((basis_ω.repr om) j).
  -- RHS: star (fun i => star (repr om i)) ⬝ᵥ (M *ᵥ (fun i => star (repr om i))).
  -- Unfold the matrix-vector product and dot product to double sums.
  unfold dotProduct Matrix.mulVec
  simp_rw [Pi.star_apply, star_star, dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- **Canonical Hodge form is positive definite from
`RiemannBilinearSecondRelation` positivity.** Given anti-symmetric `J`
and the positivity conjunct on `i • periodMatrixForm pm J`, the
canonical Hodge form is positive definite. -/
theorem isPositiveDefinite_canonicalHodgeFormFromAntiSymm
    {data : PeriodPairingData X}
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    {cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1}
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    (hJ : Jᵀ = -J)
    (h_pos : ∀ x : Fin (JacobianChallenge.genus X) → ℂ, x ≠ 0 →
        (star x ⬝ᵥ
            (((Complex.I : ℂ) •
                periodMatrixForm (periodMatrix data basis_ω cycleGens) J)
              *ᵥ x)).im = 0 ∧
          0 < (star x ⬝ᵥ
            (((Complex.I : ℂ) •
                periodMatrixForm (periodMatrix data basis_ω cycleGens) J)
              *ᵥ x)).re) :
    (canonicalHodgeFormFromAntiSymm data basis_ω cycleGens hJ).IsPositiveDefinite := by
  refine ⟨fun om => ?_, fun om h_zero => ?_⟩
  · -- Part 1: (H om om).im = 0 ∧ 0 ≤ (H om om).re
    rw [canonicalHodgeFormFromAntiSymm_toFun_self_eq]
    set x : Fin (JacobianChallenge.genus X) → ℂ :=
      fun i => star ((basis_ω.repr om) i)
    by_cases hx : x = 0
    · -- x = 0 ⟹ M *ᵥ x = 0 ⟹ dot product is 0.
      simp [hx]
    · have h := h_pos x hx
      exact ⟨h.1, le_of_lt h.2⟩
  · -- Part 2: H om om = 0 ⟹ om = 0.
    rw [canonicalHodgeFormFromAntiSymm_toFun_self_eq] at h_zero
    set x : Fin (JacobianChallenge.genus X) → ℂ :=
      fun i => star ((basis_ω.repr om) i) with hx_def
    -- h_zero : star x ⬝ᵥ (M *ᵥ x) = 0
    -- If x ≠ 0, h_pos gives 0 < (...).re, contradicting (... = 0).re = 0.
    by_contra hom
    have hx : x ≠ 0 := by
      intro hx
      apply hom
      -- om = 0 from x = 0: x = star ∘ basis_ω.repr om, so x = 0 ⟹ basis_ω.repr om = 0 ⟹ om = 0.
      have h_repr_apply : ∀ i, (basis_ω.repr om) i = 0 := by
        intro i
        have h_xi : x i = 0 := congr_fun hx i
        have h_star_xi : star (x i) = 0 := by rw [h_xi]; simp
        change star (star ((basis_ω.repr om) i)) = 0 at h_star_xi
        rwa [star_star] at h_star_xi
      have h_repr_zero : basis_ω.repr om = 0 := Finsupp.ext h_repr_apply
      have : basis_ω.repr.symm (basis_ω.repr om) = basis_ω.repr.symm 0 := by
        rw [h_repr_zero]
      simpa [LinearEquiv.symm_apply_apply, LinearEquiv.map_zero] using this
    have h_pos_pos := (h_pos x hx).2
    rw [h_zero] at h_pos_pos
    exact absurd h_pos_pos (by simp)

end JacobianChallenge

end
