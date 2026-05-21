/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HodgeFormMatrix

set_option linter.unusedSectionVars false

/-! # `hodgeFormFromMatrix`: realising any Hermitian matrix as a Hodge-style form

For any compact connected complex 1-manifold `X` with chosen ℂ-basis
`basis_ω : Basis (Fin g) ℂ (HolomorphicOneForm X)` and any **Hermitian**
matrix `M : Matrix (Fin g) (Fin g) ℂ` (`Mᴴ = M`), we construct a
`HermitianOnHolomorphicOneForm X` whose matrix representation against
`basis_ω` is exactly `M`. The form is the double-sum sesquilinear
pairing

  `H(om, eta) := ∑ i j, (basis_ω.repr om) i · M i j · star ((basis_ω.repr eta) j)`.

This is the **realisation map** from Hermitian matrices on `Fin g × Fin g`
back to abstract Hermitian forms — the inverse direction of
`HermitianOnHolomorphicOneForm.toMatrix`. The two are related by
`hodgeFormFromMatrix_toMatrix`: realising and then matrixifying gives
back the same matrix.

## What this file ships

* `hodgeFormFromMatrix basis_ω M hM` — the `HermitianOnHolomorphicOneForm
  X` realising the matrix `M`.
* `hodgeFormFromMatrix_toMatrix` — `(...).toMatrix basis_ω = M`.
* `hodgeFormFromMatrix_apply` — explicit formula for `toFun`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Matrix

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`hodgeFormFromMatrix basis_ω M hM`** — the Hermitian form on
`HolomorphicOneForm X` realising the matrix `M` (with `Mᴴ = M`).

Defined as the sesquilinear pairing
`H(om, eta) := ∑ i j, (basis_ω.repr om) i · M i j · star ((basis_ω.repr eta) j)`. -/
noncomputable def hodgeFormFromMatrix
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (M : Matrix (Fin (JacobianChallenge.genus X))
          (Fin (JacobianChallenge.genus X)) ℂ)
    (hM : M.IsHermitian) :
    HermitianOnHolomorphicOneForm X where
  toFun om eta :=
    ∑ i, ∑ j, (basis_ω.repr om) i * M i j * star ((basis_ω.repr eta) j)
  map_zero_left eta := by
    simp
  map_add_left om₁ om₂ eta := by
    -- repr (om₁ + om₂) = repr om₁ + repr om₂
    simp only [map_add, Finsupp.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  map_smul_left c om eta := by
    have h_repr_smul : ∀ i, (basis_ω.repr (c • om)) i = c * (basis_ω.repr om) i := by
      intro i
      simp [Finsupp.smul_apply, smul_eq_mul]
    change (∑ i, ∑ j, (basis_ω.repr (c • om)) i * M i j * star ((basis_ω.repr eta) j))
        = c * (∑ i, ∑ j, (basis_ω.repr om) i * M i j * star ((basis_ω.repr eta) j))
    simp_rw [h_repr_smul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  conjSymm om eta := by
    -- Goal: (∑ i j, (basis_ω.repr om) i * M i j * star ((basis_ω.repr eta) j))
    --     = star (∑ i j, (basis_ω.repr eta) i * M i j * star ((basis_ω.repr om) j))
    -- Push star inside the double sum on RHS.
    rw [star_sum]
    simp_rw [star_sum]
    -- Swap dummy indices via Finset.sum_comm on LHS so both sides match shape.
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    -- After sum_comm + double-refine: Lean's `i`/`j` are the *swapped* dummies.
    -- Goal: (basis_ω.repr om) j * M j i * star ((basis_ω.repr eta) i)
    --     = star ((basis_ω.repr eta) i * M i j * star ((basis_ω.repr om) j))
    rw [StarMul.star_mul, StarMul.star_mul, star_star]
    -- Goal (right side distributed; right-assoc):
    --   (basis_ω.repr om) j * M j i * star ((basis_ω.repr eta) i)
    --     = (basis_ω.repr om) j * (star (M i j) * star ((basis_ω.repr eta) i))
    have hM_ij : star (M i j) = M j i := by
      have h := congr_fun (congr_fun hM j) i
      rw [Matrix.conjTranspose_apply] at h
      exact h
    rw [hM_ij]
    ring

/-- **Explicit formula for `hodgeFormFromMatrix.toFun`.** -/
@[simp] lemma hodgeFormFromMatrix_apply
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (M : Matrix (Fin (JacobianChallenge.genus X))
          (Fin (JacobianChallenge.genus X)) ℂ)
    (hM : M.IsHermitian) (om eta : HolomorphicOneForm X) :
    (hodgeFormFromMatrix basis_ω M hM).toFun om eta
      = ∑ i, ∑ j, (basis_ω.repr om) i * M i j * star ((basis_ω.repr eta) j) :=
  rfl

/-- **`hodgeFormFromMatrix` recovers the matrix.** The Hermitian form
constructed from a matrix `M`, when re-matrixified against the same
basis, returns `M` exactly. -/
theorem hodgeFormFromMatrix_toMatrix
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (M : Matrix (Fin (JacobianChallenge.genus X))
          (Fin (JacobianChallenge.genus X)) ℂ)
    (hM : M.IsHermitian) :
    (hodgeFormFromMatrix basis_ω M hM).toMatrix basis_ω = M := by
  funext i j
  change (∑ k, ∑ l, (basis_ω.repr (basis_ω i)) k * M k l
              * star ((basis_ω.repr (basis_ω j)) l)) = M i j
  -- `Basis.repr_self_apply` : `b.repr (b i) k = if i = k then 1 else 0`.
  -- Note: the condition is `i = k`, not `k = i`.
  simp_rw [Basis.repr_self_apply]
  -- Pure-real conditional: star (if p then 1 else 0) = if p then 1 else 0.
  have h_star_ite : ∀ (p : Prop) [Decidable p],
      star (ite p (1 : ℂ) 0) = ite p (1 : ℂ) 0 := by
    intros p hp
    by_cases h : p <;> simp [h]
  simp_rw [h_star_ite]
  -- Goal: ∑ k l, (if i = k then 1 else 0) * M k l * (if j = l then 1 else 0) = M i j.
  -- Outer sum: only k = i contributes.
  refine (Finset.sum_eq_single i ?_ ?_).trans ?_
  · intros k _ hk
    rw [if_neg (Ne.symm hk)]
    simp
  · intro h_not_mem; exact absurd (Finset.mem_univ i) h_not_mem
  -- Now k := i: ∑ l, (if i = i then 1 else 0) * M i l * (if j = l then 1 else 0) = M i j.
  rw [if_pos rfl]
  simp_rw [one_mul]
  -- Inner sum: only l = j contributes.
  refine (Finset.sum_eq_single j ?_ ?_).trans ?_
  · intros l _ hl
    rw [if_neg (Ne.symm hl)]
    simp
  · intro h_not_mem; exact absurd (Finset.mem_univ j) h_not_mem
  rw [if_pos rfl, mul_one]

end JacobianChallenge

end
