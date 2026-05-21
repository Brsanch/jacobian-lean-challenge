/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannBilinearRelations

set_option linter.unusedSectionVars false

/-! # `RiemannBilinearFirstRelation` automatic at genus 1 (chip 13)

The matrix `pmatᵀ * J.cast * pmat` is `g × g` and anti-symmetric when
`J` is anti-symmetric (since `(pmatᵀ J pmat)ᵀ = pmatᵀ Jᵀ pmat = -pmatᵀ J pmat`).
At `g = 1`, the `1 × 1` anti-symmetric matrix is forced to be zero
(a Hermitian-like scalar identity in characteristic ≠ 2). Hence the
**first relation `RiemannBilinearFirstRelation` is automatic** at
genus 1 for any anti-symmetric `J`.

At higher genus, the diagonal entries of `pmatᵀ J pmat` are still
forced to be zero (by the same scalar identity on each `(i,i)` entry),
but the off-diagonal entries encode actual conditions.

## What this file ships

* `antiSymmetric_one_by_one_eq_zero` — a `Fin 1`-indexed anti-symmetric
  matrix over a ring with `2 ≠ 0` is zero.
* `riemannBilinearFirstRelation_of_antisymmetric_genus_one` — genus-1
  discharge of `RiemannBilinearFirstRelation` for any anti-symmetric J.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Anti-symmetric `1 × 1` matrix is zero.** Over a ring with `2 ≠ 0`
(e.g., ℂ), the only `Fin 1 × Fin 1` anti-symmetric matrix is `0`. -/
theorem antiSymmetric_one_by_one_eq_zero
    {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]
    (M : Matrix (Fin 1) (Fin 1) R) (h : Mᵀ = -M) :
    M = 0 := by
  ext i j
  fin_cases i; fin_cases j
  show M 0 0 = 0
  have h00 : M 0 0 = -M 0 0 := by
    have := congr_fun (congr_fun h 0) 0
    simpa using this
  have h2 : (2 : R) * M 0 0 = 0 := by
    have heq : (2 : R) * M 0 0 = M 0 0 - (-M 0 0) := by ring
    rw [heq, ← h00, sub_self]
  have h2_ne : (2 : R) ≠ 0 := two_ne_zero
  exact (mul_eq_zero.mp h2).resolve_left h2_ne

/-- **Genus-1 automatic discharge of `RiemannBilinearFirstRelation`.**
For any X with `genus X = 1` and any anti-symmetric integer matrix `J`,
the first bilinear relation holds: `pmatᵀ * J.cast * pmat = 0` (a `1×1`
anti-symmetric ℂ-matrix is `0`). -/
theorem riemannBilinearFirstRelation_of_antisymmetric_genus_one
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    (hJ : Jᵀ = -J)
    (h_g : JacobianChallenge.genus X = 1) :
    RiemannBilinearFirstRelation data basis_ω cycleGens J := by
  -- The matrix `pmatᵀ J pmat` is anti-symmetric (since J is).
  unfold RiemannBilinearFirstRelation
  -- Reindex Fin (genus X) ≅ Fin 1 via h_g.
  -- After reindex, apply antiSymmetric_one_by_one_eq_zero.
  -- The cleanest approach: cast the matrix back to Fin 1 via Equiv.
  -- Strategy: use `Subsingleton` argument on Fin (genus X) when genus = 1.
  haveI : Subsingleton (Fin (JacobianChallenge.genus X)) := by
    rw [h_g]; infer_instance
  -- For a Subsingleton index, any matrix is determined by its (0, 0) entry.
  -- For an anti-symmetric matrix with Subsingleton index, the (0, 0) entry
  -- is its own negation, hence zero.
  ext i j
  -- Goal: ((pmat^T * J.cast * pmat) i j = 0 i j).
  have hi : i = j := Subsingleton.elim i j
  subst hi
  -- Goal: (pmatᵀ * J.cast * pmat) i i = 0.
  -- Anti-symmetry of pmatᵀ J pmat: (pmatᵀ J pmat)ᵀ = -(pmatᵀ J pmat).
  -- So (pmatᵀ J pmat) i i = ((pmatᵀ J pmat)ᵀ) i i = -((pmatᵀ J pmat) i i).
  set N := (periodMatrix data basis_ω cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)
            * periodMatrix data basis_ω cycleGens
  show N i i = 0
  have hN_antisym : Nᵀ = -N := by
    show ((periodMatrix data basis_ω cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)
           * periodMatrix data basis_ω cycleGens)ᵀ =
          -((periodMatrix data basis_ω cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)
           * periodMatrix data basis_ω cycleGens)
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [show (J.map ((↑) : ℤ → ℂ))ᵀ = (Jᵀ).map ((↑) : ℤ → ℂ) from rfl]
    rw [hJ]
    rw [show ((-J).map ((↑) : ℤ → ℂ)) = -J.map ((↑) : ℤ → ℂ) from by
      ext k l; simp]
    rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  have h00 : N i i = -N i i := by
    have := congr_fun (congr_fun hN_antisym i) i
    simpa using this
  -- 2 * N i i = 0 ⟹ N i i = 0.
  have h2 : (2 : ℂ) * N i i = 0 := by
    have heq : (2 : ℂ) * N i i = N i i - (-N i i) := by ring
    rw [heq, ← h00, sub_self]
  have h2_ne : (2 : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h2).resolve_left h2_ne

end JacobianChallenge

end
