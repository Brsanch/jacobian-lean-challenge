/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannBilinearRelations

set_option linter.unusedSectionVars false

/-! # Diagonal of `pmatᵀ · J.cast · pmat` vanishes from anti-symmetry of `J` (chip 20e)

For *any* genus `g`, any complex `2g × g` period matrix `pmat`, and any
anti-symmetric integer `2g × 2g` matrix `J`, the diagonal entries of
the `g × g` matrix `N := pmatᵀ · J.cast · pmat` vanish:

  `N i i = 0` for every `i : Fin g`.

This generalises the genus-1 argument of chip 13
(`antiSymmetric_one_by_one_eq_zero`) — which uses *Subsingleton (Fin
1)* to conclude `N = 0` — to a *per-diagonal-entry* statement at
arbitrary genus.

Mathematical content: `N` is anti-symmetric (since `J` is), and an
anti-symmetric matrix has vanishing diagonal in any characteristic
`≠ 2`.

This is a **partial structural reduction** of the Riemann bilinear
first relation at general genus: the diagonal entries are
unconditionally forced to vanish; only the off-diagonal entries
encode genuine classical content (integration of `ω_i ∧ ω_j` over
the surface and Stokes).

## What this file ships

* `pmat_transpose_J_pmat_diag_eq_zero_of_antisymm` — the per-entry diagonal
  vanishing.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix

namespace JacobianChallenge

/-- **Diagonal entries of `pmatᵀ · J.cast · pmat` vanish for
anti-symmetric `J`.** Per-entry version of the genus-1 chip 13:
holds for every `i : Fin g`, at every genus. -/
theorem pmat_transpose_J_pmat_diag_eq_zero_of_antisymm
    {g : ℕ}
    (pmat : Matrix (Fin (2 * g)) (Fin g) ℂ)
    {J : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ}
    (hJ : Jᵀ = -J)
    (i : Fin g) :
    (pmatᵀ * J.map ((↑) : ℤ → ℂ) * pmat) i i = 0 := by
  set N := pmatᵀ * J.map ((↑) : ℤ → ℂ) * pmat with hN_def
  -- Anti-symmetry: `Nᵀ = -N` from anti-symmetry of `J`.
  have hN_antisym : Nᵀ = -N := by
    change ((pmatᵀ * J.map ((↑) : ℤ → ℂ) * pmat)ᵀ)
        = -(pmatᵀ * J.map ((↑) : ℤ → ℂ) * pmat)
    rw [Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose]
    rw [show (J.map ((↑) : ℤ → ℂ))ᵀ = (Jᵀ).map ((↑) : ℤ → ℂ) from rfl]
    rw [hJ]
    rw [show ((-J).map ((↑) : ℤ → ℂ)) = -J.map ((↑) : ℤ → ℂ) from by
      ext k l; simp]
    rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  -- `N i i = (Nᵀ) i i = (-N) i i = -(N i i)`.
  have h_diag : N i i = -N i i := by
    have := congr_fun (congr_fun hN_antisym i) i
    simpa using this
  -- `2 · N i i = 0` over ℂ, hence `N i i = 0`.
  have h2 : (2 : ℂ) * N i i = 0 := by
    have heq : (2 : ℂ) * N i i = N i i - (-N i i) := by ring
    rw [heq, ← h_diag, sub_self]
  have h2_ne : (2 : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h2).resolve_left h2_ne

end JacobianChallenge

end
