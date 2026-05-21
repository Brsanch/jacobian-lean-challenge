/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannBilinearFirstRelationOffDiagonal

set_option linter.unusedSectionVars false

/-! # First relation reduces to strict-upper-triangular vanishing (chip 20g)

Composes chip 20f with the anti-symmetry of `N := pmatᵀ · J.cast · pmat`
(automatic from anti-sym `J`):

* chip 20f: first relation ⟺ off-diagonal vanishing.
* anti-symmetry: `N i j = -N j i`, so `N i j = 0` ⟺ `N j i = 0`.

Therefore the off-diagonal vanishing reduces to the *strict-upper-
triangular* vanishing:

  `∀ i j : Fin g, i < j → (pmatᵀ · J.cast · pmat) i j = 0`.

(Equivalently, the strict-lower triangle works; we use upper as the
canonical convention.) This halves the open content again compared
to chip 20f:

* `g = 0`: 0 strict-upper entries → vacuous.
* `g = 1`: 0 strict-upper entries → automatic (chip 13).
* `g = 2`: 1 strict-upper entry → first relation reduces to a **single
  scalar equation** `(pmatᵀ · J.cast · pmat) 0 1 = 0`.
* `g ≥ 3`: `g(g − 1)/2` independent scalar equations.

This is the sharpest in-tree reduction of the first relation at
general genus from purely structural (algebraic) content. The
remaining open content is the explicit "ω_i ∧ ω_j integration"
classical theorem.

## What this file ships

* `riemannBilinearFirstRelation_iff_strictUpperTriangular_zero_of_antisymm`
  — the biconditional reduction.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Reduction to strict-upper-triangular vanishing.**

For anti-symmetric `J`, the Riemann bilinear first relation holds
iff every strictly-upper-triangular entry of `N := pmatᵀ · J.cast · pmat`
vanishes. Combines chip 20f (off-diagonal reduction) with the
anti-symmetry of `N` to fold the lower triangle into the upper. -/
theorem riemannBilinearFirstRelation_iff_strictUpperTriangular_zero_of_antisymm
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    (hJ : Jᵀ = -J) :
    RiemannBilinearFirstRelation data α cycleGens J ↔
      ∀ i j : Fin (JacobianChallenge.genus X), i < j →
        ((periodMatrix data α cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)
          * periodMatrix data α cycleGens) i j = 0 := by
  -- Step 1: bridge through chip 20f's off-diagonal characterisation.
  rw [riemannBilinearFirstRelation_iff_offDiagonal_zero_of_antisymm
        data α cycleGens hJ]
  -- Step 2: derive anti-symmetry of `N := pmatᵀ · J · pmat`.
  set N := (periodMatrix data α cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)
            * periodMatrix data α cycleGens with hN_def
  have hN_antisym : Nᵀ = -N := by
    change ((periodMatrix data α cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)
              * periodMatrix data α cycleGens)ᵀ
          = -((periodMatrix data α cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)
              * periodMatrix data α cycleGens)
    rw [Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose]
    rw [show (J.map ((↑) : ℤ → ℂ))ᵀ = (Jᵀ).map ((↑) : ℤ → ℂ) from rfl]
    rw [hJ]
    rw [show ((-J).map ((↑) : ℤ → ℂ)) = -J.map ((↑) : ℤ → ℂ) from by
      ext k l; simp]
    rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  -- Step 3: build the biconditional `N i j = 0 (i ≠ j) ↔ N i j = 0 (i < j)`.
  constructor
  · intro h_offdiag i j hij
    exact h_offdiag i j (ne_of_lt hij)
  · intro h_upper i j hij
    rcases lt_or_gt_of_ne hij with h_lt | h_gt
    · exact h_upper i j h_lt
    · -- i > j case: use N i j = -N j i = -0 = 0.
      have h_anti_ij : N i j = -(N j i) := by
        have := congr_fun (congr_fun hN_antisym j) i
        -- `Nᵀ j i = N i j` and `(-N) j i = -(N j i)`.
        simpa using this
      rw [h_anti_ij]
      rw [h_upper j i h_gt]
      simp

end JacobianChallenge

end
