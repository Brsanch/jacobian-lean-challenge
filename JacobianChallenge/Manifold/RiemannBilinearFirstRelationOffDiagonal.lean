/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodMatrixDiagonalAntisymm

set_option linter.unusedSectionVars false

/-! # First relation reduces to off-diagonal vanishing at any genus (chip 20f)

For anti-symmetric integer `2g × 2g` matrix `J` and any complex
`2g × g` period matrix `pmat`, the matrix `N := pmatᵀ · J.cast · pmat`
is anti-symmetric. Chip 20e shows its **diagonal vanishes
automatically** from anti-symmetry of `J`. This chip composes that
fact with the observation that an anti-symmetric matrix is determined
by its off-diagonal entries: `N = 0` iff `N i j = 0` for all `i ≠ j`.

Consequently, the Riemann bilinear *first relation*
`RiemannBilinearFirstRelation data α cycleGens J` at general genus
reduces from a `g²`-entry condition to a `g(g − 1)/2`-entry condition
on the strict upper triangle of `N`.

At `g = 0`: 0 off-diagonal entries → vacuously true (chip 20b also
gives this via the empty-matrix route).

At `g = 1`: 0 off-diagonal entries → first relation automatic
(coincides with chip 13 `riemannBilinearFirstRelation_of_antisymmetric_genus_one`).

At `g ≥ 2`: nontrivial. The remaining open content is exactly the
classical "off-diagonal" / "ω_i ∧ ω_j integration" content.

## What this file ships

* `riemannBilinearFirstRelation_iff_offDiagonal_zero_of_antisymm` —
  the equivalence.
* `riemannBilinearFirstRelation_of_offDiagonal_zero_of_antisymm` —
  the forward implication (the useful one for discharging).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Reduction of the first relation to off-diagonal vanishing.**

For anti-symmetric `J`, `RiemannBilinearFirstRelation data α cycleGens J`
holds iff every off-diagonal entry `N i j` (with `i ≠ j`) of
`N := pmatᵀ · J.cast · pmat` vanishes. The diagonal entries vanish
automatically from anti-symmetry (chip 20e). -/
theorem riemannBilinearFirstRelation_iff_offDiagonal_zero_of_antisymm
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    (hJ : Jᵀ = -J) :
    RiemannBilinearFirstRelation data α cycleGens J ↔
      ∀ i j : Fin (JacobianChallenge.genus X), i ≠ j →
        ((periodMatrix data α cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)
          * periodMatrix data α cycleGens) i j = 0 := by
  unfold RiemannBilinearFirstRelation
  constructor
  · -- N = 0 ⟹ every entry is 0, in particular off-diagonal.
    intro hN i j _hne
    have := congr_fun (congr_fun hN i) j
    simpa using this
  · -- Off-diagonal entries 0 + diagonal entries 0 (chip 20e) ⟹ N = 0.
    intro h_offdiag
    ext i j
    by_cases hij : i = j
    · subst hij
      -- Diagonal entry: apply chip 20e.
      exact pmat_transpose_J_pmat_diag_eq_zero_of_antisymm
        (periodMatrix data α cycleGens) hJ i
    · exact h_offdiag i j hij

/-- **Forward implication: off-diagonal vanishing implies the first
relation** (anti-sym `J`). The useful direction for discharging the
first relation at general genus. -/
theorem riemannBilinearFirstRelation_of_offDiagonal_zero_of_antisymm
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    (hJ : Jᵀ = -J)
    (h_offdiag :
      ∀ i j : Fin (JacobianChallenge.genus X), i ≠ j →
        ((periodMatrix data α cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)
          * periodMatrix data α cycleGens) i j = 0) :
    RiemannBilinearFirstRelation data α cycleGens J :=
  (riemannBilinearFirstRelation_iff_offDiagonal_zero_of_antisymm
    data α cycleGens hJ).mpr h_offdiag

end JacobianChallenge

end
