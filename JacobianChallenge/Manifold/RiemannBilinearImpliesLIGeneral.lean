/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannBilinearImpliesLI
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option linter.unusedSectionVars false

/-! # `RiemannBilinearSecondRelation`-style positivity ⟹ invertibility

The general-g implication "Riemann second relation ⟹ ℝ-LI of period
vectors" requires a Σ-block argument (see `PeriodSigmaInvertibility.lean`).
This file isolates the first step: positive-definiteness ⟹ invertibility
of the underlying matrix `M = i Π^T J Π̄`.

The argument: if `M.mulVec v = 0`, then `star v ⬝ᵥ (M *ᵥ v) = 0`, so its
real part is `0`; if `v ≠ 0`, that contradicts strict positivity of the
real part. Hence `M.mulVec` is injective; for a square matrix over a
field, injectivity equals `IsUnit`.

## What this file ships

* `Matrix.isUnit_of_re_pos` — invertibility lemma: any Hermitian matrix
  whose Hodge-style quadratic form has strictly positive real part on
  every non-zero vector is `IsUnit`.
* `Matrix.isUnit_of_riemannBilinearSecondRelation` — direct corollary
  applied to the matrix appearing in `RiemannBilinearSecondRelation`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Step 1: `RiemannBilinearSecondRelation`-style positivity ⟹ invertible -/

/-- **Invertibility of a Hermitian matrix from `.re`-positivity on
non-zero vectors.** A `n × n` complex matrix that is Hermitian and
satisfies `0 < (xᴴ M x).re` for every non-zero `x : ι → ℂ` is
invertible (i.e., `IsUnit`).

The argument: `M.mulVec v = 0` ⟹ `star v ⬝ᵥ (M *ᵥ v) = 0` ⟹ if `v ≠ 0`,
then `.re > 0`, contradiction. So `M.mulVec` is injective; for a square
matrix over a field, this is equivalent to `IsUnit`. -/
theorem Matrix.isUnit_of_re_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ}
    (_hHerm : M.IsHermitian)
    (hPos : ∀ x : ι → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ (M *ᵥ x)).re) :
    IsUnit M := by
  rw [← mulVec_injective_iff_isUnit]
  intro v w hvw
  by_contra h_ne
  set u := v - w with hu_def
  have h_mv_u : M.mulVec u = 0 := by
    show M.mulVec (v - w) = 0
    rw [mulVec_sub]
    exact sub_eq_zero.mpr hvw
  have hu_ne : u ≠ 0 := fun h => h_ne (sub_eq_zero.mp h)
  have h_quad : star u ⬝ᵥ (M *ᵥ u) = 0 := by
    rw [h_mv_u]
    simp [dotProduct]
  have h_re : (star u ⬝ᵥ (M *ᵥ u)).re = 0 := by rw [h_quad]; simp
  exact absurd h_re (ne_of_gt (hPos u hu_ne))

/-- **The Riemann second-relation matrix `i Π^T J Π̄` is invertible.**
Direct corollary of `Matrix.isUnit_of_re_pos` for the specific shape
appearing in `RiemannBilinearSecondRelation`. -/
theorem isUnit_riemannBilinear2_matrix
    {data : PeriodPairingData X}
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    {cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1}
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    (hSecond : RiemannBilinearSecondRelation data basis_ω cycleGens J) :
    IsUnit ((Complex.I : ℂ) •
      ((periodMatrix data basis_ω cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)
        * (periodMatrix data basis_ω cycleGens).map star)) := by
  apply Matrix.isUnit_of_re_pos hSecond.1
  intro x hx
  exact (hSecond.2 x hx).2

end JacobianChallenge

end
