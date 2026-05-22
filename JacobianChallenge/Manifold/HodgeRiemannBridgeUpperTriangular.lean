/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HodgeRiemannBridge
import JacobianChallenge.Manifold.PeriodMatrixAntiHermitian
import JacobianChallenge.Manifold.StandardSymplecticForm

set_option linter.unusedSectionVars false

/-! # Bridge identity reduces to upper-triangular entries

Both sides of `HodgeRiemannBridgeHypothesis` for `J = standardSymplectic g`
are `g × g` Hermitian matrices:

* LHS `(I • periodMatrixForm pm (standardSymplectic g))` is Hermitian
  via `iPeriodMatrixForm_isHermitian` + `standardSymplectic_antisymm`
  (chip 19a).
* RHS `H.toMatrix basis_ω` is Hermitian via `toMatrix_conjTranspose`.

Two Hermitian matrices are equal iff they agree on the upper triangle
(including diagonal). Hence the bridge identity reduces to verifying
`g + g(g − 1)/2 = g(g + 1)/2` entries rather than `g²`.

## What ships

* `hodgeRiemannBridgeHypothesis_of_upperTriangular` — backward: from
  equality on `i ≤ j` to the full matrix bridge.

## Significance

A constructive reduction: a user proving the bridge identity at general
genus needs only check the upper triangle (diagonal + strict upper).
At genus 1 the upper triangle is the single diagonal entry; at genus 2
it is 3 entries; at genus g, `g(g+1)/2` entries.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Bridge identity at `J = standardSymplectic g` from upper-triangular
agreement.**

If the matrices agree on every `(i, j)` with `i.val ≤ j.val`, the full
matrix identity follows, since both sides are Hermitian (`i • periodMatrixForm`
via `standardSymplectic_antisymm`; `H.toMatrix` via `conjSymm`). -/
theorem hodgeRiemannBridgeHypothesis_of_upperTriangular
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (H : HermitianOnHolomorphicOneForm X)
    (h_upper :
      ∀ i j : Fin (JacobianChallenge.genus X), i.val ≤ j.val →
        ((Complex.I : ℂ) •
          ((periodMatrix data basis_ω cycleGens)ᵀ
            * (standardSymplectic (JacobianChallenge.genus X)).map
                ((↑) : ℤ → ℂ)
            * (periodMatrix data basis_ω cycleGens).map star)) i j
          = H.toMatrix basis_ω i j) :
    HodgeRiemannBridgeHypothesis data basis_ω cycleGens
      (standardSymplectic (JacobianChallenge.genus X)) H := by
  unfold HodgeRiemannBridgeHypothesis
  funext i j
  -- The matrix product expression is `i • periodMatrixForm pm J`.
  -- Set M := the LHS pointwise function for clarity.
  set M : Matrix (Fin (JacobianChallenge.genus X))
                 (Fin (JacobianChallenge.genus X)) ℂ :=
    (Complex.I : ℂ) •
      ((periodMatrix data basis_ω cycleGens)ᵀ
        * (standardSymplectic (JacobianChallenge.genus X)).map
            ((↑) : ℤ → ℂ)
        * (periodMatrix data basis_ω cycleGens).map star) with hM
  show M i j = H.toMatrix basis_ω i j
  -- LHS is Hermitian: chip 19a + standardSymplectic_antisymm.
  have hM_herm : M.IsHermitian := by
    rw [hM]
    exact iPeriodMatrixForm_isHermitian (periodMatrix data basis_ω cycleGens)
      (standardSymplectic (JacobianChallenge.genus X))
      (standardSymplectic_antisymm (JacobianChallenge.genus X))
  -- RHS is Hermitian: toMatrix_conjTranspose.
  have hH_herm : (H.toMatrix basis_ω).IsHermitian :=
    H.toMatrix_conjTranspose basis_ω
  -- Case split on i.val ≤ j.val.
  by_cases h_le : i.val ≤ j.val
  · -- Upper triangle (including diagonal): direct from hypothesis.
    exact h_upper i j h_le
  · -- Lower triangle: use Hermitian symmetry of both sides.
    have h_le' : j.val ≤ i.val := Nat.le_of_lt (Nat.lt_of_not_le h_le)
    have h_swap : M j i = H.toMatrix basis_ω j i := h_upper j i h_le'
    -- M i j = star (M j i) since Mᴴ = M.
    have hM_swap : M i j = star (M j i) := by
      have h_eq : Mᴴ i j = M i j := congrFun (congrFun hM_herm i) j
      change star (M j i) = M i j at h_eq
      exact h_eq.symm
    have hH_swap : H.toMatrix basis_ω i j = star (H.toMatrix basis_ω j i) := by
      have h_eq : (H.toMatrix basis_ω)ᴴ i j = H.toMatrix basis_ω i j :=
        congrFun (congrFun hH_herm i) j
      change star (H.toMatrix basis_ω j i) = H.toMatrix basis_ω i j at h_eq
      exact h_eq.symm
    rw [hM_swap, h_swap, ← hH_swap]

end JacobianChallenge

end

