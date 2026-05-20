/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodLatticeFromPairing

set_option linter.unusedSectionVars false

/-! # `PeriodMatrix`: the `2g × g` complex matrix of period integrals

For a basis `α : Basis (Fin g) ℂ (HolomorphicOneForm X)` and a tuple of
`2g` cycles `cycleGens : Fin (2g) → data.H1`, the **`PeriodMatrix`** is
the complex matrix `Π_ij = ∫_{cycleGens i} α j`, i.e., the `i`-th row
is `periodVector α (cycleGens i)`.

Riemann's bilinear relations, in matrix form, are statements about this
period matrix `Π` and the symplectic intersection form `J ∈ Mat_{2g×2g}(ℤ)`:

1. **First relation:** `Π · J · Π^T = 0`.
2. **Second relation:** `i · Π · J · Π̄^T` is a positive-definite
   Hermitian `g × g` matrix.

The second relation implies the ℝ-linear independence of the `2g` rows
of `Π` (the `bilinear` field of `SmoothHomologyDataPackage`).

## What this file ships

* `periodMatrix data α cycleGens` — the `2g × g` complex matrix.
* `periodMatrix_row` — `i`-th row equals `periodVector α (cycleGens i)`.
* `periodMatrix_apply` — pointwise formula via `PeriodPairing`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Matrix

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **The period matrix** as a `2g × g` complex matrix.

The `i`-th row is the period vector of `cycleGens i` against the basis
`α`: `Π_ij = ∫_{cycleGens i} (α j) = periodVector α (cycleGens i) j`. -/
noncomputable def periodMatrix
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1) :
    Matrix (Fin (2 * JacobianChallenge.genus X))
      (Fin (JacobianChallenge.genus X)) ℂ :=
  fun i j => periodVector data α (cycleGens i) j

@[simp] lemma periodMatrix_apply
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (i : Fin (2 * JacobianChallenge.genus X))
    (j : Fin (JacobianChallenge.genus X)) :
    periodMatrix data α cycleGens i j = PeriodPairing data (cycleGens i) (α j) :=
  rfl

/-- **The `i`-th row of the period matrix equals the period vector of
`cycleGens i`.** -/
lemma periodMatrix_row
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (i : Fin (2 * JacobianChallenge.genus X)) :
    (fun j => periodMatrix data α cycleGens i j)
      = periodVector data α (cycleGens i) :=
  rfl

/-! ## ℝ-linear independence of rows = ℝ-linear independence of period vectors

The `bilinear` field of `SmoothHomologyDataPackage` is the ℝ-linear
independence of the period vectors. By `periodMatrix_row`, this is
*equivalently* the ℝ-linear independence of the rows of `periodMatrix`. -/

/-- **ℝ-linear independence of period vectors equivalent to ℝ-LI of
the period matrix rows.** Direct from `periodMatrix_row` — the rows
*are* the period vectors. -/
theorem linearIndependent_periodVector_iff_periodMatrix_rows
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1) :
    LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus X) =>
          periodVector data α (cycleGens i))
      ↔
    LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus X) =>
          (fun j : Fin (JacobianChallenge.genus X) =>
            periodMatrix data α cycleGens i j)) := by
  -- The two `fun i => ...` arguments are *definitionally* equal by
  -- `periodMatrix_row`.
  rfl

end JacobianChallenge

end
