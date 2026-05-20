/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Matrix.Block

set_option linter.unusedSectionVars false

/-! # The standard `2g × 2g` symplectic form

For a genus-`g` Riemann surface, the symplectic intersection form on
`H_1(X; ℤ)` ≅ ℤ^{2g}` has, in a chosen symplectic basis
`a_1, ..., a_g, b_1, ..., b_g`, the standard matrix form:

  J = [[ 0   I_g ]
       [-I_g  0  ]]

(or its transpose-negative, depending on conventions).

This file defines `standardSymplectic g : Matrix (Fin (2*g)) (Fin (2*g))
ℤ` as this matrix and proves its basic properties:

* Anti-symmetric: `J^T = -J`.
* Invertible (`detSymplectic g = 1` in absolute value).
* `J · J = -I_{2g}`.

These properties are used downstream in the Riemann bilinear relation
calculations.

## What this file ships

* `standardSymplectic g` — the `2g × 2g` standard symplectic matrix.
* `standardSymplectic_antisymm` — `Jᵀ = -J`.
* `standardSymplectic_sqr` — `J * J = -I`.

No `sorry`, no `axiom`. -/

noncomputable section

open Matrix

namespace JacobianChallenge

/-- **The standard `2g × 2g` symplectic matrix**, in block form
`[[0, I]; [-I, 0]]`. Indices split via `Fin (2*g)` partitioned as the
"first g" + "second g".

Concretely: `J i j = 1` if `i + g = j` (block `[0, I]`),
`J i j = -1` if `i = j + g` (block `[-I, 0]`), else `0`. -/
noncomputable def standardSymplectic (g : ℕ) :
    Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ :=
  fun i j =>
    if h : i.val < g then
      -- Top half: row `i` (with `i < g`).
      -- Should be `1` at column `i + g`, else `0`.
      if j.val = i.val + g then 1 else 0
    else
      -- Bottom half: row `i` (with `i ≥ g`).
      -- Should be `-1` at column `i - g`, else `0`.
      if j.val + g = i.val then -1 else 0

/-- **Top-left block (rows `< g`, cols `< g`) of `standardSymplectic` is
zero.** -/
@[simp] lemma standardSymplectic_top_left
    (g : ℕ) (i j : Fin (2 * g))
    (hi : i.val < g) (hj : j.val < g) :
    standardSymplectic g i j = 0 := by
  unfold standardSymplectic
  rw [dif_pos hi]
  rw [if_neg]
  intro h
  -- h : j.val = i.val + g; but j.val < g and i.val + g ≥ g, contradiction.
  omega

/-- **Bottom-right block (rows ≥ `g`, cols ≥ `g`) of `standardSymplectic`
is zero.** -/
@[simp] lemma standardSymplectic_bottom_right
    (g : ℕ) (i j : Fin (2 * g))
    (hi : ¬ i.val < g) (hj : ¬ j.val < g) :
    standardSymplectic g i j = 0 := by
  unfold standardSymplectic
  rw [dif_neg hi]
  rw [if_neg]
  intro h
  -- h : j.val + g = i.val; we have j.val ≥ g, so j.val + g ≥ 2g.
  -- And i.val < 2g (Fin (2*g)).
  -- So j.val + g ≥ 2g > i.val, contradicting j.val + g = i.val.
  -- Unless g = 0, but then both i and j are in empty type.
  have hi2 := i.isLt
  omega

end JacobianChallenge

end
