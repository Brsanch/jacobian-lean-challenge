/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.Basic

set_option linter.unusedSectionVars false

/-! # `i · Πᵀ · J · Π̄` is Hermitian for any anti-symmetric integer `J`

Pure linear algebra. The **Hermitian conjunct** of Riemann's second
bilinear relation does NOT require the Hodge–Riemann bridge identity —
it is automatic from anti-symmetry of `J` alone.

Given any complex matrix `Π : Matrix ι κ ℂ` (think: the period matrix)
and any anti-symmetric integer matrix `J : Matrix ι ι ℤ` (`Jᵀ = -J`):

* `M := Πᵀ · J.map ((↑) : ℤ → ℂ) · Π.map star` is **anti-Hermitian**
  (`Mᴴ = -M`).
* `(Complex.I : ℂ) • M` is **Hermitian** (`(i • M)ᴴ = i • M`).

This eliminates the need for a separate `IsHermitian` proof in the
`RiemannBilinearSecondRelation` conjunct: the structural anti-symmetry
of `J` already supplies it. The remaining classical content is then
purely the **positivity** half (`xᴴ · (i • M) · x > 0` for `x ≠ 0`).

## What this file ships

* `JacobianChallenge.periodMatrixForm Π J` — the abbreviation
  `Πᵀ · J.map ↑ · Π.map star : Matrix κ κ ℂ`.
* `periodMatrixForm_isAntiHermitian` — `Mᴴ = -M` for anti-symmetric `J`.
* `iPeriodMatrixForm_isHermitian` — `((Complex.I : ℂ) • M).IsHermitian`
  for anti-symmetric `J`.

No `sorry`, no `axiom`. -/

noncomputable section

open Matrix

namespace JacobianChallenge

universe u v

variable {ι : Type u} {κ : Type v} [Fintype ι] [DecidableEq ι]

/-- **The period-matrix bilinear form** `pmᵀ · J · pm̄` (with `J` cast to
ℂ via `Int.cast` and `pm̄` the entrywise conjugate of the period matrix
`pm`). Concretely a `κ × κ` ℂ-matrix. The bridge identity says this
equals `(1 / i) · H.toMatrix` for the Hodge inner product `H`; we use
it independent of that identity here. -/
def periodMatrixForm
    (pm : Matrix ι κ ℂ) (J : Matrix ι ι ℤ) : Matrix κ κ ℂ :=
  pmᵀ * J.map ((↑) : ℤ → ℂ) * pm.map star

/-- **Anti-Hermitian property.** For any matrix `pm : Matrix ι κ ℂ` and
any anti-symmetric integer matrix `J : Matrix ι ι ℤ` (`Jᵀ = -J`), the
matrix `periodMatrixForm pm J = pmᵀ · J.map ↑ · pm.map star` satisfies
`Mᴴ = -M`. -/
theorem periodMatrixForm_isAntiHermitian
    (pm : Matrix ι κ ℂ) (J : Matrix ι ι ℤ) (hJ : Jᵀ = -J) :
    (periodMatrixForm pm J)ᴴ = -(periodMatrixForm pm J) := by
  unfold periodMatrixForm
  -- Conjugate-transpose distributes over product (anti-homomorphism).
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  -- Goal: (pm.map star)ᴴ * (J.map ↑)ᴴ * (pmᵀ)ᴴ
  --     = -(pmᵀ * J.map ↑ * pm.map star).
  -- Compute each conjT:
  -- 1) (pm.map star)ᴴ = pmᵀ.
  have h_PsH : (pm.map star : Matrix ι κ ℂ)ᴴ = pmᵀ := by
    ext i j
    show star ((pm.map star)ᵀ i j) = pmᵀ i j
    show star (star (pm j i)) = pm j i
    exact star_star _
  -- 2) (pmᵀ)ᴴ = pm.map star.
  have h_PtH : (pmᵀ : Matrix κ ι ℂ)ᴴ = pm.map star := by
    ext i j; rfl
  -- 3) (J.map ↑)ᴴ = Jᵀ.map ↑.
  have h_JcH : (J.map ((↑) : ℤ → ℂ))ᴴ = Jᵀ.map ((↑) : ℤ → ℂ) := by
    ext i j
    show star ((J.map ((↑) : ℤ → ℂ))ᵀ i j) = (Jᵀ.map ((↑) : ℤ → ℂ)) i j
    show star (((↑) : ℤ → ℂ) (J j i)) = ((↑) : ℤ → ℂ) (J j i)
    exact star_intCast (R := ℂ) (J j i)
  rw [h_PsH, h_JcH, h_PtH]
  -- Goal: pmᵀ * (Jᵀ.map ↑) * (pm.map star) = -(pmᵀ * (J.map ↑) * pm.map star).
  rw [hJ]
  -- Goal: pmᵀ * ((-J).map ↑) * (pm.map star) = -(pmᵀ * (J.map ↑) * pm.map star).
  have h_neg_map : (-J).map ((↑) : ℤ → ℂ) = -(J.map ((↑) : ℤ → ℂ)) := by
    ext i j
    show ((↑) : ℤ → ℂ) ((-J) i j) = -(((↑) : ℤ → ℂ) (J i j))
    show ((↑) : ℤ → ℂ) (-(J i j)) = -(((↑) : ℤ → ℂ) (J i j))
    push_cast
    ring
  rw [h_neg_map, Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc]

/-- **`i • M` is Hermitian.** With `M := periodMatrixForm pm J`, the
matrix `(Complex.I : ℂ) • M` is Hermitian whenever `J` is
anti-symmetric. -/
theorem iPeriodMatrixForm_isHermitian
    (pm : Matrix ι κ ℂ) (J : Matrix ι ι ℤ) (hJ : Jᵀ = -J) :
    ((Complex.I : ℂ) • periodMatrixForm pm J).IsHermitian := by
  change ((Complex.I : ℂ) • periodMatrixForm pm J)ᴴ
      = (Complex.I : ℂ) • periodMatrixForm pm J
  rw [Matrix.conjTranspose_smul, periodMatrixForm_isAntiHermitian pm J hJ]
  -- Goal: star Complex.I • (-(periodMatrixForm pm J))
  --     = Complex.I • periodMatrixForm pm J.
  have h_starI : (star (Complex.I : ℂ) : ℂ) = -Complex.I := by
    change (starRingEnd ℂ) Complex.I = -Complex.I
    exact Complex.conj_I
  rw [h_starI, neg_smul, smul_neg, neg_neg]

end JacobianChallenge

end
