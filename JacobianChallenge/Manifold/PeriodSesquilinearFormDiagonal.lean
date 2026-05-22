/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodSesquilinearFormProperties

set_option linter.unusedSectionVars false

/-! # Diagonal of the period sesquilinear form is purely imaginary

For anti-symmetric `J : Matrix (Fin (2g)) (Fin (2g)) ℤ` (`Jᵀ = -J`),
the diagonal value `Q_sq J cycleGens data ω ω` is purely imaginary:
`star(z) = -z` (a purely imaginary number).

Direct corollary of `periodSesquilinearForm.conj_swap` at `ω₀ = ω₁ = ω`.
The matrix-level analog is chip 19a's `iPeriodMatrixForm_isHermitian`
diagonal property.

## What ships

* `periodSesquilinearForm_diagonal_starEq_neg` — `star(z) = -z`.
* `periodSesquilinearForm_diagonal_re_eq_zero` — `(diagonal).re = 0`.
* `iPeriodSesquilinearForm_diagonal_im_eq_zero` — `(I · diagonal).im
  = 0` (the `I` factor makes it purely real).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Complex

namespace JacobianChallenge

universe u

namespace periodSesquilinearForm

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]
  {data : PeriodPairingData X}
  (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
  (J : Matrix (Fin (2 * JacobianChallenge.genus X))
        (Fin (2 * JacobianChallenge.genus X)) ℤ)

/-- **Diagonal is anti-self-conjugate**: for anti-symmetric `J`,
`star (Q_sq J cycleGens data ω ω) = -(Q_sq J cycleGens data ω ω)`. -/
theorem diagonal_starEq_neg (hJ : Jᵀ = -J) (om : HolomorphicOneForm X) :
    star (periodSesquilinearForm cycleGens J om om)
      = -(periodSesquilinearForm cycleGens J om om) := by
  -- From conj_swap: Q_sq J cycleGens ω₀ ω₁ = - star (Q_sq J cycleGens ω₁ ω₀).
  -- At ω₀ = ω₁ = ω: Q_sq J cycleGens ω ω = - star (Q_sq J cycleGens ω ω).
  -- So star (Q_sq diagonal) = - Q_sq diagonal.
  have h := conj_swap cycleGens J hJ om om
  -- h : Q_sq J cycleGens ω ω = - star (Q_sq J cycleGens ω ω).
  -- Star both sides; then star (- star z) = - star (star z) = -z.
  have h_star := congrArg star h
  rw [star_neg, star_star] at h_star
  -- h_star : star (Q_sq J cycleGens ω ω) = - Q_sq J cycleGens ω ω.
  exact h_star

/-- **Diagonal has zero real part.** Direct from `diagonal_starEq_neg`:
`star z = -z` ⟹ `z.re = 0`. -/
theorem diagonal_re_eq_zero (hJ : Jᵀ = -J) (om : HolomorphicOneForm X) :
    (periodSesquilinearForm cycleGens J om om).re = 0 := by
  have h_star := diagonal_starEq_neg cycleGens J hJ om
  -- star z = -z means z.re = -(z.re), i.e., 2 · z.re = 0.
  -- (star z).re = z.re; (-z).re = -(z.re).
  have h_eq : (periodSesquilinearForm cycleGens J om om).re
            = -((periodSesquilinearForm cycleGens J om om).re) := by
    have := congrArg Complex.re h_star
    -- (star z).re = z.re (conjugate preserves real part);
    -- (-z).re = -(z.re).
    rw [show ∀ z : ℂ, (star z).re = z.re from fun z => Complex.conj_re z,
        Complex.neg_re] at this
    exact this
  linarith

/-- **`(I · diagonal).im = 0`** — multiplying the purely-imaginary
diagonal by `I` produces a purely real number. -/
theorem iDiagonal_im_eq_zero (hJ : Jᵀ = -J) (om : HolomorphicOneForm X) :
    ((Complex.I : ℂ) * periodSesquilinearForm cycleGens J om om).im = 0 := by
  -- (I · z).im = I.re · z.im + I.im · z.re = 0 · z.im + 1 · 0 = 0.
  -- Use diagonal_re_eq_zero.
  rw [Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [diagonal_re_eq_zero cycleGens J hJ om]
  ring

end periodSesquilinearForm

end JacobianChallenge

end
