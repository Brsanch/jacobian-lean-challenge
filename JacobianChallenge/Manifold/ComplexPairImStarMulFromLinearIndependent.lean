/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! # ℝ-LI of a complex pair forces `Im(star a · b) ≠ 0` (chip 19q)

For two complex numbers `a, b ∈ ℂ`, ℝ-linear independence of
`![a, b] : Fin 2 → ℂ` implies that `Im(star a · b) ≠ 0`. This is
standard linear algebra: identifying `ℂ ≃ₗ[ℝ] ℝ²` via
`z ↦ (z.re, z.im)`, the `2 × 2` ℝ-determinant of the matrix with rows
`a, b` is exactly `a.re · b.im − a.im · b.re = Im(star a · b)`, and a
pair of vectors in `ℝ²` is ℝ-LI iff its determinant is nonzero.

This file closes the *last* gap on the way to making
`HasJacobianHodgeChain (ℂ ⧸ L)` unconditional: chip 19p (file
`HasJacobianHodgeChainComplexTorusFromNonzero.lean`) already reduces
the chain to the *nondegeneracy* condition
`(star (lam₁_complexTorus L) · (lam₂_complexTorus L)).im ≠ 0`, and the
in-tree `basisFin2OfL_realLinearIndependent` from
`PeriodLatticeSymplecticBundleComplexTorus.lean` provides the ℝ-LI
premise for the basis pair on every discrete full-rank ℤ-lattice
`L ≤ ℂ`. Chip 19q is the bridge.

## What this file ships

* `JacobianChallenge.Complex.im_star_mul_ne_zero_of_linearIndependent_pair`
  — the forward implication
  `LinearIndependent ℝ ![a, b] → (star a * b).im ≠ 0`.
* `JacobianChallenge.Complex.linearIndependent_pair_of_im_star_mul_ne_zero`
  — the reverse implication
  `(star a * b).im ≠ 0 → LinearIndependent ℝ ![a, b]`.
* `JacobianChallenge.Complex.linearIndependent_pair_iff_im_star_mul_ne_zero`
  — the biconditional.

No `sorry`, no `axiom`. -/

namespace JacobianChallenge

namespace Complex

open scoped Complex

/-- **ℝ-LI of `(a, b) ∈ ℂ²` forces `Im(star a · b) ≠ 0`.**

The 2 × 2 ℝ-determinant of the matrix with rows `(a.re, a.im)` and
`(b.re, b.im)` is `a.re · b.im − a.im · b.re`, which equals
`(star a · b).im`. A pair of vectors in `ℝ²` is ℝ-LI iff its
determinant is nonzero; the proof here is the contrapositive,
constructing an explicit ℝ-linear relation when the determinant
vanishes.

The case split is on whether `a.re ≠ 0`, `a.im ≠ 0`, or both are zero
(i.e. `a = 0`):

* If `a.re ≠ 0`: the relation `(−b.re) • a + a.re • b = 0` holds
  (both components compute by the determinant hypothesis), and its
  second coefficient `a.re ≠ 0` contradicts ℝ-LI.
* If `a.re = 0` and `a.im ≠ 0`: symmetrically with `(−b.im, a.im)`.
* If both are zero: `a = 0`, and `1 • a + 0 • b = 0` has nonzero
  first coefficient, again contradicting ℝ-LI. -/
theorem im_star_mul_ne_zero_of_linearIndependent_pair
    {a b : ℂ}
    (h : LinearIndependent ℝ (![a, b] : Fin 2 → ℂ)) :
    (star a * b).im ≠ 0 := by
  rw [LinearIndependent.pair_iff] at h
  -- Compute `(star a * b).im = a.re * b.im - a.im * b.re`.
  have h_im_eq : (star a * b).im = a.re * b.im - a.im * b.re := by
    rw [Complex.star_def]
    simp [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  intro h_im_zero
  rw [h_im_eq] at h_im_zero
  -- Case split on `a.re ≠ 0`, then `a.im ≠ 0`.
  by_cases ha_re : a.re ≠ 0
  · -- Case A: `a.re ≠ 0`. Use `(-b.re) • a + a.re • b = 0`.
    have h_lin :
        ((-b.re : ℝ) • a + (a.re : ℝ) • b : ℂ) = 0 := by
      -- Convert ℝ-smul to ℂ-multiplication.
      change (((-b.re : ℝ) : ℂ) * a + ((a.re : ℝ) : ℂ) * b : ℂ) = 0
      apply Complex.ext
      · -- `.re` component: `-b.re * a.re + a.re * b.re = 0`.
        simp [Complex.add_re, Complex.mul_re]; ring
      · -- `.im` component: `-b.re * a.im + a.re * b.im = 0`,
        -- i.e. the determinant identity `h_im_zero`.
        simp [Complex.add_im, Complex.mul_im]; linarith
    exact ha_re (h (-b.re) a.re h_lin).2
  · -- Case B/C: `a.re = 0`.
    push Not at ha_re
    by_cases ha_im : a.im ≠ 0
    · -- Case B: `a.im ≠ 0`. Use `(-b.im) • a + a.im • b = 0`.
      -- Simplify `h_im_zero` using `a.re = 0` for use in the `.re`
      -- component below: it becomes `a.im * b.re = 0`.
      rw [ha_re, zero_mul, zero_sub, neg_eq_zero] at h_im_zero
      have h_lin :
          ((-b.im : ℝ) • a + (a.im : ℝ) • b : ℂ) = 0 := by
        -- Convert ℝ-smul to ℂ-multiplication.
        change (((-b.im : ℝ) : ℂ) * a + ((a.im : ℝ) : ℂ) * b : ℂ) = 0
        apply Complex.ext
        · -- `.re` component: `-b.im * a.re + a.im * b.re = 0`.
          -- `a.re = 0` and `h_im_zero : a.im * b.re = 0`.
          simp [Complex.add_re, Complex.mul_re, ha_re, h_im_zero]
        · -- `.im` component: `-b.im * a.im + a.im * b.im = 0`.
          simp [Complex.add_im, Complex.mul_im]; ring
      exact ha_im (h (-b.im) a.im h_lin).2
    · -- Case C: both `a.re = 0` and `a.im = 0`, so `a = 0`.
      push Not at ha_im
      have ha_zero : a = 0 := Complex.ext ha_re ha_im
      have h_lin : ((1 : ℝ) • a + (0 : ℝ) • b : ℂ) = 0 := by
        simp [ha_zero]
      exact one_ne_zero (h 1 0 h_lin).1

/-- **Reverse direction: `Im(star a · b) ≠ 0 ⟹ ℝ-LI of `(a, b)`.**

If the imaginary part of `star a · b` is nonzero, then the pair
`(a, b) ∈ ℂ²` is ℝ-linearly independent. The proof uses the
determinant identity in ℝ²: a pair of vectors with nonzero
2 × 2 determinant is automatically ℝ-LI.

Given an ℝ-linear relation `s • a + t • b = 0`, take real and
imaginary parts to get two equations on `(s, t)`; their
coefficient matrix is `[[a.re, b.re], [a.im, b.im]]` with
determinant `(star a · b).im ≠ 0`, forcing `(s, t) = (0, 0)`. -/
theorem linearIndependent_pair_of_im_star_mul_ne_zero
    {a b : ℂ}
    (h : (star a * b).im ≠ 0) :
    LinearIndependent ℝ (![a, b] : Fin 2 → ℂ) := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  -- Compute `(star a * b).im = a.re * b.im - a.im * b.re`.
  have h_im_eq : (star a * b).im = a.re * b.im - a.im * b.re := by
    rw [Complex.star_def]
    simp [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [h_im_eq] at h
  -- Convert ℝ-smul to ℂ-multiplication: `s • a = ↑s * a` (definitional).
  have hst' : ((s : ℂ) * a + (t : ℂ) * b : ℂ) = 0 := hst
  -- Take real and imaginary parts of the relation.
  have h_re : s * a.re + t * b.re = 0 := by
    have := congrArg Complex.re hst'
    simpa [Complex.add_re, Complex.mul_re] using this
  have h_im : s * a.im + t * b.im = 0 := by
    have := congrArg Complex.im hst'
    simpa [Complex.add_im, Complex.mul_im] using this
  -- Determinant elimination: `a.im · h_re − a.re · h_im` yields
  -- `t · (a.im · b.re − a.re · b.im) = 0`, i.e.
  -- `t · −((star a · b).im) = 0`, so `t · (star a · b).im = 0`.
  -- Combined with `(star a · b).im ≠ 0`, this gives `t = 0`.
  have h_det : t * (a.re * b.im - a.im * b.re) = 0 := by
    have key :
        a.im * (s * a.re + t * b.re) - a.re * (s * a.im + t * b.im)
          = -(t * (a.re * b.im - a.im * b.re)) := by ring
    rw [h_re, h_im, mul_zero, mul_zero, sub_zero] at key
    linarith
  have ht_zero : t = 0 := by
    rcases mul_eq_zero.mp h_det with h1 | h2
    · exact h1
    · exact absurd h2 h
  refine ⟨?_, ht_zero⟩
  -- Now `s • a = 0`. Since `(star a · b).im ≠ 0`, `a ≠ 0`,
  -- so `s = 0`.
  have ha : a ≠ 0 := by
    intro h_zero
    apply h
    simp [h_zero]
  -- Convert `s • a + 0 • b = 0` to `↑s * a = 0`.
  have hst_simp : ((s : ℂ) * a : ℂ) = 0 := by
    have := hst
    rw [ht_zero] at this
    simpa using this
  rcases mul_eq_zero.mp hst_simp with h1 | h2
  · exact_mod_cast h1
  · exact absurd h2 ha

/-- **Biconditional form.** -/
theorem linearIndependent_pair_iff_im_star_mul_ne_zero {a b : ℂ} :
    LinearIndependent ℝ (![a, b] : Fin 2 → ℂ) ↔ (star a * b).im ≠ 0 :=
  ⟨im_star_mul_ne_zero_of_linearIndependent_pair,
   linearIndependent_pair_of_im_star_mul_ne_zero⟩

end Complex

end JacobianChallenge
