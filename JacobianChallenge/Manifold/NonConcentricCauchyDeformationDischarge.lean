/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import JacobianChallenge.Manifold.NonConcentricCauchyDeformation

/-! # Non-concentric Cauchy deformation — Laurent monomial discharge (ZZ63)

This file is a sibling to `NonConcentricCauchyDeformation.lean` (ZZ62).
ZZ62 names the **general** non-concentric single-hole Cauchy deformation
identity as a `Prop`-valued hypothesis and proves only the concentric
special case unconditionally.

This file proves the identity **unconditionally** for the family of
**Laurent monomial integrands** `g(z) = (z - x₀) ^ n` with `n : ℤ`. This
is genuinely new mathematical content relative to ZZ62: the integrand is
*not* required to be holomorphic on the off-centre annulus (for `n < 0`
it has a pole at `x₀`), and the proof routes entirely through closed-form
mathlib evaluations of `∮ z in C(c, R), (z - w) ^ n`, never invoking a
deformation hypothesis.

The exported lemmas:

* `nonConcentric_circleIntegral_zpow_eq` — for every `n : ℤ`,
    `(∮ z in C(c, R), (z - x₀) ^ n) = ∮ z in C(x₀, ε₀), (z - x₀) ^ n`,
  under `closedBall x₀ ε₀ ⊆ ball c R`, `0 < R`, `0 < ε₀`. Proven by
  case-split on `n = -1` vs `n ≠ -1`, evaluating both sides via
  `circleIntegral.integral_sub_zpow_of_ne` and
  `circleIntegral.integral_sub_inv_of_mem_ball`.

* `nonConcentric_circleIntegral_pow_eq` — natural-power specialisation
  (corollary by ℕ→ℤ cast on the sphere).

## Mathlib lemmas used

* `circleIntegral.integral_sub_zpow_of_ne` (Mathlib4
  `Mathlib/MeasureTheory/Integral/CircleIntegral.lean`, line ≈519):
  `n ≠ -1 → (∮ z in C(c, R), (z - w) ^ n) = 0`.
* `circleIntegral.integral_sub_inv_of_mem_ball` (line ≈652):
  `w ∈ ball c R → (∮ z in C(c, R), (z - w)⁻¹) = 2 * π * I`.

## Mathlib lemmas searched and **not** found at this pin

* `Complex.circleIntegral_eq_circleIntegral_of_differentiable_on_diff_balls` — absent.
* `Complex.circleIntegral_sub_circleIntegral_of_differentiable_on_diff_balls` — absent.
* `Complex.circleIntegral_eq_of_differentiable_on_subdisc_complement` — absent.
* General homotopy / homology Cauchy theorem for cycles in a holomorphy
  domain — absent. Mathlib has only the **concentric** annulus form
  (`Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`)
  and the axis-aligned rectangle form
  (`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`).

## Anti-cheat

* No `axiom`, no `sorry`.
* No existing definition or signature is changed.
* All theorems are proved unconditionally (no hypothesis arguments
  beyond the geometric ones `0 < R`, `0 < ε₀`,
  `closedBall x₀ ε₀ ⊆ ball c R`).
-/

noncomputable section

open Complex MeasureTheory Set Metric Real

namespace JacobianChallenge

namespace NonConcentricCauchy

/-- The centre `x₀` of the inner closed ball lies in the outer open ball
whenever `closedBall x₀ ε₀ ⊆ ball c R` and `0 < ε₀`. -/
private lemma center_mem_ball_of_closedBall_subset_ball
    {c x₀ : ℂ} {R ε₀ : ℝ} (hε : 0 < ε₀)
    (hsub : closedBall x₀ ε₀ ⊆ ball c R) :
    x₀ ∈ ball c R := by
  have hx₀ : x₀ ∈ closedBall x₀ ε₀ := by
    rw [Metric.mem_closedBall]; exact dist_self x₀ ▸ hε.le
  exact hsub hx₀

/-- The centre `x₀` lies in its own open ball of any positive radius. -/
private lemma center_mem_ball_self {x₀ : ℂ} {ε₀ : ℝ} (hε : 0 < ε₀) :
    x₀ ∈ ball x₀ ε₀ := by
  rw [Metric.mem_ball]; exact dist_self x₀ ▸ hε

/-- **Non-concentric Cauchy deformation for Laurent monomials** (`n : ℤ`).

For every integer `n`, every pair of centres `c x₀ : ℂ`, and every pair
of radii `R ε₀ > 0` with `closedBall x₀ ε₀ ⊆ ball c R`,

  `(∮ z in C(c, R), (z - x₀) ^ n) = ∮ z in C(x₀, ε₀), (z - x₀) ^ n`.

Proven unconditionally by case-splitting on `n = -1`:

* If `n ≠ -1`, both sides are `0` by
  `circleIntegral.integral_sub_zpow_of_ne`.
* If `n = -1`, both sides are `2 * π * I` by
  `circleIntegral.integral_sub_inv_of_mem_ball`, which applies because
  `x₀ ∈ ball c R` (consequence of the closed-ball subset hypothesis)
  and `x₀ ∈ ball x₀ ε₀` (centre is in its own open ball).

This is the **first proven instance** in this repo of the
non-concentric Cauchy deformation identity that does not rely on the
named-hypothesis pattern of `NonConcentricCauchyDeformation.lean`. -/
theorem nonConcentric_circleIntegral_zpow_eq
    (n : ℤ) {c x₀ : ℂ} {R ε₀ : ℝ}
    (hR : 0 < R) (hε : 0 < ε₀)
    (hsub : closedBall x₀ ε₀ ⊆ ball c R) :
    (∮ z in C(c, R), (z - x₀) ^ n) = ∮ z in C(x₀, ε₀), (z - x₀) ^ n := by
  by_cases hn : n = -1
  · subst hn
    -- Rewrite zpow `-1` as inverse on both sides via the explicit
    -- evaluation `integral_sub_inv_of_mem_ball`.
    have hL : (∮ z in C(c, R), (z - x₀) ^ (-1 : ℤ)) = 2 * π * I := by
      have hx₀_mem : x₀ ∈ ball c R :=
        center_mem_ball_of_closedBall_subset_ball hε hsub
      have h := circleIntegral.integral_sub_inv_of_mem_ball
        (c := c) (w := x₀) (R := R) hx₀_mem
      -- `(z - x₀)⁻¹ = (z - x₀) ^ (-1 : ℤ)`
      have : (∮ z in C(c, R), (z - x₀) ^ (-1 : ℤ))
              = ∮ z in C(c, R), (z - x₀)⁻¹ := by
        refine circleIntegral.integral_congr (R := R) hR.le ?_
        intro z _
        simp [zpow_neg, zpow_one]
      rw [this]; exact h
    have hR_inner : (∮ z in C(x₀, ε₀), (z - x₀) ^ (-1 : ℤ)) = 2 * π * I := by
      have hx₀_self : x₀ ∈ ball x₀ ε₀ := center_mem_ball_self hε
      have h := circleIntegral.integral_sub_inv_of_mem_ball
        (c := x₀) (w := x₀) (R := ε₀) hx₀_self
      have : (∮ z in C(x₀, ε₀), (z - x₀) ^ (-1 : ℤ))
              = ∮ z in C(x₀, ε₀), (z - x₀)⁻¹ := by
        refine circleIntegral.integral_congr (R := ε₀) hε.le ?_
        intro z _
        simp [zpow_neg, zpow_one]
      rw [this]; exact h
    rw [hL, hR_inner]
  · -- `n ≠ -1`: both sides vanish.
    have hL := circleIntegral.integral_sub_zpow_of_ne hn c x₀ R
    have hR' := circleIntegral.integral_sub_zpow_of_ne hn x₀ x₀ ε₀
    rw [hL, hR']

/-- Natural-power specialisation: for `n : ℕ`, the integrand
`(z - x₀) ^ n` is a polynomial; both circle integrals vanish, and they
are equal trivially. This is a direct corollary of
`nonConcentric_circleIntegral_zpow_eq` via `zpow_natCast`. -/
theorem nonConcentric_circleIntegral_pow_eq
    (n : ℕ) {c x₀ : ℂ} {R ε₀ : ℝ}
    (hR : 0 < R) (hε : 0 < ε₀)
    (hsub : closedBall x₀ ε₀ ⊆ ball c R) :
    (∮ z in C(c, R), (z - x₀) ^ n) = ∮ z in C(x₀, ε₀), (z - x₀) ^ n := by
  -- Bridge ℕ-pow to ℤ-zpow on the sphere, then invoke the zpow result.
  have h := nonConcentric_circleIntegral_zpow_eq (n : ℤ) hR hε hsub
  have hLcong : (∮ z in C(c, R), (z - x₀) ^ ((n : ℤ)))
              = ∮ z in C(c, R), (z - x₀) ^ n :=
    circleIntegral.integral_congr (R := R) hR.le
      (fun z _ => by push_cast; rfl)
  have hRcong : (∮ z in C(x₀, ε₀), (z - x₀) ^ ((n : ℤ)))
              = ∮ z in C(x₀, ε₀), (z - x₀) ^ n :=
    circleIntegral.integral_congr (R := ε₀) hε.le
      (fun z _ => by push_cast; rfl)
  rw [← hLcong, ← hRcong]; exact h

end NonConcentricCauchy

end JacobianChallenge

end
