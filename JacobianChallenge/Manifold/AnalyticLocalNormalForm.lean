/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import JacobianChallenge.Manifold.AnalyticLocalFactorization
import JacobianChallenge.Manifold.AnalyticKthRoot

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Hurwitz local normal form for an analytic map (ZZ151 probe)

If `f : ℂ → ℂ` is analytic at `x₀`, with `f x₀ = w₀` and the analytic order
of `f - w₀` at `x₀` equals a natural number `k ≥ 1`, then there is an
analytic local biholomorphism `ψ` near `x₀` with `ψ x₀ = 0`,
`deriv ψ x₀ ≠ 0`, and

  `f z = w₀ + (ψ z) ^ k`

on a closed disk around `x₀`. This is the local model used by the
Hurwitz theorem and by every "branched-cover" argument: locally a
non-constant analytic map looks like the `k`-th power map up to an
analytic change of coordinates.

## Construction

Combine two repo theorems:

* `analytic_local_factorization` (file `AnalyticLocalFactorization.lean`)
  gives `f z - w₀ = (z - x₀) ^ k * u z` on a closed ball of radius `R`,
  with `u` analytic and `u x₀ ≠ 0`.
* `analytic_kth_root_of_nonvanishing` (file `AnalyticKthRoot.lean`)
  gives, on a (possibly smaller) closed ball of radius `ρ'`, an analytic
  function `r : ℂ → ℂ` with `r z ^ k = u z`.

Setting `ψ z := (z - x₀) * r z`, we get on the smaller ball:
  `(ψ z) ^ k = (z - x₀) ^ k * (r z) ^ k = (z - x₀) ^ k * u z = f z - w₀`,
which rearranges to `f z = w₀ + (ψ z) ^ k`. Analyticity of `ψ` is the
product of the affine map `z ↦ z - x₀` with the analytic `r`. We also
record `ψ x₀ = 0` and `deriv ψ x₀ = r x₀ ≠ 0`, the standard input to
the inverse function theorem (and hence to a local biholomorphism
witness, which we do not package here).

## Anti-cheat

* No `axiom`, no `sorry`.
* No signature change to any pre-existing definition or theorem.
* Adds one new theorem in a new file, imported into the manifest.
-/

noncomputable section

open scoped Topology
open Set Filter Metric

namespace JacobianChallenge
namespace Manifold

/-- **Hurwitz local normal form for an analytic map.**

If `f : ℂ → ℂ` is analytic at `x₀` with `f x₀ = w₀` and
`analyticOrderAt (f - w₀) x₀ = k` for some natural `k ≥ 1`, then there
exist `ρ > 0` and an analytic function `ψ : ℂ → ℂ` on
`closedBall x₀ ρ` with

* `ψ x₀ = 0`,
* `deriv ψ x₀ ≠ 0` (the local-biholomorphism input to the inverse
  function theorem), and
* `f z = w₀ + (ψ z) ^ k` for every `z ∈ closedBall x₀ ρ`. -/
theorem analytic_local_normal_form
    {f : ℂ → ℂ} {x₀ w₀ : ℂ} {k : ℕ}
    (hk : 1 ≤ k)
    (hf : AnalyticAt ℂ f x₀)
    (h_w₀ : f x₀ = w₀)
    (hord : analyticOrderAt (fun z => f z - w₀) x₀ = (k : ℕ∞)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ ψ : ℂ → ℂ,
      AnalyticOnNhd ℂ ψ (Metric.closedBall x₀ ρ) ∧
      ψ x₀ = 0 ∧
      deriv ψ x₀ ≠ 0 ∧
      ∀ z ∈ Metric.closedBall x₀ ρ, f z = w₀ + (ψ z) ^ k := by
  classical
  -- Step 1: factorise `f - w₀ = (z - x₀)^k * u z` with `u x₀ ≠ 0`.
  obtain ⟨R, hR_pos, u, hu_an, hu_x₀, hu_eq⟩ :=
    analytic_local_factorization (g := f) (x₀ := x₀) (w₀ := w₀) (k := k)
      hk hf h_w₀ hord
  -- Step 2: take an analytic `k`-th root of `u` on a smaller ball.
  obtain ⟨r, ρ', hρ'_pos, hρ'_le, hr_an, hr_eq⟩ :=
    analytic_kth_root_of_nonvanishing (u := u) (x₀ := x₀) (ρ := R) (k := k)
      hR_pos hu_an hu_x₀ hk
  -- The shrunken ball lies inside the bigger one.
  have hsubset : Metric.closedBall x₀ ρ' ⊆ Metric.closedBall x₀ R :=
    Metric.closedBall_subset_closedBall hρ'_le
  -- Step 3: define ψ z = (z - x₀) * r z.
  refine ⟨ρ', hρ'_pos, fun z => (z - x₀) * r z, ?hψ_an, ?hψ0, ?hψ_deriv, ?hψ_eq⟩
  · -- analyticity of ψ on closedBall x₀ ρ'
    intro z hz
    have h_id : AnalyticAt ℂ (fun w : ℂ => w - x₀) z :=
      (analyticAt_id : AnalyticAt ℂ (fun w : ℂ => w) z).sub analyticAt_const
    have h_r : AnalyticAt ℂ r z := hr_an z hz
    exact h_id.mul h_r
  · -- ψ x₀ = 0
    show (x₀ - x₀) * r x₀ = 0
    rw [sub_self, zero_mul]
  · -- deriv ψ x₀ ≠ 0
    -- ψ'(x₀) = r x₀, computed via the product rule applied to (z - x₀) * r z.
    -- Differentiability of the affine factor:
    have h_subAt : HasDerivAt (fun w : ℂ => w - x₀) 1 x₀ :=
      (hasDerivAt_id x₀).sub_const x₀
    -- Differentiability of r at x₀ (it is analytic on the closed ball, hence at x₀):
    have hr_x₀ : AnalyticAt ℂ r x₀ := hr_an x₀ (Metric.mem_closedBall_self hρ'_pos.le)
    have h_rDiffAt : DifferentiableAt ℂ r x₀ := hr_x₀.differentiableAt
    have h_rAt : HasDerivAt r (deriv r x₀) x₀ := h_rDiffAt.hasDerivAt
    -- Product rule: HasDerivAt (z-x₀)·r(z) at x₀.
    have h_prodAt :
        HasDerivAt (fun z : ℂ => (z - x₀) * r z)
          (1 * r x₀ + (x₀ - x₀) * deriv r x₀) x₀ :=
      h_subAt.mul h_rAt
    -- Simplify the derivative value.
    have h_val : 1 * r x₀ + (x₀ - x₀) * deriv r x₀ = r x₀ := by
      rw [sub_self, zero_mul, add_zero, one_mul]
    have h_prodAt' :
        HasDerivAt (fun z : ℂ => (z - x₀) * r z) (r x₀) x₀ := by
      rw [← h_val]; exact h_prodAt
    have h_deriv : deriv (fun z : ℂ => (z - x₀) * r z) x₀ = r x₀ :=
      h_prodAt'.deriv
    rw [h_deriv]
    -- r x₀ ≠ 0 since r x₀ ^ k = u x₀ ≠ 0.
    intro hr0
    have h_pow_eq : (r x₀) ^ k = u x₀ :=
      hr_eq x₀ (Metric.mem_closedBall_self hρ'_pos.le)
    rw [hr0, zero_pow (Nat.one_le_iff_ne_zero.mp hk)] at h_pow_eq
    exact hu_x₀ h_pow_eq.symm
  · -- f z = w₀ + ψ(z)^k on closedBall x₀ ρ'
    intro z hz
    have h_pow : (r z) ^ k = u z := hr_eq z hz
    have h_fact : f z - w₀ = (z - x₀) ^ k * u z := hu_eq z (hsubset hz)
    -- ψ(z)^k = ((z-x₀)·r z)^k = (z-x₀)^k · (r z)^k = (z-x₀)^k · u z = f z - w₀.
    have h_psi_pow : ((z - x₀) * r z) ^ k = f z - w₀ := by
      rw [mul_pow, h_pow, ← h_fact]
    -- Conclude.
    have : f z = w₀ + ((z - x₀) * r z) ^ k := by
      rw [h_psi_pow]; ring
    exact this

end Manifold
end JacobianChallenge

end
