/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AnalyticLocalFactorization
import JacobianChallenge.Manifold.AnalyticKthRoot

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Hurwitz local normal form `g(z) - w₀ = ψ(z)^k`

Composes `analytic_local_factorization` (giving `g - w₀ = (z-x₀)^k · u`
with `u(x₀) ≠ 0`) and `analytic_kth_root_of_nonvanishing` (giving an
analytic `r` with `r^k = u` on a disc) to produce the **Hurwitz local
normal form**:

  `∃ ψ analytic at x₀, ψ(x₀) = 0, ψ'(x₀) ≠ 0,`
  `      and  g(z) - w₀ = ψ(z)^k  on a disc.`

Concretely, `ψ(z) := (z - x₀) · r(z)`. Then
* `ψ(x₀) = 0 · r(x₀) = 0`,
* `ψ(z)^k = (z - x₀)^k · r(z)^k = (z - x₀)^k · u(z) = g(z) - w₀`,
* `deriv ψ x₀ = r(x₀) ≠ 0` (since `r(x₀)^k = u(x₀) ≠ 0`).

This is the classical Hurwitz normal form, the analytic local model for
any analytic `g` near a point of order `k`. Downstream chips use this
to set up the source-side k-fold cover and apply the cyclic-sum-factor
descent to the chart coefficient of α.

No `sorry`, no `axiom`. -/

open Complex Metric Filter Topology

namespace JacobianChallenge
namespace Manifold

/-- **Hurwitz local normal form.**

If `g : ℂ → ℂ` is analytic at `x₀` with `g x₀ = w₀` and the analytic
order of `g - w₀` at `x₀` equals `k : ℕ` with `k ≥ 1`, then on a closed
disc `closedBall x₀ R` (`R > 0`) there is an analytic function `ψ` with

* `ψ x₀ = 0`,
* `deriv ψ x₀ ≠ 0` (so `ψ` is a local biholomorphism at `x₀`),
* `g z - w₀ = ψ z ^ k` for all `z ∈ closedBall x₀ R`.

The construction is `ψ z := (z - x₀) · r z` where `r` is the analytic
`k`-th root of the non-vanishing factor `u` from
`analytic_local_factorization`. -/
theorem hurwitz_local_form
    {g : ℂ → ℂ} {x₀ w₀ : ℂ} {k : ℕ}
    (hk : 1 ≤ k)
    (hg : AnalyticAt ℂ g x₀)
    (h_w₀ : g x₀ = w₀)
    (hord : analyticOrderAt (fun z => g z - w₀) x₀ = (k : ℕ∞)) :
    ∃ R : ℝ, 0 < R ∧ ∃ ψ : ℂ → ℂ,
      AnalyticOnNhd ℂ ψ (Metric.closedBall x₀ R) ∧
      ψ x₀ = 0 ∧ deriv ψ x₀ ≠ 0 ∧
      ∀ z ∈ Metric.closedBall x₀ R, g z - w₀ = (ψ z) ^ k := by
  -- Step 1. Factor `g - w₀ = (z - x₀)^k · u` with `u(x₀) ≠ 0`.
  obtain ⟨R₁, hR₁_pos, u, hu_an, hu_x₀_ne, h_fact⟩ :=
    analytic_local_factorization hk hg h_w₀ hord
  -- Step 2. Take an analytic `k`-th root of `u`: `r^k = u` on a smaller disc.
  obtain ⟨r, R₂, hR₂_pos, hR₂_le, hr_an, hr_pow⟩ :=
    analytic_kth_root_of_nonvanishing hR₁_pos hu_an hu_x₀_ne hk
  -- The Hurwitz factor.
  refine ⟨R₂, hR₂_pos, fun z => (z - x₀) * r z, ?_, ?_, ?_, ?_⟩
  · -- Analyticity of `z ↦ (z - x₀) · r z` on `closedBall x₀ R₂`.
    intro z hz
    have h_sub_an : AnalyticAt ℂ (fun ζ : ℂ => ζ - x₀) z :=
      (analyticAt_id (𝕜 := ℂ) (z := z)).sub analyticAt_const
    have h_r_an : AnalyticAt ℂ r z := hr_an z hz
    exact h_sub_an.mul h_r_an
  · -- `ψ x₀ = 0`.
    simp
  · -- `deriv ψ x₀ ≠ 0`. Compute: `ψ z = (z - x₀) · r z`, so
    -- `deriv ψ x₀ = 1 · r(x₀) + 0 · r'(x₀) = r(x₀)`, non-zero since
    -- `r(x₀)^k = u(x₀) ≠ 0`.
    have hr_x₀_ne : r x₀ ≠ 0 := by
      intro h_zero
      have h_pow : r x₀ ^ k = u x₀ := hr_pow x₀ (Metric.mem_closedBall_self hR₂_pos.le)
      rw [h_zero] at h_pow
      have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
      rw [zero_pow hk_ne] at h_pow
      exact hu_x₀_ne h_pow.symm
    -- `deriv` at `x₀`.
    have h_sub_an_x₀ : AnalyticAt ℂ (fun ζ : ℂ => ζ - x₀) x₀ :=
      (analyticAt_id (𝕜 := ℂ) (z := x₀)).sub analyticAt_const
    have h_r_an_x₀ : AnalyticAt ℂ r x₀ :=
      hr_an x₀ (Metric.mem_closedBall_self hR₂_pos.le)
    have h_r_diff : DifferentiableAt ℂ r x₀ := h_r_an_x₀.differentiableAt
    -- `HasDerivAt (fun z => z - x₀) 1 x₀`.
    have h_sub_hasDeriv : HasDerivAt (fun z : ℂ => z - x₀) 1 x₀ :=
      (hasDerivAt_id x₀).sub_const x₀
    -- `HasDerivAt r (deriv r x₀) x₀`.
    have h_r_hasDeriv : HasDerivAt r (deriv r x₀) x₀ := h_r_diff.hasDerivAt
    -- Pointwise product rule.
    have h_mul_hasDeriv :
        HasDerivAt (fun z : ℂ => (z - x₀) * r z)
          (1 * r x₀ + (x₀ - x₀) * deriv r x₀) x₀ :=
      h_sub_hasDeriv.mul h_r_hasDeriv
    have h_deriv_eq :
        deriv (fun z : ℂ => (z - x₀) * r z) x₀ = r x₀ := by
      have h_val : 1 * r x₀ + (x₀ - x₀) * deriv r x₀ = r x₀ := by ring
      rw [h_mul_hasDeriv.deriv, h_val]
    rw [h_deriv_eq]
    exact hr_x₀_ne
  · -- The factorisation `g z - w₀ = ψ z ^ k`.
    intro z hz
    have hz_R₁ : z ∈ Metric.closedBall x₀ R₁ := by
      rw [Metric.mem_closedBall] at hz ⊢
      exact hz.trans hR₂_le
    have h1 : g z - w₀ = (z - x₀) ^ k * u z := h_fact z hz_R₁
    have h2 : r z ^ k = u z := hr_pow z hz
    rw [h1, ← h2]
    rw [mul_pow]

end Manifold
end JacobianChallenge
