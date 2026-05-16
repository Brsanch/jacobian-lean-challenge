/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalKFoldMultiplicity
import JacobianChallenge.Manifold.AnalyticLocalFactorization
import JacobianChallenge.Manifold.AnalyticKthRoot

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # General-`k` `KthRootSubstitution` discharge

For `g : ℂ → ℂ` analytic at `x₀` with `g x₀ = w₀` and analytic order
`k ≥ 1`, `KthRootSubstitution g x₀ w₀ k` holds. This was the
named-only gap in `Manifold/LocalKFoldMultiplicity.lean` for general
`k ≥ 2` — `k = 1` was already discharged by
`kthRootSubstitution_of_localMultiplicityOne`.

## Construction

Composing:

1. `analytic_local_factorization` (`Manifold/AnalyticLocalFactorization.lean`):
   gives `R > 0` and analytic non-vanishing `u` on `closedBall x₀ R`
   with `g z - w₀ = (z - x₀)^k * u z`.
2. `analytic_kth_root_of_nonvanishing` (`Manifold/AnalyticKthRoot.lean`):
   gives an analytic `r` on a smaller `closedBall x₀ ρ' ⊆ closedBall x₀ R`
   with `r(z)^k = u(z)`.
3. Set `v(z) := (z - x₀) * r(z)`. Then:
   * `v` analytic on `closedBall x₀ ρ'`,
   * `v x₀ = 0`,
   * `deriv v x₀ = r(x₀) ≠ 0` (since `r(x₀)^k = u(x₀) ≠ 0`),
   * `v(z)^k = (z - x₀)^k * r(z)^k = (z - x₀)^k * u(z) = g(z) - w₀`.

This unblocks the n-th-root cancellation argument for the
`HolomorphicTraceExtension X` item-(2) bounded-trace step: at each
preimage `p` of a critical value `v₀` with ramification index `k_p`,
this substitution gives the local biholomorphism `v_p` putting `f`
into the n-th-power normal form `f(z) - v₀ = v_p(z)^{k_p}` on a
chart neighbourhood of `p`.

No `sorry`, no `axiom`. -/

noncomputable section

open Metric

namespace JacobianChallenge

namespace Manifold

/-- **General-`k` discharge of `KthRootSubstitution`.** From the
classical analytic local factorization + analytic `k`-th root branch
(both already in the repo), we build the substitution
`v(z) := (z - x₀) * r(z)` putting `g(z) - w₀` into `k`-th-power form. -/
theorem kthRootSubstitution_general
    {g : ℂ → ℂ} {x₀ w₀ : ℂ} {k : ℕ} (hk : 1 ≤ k)
    (hg : AnalyticAt ℂ g x₀) (h_w₀ : g x₀ = w₀)
    (hord : analyticOrderAt (fun z => g z - w₀) x₀ = (k : ℕ∞)) :
    KthRootSubstitution g x₀ w₀ k := by
  -- Step 1: analytic local factorization.
  obtain ⟨R, hR_pos, u, hu_an, hu_x₀, hfact⟩ :=
    analytic_local_factorization hk hg h_w₀ hord
  -- Step 2: analytic k-th root branch of u on a smaller closed ball.
  obtain ⟨r, ρ', hρ'_pos, hρ'_le, hr_an, hr_pow⟩ :=
    analytic_kth_root_of_nonvanishing hR_pos hu_an hu_x₀ hk
  -- Step 3: build v.
  refine ⟨⟨fun z => (z - x₀) * r z, ρ', hρ'_pos, ?_, ?_, ?_, ?_⟩⟩
  · -- v analytic on closedBall x₀ ρ'.
    intro z hz
    have h_sub_an : AnalyticAt ℂ (fun ζ : ℂ => ζ - x₀) z :=
      analyticAt_id.sub analyticAt_const
    exact h_sub_an.mul (hr_an z hz)
  · -- v x₀ = 0.
    show (x₀ - x₀) * r x₀ = 0
    rw [sub_self, zero_mul]
  · -- deriv v x₀ ≠ 0: deriv v x₀ = r x₀ and r x₀ ≠ 0.
    have hr_x₀_pow : (r x₀) ^ k = u x₀ :=
      hr_pow x₀ (Metric.mem_closedBall_self hρ'_pos.le)
    have hr_x₀_ne : r x₀ ≠ 0 := by
      intro h_zero
      apply hu_x₀
      rw [← hr_x₀_pow, h_zero, zero_pow]
      exact Nat.one_le_iff_ne_zero.mp hk
    -- Compute deriv of v = (· - x₀) * r at x₀.
    have hr_diff : DifferentiableAt ℂ r x₀ :=
      (hr_an x₀ (Metric.mem_closedBall_self hρ'_pos.le)).differentiableAt
    have h_sub_diff : DifferentiableAt ℂ (fun ζ : ℂ => ζ - x₀) x₀ :=
      (differentiableAt_id).sub_const x₀
    have h_deriv :
        deriv (fun z : ℂ => (z - x₀) * r z) x₀ =
          deriv (fun ζ : ℂ => ζ - x₀) x₀ * r x₀ +
            (x₀ - x₀) * deriv r x₀ :=
      deriv_mul h_sub_diff hr_diff
    have h_deriv_sub : deriv (fun ζ : ℂ => ζ - x₀) x₀ = 1 := by
      have : (fun ζ : ℂ => ζ - x₀) = (fun ζ : ℂ => ζ) - (fun _ : ℂ => x₀) := by
        funext ζ; rfl
      rw [this]
      rw [deriv_sub differentiableAt_id (differentiableAt_const _)]
      simp
    rw [h_deriv, h_deriv_sub, one_mul, sub_self, zero_mul, add_zero]
    exact hr_x₀_ne
  · -- v(z)^k = g(z) - w₀.
    intro z hz
    have h_rk : r z ^ k = u z := hr_pow z hz
    -- z ∈ closedBall x₀ ρ' ⊆ closedBall x₀ R, so the factorization applies.
    have hz_R : z ∈ Metric.closedBall x₀ R := by
      have : Metric.closedBall x₀ ρ' ⊆ Metric.closedBall x₀ R :=
        Metric.closedBall_subset_closedBall hρ'_le
      exact this hz
    have h_g : g z - w₀ = (z - x₀) ^ k * u z := hfact z hz_R
    show g z - w₀ = ((z - x₀) * r z) ^ k
    rw [mul_pow, h_rk, h_g]

end Manifold

end JacobianChallenge

end
