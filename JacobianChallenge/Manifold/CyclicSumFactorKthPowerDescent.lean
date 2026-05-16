/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CyclicSumFactorGroupInvariant
import JacobianChallenge.Manifold.MuKInvariantAnalyticDescent

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Descent of the cyclic-sum factor `q` to a function of `ξ^k`

Composing today's algebraic core with `analyticAt_descent_of_mu_k_invariant`
(`Manifold/MuKInvariantAnalyticDescent.lean`):

* `cyclicSum_factor_pow_k_sub_one_cyclic_invariant` (chip 3b-3d) gives an
  analytic `q : ℂ → ℂ` at `0` with
  `cyclicSum h ω k ξ = ξ ^ (k-1) * q ξ` eventually and
  `∀ ζ ∈ μ_k, q (ζ · ξ) = q ξ` eventually.
* `analyticAt_descent_of_mu_k_invariant` produces an analytic
  `Q : ℂ → ℂ` at `0` with `q ξ = Q (ξ ^ k)` eventually.

Composing:
`cyclicSum h ω k ξ = ξ ^ (k-1) * Q (ξ ^ k)` eventually.

This is the **descent step** of `HolomorphicTraceExtension X` item-(2):
on the source-side k-fold cover near a critical point, the cyclic-sum
that computes the trace 1-form factors through the target coordinate
`v = ξ ^ k` as a function `Q` analytic at the critical value. Combined
with `cotangentEquiv` and Riemann removable singularity (downstream
chips), this gives the holomorphic extension of `f_*ω` across critical
values on `ℙ¹`.

No `sorry`, no `axiom`. -/

open Filter Topology Finset

namespace JacobianChallenge

/-- **Descent of the cyclic-sum factor.** For `h : ℂ → ℂ` analytic at
`0` and `ω` a primitive `k`-th root of unity with `k ≥ 2`, there exists
an analytic `Q : ℂ → ℂ` at `0` such that

`cyclicSum h ω k ξ = ξ ^ (k - 1) * Q (ξ ^ k)`

on a neighbourhood of `0`. -/
theorem cyclicSum_factor_descends_to_kth_power
    {h : ℂ → ℂ} {ω : ℂ} {k : ℕ} (hω : IsPrimitiveRoot ω k) (hk : 2 ≤ k)
    (h_an : AnalyticAt ℂ h 0) :
    ∃ Q : ℂ → ℂ, AnalyticAt ℂ Q 0 ∧
      (∀ᶠ ξ in 𝓝 (0 : ℂ), cyclicSum h ω k ξ = ξ ^ (k - 1) * Q (ξ ^ k)) := by
  -- Step 1: get q from the algebraic core (chip 3b-3d).
  obtain ⟨q, q_an, h_eq, h_inv⟩ :=
    cyclicSum_factor_pow_k_sub_one_cyclic_invariant hω hk h_an
  -- Step 2: convert the eventually-form `∀ᶠ ξ, ∀ j ∈ range k, q (ω^j ξ) = q ξ`
  -- into the descent-form `∀ ζ, ζ^k = 1 → (fun ξ => q (ζ · ξ)) =ᶠ q`.
  have hk_pos : 1 ≤ k := by omega
  have hk_ne : k ≠ 0 := by omega
  haveI : NeZero k := ⟨hk_ne⟩
  have hinv_descent : ∀ ζ : ℂ, ζ ^ k = 1 →
      (fun ξ : ℂ => q (ζ * ξ)) =ᶠ[𝓝 0] q := by
    intro ζ hζ
    -- Pick `i < k` with `ω^i = ζ`.
    obtain ⟨i, hi_lt, hi_eq⟩ := hω.eq_pow_of_pow_eq_one hζ
    -- Specialise the `j`-eventual statement to `j = i`.
    have h_i : ∀ᶠ ξ in 𝓝 (0 : ℂ), q (ω ^ i * ξ) = q ξ := by
      filter_upwards [h_inv] with ξ hξ
      exact hξ i (Finset.mem_range.mpr hi_lt)
    -- Rewrite `ω^i` to `ζ`.
    filter_upwards [h_i] with ξ hξ
    rw [← hi_eq]
    exact hξ
  -- Step 3: apply analytic descent.
  obtain ⟨Q, Q_an, hQ_eq⟩ :=
    Manifold.analyticAt_descent_of_mu_k_invariant (k := k) hk_pos q_an hinv_descent
  -- `hQ_eq : (fun ξ => Q (ξ ^ k)) =ᶠ[𝓝 0] q`
  refine ⟨Q, Q_an, ?_⟩
  -- Step 4: combine `cyclicSum = ξ^(k-1) · q ξ` with `q ξ = Q (ξ^k)`.
  filter_upwards [h_eq, hQ_eq] with ξ h1 h2
  -- h1 : cyclicSum h ω k ξ = ξ ^ (k-1) * q ξ
  -- h2 : Q (ξ ^ k) = q ξ
  rw [h1, ← h2]

end JacobianChallenge
