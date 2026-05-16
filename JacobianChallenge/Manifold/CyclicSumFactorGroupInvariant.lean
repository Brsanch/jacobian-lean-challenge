/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CyclicSumFactorOmegaInvariant

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Full cyclic-group invariance of the factor `q`

Strengthening of `cyclicSum_factor_pow_k_sub_one_omega_invariant` (chip 3b-3c)
from invariance under `ω` to invariance under all `ω^j` for `j ∈ range k`,
on a *common* neighbourhood of `0`.

This is the form needed for the descent step: an analytic function
invariant under the action of the cyclic group `⟨ω⟩` on its domain
descends to an analytic function of `ξ^k`. The averaging operator
`(P_k q)(ξ) := (1/k) ∑_{j ∈ range k} q(ω^j ξ)` projects onto the
invariant part; together with the orthogonality identity
`isPrimitiveRoot_cyclic_sum_eq` (chip 3b-0), this gives the Taylor
coefficients of `Q` from those of `q`.

Proof: iterate `q(ωξ) = q(ξ)` (chip 3b-3c) `j` times, using continuity
to pull back each step along `ξ ↦ ω · ξ`. The intersection of `k`
eventual statements yields a common eventual statement (`Finset.range k`
is finite). -/

open Filter Topology

namespace JacobianChallenge

/-- **Full cyclic-group invariance.** The analytic factor `q` in
`cyclicSum h ω k ξ = ξ^(k-1) · q(ξ)` is invariant under multiplication
of `ξ` by any power of `ω`, on a common neighbourhood of `0`. -/
theorem cyclicSum_factor_pow_k_sub_one_cyclic_invariant
    {h : ℂ → ℂ} {ω : ℂ} {k : ℕ} (hω : IsPrimitiveRoot ω k) (hk : 2 ≤ k)
    (h_an : AnalyticAt ℂ h 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      (∀ᶠ ξ in 𝓝 (0 : ℂ), cyclicSum h ω k ξ = ξ ^ (k - 1) * q ξ) ∧
      (∀ᶠ ξ in 𝓝 (0 : ℂ), ∀ j ∈ Finset.range k, q (ω ^ j * ξ) = q ξ) := by
  obtain ⟨q, q_an, h_eq, h_inv⟩ :=
    cyclicSum_factor_pow_k_sub_one_omega_invariant hω hk h_an
  refine ⟨q, q_an, h_eq, ?_⟩
  -- For each j ∈ range k, pulling h_inv back j times along ξ ↦ ω·ξ gives
  -- the equation `q (ω^j · ξ) = q ξ` eventually.  We collect all k of these
  -- eventual statements into a single one.
  -- Continuous map ξ ↦ ω · ξ tends to 0 at 0.
  have h_mul_tendsto : Tendsto (fun ξ : ℂ => ω * ξ) (𝓝 (0 : ℂ)) (𝓝 0) := by
    have : Tendsto (fun ξ : ℂ => ω * ξ) (𝓝 0) (𝓝 (ω * 0)) :=
      (continuous_const.mul continuous_id).continuousAt.tendsto
    simpa using this
  -- For each j, prove `∀ᶠ ξ in 𝓝 0, q (ω^j · ξ) = q ξ` by induction on j.
  have h_each : ∀ j, ∀ᶠ ξ in 𝓝 (0 : ℂ), q (ω ^ j * ξ) = q ξ := by
    intro j
    induction j with
    | zero =>
      filter_upwards with ξ
      simp
    | succ n ih =>
      -- Step n → n+1: pull `ih` back along ξ ↦ ω·ξ and combine with `h_inv` at ω·ξ.
      -- ih at ω·ξ: q (ω^n · (ω·ξ)) = q (ω·ξ).
      -- h_inv at ξ: q (ω · ξ) = q ξ.
      -- Combine: q (ω^(n+1) · ξ) = q (ω^n · (ω·ξ)) = q (ω·ξ) = q ξ.
      have h_ih_shift : ∀ᶠ ξ in 𝓝 (0 : ℂ),
          q (ω ^ n * (ω * ξ)) = q (ω * ξ) :=
        h_mul_tendsto.eventually ih
      filter_upwards [h_ih_shift, h_inv] with ξ h1 h2
      have h_rewrite : ω ^ (n + 1) * ξ = ω ^ n * (ω * ξ) := by
        rw [pow_succ]; ring
      rw [h_rewrite, h1, h2]
  -- Collect the `k` eventually-statements over `j ∈ range k` into one.
  have h_collect : ∀ᶠ ξ in 𝓝 (0 : ℂ), ∀ j ∈ Finset.range k, q (ω ^ j * ξ) = q ξ := by
    rw [eventually_all_finset]
    intro j _
    exact h_each j
  exact h_collect

end JacobianChallenge
