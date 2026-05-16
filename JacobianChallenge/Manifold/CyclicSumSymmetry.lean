/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PrimitiveRootCyclicSum

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Cyclic-sum symmetry: `S(ωξ) = ω⁻¹ S(ξ)`

For `h : ℂ → ℂ` and `ω` a primitive `k`-th root of unity (`k ≥ 1`),
the cyclic sum

`cyclicSum h ω k ξ := ∑_{j ∈ range k} ω^j · h(ω^j · ξ)`

satisfies the `ω`-shift identity

`cyclicSum h ω k (ω · ξ) = ω⁻¹ · cyclicSum h ω k ξ`.

Proof: reindex `j → j-1 mod k`. The shift `ω^j · h(ω^{j+1} ξ)` becomes,
after `i := j+1`, `ω^{i-1} · h(ω^i ξ)`. Summing over `i ∈ {1, ..., k-1, 0}`
(= reindex of `j ∈ {0, ..., k-1}` with one shift) gives `ω⁻¹ · S(ξ)`,
since `ω^k = 1` lets `i = k` (= the wrapped `j = k-1` shifted) be
reinterpreted as `i = 0`.

This is the algebraic kernel of the vanishing-to-order-`(k-1)` argument
for `S` at `ξ = 0`: differentiating both sides `m` times at `ξ = 0`
gives `S^{(m)}(0) · (ω^{m+1} - 1) = 0`, forcing `S^{(m)}(0) = 0` for
`0 ≤ m < k-1` (since `1 ≤ m+1 < k` and `ω` has order `k`).

## What this file ships

* `cyclicSum h ω k ξ` — definition.
* `cyclicSum_omega_shift` — the symmetry identity, generic over a
  primitive `k`-th root of unity in any field.

No `sorry`, no `axiom`. -/

open Finset

namespace JacobianChallenge

/-- The cyclic sum `∑_{j ∈ range k} ω^j · h(ω^j · ξ)`. Defined for any
field `K` and value `ξ : K`. -/
def cyclicSum {K : Type*} [CommRing K] (h : K → K) (ω : K) (k : ℕ) (ξ : K) : K :=
  ∑ j ∈ Finset.range k, ω ^ j * h (ω ^ j * ξ)

/-- **Cyclic-sum symmetry.** For `ω` a primitive `k`-th root of unity
(`k ≥ 1`) in a field, `cyclicSum h ω k (ω · ξ) = ω⁻¹ · cyclicSum h ω k ξ`.

Algebraic identity; no analytic content. The proof reindexes
`j ↦ (j + 1) mod k`, using `ω^k = 1` to wrap the `j = k - 1` term
back to `j = 0`. -/
theorem cyclicSum_omega_shift
    {K : Type*} [Field K] {ω : K} {k : ℕ} (hω : IsPrimitiveRoot ω k)
    (hk : 0 < k) (h : K → K) (ξ : K) :
    cyclicSum h ω k (ω * ξ) = ω⁻¹ * cyclicSum h ω k ξ := by
  -- ω ≠ 0 (as a primitive root in a field).
  have hω_ne : ω ≠ 0 := by
    intro h_zero
    have : (0 : K) ^ k = 1 := by rw [← h_zero]; exact hω.pow_eq_one
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hk)] at this
    exact zero_ne_one this
  -- ω^k = 1.
  have hω_pow_k : ω ^ k = 1 := hω.pow_eq_one
  unfold cyclicSum
  -- LHS: ∑ j, ω^j · h(ω^j · ω · ξ) = ∑ j, ω^j · h(ω^(j+1) · ξ).
  -- Reindex: let i = j + 1 (mod k).  Use Finset.sum_range_succ_comm-style: rewrite
  -- ω^j · h(ω^(j+1) · ξ) = ω^{-1} · ω^(j+1) · h(ω^(j+1) · ξ) =
  -- ω^{-1} · (term at index j+1 in the original sum).
  have h_term : ∀ j : ℕ, ω ^ j * h (ω ^ j * (ω * ξ))
      = ω⁻¹ * (ω ^ (j + 1) * h (ω ^ (j + 1) * ξ)) := by
    intro j
    have h_arg : ω ^ j * (ω * ξ) = ω ^ (j + 1) * ξ := by
      rw [pow_succ]; ring
    have h_left_factor : ω ^ j = ω⁻¹ * ω ^ (j + 1) := by
      have : ω⁻¹ * ω ^ (j + 1) = (ω⁻¹ * ω) * ω ^ j := by
        rw [pow_succ]; ring
      rw [this, inv_mul_cancel₀ hω_ne, one_mul]
    rw [h_arg, h_left_factor]
    ring
  rw [Finset.sum_congr rfl (fun j _ => h_term j)]
  rw [← Finset.mul_sum]
  -- Goal: ω⁻¹ * ∑ j, ω^(j+1) · h(ω^(j+1) · ξ) = ω⁻¹ * ∑ j, ω^j · h(ω^j · ξ).
  -- Reduce to the sum equality.
  congr 1
  -- ∑ j ∈ range k, ω^(j+1) · h(ω^(j+1) · ξ) = ∑ j ∈ range k, ω^j · h(ω^j · ξ).
  -- Use Finset.sum_range_succ_comm or direct bijection.
  -- LHS = ∑_{j=0}^{k-1} ω^(j+1) · h(ω^(j+1) · ξ) = ∑_{i=1}^{k} ω^i · h(ω^i · ξ)
  --     = (∑_{i=0}^{k-1} ω^i · h(ω^i · ξ)) - (ω^0 · h(ω^0 · ξ)) + (ω^k · h(ω^k · ξ))
  --     = RHS - h(ξ) + 1 · h(ξ) (since ω^k = 1)
  --     = RHS. ✓
  have h_sum_shift :
      ∑ j ∈ Finset.range k, ω ^ (j + 1) * h (ω ^ (j + 1) * ξ)
        = ∑ j ∈ Finset.range k, ω ^ j * h (ω ^ j * ξ) := by
    have h_extended :
        (∑ j ∈ Finset.range k, ω ^ (j + 1) * h (ω ^ (j + 1) * ξ))
          + ω ^ 0 * h (ω ^ 0 * ξ)
          = (∑ j ∈ Finset.range k, ω ^ j * h (ω ^ j * ξ))
            + ω ^ k * h (ω ^ k * ξ) := by
      -- Both sides equal ∑_{j=0}^{k} ω^j · h(ω^j · ξ): LHS reindexes 1..k+0 = 0..k,
      -- RHS is 0..k-1 plus the k term.
      have h_lhs : (∑ j ∈ Finset.range k, ω ^ (j + 1) * h (ω ^ (j + 1) * ξ))
              + ω ^ 0 * h (ω ^ 0 * ξ)
          = ∑ j ∈ Finset.range (k + 1), ω ^ j * h (ω ^ j * ξ) := by
        rw [Finset.sum_range_succ' (fun j => ω ^ j * h (ω ^ j * ξ)) k]
      have h_rhs : (∑ j ∈ Finset.range k, ω ^ j * h (ω ^ j * ξ))
              + ω ^ k * h (ω ^ k * ξ)
          = ∑ j ∈ Finset.range (k + 1), ω ^ j * h (ω ^ j * ξ) := by
        rw [Finset.sum_range_succ (fun j => ω ^ j * h (ω ^ j * ξ)) k]
      rw [h_lhs, h_rhs]
    -- Use ω^k = 1 and ω^0 = 1.
    have h_omega_k : ω ^ k * h (ω ^ k * ξ) = ω ^ 0 * h (ω ^ 0 * ξ) := by
      rw [hω_pow_k, pow_zero]
    rw [h_omega_k] at h_extended
    exact add_right_cancel h_extended
  exact h_sum_shift

end JacobianChallenge
