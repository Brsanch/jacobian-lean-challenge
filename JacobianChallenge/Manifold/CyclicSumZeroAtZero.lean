/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CyclicSumSymmetry

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `cyclicSum h ω k 0 = 0` for `k ≥ 2`

First-order vanishing of `cyclicSum h ω k` at `ξ = 0` for any
function `h` and primitive `k`-th root of unity `ω` with `k ≥ 2`.
Immediate from the symmetry `cyclicSum_omega_shift` evaluated at
`ξ = 0`: it gives `cyclicSum h ω k 0 = ω⁻¹ · cyclicSum h ω k 0`,
so `(1 - ω⁻¹) · cyclicSum h ω k 0 = 0`, and `ω⁻¹ ≠ 1` (since
`ω ≠ 1` for `k ≥ 2`).

This is the first step of the chain that ultimately gives
`cyclicSum h ω k ξ = O(ξ^{k-1})` near 0 for analytic `h`. Continuing
via `analyticOrderAt`-based factorisation produces successive
factorisations `cyclicSum h ω k ξ = ξ^j · g_j(ξ)` with `g_j(0) ≠ 0`,
where the symmetry forces `k ∣ j + 1`, i.e. `j ≥ k - 1` is the lowest
possible order.

## What this file ships

* `cyclicSum_zero_eq_zero` — for `ω` a primitive `k`-th root of unity
  with `k ≥ 2`, `cyclicSum h ω k 0 = 0` for every `h`.

No `sorry`, no `axiom`. -/

namespace JacobianChallenge

/-- **First-order vanishing.** For `ω` a primitive `k`-th root of
unity with `2 ≤ k` in any field, `cyclicSum h ω k 0 = 0` for every
function `h : K → K`. Proof: by the symmetry `cyclicSum_omega_shift`
at `ξ = 0`, `cyclicSum h ω k 0 = ω⁻¹ · cyclicSum h ω k 0`; cancel via
`ω⁻¹ ≠ 1` (immediate from `ω ≠ 1`). -/
theorem cyclicSum_zero_eq_zero
    {K : Type*} [Field K] {ω : K} {k : ℕ} (hω : IsPrimitiveRoot ω k)
    (hk : 2 ≤ k) (h : K → K) :
    cyclicSum h ω k 0 = 0 := by
  have hk_pos : 0 < k := by linarith
  -- Symmetry at ξ = 0: cyclicSum (ω·0) = ω⁻¹ · cyclicSum 0.
  have h_sym := cyclicSum_omega_shift hω hk_pos h 0
  rw [mul_zero] at h_sym
  -- h_sym : cyclicSum h ω k 0 = ω⁻¹ · cyclicSum h ω k 0.
  have hω_ne_zero : ω ≠ 0 := by
    intro h_zero
    have : (0 : K) ^ k = 1 := by rw [← h_zero]; exact hω.pow_eq_one
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hk_pos)] at this
    exact zero_ne_one this
  have hω_ne_one : ω ≠ 1 := hω.ne_one (by linarith)
  have hω_inv_ne_one : ω⁻¹ ≠ 1 := by
    intro h_inv_one
    apply hω_ne_one
    have : ω * ω⁻¹ = ω * 1 := by rw [h_inv_one]
    rw [mul_inv_cancel₀ hω_ne_zero, mul_one] at this
    exact this.symm
  have h_factor : (1 - ω⁻¹) * cyclicSum h ω k 0 = 0 := by
    linear_combination h_sym
  -- 1 - ω⁻¹ ≠ 0 since ω⁻¹ ≠ 1.
  have h_one_sub_ne : (1 - ω⁻¹ : K) ≠ 0 :=
    sub_ne_zero_of_ne (Ne.symm hω_inv_ne_one)
  exact (mul_eq_zero.mp h_factor).resolve_left h_one_sub_ne

end JacobianChallenge
