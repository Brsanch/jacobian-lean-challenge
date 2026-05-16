/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Roots-of-unity orthogonality: cyclic sum identity

For `ω` a primitive `k`-th root of unity (in a field, e.g. `ℂ`) and a
natural exponent `m`, the cyclic sum

`∑_{j ∈ range k} ω ^ (j * m) = if k ∣ m then k else 0`.

This is the algebraic kernel of the n-th-root cancellation argument
used in the `HolomorphicTraceExtension X` item-(2) globalize step: a
holomorphic function `H(z)` evaluated at `ω^j ξ` and summed with
weights `ω^{j r}` projects out the coefficients `a_n` with
`n ≡ -r mod k` from `H`'s power series, giving a power series in `ξ^k`.

## What this file ships

* `complex_primitive_root_cyclic_sum` — the orthogonality identity,
  specialised to `ℂ` for our manifold-trace application but using the
  generic `IsPrimitiveRoot` predicate.

The exact roots-of-unity instance we'll consume downstream is
`Complex.isPrimitiveRoot_exp k h0 : IsPrimitiveRoot (Complex.exp (2 * π * I / k)) k`
from `Mathlib.RingTheory.RootsOfUnity.Complex`.

No `sorry`, no `axiom`. -/

open Finset

namespace JacobianChallenge

/-- **Roots-of-unity orthogonality.** For `ω` a primitive `k`-th root
of unity in a field `K` (with `1 ≤ k`) and any `m : ℕ`, the cyclic
power sum equals `k` when `k ∣ m`, else `0`. -/
theorem isPrimitiveRoot_cyclic_sum_eq
    {K : Type*} [Field K] {ω : K} {k : ℕ} (hω : IsPrimitiveRoot ω k)
    (_hk : 0 < k) (m : ℕ) :
    ∑ j ∈ Finset.range k, ω ^ (j * m) = if k ∣ m then (k : K) else 0 := by
  by_cases hdvd : k ∣ m
  · -- k ∣ m: each ω^(j*m) = (ω^m)^j = 1^j = 1, sum = k.
    simp only [hdvd, if_true]
    have h_each : ∀ j ∈ Finset.range k, ω ^ (j * m) = 1 := by
      intro j _
      have h_pow : ω ^ m = 1 := (hω.pow_eq_one_iff_dvd m).mpr hdvd
      rw [mul_comm, pow_mul, h_pow, one_pow]
    rw [Finset.sum_congr rfl h_each, Finset.sum_const, Finset.card_range]
    simp
  · -- k ∤ m: ω^m ≠ 1, geometric sum vanishes.
    simp only [hdvd, if_false]
    have h_m_pow_ne_one : ω ^ m ≠ 1 := by
      intro h_one
      exact hdvd ((hω.pow_eq_one_iff_dvd m).mp h_one)
    -- Reindex: ∑ j, ω^(j*m) = ∑ j, (ω^m)^j.
    have h_reindex : ∀ j ∈ Finset.range k, ω ^ (j * m) = (ω ^ m) ^ j := by
      intro j _
      rw [mul_comm, pow_mul]
    rw [Finset.sum_congr rfl h_reindex]
    -- Closed form via geom_sum_eq: ∑ j ∈ range k, x^j = (x^k - 1)/(x - 1) for x ≠ 1.
    rw [geom_sum_eq h_m_pow_ne_one k]
    -- (ω^m)^k = ω^(m*k) = (ω^k)^m = 1^m = 1, so numerator = 0.
    have h_mk_pow : (ω ^ m) ^ k = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    rw [h_mk_pow, sub_self, zero_div]

/-- **Specialisation to `ℂ`** via the canonical primitive `k`-th root
`exp(2πi/k)`. This is the form consumed by the
`HolomorphicTraceExtension X` n-th-root cancellation chip. -/
theorem complex_exp_primitive_root_cyclic_sum
    {k : ℕ} (hk : 0 < k) (m : ℕ) :
    let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / k)
    ∑ j ∈ Finset.range k, ω ^ (j * m) = if k ∣ m then (k : ℂ) else 0 := by
  intro ω
  have hω : IsPrimitiveRoot ω k :=
    Complex.isPrimitiveRoot_exp k (Nat.pos_iff_ne_zero.mp hk)
  exact isPrimitiveRoot_cyclic_sum_eq hω hk m

end JacobianChallenge
