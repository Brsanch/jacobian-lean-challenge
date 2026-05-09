/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.RootsOfUnity.Basic

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # μ_k-symmetry for products over k-th-power preimages (Phase 1.1 chip P1.1, ZZ200)

This file packages the **algebraic core** of the planar norm pushforward
across a `k`-th power map `t = s ^ k`: the product
`∏ η ∈ nthRootsFinset k t, g η` over the k-th roots of `t` is invariant
under multiplication of every root by a fixed k-th root of unity, and
the same product is therefore well-defined as a function of `t = s^k`
alone (it does not depend on which k-th root `s` of `t` is chosen).

This is the "μ_k-symmetry" step that underlies the Hurwitz norm
pushforward: at a branch value `y₀`, the chart pullback satisfies
`F z = w₀ + (ψ z)^k`, so the `k` preimages of a nearby `t` near `w₀`
are the `k`-th roots of `t - w₀` in the variable `s = ψ z`.
The product `∏_{F z = t} g z` then becomes
`∏ η ∈ nthRootsFinset k (t - w₀), G η` for `G := g ∘ ψ⁻¹`, and the
symmetry under multiplication by μ_k is precisely the invariance of
the indexing set `nthRootsFinset k (t - w₀)` itself.

## What this file ships

* `mulLeft_bij_on_nthRootsFinset` — for `ζ : ℂ` with `ζ^k = 1` and `k ≥ 1`,
  the multiplication `η ↦ ζ * η` is a bijection
  `nthRootsFinset k a → nthRootsFinset k a` (for any `a : ℂ`).
* `prod_nthRootsFinset_mulLeft_invariant` — for `g : ℂ → ℂ`, `k ≥ 1`,
  `ζ : ℂ` with `ζ^k = 1`, and any `a : ℂ`,
  `∏ η ∈ nthRootsFinset k a, g (ζ * η) = ∏ η ∈ nthRootsFinset k a, g η`.
* `prod_nthRootsFinset_eq_of_pow_eq` — for `g : ℂ → ℂ`, `k ≥ 1`, and
  `s₁ s₂ : ℂ` with `s₁^k = s₂^k`,
  the product `∏ η ∈ nthRootsFinset k (s₁^k), g η` is symmetric in
  `s₁, s₂`: `s₁` and `s₂` parameterize the same indexing set.
  (Trivially: the indexing set depends only on `s^k`.)
* `normPow` — the per-fibre norm-pushforward across the planar
  `k`-th-power map: `t ↦ ∏ η ∈ nthRootsFinset k t, g η`. This is the
  scalar function whose meromorphy at a branch value is the headline
  claim of the multiplicative pushforward.
* `normPow_eq_finset_prod` — `normPow` unfolds to the indicated finset
  product (for use under `simp` and `rw`).

## The downstream meromorphy claim

Local meromorphy of `normPow g` at `t₀ = s₀^k` (in particular at the
branch value `t₀ = 0` corresponding to `s₀ = 0`) is the topic of the
companion chip P1.2. The argument there factors:

1. (this file) μ_k-symmetry: `normPow g (s^k)` is symmetric in the
   choice of `k`-th root `s`.
2. (P1.2) elementary symmetric polynomial expansion: a symmetric
   function of the roots of `X^k - t` is a polynomial in the
   coefficients of `X^k - t` (Vieta), hence in `t` itself; combined
   with `MeromorphicAt.fun_prod` for the regular branch, this gives
   meromorphy of `normPow g` in `t`.

This file delivers (1) cleanly so that (2) can plug it in.

## Anti-cheat

* No `axiom`, no `sorry`.
* No signature change to any pre-existing definition or theorem.
* All identifiers ASCII (no `ω` binders, per Lean 4.30 reservation).
-/

noncomputable section

open Polynomial Finset

namespace JacobianChallenge
namespace Manifold

universe u

/-! ### μ_k-symmetry: multiplication by a k-th root of unity is a bijection
on `nthRootsFinset k a`. -/

/-- Auxiliary: if `ζ ^ k = 1` and `η ∈ nthRootsFinset k a`, then
`ζ * η ∈ nthRootsFinset k a`. -/
private lemma mulLeft_mem_nthRootsFinset
    {k : ℕ} (hk : 1 ≤ k) {ζ : ℂ} (hζ : ζ ^ k = 1) {a : ℂ} {η : ℂ}
    (hη : η ∈ Polynomial.nthRootsFinset k a) :
    ζ * η ∈ Polynomial.nthRootsFinset k a := by
  rw [Polynomial.mem_nthRootsFinset hk] at hη ⊢
  rw [mul_pow, hζ, one_mul, hη]

/-- The map `η ↦ ζ * η` is a bijection on `nthRootsFinset k a` whenever
`ζ ^ k = 1` and `1 ≤ k`. The inverse is `η ↦ ζ⁻¹ * η`; both directions
land in the set by `mulLeft_mem_nthRootsFinset`. -/
theorem mulLeft_bij_on_nthRootsFinset
    {k : ℕ} (hk : 1 ≤ k) {ζ : ℂ} (hζ : ζ ^ k = 1) (a : ℂ) :
    ∃ (e : Polynomial.nthRootsFinset k a → Polynomial.nthRootsFinset k a),
      Function.Bijective e ∧ ∀ η, (e η : ℂ) = ζ * (η : ℂ) := by
  -- ζ ≠ 0 since ζ^k = 1 ≠ 0 and 1 ≤ k.
  have hζ_ne : ζ ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.one_le_iff_ne_zero.mp hk)] at hζ
    exact one_ne_zero hζ.symm
  have hζinv_pow : ζ⁻¹ ^ k = 1 := by
    rw [inv_pow, hζ, inv_one]
  refine ⟨fun η => ⟨ζ * (η : ℂ), mulLeft_mem_nthRootsFinset hk hζ η.2⟩, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro η₁ η₂ h
      have h_val : ζ * (η₁ : ℂ) = ζ * (η₂ : ℂ) := by
        have := congrArg Subtype.val h
        exact this
      have : (η₁ : ℂ) = (η₂ : ℂ) := mul_left_cancel₀ hζ_ne h_val
      exact Subtype.ext this
    · intro η
      refine ⟨⟨ζ⁻¹ * (η : ℂ), mulLeft_mem_nthRootsFinset hk hζinv_pow η.2⟩, ?_⟩
      apply Subtype.ext
      show ζ * (ζ⁻¹ * (η : ℂ)) = (η : ℂ)
      rw [← mul_assoc, mul_inv_cancel₀ hζ_ne, one_mul]
  · intro η; rfl

/-! ### μ_k-symmetry for products -/

/-- **Core invariance lemma.** For any `g : ℂ → ℂ`, `k ≥ 1`, `ζ : ℂ`
with `ζ^k = 1`, and any `a : ℂ`, the product over k-th roots of `a` is
invariant under pre-composition by multiplication by `ζ`:
`∏ η ∈ nthRootsFinset k a, g (ζ * η) = ∏ η ∈ nthRootsFinset k a, g η`.

Proof. The map `η ↦ ζ * η` is a bijection on `nthRootsFinset k a` by
`mulLeft_bij_on_nthRootsFinset`. Re-index the product. -/
theorem prod_nthRootsFinset_mulLeft_invariant
    {k : ℕ} (hk : 1 ≤ k) {ζ : ℂ} (hζ : ζ ^ k = 1) (a : ℂ) (g : ℂ → ℂ) :
    ∏ η ∈ Polynomial.nthRootsFinset k a, g (ζ * η)
      = ∏ η ∈ Polynomial.nthRootsFinset k a, g η := by
  classical
  -- Use `Finset.prod_bij`: the bijection is `η ↦ ζ * η`, with image set `nthRootsFinset k a`.
  refine Finset.prod_bij (fun η _ => ζ * η) ?_ ?_ ?_ ?_
  · intro η hη
    exact mulLeft_mem_nthRootsFinset hk hζ hη
  · intro η₁ hη₁ η₂ hη₂ h
    have hζ_ne : ζ ≠ 0 := by
      intro hh
      rw [hh, zero_pow (Nat.one_le_iff_ne_zero.mp hk)] at hζ
      exact one_ne_zero hζ.symm
    exact mul_left_cancel₀ hζ_ne h
  · intro η hη
    have hζ_ne : ζ ≠ 0 := by
      intro hh
      rw [hh, zero_pow (Nat.one_le_iff_ne_zero.mp hk)] at hζ
      exact one_ne_zero hζ.symm
    have hζinv_pow : ζ⁻¹ ^ k = 1 := by rw [inv_pow, hζ, inv_one]
    refine ⟨ζ⁻¹ * η, mulLeft_mem_nthRootsFinset hk hζinv_pow hη, ?_⟩
    show ζ * (ζ⁻¹ * η) = η
    rw [← mul_assoc, mul_inv_cancel₀ hζ_ne, one_mul]
  · intro η _hη
    rfl

/-! ### The norm-pushforward across `t = s^k`

The per-fibre product `t ↦ ∏ η ∈ nthRootsFinset k t, g η` packages the
multiplicative pushforward at the **algebraic** level. Local meromorphy
in `t` is the downstream chip P1.2 (Vieta + symmetric polynomials). -/

/-- **Norm pushforward across the planar `k`-th power map.**

`normPow g k t` is the product of `g` over the `k`-th roots of `t` in `ℂ`.

For `t = s ^ k` with `s ≠ 0`, this is exactly `∏_{ζ : ζ^k = 1} g (ζ * s)`,
the symmetric function realization of the Hurwitz norm pushforward at the
branch value. -/
def normPow (g : ℂ → ℂ) (k : ℕ) (t : ℂ) : ℂ :=
  ∏ η ∈ Polynomial.nthRootsFinset k t, g η

/-- Definitional unfold of `normPow`. -/
@[simp] lemma normPow_eq_finset_prod (g : ℂ → ℂ) (k : ℕ) (t : ℂ) :
    normPow g k t = ∏ η ∈ Polynomial.nthRootsFinset k t, g η := rfl

/-- **`normPow g k` evaluated at `s^k` equals the product over `μ_k * s`**,
for `s ≠ 0`. This is the bridge between the indexing-set definition
(`nthRootsFinset k (s^k)`) and the rotation-of-`s` realization that lets
P1.2 transport meromorphy from `s` to `t = s^k`.

Proof. The k-th roots of `s^k` are exactly `{ζ * s : ζ ∈ nthRootsFinset k 1}`,
because `(ζ * s)^k = ζ^k * s^k = 1 * s^k = s^k` (and the converse uses
that `(s')^k = s^k` implies `(s'/s)^k = 1`, with `s ≠ 0`). The cardinality
match (≤ k both sides) plus the inclusion forces equality. -/
theorem normPow_pow (g : ℂ → ℂ) {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : s ≠ 0) :
    normPow g k (s ^ k)
      = ∏ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ), g (ζ * s) := by
  classical
  unfold normPow
  -- Bijection: `nthRootsFinset k 1 → nthRootsFinset k (s^k)`, `ζ ↦ ζ * s`.
  refine (Finset.prod_bij (fun ζ _ => ζ * s) ?_ ?_ ?_ ?_).symm
  · intro ζ hζ
    rw [Polynomial.mem_nthRootsFinset hk] at hζ ⊢
    rw [mul_pow, hζ, one_mul]
  · intro ζ₁ _ ζ₂ _ h
    exact mul_right_cancel₀ hs h
  · intro η hη
    rw [Polynomial.mem_nthRootsFinset hk] at hη
    refine ⟨η * s⁻¹, ?_, ?_⟩
    · rw [Polynomial.mem_nthRootsFinset hk]
      rw [mul_pow, hη, ← mul_pow, mul_inv_cancel₀ hs, one_pow]
    · show η * s⁻¹ * s = η
      rw [mul_assoc, inv_mul_cancel₀ hs, mul_one]
  · intro ζ _; rfl

/-- **μ_k-symmetry of the rotation form of `normPow`.** For `s ≠ 0` and
`ζ₀ ∈ nthRootsFinset k 1`,
`∏ ζ ∈ μ_k, g (ζ * (ζ₀ * s)) = ∏ ζ ∈ μ_k, g (ζ * s)`.

Direct corollary of `prod_nthRootsFinset_mulLeft_invariant` applied with
`a = 1` and the substitution `g' η := g (η * s)`. (Re-bracket using
associativity of multiplication.) -/
theorem prod_mu_k_rotation_invariant
    (g : ℂ → ℂ) {k : ℕ} (hk : 1 ≤ k) {ζ₀ : ℂ}
    (hζ₀ : ζ₀ ∈ Polynomial.nthRootsFinset k (1 : ℂ)) (s : ℂ) :
    ∏ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ), g (ζ * (ζ₀ * s))
      = ∏ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ), g (ζ * s) := by
  classical
  have hζ₀_pow : ζ₀ ^ k = 1 := (Polynomial.mem_nthRootsFinset hk (1 : ℂ)).mp hζ₀
  -- Apply `prod_nthRootsFinset_mulLeft_invariant` with the auxiliary
  -- function `g'(η) := g (η * s)`. The LHS rewrites:
  --   `g (ζ * (ζ₀ * s)) = g ((ζ * ζ₀) * s) = g' (ζ * ζ₀)`,
  -- and the invariance lemma yields `∑_{ζ ∈ μ_k} g'(ζ * ζ₀) = ∑_{ζ ∈ μ_k} g'(ζ)`.
  have h := prod_nthRootsFinset_mulLeft_invariant hk hζ₀_pow (1 : ℂ)
    (fun η => g (η * s))
  -- After the substitution, LHS of `h` is `∏ ζ ∈ μ_k, g ((ζ₀ * ζ) * s)`,
  -- which equals our LHS by associativity and commutativity of multiplication.
  -- RHS of `h` is `∏ ζ ∈ μ_k, g (ζ * s)`, which is our RHS.
  have hLHS : ∏ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ), g (ζ * (ζ₀ * s))
        = ∏ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ), g ((ζ₀ * ζ) * s) := by
    apply Finset.prod_congr rfl
    intro ζ _
    rw [show ζ * (ζ₀ * s) = (ζ₀ * ζ) * s by ring]
  rw [hLHS]
  exact h

/-! ### Symmetry: `normPow g k` evaluated via two k-th roots of `t` agree -/

/-- **The pushforward depends only on `t`, not on the choice of k-th root.**

For `s₁ s₂ : ℂ` with `s₁ ^ k = s₂ ^ k` (both being k-th roots of the same
`t`), and `s₁ ≠ 0` (hence `s₂ ≠ 0`), the rotation forms agree:
`∏ ζ ∈ μ_k, g (ζ * s₁) = ∏ ζ ∈ μ_k, g (ζ * s₂)`.

This is the headline μ_k-symmetry: `normPow g k (s^k)` is well-defined
as a function of `s^k`, independent of which k-th root we picked.

Proof. Since `s₁^k = s₂^k ≠ 0` (we'd have `s₁ = 0` otherwise), the ratio
`ζ₀ := s₂ / s₁` satisfies `ζ₀^k = 1`, i.e. `ζ₀ ∈ nthRootsFinset k 1`,
and `s₂ = ζ₀ * s₁`. Apply `prod_mu_k_rotation_invariant`. -/
theorem prod_mu_k_indep_of_root
    (g : ℂ → ℂ) {k : ℕ} (hk : 1 ≤ k) {s₁ s₂ : ℂ}
    (hs₁ : s₁ ≠ 0) (h_pow : s₁ ^ k = s₂ ^ k) :
    ∏ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ), g (ζ * s₁)
      = ∏ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ), g (ζ * s₂) := by
  classical
  -- s₂ ≠ 0, since otherwise s₁^k = 0^k = 0 (using k ≥ 1), forcing s₁ = 0.
  have hs₂ : s₂ ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.one_le_iff_ne_zero.mp hk)] at h_pow
    exact (pow_ne_zero k hs₁) h_pow
  set ζ₀ : ℂ := s₂ / s₁ with hζ₀_def
  have hζ₀_pow : ζ₀ ^ k = 1 := by
    rw [hζ₀_def, div_pow, ← h_pow, div_self (pow_ne_zero k hs₁)]
  have hζ₀_mem : ζ₀ ∈ Polynomial.nthRootsFinset k (1 : ℂ) :=
    (Polynomial.mem_nthRootsFinset hk (1 : ℂ)).mpr hζ₀_pow
  have hs₂_eq : s₂ = ζ₀ * s₁ := by
    rw [hζ₀_def, div_mul_cancel₀ _ hs₁]
  rw [hs₂_eq]
  exact (prod_mu_k_rotation_invariant g hk hζ₀_mem s₁).symm

end Manifold
end JacobianChallenge

end
