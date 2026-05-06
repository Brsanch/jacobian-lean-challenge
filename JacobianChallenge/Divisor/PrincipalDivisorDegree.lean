/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.MeromorphicNonzeroGerm

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Degree-multiplicativity of `principalDivisorMap`

Combining `principalDivisorMap_mul` (`Divisor/PrincipalDivisor.lean`,
multiplicativity of the order divisor under the germ-canonicalized product)
with `principalDivisorMap_invMer` (`Divisor/MeromorphicNonzeroGerm.lean`,
the order divisor of the representative-level inverse is the negation of
the original order divisor) plus the `AddGroupHom` structure on
`Div.degreeHom` (`Divisor.lean`), we obtain the degree-level
multiplicativity statements:

* `principalDivisorMap_degree_mul` — `degree (PD (f * g)) = degree (PD f) + degree (PD g)`.
* `principalDivisorMap_degree_invMer` — `degree (PD (invMer f)) = -degree (PD f)`.
* `Germ.principalDivisorMap_degree_mul` — same on the `Germ X` quotient.
* `Germ.principalDivisorMap_degree_inv` — `degree (PD (g⁻¹)) = -degree (PD g)` on `Germ X`.
* `Germ.principalDivisorMap_degree_zpow` — `degree (PD (g^n)) = n * degree (PD g)`
  for `n : ℤ`, on `Germ X`.

These are exactly the corollaries the chip targets: degree is an
`AddGroupHom`, `Div`-valued `principalDivisorMap` is multiplicative, hence
the composition `degree ∘ principalDivisorMap` is a `MonoidHom` from
`(Germ X, *)` to `(ℤ, +)`. The residue-theorem program needs only that
this composite vanishes on a single witness; multiplicativity propagates
the vanishing through the multiplicative subgroup it generates. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace JacobianChallenge

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ### Representative-level degree lemmas -/

/-- Degree-multiplicativity at the `MeromorphicNonzero` representative
level: `degree (PD (f * g)) = degree (PD f) + degree (PD g)`. Direct
combination of `principalDivisorMap_mul` (multiplicativity of the order
divisor) and `Div.degree_add` (additivity of degree). -/
lemma principalDivisorMap_degree_mul (f g : MeromorphicNonzero X) :
    (principalDivisorMap (f * g)).degree
      = (principalDivisorMap f).degree + (principalDivisorMap g).degree := by
  rw [principalDivisorMap_mul, Div.degree_add]

/-- Degree-inversion at the `MeromorphicNonzero` representative level:
`degree (PD (invMer f)) = -degree (PD f)`. Direct combination of
`principalDivisorMap_invMer` and `Div.degree_neg`. -/
lemma principalDivisorMap_degree_invMer (f : MeromorphicNonzero X) :
    (principalDivisorMap (MeromorphicNonzero.invMer f)).degree
      = -(principalDivisorMap f).degree := by
  rw [principalDivisorMap_invMer, Div.degree_neg]

/-- The constant `1` representative has degree-zero principal divisor.
`principalDivisorMap_one` collapses to the zero divisor; `Div.degree_zero`
finishes. -/
@[simp] lemma principalDivisorMap_degree_one :
    (principalDivisorMap (1 : MeromorphicNonzero X)).degree = 0 := by
  rw [principalDivisorMap_one, Div.degree_zero]

end JacobianChallenge

/-! ### `Germ X` versions

On the germ quotient the `CommGroup` structure is in scope, so `g⁻¹`,
`g₁ * g₂`, and `g^n` are all defined and we can phrase the chip's headline
statements verbatim. Each germ-level lemma reduces to its representative
counterpart by `Quotient.inductionOn`. -/

namespace JacobianChallenge.MeromorphicNonzero

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- Multiplicativity of `Germ.principalDivisorMap`. Reduces to
`principalDivisorMap_mul` after `Quotient.inductionOn`. -/
lemma Germ.principalDivisorMap_mul (g₁ g₂ : Germ X) :
    Germ.principalDivisorMap (g₁ * g₂)
      = Germ.principalDivisorMap g₁ + Germ.principalDivisorMap g₂ := by
  refine Quotient.inductionOn₂ (motive := fun a b =>
      Germ.principalDivisorMap (a * b)
        = Germ.principalDivisorMap a + Germ.principalDivisorMap b) g₁ g₂ ?_
  intro f₁ f₂
  -- `Quotient.mk f * Quotient.mk g = Quotient.mk (f * g)` definitionally.
  -- `Germ.principalDivisorMap (Germ.mk f) = principalDivisorMap f` definitionally.
  show JacobianChallenge.principalDivisorMap (f₁ * f₂)
      = JacobianChallenge.principalDivisorMap f₁
        + JacobianChallenge.principalDivisorMap f₂
  exact JacobianChallenge.principalDivisorMap_mul f₁ f₂

/-- Inversion: `Germ.principalDivisorMap (g⁻¹) = -Germ.principalDivisorMap g`.
By `Quotient.inductionOn` and the unfolding `(Germ.mk f)⁻¹ = Germ.mk (invMer f)`. -/
lemma Germ.principalDivisorMap_inv (g : Germ X) :
    Germ.principalDivisorMap (g⁻¹)
      = -Germ.principalDivisorMap g := by
  refine Quotient.inductionOn (motive := fun a =>
      Germ.principalDivisorMap (a⁻¹) = -Germ.principalDivisorMap a) g ?_
  intro f
  show JacobianChallenge.principalDivisorMap (invMer f)
      = -JacobianChallenge.principalDivisorMap f
  exact JacobianChallenge.principalDivisorMap_invMer f

/-- The unit germ has the zero divisor: `Germ.principalDivisorMap 1 = 0`. -/
@[simp] lemma Germ.principalDivisorMap_one :
    Germ.principalDivisorMap (1 : Germ X) = (0 : Div X) := by
  show JacobianChallenge.principalDivisorMap (one X) = (0 : Div X)
  -- `one X` and `(1 : MeromorphicNonzero X)` are definitionally the same.
  exact JacobianChallenge.principalDivisorMap_one

/-- Degree-multiplicativity on the germ quotient. -/
lemma Germ.principalDivisorMap_degree_mul (g₁ g₂ : Germ X) :
    (Germ.principalDivisorMap (g₁ * g₂)).degree
      = (Germ.principalDivisorMap g₁).degree
        + (Germ.principalDivisorMap g₂).degree := by
  rw [Germ.principalDivisorMap_mul, Div.degree_add]

/-- Degree-inversion on the germ quotient. -/
lemma Germ.principalDivisorMap_degree_inv (g : Germ X) :
    (Germ.principalDivisorMap (g⁻¹)).degree
      = -(Germ.principalDivisorMap g).degree := by
  rw [Germ.principalDivisorMap_inv, Div.degree_neg]

/-- The composite `degree ∘ Germ.principalDivisorMap : Germ X →* ℤ`
phrased as a multiplicative-to-additive map. Useful as a single bundle
when invoking the residue-theorem program. -/
@[simp] lemma Germ.principalDivisorMap_degree_one :
    (Germ.principalDivisorMap (1 : Germ X)).degree = 0 := by
  rw [Germ.principalDivisorMap_one, Div.degree_zero]

/-! ### Powers (natural and integer)

For natural `n`, `g^n = g * g * … * g` is `Monoid.npow`. The degree-power
identity follows by induction on `n`. For integer `n`, the `CommGroup`
structure splits via the sign and we combine `npow` with the inversion
identity. -/

/-- Degree-multiplicativity for natural powers. By induction on `n`, using
`pow_succ` and `principalDivisorMap_degree_mul`. -/
lemma Germ.principalDivisorMap_degree_pow (g : Germ X) (n : ℕ) :
    (Germ.principalDivisorMap (g ^ n)).degree
      = n * (Germ.principalDivisorMap g).degree := by
  induction n with
  | zero =>
    rw [pow_zero, Germ.principalDivisorMap_degree_one, Nat.cast_zero, zero_mul]
  | succ k ih =>
    rw [pow_succ, Germ.principalDivisorMap_degree_mul, ih]
    push_cast
    ring

/-- Degree-multiplicativity for integer powers. Splits on the sign of `n`
via `Int.emod_two_eq` style — concretely we use `zpow_natCast` for
non-negative integers and `zpow_negSucc` (i.e. `g ^ (-(n+1) : ℤ) =
(g ^ (n+1))⁻¹`) for negative integers. -/
lemma Germ.principalDivisorMap_degree_zpow (g : Germ X) (n : ℤ) :
    (Germ.principalDivisorMap (g ^ n)).degree
      = n * (Germ.principalDivisorMap g).degree := by
  induction n with
  | ofNat k =>
    -- `g ^ (Int.ofNat k) = g ^ k` (the natural-number power).
    have h_zpow : (g ^ (Int.ofNat k : ℤ)) = g ^ k := by
      rw [Int.ofNat_eq_coe, zpow_natCast]
    rw [h_zpow, Germ.principalDivisorMap_degree_pow]
    simp
  | negSucc k =>
    -- `g ^ (-(k+1)) = (g ^ (k+1))⁻¹` (mathlib `zpow_negSucc`).
    have h_zpow : g ^ (Int.negSucc k) = (g ^ (k + 1))⁻¹ := zpow_negSucc g k
    rw [h_zpow, Germ.principalDivisorMap_degree_inv,
        Germ.principalDivisorMap_degree_pow]
    push_cast
    ring

end JacobianChallenge.MeromorphicNonzero

end
