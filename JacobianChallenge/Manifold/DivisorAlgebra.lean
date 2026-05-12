/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor
import JacobianChallenge.Divisor.Single

set_option diagnostics.threshold 100

/-! # Divisor algebra: pointwise evaluation and `Div0` membership lemmas

This file packages the small but missing layer of pointwise-evaluation and
`AddGroup`/`AddSubgroup`-closure lemmas natural to want about `Div X`:

* Pointwise evaluation of `0`, `D₁ + D₂`, `-D`, `D₁ - D₂`, `n • D`
  (`Div.zero_apply`, `Div.add_apply`, `Div.neg_apply`, `Div.sub_apply`,
  `Div.zsmul_apply`, `Div.nsmul_apply`).
* `Div.coe_*` variants of the above (when not already supplied verbatim by
  the underlying `Function.locallyFinsuppWithin` API).
* `Div.degree_zsmul`, `Div.degree_nsmul`, `Div.degree_sum` — degree
  commutes with `ℤ`-scalar action and finset sums, immediate from
  `degreeHom` being an additive group homomorphism.
* `Div.mem_Div0_iff` — explicit unfolding of `D ∈ Div0 X`.
* `Div.zero_mem_Div0`, `Div.add_mem_Div0`, `Div.neg_mem_Div0`,
  `Div.sub_mem_Div0`, `Div.zsmul_mem_Div0`, `Div.sum_mem_Div0` — the
  `AddSubgroup` closure laws restated in a form usable downstream
  without unfolding `Div0`.
* `Div.support_zero` / `Div.supportFinset_zero`, `Div.support_neg` /
  `Div.supportFinset_neg`.
* `Div.single_injective` and `Div.single_ne_single_iff` — restatements
  of `Div.single_eq_iff` as `Function.Injective` and as a `≠` form.

Nothing here adds new axioms or named hypotheses; everything is pure
composition of existing infrastructure in `JacobianChallenge.Divisor` and
`JacobianChallenge.Divisor.Single`, plus the `Function.locallyFinsuppWithin`
mathlib API. Diagnostics threshold is set per the repo convention.
-/

namespace JacobianChallenge

namespace Div

variable {X : Type*} [TopologicalSpace X]

/-! ### Pointwise evaluation -/

/-- Pointwise evaluation of `0 : Div X`. -/
@[simp] lemma zero_apply (x : X) : ((0 : Div X) : X → ℤ) x = 0 := by
  rw [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]

/-- Pointwise evaluation of `D₁ + D₂`. -/
@[simp] lemma add_apply (D₁ D₂ : Div X) (x : X) :
    ((D₁ + D₂ : Div X) : X → ℤ) x
      = (D₁ : X → ℤ) x + (D₂ : X → ℤ) x := by
  rw [Function.locallyFinsuppWithin.coe_add, Pi.add_apply]

/-- Pointwise evaluation of `-D`. -/
@[simp] lemma neg_apply (D : Div X) (x : X) :
    ((-D : Div X) : X → ℤ) x = -((D : X → ℤ) x) := by
  rw [Function.locallyFinsuppWithin.coe_neg, Pi.neg_apply]

/-- Pointwise evaluation of `D₁ - D₂`. -/
@[simp] lemma sub_apply (D₁ D₂ : Div X) (x : X) :
    ((D₁ - D₂ : Div X) : X → ℤ) x
      = (D₁ : X → ℤ) x - (D₂ : X → ℤ) x := by
  rw [sub_eq_add_neg, add_apply, neg_apply, sub_eq_add_neg]

/-- Pointwise evaluation of `n • D` for `n : ℤ`. -/
@[simp] lemma zsmul_apply (n : ℤ) (D : Div X) (x : X) :
    ((n • D : Div X) : X → ℤ) x = n * (D : X → ℤ) x := by
  rw [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, smul_eq_mul]

/-- Pointwise evaluation of `n • D` for `n : ℕ`. -/
@[simp] lemma nsmul_apply (n : ℕ) (D : Div X) (x : X) :
    ((n • D : Div X) : X → ℤ) x = n * (D : X → ℤ) x := by
  rw [Function.locallyFinsuppWithin.coe_nsmul, Pi.smul_apply, nsmul_eq_mul]

/-! ### Degree and scalar action / sums -/

/-- The degree of `n • D` is `n * D.degree` (for `n : ℤ`). Immediate from
`degreeHom` being an `AddMonoidHom`. -/
@[simp] lemma degree_zsmul [T2Space X] [CompactSpace X] (n : ℤ) (D : Div X) :
    degree (n • D) = n * degree D := by
  have h : degree (n • D) = degreeHom (X := X) (n • D) := rfl
  rw [h, map_zsmul]
  simp [degreeHom_apply, zsmul_eq_mul]

/-- The degree of `n • D` is `n * D.degree` (for `n : ℕ`). -/
@[simp] lemma degree_nsmul [T2Space X] [CompactSpace X] (n : ℕ) (D : Div X) :
    degree (n • D) = n * degree D := by
  have h : degree (n • D) = degreeHom (X := X) (n • D) := rfl
  rw [h, map_nsmul]
  simp [degreeHom_apply, nsmul_eq_mul]

/-- The degree of a finset sum of divisors is the sum of the degrees.
Immediate from `degreeHom` being an `AddMonoidHom`. -/
lemma degree_sum [T2Space X] [CompactSpace X] {ι : Type*} (s : Finset ι)
    (f : ι → Div X) :
    degree (∑ i ∈ s, f i) = ∑ i ∈ s, degree (f i) := by
  have h : degree (∑ i ∈ s, f i) = degreeHom (X := X) (∑ i ∈ s, f i) := rfl
  rw [h, map_sum]
  rfl

/-! ### `Div0` membership API -/

/-- A divisor lies in `Div0 X` iff its degree is `0`. -/
lemma mem_Div0_iff [T2Space X] [CompactSpace X] {D : Div X} :
    D ∈ Div0 X ↔ degree D = 0 := by
  unfold Div0
  rw [AddMonoidHom.mem_ker, degreeHom_apply]

/-- `0 ∈ Div0 X`. -/
@[simp] lemma zero_mem_Div0 [T2Space X] [CompactSpace X] :
    (0 : Div X) ∈ Div0 X := (Div0 X).zero_mem

/-- `Div0 X` is closed under addition. -/
lemma add_mem_Div0 [T2Space X] [CompactSpace X] {D₁ D₂ : Div X}
    (h₁ : D₁ ∈ Div0 X) (h₂ : D₂ ∈ Div0 X) : D₁ + D₂ ∈ Div0 X :=
  (Div0 X).add_mem h₁ h₂

/-- `Div0 X` is closed under negation. -/
lemma neg_mem_Div0 [T2Space X] [CompactSpace X] {D : Div X}
    (h : D ∈ Div0 X) : -D ∈ Div0 X := (Div0 X).neg_mem h

/-- `Div0 X` is closed under subtraction. -/
lemma sub_mem_Div0 [T2Space X] [CompactSpace X] {D₁ D₂ : Div X}
    (h₁ : D₁ ∈ Div0 X) (h₂ : D₂ ∈ Div0 X) : D₁ - D₂ ∈ Div0 X :=
  (Div0 X).sub_mem h₁ h₂

/-- `Div0 X` is closed under `ℤ`-scalar action. -/
lemma zsmul_mem_Div0 [T2Space X] [CompactSpace X] (n : ℤ) {D : Div X}
    (h : D ∈ Div0 X) : n • D ∈ Div0 X :=
  (Div0 X).zsmul_mem h n

/-- `Div0 X` is closed under finset sums. -/
lemma sum_mem_Div0 [T2Space X] [CompactSpace X] {ι : Type*}
    (s : Finset ι) (f : ι → Div X) (h : ∀ i ∈ s, f i ∈ Div0 X) :
    (∑ i ∈ s, f i) ∈ Div0 X :=
  (Div0 X).sum_mem h

/-! ### Support of `0` and `-D` -/

/-- The function-support of `0 : Div X` is empty. -/
@[simp] lemma support_zero : ((0 : Div X) : X → ℤ).support = (∅ : Set X) := by
  ext x; simp

/-- On compact Hausdorff `X`, the `supportFinset` of `0 : Div X` is empty. -/
@[simp] lemma supportFinset_zero [T2Space X] [CompactSpace X] :
    (0 : Div X).supportFinset = (∅ : Finset X) := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rw [mem_supportFinset] at hx
  exact hx (zero_apply x)

/-- The function-support of `-D` equals the function-support of `D`. -/
@[simp] lemma support_neg (D : Div X) :
    ((-D : Div X) : X → ℤ).support = (D : X → ℤ).support := by
  ext x
  rw [Function.mem_support, Function.mem_support, neg_apply, ne_eq,
      neg_eq_zero, ne_eq]

/-- On compact Hausdorff `X`, the `supportFinset` of `-D` equals that of `D`. -/
@[simp] lemma supportFinset_neg [T2Space X] [CompactSpace X] (D : Div X) :
    (-D).supportFinset = D.supportFinset := by
  classical
  apply Finset.coe_injective
  ext x
  simp only [Finset.mem_coe, mem_supportFinset, neg_apply, ne_eq, neg_eq_zero]

/-! ### Singleton injectivity -/

/-- `Div.single : X → Div X` is injective on the decidable-equality set. -/
lemma single_injective [DecidableEq X] :
    Function.Injective (single : X → Div X) :=
  fun _ _ h => (single_eq_iff _ _).mp h

/-- `Div.single x ≠ Div.single y` iff `x ≠ y`. -/
lemma single_ne_single_iff [DecidableEq X] (x y : X) :
    (single x : Div X) ≠ single y ↔ x ≠ y := by
  rw [ne_eq, ne_eq, single_eq_iff]

/-! ### Pointwise evaluation of `n • single` (cf. `Jacobian.zsmul_single_apply`) -/

/-- A small `n • single`-difference identity: pointwise evaluation of
`n • single P - n • single Q` factors through `single_apply`. This is a
convenience wrapper used when reasoning about `n • (single P - single Q)`
divisors. -/
lemma zsmul_single_sub_zsmul_single_apply [DecidableEq X]
    (n : ℤ) (P Q y : X) :
    ((n • (single P : Div X) - n • single Q) : X → ℤ) y
      = n * ((if y = P then 1 else 0) - (if y = Q then 1 else 0)) := by
  classical
<<<<<<< Updated upstream
  rw [sub_apply, zsmul_apply, zsmul_apply, single_apply, single_apply,
      mul_sub]
=======
  simp [sub_apply, zsmul_apply, single_apply, mul_sub]
>>>>>>> Stashed changes

/-- `n • (single P - single Q)` lies in `Div0 X` (compact Hausdorff `X`).
The degree of `single P - single Q` is `0`, so its `ℤ`-multiples are too. -/
lemma zsmul_single_sub_single_mem_Div0 [DecidableEq X] [T2Space X]
    [CompactSpace X] (n : ℤ) (P Q : X) :
    n • ((single P : Div X) - single Q) ∈ Div0 X := by
<<<<<<< Updated upstream
  -- `single P - single Q ∈ Div0 X` is provided by
  -- `single_sub_single_mem_Div0` (with the arguments swapped: it is stated
  -- for `single Q - single P`; we negate).
  have hbase : ((single P : Div X) - single Q) ∈ Div0 X := by
    -- `(single P - single Q) = -(single Q - single P)`
    have hneg : (single P : Div X) - single Q = -((single Q : Div X) - single P) := by
      rw [neg_sub]
    rw [hneg]
    exact neg_mem_Div0 (single_sub_single_mem_Div0 (X := X) Q P)
=======
  -- `single_sub_single_mem_Div0` reads `(P Q : X) : single Q - single P ∈ Div0`;
  -- calling with the args swapped gives the variant we want.
  have hbase : ((single P : Div X) - single Q) ∈ Div0 X :=
    single_sub_single_mem_Div0 (X := X) Q P
>>>>>>> Stashed changes
  exact zsmul_mem_Div0 n hbase

end Div

end JacobianChallenge
