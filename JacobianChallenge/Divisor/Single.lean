/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor

set_option diagnostics.threshold 100

/-! # Single-point divisors

This file packages the singleton-indicator divisor `Div.single x`, the
`ℤ`-valued divisor that equals `1` at `x` and `0` elsewhere. It is the
analogue of `Finsupp.single x 1` for `Function.locallyFinsuppWithin
(Set.univ : Set X) ℤ`, and is the building block of every concrete
construction `ofCurve P := fun Q ↦ Div.single Q - Div.single P` that we
will need downstream (in particular for `JacobianChallenge.Basic` items
that need a real `ofCurve : X → Pic0 X` rather than a placeholder).

## Contents

* `Div.single x` — the singleton-indicator divisor, defined as
  `Function.locallyFinsuppWithin.single x (1 : ℤ)`.
* `Div.single_apply` / `Div.coe_single` — value of `Div.single` at a
  point.
* `Div.support_single` — support as a set is `{x}`.
* `Div.supportFinset_single` — support as a finset is `{x}` (compact
  Hausdorff `X`).
* `Div.degree_single` — `degree (Div.single x) = 1` (compact Hausdorff
  `X`).
* `Div.degree_single_sub_single` — `degree (Div.single Q - Div.single P) = 0`.
* `Div.single_sub_single_mem_Div0` — that difference lies in `Div0 X`.
* `Div.single_sub_single_apply` / `Div.coe_single_sub_single_apply` —
  pointwise evaluation of `Div.single Q - Div.single P` (FunLike-direct
  and function-coercion forms).
* `Div.support_single_sub_single` — when `P ≠ Q`, the function-support is
  the two-point set `{P, Q}`.
* `Div.supportFinset_single_sub_single` — Finset-form of the above on
  compact Hausdorff `X`.
* `Div.single_eq_iff` — `Div.single x = Div.single y ↔ x = y` (bonus,
  needed for injectivity of any `ofCurve P` against the placeholder
  `PrincDiv = ⊥`).

The `[DecidableEq X]` hypothesis is inherited from mathlib's
`Function.locallyFinsuppWithin.single` (which uses `Pi.single`); it is
required to make `Div.single x` definable. Compact complex manifolds in
the challenge will satisfy this via `Classical.decEq` at the use site,
but we keep the hypothesis explicit here so the API stays computable
where possible.
-/

namespace JacobianChallenge

namespace Div

variable {X : Type*} [TopologicalSpace X]

/-! ### Definition and basic API -/

/-- The *singleton-indicator divisor* `Div.single x`: the divisor with
value `1` at `x` and `0` elsewhere. -/
noncomputable def single [DecidableEq X] (x : X) : Div X :=
  Function.locallyFinsuppWithin.single x (1 : ℤ)

/-- Pointwise evaluation of `Div.single x`. -/
@[simp] lemma single_apply [DecidableEq X] (x y : X) :
    (single x : Div X) y = if y = x then 1 else 0 := by
  classical
  unfold single
  simp [Function.locallyFinsuppWithin.single_apply]

/-- Coercion of `Div.single x` to a function on `X`. -/
@[simp] lemma coe_single [DecidableEq X] (x : X) :
    ((single x : Div X) : X → ℤ) = fun y => if y = x then 1 else 0 := by
  classical
  funext y
  exact single_apply (X := X) x y

/-- The function-support of `Div.single x` is exactly the set `{x}`. -/
lemma support_single [DecidableEq X] (x : X) :
    ((single x : Div X) : X → ℤ).support = {x} := by
  classical
  ext y
  simp only [Function.mem_support, coe_single, Set.mem_singleton_iff,
    ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]

/-! ### Support as a finset, on compact Hausdorff `X` -/

/-- On a compact Hausdorff space, the `supportFinset` of `Div.single x` is
the finset `{x}`. -/
lemma supportFinset_single [DecidableEq X] [T2Space X] [CompactSpace X]
    (x : X) : (single x : Div X).supportFinset = {x} := by
  classical
  -- Two finite sets are equal as finsets iff they are equal as sets.
  apply Finset.coe_injective
  -- `↑supportFinset = function-support` via `mem_supportFinset`.
  ext y
  simp only [Finset.coe_singleton, Set.mem_singleton_iff, Finset.mem_coe]
  rw [mem_supportFinset]
  -- `D y ≠ 0 ↔ y ∈ {x}` from `support_single`.
  have hsupp := support_single (X := X) x
  constructor
  · intro hy
    have : y ∈ ((single x : Div X) : X → ℤ).support := hy
    rw [hsupp] at this
    exact this
  · intro hy
    have : y ∈ ((single x : Div X) : X → ℤ).support := by
      rw [hsupp]; exact hy
    exact this

/-! ### Degree of singleton and singleton-difference divisors -/

/-- The degree of `Div.single x` is `1`. -/
@[simp] lemma degree_single [DecidableEq X] [T2Space X] [CompactSpace X]
    (x : X) : (single x : Div X).degree = 1 := by
  classical
  unfold degree
  rw [supportFinset_single]
  simp

/-- The degree of `Div.single Q - Div.single P` is `0`. -/
@[simp] lemma degree_single_sub_single [DecidableEq X] [T2Space X]
    [CompactSpace X] (P Q : X) :
    ((single Q : Div X) - single P).degree = 0 := by
  classical
  -- `degree` is an `AddGroup` hom via `degreeHom`, so it commutes with `-`.
  have h : ((single Q : Div X) - single P).degree
      = degreeHom (single Q - single P : Div X) := rfl
  rw [h, map_sub]
  simp [degreeHom_apply]

/-- `Div.single Q - Div.single P` lies in `Div0 X` (the kernel of the
degree homomorphism). -/
lemma single_sub_single_mem_Div0 [DecidableEq X] [T2Space X] [CompactSpace X]
    (P Q : X) : ((single Q : Div X) - single P) ∈ Div0 X := by
  -- `Div0 X = degreeHom.ker`, so membership = `degreeHom _ = 0`.
  have h : degreeHom (X := X) ((single Q : Div X) - single P) = 0 := by
    rw [map_sub]; simp [degreeHom_apply]
  exact AddMonoidHom.mem_ker.mpr h

/-! ### Support of singleton-difference divisors -/

/-- Pointwise evaluation of `Div.single Q - Div.single P`. -/
lemma single_sub_single_apply [DecidableEq X] (P Q y : X) :
    ((single Q : Div X) - single P) y
      = (if y = Q then 1 else 0) - (if y = P then 1 else 0) := by
  classical
  -- `coe_sub` (= rfl) makes FunLike application of `D₁ - D₂` definitionally
  -- equal to the pointwise difference; `single_apply` handles each summand.
  have h : ((single Q : Div X) - single P) y
      = (single Q : Div X) y - (single P : Div X) y := rfl
  rw [h, single_apply, single_apply]

/-- Coercion-form variant of `single_sub_single_apply`, useful for
support-related rewrites. -/
lemma coe_single_sub_single_apply [DecidableEq X] (P Q y : X) :
    (((single Q : Div X) - single P) : X → ℤ) y
      = (if y = Q then 1 else 0) - (if y = P then 1 else 0) :=
  single_sub_single_apply P Q y

/-- When `P ≠ Q`, the function-support of `Div.single Q - Div.single P`
is exactly the two-point set `{P, Q}`. -/
lemma support_single_sub_single [DecidableEq X] {P Q : X} (hPQ : P ≠ Q) :
    (((single Q : Div X) - single P) : X → ℤ).support = {P, Q} := by
  classical
  ext y
  simp only [Function.mem_support, coe_single_sub_single_apply,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hy
    -- `(if y=Q then 1 else 0) - (if y=P then 1 else 0) ≠ 0`
    by_cases hyQ : y = Q
    · exact Or.inr hyQ
    · by_cases hyP : y = P
      · exact Or.inl hyP
      · -- both branches are 0, so the difference is 0, contradicting `hy`.
        rw [if_neg hyQ, if_neg hyP, sub_zero] at hy
        exact absurd rfl hy
  · intro hy
    rcases hy with hyP | hyQ
    · -- y = P, so y ≠ Q (since P ≠ Q)
      have hyQne : y ≠ Q := by rw [hyP]; exact hPQ
      rw [if_neg hyQne, if_pos hyP, zero_sub]
      exact neg_ne_zero.mpr one_ne_zero
    · -- y = Q, so y ≠ P
      have hyPne : y ≠ P := by rw [hyQ]; exact hPQ.symm
      rw [if_pos hyQ, if_neg hyPne, sub_zero]
      exact one_ne_zero

/-- When `P ≠ Q`, the `supportFinset` of `Div.single Q - Div.single P`
is the two-point finset `{P, Q}`. -/
lemma supportFinset_single_sub_single [DecidableEq X] [T2Space X]
    [CompactSpace X] {P Q : X} (hPQ : P ≠ Q) :
    ((single Q : Div X) - single P).supportFinset = {P, Q} := by
  classical
  -- Two finsets are equal iff equal as sets; reduce both sides to sets.
  apply Finset.coe_injective
  ext y
  simp only [Finset.coe_insert, Finset.coe_singleton, Finset.mem_coe]
  rw [mem_supportFinset]
  -- Goal: `((single Q - single P : Div X) : X → ℤ) y ≠ 0 ↔ y ∈ insert P {Q}`.
  have hsupp := support_single_sub_single (X := X) hPQ
  -- `y ∈ support ↔ y ∈ insert P {Q}` after rewriting support.
  have : y ∈ (((single Q : Div X) - single P) : X → ℤ).support
      ↔ y ∈ ({P, Q} : Set X) := by rw [hsupp]
  -- `Function.mem_support` translates LHS to `D y ≠ 0`.
  rw [Function.mem_support] at this
  exact this

/-! ### Bonus: injectivity of `single` -/

/-- `Div.single x = Div.single y` iff `x = y`. This is the key step in
proving injectivity of any `ofCurve P : X → Pic0 X` defined as
`Q ↦ [Div.single Q - Div.single P]` against the current placeholder
`PrincDiv X = ⊥` (under which `[D₁] = [D₂]` reduces to `D₁ = D₂`). -/
lemma single_eq_iff [DecidableEq X] (x y : X) :
    (single x : Div X) = single y ↔ x = y := by
  classical
  refine ⟨fun h => ?_, fun h => by cases h; rfl⟩
  -- Evaluate both sides at `x`. LHS gives `1`; RHS gives `if x = y then 1 else 0`.
  have hx : (single x : Div X) x = (single y : Div X) x := by rw [h]
  rw [single_apply, single_apply, if_pos rfl] at hx
  -- `hx : 1 = if x = y then 1 else 0`
  by_cases hxy : x = y
  · exact hxy
  · rw [if_neg hxy] at hx
    exact absurd hx one_ne_zero

/-- The singleton-indicator divisor `Div.single x` is never zero. -/
lemma single_ne_zero [DecidableEq X] (x : X) :
    (single x : Div X) ≠ 0 := by
  classical
  intro h
  -- Evaluate at `x`: LHS = `1`, RHS = `0`. Contradiction.
  have hx : (single x : Div X) x = (0 : Div X) x := by rw [h]
  rw [single_apply, if_pos rfl] at hx
  -- `(0 : Div X) x = 0` by `Function.locallyFinsuppWithin.coe_zero`.
  have h0 : (0 : Div X) x = 0 := by
    show ((0 : Div X) : X → ℤ) x = 0
    rw [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
  rw [h0] at hx
  exact absurd hx one_ne_zero

/-- The singleton-indicator divisor `Div.single x` is nonzero at `x`. -/
lemma single_self_apply [DecidableEq X] (x : X) :
    (single x : Div X) x = 1 := by
  classical
  rw [single_apply, if_pos rfl]

/-- The singleton-indicator divisor `Div.single x` is zero at any
point distinct from `x`. -/
lemma single_apply_of_ne [DecidableEq X] {x y : X} (h : y ≠ x) :
    (single x : Div X) y = 0 := by
  classical
  rw [single_apply, if_neg h]

end Div

end JacobianChallenge
