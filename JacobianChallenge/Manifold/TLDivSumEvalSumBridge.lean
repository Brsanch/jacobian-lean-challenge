/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelHypothesisReductionComplexTorus
import JacobianChallenge.Manifold.EvalSumGeneral
import JacobianChallenge.Divisor.EvalSum
import JacobianChallenge.Divisor.PrincipalDivisorRange
import JacobianChallenge.Divisor.ChipAliases

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Bridge: `TLDivSumHypothesis L` ⇔ `evalSum (principalDivisorMap _) = 0`

`TLDivSumHypothesis L` (Abel's theorem on elliptic functions, at the T_L
level) is, definitionally, the statement that for every meromorphic-
nonvanishing-germ function `f` on `ℂ ⧸ L`, the support-weighted sum
`∑ x ∈ supp(div f), ord_x f • x` vanishes in `ℂ ⧸ L`. With the
`evalSum`/`evalSumHom` API of `Divisor/EvalSum.lean`, this rephrases as a
single AddMonoidHom-vanishing statement on the generator set of
`PrincDiv (ℂ ⧸ L)`.

The structural consequences:

* `evalSum_eq_zero_on_PrincDiv_of_TLDivSum` —
  `TLDivSumHypothesis L` ⇒ `evalSumHom` vanishes on **all** of
  `PrincDiv (ℂ ⧸ L)`, not only the generators. Free upgrade via
  `AddSubgroup.closure_induction` on the principal-divisor closure.
* `TLDivSum_holds_at_one`, `TLDivSum_holds_at_mul`,
  `TLDivSum_holds_at_invMer` — closure of the per-`f` vanishing
  statement under the multiplicative-group operations on
  `MeromorphicNonzero (ℂ ⧸ L)`. Reduces a future discharge of
  `TLDivSumHypothesis L` to verifying the property on a *multiplicative
  generating set* (rather than on every `MeromorphicNonzero`).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Definitional bridge -/

/-- **Definitional rephrasing of `TLDivSumHypothesis L`.**

`TLDivSumHypothesis L` is exactly the statement that for every
`f : MeromorphicNonzero (ℂ ⧸ L)`, `Div.evalSum (principalDivisorMap f) = 0`. -/
theorem TLDivSumHypothesis_iff_evalSum_principalDivisor_zero :
    TLDivSumHypothesis L ↔
      ∀ f : MeromorphicNonzero (ℂ ⧸ L),
        Div.evalSum (principalDivisorMap f) = (0 : ℂ ⧸ L) := Iff.rfl

/-- **AddMonoidHom form.** `TLDivSumHypothesis L` is equivalent to
`evalSumHom (principalDivisorMap f) = 0` for every `f`. -/
theorem TLDivSumHypothesis_iff_evalSumHom_principalDivisor_zero :
    TLDivSumHypothesis L ↔
      ∀ f : MeromorphicNonzero (ℂ ⧸ L),
        Div.evalSumHom (principalDivisorMap f) = (0 : ℂ ⧸ L) := Iff.rfl

/-- **`TLDivSumHypothesis L` is the T_L specialization of
`EvalSumAbelHypothesis (ℂ ⧸ L)`.** -/
theorem TLDivSumHypothesis_iff_evalSumAbelHypothesis :
    TLDivSumHypothesis L ↔ EvalSumAbelHypothesis (ℂ ⧸ L) := Iff.rfl

/-! ## Closure-induction upgrade: vanishing on all of `PrincDiv` -/

/-- **Vanishing on the closed subgroup.** If `TLDivSumHypothesis L` holds,
then `Div.evalSumHom` vanishes on every element of `PrincDiv (ℂ ⧸ L)` —
not just the generators (`principalDivisorMap` images).

The proof is `AddSubgroup.closure_induction` on the principal-divisor
closure, leveraging the fact that `evalSumHom` is an `AddMonoidHom`
(linearity in the four closure operations: generator, zero, add, neg). -/
theorem evalSumHom_eq_zero_on_PrincDiv_of_TLDivSum
    (hTL : TLDivSumHypothesis L) :
    ∀ D ∈ PrincDiv (ℂ ⧸ L), Div.evalSumHom D = (0 : ℂ ⧸ L) := by
  intro D hD
  unfold PrincDiv PrincDivHonestCandidate at hD
  refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ hD
  · rintro x ⟨f, rfl⟩
    exact hTL f
  · exact map_zero _
  · intro x y _ _ hx hy
    rw [map_add, hx, hy, zero_add]
  · intro x _ hx
    rw [map_neg, hx, neg_zero]

/-- **Kernel-containment form.** `TLDivSumHypothesis L` is equivalent to
`PrincDiv (ℂ ⧸ L) ≤ ker evalSumHom`. -/
theorem TLDivSumHypothesis_iff_PrincDiv_le_ker_evalSumHom :
    TLDivSumHypothesis L ↔
      PrincDiv (ℂ ⧸ L) ≤ (Div.evalSumHom (X := ℂ ⧸ L)).ker := by
  constructor
  · intro hTL D hD
    rw [AddMonoidHom.mem_ker]
    exact evalSumHom_eq_zero_on_PrincDiv_of_TLDivSum L hTL D hD
  · intro h_ker f
    have h_mem : principalDivisorMap f ∈ PrincDiv (ℂ ⧸ L) :=
      principalDivisorMap_mem_PrincDiv f
    have h_in_ker := h_ker h_mem
    rw [AddMonoidHom.mem_ker] at h_in_ker
    exact h_in_ker

/-! ## Closure under multiplicative-group operations on `MeromorphicNonzero`

These structural lemmas let `TLDivSumHypothesis L` be discharged by
verifying it on a *multiplicative generating set* of
`MeromorphicNonzero (ℂ ⧸ L)`. Each step is one rewrite chain. -/

/-- **`TLDivSum` holds at `1`.** -/
@[simp] theorem TLDivSum_holds_at_one :
    Div.evalSum
      (principalDivisorMap (1 : MeromorphicNonzero (ℂ ⧸ L)))
      = (0 : ℂ ⧸ L) := by
  rw [principalDivisorMap_one, Div.evalSum_zero]

/-- **`TLDivSum` is closed under products.** -/
theorem TLDivSum_holds_at_mul
    (f g : MeromorphicNonzero (ℂ ⧸ L))
    (hf : Div.evalSum (principalDivisorMap f) = (0 : ℂ ⧸ L))
    (hg : Div.evalSum (principalDivisorMap g) = (0 : ℂ ⧸ L)) :
    Div.evalSum (principalDivisorMap (f * g)) = (0 : ℂ ⧸ L) := by
  rw [principalDivisorMap_mul, Div.evalSum_add, hf, hg, add_zero]

/-- **`TLDivSum` is closed under `invMer` (representative-level inverse).** -/
theorem TLDivSum_holds_at_invMer
    (f : MeromorphicNonzero (ℂ ⧸ L))
    (hf : Div.evalSum (principalDivisorMap f) = (0 : ℂ ⧸ L)) :
    Div.evalSum
      (principalDivisorMap (MeromorphicNonzero.invMer f))
      = (0 : ℂ ⧸ L) := by
  rw [principalDivisorMap_neg, Div.evalSum_neg, hf, neg_zero]

/-- **`TLDivSum` holds at any nonzero constant function.**

Concrete first step in a multiplicative-generators discharge program.
The principal divisor of a nonzero constant is the zero divisor, whose
`evalSum` is `0`. -/
@[simp] theorem TLDivSum_holds_at_const
    (c : ℂ) (hc : c ≠ 0) :
    Div.evalSum
      (principalDivisorMap (MeromorphicNonzero.const (X := ℂ ⧸ L) c hc))
      = (0 : ℂ ⧸ L) := by
  rw [principalDivisorMap_const, Div.evalSum_zero]

/-! ## Multiplicative-generators reduction

The "`TLDivSum` holds for `f`" property is closed under the
multiplicative-group operations on `MeromorphicNonzero (ℂ ⧸ L)`
(`TLDivSum_holds_at_one`, `_at_mul`, `_at_invMer`). The inductive
closure of an arbitrary generating set `S` therefore satisfies the
property whenever every element of `S` does. -/

/-- The inductive closure of a set `S : Set (MeromorphicNonzero (ℂ ⧸ L))`
under `1`, `*`, and `MeromorphicNonzero.invMer`. -/
inductive MultiplicativeClosure
    (S : Set (MeromorphicNonzero (ℂ ⧸ L))) :
    MeromorphicNonzero (ℂ ⧸ L) → Prop
  | base {f : MeromorphicNonzero (ℂ ⧸ L)} (hf : f ∈ S) :
      MultiplicativeClosure S f
  | one : MultiplicativeClosure S 1
  | mul {f g : MeromorphicNonzero (ℂ ⧸ L)}
      (hf : MultiplicativeClosure S f)
      (hg : MultiplicativeClosure S g) :
      MultiplicativeClosure S (f * g)
  | invMer {f : MeromorphicNonzero (ℂ ⧸ L)}
      (hf : MultiplicativeClosure S f) :
      MultiplicativeClosure S (MeromorphicNonzero.invMer f)

/-- **Generators-to-closure reduction.**

If `TLDivSum` holds for every `f ∈ S`, then it holds for every `f` in
the multiplicative closure of `S`. -/
theorem TLDivSum_holds_at_of_multiplicativeClosure
    {S : Set (MeromorphicNonzero (ℂ ⧸ L))}
    (hS : ∀ f ∈ S,
        Div.evalSum (principalDivisorMap f) = (0 : ℂ ⧸ L))
    {f : MeromorphicNonzero (ℂ ⧸ L)}
    (hf : MultiplicativeClosure L S f) :
    Div.evalSum (principalDivisorMap f) = (0 : ℂ ⧸ L) := by
  induction hf with
  | base h => exact hS _ h
  | one => exact TLDivSum_holds_at_one L
  | mul _ _ ih_f ih_g => exact TLDivSum_holds_at_mul L _ _ ih_f ih_g
  | invMer _ ih_f => exact TLDivSum_holds_at_invMer L _ ih_f

/-- **Discharge of `TLDivSumHypothesis L` from a multiplicatively
generating set.**

If `S` generates `MeromorphicNonzero (ℂ ⧸ L)` multiplicatively (i.e.
every `f : MeromorphicNonzero (ℂ ⧸ L)` lies in the inductive closure
of `S` under `1`, `*`, `invMer`) and `TLDivSum` holds on every element
of `S`, then `TLDivSumHypothesis L` holds. -/
theorem TLDivSumHypothesis_of_multiplicatively_generating
    {S : Set (MeromorphicNonzero (ℂ ⧸ L))}
    (h_gen : ∀ f : MeromorphicNonzero (ℂ ⧸ L), MultiplicativeClosure L S f)
    (hS : ∀ f ∈ S,
        Div.evalSum (principalDivisorMap f) = (0 : ℂ ⧸ L)) :
    TLDivSumHypothesis L := by
  intro f
  exact TLDivSum_holds_at_of_multiplicativeClosure L hS (h_gen f)

end ComplexTorus

end JacobianChallenge

end
