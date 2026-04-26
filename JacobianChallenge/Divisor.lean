/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicAt
import Mathlib.Topology.LocallyFinsupp
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option diagnostics.threshold 100

/-! # Divisors and `Pic⁰` on a complex manifold

This file scaffolds the divisor-class group construction of the Jacobian for a
compact complex manifold `X` modelled on `ℂ`:

* `Div X` — the additive group of divisors on `X`, defined as the mathlib
  type `Function.locallyFinsuppWithin (Set.univ : Set X) ℤ`.
* `Div.degree D` — the integer `∑ x ∈ D.support, D x`, well-defined because
  on a compact Hausdorff space the support of a `locallyFinsuppWithin` is
  finite (`Function.locallyFinsuppWithin.finiteSupport`).
* `Div.degreeHom : Div X →+ ℤ` — the degree as an additive group hom.
* `Div0 X` — the kernel `AddSubgroup` of `degreeHom`, i.e. degree-0 divisors.
* `PrincDiv X` — the subgroup of *principal* divisors. **PLACEHOLDER**: see
  the docstring of `PrincDiv` below; this is set to `⊥` at this pin because
  the residue-theorem chain needed to prove `principalDivisor f ∈ Div0` (i.e.
  that the orders of zeros and poles of a global meromorphic function on a
  compact Riemann surface sum to zero) is not in mathlib at
  `8e3c989104daaa052921bf43de9eef0e1ac9fbf5`. The *type signature* of `Pic0`
  is therefore correct (a quotient of an abelian group by a subgroup) and
  carries an `AddCommGroup` instance, but the mathematical content of
  `PrincDiv` is currently the trivial subgroup, so `Pic0 X` is at this pin
  *isomorphic* to `Div0 X` — not yet the analytic Picard group.
* `Pic0 X := Div0 X ⧸ PrincDiv.subgroupOf Div0` — the Picard group of
  degree-0 divisors. Inherits `AddCommGroup`.

The compactness hypothesis `[CompactSpace X]` is required for `degree` to make
sense pointwise as a finite sum (without compactness, the support of a
locally-finite divisor is at most countable but need not be finite).

## Owed work (intentionally not in this file)

1. The full `principalDivisor` map from a chart-pulled-back
   `MMeromorphicOn I f Set.univ` to `Div X` (orders at each point assembled
   into a `locallyFinsuppWithin`). This needs the chart-independence of
   `mmeromorphicOrderAt` (already owed by `MeromorphicAt.lean`) plus the
   local-finiteness of zeros/poles of a non-zero meromorphic function on a
   compact manifold. Both are tracked in `OPEN.md`.
2. The residue-theorem identity giving `(principalDivisor f).degree = 0`
   on a compact Riemann surface, which would let us replace the `⊥`
   placeholder by the genuine subgroup of principal divisors.
3. The Abel–Jacobi map `Pic0 X → Jacobian X` and its bijectivity for
   compact Riemann surfaces of genus `g`.
-/

namespace JacobianChallenge

/-! ### Divisors -/

/-- A *divisor* on a topological space `X` is a `ℤ`-valued function on `X`
whose support is locally finite. We use the mathlib carrier
`Function.locallyFinsuppWithin (Set.univ : Set X) ℤ`. The `AddCommGroup`
instance is inherited from mathlib. -/
abbrev Div (X : Type*) [TopologicalSpace X] : Type _ :=
  Function.locallyFinsuppWithin (Set.univ : Set X) ℤ

/-- The `AddCommGroup` structure on `Div X` is the one provided by
`Function.locallyFinsuppWithin`. -/
example (X : Type*) [TopologicalSpace X] : AddCommGroup (Div X) := inferInstance

/-! ### Degree of a divisor on a compact space -/

namespace Div

variable {X : Type*} [TopologicalSpace X]

/-- On a compact Hausdorff space, the support of a divisor (as a `Set X`) is
finite, so admits a `Finset` representative. -/
noncomputable def supportFinset [T2Space X] [CompactSpace X] (D : Div X) :
    Finset X :=
  (D.finiteSupport isCompact_univ).toFinset

/-- The *degree* of a divisor on a compact Hausdorff space is the integer
sum of its values over its (finite) support. -/
noncomputable def degree [T2Space X] [CompactSpace X] (D : Div X) : ℤ :=
  ∑ x ∈ D.supportFinset, D x

@[simp] lemma degree_zero [T2Space X] [CompactSpace X] :
    degree (0 : Div X) = 0 := by
  classical
  -- The support of `0 : Div X` is empty, so `supportFinset` is empty.
  unfold degree supportFinset
  have hsupp : ((0 : Div X) : X → ℤ).support = (∅ : Set X) := by
    ext x; simp
  -- Rewrite the support as ∅, then the toFinset is ∅, then the sum is 0.
  have : (Function.locallyFinsuppWithin.finiteSupport (0 : Div X)
            isCompact_univ).toFinset = (∅ : Finset X) := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro x hx
    have hx' : x ∈ ((0 : Div X) : X → ℤ).support := by
      simpa using (Set.Finite.mem_toFinset _).1 hx
    -- `Function.support` of `0` is empty, contradiction.
    have : x ∈ (∅ : Set X) := by simpa [hsupp] using hx'
    exact this.elim
  simp [this]

lemma degree_add [T2Space X] [CompactSpace X] (D₁ D₂ : Div X) :
    degree (D₁ + D₂) = degree D₁ + degree D₂ := by
  classical
  -- Combine the three supports into one common finset and split the sum.
  unfold degree
  set S₁ : Finset X := D₁.supportFinset
  set S₂ : Finset X := D₂.supportFinset
  set S₁₂ : Finset X := (D₁ + D₂).supportFinset
  set S : Finset X := S₁ ∪ S₂ ∪ S₁₂
  -- Each individual sum extends to S because added points carry value 0.
  have h₁ : ∑ x ∈ S₁, D₁ x = ∑ x ∈ S, D₁ x := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro x hx; exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
    intro x _ hxS₁
    -- x ∉ supportFinset D₁ ⇒ x ∉ support D₁ ⇒ D₁ x = 0
    by_contra hne
    apply hxS₁
    show x ∈ S₁
    unfold_let S₁
    unfold supportFinset
    rw [Set.Finite.mem_toFinset]
    exact hne
  have h₂ : ∑ x ∈ S₂, D₂ x = ∑ x ∈ S, D₂ x := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro x hx; exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
    intro x _ hxS₂
    by_contra hne
    apply hxS₂
    show x ∈ S₂
    unfold_let S₂
    unfold supportFinset
    rw [Set.Finite.mem_toFinset]
    exact hne
  have h₁₂ : ∑ x ∈ S₁₂, (D₁ + D₂) x = ∑ x ∈ S, (D₁ + D₂) x := by
    refine Finset.sum_subset ?_ ?_
    · intro x hx; exact Finset.mem_union_right _ hx
    intro x _ hxS₁₂
    by_contra hne
    apply hxS₁₂
    show x ∈ S₁₂
    unfold_let S₁₂
    unfold supportFinset
    rw [Set.Finite.mem_toFinset]
    -- (D₁ + D₂) x ≠ 0 ⇒ x ∈ support of (D₁ + D₂)
    intro hx0
    apply hne
    -- coe_add: ((D₁ + D₂) : X → ℤ) x = D₁ x + D₂ x
    have := Function.locallyFinsuppWithin.coe_add D₁ D₂
    have hx0' : D₁ x + D₂ x = 0 := by
      have := congrArg (fun g : X → ℤ => g x) this
      simp at this
      simpa [this] using hx0
    -- conclude (D₁ + D₂) x = 0 in the FunLike sense
    show (D₁ + D₂) x = 0
    have h := Function.locallyFinsuppWithin.coe_add D₁ D₂
    have := congrArg (fun g : X → ℤ => g x) h
    simp at this
    simpa [this] using hx0'
  rw [h₁, h₂, h₁₂, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  -- Pointwise: (D₁ + D₂) x = D₁ x + D₂ x via `coe_add`.
  have h := Function.locallyFinsuppWithin.coe_add D₁ D₂
  have := congrArg (fun g : X → ℤ => g x) h
  simp at this
  exact this

/-- The degree, packaged as an additive group homomorphism `Div X →+ ℤ`. -/
noncomputable def degreeHom [T2Space X] [CompactSpace X] : Div X →+ ℤ where
  toFun := degree
  map_zero' := degree_zero
  map_add' := degree_add

@[simp] lemma degreeHom_apply [T2Space X] [CompactSpace X] (D : Div X) :
    degreeHom D = degree D := rfl

end Div

/-! ### Degree-zero divisors and the placeholder principal subgroup -/

/-- The `AddSubgroup` of degree-zero divisors on a compact Hausdorff space. -/
noncomputable def Div0 (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] : AddSubgroup (Div X) :=
  (Div.degreeHom : Div X →+ ℤ).ker

/-- The subgroup of *principal* divisors.

**PLACEHOLDER (Option B in the design notes).** A principal divisor is the
divisor `(f) := ∑_x ord_x(f) · [x]` of a non-zero global meromorphic function
`f : X → ℂ`. To define this honestly we would need:

1. The chart-independence of `mmeromorphicOrderAt I f x` (currently owed by
   `JacobianChallenge.Manifold.MeromorphicAt` — see its `## Owed work`
   section).
2. Local finiteness of `{x | mmeromorphicOrderAt I f x ≠ 0}` for a non-zero
   meromorphic `f`, packaged into a `Function.locallyFinsuppWithin` on
   `Set.univ`.
3. The residue-theorem identity, which on a compact Riemann surface yields
   `∑_x ord_x(f) = 0`, i.e. that the constructed divisor *does* lie in
   `Div0 X`. This is the deep input from complex analysis on compact Riemann
   surfaces and is *not* present in mathlib at the pin
   `8e3c989104daaa052921bf43de9eef0e1ac9fbf5`.

Until items (1)–(3) are in place we set `PrincDiv X := ⊥`, the trivial
subgroup. The *type* `Pic0 X` defined below is therefore well-formed and
carries the expected `AddCommGroup` instance, but the *mathematical content*
of `Pic0 X` at this pin coincides with `Div0 X` itself rather than with the
analytic Picard group of degree-zero line bundles. This placeholder is
deliberate: it lets downstream files (`JacobianChallenge.Basic` item 12) refer
to `Pic0 X` as an abelian group target while the underlying analytic content
is being built. Do not prove statements about `Pic0 X` that rely on
`PrincDiv` actually being the principal subgroup. -/
noncomputable def PrincDiv (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] : AddSubgroup (Div X) := ⊥

/-! ### The Picard group of degree-zero divisors -/

/-- The Picard group of degree-zero divisors,
`Pic⁰ X := Div⁰ X / Princ X`. See the docstring of `PrincDiv` for the
placeholder caveat: at this mathlib pin `PrincDiv X = ⊥`, so this quotient is
*type-correct* (an `AddCommGroup`) but does not yet implement the analytic
Picard group. -/
noncomputable def Pic0 (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] : Type _ :=
  Div0 X ⧸ (PrincDiv X).addSubgroupOf (Div0 X)

namespace Pic0

variable (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]

noncomputable instance : AddCommGroup (Pic0 X) :=
  inferInstanceAs (AddCommGroup (Div0 X ⧸ _))

end Pic0

end JacobianChallenge
