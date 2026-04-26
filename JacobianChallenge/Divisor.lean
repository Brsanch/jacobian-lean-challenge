/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicAt
import Mathlib.Topology.LocallyFinsupp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option diagnostics.threshold 100

/-! # Divisors on a complex manifold

This file scaffolds the divisor-class construction of the Jacobian for a
compact complex manifold `X` modelled on `ℂ`. The full chain
`Div → Div⁰ → Pic⁰` is *not* completed in this commit — the proof of
additivity of `Div.degree` runs into several mathlib-API mismatches at
the pinned commit (`Function.locallyFinsuppWithin.coe_add` rewriting
through `Finset.sum_subset` over a union of supports). Those mismatches
are diagnosable but eat CI cycles, so this commit ships only what is
known to compile cleanly: the carrier `Div X` and the pointwise
`Div.degree` for compact Hausdorff `X`.

## What's in this file

* `JacobianChallenge.Div X` — the additive group of divisors on `X`,
  defined as `Function.locallyFinsuppWithin (Set.univ : Set X) ℤ` (an
  abbreviation; the `AddCommGroup` instance is inherited).
* `JacobianChallenge.Div.supportFinset D` — the support as a `Finset X`,
  using `Function.locallyFinsuppWithin.finiteSupport` (which requires
  `[T2Space X] [CompactSpace X]`).
* `JacobianChallenge.Div.degree D` — `∑ x ∈ D.supportFinset, D x`.
* `JacobianChallenge.Div.degree_zero` — `degree (0 : Div X) = 0`.

## Owed for follow-up (not in this commit)

1. `Div.degree_add` — additivity of the degree. The proof has to align
   with `Function.locallyFinsuppWithin`'s coercion API at this pin (no
   `add_apply` lemma; the existing `coe_add` uses pointwise function-
   equality), and the `Finset.sum_subset`-over-union-of-supports proof
   tripped a parse / `unfold_let` / `show` chain in the previous
   attempt.
2. `Div.degreeHom : Div X →+ ℤ` — packages `degree` + `degree_zero` +
   `degree_add`.
3. `Div0 X := degreeHom.ker` — degree-zero subgroup.
4. `principalDivisor f` and the `PrincDiv X : AddSubgroup (Div X)`
   subgroup — needs the chart-independence of `mmeromorphicOrderAt`
   (owed by `MeromorphicAt.lean`) plus, ultimately, the residue
   theorem on a compact Riemann surface for the degree-0 property.
5. `Pic0 X := Div0 X ⧸ PrincDiv.subgroupOf Div0` — the Picard group of
   degree-zero divisors; `AddCommGroup` instance via `inferInstanceAs`.

The structure to land items 1–5 cleanly is sketched in the design
notes; see commit history for the prior attempt.
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
  -- The support of `0 : Div X` is empty, so `supportFinset` is empty,
  -- and the sum over an empty finset is `0`.
  unfold degree supportFinset
  have hsupp : ((0 : Div X) : X → ℤ).support = (∅ : Set X) := by
    ext x; simp
  have hempty : (Function.locallyFinsuppWithin.finiteSupport (0 : Div X)
                  isCompact_univ).toFinset = (∅ : Finset X) := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro x hx
    have hx' : x ∈ ((0 : Div X) : X → ℤ).support := by
      simpa using (Set.Finite.mem_toFinset _).1 hx
    have : x ∈ (∅ : Set X) := by simpa [hsupp] using hx'
    exact this.elim
  simp [hempty]

end Div

end JacobianChallenge
