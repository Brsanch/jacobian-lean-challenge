/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor
import JacobianChallenge.Divisor.Single

set_option diagnostics.threshold 100

/-! # Weighted divisor pullback along a finite-fiber map (ZZ179)

This file constructs the **multiplicity-weighted** version of
`Div.fiberSum` (in `Divisor/FiberSum.lean`). It will be the load-bearing
input for the honest `Jacobian.pullback` swap (see
`HANDOFF_ZZ177_PULLBACK_BLOCKER.md`): for branched analytic
`f : X → Y`, the unweighted fibre sum does **not** preserve `Div⁰`
(the fibre cardinality drops at branch points), but the
multiplicity-weighted sum does, with `∑_{x ∈ f⁻¹{y}} e_x(f) = deg(f)`
constant in `y` on regular fibres.

The weight function `e : X → ℕ` is supplied generically here; the
canonical choice is `e := manifoldRamificationIndex f`
(`Manifold/RamificationIndex.lean`), but no analytic hypothesis is
assumed at this level — the construction is purely algebraic.

## What's in this file

* `Div.fiberSumWeightedFun f hf e D` — the underlying function:
  `∑ y ∈ D.supportFinset, D y • (∑ x ∈ (hf y).toFinset, (e x : ℤ) • Div.single x)`.
* `Div.fiberSumWeightedFun_eq_sum` — extends the support sum to any
  ambient finset.
* `Div.fiberSumWeightedFun_zero` / `Div.fiberSumWeightedFun_add` —
  zero-preserving and additive.
* `Div.fiberSumWeighted f hf e : Div Y →+ Div X` — packaged.
* `Div.fiberSumWeighted_apply` — definitional unfolding.

The unweighted `Div.fiberSum` is recovered by setting `e ≡ 1`. -/

namespace JacobianChallenge

namespace Div

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [DecidableEq X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]

/-! ### The underlying function `Div Y → Div X` -/

/-- The *weighted* fibre-sum function. Each preimage point `x` contributes
`(e x : ℤ) • Div.single x` rather than `Div.single x`. -/
noncomputable def fiberSumWeightedFun
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) (e : X → ℕ) (D : Div Y) :
    Div X :=
  ∑ y ∈ D.supportFinset,
    D y • (∑ x ∈ (hf y).toFinset, (e x : ℤ) • Div.single x)

/-- The weighted fibre-sum agrees with the finset sum over any finset
containing the support of `D`. -/
lemma fiberSumWeightedFun_eq_sum
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) (e : X → ℕ)
    (D : Div Y) (S : Finset Y) (hS : D.supportFinset ⊆ S) :
    fiberSumWeightedFun f hf e D
      = ∑ y ∈ S,
          D y • (∑ x ∈ (hf y).toFinset, (e x : ℤ) • Div.single x) := by
  change (∑ y ∈ D.supportFinset,
            D y • (∑ x ∈ (hf y).toFinset, (e x : ℤ) • Div.single x) : Div X)
        = ∑ y ∈ S,
            D y • (∑ x ∈ (hf y).toFinset, (e x : ℤ) • Div.single x)
  refine Finset.sum_subset hS ?_
  intro y _ hyS
  have hy : (D : Div Y) y = 0 := apply_eq_zero_of_notMem_supportFinset hyS
  rw [hy, zero_smul]

/-- The weighted fibre-sum function sends `0` to `0`. -/
lemma fiberSumWeightedFun_zero
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) (e : X → ℕ) :
    fiberSumWeightedFun f hf e (0 : Div Y) = 0 := by
  classical
  unfold fiberSumWeightedFun
  have hempty : (0 : Div Y).supportFinset = (∅ : Finset Y) := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro y hy
    rw [mem_supportFinset] at hy
    apply hy
    show ((0 : Div Y) : Y → ℤ) y = 0
    rw [Function.locallyFinsuppWithin.coe_zero]
    rfl
  rw [hempty, Finset.sum_empty]

/-- Additivity of the weighted fibre-sum function. -/
lemma fiberSumWeightedFun_add
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) (e : X → ℕ)
    (D₁ D₂ : Div Y) :
    fiberSumWeightedFun f hf e (D₁ + D₂)
      = fiberSumWeightedFun f hf e D₁ + fiberSumWeightedFun f hf e D₂ := by
  classical
  set S : Finset Y :=
    (D₁ + D₂).supportFinset ∪ D₁.supportFinset ∪ D₂.supportFinset with hS_def
  have h12 : (D₁ + D₂).supportFinset ⊆ S := by
    intro y hy
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hy)
  have h1 : D₁.supportFinset ⊆ S := by
    intro y hy
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hy)
  have h2 : D₂.supportFinset ⊆ S := by
    intro y hy
    exact Finset.mem_union_right _ hy
  rw [fiberSumWeightedFun_eq_sum f hf e (D₁ + D₂) S h12,
      fiberSumWeightedFun_eq_sum f hf e D₁ S h1,
      fiberSumWeightedFun_eq_sum f hf e D₂ S h2]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro y _
  have hpt : ((D₁ + D₂ : Div Y) : Y → ℤ) y = (D₁ : Y → ℤ) y + (D₂ : Y → ℤ) y := by
    simp [Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
  rw [hpt, add_smul]

/-! ### Packaged as an `AddMonoidHom` -/

/-- The weighted divisor pullback as an `AddMonoidHom Div Y →+ Div X`. -/
noncomputable def fiberSumWeighted
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) (e : X → ℕ) :
    Div Y →+ Div X where
  toFun := fiberSumWeightedFun f hf e
  map_zero' := fiberSumWeightedFun_zero f hf e
  map_add' := fiberSumWeightedFun_add f hf e

@[simp] lemma fiberSumWeighted_apply
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) (e : X → ℕ) (D : Div Y) :
    fiberSumWeighted f hf e D = fiberSumWeightedFun f hf e D := rfl

end Div

end JacobianChallenge
