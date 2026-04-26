/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor
import JacobianChallenge.Divisor.Single
import JacobianChallenge.Divisor.FiberSum
import JacobianChallenge.Jacobian

set_option diagnostics.threshold 100

/-! # `Pic⁰`-level pullback under constant-fibre cardinality

This file descends `Div.fiberSum` (built in `JacobianChallenge.Divisor.FiberSum`)
through the chain `Div Y →+ Div X` ↝ `Div⁰ Y →+ Div⁰ X` ↝ `Pic⁰ Y →+ Pic⁰ X`,
under the hypothesis that every fibre of `f : X → Y` has the same finite
cardinality `N`.

The point of this file is to make the future swap inside `Jacobian.pullback`
(currently a zero stub in `Basic.lean`) a one-line change: once the eventual
classical input "every analytic non-constant `f : X → Y` between compact
connected Riemann surfaces has constant fibre cardinality on regular fibres"
lands, the body of `Jacobian.pullback` becomes
`Pic0.pullback f h_finite_fibers (degreeFiber f hf) h_const_card`.

## Contents

* `JacobianChallenge.Div.degree_fiberSum` — degree of `fiberSum f hf D` equals
  the weighted sum `∑_{y ∈ supp D} D(y) · |f⁻¹{y}|`.
* `JacobianChallenge.Div.fiberSum_mem_Div0_of_const_card` — if every fibre has
  the same finite cardinality `N`, then `Div.fiberSum f hf` sends `Div⁰ Y`
  into `Div⁰ X` (it scales degrees by `N`).
* `JacobianChallenge.Pic0.divPullback` — the descent of `Div.fiberSum` to
  `Div0 Y →+ Div0 X` under the constant-fibre-cardinality hypothesis.
* `JacobianChallenge.Pic0.pullback` — the same construction promoted to
  `Pic0 Y →+ Pic0 X`. With the placeholder `PrincDiv = ⊥` the descent through
  the quotient is automatic (cf. `Pic0.pushforward` in `Jacobian.lean`).
* `JacobianChallenge.Pic0.pullback_mk` — `pullback` on a representative class.

## Anti-cheat note

The hypothesis `hN : ∀ y, (hf y).toFinset.card = N` is *load-bearing* in
`divPullback`: it is used in `divPullback_mem_Div0` to turn the weighted
degree formula `∑ y ∈ D.supportFinset, D y * ((hf y).toFinset.card : ℤ)`
into `N * D.degree`, which is `0` when `D ∈ Div0 Y`. Without that hypothesis
the cast `((hf y).toFinset.card : ℤ)` varies with `y` and the sum need not
factor as `N * D.degree`. -/

namespace JacobianChallenge

/-! ### Degree of a fibre-sum -/

namespace Div

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [DecidableEq X]

/-- The degree of `fiberSum f hf D` is the weighted sum
`∑_{y ∈ supp D} D(y) · |f⁻¹{y}|`. -/
lemma degree_fiberSum
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) (D : Div Y) :
    (Div.fiberSum f hf D).degree
      = ∑ y ∈ D.supportFinset, D y * ((hf y).toFinset.card : ℤ) := by
  classical
  -- Reduce `degree` to `degreeHom` so we can transport through the
  -- `AddMonoidHom` `fiberSum f hf`.
  have hLHS : (Div.fiberSum f hf D).degree
      = degreeHom (X := X) (Div.fiberSum f hf D : Div X) := rfl
  rw [hLHS]
  -- Unfold the bundled hom application to its `fiberSumFun` form, which is
  -- a finite sum over `D.supportFinset`.
  have hsum : (Div.fiberSum f hf D : Div X)
      = ∑ y ∈ D.supportFinset,
          D y • (∑ x ∈ (hf y).toFinset, Div.single x) := by
    show Div.fiberSumFun f hf D = _
    rfl
  rw [hsum, map_sum]
  -- Each term is `degreeHom (D y • (∑ x ∈ fiber, single x)) = D y * card`.
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [map_zsmul, degreeHom_apply]
  -- `degree (∑ x ∈ (hf y).toFinset, Div.single x) = (card : ℤ)`.
  have hfib :
      (∑ x ∈ (hf y).toFinset, (Div.single x : Div X)).degree
        = ((hf y).toFinset.card : ℤ) := by
    have hsub :
        (∑ x ∈ (hf y).toFinset, (Div.single x : Div X)).degree
          = degreeHom (X := X) (∑ x ∈ (hf y).toFinset, Div.single x) := rfl
    rw [hsub, map_sum]
    -- Each summand `degreeHom (Div.single x) = 1`.
    have hone : ∀ x ∈ (hf y).toFinset,
        degreeHom (X := X) (Div.single x : Div X) = 1 := by
      intro x _
      rw [degreeHom_apply, degree_single]
    rw [Finset.sum_congr rfl hone]
    -- `∑ x ∈ S, (1 : ℤ) = (S.card : ℤ)`.
    simp
  rw [hfib]
  -- Goal: `D y • ((hf y).toFinset.card : ℤ) = D y * ((hf y).toFinset.card : ℤ)`.
  -- ℤ-smul on ℤ is multiplication (`smul_eq_mul`).
  rw [smul_eq_mul]

/-- If every fibre of `f` has the *same* finite cardinality `N`, then
`Div.fiberSum f hf` sends `Div⁰ Y` into `Div⁰ X` (it scales degrees by `N`). -/
lemma fiberSum_mem_Div0_of_const_card
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) (N : ℕ)
    (hN : ∀ y, (hf y).toFinset.card = N)
    {D : Div Y} (hD : D ∈ Div0 Y) :
    Div.fiberSum f hf D ∈ Div0 X := by
  classical
  -- Membership in `Div0 X` is zero degree.
  rw [JacobianChallenge.mem_Div0_iff, degree_fiberSum]
  -- Goal: `∑ y ∈ supp D, D y * ((hf y).toFinset.card : ℤ) = 0`.
  -- Replace each `((hf y).toFinset.card : ℤ)` by `(N : ℤ)` using `hN`.
  have hcast : ∀ y ∈ D.supportFinset,
      D y * ((hf y).toFinset.card : ℤ) = D y * (N : ℤ) := by
    intro y _
    rw [hN y]
  rw [Finset.sum_congr rfl hcast]
  -- Factor out `(N : ℤ)`: `∑ y, D y * N = (∑ y, D y) * N = D.degree * N`.
  rw [← Finset.sum_mul]
  -- The bare `∑ y ∈ D.supportFinset, D y` is `D.degree` by definition.
  have hdeg : ∑ y ∈ D.supportFinset, (D : Y → ℤ) y = D.degree := rfl
  rw [hdeg]
  -- `D.degree = 0` from `D ∈ Div0 Y`.
  rw [(JacobianChallenge.mem_Div0_iff D).mp hD, zero_mul]

end Div

/-! ### `Div0`-level and `Pic0`-level pullback -/

namespace Pic0

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [DecidableEq X]

/-- The constant-fibre-cardinality version of the divisor pullback,
descending `Div.fiberSum` to `Div0 Y →+ Div0 X`. -/
noncomputable def divPullback
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) (N : ℕ)
    (hN : ∀ y, (hf y).toFinset.card = N) :
    Div0 Y →+ Div0 X :=
  AddMonoidHom.codRestrict
    ((Div.fiberSum f hf).comp (Div0 Y).subtype) (Div0 X)
    (fun D => Div.fiberSum_mem_Div0_of_const_card f hf N hN D.2)

/-- Compute the underlying `Div X`-element of `divPullback f hf N hN D`. -/
@[simp] lemma divPullback_coe
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) (N : ℕ)
    (hN : ∀ y, (hf y).toFinset.card = N) (D : Div0 Y) :
    ((divPullback f hf N hN D : Div0 X) : Div X)
      = Div.fiberSum f hf (D : Div Y) := rfl

/-- Same construction promoted to `Pic⁰ Y →+ Pic⁰ X`. With the placeholder
`PrincDiv = ⊥` the descent through the quotient is automatic
(cf. `Pic0.pushforward` in `Jacobian.lean` for the same trick). -/
noncomputable def pullback
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) (N : ℕ)
    (hN : ∀ y, (hf y).toFinset.card = N) :
    Pic0 Y →+ Pic0 X := by
  refine QuotientAddGroup.map
    ((PrincDiv Y).addSubgroupOf (Div0 Y))
    ((PrincDiv X).addSubgroupOf (Div0 X))
    (divPullback f hf N hN) ?_
  -- LHS is `⊥` since `PrincDiv Y = ⊥`, so the comap condition is vacuous.
  intro D hD
  have hBot : (PrincDiv Y).addSubgroupOf (Div0 Y) = ⊥ := by
    unfold PrincDiv
    simp [AddSubgroup.addSubgroupOf]
  rw [hBot, AddSubgroup.mem_bot] at hD
  -- `D = 0`, so `divPullback _ D = 0 ∈ any subgroup`.
  subst hD
  rw [AddSubgroup.mem_comap]
  rw [map_zero]
  exact AddSubgroup.zero_mem _

@[simp] lemma pullback_mk
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) (N : ℕ)
    (hN : ∀ y, (hf y).toFinset.card = N) (D : Div0 Y) :
    pullback f hf N hN (QuotientAddGroup.mk D : Pic0 Y)
      = (QuotientAddGroup.mk (divPullback f hf N hN D) : Pic0 X) := rfl

/-! ### Contravariant composition at `Pic⁰` level -/

section Comp

variable {X Y Z : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
  [DecidableEq X] [DecidableEq Y]

/-- Contravariant composition at the `Pic⁰` level: pulling back along
    `g ∘ f` agrees with first pulling back along `g` then along `f`,
    provided the cardinality witnesses compose multiplicatively
    (`(g∘f)⁻¹{z}` has cardinality `M * N` when fibres of `g` have
    cardinality `M` and fibres of `f` have cardinality `N`). -/
lemma pullback_comp_apply
    (f : X → Y) (g : Y → Z)
    (hf : ∀ y, (f ⁻¹' {y}).Finite)
    (hg : ∀ z, (g ⁻¹' {z}).Finite)
    (hgf : ∀ z, ((g ∘ f) ⁻¹' {z}).Finite)
    (Nf Ng : ℕ)
    (hNf : ∀ y, (hf y).toFinset.card = Nf)
    (hNg : ∀ z, (hg z).toFinset.card = Ng)
    (hNgf : ∀ z, (hgf z).toFinset.card = Ng * Nf)
    (P : Pic0 Z) :
    pullback (g ∘ f) hgf (Ng * Nf) hNgf P
      = pullback f hf Nf hNf (pullback g hg Ng hNg P) := by
  refine QuotientAddGroup.induction_on P ?_
  intro D
  rw [pullback_mk, pullback_mk, pullback_mk]
  -- Need `divPullback (g ∘ f) hgf (Ng * Nf) hNgf D
  --        = divPullback f hf Nf hNf (divPullback g hg Ng hNg D)`.
  have hDiv : (divPullback (g ∘ f) hgf (Ng * Nf) hNgf D : Div X)
      = (divPullback f hf Nf hNf (divPullback g hg Ng hNg D) : Div X) := by
    rw [divPullback_coe, divPullback_coe, divPullback_coe]
    -- Reduces to the underlying `fiberSum`-level composition, freshly merged
    -- as `Div.fiberSum_comp_apply` in `FiberSum.lean`.
    exact Div.fiberSum_comp_apply f g hf hg hgf (D : Div Z)
  have h : divPullback (g ∘ f) hgf (Ng * Nf) hNgf D
      = divPullback f hf Nf hNf (divPullback g hg Ng hNg D) :=
    Subtype.ext hDiv
  rw [h]

end Comp

end Pic0

end JacobianChallenge
