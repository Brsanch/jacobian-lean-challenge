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

end Pic0

/-! ### `pushforward ∘ pullback` is multiplication by the (constant) fibre cardinality

This is the divisor-side of challenge item 24 (`pushforward_pullback`). The
core lemma `Div.singletonMap_fiberSum` is a pure divisor identity: collapsing
each fibre back to its image multiplies multiplicities by the (constant)
fibre cardinality `N`. The `Pic0`-level statement
`Pic0.pushforward_pullback` follows by quotient induction. -/

namespace Div

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [DecidableEq X] [DecidableEq Y]

/-- The composition `singletonMap f ∘ fiberSum f hf` collapses each fibre
    back to its image and so multiplies divisor multiplicities by the
    (constant) fibre cardinality. -/
lemma singletonMap_fiberSum
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite)
    (N : ℕ) (hN : ∀ y, (hf y).toFinset.card = N)
    (D : Div Y) :
    Div.singletonMap f (Div.fiberSum f hf D) = (N : ℤ) • D := by
  classical
  -- Step 1: rewrite `fiberSum f hf D` as its sum-of-smul form.
  have hfs : Div.fiberSum f hf D
      = ∑ y ∈ D.supportFinset,
          D y • (∑ x ∈ (hf y).toFinset, (Div.single x : Div X)) := by
    show Div.fiberSumFun f hf D = _
    rfl
  rw [hfs, map_sum]
  -- Step 2: for each `y ∈ supp D`, push `singletonMap f` through the
  -- ℤ-smul and the inner sum, then simplify each `Div.single (f x)` to
  -- `Div.single y` (since `x ∈ (hf y).toFinset` means `f x = y`), and
  -- collapse the resulting constant sum to `(card · single y) = N · single y`.
  have hterm : ∀ y ∈ D.supportFinset,
      Div.singletonMap f
          (D y • (∑ x ∈ (hf y).toFinset, (Div.single x : Div X)))
        = D y • ((N : ℤ) • (Div.single y : Div Y)) := by
    intro y _hy
    -- Push `singletonMap f` through the ℤ-smul.
    rw [map_zsmul]
    -- Push `singletonMap f` through the inner sum.
    rw [map_sum]
    -- Strip the common `D y • ·` by `congr 1`.
    congr 1
    -- Goal: ∑ x ∈ (hf y).toFinset, singletonMap f (single x)
    --       = (N : ℤ) • Div.single y.
    -- Each summand equals `Div.single (f x) = Div.single y` since `f x = y`.
    have hsumm : ∀ x ∈ (hf y).toFinset,
        Div.singletonMap f (Div.single x : Div X) = (Div.single y : Div Y) := by
      intro x hx
      rw [Set.Finite.mem_toFinset] at hx
      -- `hx : x ∈ f ⁻¹' {y}`, i.e., `f x = y`.
      have hfx : f x = y := hx
      rw [Div.singletonMap_single, hfx]
    rw [Finset.sum_congr rfl hsumm]
    -- Constant sum: `∑ x ∈ S, c = S.card • c` (for `c : Div Y`).
    rw [Finset.sum_const]
    -- Replace `(hf y).toFinset.card` by `N` via `hN`.
    rw [hN y]
    -- Goal: `N • Div.single y = (N : ℤ) • Div.single y`.
    -- The ℕ-smul on an `AddCommGroup` agrees with the ℤ-smul of the cast.
    -- Prove by induction on `N` (extracted inline to avoid depending on a
    -- specific mathlib lemma name).
    have hcast : ∀ (m : ℕ) (c : Div Y), m • c = (m : ℤ) • c := by
      intro m c
      induction m with
      | zero => simp
      | succ k ih =>
        rw [succ_nsmul, ih, Nat.cast_succ, add_zsmul, one_zsmul]
    exact hcast N (Div.single y : Div Y)
  rw [Finset.sum_congr rfl hterm]
  -- Step 3: pull `(N : ℤ) • ·` outside the outer sum and identify the
  -- remaining sum `∑ y ∈ supp D, D y • Div.single y` with `D` (this is
  -- the same identity that `Div.singletonMap_id_apply` proves for the
  -- identity map).
  -- First, swap `D y • ((N : ℤ) • single y)` to `(N : ℤ) • (D y • single y)`
  -- using ℤ-smul commutativity.
  have hswap : ∀ y ∈ D.supportFinset,
      D y • ((N : ℤ) • (Div.single y : Div Y))
        = (N : ℤ) • (D y • (Div.single y : Div Y)) := by
    intro y _
    -- `m • (n • x) = (m * n) • x = (n * m) • x = n • (m • x)` for ℤ-smul.
    rw [smul_comm]
  rw [Finset.sum_congr rfl hswap]
  -- Pull `(N : ℤ) • ·` out via `Finset.smul_sum` (additivity of ℤ-smul over Finset.sum).
  rw [← Finset.smul_sum]
  -- Goal: `(N : ℤ) • ∑ y ∈ supp D, D y • single y = (N : ℤ) • D`.
  -- Identify the inner sum with `D` via `singletonMap_id_apply` on `Y`.
  have hD : (∑ y ∈ D.supportFinset, D y • (Div.single y : Div Y)) = D := by
    have h := Div.singletonMap_id_apply (X := Y) D
    -- `singletonMap (id : Y → Y) D = singletonMapFun id D
    --   = ∑ y ∈ supp D, D y • single (id y)
    --   = ∑ y ∈ supp D, D y • single y`.
    have hexp : Div.singletonMap (id : Y → Y) D
        = ∑ y ∈ D.supportFinset, D y • (Div.single y : Div Y) := by
      show Div.singletonMapFun (id : Y → Y) D = _
      rfl
    rw [hexp] at h
    exact h
  rw [hD]

end Div

namespace Pic0

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [DecidableEq X] [DecidableEq Y]

/-- The composite `pushforward ∘ pullback` is multiplication by the (constant)
fibre cardinality. This is the divisor-side of challenge item 24
(`pushforward_pullback`); the `Basic.lean` version replaces `N` with
`ContMDiff.degree f hf` and is gated on a derivation `Nonempty witness ⇒
constant-fibre-cardinality with that exact value`. -/
lemma pushforward_pullback
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite)
    (N : ℕ) (hN : ∀ y, (hf y).toFinset.card = N)
    (P : Pic0 Y) :
    Pic0.pushforward f (Pic0.pullback f hf N hN P) = (N : ℤ) • P := by
  -- Match the `Classical.decEq Y` instance used inside `divPushforwardHom`,
  -- so that `singletonMap (Y := Y) f` (whose `[DecidableEq Y]` instance is
  -- supplied here via `Classical.decEq Y`) is the *same* function as the one
  -- inside `divPushforwardHom`.
  letI : DecidableEq Y := Classical.decEq Y
  -- Quotient-induction on `P` to a representative `D : Div0 Y`.
  refine QuotientAddGroup.induction_on P ?_
  intro D
  -- Step through `pullback_mk` and `pushforward_mk`.
  rw [Pic0.pullback_mk, Pic0.pushforward_mk]
  -- Compare in `Pic0 Y`: both sides are quotient classes; reduce to a
  -- `Div0 Y`-equality, then to a `Div Y`-equality.
  -- RHS: `(N : ℤ) • mk D = mk ((N : ℤ) • D)` (ℤ-smul lifts pointwise from
  -- the AddCommGroup instance on the quotient).
  rw [show ((N : ℤ) • (QuotientAddGroup.mk D : Pic0 Y))
      = (QuotientAddGroup.mk ((N : ℤ) • D) : Pic0 Y) by
        rw [← QuotientAddGroup.mk_zsmul]]
  -- Equality of two quotient classes: it suffices that the underlying
  -- `Div0 Y`-elements are equal.
  congr 1
  -- Reduce `Div0 Y`-equality to `Div Y`-equality via `Subtype.ext`.
  apply Subtype.ext
  -- LHS coerces to `divPushforwardHom f (Div.fiberSum f hf D)`.
  -- RHS coerces to `(N : ℤ) • (D : Div Y)` (ℤ-smul on a subgroup is the
  -- pointwise ℤ-smul on the ambient group).
  show ((Pic0.divPushforward f (Pic0.divPullback f hf N hN D) : Div0 Y) : Div Y)
      = (((N : ℤ) • D : Div0 Y) : Div Y)
  rw [Pic0.divPushforward_coe, Pic0.divPullback_coe]
  -- Unfold `divPushforwardHom f` to `singletonMap (Y := Y) f` (which is what
  -- it is, after the `letI` above makes the `DecidableEq Y` instance match).
  change Div.singletonMap (Y := Y) f (Div.fiberSum f hf (D : Div Y))
      = (((N : ℤ) • D : Div0 Y) : Div Y)
  -- Apply the divisor-level identity.
  rw [Div.singletonMap_fiberSum (Y := Y) f hf N hN (D : Div Y)]
  -- Goal: `(N : ℤ) • (D : Div Y) = (((N : ℤ) • D : Div0 Y) : Div Y)`.
  -- `(N : ℤ) • ·` on `Div0 Y` is the underlying `(N : ℤ) • ·` on `Div Y`.
  rfl

end Pic0

end JacobianChallenge
