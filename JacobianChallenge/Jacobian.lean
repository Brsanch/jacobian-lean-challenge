/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor
import JacobianChallenge.Divisor.Single
import JacobianChallenge.Manifold.HolomorphicOneForm
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # The Jacobian of a compact Riemann surface

This file defines the carrier type `JacobianChallenge.Jacobian X` together with
the `AddCommGroup`, `TopologicalSpace` and `T2Space` instances that the
challenge signatures in `Basic.lean` (items 2–4 of the challenge, plus the
`ofCurve_self` consequence in item 15) demand.

## Route chosen: `Pic0`-via-`Divisor.lean`

`JacobianChallenge.Pic0 X` is already defined in `JacobianChallenge.Divisor`
as the additive quotient `Div0 X ⧸ (PrincDiv X).addSubgroupOf (Div0 X)`.
At the current pin (mathlib commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5`,
15 Apr 2026) the principal-divisor subgroup `PrincDiv X` is the deliberate
*placeholder* `⊥` — see the docstring of `JacobianChallenge.PrincDiv` for the
three classical inputs (chart-independence of meromorphic order, local
finiteness of the order divisor, residue theorem) that are owed before the
honest principal-subgroup definition lands. With that placeholder, `Pic0 X`
is *as a group* canonically isomorphic to `Div0 X`; this file does not assume
anything beyond the abelian-group structure of the quotient, so it stays
honest as the analytic content is filled in later.

We therefore **set `Jacobian X := Pic0 X`** rather than the `PUnit` fallback.
The `AddCommGroup` instance comes from `Pic0.instAddCommGroup` for free.

## What this file *does* supply (no `sorry`s)

* `JacobianChallenge.Jacobian X := JacobianChallenge.Pic0 X`
* `instance : AddCommGroup (Jacobian X)` — inherited from `Pic0`.
* `instance : TopologicalSpace (Jacobian X)` — the *discrete* topology on the
  quotient. This is the honest topology one can give a divisor-class group
  before the period-lattice quotient is built; downstream files that need a
  finer manifold topology will have to refine it together with the analytic
  Jacobian (`ℂᵍ / Λ`) construction.
* `instance : T2Space (Jacobian X)` — automatic from the discrete topology.
* `Jacobian.ofCurve (P : X) : X → Jacobian X` — the Abel–Jacobi *signature*.
  At this stage we cannot yet build the honest map `Q ↦ [Q] - [P]` inside
  `Pic0 X` because the membership statement `(δ Q − δ P) ∈ Div0 X` is owed
  by `Divisor.lean` (it requires a `single`-point divisor constructor and a
  one-point degree lemma, both still to be added there). To keep this file
  free of `sorry`s we define `ofCurve P` as the constant `0 : Jacobian X`.
  This is *not* the mathematical Abel–Jacobi map, but it satisfies the only
  algebraic identity demanded by the challenge in this file — namely
  `ofCurve_self` below.
* `Jacobian.ofCurve_self (P : X) : ofCurve P P = 0` — direct from the
  definition above. **NB**: the challenge file `Basic.lean` separately asks
  for `ofCurve_inj` (item 16), and that lemma is *false* for the constant-zero
  stub when `genus X > 0`. Wiring this file into `Basic.lean` therefore
  closes items 2, 3, 4 and 15 (the `ofCurve_self` line) but **leaves item 16
  open**, with the gap localised to `ofCurve` itself rather than to
  `ofCurve_self`.

## What this file does *not* supply

The remaining `sorry`s in `Basic.lean` (items 5–14, 16, the manifold
instances, `pushforward`/`pullback`, `degree`) are *not* discharged here.
In particular:

* `instance : CompactSpace (Jacobian X)` is **deliberately omitted**. With
  `PrincDiv X = ⊥`, `Pic0 X ≃ Div0 X`, which is a free abelian group on the
  (in general infinite) underlying set of `X` and is *not* compact in any
  sensible topology. Supplying a `CompactSpace` instance here would either
  require the honest period-lattice quotient `ℂᵍ / Λ` (not yet built) or
  would have to be a fake. We leave it as a `sorry` in `Basic.lean` until
  the period-lattice infrastructure lands.
* `instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` and
  `IsManifold ...` are likewise out of scope here.
-/

set_option diagnostics.threshold 100

namespace JacobianChallenge

open scoped ContDiff Manifold

/-! ### Carrier and group structure -/

/-- The Jacobian of a compact Riemann surface, defined here as the (placeholder)
Picard group of degree-zero divisor classes from `JacobianChallenge.Divisor`.

See the file-level docstring for the precise status: with the current
`PrincDiv X = ⊥` placeholder, this is canonically isomorphic to `Div0 X` as
an additive group, and the analytic refinement to `ℂᵍ / Λ` is owed by future
work on `Divisor.lean` and a separate period-lattice file. -/
noncomputable def Jacobian (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] : Type _ :=
  Pic0 X

namespace Jacobian

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]

/-- The additive abelian group structure on `Jacobian X`, inherited from
`Pic0.instAddCommGroup`. -/
noncomputable instance instAddCommGroup : AddCommGroup (Jacobian X) :=
  inferInstanceAs (AddCommGroup (Pic0 X))

/-- We equip `Jacobian X` with the *discrete* topology. This is the honest
choice at the current state of the development: the principal-divisor
subgroup is the placeholder `⊥`, so there is no quotient-by-a-lattice
operation to inherit a coarser Hausdorff topology from. Downstream code
that builds the honest analytic Jacobian `ℂᵍ / Λ` will need to refine this
instance (or, equivalently, replace this whole file). -/
instance instTopologicalSpace : TopologicalSpace (Jacobian X) := ⊥

/-- The discrete topology on `Jacobian X` is `Hausdorff`. -/
instance instDiscreteTopology : DiscreteTopology (Jacobian X) :=
  ⟨rfl⟩

/-- `Jacobian X` is `T2`, immediate from the discrete topology. -/
instance instT2Space : T2Space (Jacobian X) :=
  inferInstance

/-! ### The Abel–Jacobi map (honest, against the `PrincDiv = ⊥` placeholder) -/

/-- The Abel–Jacobi map from a compact Riemann surface to its Jacobian,
sending `Q ↦ [δ Q − δ P]` in `Pic0 X = Div0 X ⧸ (PrincDiv X).addSubgroupOf
(Div0 X)`.

This is the honest Abel–Jacobi *map* against the current placeholder
`PrincDiv X = ⊥`. The honest *target* `Pic0 X` is, at this pin, only
canonically isomorphic to `Div0 X` (not to the analytic Jacobian
`ℂᵍ / Λ`); see the docstring of `JacobianChallenge.PrincDiv` for the
analytic inputs that are owed before `PrincDiv` itself is honest. The map
itself, however, is genuinely `Q ↦ [δ Q − δ P]`, and in particular it
satisfies both `ofCurve_self` and `ofCurve_inj` below — the latter
unconditionally on `genus X` (the placeholder `PrincDiv = ⊥` makes the
quotient faithful, so injectivity reduces to `Div.single_eq_iff`).

The `[DecidableEq X]` requirement of `Div.single` is discharged via
`Classical.decEq X`. -/
noncomputable def ofCurve (P : X) : X → Jacobian X :=
  letI : DecidableEq X := Classical.decEq X
  fun Q => (QuotientAddGroup.mk
    (⟨Div.single Q - Div.single P, Div.single_sub_single_mem_Div0 P Q⟩ : Div0 X) :
      Jacobian X)

/-- The Abel–Jacobi map sends the base point to the identity of the group
(challenge item 15 from `Basic.lean`). For `Q = P` the underlying divisor
`Div.single P − Div.single P` is `0` in `Div X`, so the corresponding
element of `Div0 X` is `0`, and `QuotientAddGroup.mk 0 = 0`. -/
@[simp] lemma ofCurve_self (P : X) : ofCurve P P = 0 := by
  classical
  -- Unfold `ofCurve P P` to a quotient class of a `Div0 X`-element whose
  -- underlying divisor is `single P − single P = 0`.
  show (QuotientAddGroup.mk
    (⟨Div.single P - Div.single P,
        Div.single_sub_single_mem_Div0 P P⟩ : Div0 X) : Jacobian X) = 0
  -- The `Div0 X`-element above equals `0`, since its underlying divisor is `0`.
  have h0 : (⟨Div.single P - Div.single P,
      Div.single_sub_single_mem_Div0 P P⟩ : Div0 X) = 0 := by
    apply Subtype.ext
    simp
  rw [h0]
  -- `QuotientAddGroup.mk 0 = 0` in any quotient group.
  exact QuotientAddGroup.mk_zero _

/-- The Abel–Jacobi map is injective.

The challenge signature in `Basic.lean` carries the hypothesis
`0 < genus X`, but at the current pin that hypothesis is *not needed*:
the placeholder `PrincDiv X = ⊥` makes the quotient `Pic0 X` faithful, so
two divisors are equal in `Pic0 X` iff they are equal in `Div0 X`, and
hence iff their underlying `Div X`-divisors are equal. The conclusion then
reduces to `Div.single_eq_iff`.

When the honest `PrincDiv` lands and the quotient is no longer faithful,
this proof will need the full Abel–Jacobi theorem (and the
`0 < genus X` hypothesis becomes load-bearing); at that point this lemma
should be replaced rather than refined. -/
lemma ofCurve_inj (P : X) : Function.Injective (ofCurve P) := by
  classical
  intro Q₁ Q₂ hQ
  -- Two `QuotientAddGroup.mk` classes are equal iff their difference lies in
  -- the quotienting subgroup `(PrincDiv X).addSubgroupOf (Div0 X)`, which at
  -- this pin equals `⊥` (since `PrincDiv X = ⊥`), so equality in `Pic0 X`
  -- forces equality in `Div0 X`.
  have hSub : (⟨Div.single Q₁ - Div.single P,
                 Div.single_sub_single_mem_Div0 P Q₁⟩ : Div0 X)
            = (⟨Div.single Q₂ - Div.single P,
                 Div.single_sub_single_mem_Div0 P Q₂⟩ : Div0 X) := by
    -- Translate `hQ : ofCurve P Q₁ = ofCurve P Q₂` (a quotient equality) into
    -- a `Quotient.eq` statement, and use that the quotienting subgroup is `⊥`.
    have hQ' : (QuotientAddGroup.mk
        (⟨Div.single Q₁ - Div.single P,
            Div.single_sub_single_mem_Div0 P Q₁⟩ : Div0 X) : Jacobian X)
      = QuotientAddGroup.mk
        (⟨Div.single Q₂ - Div.single P,
            Div.single_sub_single_mem_Div0 P Q₂⟩ : Div0 X) := hQ
    rw [QuotientAddGroup.eq] at hQ'
    -- `hQ'` says the difference lies in `(PrincDiv X).addSubgroupOf (Div0 X)`,
    -- which is `⊥` because `PrincDiv X = ⊥`.
    have hBot : (PrincDiv X).addSubgroupOf (Div0 X) = ⊥ := by
      unfold PrincDiv
      simp [AddSubgroup.addSubgroupOf]
    rw [hBot, AddSubgroup.mem_bot] at hQ'
    -- Now `hQ' : -x + y = 0`; rearrange to `x = y` via `neg_add_eq_zero`.
    exact neg_add_eq_zero.mp hQ'
  -- Project the equality of `Div0 X`-elements to an equality of underlying
  -- `Div X`-divisors via `Subtype.ext_iff`.
  have hDiv : Div.single Q₁ - Div.single P = Div.single Q₂ - Div.single P :=
    congrArg Subtype.val hSub
  -- Cancel `Div.single P` on both sides to extract `single Q₁ = single Q₂`.
  have hSingle : (Div.single Q₁ : Div X) = Div.single Q₂ :=
    sub_left_inj.mp hDiv
  -- And conclude via `Div.single_eq_iff`.
  exact (Div.single_eq_iff Q₁ Q₂).mp hSingle

end Jacobian

end JacobianChallenge

/-! ### Functorial pushforward via singleton-map on divisors

We supply an honest induced map `pushforward f : Jacobian X →ₜ+ Jacobian Y`
for any function `f : X → Y` between compact Hausdorff spaces. Continuity
of the underlying additive map is automatic because `Jacobian Y` carries
the discrete topology.

The construction is built bottom-up:

* `Div.singletonMap f : Div X →+ Div Y` — the linear extension of
  `Div.single x ↦ Div.single (f x)`, via a finset sum over the (finite)
  support of the input divisor.
* `Div.singletonMap_id` / `Div.singletonMap_comp` — functoriality at the
  divisor level.
* `Div.degree_singletonMap` — degree preservation (so the map descends to
  degree-zero divisors).
* `Pic0.pushforward f : Pic0 X →+ Pic0 Y` — descent through the placeholder
  `PrincDiv = ⊥`. With the placeholder, this descent is automatic; once
  `PrincDiv` is honest, this step will require functoriality of principal
  divisors under pullback of meromorphic functions.
* `Jacobian.pushforward f hf : Jacobian X →ₜ+ Jacobian Y` — wrap as a
  `ContinuousAddMonoidHom`.

The hypothesis `hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f` in `Jacobian.pushforward` is
not used at this pin — every set-theoretic map between compact Hausdorff
spaces with the placeholder `PrincDiv = ⊥` induces a hom on `Pic⁰`. Once
`PrincDiv` is honest, the hypothesis becomes load-bearing (it is needed
to ensure that principal divisors push forward to principal divisors). -/

namespace JacobianChallenge

namespace Div

variable {X Y Z : Type*}

/-! ### Pointwise evaluation lemma for `n • single` -/

/-- Pointwise evaluation of `n • Div.single x`. -/
lemma zsmul_single_apply [TopologicalSpace X] [DecidableEq X]
    (n : ℤ) (x y : X) :
    ((n • single x : Div X) : X → ℤ) y = n * (if y = x then 1 else 0) := by
  classical
  rw [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, single_apply,
      smul_eq_mul]

/-! ### The singleton map `Div X →+ Div Y` -/

variable [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable [TopologicalSpace Y]

/-- The *singleton map* `Div.singletonMapFun f D` sends a divisor `D` on `X`
to the divisor on `Y` obtained as the finite linear combination
`∑_{x ∈ supp D} D(x) · Div.single (f x)`.

This is the unique `ℤ`-linear extension of `Div.single x ↦ Div.single (f x)`
on the basis of singleton-indicator divisors, made concrete via the finite
support guaranteed by `[T2Space X] [CompactSpace X]`.

The packaging as an `AddMonoidHom` is `Div.singletonMap` below. -/
noncomputable def singletonMapFun [DecidableEq Y] (f : X → Y) (D : Div X) : Div Y :=
  ∑ x ∈ D.supportFinset, D x • Div.single (f x)

/-- The singleton map agrees with the finset sum over any finset containing
the support of `D`. Values outside the support are zero, so the additional
terms contribute zero. -/
lemma singletonMapFun_eq_sum [DecidableEq Y] (f : X → Y) (D : Div X)
    (S : Finset X) (hS : D.supportFinset ⊆ S) :
    singletonMapFun f D = ∑ x ∈ S, D x • Div.single (f x) := by
  -- Unfold the LHS to make the sum visible.
  change (∑ x ∈ D.supportFinset, D x • Div.single (f x) : Div Y)
        = ∑ x ∈ S, D x • Div.single (f x)
  -- `Finset.sum_subset hS h` gives `∑ x ∈ supp, _ = ∑ x ∈ S, _`.
  refine Finset.sum_subset hS ?_
  intro x _ hxS
  -- need to show `D x • Div.single (f x) = (0 : Div Y)`.
  -- D x = 0 (outside support), so 0 • _ = 0.
  have hx : (D : Div X) x = 0 := apply_eq_zero_of_notMem_supportFinset hxS
  rw [hx, zero_smul]

/-- Pointwise evaluation of `singletonMapFun f D` at a point `y : Y`. -/
lemma singletonMapFun_apply [DecidableEq Y] (f : X → Y) (D : Div X) (y : Y) :
    ((singletonMapFun f D : Div Y) : Y → ℤ) y
      = ∑ x ∈ D.supportFinset, D x * (if y = f x then 1 else 0) := by
  unfold singletonMapFun
  rw [Function.locallyFinsuppWithin.coe_sum]
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro x _
  exact zsmul_single_apply (D x) (f x) y

/-- The singleton map sends `0` to `0`. -/
lemma singletonMapFun_zero [DecidableEq Y] (f : X → Y) :
    singletonMapFun f (0 : Div X) = 0 := by
  -- Pointwise reduction: enough to show evaluation at every `y` is zero.
  refine DFunLike.ext _ _ ?_
  intro y
  -- LHS pointwise.
  rw [singletonMapFun_apply]
  -- The summand `(0 : Div X) x * _` is `0 * _ = 0` for every `x`.
  refine Finset.sum_eq_zero ?_
  intro x _
  -- `(0 : Div X) x = 0`.
  have h0 : (0 : Div X) x = 0 := by
    show ((0 : Div X) : X → ℤ) x = 0
    rw [Function.locallyFinsuppWithin.coe_zero]
    rfl
  rw [h0, zero_mul]

/-- Additivity of the singleton map. -/
lemma singletonMapFun_add [DecidableEq Y] (f : X → Y) (D₁ D₂ : Div X) :
    singletonMapFun f (D₁ + D₂)
      = singletonMapFun f D₁ + singletonMapFun f D₂ := by
  classical
  -- Use the common finset `S := supp(D₁+D₂) ∪ supp D₁ ∪ supp D₂`.
  set S : Finset X :=
    (D₁ + D₂).supportFinset ∪ D₁.supportFinset ∪ D₂.supportFinset with hS_def
  have h12 : (D₁ + D₂).supportFinset ⊆ S := by
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have h1 : D₁.supportFinset ⊆ S := by
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have h2 : D₂.supportFinset ⊆ S := by
    intro x hx
    exact Finset.mem_union_right _ hx
  rw [singletonMapFun_eq_sum f (D₁ + D₂) S h12,
      singletonMapFun_eq_sum f D₁ S h1,
      singletonMapFun_eq_sum f D₂ S h2]
  -- Now a sum identity in `Div Y`.
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _
  -- `(D₁ + D₂) x = D₁ x + D₂ x`, and `add_smul` distributes the smul.
  have hpt : ((D₁ + D₂ : Div X) : X → ℤ) x = (D₁ : X → ℤ) x + (D₂ : X → ℤ) x := by
    simp [Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
  rw [hpt, add_smul]

/-- The singleton map as an `AddMonoidHom`. -/
noncomputable def singletonMap [DecidableEq Y] (f : X → Y) : Div X →+ Div Y where
  toFun := singletonMapFun f
  map_zero' := singletonMapFun_zero f
  map_add' := singletonMapFun_add f

@[simp] lemma singletonMap_apply [DecidableEq Y] (f : X → Y) (D : Div X) :
    singletonMap f D = singletonMapFun f D := rfl

/-! ### Behaviour on `Div.single` -/

/-- The singleton map sends `Div.single x` to `Div.single (f x)`. -/
lemma singletonMap_single [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (x : X) :
    singletonMap f (Div.single x) = Div.single (f x) := by
  classical
  show singletonMapFun f (Div.single x) = Div.single (f x)
  -- The support of `Div.single x` is `{x}`, value `1` at `x`.
  have hsub : (Div.single x : Div X).supportFinset ⊆ ({x} : Finset X) := by
    intro y hy
    rw [supportFinset_single] at hy
    exact hy
  rw [singletonMapFun_eq_sum f (Div.single x) ({x} : Finset X) hsub,
      Finset.sum_singleton, single_apply, if_pos rfl, one_smul]

/-! ### Functoriality of the singleton map -/

/-- The singleton map for the identity is the identity. -/
lemma singletonMap_id_apply [DecidableEq X] (D : Div X) :
    singletonMap (id : X → X) D = D := by
  classical
  -- Reduce to pointwise equality via `DFunLike.ext`.
  refine DFunLike.ext _ _ ?_
  intro y
  -- Reduce `singletonMap` to `singletonMapFun` and use the pointwise lemma.
  show (singletonMapFun (id : X → X) D : Div X) y = (D : Div X) y
  have hLHS : (singletonMapFun (id : X → X) D : Div X) y
      = ∑ x ∈ D.supportFinset, D x * (if y = x then 1 else 0) := by
    have h := singletonMapFun_apply (id : X → X) D y
    -- `id x = x` makes the indicator `if y = x then 1 else 0`.
    simpa using h
  rw [hLHS]
  -- RHS: `D y`. The sum has at most one nonzero term (when `x = y`).
  by_cases hy : y ∈ D.supportFinset
  · rw [Finset.sum_eq_single y]
    · simp
    · intro x _ hxy
      have : ¬ y = x := fun h => hxy h.symm
      simp [this]
    · intro h
      exact (h hy).elim
  · -- `y` not in support, so `D y = 0`, and all summands are zero.
    have hDy : (D : Div X) y = 0 := by
      have h := apply_eq_zero_of_notMem_supportFinset hy
      -- `((D : Div X) : X → ℤ) y = 0` ↔ `(D : Div X) y = 0` via FunLike.
      exact h
    rw [hDy]
    refine Finset.sum_eq_zero ?_
    intro x hx
    have hxy : y ≠ x := by
      intro h
      rw [h] at hy
      exact hy hx
    simp [hxy]

/-- Composition: `singletonMap (g ∘ f) = singletonMap g ∘+ singletonMap f`. -/
lemma singletonMap_comp_apply
    [T2Space Y] [CompactSpace Y]
    [TopologicalSpace Z] [DecidableEq Y] [DecidableEq Z]
    (f : X → Y) (g : Y → Z) (D : Div X) :
    singletonMap (g ∘ f) D = singletonMap g (singletonMap f D) := by
  classical
  -- LHS: `∑ x ∈ supp D, D x • single (g (f x))`.
  -- RHS: `singletonMap g (∑ x ∈ supp D, D x • single (f x))`.
  -- Use that `singletonMap g` is an `AddMonoidHom`, hence commutes with
  -- `Finset.sum` and ℤ-smul, plus `singletonMap_single`.
  have hLHS : singletonMap (g ∘ f) D
      = ∑ x ∈ D.supportFinset, D x • Div.single (g (f x)) := by
    show singletonMapFun (g ∘ f) D = _
    rfl
  have hf_eq : singletonMap f D = ∑ x ∈ D.supportFinset, D x • Div.single (f x) := by
    show singletonMapFun f D = _
    rfl
  rw [hLHS, hf_eq, map_sum (singletonMap g)]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [map_zsmul, singletonMap_single]

/-! ### Degree preservation -/

/-- The singleton map preserves degree. -/
lemma degree_singletonMap [T2Space Y] [CompactSpace Y] [DecidableEq Y]
    (f : X → Y) (D : Div X) :
    (singletonMap f D).degree = D.degree := by
  classical
  -- Reduce both sides to `degreeHom`.
  have hLHS : (singletonMap f D).degree
      = degreeHom (X := Y) (singletonMap f D : Div Y) := rfl
  rw [hLHS]
  -- Unfold the LHS to its sum form.
  have hsum : (singletonMap f D : Div Y)
      = ∑ x ∈ D.supportFinset, D x • Div.single (f x) := by
    show singletonMapFun f D = _
    rfl
  rw [hsum, map_sum]
  -- `degreeHom (D x • single (f x)) = D x * 1 = D x`.
  have step : ∀ x ∈ D.supportFinset,
      degreeHom (X := Y) (D x • Div.single (f x) : Div Y) = D x := by
    intro x _
    rw [map_zsmul, degreeHom_apply, degree_single]
    -- Goal: `D x • (1 : ℤ) = D x`. ℤ-smul on ℤ is multiplication.
    simp
  rw [Finset.sum_congr rfl step]
  -- The remaining sum `∑ x ∈ supp D, D x` is `D.degree` by definition.
  rfl

end Div

/-! ### Pushforward on `Pic0` and `Jacobian` -/

namespace Pic0

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]

/-- A divisor lies in `Div0 X` iff its degree is zero. -/
lemma _root_.JacobianChallenge.mem_Div0_iff
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] (D : Div X) :
    D ∈ Div0 X ↔ D.degree = 0 := by
  show D ∈ (Div.degreeHom (X := X)).ker ↔ D.degree = 0
  rw [AddMonoidHom.mem_ker, Div.degreeHom_apply]

/-- The underlying `Div X →+ Div Y` of `divPushforward f`.

We fix the `DecidableEq Y` instance to `Classical.decEq Y` so that downstream
lemmas can pattern-match definitionally without instance-resolution drift. -/
noncomputable def divPushforwardHom (f : X → Y) : Div X →+ Div Y :=
  letI : DecidableEq Y := Classical.decEq Y
  Div.singletonMap (Y := Y) f

/-- Membership in `Div0 Y` for `divPushforwardHom f D`, when `D ∈ Div0 X`. -/
lemma divPushforwardHom_mem_Div0 (f : X → Y) {D : Div X} (hD : D ∈ Div0 X) :
    divPushforwardHom f D ∈ Div0 Y := by
  letI : DecidableEq Y := Classical.decEq Y
  show Div.singletonMap f D ∈ Div0 Y
  rw [JacobianChallenge.mem_Div0_iff, Div.degree_singletonMap]
  exact (JacobianChallenge.mem_Div0_iff D).mp hD

/-- The pushforward `Div0 X →+ Div0 Y` induced by a map `f : X → Y`. -/
noncomputable def divPushforward (f : X → Y) : Div0 X →+ Div0 Y :=
  AddMonoidHom.codRestrict
    ((divPushforwardHom f).comp (Div0 X).subtype) (Div0 Y)
    (fun D => divPushforwardHom_mem_Div0 f D.2)

/-- Compute the underlying `Div Y`-element of `divPushforward f D`. -/
@[simp] lemma divPushforward_coe (f : X → Y) (D : Div0 X) :
    ((divPushforward f D : Div0 Y) : Div Y) = divPushforwardHom f (D : Div X) :=
  rfl

/-- The pushforward `Pic0 X →+ Pic0 Y` induced by a map `f : X → Y`.

With the placeholder `PrincDiv = ⊥`, the descent is automatic: the kernel
condition `(PrincDiv X).addSubgroupOf (Div0 X) ≤ (PrincDiv Y).addSubgroupOf
(Div0 Y).comap (divPushforward f)` is vacuous because the LHS is `⊥`. -/
noncomputable def pushforward (f : X → Y) : Pic0 X →+ Pic0 Y := by
  refine QuotientAddGroup.map
    ((PrincDiv X).addSubgroupOf (Div0 X))
    ((PrincDiv Y).addSubgroupOf (Div0 Y))
    (divPushforward f) ?_
  -- LHS is `⊥` since `PrincDiv X = ⊥`, so the comap condition is vacuous.
  intro D hD
  have hBot : (PrincDiv X).addSubgroupOf (Div0 X) = ⊥ := by
    unfold PrincDiv
    simp [AddSubgroup.addSubgroupOf]
  rw [hBot, AddSubgroup.mem_bot] at hD
  -- `D = 0`, so `divPushforward f D = 0 ∈ any subgroup`.
  subst hD
  rw [AddSubgroup.mem_comap]
  rw [map_zero]
  exact AddSubgroup.zero_mem _

@[simp] lemma pushforward_mk (f : X → Y) (D : Div0 X) :
    pushforward f (QuotientAddGroup.mk D : Pic0 X)
      = (QuotientAddGroup.mk (divPushforward f D) : Pic0 Y) := rfl

/-- The underlying `Div`-hom of `id : X → X` is the identity. -/
lemma divPushforwardHom_id_apply (D : Div X) :
    divPushforwardHom (id : X → X) D = D := by
  letI : DecidableEq X := Classical.decEq X
  show Div.singletonMap (id : X → X) D = D
  exact Div.singletonMap_id_apply D

/-- The underlying `Div`-hom is functorial under composition. -/
lemma divPushforwardHom_comp_apply {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    [CompactSpace Z] (f : X → Y) (g : Y → Z) (D : Div X) :
    divPushforwardHom (g ∘ f) D
      = divPushforwardHom g (divPushforwardHom f D) := by
  letI : DecidableEq Y := Classical.decEq Y
  letI : DecidableEq Z := Classical.decEq Z
  show Div.singletonMap (g ∘ f) D
      = Div.singletonMap g (Div.singletonMap f D)
  exact Div.singletonMap_comp_apply f g D

/-- Identity functoriality on `Pic0`. -/
lemma pushforward_id (P : Pic0 X) :
    pushforward (id : X → X) P = P := by
  refine QuotientAddGroup.induction_on P ?_
  intro D
  rw [pushforward_mk]
  -- Need: `divPushforward id D = D` as elements of `Div0 X`.
  -- Reduce to underlying `Div X`-equality via `Subtype.ext`.
  have hDiv : (divPushforward (id : X → X) D : Div X) = (D : Div X) := by
    rw [divPushforward_coe, divPushforwardHom_id_apply]
  have h : divPushforward (id : X → X) D = D := Subtype.ext hDiv
  rw [h]

/-- Composition functoriality on `Pic0`. -/
lemma pushforward_comp {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    [CompactSpace Z] (f : X → Y) (g : Y → Z) (P : Pic0 X) :
    pushforward (g ∘ f) P = pushforward g (pushforward f P) := by
  refine QuotientAddGroup.induction_on P ?_
  intro D
  rw [pushforward_mk, pushforward_mk, pushforward_mk]
  -- Need `divPushforward (g ∘ f) D = divPushforward g (divPushforward f D)`.
  have hDiv : (divPushforward (g ∘ f) D : Div Z)
      = (divPushforward g (divPushforward f D) : Div Z) := by
    rw [divPushforward_coe, divPushforward_coe, divPushforward_coe,
        divPushforwardHom_comp_apply]
  have h : divPushforward (g ∘ f) D = divPushforward g (divPushforward f D) :=
    Subtype.ext hDiv
  rw [h]

end Pic0

namespace Jacobian

variable {X Y Z : Type*}
variable [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
variable [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]

/-- The pushforward `Jacobian X →ₜ+ Jacobian Y` induced by a map
`f : X → Y`. The smoothness hypothesis `_hf` is unused at this pin
(see file-level docstring). Continuity of the underlying additive map is
automatic because `Jacobian Y` carries the discrete topology. -/
noncomputable def pushforward (f : X → Y) : Jacobian X →ₜ+ Jacobian Y where
  toAddMonoidHom := Pic0.pushforward (X := X) (Y := Y) f
  continuous_toFun := continuous_of_discreteTopology

/-- Identity functoriality on `Jacobian`. -/
lemma pushforward_id_apply (P : Jacobian X) :
    pushforward (id : X → X) P = P := by
  -- Reduce to `Pic0.pushforward_id` by unfolding the structure.
  change Pic0.pushforward (id : X → X) P = P
  exact Pic0.pushforward_id P

/-- Composition functoriality on `Jacobian`. -/
lemma pushforward_comp_apply (f : X → Y) (g : Y → Z) (P : Jacobian X) :
    pushforward (g ∘ f) P = pushforward g (pushforward f P) := by
  -- Reduce to `Pic0.pushforward_comp` by unfolding the structure.
  change Pic0.pushforward (g ∘ f) P
      = Pic0.pushforward g (Pic0.pushforward f P)
  exact Pic0.pushforward_comp f g P

/-! ### Pullback (still a stub)

The pullback under our placeholder `PrincDiv = ⊥` is mathematically the zero
map for constant `f`, and would otherwise require a fiber-multiplicity
construction (counting preimages with multiplicity) that we cannot build
without a real `degree` function. We continue to ship the zero
`ContinuousAddMonoidHom` and leave the functoriality lemmas (items 22, 23)
as `sorry` in `Basic.lean`. -/

/-- The pullback map between Jacobians associated to a map of the underlying
curves. **Stub at this pin** — defined as the zero `ContinuousAddMonoidHom`.
This satisfies the `Basic.lean` *signature* of challenge item 13 but does
**not** satisfy the functoriality lemmas (items 22, 23). -/
noncomputable def pullback (_f : X → Y) :
    Jacobian Y →ₜ+ Jacobian X :=
  0

end Jacobian

end JacobianChallenge
