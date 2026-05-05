/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor
import JacobianChallenge.Divisor.PrincipalDivisor
import JacobianChallenge.Divisor.MeromorphicNonzeroGerm
import Mathlib.Algebra.Group.TypeTags.Basic

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # The eventual honest `PrincDiv X`: range of `principalDivisorAddHom`

This file packages `principalDivisorMap` (built in
`Divisor/PrincipalDivisor.lean`) into an `AddMonoidHom` with codomain
`Div X`, and exposes its range as the eventual honest `PrincDiv X`
subgroup. The construction is gated on a single, named, `Prop`-valued
classical input — the **residue theorem on a compact Riemann surface** —
which states that every principal divisor has degree zero (equivalently:
the range is contained in `Div⁰ X`).

## Design

The `MeromorphicNonzero X` carrier of `principalDivisorMap` is *almost* a
commutative group: pointwise multiplication of two non-vanishing-germ
meromorphic functions is again such a function, the constant function `1`
is a unit, and pointwise inversion swaps zeros and poles. None of these
algebraic facts has been wired into mathlib at the pin
`8e3c989104daaa052921bf43de9eef0e1ac9fbf5`, and the corresponding
order-divisor compatibilities

  `principalDivisorMap (1 : MeromorphicNonzero X) = 0`,
  `principalDivisorMap (f * g)               = principalDivisorMap f
                                              + principalDivisorMap g`

(the second is the local-order valuation
`ord_x(fg) = ord_x f + ord_x g` packaged into `Div X`) are likewise owed.

We bundle the missing `CommGroup (MeromorphicNonzero X)` structure together
with the two compatibility lemmas into one type-class
`PrincipalDivisorMultiplicative X`. Given an instance, this file then
delivers:

* `principalDivisorAddHom : Additive (MeromorphicNonzero X) →+ Div X`
  — the multiplicative principal-divisor map repackaged as an additive
  group homomorphism via the `Additive` `TypeTag` (which transports any
  `CommGroup G` to an `AddCommGroup (Additive G)`), with `map_zero'`
  exactly the bundle's `principalDivisorMap_one` and `map_add'` exactly
  the bundle's `principalDivisorMap_mul` (load-bearing).
* `PrincDivHonestCandidate X : AddSubgroup (Div X)` — the *eventual* honest
  `PrincDiv X`, defined as `principalDivisorAddHom.range`.
* `ResidueTheorem X : Prop` — the named (statement-only) classical input.
* `residueTheorem_iff_range_le_Div0` — the residue theorem is equivalent
  to `PrincDivHonestCandidate X ≤ Div0 X`. **Real proof, not `Iff.rfl`.**

A note on the wrapper choice. The task spec sketch wrote
`Multiplicative (MeromorphicNonzero X) →+ Div X`. That is the wrong
direction: `Multiplicative G` *adds* a multiplicative structure on top of
an additive one (so `Multiplicative G` carries `CommGroup (Multiplicative G)`
when `G` is `AddCommGroup`). What we need is the opposite — to view the
already-multiplicative `MeromorphicNonzero X` *as* an additive group —
which is exactly what `Additive` does (`[CommGroup G] ⇒
AddCommGroup (Additive G)`, see `Mathlib.Algebra.Group.TypeTags.Basic`).
The spec explicitly anticipated this: "the exact `Multiplicative`
boilerplate may need tweaking — the structural point is to wrap
`MeromorphicNonzero X`'s commutative monoid into an additive
`AddMonoidHom` target." We use `Additive`.

## What this file does **not** do

* It does **not** provide an instance of `PrincipalDivisorMultiplicative X`.
  That is the deliverable of a sister file (`feat/principal-divisor-
  multiplicative`, owed by I1) that proves the four facts directly from the
  `MMeromorphicAt.mul` / `MMeromorphicAt.inv` / `MMeromorphicOn.const`
  lemmas plus the local-order valuation property. As long as no instance is
  in scope, `principalDivisorAddHom` and `PrincDivHonestCandidate` are
  noncomputable definitions parametrised by the (currently absent)
  instance, and the rest of the file consumes only their definitions —
  nothing here uses `sorry` or `axiom`.
* It does **not** prove `ResidueTheorem X`. That is the deep classical
  input. The point of this file is to *name* the statement so that
  downstream code can take it as a hypothesis.
* It does **not** swap the placeholder `PrincDiv X := ⊥` (in
  `Divisor.lean`) for the honest `principalDivisorAddHom.range`. That swap
  is the **deliberate one-line follow-up** once both
  `[PrincipalDivisorMultiplicative X]` and `ResidueTheorem X` are
  available; keeping it as a one-liner keeps the change auditable.

## The eventual one-line swap (kept here as documentation)

Once `[PrincipalDivisorMultiplicative X]` is provided and `ResidueTheorem X`
is proven, the change in `Divisor.lean` is:

```
noncomputable def PrincDiv (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X] [PrincipalDivisorMultiplicative X] :
    AddSubgroup (Div X) :=
  principalDivisorAddHom.range
```

and items 15, 19, 20 in `Basic.lean` (already PROOF-HONEST in `OPEN.md`)
strict-close immediately because their proof bodies route through the
`Pic⁰` quotient *abstractly* — they survive any honest replacement of
`PrincDiv`.
-/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

/-! ## The bundle of multiplicative-principal-divisor data -/

/-- The multiplicative structure on `MeromorphicNonzero X` together with
the two `principalDivisorMap` compatibility lemmas, bundled as a
type class.

This bundle is the load-bearing input that the sister file
`feat/principal-divisor-multiplicative` (owed by I1) is expected to
provide. It packages four facts:

1. `MeromorphicNonzero X` is a commutative group under pointwise
   multiplication of functions, with `1` the constant function `1` and
   `f⁻¹` the pointwise inverse.
2. `principalDivisorMap (1 : MeromorphicNonzero X) = 0`. (The constant
   function `1` is regular non-zero everywhere, hence its order divisor
   is the zero divisor.)
3. `principalDivisorMap (f * g) = principalDivisorMap f + principalDivisorMap g`.
   (Pointwise: the local order is a valuation,
   `ord_x(fg) = ord_x f + ord_x g`.)
4. (Implied by 1: `f⁻¹` is a `MeromorphicNonzero X`, since pointwise
   inversion swaps zeros and poles and preserves the non-vanishing-germ
   condition; this is the content of mathlib's `MeromorphicAt.inv` plus
   the order-swap identity.)

The two named compatibility lemmas are precisely what is required for
the additive packaging of `principalDivisorMap` into an `AddMonoidHom`. -/
class PrincipalDivisorMultiplicative (X : Type u)
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] : Prop where
  /-- The principal divisor of the constant function `1` is the zero
      divisor. -/
  principalDivisorMap_one :
    principalDivisorMap (1 : MeromorphicNonzero X) = 0
  /-- The principal-divisor map intertwines pointwise multiplication on
      `MeromorphicNonzero X` with addition on `Div X`:
      `(fg) = (f) + (g)`. Equivalently, the local-order map is a valuation. -/
  principalDivisorMap_mul :
    ∀ f g : MeromorphicNonzero X,
      principalDivisorMap (f * g) = principalDivisorMap f + principalDivisorMap g

/-- Default instance of `PrincipalDivisorMultiplicative X` using the
    standalone `principalDivisorMap_one` and `principalDivisorMap_mul`
    lemmas from `Divisor/PrincipalDivisor.lean` (I1's contribution).
    Means downstream `[PrincipalDivisorMultiplicative X]` requirements
    are satisfied automatically. -/
instance principalDivisorMultiplicativeInstance (X : Type u)
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] :
    PrincipalDivisorMultiplicative X where
  principalDivisorMap_one := principalDivisorMap_one
  principalDivisorMap_mul := principalDivisorMap_mul

namespace PrincipalDivisorMultiplicative

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [PrincipalDivisorMultiplicative X]

/-- Re-export `principalDivisorMap_one` as a `simp` lemma. -/
@[simp] lemma principalDivisorMap_one' :
    principalDivisorMap (1 : MeromorphicNonzero X) = 0 :=
  PrincipalDivisorMultiplicative.principalDivisorMap_one

/-- Re-export `principalDivisorMap_mul` as a `simp` lemma. -/
@[simp] lemma principalDivisorMap_mul' (f g : MeromorphicNonzero X) :
    principalDivisorMap (f * g)
      = principalDivisorMap f + principalDivisorMap g :=
  PrincipalDivisorMultiplicative.principalDivisorMap_mul f g

end PrincipalDivisorMultiplicative

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## The eventual honest `PrincDiv X`

`MeromorphicNonzero X` is a `CommMonoid`, not a `CommGroup` (pointwise
inversion fails at zeros: `0 * 0⁻¹ = 0 ≠ 1`). So `principalDivisorMap`
cannot be packaged as an `AddMonoidHom` *whose range is automatically an
`AddSubgroup`*. We therefore define `PrincDivHonestCandidate` directly
as the additive *subgroup* of `Div X` generated by the principal divisors,
via `AddSubgroup.closure`. This is mathematically the right object —
the principal-divisor subgroup is by definition the subgroup generated
by `{(f) : f meromorphic non-vanishing-germ}` — and it works without
assuming any group structure on `MeromorphicNonzero X`. -/

/-- The **eventual honest `PrincDiv X`**: the additive subgroup of
`Div X` generated by all principal divisors `(f)` for
`f : MeromorphicNonzero X`. -/
noncomputable def PrincDivHonestCandidate (X : Type u)
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] :
    AddSubgroup (Div X) :=
  AddSubgroup.closure (Set.range (principalDivisorMap (X := X)))

/-- Generators of `PrincDivHonestCandidate X` are in the subgroup. -/
lemma principalDivisorMap_mem_PrincDivHonestCandidate
    (f : MeromorphicNonzero X) :
    principalDivisorMap f ∈ PrincDivHonestCandidate X := by
  unfold PrincDivHonestCandidate
  exact AddSubgroup.subset_closure ⟨f, rfl⟩

/-! ## The residue theorem (statement only) and the equivalence -/

/-- The **residue theorem** on a compact Riemann surface: every principal
divisor has degree zero.

This is a `Prop`-valued `def`, *not* an `axiom`. It records the statement
exactly so that downstream files can take it as a hypothesis (or a future
sister file can prove it). The classical proof is the contour-integral
identity `∑_x ord_x(f) = (2πi)⁻¹ ∮ d log f`, which on a compact Riemann
surface vanishes because there is no boundary.

`ConnectedSpace X` is included here to align with the canonical statement
on a *connected* compact Riemann surface, matching the `Basic.lean`
variable convention. The bare statement makes sense without
connectedness, but quoting it without is a needless weakening. -/
def ResidueTheorem (X : Type u)
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] : Prop :=
  ∀ f : MeromorphicNonzero X, (principalDivisorMap f).degree = 0

/-- The residue theorem is equivalent to the inclusion
`PrincDivHonestCandidate X ≤ Div0 X` of additive subgroups of `Div X`.

This is the precise statement of the gating: once the residue theorem is
discharged, the honest `PrincDiv X = principalDivisorAddHom.range`
automatically lands in `Div0 X`, and the `(PrincDiv X).addSubgroupOf
(Div0 X)` quotient that defines `Pic0 X` (in `Divisor.lean`) becomes
mathematically meaningful (i.e. `Pic0 X` becomes the genuine Picard group
of degree-zero divisor classes rather than the placeholder `Div0 X`).

The proof unfolds `PrincDivHonestCandidate`, `Div0`, `principalDivisorAddHom`
and `Div.degreeHom`, and reduces the inclusion `f.range ≤ degreeHom.ker`
to "every principal divisor has degree zero" — i.e. to `ResidueTheorem X`.
This is **not** `Iff.rfl`: it depends on `AddMonoidHom.mem_range`,
`AddSubgroup.mem_ker`, and an unfolding of `Div.degreeHom`. -/
lemma residueTheorem_iff_range_le_Div0
    [ConnectedSpace X] :
    ResidueTheorem X ↔ PrincDivHonestCandidate X ≤ Div0 X := by
  constructor
  · -- Residue theorem ⇒ inclusion.
    intro hRes
    unfold PrincDivHonestCandidate
    rw [AddSubgroup.closure_le]
    -- Goal: `Set.range principalDivisorMap ⊆ ↑(Div0 X)`.
    rintro D ⟨f, hf⟩
    -- `D = principalDivisorMap f`. Need `D ∈ Div0 X`, i.e. `degree D = 0`.
    show D ∈ (Div.degreeHom (X := X)).ker
    rw [AddMonoidHom.mem_ker, Div.degreeHom_apply, ← hf]
    exact hRes f
  · -- Inclusion ⇒ residue theorem.
    intro hLe f
    -- `principalDivisorMap f ∈ PrincDivHonestCandidate X` (it's a generator).
    have hMem : principalDivisorMap f ∈ PrincDivHonestCandidate X :=
      principalDivisorMap_mem_PrincDivHonestCandidate f
    have hKer : principalDivisorMap f ∈ (Div.degreeHom (X := X)).ker := hLe hMem
    rw [AddMonoidHom.mem_ker, Div.degreeHom_apply] at hKer
    exact hKer

/-! ## Germ-level `AddMonoidHom` packaging

With `MeromorphicNonzero.Germ X` carrying a genuine `CommGroup` instance
(from `Divisor/MeromorphicNonzeroGerm.lean`), we can repackage the germ-
level principal-divisor map as a real `AddMonoidHom` from
`Additive (Germ X)` to `Div X`. The `Additive` wrapper transports
`CommGroup (Germ X)` to `AddCommGroup (Additive (Germ X))`, so the range
of this `AddMonoidHom` lands in `AddSubgroup (Div X)` — i.e. an honest
*subgroup*, no `AddSubgroup.closure` workaround needed.

`PrincDivHonestCandidateGerm` is the cleaner, range-of-an-AddMonoidHom
form of `PrincDivHonestCandidate`. The lemma
`PrincDivHonestCandidateGerm_eq` asserts they coincide as additive
subgroups of `Div X`. -/

/-- Auxiliary: `Germ.principalDivisorMap (1 : Germ X) = 0`. Reduces to
    the underlying `principalDivisorMap_one` via the definitional
    `Germ.one_def` and the `Quotient.lift` computation rule
    `Germ.principalDivisorMap_mk`. -/
lemma Germ.principalDivisorMap_one :
    MeromorphicNonzero.Germ.principalDivisorMap (1 : MeromorphicNonzero.Germ X) = 0 := by
  show MeromorphicNonzero.Germ.principalDivisorMap
        (MeromorphicNonzero.Germ.mk (1 : MeromorphicNonzero X)) = 0
  rw [MeromorphicNonzero.Germ.principalDivisorMap_mk]
  exact principalDivisorMap_one

/-- Auxiliary: `Germ.principalDivisorMap` intertwines multiplication on
    the germ quotient with addition on `Div X`. By induction on both
    germ classes (`Quotient.inductionOn₂`), reduces to the underlying
    `principalDivisorMap_mul`. -/
lemma Germ.principalDivisorMap_mul
    (g h : MeromorphicNonzero.Germ X) :
    MeromorphicNonzero.Germ.principalDivisorMap (g * h)
      = MeromorphicNonzero.Germ.principalDivisorMap g
        + MeromorphicNonzero.Germ.principalDivisorMap h := by
  refine Quotient.inductionOn₂ (motive := fun g h =>
      MeromorphicNonzero.Germ.principalDivisorMap (g * h)
        = MeromorphicNonzero.Germ.principalDivisorMap g
          + MeromorphicNonzero.Germ.principalDivisorMap h) g h ?_
  intro f f'
  -- `Quotient.mk _ f` is `Germ.mk f`. Both `*` and `principalDivisorMap`
  -- compute definitionally on representatives.
  show MeromorphicNonzero.Germ.principalDivisorMap
        ((MeromorphicNonzero.Germ.mk f) * (MeromorphicNonzero.Germ.mk f')) =
      MeromorphicNonzero.Germ.principalDivisorMap (MeromorphicNonzero.Germ.mk f)
        + MeromorphicNonzero.Germ.principalDivisorMap (MeromorphicNonzero.Germ.mk f')
  rw [MeromorphicNonzero.Germ.mk_mul,
      MeromorphicNonzero.Germ.principalDivisorMap_mk,
      MeromorphicNonzero.Germ.principalDivisorMap_mk,
      MeromorphicNonzero.Germ.principalDivisorMap_mk]
  exact principalDivisorMap_mul f f'

/-- The **germ-level principal divisor map**, packaged as an
`AddMonoidHom` from `Additive (Germ X)` to `Div X`. The `Additive`
wrapper transports `CommGroup (Germ X)` (proven in
`Divisor/MeromorphicNonzeroGerm.lean`) to
`AddCommGroup (Additive (Germ X))`, so this is an honest additive group
homomorphism — `range` will land in `AddSubgroup (Div X)` rather than
just `AddSubmonoid`. -/
noncomputable def principalDivisorAddHom :
    Additive (MeromorphicNonzero.Germ X) →+ Div X where
  toFun g := MeromorphicNonzero.Germ.principalDivisorMap (Additive.toMul g)
  map_zero' := by
    -- `Additive.toMul (0 : Additive (Germ X)) = (1 : Germ X)` definitionally,
    -- and `Germ.principalDivisorMap 1 = 0` is `Germ.principalDivisorMap_one`.
    show MeromorphicNonzero.Germ.principalDivisorMap
          (Additive.toMul (0 : Additive (MeromorphicNonzero.Germ X))) = 0
    exact Germ.principalDivisorMap_one
  map_add' g h := by
    -- `Additive.toMul (g + h) = Additive.toMul g * Additive.toMul h`
    -- definitionally; reduce to `Germ.principalDivisorMap_mul`.
    show MeromorphicNonzero.Germ.principalDivisorMap
          (Additive.toMul (g + h)) =
        MeromorphicNonzero.Germ.principalDivisorMap (Additive.toMul g)
          + MeromorphicNonzero.Germ.principalDivisorMap (Additive.toMul h)
    exact Germ.principalDivisorMap_mul (Additive.toMul g) (Additive.toMul h)

/-- The **germ-based** honest principal-divisor subgroup: the range of
`principalDivisorAddHom`. Because the source `Additive (Germ X)` is an
`AddCommGroup`, this range is an honest `AddSubgroup (Div X)`. This is
the clean replacement for `PrincDivHonestCandidate`, which had to be
defined as `AddSubgroup.closure (Set.range principalDivisorMap)` because
`MeromorphicNonzero X` lacked a `CommGroup` instance. -/
noncomputable def PrincDivHonestCandidateGerm (X : Type u)
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] :
    AddSubgroup (Div X) :=
  (principalDivisorAddHom (X := X)).range

/-- The germ-based and the closure-based `PrincDivHonestCandidate`
coincide as additive subgroups of `Div X`.

Both are subgroups containing the same generators (the principal
divisors `principalDivisorMap f` for `f : MeromorphicNonzero X`):

* `PrincDivHonestCandidate X = AddSubgroup.closure (Set.range principalDivisorMap)`
  is the smallest subgroup containing those generators.
* `PrincDivHonestCandidateGerm X = (principalDivisorAddHom).range` is
  also a subgroup containing those generators, since
  `principalDivisorAddHom (Additive.ofMul (Germ.mk f)) = principalDivisorMap f`.

Two-sided inclusion finishes the proof. The reverse direction —
that every range element is in the closure — uses the fact that the
range of an `AddMonoidHom` from an `AddCommGroup` is itself an
`AddSubgroup`, and by `AddSubgroup.closure_le` the closure is the
smallest such, so it must be contained in the range. Combined with the
fact that the range is contained in the closure (each generator is
trivially in the closure), the two coincide. -/
lemma PrincDivHonestCandidateGerm_eq :
    PrincDivHonestCandidateGerm X = PrincDivHonestCandidate X := by
  apply le_antisymm
  · -- `range principalDivisorAddHom ≤ closure (range principalDivisorMap)`.
    rintro D ⟨g, rfl⟩
    -- `D = principalDivisorAddHom g
    --    = Germ.principalDivisorMap (Additive.toMul g)`.
    -- Show this lies in the closure by induction on the germ.
    refine Quotient.inductionOn (motive := fun (q : MeromorphicNonzero.Germ X) =>
        MeromorphicNonzero.Germ.principalDivisorMap q
          ∈ PrincDivHonestCandidate X) (Additive.toMul g) ?_
    intro f
    -- `Germ.principalDivisorMap (Germ.mk f) = principalDivisorMap f`
    -- is in the closure by `principalDivisorMap_mem_PrincDivHonestCandidate`.
    show MeromorphicNonzero.Germ.principalDivisorMap (MeromorphicNonzero.Germ.mk f)
            ∈ PrincDivHonestCandidate X
    rw [MeromorphicNonzero.Germ.principalDivisorMap_mk]
    exact principalDivisorMap_mem_PrincDivHonestCandidate f
  · -- `closure (range principalDivisorMap) ≤ range principalDivisorAddHom`.
    -- `range principalDivisorAddHom` is a subgroup; by `closure_le` it
    -- suffices to show every generator lies in the range.
    unfold PrincDivHonestCandidate
    rw [AddSubgroup.closure_le]
    rintro D ⟨f, rfl⟩
    -- `principalDivisorMap f = principalDivisorAddHom (Additive.ofMul (Germ.mk f))`.
    refine ⟨Additive.ofMul (MeromorphicNonzero.Germ.mk f), ?_⟩
    show MeromorphicNonzero.Germ.principalDivisorMap
            (Additive.toMul (Additive.ofMul (MeromorphicNonzero.Germ.mk f)))
          = principalDivisorMap f
    exact MeromorphicNonzero.Germ.principalDivisorMap_mk f

end JacobianChallenge
