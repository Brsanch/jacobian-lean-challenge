/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor
import JacobianChallenge.Divisor.PrincipalDivisor

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

* `principalDivisorAddHom : Multiplicative (MeromorphicNonzero X) →+ Div X`
  — the multiplicative principal-divisor map repackaged as an additive
  group homomorphism, with `map_zero'` exactly the bundle's
  `principalDivisorMap_one` and `map_add'` exactly the bundle's
  `principalDivisorMap_mul` (load-bearing).
* `PrincDivHonestCandidate X : AddSubgroup (Div X)` — the *eventual* honest
  `PrincDiv X`, defined as `principalDivisorAddHom.range`.
* `ResidueTheorem X : Prop` — the named (statement-only) classical input.
* `residueTheorem_iff_range_le_Div0` — the residue theorem is equivalent
  to `PrincDivHonestCandidate X ≤ Div0 X`. **Real proof, not `Iff.rfl`.**

## What this file does **not** do

* It does **not** provide an instance of `PrincipalDivisorMultiplicative X`.
  That is the deliverable of a sister file (`feat/principal-divisor-
  multiplicative`, owed by I1) that proves the four facts directly from the
  `MMeromorphicAt.mul` / `MMeromorphicAt.inv` / `MMeromorphicOn.const`
  lemmas plus the local-order valuation property. As long as no instance is
  in scope, `principalDivisorAddHom` and `PrincDivHonestCandidate` are
  noncomputable definitions parametrised by the (currently absent)
  instance, and the rest of the file consumes only their definitions —
  nothing here uses sorry or axiom.
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
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    extends CommGroup (MeromorphicNonzero X) where
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

/-! ## The principal divisor map as an `AddMonoidHom` -/

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- The **principal divisor map as an `AddMonoidHom`**, sending a
non-vanishing-germ meromorphic function `f` (viewed *additively* via the
`Multiplicative` wrapper) to its order divisor `(f) ∈ Div X`.

* `toFun` is `principalDivisorMap` composed with `Multiplicative.toAdd`'s
  underlying carrier identification (the carrier of `Multiplicative G` is
  literally `G`; we use `Multiplicative.toAdd` only to get the additive
  `0` and `+` to line up with `principalDivisorMap_one` /
  `principalDivisorMap_mul`).
* `map_zero'` is exactly `principalDivisorMap_one`.
* `map_add'` is exactly `principalDivisorMap_mul`.

Both compatibility fields are **load-bearing**: they are the typeclass
`PrincipalDivisorMultiplicative X` fields, not duplicated proofs. -/
def principalDivisorAddHom [PrincipalDivisorMultiplicative X] :
    Multiplicative (MeromorphicNonzero X) →+ Div X where
  toFun f := principalDivisorMap (Multiplicative.toAdd f)
  map_zero' := PrincipalDivisorMultiplicative.principalDivisorMap_one
  map_add' f g :=
    PrincipalDivisorMultiplicative.principalDivisorMap_mul
      (Multiplicative.toAdd f) (Multiplicative.toAdd g)

/-- Apply lemma for `principalDivisorAddHom`: it agrees with
`principalDivisorMap` on the `Multiplicative.toAdd` image. -/
@[simp] lemma principalDivisorAddHom_apply
    [PrincipalDivisorMultiplicative X]
    (f : Multiplicative (MeromorphicNonzero X)) :
    principalDivisorAddHom f = principalDivisorMap (Multiplicative.toAdd f) :=
  rfl

/-- Apply lemma for `principalDivisorAddHom` on the canonical
`Multiplicative.ofAdd` lift of a bare `MeromorphicNonzero X`: it agrees
with `principalDivisorMap`. -/
@[simp] lemma principalDivisorAddHom_ofAdd
    [PrincipalDivisorMultiplicative X] (f : MeromorphicNonzero X) :
    principalDivisorAddHom (Multiplicative.ofAdd f) = principalDivisorMap f :=
  rfl

/-! ## The eventual honest `PrincDiv X` -/

/-- The **eventual honest `PrincDiv X`**: the additive subgroup of
`Div X` consisting of all principal divisors `(f)` for
`f : MeromorphicNonzero X`. Concretely it is the range of
`principalDivisorAddHom`.

This definition is gated on `[PrincipalDivisorMultiplicative X]`; the
eventual one-line swap in `Divisor.lean` is

```
noncomputable def PrincDiv (X : Type*) ... [PrincipalDivisorMultiplicative X] :
    AddSubgroup (Div X) :=
  principalDivisorAddHom.range
```

at which point `PrincDiv X = PrincDivHonestCandidate X` definitionally. -/
def PrincDivHonestCandidate (X : Type u)
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    [PrincipalDivisorMultiplicative X] : AddSubgroup (Div X) :=
  (principalDivisorAddHom (X := X)).range

/-- Membership in `PrincDivHonestCandidate X` unfolds to "is in the image
of `principalDivisorMap`". -/
lemma mem_PrincDivHonestCandidate
    [PrincipalDivisorMultiplicative X] {D : Div X} :
    D ∈ PrincDivHonestCandidate X
      ↔ ∃ f : MeromorphicNonzero X, principalDivisorMap f = D := by
  unfold PrincDivHonestCandidate
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨Multiplicative.toAdd g, by simpa using hg⟩
  · rintro ⟨f, hf⟩
    exact ⟨Multiplicative.ofAdd f, by simpa using hf⟩

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
    [ConnectedSpace X] [PrincipalDivisorMultiplicative X] :
    ResidueTheorem X ↔ PrincDivHonestCandidate X ≤ Div0 X := by
  constructor
  · -- Residue theorem ⇒ inclusion.
    intro hRes D hD
    -- `D` is in the range, so `D = principalDivisorMap f` for some `f`.
    rw [mem_PrincDivHonestCandidate] at hD
    obtain ⟨f, hf⟩ := hD
    -- Goal: `D ∈ Div0 X`, i.e. `degreeHom D = 0`.
    show D ∈ (Div.degreeHom (X := X)).ker
    rw [AddMonoidHom.mem_ker, Div.degreeHom_apply, ← hf]
    exact hRes f
  · -- Inclusion ⇒ residue theorem.
    intro hLe f
    -- Plug `principalDivisorMap f` into the inclusion.
    have hMem : principalDivisorMap f ∈ PrincDivHonestCandidate X := by
      rw [mem_PrincDivHonestCandidate]
      exact ⟨f, rfl⟩
    have hKer : principalDivisorMap f ∈ (Div.degreeHom (X := X)).ker := hLe hMem
    rw [AddMonoidHom.mem_ker, Div.degreeHom_apply] at hKer
    exact hKer

end JacobianChallenge
