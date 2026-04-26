/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor
import JacobianChallenge.Manifold.MeromorphicAt
import JacobianChallenge.Manifold.MeromorphicDivisor

set_option diagnostics.threshold 100

/-! # The principal divisor map

This file builds the **principal divisor map** that sends a non-zero global
meromorphic function `f : X → ℂ` on a compact complex 1-manifold to its
order divisor `(f) := ∑_x ord_x(f) · [x]` in `Div X`. Concretely, it is a
genuine `Div X`-valued function on the type `MeromorphicNonzero X`, defined
by invoking `JacobianChallenge.MMeromorphicOn.divisor` (the chart-pullback
order divisor packaged in `Manifold/MeromorphicDivisor.lean`).

## The intended use

The set `range principalDivisorMap` is the future honest `PrincDiv X`
subgroup of `Div X` (currently `⊥` in `Divisor.lean`). The remaining
input — that the range is contained in `Div⁰ X`, equivalently the
residue theorem on a compact Riemann surface — is **not** in this file;
this file only builds the map.

## What's load-bearing

The `MeromorphicNonzero X` structure carries three fields:

* `toFun : X → ℂ`
* `meromorphic : MMeromorphicOn (𝓘(ℂ, ℂ)) toFun Set.univ`
* `nonvanishing_germ : ∀ x, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) toFun x ≠ ⊤`

The `nonvanishing_germ` field is the standard non-vanishing-germ hypothesis
("no point has identically-zero germ"). It is **load-bearing**: without it,
`MMeromorphicOn.divisor` cannot be applied (its third argument is exactly
this hypothesis, and the local-finiteness of the support fails for the
identically-zero function).

The constant-zero function does not give a `MeromorphicNonzero X` because
`mmeromorphicOrderAt 𝓘(ℂ,ℂ) 0 x = ⊤` everywhere (the germ is identically
zero). This is the correct semantic exclusion. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace JacobianChallenge

universe u

/-- A **non-vanishing-germ meromorphic function** on `X`: a function
`f : X → ℂ`, a proof that `f` is meromorphic on `Set.univ`, and a proof
that no germ of `f` is identically zero (`mmeromorphicOrderAt I f x ≠ ⊤`
everywhere).

The non-vanishing-germ field is the standard hypothesis under which the
order divisor is locally finite and `principalDivisorMap` is well-defined.
The model is hard-coded to `𝓘(ℂ, ℂ)` (the trivial complex model), matching
the rest of the manifold-meromorphic API in this repository. -/
structure MeromorphicNonzero (X : Type u)
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] where
  /-- The underlying function `X → ℂ`. -/
  toFun : X → ℂ
  /-- `toFun` is meromorphic on the whole manifold. -/
  meromorphic : MMeromorphicOn (𝓘(ℂ, ℂ)) toFun Set.univ
  /-- No point of `X` carries an identically-zero germ of `toFun`
  (equivalently, `toFun` is not the zero function in any chart neighborhood). -/
  nonvanishing_germ :
    ∀ x, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) toFun x ≠ ⊤

namespace MeromorphicNonzero

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- Coercion from `MeromorphicNonzero X` to the underlying function `X → ℂ`. -/
instance : CoeFun (MeromorphicNonzero X) (fun _ => X → ℂ) where
  coe f := f.toFun

end MeromorphicNonzero

/-- The **principal divisor map**: send a non-vanishing-germ meromorphic
function `f : MeromorphicNonzero X` to its order divisor `(f)` in `Div X`.

The body genuinely invokes `JacobianChallenge.MMeromorphicOn.divisor` from
`Manifold/MeromorphicDivisor.lean`; in particular all three fields of
`MeromorphicNonzero` are load-bearing inputs to that divisor construction. -/
noncomputable def principalDivisorMap
    {X : Type u}
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (f : MeromorphicNonzero X) : Div X :=
  JacobianChallenge.MMeromorphicOn.divisor (𝓘(ℂ, ℂ)) f.toFun
    f.meromorphic f.nonvanishing_germ

/-- The pointwise value of `principalDivisorMap f` at `x` is the integer
order `orderFun 𝓘(ℂ,ℂ) f.toFun x = (mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x).untop₀`.
This unfolds the divisor's `toFun` field and is the API-friendly form of the
underlying definition. -/
@[simp] lemma principalDivisorMap_apply
    {X : Type u}
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (f : MeromorphicNonzero X) (x : X) :
    (principalDivisorMap f : X → ℤ) x
      = JacobianChallenge.MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x := rfl

/-! ### Multiplicativity of the chart-pulled-back meromorphic order

The lemma `mmeromorphicOrderAt_mul` lifts mathlib's `meromorphicOrderAt_mul`
(`Mathlib/Analysis/Meromorphic/Order.lean`) through the chart-pullback
definition of `mmeromorphicOrderAt`. The proof is purely chart-pullback
bookkeeping: the chart representative of `f * g` is the pointwise product
of the chart representatives of `f` and `g`, so the standard
multiplicativity transports verbatim.

The constant-`1` order lemma `mmeromorphicOrderAt_one` follows from
`meromorphicOrderAt_const` at `c = 1 ≠ 0`. -/

variable {X : Type u}
  [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Multiplicativity of the chart-pulled-back meromorphic order.**
`mmeromorphicOrderAt I (f * g) x = mmeromorphicOrderAt I f x +
mmeromorphicOrderAt I g x` whenever both `f` and `g` are meromorphic at `x`.

Proof: unfold both sides to `meromorphicOrderAt` of chart pullbacks; observe
`(f * g) ∘ (chartAt ℂ x).symm = (f ∘ (chartAt ℂ x).symm) * (g ∘ (chartAt ℂ x).symm)`
definitionally; apply mathlib's `meromorphicOrderAt_mul`. -/
lemma mmeromorphicOrderAt_mul
    {I : ModelWithCorners ℂ ℂ ℂ} {f g : X → ℂ} {x : X}
    (hf : MMeromorphicAt I f x) (hg : MMeromorphicAt I g x) :
    mmeromorphicOrderAt I (f * g) x
      = mmeromorphicOrderAt I f x + mmeromorphicOrderAt I g x := by
  -- Unpack chart-pullback meromorphy of `f` and `g`.
  have hf' : MeromorphicAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hf
  have hg' : MeromorphicAt (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hg
  -- LHS: `mmeromorphicOrderAt I (f*g) x` is `meromorphicOrderAt ((f*g) ∘ ...) ...`
  -- and `(f * g) ∘ (chartAt ℂ x).symm = (f ∘ ...) * (g ∘ ...)` is rfl.
  show meromorphicOrderAt ((f * g) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
      = meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
        + meromorphicOrderAt (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  have h_comp : (f * g) ∘ (chartAt ℂ x).symm
      = (f ∘ (chartAt ℂ x).symm) * (g ∘ (chartAt ℂ x).symm) := rfl
  rw [h_comp]
  exact meromorphicOrderAt_mul hf' hg'

/-- **The chart-pulled-back order of the constant `1` is zero.** -/
lemma mmeromorphicOrderAt_one
    {I : ModelWithCorners ℂ ℂ ℂ} {x : X} :
    mmeromorphicOrderAt I (1 : X → ℂ) x = 0 := by
  -- LHS: unfold to `meromorphicOrderAt ((1 : X → ℂ) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)`.
  show meromorphicOrderAt ((1 : X → ℂ) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0
  -- `(1 : X → ℂ) ∘ (chartAt ℂ x).symm = fun _ => (1 : ℂ)` definitionally.
  have h_comp : ((1 : X → ℂ) ∘ (chartAt ℂ x).symm) = (fun _ : ℂ => (1 : ℂ)) := rfl
  rw [h_comp]
  -- Then apply `meromorphicOrderAt_const` at `c = 1`, which is `≠ 0`.
  classical
  rw [meromorphicOrderAt_const ((chartAt ℂ x) x) (1 : ℂ)]
  simp

end JacobianChallenge

/-! ## `MeromorphicNonzero X` as a commutative monoid

We endow `MeromorphicNonzero X` with pointwise multiplication and the
constant `1`, then bundle into a `CommMonoid`. The non-vanishing-germ field
is preserved by `mmeromorphicOrderAt_mul`: `order(f*g) = order(f) + order(g)`,
and `WithTop.add_eq_top.not.mpr` kills the `⊤` case from each individual
non-vanishing-germ hypothesis. The constant `1` has order `0 ≠ ⊤`. -/

namespace JacobianChallenge.MeromorphicNonzero

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- Pointwise multiplication of non-vanishing-germ meromorphic functions
is again a non-vanishing-germ meromorphic function. The non-vanishing-germ
hypothesis is preserved via `mmeromorphicOrderAt_mul`: the order of the
product is the sum of the two orders, and a sum in `WithTop ℤ` is `⊤`
iff one of the summands is `⊤` (which neither is, by hypothesis). -/
noncomputable instance : Mul (MeromorphicNonzero X) where
  mul f g :=
    { toFun := fun x => f.toFun x * g.toFun x
      meromorphic := f.meromorphic.mul g.meromorphic
      nonvanishing_germ := by
        intro x
        -- `(f * g) x = f x * g x` is `rfl`; we need
        -- `mmeromorphicOrderAt I (f.toFun * g.toFun) x ≠ ⊤`.
        have hf_at : MMeromorphicAt 𝓘(ℂ, ℂ) f.toFun x := f.meromorphic x trivial
        have hg_at : MMeromorphicAt 𝓘(ℂ, ℂ) g.toFun x := g.meromorphic x trivial
        have h_sum : mmeromorphicOrderAt 𝓘(ℂ, ℂ)
            (f.toFun * g.toFun) x
            = mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun x
              + mmeromorphicOrderAt 𝓘(ℂ, ℂ) g.toFun x :=
          mmeromorphicOrderAt_mul hf_at hg_at
        rw [h_sum]
        -- `a + b ≠ ⊤` from `a ≠ ⊤` and `b ≠ ⊤` in `WithTop ℤ`.
        intro h_top
        rw [WithTop.add_eq_top] at h_top
        rcases h_top with h | h
        · exact f.nonvanishing_germ x h
        · exact g.nonvanishing_germ x h }

/-- `(f * g).toFun x = f.toFun x * g.toFun x`. Definitional. -/
@[simp] lemma mul_toFun (f g : MeromorphicNonzero X) (x : X) :
    (f * g).toFun x = f.toFun x * g.toFun x := rfl

/-- The constant function `1` as a `MeromorphicNonzero`. -/
noncomputable def one (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] :
    MeromorphicNonzero X :=
  { toFun := fun _ => (1 : ℂ)
    meromorphic := MMeromorphicOn.const (1 : ℂ)
    nonvanishing_germ := by
      intro x
      -- `(fun _ : X => (1 : ℂ)) = (1 : X → ℂ)` definitionally (Pi instance).
      have h_eq : (fun _ : X => (1 : ℂ)) = (1 : X → ℂ) := rfl
      rw [h_eq, mmeromorphicOrderAt_one]
      exact WithTop.zero_ne_top }

noncomputable instance : One (MeromorphicNonzero X) := ⟨one X⟩

/-- `(1 : MeromorphicNonzero X).toFun x = 1`. Definitional. -/
@[simp] lemma one_toFun (x : X) :
    ((1 : MeromorphicNonzero X)).toFun x = (1 : ℂ) := rfl

/-- Two `MeromorphicNonzero X` values are equal iff their underlying
functions are equal pointwise. Proof-irrelevance on the two `Prop` fields
(`meromorphic`, `nonvanishing_germ`) does the rest. -/
@[ext] theorem ext_aux {f g : MeromorphicNonzero X}
    (h : ∀ x, f.toFun x = g.toFun x) : f = g := by
  cases f with
  | mk f1 f2 f3 =>
    cases g with
    | mk g1 g2 g3 =>
      have hfg : f1 = g1 := funext h
      subst hfg
      rfl

/-- Pointwise multiplication on `MeromorphicNonzero X` is associative,
commutative, and has the constant `1` as identity. The proofs reduce to
extensionality on `toFun` and the underlying ring laws on `ℂ`. -/
noncomputable instance : CommMonoid (MeromorphicNonzero X) where
  mul_assoc f g h := by
    apply ext_aux
    intro x
    -- LHS: ((f * g) * h).toFun x = (f.toFun x * g.toFun x) * h.toFun x
    -- RHS: (f * (g * h)).toFun x = f.toFun x * (g.toFun x * h.toFun x)
    show (f.toFun x * g.toFun x) * h.toFun x = f.toFun x * (g.toFun x * h.toFun x)
    exact mul_assoc _ _ _
  one_mul f := by
    apply ext_aux
    intro x
    show (1 : ℂ) * f.toFun x = f.toFun x
    exact one_mul _
  mul_one f := by
    apply ext_aux
    intro x
    show f.toFun x * (1 : ℂ) = f.toFun x
    exact mul_one _
  mul_comm f g := by
    apply ext_aux
    intro x
    show f.toFun x * g.toFun x = g.toFun x * f.toFun x
    exact mul_comm _ _

end JacobianChallenge.MeromorphicNonzero

/-! ## `principalDivisorMap` is multiplicative

We prove that `principalDivisorMap` sends pointwise multiplication on
`MeromorphicNonzero X` to addition on `Div X`. This is the load-bearing
additivity of the order divisor and is the prerequisite for bundling
`principalDivisorMap` as an `AddMonoidHom`.

Both lemmas reduce by extensionality on `Div X` to pointwise statements
about `orderFun = (mmeromorphicOrderAt _ _ _).untop₀`. -/

namespace JacobianChallenge

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- The order divisor of `1 : MeromorphicNonzero X` is the zero divisor:
the constant function `1` has order zero everywhere. -/
@[simp] lemma principalDivisorMap_one :
    principalDivisorMap (1 : MeromorphicNonzero X) = (0 : Div X) := by
  classical
  ext x
  -- LHS: `principalDivisorMap_apply` reduces to `orderFun 𝓘(ℂ,ℂ) (1).toFun x`,
  -- and `(1 : MeromorphicNonzero X).toFun = fun _ => (1 : ℂ)` definitionally
  -- (via `MeromorphicNonzero.one`).
  show JacobianChallenge.MMeromorphicOn.orderFun 𝓘(ℂ, ℂ)
      ((1 : MeromorphicNonzero X).toFun) x = (0 : Div X) x
  have h_one : (1 : MeromorphicNonzero X).toFun = (1 : X → ℂ) := rfl
  rw [h_one]
  -- `orderFun I 1 x = (mmeromorphicOrderAt I 1 x).untop₀ = (0).untop₀ = 0`.
  unfold MMeromorphicOn.orderFun
  rw [mmeromorphicOrderAt_one]
  rfl

/-- The order divisor of a product is the sum of order divisors:
`ord_x(f * g) = ord_x(f) + ord_x(g)`, summed over `x`. -/
lemma principalDivisorMap_mul (f g : MeromorphicNonzero X) :
    principalDivisorMap (f * g)
      = principalDivisorMap f + principalDivisorMap g := by
  classical
  ext x
  -- LHS via `principalDivisorMap_apply` and definitional `(f*g).toFun = f.toFun * g.toFun`.
  show JacobianChallenge.MMeromorphicOn.orderFun 𝓘(ℂ, ℂ)
      ((f * g).toFun) x
    = (principalDivisorMap f + principalDivisorMap g : Div X) x
  -- The sum in `Div X` is pointwise integer sum.
  have h_sum_apply :
      ((principalDivisorMap f + principalDivisorMap g : Div X) : X → ℤ) x
        = JacobianChallenge.MMeromorphicOn.orderFun 𝓘(ℂ, ℂ) f.toFun x
          + JacobianChallenge.MMeromorphicOn.orderFun 𝓘(ℂ, ℂ) g.toFun x := by
    simp [Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
  rw [h_sum_apply]
  -- Now reduce LHS via `mmeromorphicOrderAt_mul`. `(f*g).toFun = f.toFun * g.toFun`
  -- is definitional from the `Mul` instance.
  show (mmeromorphicOrderAt 𝓘(ℂ, ℂ) (fun y => f.toFun y * g.toFun y) x).untop₀
      = (mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun x).untop₀
        + (mmeromorphicOrderAt 𝓘(ℂ, ℂ) g.toFun x).untop₀
  -- Rewrite the multiplicand into `f.toFun * g.toFun` (Pi.mul_apply is rfl).
  have h_eq_mul : (fun y => f.toFun y * g.toFun y) = f.toFun * g.toFun := rfl
  rw [h_eq_mul]
  have hf_at : MMeromorphicAt 𝓘(ℂ, ℂ) f.toFun x := f.meromorphic x trivial
  have hg_at : MMeromorphicAt 𝓘(ℂ, ℂ) g.toFun x := g.meromorphic x trivial
  have h_order :
      mmeromorphicOrderAt 𝓘(ℂ, ℂ) (f.toFun * g.toFun) x
        = mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun x
          + mmeromorphicOrderAt 𝓘(ℂ, ℂ) g.toFun x :=
    mmeromorphicOrderAt_mul hf_at hg_at
  rw [h_order]
  exact WithTop.untop₀_add (f.nonvanishing_germ x) (g.nonvanishing_germ x)

end JacobianChallenge
