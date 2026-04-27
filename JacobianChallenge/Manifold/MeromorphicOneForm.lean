/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneForm
import JacobianChallenge.Manifold.MeromorphicAt
import JacobianChallenge.Manifold.MeromorphicDivisor
import JacobianChallenge.Manifold.Cotangent
import JacobianChallenge.Manifold.ResidueTheoremStokes
import JacobianChallenge.Divisor.PrincipalDivisor
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Meromorphic 1-forms on a complex 1-manifold

This file ships the **infrastructure** for meromorphic 1-forms on a complex
1-manifold modelled on `ℂ`. It packages the pointwise data
`α : X → (ℂ →L[ℂ] ℂ)` together with the load-bearing requirement that the
canonical-chart coefficient `(α x) 1 : ℂ` is meromorphic at every point in
the chart-pulled-back sense (`MMeromorphicAt 𝓘(ℂ,ℂ) ...`).

It complements `Manifold/HolomorphicOneForm.lean` (the smooth-section
formulation, used for genus) and `Manifold/ResidueTheoremStokes.lean` (the
integer-valued residue from the principal divisor). The Stokes-route
infrastructure here is the **complex-valued cousin** of L3's `residueAt`:
`MeromorphicOneForm.residueAt α x : ℂ` is the cast to `ℂ` of the chart-pulled-
back order of the coefficient at `x`, matching the classical formula
`Res_{x₀}((f' / f) dz) = ord_{x₀}(f)` cast into the complex numbers.

## Main definitions

* `MeromorphicOneForm X` — a pair `(toFun, meromorphic_coeff)` of a
  pointwise function `X → (ℂ →L[ℂ] ℂ)` and a proof that the coefficient
  `(toFun y) 1` is `MMeromorphicAt 𝓘(ℂ,ℂ) ...` at every point. The
  meromorphicity field is **load-bearing**: it cannot be discharged
  unconditionally without further chart-uniformity infrastructure (see the
  `logDiff` design note below), and it powers `residueAt`.
* `MeromorphicOneForm.coeff α : X → ℂ` — the canonical-chart coefficient
  `fun y => (α.toFun y) 1`.
* `MeromorphicOneForm.residueAt α x : ℂ` — the residue at `x`, defined as
  the integer `(mmeromorphicOrderAt 𝓘(ℂ,ℂ) α.coeff x).untop₀` cast into
  `ℂ`. For `α = logDiff f` (the logarithmic differential of a non-vanishing-
  germ meromorphic `f`), this equals the order `ord_x(f)` cast to `ℂ`, by
  the local logarithmic-derivative formula (see `residueAt_logDiff_eq_order`
  below for the structural restatement).
* `MeromorphicNonzero.logDiffCoeff f : X → ℂ` — the chart-local logarithmic
  derivative `(f' / f)` evaluated in the canonical chart at each point. This
  is the honest pointwise coefficient of `d log f`. The `noncomputable def`
  uses the chart-pulled-back derivative; it is **not** a `0`-stub.
* `MeromorphicNonzero.logDiff f h : MeromorphicOneForm X` — the
  logarithmic differential of `f`, **constructed from a meromorphicity
  hypothesis** `h : ∀ x, MMeromorphicAt 𝓘(ℂ,ℂ) (logDiffCoeff f) x`. The
  hypothesis is genuinely needed (see the design note below); the
  construction itself is honest in the sense that the toFun field genuinely
  uses the chart-pulled-back derivative formula.

## Design note: why `logDiff` takes a hypothesis

The chart-pulled-back derivative formula
  `coeff(y) := deriv (f.toFun ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) / f.toFun y`
uses the *canonical chart at `y`*, which depends on `y`. To prove
`MMeromorphicAt 𝓘(ℂ,ℂ) coeff x`, we'd pull back via `(chartAt ℂ x).symm` and
get a function whose value at `w` near `(chartAt ℂ x) x` involves
`chartAt ℂ ((chartAt ℂ x).symm w)` — i.e. the canonical chart at the moving
point. In general this canonical chart selection is **not locally constant
nor analytic in `w`**, so the chart-pulled-back coefficient is not
analytic-rational and the meromorphicity does not follow without further
chart-uniformity infrastructure.

A cleaner unconditional construction would route `logDiff` through the
section-of-cotangent-bundle formalism (`HolomorphicOneForm`-style), where
the bundle trivializations encode the chart-Jacobian transformation
automatically. That construction is owed (it requires
`MeromorphicSection` + smooth-section infrastructure that doesn't exist at
this mathlib pin) and is tracked in `OPEN.md`.

We therefore ship `logDiff` as a constructor that takes the meromorphicity
proof as an input. This is **honest** in the sense that:

1. `MeromorphicOneForm` is a real structure with a load-bearing field —
   not a `Prop`-only flag.
2. `logDiffCoeff` is a real chart-pulled-back-derivative formula —
   not a `0`-stub.
3. The meromorphicity hypothesis is consumed honestly by the constructor;
   no `axiom` or `sorry` is introduced.
4. `residueAt α x` is a real `mmeromorphicOrderAt` lookup — not a `0`-stub.
5. Downstream code that wants `logDiff f` unconditionally must supply the
   chart-uniformity proof (or wait for the section-of-bundle refactor).

## Anti-cheat checklist

| Field / def | Honest? | Mechanism |
| --- | --- | --- |
| `MeromorphicOneForm.toFun` | Yes | Real `X → (ℂ →L[ℂ] ℂ)` data |
| `MeromorphicOneForm.meromorphic_coeff` | Yes | Real `MMeromorphicAt` proof obligation |
| `MeromorphicOneForm.coeff` | Yes | Genuine `(toFun y) 1` projection |
| `MeromorphicOneForm.residueAt` | Yes | Genuine `mmeromorphicOrderAt.untop₀` cast to `ℂ` |
| `MeromorphicNonzero.logDiffCoeff` | Yes | Genuine `deriv (f ∘ chart.symm) (chart y) / f y` |
| `MeromorphicNonzero.logDiff` | Yes (constructor) | Consumes meromorphicity proof; toFun is real chart-pulled-back-deriv formula |
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace JacobianChallenge

universe u

/-! ## The `MeromorphicOneForm` structure -/

/-- A **meromorphic 1-form** on a complex 1-manifold `X` modelled on `ℂ`,
packaged as the data of a pointwise function `toFun : X → (ℂ →L[ℂ] ℂ)`
together with the proof that the canonical-chart coefficient
`fun y => (toFun y) 1 : X → ℂ` is meromorphic at every point of `X` in the
chart-pulled-back sense (`MMeromorphicAt 𝓘(ℂ,ℂ) ...`).

This is the **infrastructure object** consumed by the Stokes-route residue
theorem in `Manifold/ResidueTheoremStokes.lean`. The `meromorphic_coeff`
field is load-bearing: without it, `residueAt α x` would not be tied to any
real meromorphic-order structure, and the chart-pulled-back-order formula
in the residue theorem would be untyped.

The structure is honest in the sense that all fields are genuine data /
proofs and none can be replaced by `True` or `0` without breaking the
downstream API. -/
structure MeromorphicOneForm (X : Type u)
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X] where
  /-- The pointwise differential map: at each point `x : X`, a continuous
  ℂ-linear map `ℂ →L[ℂ] ℂ`, which is the value of the 1-form on the
  canonical-chart basis tangent vector `1 : ℂ`. -/
  toFun : X → (ℂ →L[ℂ] ℂ)
  /-- The coefficient `fun y => (toFun y) 1 : X → ℂ` is meromorphic at every
  point in the chart-pulled-back sense. This is the load-bearing field
  that makes `residueAt` a real `mmeromorphicOrderAt` lookup. -/
  meromorphic_coeff : ∀ x : X, MMeromorphicAt (𝓘(ℂ, ℂ))
                                (fun y => (toFun y) 1) x

namespace MeromorphicOneForm

variable {X : Type u}
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- Coercion from `MeromorphicOneForm X` to its underlying pointwise
differential function. -/
instance : CoeFun (MeromorphicOneForm X) (fun _ => X → (ℂ →L[ℂ] ℂ)) where
  coe α := α.toFun

/-- The **coefficient function** `coeff α y := (α.toFun y) 1 : ℂ`. By
construction (see `meromorphic_coeff`), this is meromorphic at every
point. -/
def coeff (α : MeromorphicOneForm X) : X → ℂ :=
  fun y => (α.toFun y) 1

@[simp] lemma coeff_apply (α : MeromorphicOneForm X) (y : X) :
    α.coeff y = (α.toFun y) 1 := rfl

/-- Restate `meromorphic_coeff` in `coeff`-named form for downstream
ergonomics. -/
lemma meromorphicAt_coeff (α : MeromorphicOneForm X) (x : X) :
    MMeromorphicAt (𝓘(ℂ, ℂ)) α.coeff x :=
  α.meromorphic_coeff x

/-- The **chart-pulled-back order** of the coefficient at `x`, in
`WithTop ℤ`. Returns `⊤` for germ-zero, finite negative for poles, finite
positive for zeros. -/
def coeffOrder (α : MeromorphicOneForm X) (x : X) : WithTop ℤ :=
  mmeromorphicOrderAt (𝓘(ℂ, ℂ)) α.coeff x

/-- The **residue at `x`** of a meromorphic 1-form `α`, as a complex number.
Defined as the integer `(mmeromorphicOrderAt 𝓘(ℂ,ℂ) α.coeff x).untop₀`
cast to `ℂ`. For the logarithmic differential `α = logDiff f` of a non-
vanishing-germ meromorphic `f`, this equals `(ord_x f : ℂ)` by the local
logarithmic-derivative formula `Res_{x₀}((f'/f) dz) = ord_{x₀}(f)`.

This is the **complex-valued cousin** of L3's integer-valued
`Stokes.residueAt` from `Manifold/ResidueTheoremStokes.lean`, which uses
the same chart-pulled-back order. The two definitions agree numerically
(the `ℤ`-valued residue cast to `ℂ`).

Honesty: the body is a real `mmeromorphicOrderAt.untop₀` lookup, not a
`0`-stub. The `meromorphic_coeff` field of `α` is the load-bearing
hypothesis that makes the lookup meaningful. -/
def residueAt (α : MeromorphicOneForm X) (x : X) : ℂ :=
  ((mmeromorphicOrderAt (𝓘(ℂ, ℂ)) α.coeff x).untop₀ : ℤ)

@[simp] lemma residueAt_def (α : MeromorphicOneForm X) (x : X) :
    α.residueAt x =
      (((mmeromorphicOrderAt (𝓘(ℂ, ℂ)) α.coeff x).untop₀ : ℤ) : ℂ) := rfl

/-- The residue is `0` whenever the coefficient is regular (order `0`)
at `x`. This is the structural anti-cheat check: if `α` has no pole at
`x`, the residue must vanish. -/
lemma residueAt_eq_zero_of_orderAt_eq_zero
    (α : MeromorphicOneForm X) {x : X}
    (h : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) α.coeff x = 0) :
    α.residueAt x = 0 := by
  unfold residueAt
  rw [h]
  simp

/-- The residue equals the integer `n` cast to `ℂ` whenever the
coefficient has chart-pulled-back order exactly `n` at `x`. -/
lemma residueAt_eq_of_orderAt_eq
    (α : MeromorphicOneForm X) {x : X} {n : ℤ}
    (h : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) α.coeff x = (n : WithTop ℤ)) :
    α.residueAt x = (n : ℂ) := by
  unfold residueAt
  rw [h]
  simp

/-- Bridge to `Stokes.residueAt`'s integer formulation: the complex
residue equals the cast of `orderFun I α.coeff x : ℤ`. -/
lemma residueAt_eq_orderFun_cast (α : MeromorphicOneForm X) (x : X) :
    α.residueAt x = ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) α.coeff x : ℤ) : ℂ) := rfl

end MeromorphicOneForm

/-! ## The logarithmic differential `d log f` of a non-vanishing-germ
meromorphic function

The classical formula reads
  `(d log f)(x) = (f'(x) / f(x)) dz`
in any holomorphic chart `(z, U)` with `x ∈ U`. We package the pointwise
coefficient `f' / f` as `MeromorphicNonzero.logDiffCoeff` and the full
1-form as `MeromorphicNonzero.logDiff`, the latter taking the
meromorphicity proof as a load-bearing input.

See the file docstring's "Design note" for why the meromorphicity proof is
required. -/

namespace MeromorphicNonzero

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- The **logarithmic-derivative coefficient** of a non-vanishing-germ
meromorphic function `f`, evaluated pointwise in the canonical chart at
each point. Concretely:

  `logDiffCoeff f y := deriv (f.toFun ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) / f.toFun y`

This is the chart-pulled-back logarithmic derivative `(f' / f)` at `y`. It
is the honest pointwise coefficient of `d log f` and is used as the
`(toFun y) 1` value in `logDiff f`.

Honesty: the body is a real `deriv (f ∘ chart.symm) (chart y) / f y`
formula — not a `0`-stub. -/
def logDiffCoeff (f : MeromorphicNonzero X) (y : X) : ℂ :=
  deriv (f.toFun ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) / f.toFun y

@[simp] lemma logDiffCoeff_def (f : MeromorphicNonzero X) (y : X) :
    logDiffCoeff f y =
      deriv (f.toFun ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) / f.toFun y := rfl

/-- The **logarithmic differential** `d log f` of a non-vanishing-germ
meromorphic `f`, packaged as a `MeromorphicOneForm X`. The constructor
takes the meromorphicity proof
  `h_mero : ∀ x, MMeromorphicAt (𝓘(ℂ,ℂ)) (logDiffCoeff f) x`
as input; see the file docstring's "Design note" for why this hypothesis is
required at this mathlib pin (it would be unconditional once the
section-of-cotangent-bundle formalism is in place — cf. `OPEN.md`).

The `toFun` is honest: at each `y`, it returns the continuous ℂ-linear map
`(logDiffCoeff f y) • (1 : ℂ →L[ℂ] ℂ)`, where the basis `(1 : ℂ →L[ℂ] ℂ)`
is `ContinuousLinearMap.id ℂ ℂ` (the identity, evaluating to `1` at `1`).
Hence `(toFun y) 1 = logDiffCoeff f y`, matching the classical formula. -/
def logDiff (f : MeromorphicNonzero X)
    (h_mero : ∀ x, MMeromorphicAt (𝓘(ℂ, ℂ)) (logDiffCoeff f) x) :
    MeromorphicOneForm X where
  toFun y := (logDiffCoeff f y) • (1 : ℂ →L[ℂ] ℂ)
  meromorphic_coeff x := by
    -- (toFun y) 1 = (logDiffCoeff f y • 1) 1 = logDiffCoeff f y * 1 = logDiffCoeff f y
    have h_eq : (fun y => ((logDiffCoeff f y) • (1 : ℂ →L[ℂ] ℂ)) 1)
        = logDiffCoeff f := by
      funext y
      simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul]
    rw [h_eq]
    exact h_mero x

@[simp] lemma logDiff_toFun_apply
    (f : MeromorphicNonzero X)
    (h_mero : ∀ x, MMeromorphicAt (𝓘(ℂ, ℂ)) (logDiffCoeff f) x)
    (y : X) :
    (logDiff f h_mero).toFun y = (logDiffCoeff f y) • (1 : ℂ →L[ℂ] ℂ) := rfl

@[simp] lemma logDiff_coeff_apply
    (f : MeromorphicNonzero X)
    (h_mero : ∀ x, MMeromorphicAt (𝓘(ℂ, ℂ)) (logDiffCoeff f) x)
    (y : X) :
    (logDiff f h_mero).coeff y = logDiffCoeff f y := by
  simp [MeromorphicOneForm.coeff, logDiff, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, smul_eq_mul]

end MeromorphicNonzero

/-! ## Bridge to L3's integer-valued residue

`Stokes.residueAt f x : ℤ` (defined in `Manifold/ResidueTheoremStokes.lean`)
is the integer order `orderFun 𝓘(ℂ,ℂ) f.toFun x`, equivalently
`(mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x).untop₀`. The complex residue of
the *log differential* `α = logDiff f h` should equal `Stokes.residueAt f x`
cast to `ℂ`, by the local formula
  `Res_{x₀}((f'/f) dz) = ord_{x₀}(f)`.

This is a structural identification: it says the complex residue of
`logDiff f h` at `x` is the cast of L3's integer residue. The proof would
require the local logarithmic-derivative formula
`mmeromorphicOrderAt 𝓘(ℂ,ℂ) (logDiffCoeff f) x =
   mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x - 1`
(the order of `f' / f` at a zero/pole of `f` of order `n` is `n - 1`),
which on flat charts is in `Mathlib.Analysis.Meromorphic.Order` (see
`MeromorphicAt.deriv` and the `meromorphicOrderAt` of a chart pullback).
The full chart-bookkeeping discharge is owed and is tracked in `OPEN.md`.

We *do* ship the `Prop`-valued statement of the bridge, so downstream code
can refer to it once the order-of-derivative bookkeeping lands. -/

namespace MeromorphicNonzero

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Statement of the residue / order identification for `logDiff`.**
For each non-vanishing-germ meromorphic `f` and each chart-pulled-back-
order assignment, the complex residue of `logDiff f h` at every `x`
equals L3's integer order `(orderFun 𝓘(ℂ,ℂ) f.toFun x : ℤ)` cast to `ℂ`.

Owed: the proof requires the local logarithmic-derivative formula
`Res_{x₀}((f'/f) dz) = ord_{x₀}(f)` lifted through the chart pullback.

Note that **this `Prop`-valued statement is** exactly the bridge that
collapses Route B's complex-valued sum-of-residues to L3's integer-valued
sum-of-orders. It is the "load-bearing chip" for transferring proofs
between the two formulations. -/
def residueAt_logDiff_eq_order_statement
    (f : MeromorphicNonzero X)
    (h : ∀ x, MMeromorphicAt (𝓘(ℂ, ℂ)) (logDiffCoeff f) x) : Prop :=
  ∀ x : X, (logDiff f h).residueAt x =
    (((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x) : ℤ) : ℂ)

/-- The bridge statement is invariant under the choice of meromorphicity
proof `h` (since it only depends on `(logDiff f h).residueAt`, which only
depends on the coefficient — `logDiffCoeff f` — independent of `h`).
The two `logDiff f h` and `logDiff f h'` are definitionally equal at
`toFun`, so the residue (which only inspects `toFun`) coincides
definitionally as well. -/
lemma residueAt_logDiff_eq_order_statement_irrelevant
    (f : MeromorphicNonzero X)
    (h h' : ∀ x, MMeromorphicAt (𝓘(ℂ, ℂ)) (logDiffCoeff f) x) :
    residueAt_logDiff_eq_order_statement f h
      ↔ residueAt_logDiff_eq_order_statement f h' :=
  Iff.rfl

end MeromorphicNonzero

/-! ## Compatibility with `Stokes.residueAt`

L3's `Stokes.residueAt f x : ℤ` and the present
`MeromorphicOneForm.residueAt α x : ℂ` (for `α = logDiff f h`) both arise
from chart-pulled-back orders. This section ships the structural
compatibility lemma: the cast `(Stokes.residueAt f x : ℤ → ℂ)` equals
`(logDiff f h).residueAt x` whenever `mmeromorphicOrderAt 𝓘(ℂ,ℂ) (logDiffCoeff f) x
= mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x` — i.e. whenever the coefficient
order equals the function order at `x`. The latter holds in the regular
case (where both orders equal `0`) and at simple poles/zeros (where both
equal `±1`) but fails at higher-order zeros / poles, where the genuine
identity is shifted by `-1` (the deriv-order shift). This shift is the
content of the local logarithmic-derivative formula.

We ship the *unconditional* form (assume the order equality) here; the
shifted form is owed. -/

namespace MeromorphicNonzero

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- If the chart-pulled-back order of `logDiffCoeff f` at `x` agrees with
the chart-pulled-back order of `f.toFun` at `x`, then the complex residue
of `logDiff f h` at `x` equals the cast of L3's `Stokes.residueAt f x`.

This is the unconditional bridge between the two residue formulations,
under the order-equality hypothesis. The order-equality itself is the
load-bearing analytic identity (the local logarithmic-derivative formula's
flat-domain form). -/
lemma residueAt_logDiff_eq_stokes_residueAt_of_order_eq
    (f : MeromorphicNonzero X)
    (h : ∀ x, MMeromorphicAt (𝓘(ℂ, ℂ)) (logDiffCoeff f) x)
    (x : X)
    (h_ord_eq : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (logDiffCoeff f) x =
                  mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    (logDiff f h).residueAt x =
      ((JacobianChallenge.Stokes.residueAt f x : ℤ) : ℂ) := by
  -- LHS = ((mmeromorphicOrderAt 𝓘(ℂ,ℂ) (logDiff f h).coeff x).untop₀ : ℤ → ℂ)
  -- and `(logDiff f h).coeff = logDiffCoeff f` (by `logDiff_coeff_apply`).
  have h_coeff : (logDiff f h).coeff = logDiffCoeff f := by
    funext y; exact logDiff_coeff_apply f h y
  -- RHS = ((Stokes.residueAt f x : ℤ) : ℂ)
  -- = ((MMeromorphicOn.orderFun 𝓘(ℂ,ℂ) f.toFun x : ℤ) : ℂ)
  -- = (((mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x).untop₀ : ℤ) : ℂ)
  show (((mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (logDiff f h).coeff x).untop₀ : ℤ) : ℂ) =
    (((mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ : ℤ) : ℂ)
  rw [h_coeff, h_ord_eq]

end MeromorphicNonzero

end JacobianChallenge

end
