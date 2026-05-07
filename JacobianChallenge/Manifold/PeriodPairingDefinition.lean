/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneForm
import JacobianChallenge.Manifold.PeriodIntegral
import JacobianChallenge.Manifold.PeriodLattice
import JacobianChallenge.Manifold.PeriodLatticeRankTwoG

/-! # The period pairing — Tier-2 named-hypothesis bundle (chip ZZ81)

This file makes **explicit** the period pairing

  `PeriodPairing : H₁(X; ℤ) → HolomorphicOneForm X → ℂ`

so that subsequent chips know what abstract object to invoke, and so that the
period lattice `Λ ⊆ ℂ^g` can be built on top of it as the integer span of the
`g`-tuples `(γ ↦ pairing γ ω₁, …, pairing γ ωg)` over a basis `(ω₁, …, ωg)`
of `HolomorphicOneForm X`.

## Design — why a Tier-2 reduction here

The **honest** definition of the period integral
`∫_γ ω` for a 1-cycle `γ ∈ H₁(X; ℤ)` and `ω : HolomorphicOneForm X` requires:

* A type for `H₁(X; ℤ)` — singular homology of a complex manifold is not
  packaged at the mathlib pin (`8e3c989104daaa052921bf43de9eef0e1ac9fbf5`,
  15 Apr 2026). `Mathlib.AlgebraicTopology.SingularSet` exists, but the
  abelian group `H_1` of a Riemann surface as an `AddCommGroup` with a
  `Free` `ℤ`-rank-`2g` certificate is not derivable from what is there.
* A globally-defined path integral. The sister file
  `PeriodIntegral.lean` honestly stops at the chart-local building block
  `pathIntegralOnInterval`, with a docstring explaining why a
  cover-and-glue construction is unwritten infrastructure rather than a
  five-line adapter.

Per the strict-reader rule (`OPEN.md`), we do **not** ship a
`PeriodPairing` whose body is `0` — that would mislead a reviewer into
thinking the pairing is defined when only its type is, and would silently
agree with the trivial answer `0` for every period.

Instead we follow the same Tier-2 pattern as
`PeriodLatticeRankTwoG.lean`: package the pairing as a *named hypothesis
bundle* `PeriodPairingData X`. A strict reader who supplies an honest
`H₁(X; ℤ)` and an honest pairing function lands a term of this bundle;
downstream chips then use the bundle to *build* the period lattice
`Λ` and the rank-`2g` certificate of `PeriodLatticeOfRankTwoG X`.

## What this file delivers

* `PeriodPairingData X` — a structure packaging
  - a type `H1` for first integer homology (with `AddCommGroup` instance),
  - a pairing `pairing : H1 → HolomorphicOneForm X →ₗ[ℂ] ℂ`,
  - the fact that the pairing is `ℤ`-additive in `H1` (i.e.
    `pairing (γ + γ') ω = pairing γ ω + pairing γ' ω`), already implicit in
    `H1` being an `AddCommGroup` once we use `AddMonoidHom` for the outer
    map. We use `H1 →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ)` so additivity in
    the cycle and `ℂ`-linearity in the form are simultaneously enforced
    *by the type*, with no extra fields.
* `PeriodPairing data γ ω` — the period of `ω` over `γ` extracted from the
  bundle. The unbundled form most chips will use.
* `PeriodPairing_zero_left`, `PeriodPairing_add_left`, `PeriodPairing_zero_right`,
  `PeriodPairing_add_right`, `PeriodPairing_smul_right` — the bilinearity
  lemmas, all immediate from the bundling.
* `periodTuple data ω` — the `ℂ`-linear functional `H1 → ℂ` obtained by
  fixing a holomorphic 1-form. Building block for the period matrix.
* `chartLocalPeriod` — a thin wrapper around
  `JacobianChallenge.pathIntegralOnInterval` documenting the connection to
  the chart-local building block already in `PeriodIntegral.lean`. The
  wrapper makes explicit the *intended* contribution of one chart-covered
  segment of a 1-cycle's representative loop to its period.

## What this file does NOT do

* It does **not** assert that a term of `PeriodPairingData X` exists. The
  inhabitation is a separate (currently open) chip that needs the singular
  homology of a Riemann surface plus a global path-integral construction.
* It does **not** modify any existing signature in
  `PeriodIntegral.lean`, `PeriodLattice.lean`, or
  `PeriodLatticeRankTwoG.lean`. All new content is additive.
* It does **not** wire `Jacobian X` to use this bundle. That is a downstream
  call.

## Connection to ZZ77's `PeriodLatticeOfRankTwoG`

A `PeriodPairingData X` together with a basis of `HolomorphicOneForm X`
produces the candidate lattice
`Λ = AddSubgroup.closure { (pairing γ ω₁, …, pairing γ ωg) | γ : data.H1 }`.
The closedness, rank, and discreteness fields of
`PeriodLatticeOfRankTwoG X` then become *theorems* about `Λ` (the Riemann
bilinear relations + `H1 ≃ ℤ^{2g}`), each one of which is itself a
named-hypothesis chip downstream. This file does not perform that bridge
— it provides the building block the bridge will invoke.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

set_option diagnostics.threshold 100

namespace JacobianChallenge

variable (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Named-hypothesis bundle** for the period pairing on a complex
manifold `X` modelled on `ℂ`.

A strict reader supplies:

* a carrier `H1` for `H₁(X; ℤ)` with an `AddCommGroup` structure,
* the pairing as an `AddMonoidHom` from `H1` into the `ℂ`-linear
  functionals on `HolomorphicOneForm X`.

Bundling the pairing as `H1 →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ)` enforces by
the *types*:

* additivity in the cycle: `pairing (γ + γ') ω = pairing γ ω + pairing γ' ω`,
* `ℂ`-linearity in the holomorphic 1-form: `pairing γ (a • ω + ω') =
  a • pairing γ ω + pairing γ ω'`,

so no extra `pairing_add` / `pairing_smul` fields are needed; they fall out
of `AddMonoidHom.map_add` and `LinearMap.map_add` / `LinearMap.map_smul`.

This is the type a future closure of "the period pairing exists" will
inhabit. Once such a term lands, the downstream period lattice
construction in `PeriodLatticeRankTwoG.lean` can use it to populate the
`lattice` field of `PeriodLatticeOfRankTwoG X`. -/
structure PeriodPairingData where
  /-- Carrier for the first integer homology `H₁(X; ℤ)`. The honest choice
  is the singular `H_1` of `X` as a topological space, with its
  `AddCommGroup` structure; that object is not in mathlib at the pin, so
  we leave the carrier as a hypothesis. -/
  H1 : Type
  /-- `H1` is an `AddCommGroup`. Required for the pairing to have additivity
  in the cycle and for `H1` to map into the additive group of
  `ℂ`-linear functionals. -/
  [H1_addCommGroup : AddCommGroup H1]
  /-- The period pairing as an `AddMonoidHom` from `H1` into the space of
  `ℂ`-linear functionals on `HolomorphicOneForm X`. The choice of an
  `AddMonoidHom`-of-`LinearMap` (rather than two separate fields with
  bilinearity axioms) packages additivity-in-`γ` and `ℂ`-linearity-in-`ω`
  in a single object that automatically discharges all eight bilinearity
  lemmas via mathlib's existing API. -/
  pairing : H1 →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ)

namespace PeriodPairingData

variable {X}

/-- Make the bundled `AddCommGroup` instance available to the elaborator
when it sees `data.H1`. -/
attribute [instance] PeriodPairingData.H1_addCommGroup

end PeriodPairingData

/-- The **period pairing** as an unbundled function: given a period-pairing
bundle, a 1-cycle, and a holomorphic 1-form, produce the period in `ℂ`.

This is the building block subsequent chips invoke. The period lattice
`Λ` is then the additive subgroup of `ℂ^g` generated by the `g`-tuples
`(PeriodPairing data γ ω_j)_{j=1..g}` over a basis `(ω_1, …, ω_g)` of
`HolomorphicOneForm X` and over all `γ : data.H1`. -/
def PeriodPairing {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    (data : PeriodPairingData X) (γ : data.H1) (ω : HolomorphicOneForm X) : ℂ :=
  data.pairing γ ω

/-- The period of any holomorphic 1-form along the zero cycle is `0`.
Immediate from `data.pairing` being an `AddMonoidHom`. -/
@[simp]
theorem PeriodPairing_zero_left {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (data : PeriodPairingData X) (ω : HolomorphicOneForm X) :
    PeriodPairing data (0 : data.H1) ω = 0 := by
  unfold PeriodPairing
  rw [map_zero]
  rfl

/-- Additivity in the cycle. Immediate from `data.pairing` being an
`AddMonoidHom`. -/
theorem PeriodPairing_add_left {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (data : PeriodPairingData X) (γ γ' : data.H1) (ω : HolomorphicOneForm X) :
    PeriodPairing data (γ + γ') ω = PeriodPairing data γ ω + PeriodPairing data γ' ω := by
  unfold PeriodPairing
  rw [map_add]
  rfl

/-- The period of the zero 1-form along any cycle is `0`. Immediate from
`data.pairing γ` being an `ℂ`-linear map. -/
@[simp]
theorem PeriodPairing_zero_right {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (data : PeriodPairingData X) (γ : data.H1) :
    PeriodPairing data γ (0 : HolomorphicOneForm X) = 0 := by
  unfold PeriodPairing
  exact map_zero (data.pairing γ)

/-- Additivity in the holomorphic 1-form. Immediate from `data.pairing γ`
being an `ℂ`-linear map. -/
theorem PeriodPairing_add_right {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (data : PeriodPairingData X) (γ : data.H1) (ω₁ ω₂ : HolomorphicOneForm X) :
    PeriodPairing data γ (ω₁ + ω₂) = PeriodPairing data γ ω₁ + PeriodPairing data γ ω₂ := by
  unfold PeriodPairing
  exact map_add (data.pairing γ) ω₁ ω₂

/-- `ℂ`-linearity in the holomorphic 1-form. Immediate from
`data.pairing γ` being an `ℂ`-linear map. -/
theorem PeriodPairing_smul_right {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (data : PeriodPairingData X) (γ : data.H1) (a : ℂ)
    (ω : HolomorphicOneForm X) :
    PeriodPairing data γ (a • ω) = a • PeriodPairing data γ ω := by
  unfold PeriodPairing
  exact map_smul (data.pairing γ) a ω

/-- Negation in the cycle negates the period. Immediate from `data.pairing`
being an `AddMonoidHom` into an `AddCommGroup`. -/
@[simp]
theorem PeriodPairing_neg_left {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (data : PeriodPairingData X) (γ : data.H1) (ω : HolomorphicOneForm X) :
    PeriodPairing data (-γ) ω = - PeriodPairing data γ ω := by
  unfold PeriodPairing
  rw [map_neg]
  rfl

/-- The **period functional** of a fixed holomorphic 1-form: the `ℂ`-valued
`ℤ`-linear functional `γ ↦ ∫_γ ω` on `H₁(X; ℤ)`. Building block for the
period matrix entries: choosing a basis `(ω_1, …, ω_g)` of
`HolomorphicOneForm X` and a basis `(γ_1, …, γ_{2g})` of `data.H1` gives
the `g × 2g` period matrix `(periodTuple data ω_j γ_i)_{i,j}`. -/
def periodTuple {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    (data : PeriodPairingData X) (ω : HolomorphicOneForm X) :
    data.H1 →+ ℂ where
  toFun γ := PeriodPairing data γ ω
  map_zero' := PeriodPairing_zero_left data ω
  map_add' γ γ' := PeriodPairing_add_left data γ γ' ω

/-- `periodTuple` evaluates exactly to `PeriodPairing`. -/
@[simp]
theorem periodTuple_apply {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    (data : PeriodPairingData X) (ω : HolomorphicOneForm X) (γ : data.H1) :
    periodTuple data ω γ = PeriodPairing data γ ω := rfl

/-! ### Chart-local connection to `PeriodIntegral.lean`

The honest path-integral construction of the period pairing for a 1-cycle
represented by a finite chain of `C¹` chart-covered loops would, on each
chart-covered segment, produce a contribution of the form
`pathIntegralOnInterval (chart-pullback of ω) (chartCoord φ γ) a b`
already defined in `PeriodIntegral.lean`. The wrapper below documents the
connection: a chart-local period contribution is *literally* the
chart-local interval integral.

This wrapper does **not** sum the contributions over a chain or prove
chart-independence; both are open infrastructure. It only names the
single-chart contribution so that downstream chips constructing a term
of `PeriodPairingData X` from a chain decomposition have an explicit
reference to invoke.
-/

/-- **Chart-local contribution to a period.** Given a chart-pullback
`f : ℝ → (ℂ →L[ℂ] ℂ)` of a holomorphic 1-form `ω` along the chart
coordinate of a path segment, and the chart-coordinate path `c : ℝ → ℂ`
of that segment over `[a, b]`, the contribution of this segment to the
period `∫_γ ω` is precisely
`pathIntegralOnInterval f c a b = ∫_a^b f t (c'(t)) dt`.

This is a thin alias of `pathIntegralOnInterval` that exists to make the
"this is one chart's slice of a period" intent explicit at the call
site. The full period in the bundled `PeriodPairing` is, mathematically,
a sum of such contributions over a Lebesgue cover of `[0, 1]` for any
representative loop of the cycle class — but that summation is open
infrastructure (see the docstring of `PeriodIntegral.lean`). -/
def chartLocalPeriod (f : ℝ → ℂ →L[ℂ] ℂ) (c : ℝ → ℂ) (a b : ℝ) : ℂ :=
  pathIntegralOnInterval f c a b

/-- `chartLocalPeriod` unfolds to `pathIntegralOnInterval`. -/
theorem chartLocalPeriod_eq (f : ℝ → ℂ →L[ℂ] ℂ) (c : ℝ → ℂ) (a b : ℝ) :
    chartLocalPeriod f c a b = pathIntegralOnInterval f c a b := rfl

/-- Reversing the segment bounds negates the chart-local period
contribution. Inherited from `pathIntegralOnInterval_symm`. -/
theorem chartLocalPeriod_symm (f : ℝ → ℂ →L[ℂ] ℂ) (c : ℝ → ℂ) (a b : ℝ) :
    chartLocalPeriod f c b a = - chartLocalPeriod f c a b :=
  pathIntegralOnInterval_symm f c a b

/-- A constant segment contributes nothing to the period. Inherited from
`pathIntegralOnInterval_const_path`. This is the chart-local instance of
"a 1-cycle represented by a constant loop has zero period for every
holomorphic 1-form". -/
theorem chartLocalPeriod_const (f : ℝ → ℂ →L[ℂ] ℂ) (p : ℂ) (a b : ℝ) :
    chartLocalPeriod f (fun _ => p) a b = 0 :=
  pathIntegralOnInterval_const_path f p a b

end JacobianChallenge

end
