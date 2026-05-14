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
`g`-tuples `(γ ↦ pairing γ α₁, …, pairing γ αg)` over a basis
`(α₁, …, αg)` of `HolomorphicOneForm X`.

## Naming convention

Throughout this file, holomorphic 1-forms are bound to the variable `α`,
**not** `ω`. The latter is the scoped notation
`open scoped ContDiff` brings in for the analytic-smoothness regularity
(used in `[IsManifold 𝓘(ℂ) ω X]` etc.) and rebinding it as a term variable
shadows the notation and produces parse errors at uses like `α • ω + ω'`.

## Design — why a Tier-2 reduction here

The **honest** definition of the period integral
`∫_γ α` for a 1-cycle `γ ∈ H₁(X; ℤ)` and `α : HolomorphicOneForm X` requires:

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
  - a pairing `pairing : H1 →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ)` so
    additivity in the cycle and `ℂ`-linearity in the form are simultaneously
    enforced *by the type*, with no extra fields.
* `PeriodPairing data γ α` — the period of `α` over `γ` extracted from the
  bundle. The unbundled form most chips will use.
* Bilinearity / vanishing lemmas, all immediate from the bundling.
* `periodTuple data α` — the `ℤ`-linear functional `H1 → ℂ` obtained by
  fixing a holomorphic 1-form. Building block for the period matrix.
* `chartLocalPeriod` — a thin wrapper around
  `JacobianChallenge.pathIntegralOnInterval` documenting the connection to
  the chart-local building block already in `PeriodIntegral.lean`.

## What this file does NOT do

* It does **not** assert that a term of `PeriodPairingData X` exists. The
  inhabitation is a separate (currently open) chip that needs the singular
  homology of a Riemann surface plus a global path-integral construction.
* It does **not** modify any existing signature in
  `PeriodIntegral.lean`, `PeriodLattice.lean`, or
  `PeriodLatticeRankTwoG.lean`. All new content is additive.
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

* additivity in the cycle: `pairing (γ + γ') α = pairing γ α + pairing γ' α`,
* `ℂ`-linearity in the holomorphic 1-form: `pairing γ (a • α + α') =
  a • pairing γ α + pairing γ α'`,

so no extra `pairing_add` / `pairing_smul` fields are needed; they fall out
of `AddMonoidHom.map_add` and `LinearMap.map_add` / `LinearMap.map_smul`. -/
structure PeriodPairingData.{v} where
  /-- Carrier for the first integer homology `H₁(X; ℤ)`. Universe-poly
  so concrete instantiations (e.g. `SmoothCycle 𝓘(ℝ, ℂ) X` for `X : Type*`)
  can supply a carrier in the natural universe rather than `Type 0`. -/
  H1 : Type v
  /-- `H1` is an `AddCommGroup`. -/
  [H1_addCommGroup : AddCommGroup H1]
  /-- The period pairing as an `AddMonoidHom` from `H1` into the space of
  `ℂ`-linear functionals on `HolomorphicOneForm X`. -/
  pairing : H1 →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ)

attribute [instance] PeriodPairingData.H1_addCommGroup

/-- The **period pairing** as an unbundled function: given a period-pairing
bundle, a 1-cycle, and a holomorphic 1-form, produce the period in `ℂ`.

This is the building block subsequent chips invoke. The period lattice
`Λ` is then the additive subgroup of `ℂ^g` generated by the `g`-tuples
`(PeriodPairing data γ α_j)_{j=1..g}` over a basis `(α_1, …, α_g)` of
`HolomorphicOneForm X` and over all `γ : data.H1`. -/
def PeriodPairing {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    (data : PeriodPairingData X) (γ : data.H1) (α : HolomorphicOneForm X) : ℂ :=
  data.pairing γ α

/-- The period of any holomorphic 1-form along the zero cycle is `0`.
Immediate from `data.pairing` being an `AddMonoidHom`. -/
@[simp]
theorem PeriodPairing_zero_left {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (data : PeriodPairingData X) (α : HolomorphicOneForm X) :
    PeriodPairing data (0 : data.H1) α = 0 := by
  unfold PeriodPairing
  rw [map_zero]
  rfl

/-- Additivity in the cycle. Immediate from `data.pairing` being an
`AddMonoidHom`. -/
theorem PeriodPairing_add_left {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (data : PeriodPairingData X) (γ γ' : data.H1) (α : HolomorphicOneForm X) :
    PeriodPairing data (γ + γ') α = PeriodPairing data γ α + PeriodPairing data γ' α := by
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
    (data : PeriodPairingData X) (γ : data.H1) (α₁ α₂ : HolomorphicOneForm X) :
    PeriodPairing data γ (α₁ + α₂) = PeriodPairing data γ α₁ + PeriodPairing data γ α₂ := by
  unfold PeriodPairing
  exact map_add (data.pairing γ) α₁ α₂

/-- `ℂ`-linearity in the holomorphic 1-form. Immediate from
`data.pairing γ` being an `ℂ`-linear map. -/
theorem PeriodPairing_smul_right {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (data : PeriodPairingData X) (γ : data.H1) (a : ℂ)
    (α : HolomorphicOneForm X) :
    PeriodPairing data γ (a • α) = a • PeriodPairing data γ α := by
  unfold PeriodPairing
  exact map_smul (data.pairing γ) a α

/-- Negation in the cycle negates the period. -/
@[simp]
theorem PeriodPairing_neg_left {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (data : PeriodPairingData X) (γ : data.H1) (α : HolomorphicOneForm X) :
    PeriodPairing data (-γ) α = - PeriodPairing data γ α := by
  unfold PeriodPairing
  rw [map_neg]
  rfl

/-- The **period functional** of a fixed holomorphic 1-form: the `ℂ`-valued
`ℤ`-linear functional `γ ↦ ∫_γ α` on `H₁(X; ℤ)`. Building block for the
period matrix entries. -/
def periodTuple {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    (data : PeriodPairingData X) (α : HolomorphicOneForm X) :
    data.H1 →+ ℂ where
  toFun γ := PeriodPairing data γ α
  map_zero' := PeriodPairing_zero_left data α
  map_add' γ γ' := PeriodPairing_add_left data γ γ' α

/-- `periodTuple` evaluates exactly to `PeriodPairing`. -/
@[simp]
theorem periodTuple_apply {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    (data : PeriodPairingData X) (α : HolomorphicOneForm X) (γ : data.H1) :
    periodTuple data α γ = PeriodPairing data γ α := rfl

/-! ### Chart-local connection to `PeriodIntegral.lean`

The honest path-integral construction of the period pairing for a 1-cycle
represented by a finite chain of `C¹` chart-covered loops would, on each
chart-covered segment, produce a contribution of the form
`pathIntegralOnInterval (chart-pullback of α) (chartCoord φ γ) a b`
already defined in `PeriodIntegral.lean`. The wrapper below documents the
connection: a chart-local period contribution is *literally* the
chart-local interval integral.
-/

/-- **Chart-local contribution to a period.** Given a chart-pullback
`f : ℝ → (ℂ →L[ℂ] ℂ)` of a holomorphic 1-form `α` along the chart
coordinate of a path segment, and the chart-coordinate path `c : ℝ → ℂ`
of that segment over `[a, b]`, the contribution of this segment to the
period `∫_γ α` is precisely
`pathIntegralOnInterval f c a b = ∫_a^b f t (c'(t)) dt`. -/
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
`pathIntegralOnInterval_const_path`. -/
theorem chartLocalPeriod_const (f : ℝ → ℂ →L[ℂ] ℂ) (p : ℂ) (a b : ℝ) :
    chartLocalPeriod f (fun _ => p) a b = 0 :=
  pathIntegralOnInterval_const_path f p a b

end JacobianChallenge

end
