/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicAt
import JacobianChallenge.Manifold.RiemannSphere
import JacobianChallenge.Divisor.PrincipalDivisor
import Mathlib.Topology.Compactification.OnePoint.Basic

set_option diagnostics.threshold 100

/-! # Pole-extension of a meromorphic function to the Riemann sphere

This file builds the **pole extension**

`f̃ : X → RiemannSphere`

of a non-vanishing-germ meromorphic function `f : X → ℂ` on a compact
complex 1-manifold `X`. Concretely:

* `f̃ x = (some (f x) : OnePoint ℂ)` if `f` is regular at `x` (order `≥ 0`);
* `f̃ x = ∞` if `x` is a pole of `f` (order `< 0`).

The branching is controlled by the order in `WithTop ℤ` (so the case split
is between `0 ≤ order` — covering both finite-non-negative orders and the
unreachable `⊤` slot ruled out by `nonvanishing_germ` — and `order < 0`).

## What this file ships

* `MeromorphicNonzero.toRiemannSphere : (f : MeromorphicNonzero X) → X → RiemannSphere`
  — the genuine branched definition.
* `toRiemannSphere_apply_of_nonneg` and `toRiemannSphere_apply_of_neg`
  — point-wise unfolding lemmas matching the two branches.
* `toRiemannSphere_apply_of_orderTop` — convenience: a `⊤`-order point goes
  to `some (f x)` (vacuous in the presence of `nonvanishing_germ`, but
  useful for case splits).
* `toRiemannSphere_eq_some_iff_nonneg`,
  `toRiemannSphere_eq_infty_iff_neg` — the two `iff` characterizations of
  the branches, expressed in terms of the order.

* `toRiemannSphere_contMDiff_statement` —the `Prop`-valued **statement**
  that the pole extension is `ContMDiff ω` from `X` to `RiemannSphere`.
  Marked as a `Prop`-valued `def`, **not an axiom**: callers must explicitly
  thread it as a hypothesis. Discharging it requires:

  1. **At a regular point** `x` with order `≥ 0`: the pole set is locally
     finite (this is the local-finsupp content of
     `JacobianChallenge.MMeromorphicOn.divisor`, established in
     `Manifold/MeromorphicDivisor.lean`). On a punctured neighborhood of
     `x`, `f̃` agrees with the continuous map `(some : ℂ → OnePoint ℂ) ∘ f`,
     and `f` itself extends continuously by `MeromorphicAt.analyticAt`
     (continuity at `x` upgrades meromorphy to analyticity). The map is
     then read through the north chart `chartN` on the codomain, and the
     local representative is precisely the analytic representative of `f`.
  2. **At a pole** `x` with order `< 0`: again local finiteness of the
     pole set provides a punctured neighborhood with no other poles. On
     that neighborhood, `f̃ y = some (f y)` and `1 / (f̃ y) = some (1 / f y)`
     when `f y ≠ 0`. The function `1/f` extends analytically with value
     `0` at `x` (mathlib's `meromorphicOrderAt_inv` flips the sign of the
     order, so `1/f` has positive order at the pole, hence is analytic with
     `1/f (x) = 0`). The map `f̃` is then read through the south chart
     `chartS` on the codomain (which sends `(some w) ↦ 1/w` for `w ≠ 0` and
     `∞ ↦ 0`); the local representative is the analytic representative of
     `1/f`.

Both branches require chart-side bookkeeping through `OpenPartialHomeomorph`
and the `ChartedSpace ℂ X` atlas. The owed material is recorded honestly in
`OPEN.md` (this `Prop`-only statement is the named hook).

This is the **R1** discharge from
`JacobianChallenge.Manifold.ResidueTheorem`'s named-gap decomposition.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set OnePoint

namespace JacobianChallenge

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace MeromorphicNonzero

/-- The **pole extension** of a non-vanishing-germ meromorphic function
`f : X → ℂ` to a map `f̃ : X → RiemannSphere`.

* At a regular point `x` (`0 ≤ mmeromorphicOrderAt I f.toFun x` in
  `WithTop ℤ`), `f̃ x = (some (f.toFun x) : OnePoint ℂ)`.
* At a pole `x` (`mmeromorphicOrderAt I f.toFun x < 0`), `f̃ x = ∞`.

The branching is on the actual `WithTop ℤ` order (not its `untop₀`-image),
so the `⊤` case (germ identically zero) is folded into the `0 ≤` branch
where it would map to `some (f.toFun x)` — but this branch is unreachable
under the `nonvanishing_germ` field of `MeromorphicNonzero X`. -/
def toRiemannSphere (f : MeromorphicNonzero X) : X → RiemannSphere :=
  fun x =>
    if 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x then
      (OnePoint.some (f.toFun x) : RiemannSphere)
    else
      ∞

/-! ### Branch-unfolding lemmas

These are the API-friendly point-wise unfoldings of `toRiemannSphere` at
the two branches. They are stated in terms of the underlying order in
`WithTop ℤ`, not its `untop₀`-image, so they compose cleanly with the order
theory in `Manifold/MeromorphicAt.lean` and the divisor packaging in
`Manifold/MeromorphicDivisor.lean`. -/

/-- At a regular point (order `≥ 0`), the pole extension equals the simple
coercion `some (f x)` into `OnePoint ℂ`. -/
@[simp] lemma toRiemannSphere_apply_of_nonneg
    (f : MeromorphicNonzero X) {x : X}
    (hx : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    f.toRiemannSphere x = (OnePoint.some (f.toFun x) : RiemannSphere) := by
  unfold toRiemannSphere
  rw [if_pos hx]

/-- At a pole (order `< 0`), the pole extension equals `∞`. -/
@[simp] lemma toRiemannSphere_apply_of_neg
    (f : MeromorphicNonzero X) {x : X}
    (hx : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0) :
    f.toRiemannSphere x = (∞ : RiemannSphere) := by
  unfold toRiemannSphere
  rw [if_neg (not_le.mpr hx)]

/-- The pole extension of `f` is `some (f x)` iff `x` is a regular point
of `f` (order `≥ 0`). -/
lemma toRiemannSphere_eq_some_iff_nonneg
    (f : MeromorphicNonzero X) (x : X) :
    f.toRiemannSphere x = (OnePoint.some (f.toFun x) : RiemannSphere) ↔
      0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x := by
  constructor
  · intro h
    by_contra hneg
    push_neg at hneg
    rw [toRiemannSphere_apply_of_neg f hneg] at h
    exact (OnePoint.infty_ne_coe (f.toFun x)) h
  · intro h
    exact toRiemannSphere_apply_of_nonneg f h

/-- The pole extension of `f` is `∞` iff `x` is a pole of `f` (order `< 0`).
The `→` direction uses the `nonvanishing_germ` field to rule out the (in
this branch unreachable) `⊤`-order point: by definition of the `if`, the
pole extension is `∞` only when the order is **not** `≥ 0`, i.e. strictly
less than `0` in `WithTop ℤ`; together with `order ≠ ⊤` this is exactly
`order < 0`. -/
lemma toRiemannSphere_eq_infty_iff_neg
    (f : MeromorphicNonzero X) (x : X) :
    f.toRiemannSphere x = (∞ : RiemannSphere) ↔
      mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0 := by
  constructor
  · intro h
    by_contra hnonneg
    push_neg at hnonneg
    rw [toRiemannSphere_apply_of_nonneg f hnonneg] at h
    exact (OnePoint.coe_ne_infty (f.toFun x)) h
  · intro h
    exact toRiemannSphere_apply_of_neg f h

/-- The pole extension never sends a regular point's image to `∞`:
contrapositive form, useful for chart-source membership arguments. -/
lemma toRiemannSphere_ne_infty_of_nonneg
    (f : MeromorphicNonzero X) {x : X}
    (hx : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    f.toRiemannSphere x ≠ (∞ : RiemannSphere) := by
  rw [toRiemannSphere_apply_of_nonneg f hx]
  exact OnePoint.coe_ne_infty _

/-- The pole extension at a pole point is exactly `∞` (not a finite value).
Useful for chartS-source membership arguments. -/
lemma toRiemannSphere_ne_some_of_neg
    (f : MeromorphicNonzero X) {x : X}
    (hx : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0) (z : ℂ) :
    f.toRiemannSphere x ≠ (OnePoint.some z : RiemannSphere) := by
  rw [toRiemannSphere_apply_of_neg f hx]
  exact OnePoint.infty_ne_coe _

/-! ### `ContMDiff` of the pole extension — statement-only

The full discharge is a substantial chart-bookkeeping argument; see the
file header for the proof sketch. We expose a `Prop`-valued `def` (not an
`axiom`) so callers must explicitly thread it as a hypothesis. -/

/-- **(R1, statement only)** The pole extension of `f` is `ContMDiff` from
`X` to `RiemannSphere` (with model `𝓘(ℂ, ℂ) → 𝓘(ℂ)`, smoothness `ω`).

This is named with the `_statement` suffix so that callers see it is a
**Prop-valued statement**, not a proven theorem. The full discharge requires
chart-side analysis through both `RiemannSphere.chartN` (at regular points,
where the local representative is the analytic representative of `f`) and
`RiemannSphere.chartS` (at poles, where the local representative is the
analytic representative of `1 / f`, valid because
`meromorphicOrderAt_inv` flips the sign of the order). The chart-pullback
characterization `MMeromorphicAt.iff_of_isManifold` from
`Manifold/MeromorphicAt.lean` together with the local-finiteness of the
pole set (from the divisor in `Manifold/MeromorphicDivisor.lean`) supplies
all the analytic ingredients; the remaining work is the
`ContMDiffAt`-via-charts unfold and the local representative identification
through the `RiemannSphere` chart formulas. -/
def toRiemannSphere_contMDiff_statement (f : MeromorphicNonzero X) : Prop :=
  ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f.toRiemannSphere

end MeromorphicNonzero

end JacobianChallenge
