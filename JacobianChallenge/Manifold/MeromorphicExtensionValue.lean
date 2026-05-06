/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicExtension

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Pointwise value characterizations of `f.toRiemannSphere`

For `f : MeromorphicNonzero X` and `x : X`, this file packages the four
pointwise characterizations of the value `f.toRiemannSphere x` in terms of
the meromorphic order at `x` and the literal value `f.toFun x`:

* `toRiemannSphere_eq_some_of_order_nonneg` — at a regular point or zero
  (i.e. `0 ≤ mmeromorphicOrderAt I f x`), the pole extension takes the
  literal value `OnePoint.some (f.toFun x)`.

* `toRiemannSphere_eq_infty_of_order_neg` — at a pole (i.e.
  `mmeromorphicOrderAt I f x < 0`), the pole extension takes the value
  `∞`.

* `toRiemannSphere_eq_some_zero_iff` — `f.toRiemannSphere x = some 0`
  iff `x` is a regular point at which `f.toFun x = 0`.  Note that the
  honest characterization here is `0 ≤ order ∧ f.toFun x = 0`, not
  `order > 0`: `MeromorphicNonzero` constrains the *germ* of `f.toFun`
  but does not force the pointwise value `f.toFun x` to match the
  germ's analytic value, so a pointwise zero of `f.toFun` need not
  coincide with a positive-order point.

* `toRiemannSphere_eq_infty_iff` — `f.toRiemannSphere x = ∞` iff `x`
  is a pole, i.e. `mmeromorphicOrderAt I f x < 0`.

Items 1, 2 and 4 are thin re-namings of the already-shipped lemmas
`toRiemannSphere_apply_of_nonneg`, `toRiemannSphere_apply_of_neg` and
`toRiemannSphere_eq_infty_iff_neg` in `MeromorphicExtension.lean`. They
are provided here under the user-facing names for downstream callers
that prefer the "value-characterization" naming convention.

Item 3 is genuine new content; the proof mirrors the set-level
counterpart `some_zero_fiber_set_eq` in `FiberCountBridge.lean` but
imports nothing beyond `MeromorphicExtension`.
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

/-- **Value at non-poles.** If `0 ≤ mmeromorphicOrderAt I f x` (a
regular point or a zero), then `f.toRiemannSphere x` is the literal
finite value `OnePoint.some (f.toFun x)`. -/
lemma toRiemannSphere_eq_some_of_order_nonneg
    (f : MeromorphicNonzero X) {x : X}
    (hx : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    f.toRiemannSphere x = (OnePoint.some (f.toFun x) : RiemannSphere) :=
  f.toRiemannSphere_apply_of_nonneg hx

/-- **Value at poles.** If `mmeromorphicOrderAt I f x < 0` (a pole),
then `f.toRiemannSphere x = ∞`. -/
lemma toRiemannSphere_eq_infty_of_order_neg
    (f : MeromorphicNonzero X) {x : X}
    (hx : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0) :
    f.toRiemannSphere x = (∞ : RiemannSphere) :=
  f.toRiemannSphere_apply_of_neg hx

/-- **`some 0` characterization.** The pole extension takes the value
`some 0` exactly at points which are regular *and* literally vanish:
`0 ≤ mmeromorphicOrderAt I f x ∧ f.toFun x = 0`.

This is the honest pointwise version: `MeromorphicNonzero` constrains
only the *germ* of `f.toFun`, not the pointwise value, so we cannot
strengthen to `0 < order` without an additional germ-vs-value
hypothesis.  Compare with the set-level `some_zero_fiber_set_eq` in
`FiberCountBridge`. -/
lemma toRiemannSphere_eq_some_zero_iff
    (f : MeromorphicNonzero X) (x : X) :
    f.toRiemannSphere x = (OnePoint.some (0 : ℂ) : RiemannSphere) ↔
      0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x ∧ f.toFun x = 0 := by
  constructor
  · intro hx
    -- `f̃ x = some 0`, in particular `f̃ x ≠ ∞`, so the order is `≥ 0`.
    have hnonneg : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x := by
      by_contra hneg
      push_neg at hneg
      rw [f.toRiemannSphere_apply_of_neg hneg] at hx
      exact (OnePoint.infty_ne_coe (0 : ℂ)) hx
    refine ⟨hnonneg, ?_⟩
    -- At a regular point, `f̃ x = some (f x) = some 0`, so `f x = 0`.
    rw [f.toRiemannSphere_apply_of_nonneg hnonneg] at hx
    exact OnePoint.coe_injective hx
  · intro ⟨hnonneg, hzero⟩
    rw [f.toRiemannSphere_apply_of_nonneg hnonneg, hzero]

/-- **`∞` characterization.** The pole extension takes the value `∞`
exactly at poles, i.e. points with `mmeromorphicOrderAt I f x < 0`.
This is a thin renaming of `toRiemannSphere_eq_infty_iff_neg`. -/
lemma toRiemannSphere_eq_infty_iff
    (f : MeromorphicNonzero X) (x : X) :
    f.toRiemannSphere x = (∞ : RiemannSphere) ↔
      mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0 :=
  f.toRiemannSphere_eq_infty_iff_neg x

end MeromorphicNonzero

end JacobianChallenge

end
