/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphere
import JacobianChallenge.Manifold.HolomorphicOneForm
import Mathlib.Analysis.Complex.Liouville
import Mathlib.LinearAlgebra.Dimension.Finite

set_option diagnostics.threshold 100

/-! # Genus zero for the Riemann sphere — reductions and statements

This file packages the genus-zero half of `genus_eq_zero_iff_homeo`
(challenge item 14) into smaller pieces, one of which (`HolomorphicOneForm`
on `RiemannSphere` is `Subsingleton`) is the deep input.

## What is honestly proven here

* `genus_RiemannSphere_of_subsingleton` — the **reduction**: any
  `Subsingleton (HolomorphicOneForm RiemannSphere)` instance immediately
  yields `JacobianChallenge.genus RiemannSphere = 0` via
  `Module.finrank_zero_of_subsingleton`. **No `sorry`, no axiom.**

* `Liouville_holomorphic_form_chartN_coeff` — **classical Liouville for the
  coefficient function in the north chart**: any `f : ℂ → ℂ` that is
  differentiable on all of `ℂ` and tends to `0` at infinity (along
  `Filter.cocompact ℂ`) is identically zero. This is the analytic core of
  the genus-zero argument — it is exactly the conclusion one would draw, in
  the north-chart coordinate, after recording that the form extends
  holomorphically to `∞`. **No `sorry`, no axiom.** It uses
  `Differentiable.eq_const_of_tendsto_cocompact` from
  `Mathlib/Analysis/Complex/Liouville.lean`.

## What is left as a `Prop`-only statement (open)

* `HolomorphicOneForm_RiemannSphere_subsingleton_statement : Prop` —
  the asserted (but here unproven) statement that
  `Subsingleton (HolomorphicOneForm RiemannSphere)`.

* `genus_RiemannSphere_statement : Prop` — the asserted (but here unproven)
  statement that `JacobianChallenge.genus RiemannSphere = 0`.

* `HolomorphicOneForm_RiemannSphere_subsingleton_implies_genus_zero` —
  the bridge in the form `[Subsingleton ...] → genus = 0`. This is
  `genus_RiemannSphere_of_subsingleton` repackaged.

## Why the `Subsingleton` claim is hard

A holomorphic 1-form `α` on `RiemannSphere`, restricted to the north chart,
is a holomorphic function `f : ℂ → ℂ` (the coefficient of `dz`). The
transition `chartS.symm ≫ₕ chartN` is `w ↦ w⁻¹` (and its inverse on the
overlap), so on the south chart the same form reads
`g(w) dw = -f(1/w) · w⁻² dw`, i.e. the south-chart coefficient is
`g(w) = -f(1/w) / w²`. Holomorphicity at `w = 0` (i.e. at `∞ ∈ S²`) forces
`f(1/w) = -w² g(w)`, so `f(z) → 0` as `z → ∞`. By Liouville
(`eq_const_of_tendsto_cocompact`), `f = 0` on all of `ℂ`, and continuity of
the section then forces `α = 0` on `∞` as well.

To run this argument inside the manifold framework one needs the
chart-coefficient extraction — i.e. `α x` evaluated through the
local trivialisation of `CotangentBundle 𝓘(ℂ) RiemannSphere` over
`chartN.source`. That trivialisation is supplied by
`cotangentBundleCore.localTrivAt`, but composing it with the analytic
regularity from `α.contMDiff_toFun` to extract a *single complex-valued*
holomorphic function on the chart image is a multi-file chase
(`MDifferentiableSection`, `inTangentCoordinates`, the precise form of the
cotangent transition `(compL ℂ ℂ ℂ ℂ).flip`). That chase is not done in
this file — it is the gating mathlib-glue input still owed.

## Reuse downstream

When the missing `Subsingleton` instance is supplied (in a follow-up file),
the bridge `genus_RiemannSphere_of_subsingleton` here gives
`genus RiemannSphere = 0` immediately, which is in turn the `←` direction
of `Basic.lean`'s `genus_eq_zero_iff_homeo`. The wiring of that bridge
into `Basic.lean` is intentionally left as a separate PR — see the
package's anti-cheat policy on edits to `Basic.lean`.
-/

open scoped ContDiff Manifold Topology

namespace JacobianChallenge

namespace RiemannSphere

/-! ### Reductions that are honestly proven -/

/-- **Reduction.** If the space of global holomorphic 1-forms on the Riemann
sphere is a subsingleton, then its `ℂ`-genus is `0`.

Proof: `JacobianChallenge.genus` is defined as
`Module.finrank ℂ (HolomorphicOneForm RiemannSphere)`, and
`Module.finrank_zero_of_subsingleton` says any `Subsingleton`-typed module
has `finrank = 0`. -/
theorem genus_RiemannSphere_of_subsingleton
    [Subsingleton (HolomorphicOneForm RiemannSphere)] :
    JacobianChallenge.genus RiemannSphere = 0 := by
  unfold JacobianChallenge.genus
  exact Module.finrank_zero_of_subsingleton

/-- The same reduction in `→` form, taking the `Subsingleton` hypothesis
explicitly rather than via instance search. -/
theorem genus_RiemannSphere_of_subsingleton'
    (h : Subsingleton (HolomorphicOneForm RiemannSphere)) :
    JacobianChallenge.genus RiemannSphere = 0 :=
  haveI := h
  genus_RiemannSphere_of_subsingleton

/-! ### Liouville on the north chart's coefficient function

This is the analytic core of the genus-zero argument. It does *not* depend
on the manifold framework — it is a purely complex-analytic fact about
holomorphic functions `ℂ → ℂ` that vanish at infinity.

The reason this lives here, rather than in `RiemannSphere.lean`, is that
the manifold extraction (turning a `HolomorphicOneForm RiemannSphere` into
the function `f : ℂ → ℂ` and verifying `f → 0` at infinity) is the
chart-coefficient chase that we have not yet written. This file
records the analytic conclusion that chase will reach. -/

/-- **Liouville for the north-chart coefficient.** Any function
`f : ℂ → ℂ` that is differentiable on all of `ℂ` and tends to `0` at
infinity (along `Filter.cocompact ℂ`, equivalently `Bornology.cobounded ℂ`
since `ℂ` is proper) is identically zero.

Proof: by `Differentiable.eq_const_of_tendsto_cocompact`, the function is
constant equal to `0`; then evaluate at any point. -/
theorem Liouville_holomorphic_form_chartN_coeff
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hb : Filter.Tendsto f (Filter.cocompact ℂ) (nhds 0)) :
    f = 0 := by
  have hconst := hf.eq_const_of_tendsto_cocompact hb
  -- `Function.const ℂ 0 = (0 : ℂ → ℂ)` via `funext`.
  ext z
  exact congrFun hconst z

/-- Pointwise corollary of `Liouville_holomorphic_form_chartN_coeff`. -/
theorem Liouville_holomorphic_form_chartN_coeff_apply
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hb : Filter.Tendsto f (Filter.cocompact ℂ) (nhds 0)) (z : ℂ) :
    f z = 0 := by
  have h := Liouville_holomorphic_form_chartN_coeff hf hb
  exact congrFun h z

/-! ### Statements still owed (open)

These are recorded as `Prop`-valued definitions, not as theorems. The
`_statement` suffix is a deliberate flag to downstream callers that the
content is not yet proven. -/

/-- **Open.** The statement that the space of global holomorphic 1-forms on
the Riemann sphere is a subsingleton.

This is the deep input. The proof sketch is recorded in this file's
docstring. To turn this `Prop` into a theorem one needs:

* a chart-coefficient extraction map sending a `HolomorphicOneForm
  RiemannSphere` to a holomorphic `f : ℂ → ℂ` on the north chart's image;
* a transformation lemma showing the south-chart coefficient is
  `g(w) = -f(1/w) / w²`;
* the observation that `g` holomorphic at `0` forces `f(z) → 0` as
  `z → ∞`;
* `Liouville_holomorphic_form_chartN_coeff` to conclude `f = 0`;
* a continuity/density argument extending `α = 0` from
  `chartN.source = {x ≠ ∞}` to all of `RiemannSphere`. -/
def HolomorphicOneForm_RiemannSphere_subsingleton_statement : Prop :=
  Subsingleton (HolomorphicOneForm RiemannSphere)

/-- **Open.** The statement that the (geometric) genus of the Riemann sphere
is `0`. Reduces to
`HolomorphicOneForm_RiemannSphere_subsingleton_statement` via
`genus_RiemannSphere_of_subsingleton`. -/
def genus_RiemannSphere_statement : Prop :=
  JacobianChallenge.genus RiemannSphere = 0

/-- The bridge from the open `Subsingleton` statement to the open `genus = 0`
statement. This is *honest content* — given the open input, it discharges
the open output via the proven reduction
`genus_RiemannSphere_of_subsingleton`. -/
theorem genus_RiemannSphere_statement_of_subsingleton_statement
    (h : HolomorphicOneForm_RiemannSphere_subsingleton_statement) :
    genus_RiemannSphere_statement :=
  genus_RiemannSphere_of_subsingleton' h

end RiemannSphere

end JacobianChallenge
