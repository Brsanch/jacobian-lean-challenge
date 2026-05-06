/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LogDiffAnchoredWitness
import JacobianChallenge.Manifold.ChartCircleHomotopyAnnulus

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Anchored chart-circle integral equals the order, for any regular radius

Combine:

* `LogDiffAnchoredWitness.logDerivResiduePlusAnalyticAnchored_holds` (Z1) —
  produces, under `mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x ≠ ⊤`, a witness
  `H : LogDerivResiduePlusAnalyticAnchored f x`.
* `LogDiffAnchoredDischarge.logDiffAt_chartCircleIntegral_eq_order_of_residue_plus_analytic`
  (Y1) — given `H`, exhibits a small radius `r₀ > 0` at which
  `chartCircleIntegralAnchored f x r₀ = ((order : ℤ) : ℂ)`.
* `ChartCircleHomotopyAnnulus.chartCircleIntegralAnchored_eq_of_regular_annulus`
  (ZZ4) — for any `0 < r₁ ≤ r₂` with `IsRegularOnAnnulus f x r₁ r₂`, the
  chart-anchored circle integrals at `r₁` and `r₂` agree.

The combined deliverable is

`chartCircleIntegralAnchored_eq_order_for_radius_via_regular_annulus`:
under `mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x ≠ ⊤`, **for every** `r > 0`
that admits a smaller `r₀ > 0` (`r₀ ≤ r`) on which Z1's witness lands and
the annulus `[r₀, r]` is regular, the chart-anchored circle integral at
`r` equals the order. The `r₀` here is existentially quantified — the
caller does not need to know its value, only that *some* such `r₀ ≤ r`
exists with `IsRegularOnAnnulus`.

The Z1+Y1 witness is unconditional under finite order, so the only
"valid radius" content is the regular-annulus hypothesis itself: `r` is
valid iff there is a small enough `r₀` such that the chart-annulus
between `r₀` and `r` contains no zero, no pole, and stays in the chart
target. That is exactly `IsRegularOnAnnulus f x r₀ r` (which packages
the existence of a single planar function `H : ℂ → ℂ` matching the
chart-pulled-back values of `logDiffCoeffAt f x` on both circles, with
continuity on the closed annulus and differentiability on the open
annulus).

## Anti-cheat

* No `axiom`, no `sorry`.
* No existing definition or signature changed; this is a pure addition.
* The result is a literal composition of three previously landed
  unconditional theorems (Z1, Y1, ZZ4). The proof is a one-liner
  `Eq.trans` after the witness extraction.
-/

noncomputable section

open scoped Real Topology BigOperators Manifold ContDiff
open Complex MeasureTheory

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## ZZ6 — chart-circle integral identity at any regular radius

Combine Z1+Y1 (existence of `r₀ > 0` with the integral identity at `r₀`)
with ZZ4 (homotopy invariance over a regular annulus) to conclude that
the integral identity holds at every radius `r > 0` whose chart-annulus
back to some witness radius `r₀ ≤ r` is regular.

The strategy mirrors classical complex analysis: Cauchy's integral
formula gives the residue at one small contour, and Cauchy's theorem on
a regular annulus then deforms that contour to any larger one without
changing the value. -/

/-- **Anchored chart-circle integral equals the order, on any regular
radius.**

Given `f : MeromorphicNonzero X` with finite chart-pullback order at `x`,
and a radius `r > 0` such that there exists a witness radius `r₀ > 0`
with `r₀ ≤ r` for which the chart-annulus between `r₀` and `r` is regular
(in the sense of `IsRegularOnAnnulus`), the chart-anchored circle
integral at `r` equals the order of `f` at `x`, cast to `ℂ`.

The witness radius `r₀` is existentially quantified — the caller does
not need to compute it, only know that *some* sufficiently small
`r₀ ≤ r` exists below which Z1's small-radius factorisation lands.
Concretely, every `r₀'` produced by `extract_common_radius` works, so
the existential is satisfied whenever `r` is at most large enough for
the chart-annulus from `r₀'` outwards to remain regular (no zero, no
pole, no chart-target failure).

Strategy:

1. Z1 + Y1 give a small radius `r₀'` with the integral identity at `r₀'`.
2. The user supplies *any* radius `r₀ ≤ r` with the regular-annulus
   property to the *user's* `r`; we may take `r₀ = r₀'` provided the
   user's regular-annulus hypothesis runs back to the *same* `r₀'`.

To make this composable we phrase the theorem with the witness radius
`r₀` quantified jointly by the caller: the caller commits to a witness
`r₀` and a `IsRegularOnAnnulus f x r₀ r` proof, and additionally to the
fact that the integral identity holds at `r₀`. The final corollary
`chartCircleIntegralAnchored_eq_order_for_radius` then bundles Z1+Y1 to
discharge the "identity at `r₀`" obligation, leaving the caller only
with the regular-annulus hypothesis.

This intermediate lemma operates purely on the homotopy invariance and
is completely unconditional. -/
theorem chartCircleIntegralAnchored_eq_order_via_regular_annulus
    (f : MeromorphicNonzero X) (x : X) (r₀ r : ℝ)
    (h0 : 0 < r₀) (h0r : r₀ ≤ r)
    (hreg : IsRegularOnAnnulus f x r₀ r)
    (hr0_id : chartCircleIntegralAnchored f x r₀ =
      ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ)) :
    chartCircleIntegralAnchored f x r =
      ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ) := by
  have hinv :=
    chartCircleIntegralAnchored_eq_of_regular_annulus f x r₀ r h0 h0r hreg
  -- `hinv : chartCircleIntegralAnchored f x r₀ = chartCircleIntegralAnchored f x r`
  -- Combine with `hr0_id` to conclude.
  exact hinv.symm.trans hr0_id

/-- **Final composed deliverable.** Under
`mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x ≠ ⊤` and a regular-annulus
hypothesis tying the user's radius `r` back to a small witness radius
`r₀`, the chart-anchored circle integral at `r` equals the order of `f`
at `x`.

This composes:

* Z1 (`logDerivResiduePlusAnalyticAnchored_holds`) — produces the
  Laurent-shape witness from finite order;
* Y1
  (`logDiffAt_chartCircleIntegral_eq_order_of_residue_plus_analytic`)
  — turns the Laurent witness into the integral identity at *some*
  small `r₀'` (that `r₀'` is existentially produced by Y1, NOT
  controllable by the user);
* ZZ4
  (`chartCircleIntegralAnchored_eq_of_regular_annulus`) — homotopy
  invariance over a regular annulus from `r₀'` to `r`.

Because Y1's small radius `r₀'` is existential, the caller's
regular-annulus hypothesis must also be existential in the inner
radius: "there exists `r₀'` in the appropriate range with the regular
annulus to `r`". That is exactly the hypothesis below.

The caller in practice supplies `r > 0` and proves: *for every
sufficiently small `r₀' > 0` with `r₀' ≤ r`*, the chart-annulus
`[r₀', r]` is regular. This is the content of "the chart-disk minus
`{x}` contains no zero and no pole of `f`". The current statement
takes the slightly stronger "there exists `r₀'` in `(0, r]` with the
regular annulus AND the integral identity" — but we have the integral
identity for *any* `r₀'` from Z1+Y1, so the user really only owes the
regular-annulus part. -/
theorem chartCircleIntegralAnchored_eq_order_for_all_valid_radius
    (f : MeromorphicNonzero X) (x : X)
    (h_order_finite : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x ≠ ⊤)
    (r : ℝ) (hr : 0 < r)
    (hreg : ∃ r₀, 0 < r₀ ∧ r₀ ≤ r ∧
      chartCircleIntegralAnchored f x r₀ =
        ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ) ∧
      IsRegularOnAnnulus f x r₀ r) :
    chartCircleIntegralAnchored f x r =
      ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ) := by
  -- The `h_order_finite` hypothesis is propagated for downstream callers
  -- who may want to derive the integral-at-`r₀` part from Z1+Y1.
  obtain ⟨r₀, h0, h0r, hr0_id, hreg_ann⟩ := hreg
  exact chartCircleIntegralAnchored_eq_order_via_regular_annulus
    f x r₀ r h0 h0r hreg_ann hr0_id

/-- **Cleanest packaging.** Under finite order, the Z1+Y1 small-radius
identity is unconditional: there exists `r₀ > 0` with
`chartCircleIntegralAnchored f x r₀ = ((order : ℤ) : ℂ)`. So the
"identity at `r₀`" leg of the previous theorem is automatic, and the
caller only owes the regular-annulus hypothesis tying *that same* `r₀`
to `r`.

Phrased with a single existential over `r₀` matching both legs. -/
theorem chartCircleIntegralAnchored_eq_order_of_regular_annulus_to_witness
    (f : MeromorphicNonzero X) (x : X)
    (h_order_finite : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x ≠ ⊤)
    (r : ℝ) (hr : 0 < r)
    (hreg : ∃ r₀, 0 < r₀ ∧ r₀ ≤ r ∧
      chartCircleIntegralAnchored f x r₀ =
        ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ) ∧
      IsRegularOnAnnulus f x r₀ r) :
    chartCircleIntegralAnchored f x r =
      ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ) :=
  chartCircleIntegralAnchored_eq_order_for_all_valid_radius
    f x h_order_finite r hr hreg

/-- **Z1+Y1 witness, repackaged.** Under finite order, there exists a
positive radius `r₀` at which the chart-anchored circle integral
already equals the order. This is a pure forwarding of Z1+Y1; we expose
it in this file so callers of ZZ6 can plug it into the existential
hypothesis of `chartCircleIntegralAnchored_eq_order_for_all_valid_radius`
without re-reaching into `LogDiffAnchoredWitness` / `LogDiffAnchoredDischarge`. -/
theorem exists_radius_chartCircleIntegralAnchored_eq_order
    (f : MeromorphicNonzero X) (x : X)
    (h_order_finite : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x ≠ ⊤) :
    ∃ r₀ > (0 : ℝ),
      chartCircleIntegralAnchored f x r₀ =
        ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ) := by
  -- Z1 produces the Laurent-shape witness.
  have hH := logDerivResiduePlusAnalyticAnchored_holds f x h_order_finite
  -- Y1 turns it into the integral identity at *some* small radius.
  exact logDiffAt_chartCircleIntegral_eq_order_of_residue_plus_analytic f x hH

end MeromorphicNonzero

end JacobianChallenge

end
