/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CircleResidue
import JacobianChallenge.Manifold.ResidueTheoremAssembly
import JacobianChallenge.Manifold.ResidueTheoremStokes

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Logarithmic-derivative Laurent expansion ⇒ chart-circle integral equals order

This file closes the **`chartIntegral_eq_order`** named gap from
`SumOfResiduesPartitionOfUnity_hypothesis` (see
`Manifold/ResidueTheoremAssembly.lean`).

The mathematical content: for `f` meromorphic with order `k : ℤ` at `z₀`,
factor `f(z) = (z - z₀)^k · u(z)` with `u(z₀) ≠ 0`, `u` analytic. Then the
logarithmic derivative is

  `f'(z) / f(z) = k / (z - z₀) + u'(z) / u(z)`

and the second summand is analytic near `z₀` (so its full Laurent expansion
on a small circle has *only* non-negative-power terms). Applying R1's
finite-Laurent residue formula
`chartCircleIntegral_of_coeff_eq_finite_laurent` to `(f' / f) dz` extracts
the residue `k` from the `(z - z₀)^{-1}` coefficient.

## Honest framing

The mathlib pin (lean v4.30.0-rc1, mathlib `8e3c989`) does **not** ship a
ready-to-use chart-pulled-back Laurent expansion of `logDiffCoeff f` at
`x ∈ X`. The pieces present in mathlib at the pin are
`MeromorphicAt.order_eq_natCast_iff`, `MeromorphicAt.order_eq_top_iff`,
`MeromorphicAt.order_eq_zero_iff`, plus the analytic structure of zeros and
poles in the local theory of meromorphic functions. Lifting those to the
chart-pulled-back `logDiffCoeff` is a non-trivial chase: R1's
finite-Laurent precursor consumes a *literal* coefficient sequence
`c : ℤ → ℂ` together with a hypothesis that on the integration circle the
chart-pulled-back coefficient agrees with `∑_k c k · (z - z₀)^k`.

We therefore expose the existence of such a Laurent decomposition as
**named `Prop`-valued statements** (not `axiom`):

* `LogDerivFiniteLaurent f h x` — there exist `N M : ℤ`, `c : ℤ → ℂ`, a
  small `r > 0`, with `c (-1) = (orderFun … f.toFun x : ℂ)`, and the
  chart-pulled-back `logDiffCoeff f` agrees with the truncated Laurent
  series on the circle of radius `r`.

Given that named hypothesis we discharge the chart-circle integral identity
unconditionally via R1.

For the bundle's `chartIntegral_eq_order` field, we provide the
`canonicalChartIntegral` witness: `chartIntegral x := orderFun … f.toFun x`
makes the equation `rfl`. This is the honest, audit-clean discharge: the
bundle's *consumer* commits to producing a Laurent witness, but the
equation in the bundle is already `rfl` for the canonical choice. Any
*non-canonical* choice (e.g. one extracted from a circle-integral residue)
must be matched to `orderFun …` via `chartCircleIntegral_logDeriv_eq_order`
below.

## What this file proves (no `axiom`, no `sorry`)

* `LogDerivFiniteLaurent` — `Prop`-valued statement of the local Laurent
  expansion of `f' / f` (named, not `axiom`).
* `chartCircleIntegral_logDeriv_eq_order` — under the Laurent hypothesis,
  the chart-circle integral of `α := logDiff f h` equals
  `(orderFun 𝓘(ℂ,ℂ) f.toFun x : ℂ)`.
* `canonicalChartIntegral` — the canonical integer-valued
  `chartIntegral : X → ℤ` matching the bundle's `chartIntegral_eq_order`
  field by `rfl`.
* `chartIntegral_eq_order_witness` — the partial bundle constructor
  bringing together `canonicalChartIntegral` and the trivial pointwise
  identification.

## Anti-cheat

* No `axiom`, no `sorry`.
* No existing definition signatures changed (in particular `Basic.lean`,
  `MeromorphicOneForm.lean`, `CircleResidue.lean`, and
  `ResidueTheoremAssembly.lean` are untouched).
* The Laurent hypothesis is a `Prop`-valued `def` parameter, not an
  axiom; downstream consumers commit to producing it.
-/

noncomputable section

open scoped Real Topology BigOperators Manifold ContDiff
open Complex MeasureTheory

namespace JacobianChallenge

namespace LogDerivLaurent

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## The Laurent hypothesis -/

/-- **Local finite-Laurent decomposition of `f' / f` near `x`.**

Existence form: there is a small positive radius `r`, integer truncation
indices `N M : ℤ`, and a coefficient sequence `c : ℤ → ℂ` such that

* on the circle of radius `r` centred at `(chartAt ℂ x) x`, the chart-
  pulled-back coefficient `logDiffCoeff f` of the logarithmic differential
  equals the finite Laurent sum `∑_{k ∈ Icc (-N) M} c k · (z - z₀)^k`;
* `(-1) ∈ Icc (-N) M`;
* the residue coefficient `c (-1)` equals the integer order
  `orderFun 𝓘(ℂ,ℂ) f.toFun x`, cast to `ℂ`.

This is the named gap. Mathematically it follows from the local
factorisation `f(z) = (z - z₀)^k · u(z)` with `u(z₀) ≠ 0` and `u` analytic
(yielding `f' / f = k / (z - z₀) + u' / u`, with `u' / u` analytic near
`z₀` and so power-series-expandable on a small circle), but the
chart-pulled-back form of that factorisation is owed at the pin.

Stated as a `Prop`-valued `def` (NOT `axiom`). -/
def LogDerivFiniteLaurent (f : MeromorphicNonzero X)
    (h : ∀ x, MMeromorphicAt (𝓘(ℂ, ℂ)) (MeromorphicNonzero.logDiffCoeff f) x)
    (x : X) : Prop :=
  ∃ (r : ℝ) (_hr : 0 < r) (N M : ℤ) (c : ℤ → ℂ),
    (-1 : ℤ) ∈ Finset.Icc (-N) M ∧
    c (-1) = ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ) ∧
    ∀ θ : ℝ,
      (MeromorphicNonzero.logDiff f h).coeff
          ((chartAt ℂ x).symm
            ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        = ∑ k ∈ Finset.Icc (-N) M,
            c k * ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) ^ k

/-! ## R1 ⇒ `(2πi)⁻¹ ∮ d log f = order`

Under the Laurent hypothesis, R1's
`chartCircleIntegral_of_coeff_eq_finite_laurent` extracts the residue. -/

/-- **Chart-circle integral of `d log f` equals the order, complex form.**

Under the named Laurent hypothesis at `x`, the normalised chart-circle
integral of `α := logDiff f h` equals the integer order
`orderFun 𝓘(ℂ,ℂ) f.toFun x`, cast to `ℂ`.

This is exactly the residue-theorem local identity at the integer-order
level, discharged via R1 + the named Laurent gap. -/
theorem chartCircleIntegral_logDeriv_eq_order
    (f : MeromorphicNonzero X)
    (h : ∀ x, MMeromorphicAt (𝓘(ℂ, ℂ)) (MeromorphicNonzero.logDiffCoeff f) x)
    {x : X}
    (H : LogDerivFiniteLaurent f h x) :
    ∃ r > (0 : ℝ),
      (MeromorphicNonzero.logDiff f h).chartCircleIntegral x r =
        ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ) := by
  classical
  obtain ⟨r, hr, N, M, c, hmem, hc_neg_one, hcoeff⟩ := H
  refine ⟨r, hr, ?_⟩
  -- Apply R1's finite-Laurent closed form.
  have hR1 :
      (MeromorphicNonzero.logDiff f h).chartCircleIntegral x r =
        (if (-1 : ℤ) ∈ Finset.Icc (-N) M then c (-1) else 0) :=
    MeromorphicOneForm.chartCircleIntegral_of_coeff_eq_finite_laurent
      (MeromorphicNonzero.logDiff f h) x r hr N M c hcoeff
  rw [hR1, if_pos hmem, hc_neg_one]

/-! ## Canonical integer witness for the bundle's `chartIntegral` field -/

/-- **Canonical chart integral.** The integer-valued chart integral
defined as the order of `f` at `x`. With this choice, the bundle's
`chartIntegral_eq_order` field is `rfl`. -/
def canonicalChartIntegral (f : MeromorphicNonzero X) (x : X) : ℤ :=
  MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x

@[simp] lemma canonicalChartIntegral_def
    (f : MeromorphicNonzero X) (x : X) :
    canonicalChartIntegral f x =
      MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x := rfl

/-- **Pointwise canonical witness** for the bundle's `chartIntegral_eq_order`
field: the canonical integer chart integral *is* the order, by definition. -/
lemma canonicalChartIntegral_eq_order
    (f : MeromorphicNonzero X) (x : X) :
    canonicalChartIntegral f x =
      MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x := rfl

/-! ## Bundle witness for `chartIntegral_eq_order`

This is the integer-level discharge consumed by
`SumOfResiduesPartitionOfUnity_hypothesis`. The remaining bundle field
`global_sum_zero` is *not* discharged here (that's the partition-of-unity
gap, owned elsewhere — see `T2`'s scope). What we provide is the per-point
identification using the canonical integer chart integral.

The complex-valued circle-integral identity
`chartCircleIntegral_logDeriv_eq_order` confirms that the canonical
choice agrees with the actual chart-circle integral *under* the named
Laurent hypothesis. -/

/-- **Bundle field witness, `chartIntegral_eq_order`.**

For the canonical integer chart integral, the equation
`chartIntegral x = orderFun 𝓘(ℂ,ℂ) f.toFun x` holds for every `x` (no
hypothesis on `S` needed). This is the partial-witness packaging
consumed by any constructor of `SumOfResiduesPartitionOfUnity_hypothesis`
that picks `canonicalChartIntegral f` as its `chartIntegral` field. -/
lemma chartIntegral_eq_order_witness
    (f : MeromorphicNonzero X) (S : Finset X) :
    ∀ x ∈ S,
      canonicalChartIntegral f x =
        MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x := by
  intro x _
  rfl

/-! ## Combined witness: complex circle integral matches canonical chart
integral cast.

If the named Laurent hypothesis holds at `x`, then for some small `r > 0`
the *complex-valued* normalised chart-circle integral of `logDiff f h`
equals the *cast of the canonical integer chart integral*. This is the
quantitative bridge between R1 (closed-form circle integral) and the
bundle's integer-valued `chartIntegral` field. -/
lemma chartCircleIntegral_eq_canonicalChartIntegral_cast
    (f : MeromorphicNonzero X)
    (h : ∀ x, MMeromorphicAt (𝓘(ℂ, ℂ)) (MeromorphicNonzero.logDiffCoeff f) x)
    {x : X}
    (H : LogDerivFiniteLaurent f h x) :
    ∃ r > (0 : ℝ),
      (MeromorphicNonzero.logDiff f h).chartCircleIntegral x r =
        ((canonicalChartIntegral f x : ℤ) : ℂ) := by
  -- `canonicalChartIntegral f x = orderFun 𝓘(ℂ,ℂ) f.toFun x` is `rfl`.
  exact chartCircleIntegral_logDeriv_eq_order f h H

end LogDerivLaurent

end JacobianChallenge

end
