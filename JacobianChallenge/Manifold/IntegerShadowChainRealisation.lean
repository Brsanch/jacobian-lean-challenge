/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.IntegerShadowStokes
import JacobianChallenge.Manifold.ChartIntegralFibreBalanceWiring
import JacobianChallenge.Divisor.PrincipalDivisor

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Realising `IntegerShadowChainComplex` from `MeromorphicNonzero X` (ZZ72 chip)

This file sits **strictly above** ZZ71 (`IntegerShadowStokes.lean`) and
ZZ70 (`ChartIntegralFibreBalanceWiring.lean`). It addresses the question:

> Does `IntegerShadowChainComplex` (ZZ71) require *actual triangulation
> data* (Faces, oriented Edges, edge-pair maps), or is it abstract enough
> that a **chart-cover with pairwise-overlap orientations** suffices?

## Honest answer

**ZZ71's abstraction is genuinely simplicial / cellular, not chart-shaped.**

The structure exposes two finite types `Face`, `Edge` and a signed
incidence `Face → Edge → ℤ` together with the per-edge cancellation
hypothesis

```
∀ e : Edge, (∑ F : Face, incidence F e) = 0.
```

A chart cover of a compact connected 2-manifold gives **open** sets with
pairwise (and triple, quadruple, …) overlaps, not a cellular
decomposition where each interior 1-cell is shared by **exactly two**
2-cells with opposite induced orientations. Triple chart intersections
are generic, the overlap regions are 2-dimensional, and the chart-cover
nerve is a simplicial complex of dimension ≥ 2 in each chart, not the
1-skeleton of a 2-cell decomposition. So one cannot read `Edge` and the
per-edge cancellation off a chart cover by dimension count alone.

Consequently realising `IntegerShadowChainComplex` from
`f : MeromorphicNonzero X` requires **a finite triangulation (or CW
decomposition) of `X` minus the support of `f`**, plus the standard
combinatorial fact that on a closed 2-manifold each interior 1-cell is
shared by exactly two 2-cells with opposite induced orientations. Both
are classical (Radó 1925 / Cairns 1934 for the existence; standard for
the cancellation) but **neither is named in mathlib at the pinned commit
`8e3c989104daaa052921bf43de9eef0e1ac9fbf5`** (cf. the closing docstring
of `IntegerShadowStokes.lean`).

## What this file provides (output (2) of the ZZ72 brief)

A **named hypothesis bundle**
`IntegerShadowChainRealisationHypothesis f` packaging exactly the
ZZ71-shaped data needed for a fixed `f : MeromorphicNonzero X`:

1. an `IntegerShadowChainComplex` `C`;
2. a `ChartIntegralRealisation` of the divisor data
   `((principalDivisorMap f).supportFinset, (principalDivisorMap f : X → ℤ))`
   by `C`.

From this bundle the file proves, **unconditionally and without
`sorry`/`axiom`**:

* `chartIntegralFibreBalanceOn_of_realisation` —
  `chartIntegralFibreBalanceOn ((principalDivisorMap f).supportFinset)
                               (principalDivisorMap f : X → ℤ)`
  follows directly from any witness of the hypothesis bundle, by
  composing ZZ71's `chartIntegralFibreBalanceOn_of_integerShadow` with
  the bundle's realisation field.

* `chartIntegralFibreBalanceOn_holds_of_chartCoverFacePair` — the
  global/quantified form: if every `f` admits such a realisation, then
  `chartIntegralFibreBalanceOn` holds for every `f`.

The hypothesis bundle is **strictly weaker** than ZZ71 in scope (it is
ZZ71's data restricted to the divisor of `f`), but it is **strictly
stronger** than just naming the gap, because it (i) commits to the
chain-complex data shape, (ii) commits to the divisor-sided
chart-integral function, and (iii) hands the consumer a
sorry-free reduction to `chartIntegralFibreBalanceOn`.

## Honest framing

* **No `axiom`, no `sorry`. No signature change anywhere else.** The
  reduction below is genuine wiring: it composes ZZ71's
  `chartIntegralFibreBalanceOn_of_integerShadow` with the bundle's
  data field — every step type-checks against existing repo
  declarations.
* **The hypothesis bundle is the ZZ72 chip itself**, not a stub. It
  exposes precisely the missing-mathlib content: a triangulation /
  cellular decomposition of `X ∖ supp f` whose 2-cells carry the right
  signed incidences. The author of ZZ71 names this gap explicitly in
  items (1), (2) of that file's closing docstring; this file simply
  packages those items into a single hypothesis at the
  `MeromorphicNonzero X` level so a future agent who closes the
  triangulation gap can plug it in here without touching ZZ71 or
  downstream wiring.
* **What this file does NOT do.** It does not produce a triangulation
  of an arbitrary compact connected complex 1-manifold from mathlib;
  the corresponding mathlib content (Radó/Cairns) is not present at
  the pin. It also does not weaken the hypothesis to a chart-cover
  bundle, because — as analysed above — chart covers are insufficient
  to realise the ZZ71 face/edge data.

## Concrete missing-mathlib content (reaffirming ZZ71)

To unconditionally produce a `IntegerShadowChainRealisationHypothesis f`
one needs:

1. **Triangulation of a compact topological 2-manifold.**
   No theorem of the form *every compact Hausdorff topological
   2-manifold admits a finite triangulation* is named in mathlib at
   the pin (closest: `Mathlib.Topology.SimplicialSet.*`,
   `Mathlib.AlgebraicTopology.*`, neither delivers this).

2. **Edge-pair cancellation on a closed surface.**
   On a triangulated closed (no-boundary) 2-manifold each interior
   edge is shared by exactly two 2-cells with **opposite** induced
   orientations. Not named in mathlib at the pin in either
   `SimplicialComplex` or `SimplicialSet`.

3. **Chart-disk realisation of singular faces** — already a bundle
   field on `GlobalResidueSum_hypothesis` (`chartIntegral_eq_order`),
   wiring-only once (1), (2) land.

4. **Closed-form vanishing on regular faces** — already in this repo
   (`StokesDiskClosedForm.chartCircleIntegralOfFun_eq_zero_of_diffContOnCl`),
   wiring-only once (1), (2) land.

Items (1), (2) are the genuine wall; (3), (4) are
post-triangulation wiring already prepared by upstream files. -/

noncomputable section

open scoped BigOperators Manifold ContDiff

namespace JacobianChallenge

namespace IntegerShadowChainRealisation

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## The hypothesis bundle -/

/-- **Integer-shadow chain-complex realisation hypothesis for `f`.**

A bundle of the ZZ71-shaped data tied to a fixed
`f : MeromorphicNonzero X`:

* an `IntegerShadowChainComplex` `chainComplex`;
* a `ChartIntegralRealisation` of
  `((principalDivisorMap f).supportFinset, (principalDivisorMap f))`
  by that chain complex.

The chain complex's `edge_cancellation` field is the *named* gap whose
discharge requires a finite triangulation of `X ∖ supp f` together with
the closed-surface edge-pair cancellation lemma — neither of which is
in mathlib at the pin (see file-level docstring).

This packages exactly what a future agent producing a triangulation
must hand off to consume the rest of the residue-theorem stack
unconditionally. -/
structure IntegerShadowChainRealisationHypothesis
    (f : MeromorphicNonzero X) where
  /-- The combinatorial integer-shadow chain complex. -/
  chainComplex : IntegerShadowStokes.IntegerShadowChainComplex
  /-- Realisation of the divisor data of `f` by `chainComplex`. -/
  realisation :
    IntegerShadowStokes.ChartIntegralRealisation
      (principalDivisorMap f).supportFinset
      ((principalDivisorMap f : X → ℤ))
      chainComplex

/-! ## Per-`f` reduction -/

/-- **Per-`f` reduction.** A realisation witness implies the
chart-integer fibre balance on the divisor of `f`.

This is a one-step composition with ZZ71's
`chartIntegralFibreBalanceOn_of_integerShadow` — no new mathematical
content, just routing of the bundle's `realisation` field to that
reduction. -/
theorem chartIntegralFibreBalanceOn_of_realisation
    [DecidableEq X]
    {f : MeromorphicNonzero X}
    (R : IntegerShadowChainRealisationHypothesis f) :
    JacobianChallenge.GlobalResidueSum.chartIntegralFibreBalanceOn
      (principalDivisorMap f).supportFinset
      ((principalDivisorMap f : X → ℤ)) :=
  IntegerShadowStokes.chartIntegralFibreBalanceOn_of_integerShadow
    R.realisation

/-! ## Global / quantified form -/

/-- **Global form (acceptable output (2) of the ZZ72 brief).**

If every `f : MeromorphicNonzero X` admits an
`IntegerShadowChainRealisationHypothesis`, then
`chartIntegralFibreBalanceOn` holds on the divisor of every `f`.

This is the consumer-facing entry point: a future agent producing a
finite triangulation of `X` will discharge the hypothesis on the left
and obtain `chartIntegralFibreBalanceOn` on the right uniformly in `f`,
which then plugs into ZZ70's
`chartIntegralFibreBalance_iff_principalDegree_zero` and the rest of
the residue-theorem stack. -/
theorem chartIntegralFibreBalanceOn_holds_of_chartCoverFacePair
    [DecidableEq X]
    (h : ∀ f : MeromorphicNonzero X,
        IntegerShadowChainRealisationHypothesis f) :
    ∀ f : MeromorphicNonzero X,
      JacobianChallenge.GlobalResidueSum.chartIntegralFibreBalanceOn
        (principalDivisorMap f).supportFinset
        ((principalDivisorMap f : X → ℤ)) := by
  intro f
  exact chartIntegralFibreBalanceOn_of_realisation (h f)

end IntegerShadowChainRealisation

end JacobianChallenge

end
