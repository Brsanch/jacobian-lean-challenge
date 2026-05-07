/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.GlobalChainBoundaryDischarge
import JacobianChallenge.Manifold.ZeroCountEqPoleCount
import JacobianChallenge.Manifold.ResidueViaTopologicalDegree
import JacobianChallenge.Manifold.TopologicalDegree
import JacobianChallenge.Divisor
import JacobianChallenge.Divisor.PrincipalDivisor

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Wiring `chartIntegralFibreBalanceOn` directly to the topological-degree bundle (ZZ73 chip)

This file sits parallel to ZZ72's `IntegerShadowChainRealisation.lean`.
ZZ72 reduces `chartIntegralFibreBalanceOn ((principalDivisorMap f).supportFinset)
(principalDivisorMap f)` to a triangulation/cellular bundle
(`IntegerShadowChainRealisationHypothesis f`) — which owes Radó-style
triangulation of `X` and closed-surface edge-pair cancellation, neither
in mathlib at the pin.

This file routes the **same** `chartIntegralFibreBalanceOn` proposition
through the **topological-degree bundle**
`ResidueViaTopologicalDegree.TopologicalDegreeFibreBalance_hypothesis f`
instead. That bundle's single named field is

  `zeroCount f = poleCount f`,

which is the multiplicity-weighted preimage equality at the two regular
values `0, ∞ ∈ S²` for the pole-extension `f̃ : X → RiemannSphere`.

## Honest assessment of the route shortening

**The topological-degree route is `Iff`-equivalent to ZZ72's route, not
strictly shorter at the gap level.** Both reduce to the same `Prop`-class
(unfolds to `(principalDivisorMap f).degree = 0`):

* ZZ72's `IntegerShadowChainRealisationHypothesis f` discharges the gap
  via a finite cellular decomposition + edge-pair cancellation
  (Radó/Cairns); the integer chain-complex realisation is a
  combinatorial route to the integer equality.
* This file's reduction targets `TopologicalDegreeFibreBalance_hypothesis
  f`, whose single field `zeroCount f = poleCount f` is `Iff`-equivalent
  to `(principalDivisorMap f).degree = 0` (see
  `ZeroCountEqPoleCount.tdfb_iff_principalDegree_zero`, already proven
  in repo).

So both bundles' gaps are mutually `Iff`-equivalent, and per
`ZeroCountEqPoleCount.lean`'s closing docstring, the topological-degree
bundle is *named* — not a reduction to a strictly smaller `Prop`.

What this file genuinely buys:

* A **direct** per-`f` `Iff` between the chart-integer-side raw-data
  fibre balance and the topological-degree bundle, without going
  through ZZ70's bundle-level `chartIntegralFibreBalance`. Useful for a
  consumer who has the raw `(supportFinset, principalDivisorMap f)`
  data in hand from a chart-side computation and wants to feed it to
  whichever bundle (Route B / topological-degree) a future agent
  closes first.
* A second discharge path for `chartIntegralFibreBalanceOn` that
  routes through topological-degree-counting infrastructure
  (covering-space side) rather than triangulation-of-X infrastructure
  (cellular side). At the pin, **neither route's gap is closed in
  mathlib**, but the two gaps are mathematical siblings: any future
  mathlib infrastructure landing one will likely land the other.

## What this file ships

* `chartIntegralFibreBalanceOn_principalDivisor_iff_tdfb` — per-`f`
  `Iff` between the raw-data fibre balance on the divisor of `f` and
  `TopologicalDegreeFibreBalance_hypothesis f`.
* `chartIntegralFibreBalanceOn_of_topologicalDegree` — forward
  direction, the consumer-facing one-step composition.
* `forall_chartIntegralFibreBalanceOn_principalDivisor_iff_residueTheorem`
  — global form: `∀ f, chartIntegralFibreBalanceOn (supp f)
  (principalDivisorMap f) ↔ ResidueTheorem X`. Records that closing
  the raw-data fibre balance for every `f` is the same `Prop` as the
  residue theorem.

No `axiom`, no `sorry`. No signature change to existing definitions.
The proofs are genuine wiring: each Iff uses
`degree_eq_sum_of_supportFinset_subset` to translate between the
sum-over-supportFinset and the divisor-degree, then applies an existing
proven `Iff` from `ZeroCountEqPoleCount.lean` and
`GlobalChainBoundaryDischarge.lean`.
-/

noncomputable section

open scoped BigOperators Manifold ContDiff

namespace JacobianChallenge

namespace FibreBalanceTopologicalDegree

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Per-`f` Iff between raw-data fibre balance and the topological-degree bundle -/

/-- **Sum-over-supportFinset of `principalDivisorMap f` equals the
divisor degree.** Trivial specialisation of
`Div.degree_eq_sum_of_supportFinset_subset` to the support itself. -/
lemma sum_principalDivisor_supportFinset_eq_degree
    (f : MeromorphicNonzero X) :
    ∑ x ∈ (principalDivisorMap f).supportFinset,
        ((principalDivisorMap f : X → ℤ) x)
      = (principalDivisorMap f).degree :=
  (JacobianChallenge.Div.degree_eq_sum_of_supportFinset_subset
      (D := principalDivisorMap f)
      (S := (principalDivisorMap f).supportFinset)
      (Finset.Subset.refl _)).symm

/-- **Per-`f` cross-equivalence (proven, genuine wiring).**

The raw-data chart-integer fibre balance on `f`'s divisor support and
the topological-degree bundle `TopologicalDegreeFibreBalance_hypothesis
f` are `Iff`-equivalent.

The proof composes:

* `GlobalResidueSum.chartIntegralFibreBalanceOn_iff_sum_eq_zero` (raw
  data fibre balance ↔ sum over `supportFinset` is zero);
* `sum_principalDivisor_supportFinset_eq_degree` (rewrites the sum to
  `(principalDivisorMap f).degree`);
* `ResidueViaTopologicalDegree.tdfb_iff_principalDegree_zero` (degree
  zero ↔ `TopologicalDegreeFibreBalance_hypothesis`).

This is *not* `Iff.rfl`: the rewrite from sum-over-supportFinset to
divisor-degree is real proof content via
`Div.degree_eq_sum_of_supportFinset_subset`. -/
theorem chartIntegralFibreBalanceOn_principalDivisor_iff_tdfb
    [DecidableEq X]
    (f : MeromorphicNonzero X) :
    JacobianChallenge.GlobalResidueSum.chartIntegralFibreBalanceOn
        (principalDivisorMap f).supportFinset
        ((principalDivisorMap f : X → ℤ))
      ↔ JacobianChallenge.ResidueViaTopologicalDegree.TopologicalDegreeFibreBalance_hypothesis f := by
  classical
  -- Step 1: raw-data fibre balance ↔ ∑ = 0.
  have h1 :
      JacobianChallenge.GlobalResidueSum.chartIntegralFibreBalanceOn
          (principalDivisorMap f).supportFinset
          ((principalDivisorMap f : X → ℤ))
        ↔ ∑ x ∈ (principalDivisorMap f).supportFinset,
            ((principalDivisorMap f : X → ℤ) x) = 0 :=
    JacobianChallenge.GlobalResidueSum.chartIntegralFibreBalanceOn_iff_sum_eq_zero
      (principalDivisorMap f).supportFinset
      ((principalDivisorMap f : X → ℤ))
  -- Step 2: ∑ = 0 ↔ degree = 0 (via the supportFinset-sum rewrite).
  have hsum := sum_principalDivisor_supportFinset_eq_degree f
  have h2 :
      ∑ x ∈ (principalDivisorMap f).supportFinset,
          ((principalDivisorMap f : X → ℤ) x) = 0
        ↔ (principalDivisorMap f).degree = 0 := by
    rw [hsum]
  -- Step 3: degree = 0 ↔ TopologicalDegreeFibreBalance_hypothesis f.
  have h3 :
      (principalDivisorMap f).degree = 0
        ↔ JacobianChallenge.ResidueViaTopologicalDegree.TopologicalDegreeFibreBalance_hypothesis f :=
    (JacobianChallenge.ResidueViaTopologicalDegree.tdfb_iff_principalDegree_zero f).symm
  exact h1.trans (h2.trans h3)

/-! ## Forward consumer-facing wrapper -/

/-- **Forward direction (consumer-facing).** A witness of the
topological-degree bundle implies the raw-data chart-integer fibre
balance on the divisor of `f`.

This is the analogue of ZZ72's
`chartIntegralFibreBalanceOn_of_realisation`, but routed through the
topological-degree bundle instead of through the integer-shadow
chain-complex realisation. -/
theorem chartIntegralFibreBalanceOn_of_topologicalDegree
    [DecidableEq X]
    {f : MeromorphicNonzero X}
    (H : JacobianChallenge.ResidueViaTopologicalDegree.TopologicalDegreeFibreBalance_hypothesis f) :
    JacobianChallenge.GlobalResidueSum.chartIntegralFibreBalanceOn
      (principalDivisorMap f).supportFinset
      ((principalDivisorMap f : X → ℤ)) :=
  (chartIntegralFibreBalanceOn_principalDivisor_iff_tdfb f).mpr H

/-! ## Global form -/

/-- **Global form.** If the topological-degree bundle holds for every
`f : MeromorphicNonzero X`, then the raw-data chart-integer fibre
balance on `f`'s divisor support holds for every `f`.

Composes `chartIntegralFibreBalanceOn_of_topologicalDegree` over `f`. -/
theorem chartIntegralFibreBalanceOn_holds_of_topologicalDegree
    [DecidableEq X]
    (H : ∀ f : MeromorphicNonzero X,
        JacobianChallenge.ResidueViaTopologicalDegree.TopologicalDegreeFibreBalance_hypothesis f) :
    ∀ f : MeromorphicNonzero X,
      JacobianChallenge.GlobalResidueSum.chartIntegralFibreBalanceOn
        (principalDivisorMap f).supportFinset
        ((principalDivisorMap f : X → ℤ)) := by
  intro f
  exact chartIntegralFibreBalanceOn_of_topologicalDegree (H f)

/-- **Global Iff with the residue theorem.** The raw-data chart-integer
fibre balance, indexed by every `f` on its divisor support, is
`Iff`-equivalent to `ResidueTheorem X`.

Composes per-`f` `chartIntegralFibreBalanceOn_principalDivisor_iff_tdfb`
with the proven `forall_tdfb_iff_residueTheorem` of
`ZeroCountEqPoleCount.lean`. -/
theorem forall_chartIntegralFibreBalanceOn_principalDivisor_iff_residueTheorem
    [DecidableEq X] :
    (∀ f : MeromorphicNonzero X,
        JacobianChallenge.GlobalResidueSum.chartIntegralFibreBalanceOn
          (principalDivisorMap f).supportFinset
          ((principalDivisorMap f : X → ℤ)))
      ↔ JacobianChallenge.ResidueTheorem X := by
  refine Iff.trans ?_
    JacobianChallenge.ResidueViaTopologicalDegree.forall_tdfb_iff_residueTheorem
  refine ⟨?_, ?_⟩
  · intro hbal f
    exact (chartIntegralFibreBalanceOn_principalDivisor_iff_tdfb f).mp (hbal f)
  · intro htdfb f
    exact (chartIntegralFibreBalanceOn_principalDivisor_iff_tdfb f).mpr (htdfb f)

end FibreBalanceTopologicalDegree

end JacobianChallenge

end
