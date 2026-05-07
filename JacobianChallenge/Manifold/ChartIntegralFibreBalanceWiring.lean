/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.GlobalChainBoundaryDischarge
import JacobianChallenge.Manifold.FibreBalance
import JacobianChallenge.Manifold.MeromorphicDegreeFiberSum
import JacobianChallenge.Manifold.MeromorphicDegreeFiberSumEquivalences

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Wiring `chartIntegralFibreBalanceOn` to existing fibre-balance bundles

`GlobalChainBoundaryDischarge` reduced the bundle's gap field
`global_chain_boundary_eq_zero` (i.e. `∑ x ∈ S, chartIntegral x = 0`)
to the strictly-smaller, sign-separated `chartIntegralFibreBalanceOn S
chartIntegral`:

    `∑_{x ∈ S, chartIntegral x > 0} chartIntegral x
   = ∑_{x ∈ S, chartIntegral x < 0} -chartIntegral x`.

The repository already carries several `Iff`-equivalent reformulations
of the residue-theorem content in `FibreBalance.lean`,
`MeromorphicDegreeFiberSum.lean`, and
`MeromorphicDegreeFiberSumEquivalences.lean`. None of those are stated
on the bundle's *raw* `(S, chartIntegral)` data; they are stated on the
divisor `principalDivisorMap f` and on its filtered fibre-integer
sums.

This file provides the **direct cross-equivalence** between the bundle-
level `chartIntegralFibreBalance H` and `signedMult f = 0` (i.e.
`(principalDivisorMap f).degree = 0`), routed through the bundle's two
non-gap fields `support_subset` and `chartIntegral_eq_order`. From that
single Iff, three further Iffs follow by composing with already-landed
Iffs in `MeromorphicDegreeFiberSumEquivalences`:

* with `signedMult f = 0` (i.e. `(principalDivisorMap f).degree = 0`) —
  the divisor-degree zero formulation of R4, by direct support/order
  rewriting;
* with `meromorphicDegreeAtZero f = meromorphicDegreeAtInfty f` — the
  multiplicity-weighted fibre-integer equality, by composition with
  `degree_eq_zero_iff_meromorphicDegrees_eq`.

The global form `(∀ f, chartIntegralFibreBalance H_f) ↔ ResidueTheorem X`
is then immediate by composing per-`f` with the existing
`forall_meromorphicDegrees_eq_iff_residueTheorem`.

## What is real-proof here

* `chartIntegralFibreBalance_iff_signedMult_zero` — bundle-level Iff
  with `signedMult f = 0`.
* `chartIntegralFibreBalance_iff_principalDegree_zero` — bundle-level
  Iff with `(principalDivisorMap f).degree = 0` (literally the same
  `Prop` as `signedMult f = 0`).
* `chartIntegralFibreBalance_iff_meromorphicDegrees_eq` — bundle-level
  Iff with the fibre-integer equality, the form a topological-degree
  API would deliver.
* `mkBundle_of_meromorphicDegrees_eq` — bundle constructor that
  consumes the fibre-integer equality as the gap, with the bundle's
  own `support_subset` and `chartIntegral_eq_order` discharging the
  reduction.

## Honest framing

* No `axiom`, no `sorry`. No signature change to existing definitions.
* Each Iff above is genuine wiring — not `Iff.rfl`. The forward direction
  rewrites `∑ x ∈ S, chartIntegral x` using `chartIntegral_eq_order`
  into `∑ x ∈ S, principalDivisorMap f x`, then collapses to
  `(principalDivisorMap f).degree` via the bundle's `support_subset` and
  `Div.degree_eq_sum_of_supportFinset_subset`. That is real proof
  content; the rewrite would not type-check if `chartIntegral_eq_order`
  were dropped from the bundle.
* This file does not discharge R5. It exposes the bundle-level
  `chartIntegralFibreBalance` as the same `Prop` (modulo support-Finset
  bookkeeping) as the existing named fibre-balance reformulations, so
  a future agent who closes any one of them automatically discharges
  the bundle's last gap. -/

noncomputable section

open scoped Real Topology BigOperators Manifold ContDiff
open Complex MeasureTheory

namespace JacobianChallenge

namespace GlobalResidueSum

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Core support/order rewrite -/

/-- **Bundle-level support/order rewrite.** The bundle's
`chartIntegral` agrees with `principalDivisorMap f` on the
support-containing finset `S`, so the sum over `S` of `chartIntegral`
equals the sum over `S` of `principalDivisorMap f`, which by
`degree_eq_sum_of_supportFinset_subset` equals
`(principalDivisorMap f).degree`. -/
lemma sum_chartIntegral_eq_principalDegree
    {f : MeromorphicNonzero X}
    (H : GlobalResidueSum_hypothesis f) :
    ∑ x ∈ H.S, H.chartIntegral x = (principalDivisorMap f).degree := by
  classical
  have hpoint : ∀ x ∈ H.S, H.chartIntegral x
      = ((principalDivisorMap f : X → ℤ) x) := by
    intro x hxS
    -- chartIntegral_eq_order : chartIntegral x = orderFun ... f.toFun x
    -- principalDivisorMap_apply : principalDivisorMap f x = orderFun ... f.toFun x
    have hco := H.chartIntegral_eq_order x hxS
    have hpd := principalDivisorMap_apply f x
    rw [hco, ← hpd]
  have hsumeq :
      ∑ x ∈ H.S, H.chartIntegral x
        = ∑ x ∈ H.S, ((principalDivisorMap f : X → ℤ) x) :=
    Finset.sum_congr rfl hpoint
  have hdeg :
      (principalDivisorMap f).degree
        = ∑ x ∈ H.S, ((principalDivisorMap f : X → ℤ) x) :=
    JacobianChallenge.Div.degree_eq_sum_of_supportFinset_subset H.support_subset
  rw [hsumeq, hdeg]

/-! ## Bundle-level `Iff`s with the divisor-degree formulation -/

/-- **Iff with `(principalDivisorMap f).degree = 0`.** The bundle-level
chart-integer fibre balance is `Iff`-equivalent to the divisor-degree
zero formulation of the residue theorem.

This is the load-bearing wiring: it routes a bundle's last open gap
(`global_chain_boundary_eq_zero`, reduced by ZZ67 to
`chartIntegralFibreBalance`) directly onto an already-named target
across the `Manifold/FibreBalance.lean` and
`Manifold/MeromorphicDegreeFiberSum.lean` reformulations. -/
theorem chartIntegralFibreBalance_iff_principalDegree_zero
    {f : MeromorphicNonzero X}
    (H : GlobalResidueSum_hypothesis f) :
    chartIntegralFibreBalance H
      ↔ (principalDivisorMap f).degree = 0 := by
  classical
  have hsum := sum_chartIntegral_eq_principalDegree H
  -- chartIntegralFibreBalance H ↔ ∑ x ∈ S, chartIntegral x = 0
  have hbal :
      chartIntegralFibreBalance H ↔ ∑ x ∈ H.S, H.chartIntegral x = 0 :=
    chartIntegralFibreBalance_iff_global_chain_boundary_eq_zero H
  rw [hbal, hsum]

/-- **Iff with `signedMult f = 0`.** Same `Prop` as
`chartIntegralFibreBalance_iff_principalDegree_zero` modulo the
`signedMult_def` unfolding (which is `rfl`). Stated for downstream
code that prefers the `signedMult` name. -/
theorem chartIntegralFibreBalance_iff_signedMult_zero
    {f : MeromorphicNonzero X}
    (H : GlobalResidueSum_hypothesis f) :
    chartIntegralFibreBalance H ↔ signedMult f = 0 := by
  rw [chartIntegralFibreBalance_iff_principalDegree_zero, signedMult_def]

/-! ## Bundle-level `Iff` with the fibre-integer equality -/

/-- **Iff with the multiplicity-weighted fibre-integer equality.** The
bundle's chart-integer fibre balance is `Iff`-equivalent to the
fibre-integer equality form
`meromorphicDegreeAtZero f = meromorphicDegreeAtInfty f`.

This is the form a topological-degree API for proper holomorphic maps
to `S²` would deliver: degree at `0` (= zero-count with multiplicity)
equals degree at `∞` (= pole-count with multiplicity). -/
theorem chartIntegralFibreBalance_iff_meromorphicDegrees_eq
    {f : MeromorphicNonzero X}
    (H : GlobalResidueSum_hypothesis f) :
    chartIntegralFibreBalance H
      ↔ JacobianChallenge.MeromorphicDegreeFiberSum.meromorphicDegreeAtZero f
          = JacobianChallenge.MeromorphicDegreeFiberSum.meromorphicDegreeAtInfty f :=
  (chartIntegralFibreBalance_iff_principalDegree_zero H).trans
    (JacobianChallenge.MeromorphicDegreeFiberSum.degree_eq_zero_iff_meromorphicDegrees_eq f)

/-! ## Global form -/

/-- **Global form.** If for *every* `f` the bundle exists with its
chart-integer fibre balance discharged, then the residue theorem holds
on `X`. This composes the per-`f` Iff with the existing global
`forall_meromorphicDegrees_eq_iff_residueTheorem`. -/
theorem residueTheorem_of_forall_chartIntegralFibreBalance
    (H : ∀ f : MeromorphicNonzero X, GlobalResidueSum_hypothesis f)
    (hbal : ∀ f : MeromorphicNonzero X, chartIntegralFibreBalance (H f)) :
    JacobianChallenge.ResidueTheorem X := by
  intro f
  have hd : (principalDivisorMap f).degree = 0 :=
    (chartIntegralFibreBalance_iff_principalDegree_zero (H f)).1 (hbal f)
  exact hd

/-! ## Bundle constructor from the fibre-integer equality -/

/-- **Bundle constructor from `meromorphicDegreeAtZero = meromorphicDegreeAtInfty`.**

Given the bundle's two non-gap fields (`support_subset` and
`chartIntegral_eq_order`) together with the multiplicity-weighted
fibre-integer equality (a strictly named target across the FibreBalance
/ MeromorphicDegreeFiberSum reformulations), produce a full
`GlobalResidueSum_hypothesis f`.

This is the constructor a future topological-degree API would feed:
once `meromorphicDegreeAtZero f = meromorphicDegreeAtInfty f` is
discharged for every `f`, the bundle is built without ever explicitly
naming `chartIntegralFibreBalance` or
`global_chain_boundary_eq_zero`. -/
def mkBundle_of_meromorphicDegrees_eq
    {f : MeromorphicNonzero X}
    (S : Finset X)
    (support_subset : (principalDivisorMap f).supportFinset ⊆ S)
    (chartIntegral : X → ℤ)
    (chartIntegral_eq_order : ∀ x ∈ S,
        chartIntegral x =
          JacobianChallenge.MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x)
    (hmero :
        JacobianChallenge.MeromorphicDegreeFiberSum.meromorphicDegreeAtZero f
          = JacobianChallenge.MeromorphicDegreeFiberSum.meromorphicDegreeAtInfty f) :
    GlobalResidueSum_hypothesis f := by
  classical
  -- Build the bundle from the chart-integer fibre balance form,
  -- which we obtain from `hmero` by routing through the divisor degree.
  have hd : (principalDivisorMap f).degree = 0 :=
    JacobianChallenge.MeromorphicDegreeFiberSum.global_sum_zero_of_meromorphicDegrees_eq hmero
  -- A scratch bundle to feed into the existing per-f Iff.
  let H : GlobalResidueSum_hypothesis f :=
    { S := S
      support_subset := support_subset
      chartIntegral := chartIntegral
      chartIntegral_eq_order := chartIntegral_eq_order
      global_chain_boundary_eq_zero := by
        -- ∑ x ∈ S, chartIntegral x = (principalDivisorMap f).degree = 0.
        have hsum :
            ∑ x ∈ S, chartIntegral x = (principalDivisorMap f).degree := by
          classical
          have hpoint : ∀ x ∈ S, chartIntegral x
              = ((principalDivisorMap f : X → ℤ) x) := by
            intro x hxS
            have hco := chartIntegral_eq_order x hxS
            have hpd := principalDivisorMap_apply f x
            rw [hco, ← hpd]
          have hsumeq :
              ∑ x ∈ S, chartIntegral x
                = ∑ x ∈ S, ((principalDivisorMap f : X → ℤ) x) :=
            Finset.sum_congr rfl hpoint
          have hdeg :
              (principalDivisorMap f).degree
                = ∑ x ∈ S, ((principalDivisorMap f : X → ℤ) x) :=
            JacobianChallenge.Div.degree_eq_sum_of_supportFinset_subset support_subset
          rw [hsumeq, hdeg]
        rw [hsum, hd] }
  exact H

end GlobalResidueSum

end JacobianChallenge

end
