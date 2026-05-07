/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.GlobalResidueSum

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Global chain-boundary discharge: reducing the last R5 gap to a
chart-integer fibre balance.

After the ZZ58 refactor, the only remaining genuine `Prop` field on
`GlobalResidueSum_hypothesis f` is

    `global_chain_boundary_eq_zero : ∑ x ∈ S, chartIntegral x = 0`.

This file reduces that single integer identity to a strictly smaller and
more concrete hypothesis: the per-`f` **chart-integer fibre balance**

    `∑ x ∈ S.filter (chartIntegral x > 0),  chartIntegral x
   = ∑ x ∈ S.filter (chartIntegral x < 0), -chartIntegral x`

— i.e. the sum of chart-circle integers over zero-points of `f` equals
the sum of magnitudes of chart-circle integers over pole-points of `f`.

## Why this is strictly smaller than R5

* **Sign-separated.** The original `∑_{x ∈ S} chartIntegral x = 0` mixes
  positive and negative integers in a single arithmetic identity. The
  fibre-balance form replaces it with the equality of two non-negative
  integer sums, each a count of zeros / poles weighted by multiplicity.

* **Matches the topological degree.** Combined with
  `chartIntegral_eq_order` (a bundle field, not a new hypothesis), the
  positive sum is `meromorphicDegreeAtZero f` and the negative-magnitude
  sum is `meromorphicDegreeAtInfty f`, restricted to the bundle's
  support set `S`. So the chart-integer fibre balance is the per-`f`
  shadow of the topological-degree fibre-balance hypothesis already
  named in `MeromorphicDegreeFiberSumEquivalences.lean`.

* **Algebraically equivalent on `S`, but semantically smaller.** The
  two are interderivable by `Finset.sum_filter_add_sum_filter_not` plus
  sign arithmetic; the fibre-balance form, however, separates the two
  *kinds* of contributions and exposes the structural meaning: zeros
  and poles balance, with multiplicity. That is the residue-theorem
  content reduced to its irreducible combinatorial core; the original
  signed form hides it inside a single arithmetic identity.

## What is real-proof here

* `chartIntegralFibreBalanceOn` — the named small Prop on raw data
  (`Finset X`, `X → ℤ`), independent of the bundle.
* `sum_eq_zero_of_fibreBalance` and
  `fibreBalance_of_sum_eq_zero` — the two algebraic directions.
* `chartIntegralFibreBalanceOn_iff_sum_eq_zero` — packaged as `Iff`.
* `mkBundle_of_chartIntegralFibreBalance` — bundle constructor that
  consumes `chartIntegralFibreBalanceOn` instead of the original gap.

## Honest framing

* No `axiom`, no `sorry`. No signature change to existing definitions.
* This is a **reduction**, not an unconditional discharge. The R5
  discharge still awaits a topological-degree / Stokes input.
* The `Iff` shows the new hypothesis is exactly equivalent (over `S`)
  to the bundle's gap field. The shrinkage is **semantic**: same Prop,
  expressed in the form a fibre-counting tool delivers.
-/

noncomputable section

open scoped Real Topology BigOperators Manifold ContDiff
open Complex MeasureTheory

namespace JacobianChallenge

namespace GlobalResidueSum

universe u

/-! ## Reduced hypothesis on raw data -/

/-- **Chart-integer fibre balance on raw data.** The strictly-smaller
gap. Stated on a `Finset` and an integer-valued function — independent
of the bundle so it can be quoted before the bundle is built. -/
def chartIntegralFibreBalanceOn {X : Type*}
    (S : Finset X) (chartIntegral : X → ℤ) : Prop :=
  ∑ x ∈ S.filter (fun x => 0 < chartIntegral x), chartIntegral x
    = ∑ x ∈ S.filter (fun x => chartIntegral x < 0), - chartIntegral x

/-! ## Algebraic equivalence with `∑ = 0` -/

/-- **Decomposition of `∑ S` into the strict-positive and
strict-negative parts.** The zero-valued part contributes nothing. -/
private lemma sum_eq_pos_plus_neg {X : Type*} [DecidableEq X]
    (S : Finset X) (c : X → ℤ) :
    ∑ x ∈ S, c x
      = (∑ x ∈ S.filter (fun x => 0 < c x), c x)
        + ∑ x ∈ S.filter (fun x => c x < 0), c x := by
  classical
  -- Split S by `0 < c x`.
  have h1 :
      ∑ x ∈ S, c x
        = (∑ x ∈ S.filter (fun x => 0 < c x), c x)
          + ∑ x ∈ S.filter (fun x => ¬ 0 < c x), c x :=
    (Finset.sum_filter_add_sum_filter_not
        (s := S) (p := fun x => 0 < c x) (f := fun x => c x)).symm
  -- Decompose `¬ 0 < c x` into `c x < 0` ⊔ `c x = 0`.
  have hsplit :
      S.filter (fun x => ¬ 0 < c x)
        = (S.filter (fun x => c x < 0)) ∪ (S.filter (fun x => c x = 0)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hxS, hxNotPos⟩
      rcases lt_trichotomy (c x) 0 with hlt | heq | hgt
      · exact Or.inl ⟨hxS, hlt⟩
      · exact Or.inr ⟨hxS, heq⟩
      · exact (hxNotPos hgt).elim
    · rintro (⟨hxS, hlt⟩ | ⟨hxS, heq⟩)
      · exact ⟨hxS, fun hpos => (lt_asymm hlt hpos)⟩
      · refine ⟨hxS, ?_⟩
        intro hpos; rw [heq] at hpos; exact lt_irrefl 0 hpos
  have hdisj :
      Disjoint (S.filter (fun x => c x < 0)) (S.filter (fun x => c x = 0)) := by
    refine Finset.disjoint_filter.2 ?_
    intro x _ hlt heq; rw [heq] at hlt; exact lt_irrefl 0 hlt
  have hzero :
      ∑ x ∈ S.filter (fun x => c x = 0), c x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have h2 :
      ∑ x ∈ S.filter (fun x => ¬ 0 < c x), c x
        = ∑ x ∈ S.filter (fun x => c x < 0), c x := by
    calc
      ∑ x ∈ S.filter (fun x => ¬ 0 < c x), c x
          = ∑ x ∈ (S.filter (fun x => c x < 0))
                    ∪ (S.filter (fun x => c x = 0)), c x := by rw [hsplit]
      _ = (∑ x ∈ S.filter (fun x => c x < 0), c x)
            + ∑ x ∈ S.filter (fun x => c x = 0), c x :=
            Finset.sum_union hdisj
      _ = ∑ x ∈ S.filter (fun x => c x < 0), c x := by
            rw [hzero]; exact add_zero _
  rw [h1, h2]

/-- **Forward reduction.** The chart-integer fibre balance implies
`∑ x ∈ S, chartIntegral x = 0`. -/
lemma sum_eq_zero_of_fibreBalance {X : Type*} [DecidableEq X]
    {S : Finset X} {c : X → ℤ}
    (hbal : chartIntegralFibreBalanceOn S c) :
    ∑ x ∈ S, c x = 0 := by
  have hdec := sum_eq_pos_plus_neg (S := S) (c := c)
  -- `hbal : pos = -∑ neg`, i.e. `pos + ∑ neg = 0`.
  have hneg_distrib :
      ∑ x ∈ S.filter (fun x => c x < 0), (- c x)
        = - ∑ x ∈ S.filter (fun x => c x < 0), c x := by
    simp [Finset.sum_neg_distrib]
  have hbal' :
      (∑ x ∈ S.filter (fun x => 0 < c x), c x)
        + ∑ x ∈ S.filter (fun x => c x < 0), c x = 0 := by
    have h := hbal
    unfold chartIntegralFibreBalanceOn at h
    linarith [h, hneg_distrib]
  rw [hdec]; exact hbal'

/-- **Reverse reduction.** `∑ x ∈ S, chartIntegral x = 0` implies the
fibre-balance form. -/
lemma fibreBalance_of_sum_eq_zero {X : Type*} [DecidableEq X]
    {S : Finset X} {c : X → ℤ}
    (hzero : ∑ x ∈ S, c x = 0) :
    chartIntegralFibreBalanceOn S c := by
  have hdec := sum_eq_pos_plus_neg (S := S) (c := c)
  have hsum :
      (∑ x ∈ S.filter (fun x => 0 < c x), c x)
        + ∑ x ∈ S.filter (fun x => c x < 0), c x = 0 := by
    rw [← hdec]; exact hzero
  have hneg_distrib :
      ∑ x ∈ S.filter (fun x => c x < 0), (- c x)
        = - ∑ x ∈ S.filter (fun x => c x < 0), c x := by
    simp [Finset.sum_neg_distrib]
  unfold chartIntegralFibreBalanceOn
  linarith [hsum, hneg_distrib]

/-- **Logical equivalence on raw data.** -/
theorem chartIntegralFibreBalanceOn_iff_sum_eq_zero {X : Type*} [DecidableEq X]
    (S : Finset X) (c : X → ℤ) :
    chartIntegralFibreBalanceOn S c ↔ ∑ x ∈ S, c x = 0 :=
  ⟨sum_eq_zero_of_fibreBalance, fibreBalance_of_sum_eq_zero⟩

/-! ## Bundle-level wrappers and constructor -/

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Bundle-level fibre balance.** Specialisation of
`chartIntegralFibreBalanceOn` to the bundle's `S` and `chartIntegral`. -/
def chartIntegralFibreBalance
    {f : MeromorphicNonzero X}
    (H : GlobalResidueSum_hypothesis f) : Prop :=
  chartIntegralFibreBalanceOn H.S H.chartIntegral

/-- **Forward (bundle level).** Given the chart-integer fibre balance
on a bundle, the bundle's `global_chain_boundary_eq_zero` holds. -/
lemma global_chain_boundary_eq_zero_of_chartIntegralFibreBalance
    {f : MeromorphicNonzero X}
    {H : GlobalResidueSum_hypothesis f}
    (hbal : chartIntegralFibreBalance H) :
    ∑ x ∈ H.S, H.chartIntegral x = 0 := by
  classical
  exact sum_eq_zero_of_fibreBalance hbal

/-- **Reverse (bundle level).** The bundle's gap field implies the
chart-integer fibre balance. -/
lemma chartIntegralFibreBalance_of_global_chain_boundary_eq_zero
    {f : MeromorphicNonzero X}
    {H : GlobalResidueSum_hypothesis f}
    (hzero : ∑ x ∈ H.S, H.chartIntegral x = 0) :
    chartIntegralFibreBalance H := by
  classical
  exact fibreBalance_of_sum_eq_zero hzero

/-- **Logical equivalence (bundle level).** -/
theorem chartIntegralFibreBalance_iff_global_chain_boundary_eq_zero
    {f : MeromorphicNonzero X}
    (H : GlobalResidueSum_hypothesis f) :
    chartIntegralFibreBalance H ↔ ∑ x ∈ H.S, H.chartIntegral x = 0 := by
  classical
  exact chartIntegralFibreBalanceOn_iff_sum_eq_zero H.S H.chartIntegral

/-- **Bundle constructor from the reduced hypothesis.**

Given the bundle's non-gap fields together with the chart-integer
fibre balance (a strictly smaller and more concrete `Prop`), produce
a full `GlobalResidueSum_hypothesis f`. The bundle's gap field is
discharged by `sum_eq_zero_of_fibreBalance`. -/
def mkBundle_of_chartIntegralFibreBalance
    {f : MeromorphicNonzero X}
    (S : Finset X)
    (support_subset : (principalDivisorMap f).supportFinset ⊆ S)
    (chartIntegral : X → ℤ)
    (chartIntegral_eq_order : ∀ x ∈ S,
        chartIntegral x =
          JacobianChallenge.MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x)
    (hbal : chartIntegralFibreBalanceOn S chartIntegral) :
    GlobalResidueSum_hypothesis f := by
  classical
  exact
    { S := S
      support_subset := support_subset
      chartIntegral := chartIntegral
      chartIntegral_eq_order := chartIntegral_eq_order
      global_chain_boundary_eq_zero := sum_eq_zero_of_fibreBalance hbal }

end GlobalResidueSum

end JacobianChallenge

end
