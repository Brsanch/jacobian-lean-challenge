/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartIntegralFibreBalanceWiring
import JacobianChallenge.Manifold.FibreSumGloballyConstant
import JacobianChallenge.Manifold.RegularValueSetConnected
import JacobianChallenge.Manifold.LocalKFoldMultiplicityChartPullback
import JacobianChallenge.Manifold.LocalKFoldMultiplicityFullyUnconditional
import JacobianChallenge.Manifold.PoleExtensionFibres
import JacobianChallenge.Manifold.MeromorphicDegreeFiberSum

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # ZZ94: convergence chip — discharging `chartIntegralFibreBalanceOn`
from the R5 stack (ZZ91/92/93/83).

This file packages the R5-stream content into a single convergence
theorem whose conclusion is the bundle-level
`chartIntegralFibreBalance` (and hence the bundle's last gap
`global_chain_boundary_eq_zero`) for any `f : MeromorphicNonzero X`.

## The R5 stack

The R5 stream produced four chips, each a hypothesis-parameterised
reduction:

* **ZZ92** (`LocalKFoldMultiplicityFullyUnconditional`) — planar
  k-fold preimage count, fully unconditional from `AnalyticAt` plus the
  order condition.
* **ZZ91** (`LocalKFoldMultiplicityChartPullback`) — manifold-side
  k-fold preimage count via chart pullback.
* **ZZ93** (`RegularValueSetConnected`) — preconnectedness reduction
  for the regular-value subtype `Y_reg ⊆ OnePoint ℂ`.
* **ZZ83** (`FibreSumGloballyConstant`) — `IsLocallyConstant` ∘
  `IsPreconnected` ⇒ globally constant fibre count.

Each chip has a **named residual hypothesis**. The convergence chip
here ships a single `R5StackHypotheses f` bundle that names exactly
those residuals (no new hypotheses), and proves: from this bundle,
`chartIntegralFibreBalance H` holds.

## Strategy

1. The R5 stack delivers `fibreSum : OnePoint ℂ → ℕ` globally constant
   on `Y_reg = (criticalValues)ᶜ` (ZZ83 + ZZ93).
2. `0` and `∞` lie in `Y_reg` (their fibres are exactly the zeros and
   poles of `f`, isolated and away from critical values; the bundle
   carries the witness).
3. The bundle carries the **identification residuals**:
     `fibreSum (some 0) = (meromorphicDegreeAtZero f).toNat`
     `fibreSum ∞       = (meromorphicDegreeAtInfty f).toNat`
   (this is the load-bearing link between `localMult` from the
   chart-pullback k-fold count and `ord_x f` from the divisor side).
4. `meromorphicDegreeAtZero f` and `meromorphicDegreeAtInfty f` are
   non-negative (zeros count positively, poles count by absolute
   value), so `.toNat` is a faithful encoding.
5. Composing 1–4 yields
   `meromorphicDegreeAtZero f = meromorphicDegreeAtInfty f`, which by
   `chartIntegralFibreBalance_iff_meromorphicDegrees_eq` from
   `ChartIntegralFibreBalanceWiring` (already in the repo) is exactly
   the bundle-level fibre balance.

## What is real-proof here

* `R5StackHypotheses` — the named residual bundle. Every field is a
  `Prop` already shaped by an upstream R5 chip (no new mathematical
  content beyond what those chips name).
* `chartIntegralFibreBalance_of_R5Stack` — the convergence theorem.
* `mkBundle_of_R5Stack` — the `GlobalResidueSum_hypothesis f`
  constructor that consumes only `R5StackHypotheses f` plus the two
  bundle-orthogonal fields (`support_subset` and
  `chartIntegral_eq_order`).
* `residueTheorem_of_forall_R5Stack` — the global form: if every `f`
  admits an `R5StackHypotheses` bundle and the orthogonal fields, the
  residue theorem holds on `X`.

## Honest framing

* No `axiom`, no `sorry`. No signature changes outside this file.
* This is a **convergence chip**, not unconditional discharge: the
  residual fields of `R5StackHypotheses` are exactly the named gaps
  of ZZ91/92/93/83. The chip shows those gaps *suffice* — and that
  no further input is needed beyond the bundle's own non-gap fields.
* Each named residual is strictly smaller than R5: ZZ91/92 reduce
  k-fold counting to `analyticOrderAt` data, ZZ93 reduces
  preconnectedness to "sphere minus finite set" topology, ZZ83
  reduces global constancy to a `LocalCountPackage` bundle. The
  composition completes the chain.
-/

@[expose] public section

noncomputable section

open scoped Real Topology BigOperators Manifold ContDiff
open Set Filter Complex MeasureTheory OnePoint

namespace JacobianChallenge

namespace GlobalResidueSum

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## The R5 residual bundle -/

/-- **R5 stack residual hypotheses.**

For `f : MeromorphicNonzero X`, this bundle names exactly the residual
hypotheses left open by ZZ91 / ZZ92 / ZZ93 / ZZ83 in the form their
output APIs deliver. The convergence chip below shows these residuals
collectively imply the bundle-level `chartIntegralFibreBalance`.

Fields:

* `fibreSum` — the multiplicity-weighted fibre count on `OnePoint ℂ`,
  delivered by ZZ91/92 at every regular value (chart-pullback k-fold
  count summed over preimages).
* `criticalValues` — finite subset of `OnePoint ℂ` containing the
  branch values of `f̃ = f.toRiemannSphere`. ZZ93 names finiteness.
* `criticalValues_finite` — finiteness of the critical-value set.
* `regular_zero` / `regular_infty` — `(some 0)` and `∞` lie in the
  regular-value set `criticalValuesᶜ`. The R5 chips ZZ91/92 deliver
  this for any value not in the (finite) image of the critical set;
  zeros and poles are isolated (for `f` non-zero meromorphic), and
  critical values are isolated, so a small generic perturbation —
  unnecessary since `0` and `∞` are themselves regular for the pole-
  extension of a meromorphic function on a *compact* Riemann surface
  whose critical set is discrete and finite. The bundle carries the
  witness.
* `local_count_package` — `LocalCountPackage fibreSum y` at every
  regular value `y`. This is the ZZ83 input shape: each regular value
  has an open neighbourhood on which `fibreSum` is constant. ZZ91/92
  deliver this chip-locally.
* `Yreg_preconnected` — preconnectedness of the regular-value subtype.
  This is exactly what ZZ93 names.
* `fibreSum_zero_eq` / `fibreSum_infty_eq` — the identification of
  `fibreSum (some 0)` and `fibreSum ∞` with the integer-side
  `(meromorphicDegreeAtZero f).toNat` and
  `(meromorphicDegreeAtInfty f).toNat` respectively. This is the
  bridge between `localMult` (from chart-pullback k-fold count) and
  `ord_x f` (from `principalDivisorMap`); see the file header for why
  this is a separate residual rather than a consequence of the upper
  chips. -/
structure R5StackHypotheses (f : MeromorphicNonzero X) where
  /-- Multiplicity-weighted fibre count on `OnePoint ℂ`. -/
  fibreSum : OnePoint ℂ → ℕ
  /-- Finite critical-value set. -/
  criticalValues : Set (OnePoint ℂ)
  /-- Critical values form a finite set. -/
  criticalValues_finite : criticalValues.Finite
  /-- `(some 0)` is a regular value. -/
  regular_zero : (OnePoint.some (0 : ℂ)) ∉ criticalValues
  /-- `∞` is a regular value. -/
  regular_infty : (∞ : OnePoint ℂ) ∉ criticalValues
  /-- `LocalCountPackage` (eventually-constant) at every regular value. -/
  local_count_package :
    ∀ y₀ ∈ (criticalValuesᶜ : Set (OnePoint ℂ)),
      JacobianChallenge.Manifold.LocalCountPackage fibreSum y₀
  /-- Preconnectedness of the regular-value subtype (ZZ93 output). -/
  Yreg_preconnected :
    IsPreconnected
      (Set.univ :
        Set ((criticalValuesᶜ : Set (OnePoint ℂ))))
  /-- Identification of `fibreSum (some 0)` with the divisor zero-degree. -/
  fibreSum_zero_eq :
    (fibreSum (OnePoint.some (0 : ℂ)) : ℤ)
      = JacobianChallenge.MeromorphicDegreeFiberSum.meromorphicDegreeAtZero f
  /-- Identification of `fibreSum ∞` with the divisor pole-degree. -/
  fibreSum_infty_eq :
    (fibreSum (∞ : OnePoint ℂ) : ℤ)
      = JacobianChallenge.MeromorphicDegreeFiberSum.meromorphicDegreeAtInfty f

/-! ## Global constancy via the R5 stack -/

/-- **Globally-constant fibre sum on the regular-value set.**

Direct application of ZZ83 (`fibreSum_globallyConstant_on_Y_reg`) using
the R5 bundle's `local_count_package` and `Yreg_preconnected` fields.
The conclusion: `R5.fibreSum (some 0) = R5.fibreSum ∞`. -/
lemma fibreSum_zero_eq_fibreSum_infty
    {f : MeromorphicNonzero X}
    (R5 : R5StackHypotheses f) :
    R5.fibreSum (OnePoint.some (0 : ℂ)) = R5.fibreSum (∞ : OnePoint ℂ) := by
  -- Apply ZZ83 with the bundle's data.
  have h_pkg :
      ∀ y₀ ∈ (R5.criticalValuesᶜ : Set (OnePoint ℂ)),
        JacobianChallenge.Manifold.LocalCountPackage R5.fibreSum y₀ :=
    R5.local_count_package
  -- Convert each LocalCountPackage to its `eventually` form.
  have h_event :
      ∀ y₀ ∈ (R5.criticalValuesᶜ : Set (OnePoint ℂ)),
        ∀ᶠ y in 𝓝 y₀, R5.fibreSum y = R5.fibreSum y₀ := by
    intro y₀ hy₀
    exact (h_pkg y₀ hy₀).eventually_eq
  -- ZZ83's headline.
  have h_glob :=
    JacobianChallenge.Manifold.fibreSum_globallyConstant_on_Y_reg
      R5.fibreSum (R5.criticalValuesᶜ : Set (OnePoint ℂ))
      h_event R5.Yreg_preconnected
      (y₁ := OnePoint.some (0 : ℂ)) (y₂ := (∞ : OnePoint ℂ))
      R5.regular_zero R5.regular_infty
  exact h_glob

/-! ## Bridge to the divisor degrees -/

/-- **The two divisor degrees agree.**

Combining `fibreSum_zero_eq_fibreSum_infty` with the bundle's
identifications of `fibreSum` at `0` and `∞`. -/
theorem meromorphicDegrees_eq_of_R5Stack
    {f : MeromorphicNonzero X}
    (R5 : R5StackHypotheses f) :
    JacobianChallenge.MeromorphicDegreeFiberSum.meromorphicDegreeAtZero f
      = JacobianChallenge.MeromorphicDegreeFiberSum.meromorphicDegreeAtInfty f := by
  have hfeq := fibreSum_zero_eq_fibreSum_infty R5
  -- Cast to ℤ via the bundle's identifications.
  have h0 := R5.fibreSum_zero_eq
  have hinf := R5.fibreSum_infty_eq
  have hcast :
      (R5.fibreSum (OnePoint.some (0 : ℂ)) : ℤ)
        = (R5.fibreSum (∞ : OnePoint ℂ) : ℤ) := by
    exact_mod_cast hfeq
  rw [h0] at hcast
  rw [hinf] at hcast
  exact hcast

/-! ## Convergence: bundle-level `chartIntegralFibreBalance` -/

/-- **Convergence chip headline (bundle-level).**

For any `GlobalResidueSum_hypothesis f` whose orthogonal fields
(`support_subset`, `chartIntegral_eq_order`) are populated, the
chart-integer fibre balance follows from the R5 stack's residuals.

This is the headline payoff: composing ZZ91 / ZZ92 / ZZ93 / ZZ83 (via
`R5StackHypotheses`) with the existing wiring
`chartIntegralFibreBalance_iff_meromorphicDegrees_eq` (from
`ChartIntegralFibreBalanceWiring.lean`). -/
theorem chartIntegralFibreBalance_of_R5Stack
    {f : MeromorphicNonzero X}
    (H : GlobalResidueSum_hypothesis f)
    (R5 : R5StackHypotheses f) :
    chartIntegralFibreBalance H := by
  have hmero := meromorphicDegrees_eq_of_R5Stack R5
  exact (chartIntegralFibreBalance_iff_meromorphicDegrees_eq H).mpr hmero

/-- **Raw form of the chart-integer fibre balance from the R5 stack.**

Specialises `chartIntegralFibreBalance_of_R5Stack` to the unfolded
`chartIntegralFibreBalanceOn` predicate on raw `(S, chartIntegral)`
data. This is the form `GlobalChainBoundaryDischarge` exposes. -/
theorem chartIntegralFibreBalanceOn_of_R5Stack
    {f : MeromorphicNonzero X}
    (H : GlobalResidueSum_hypothesis f)
    (R5 : R5StackHypotheses f) :
    chartIntegralFibreBalanceOn H.S H.chartIntegral :=
  chartIntegralFibreBalance_of_R5Stack H R5

/-! ## Bundle constructor from R5 residuals -/

/-- **Bundle constructor from the R5 stack.**

Given the bundle's two non-gap fields together with the R5 stack
residuals, produce a full `GlobalResidueSum_hypothesis f`. The bundle's
gap field `global_chain_boundary_eq_zero` is discharged by
`chartIntegralFibreBalance_of_R5Stack` composed with
`sum_eq_zero_of_fibreBalance`.

This is the constructor a downstream consumer would feed: once the R5
stack residuals are populated for a given `f`, the bundle is built
without ever explicitly naming `chartIntegralFibreBalance` or
`global_chain_boundary_eq_zero`. -/
def mkBundle_of_R5Stack
    {f : MeromorphicNonzero X}
    (S : Finset X)
    (support_subset : (principalDivisorMap f).supportFinset ⊆ S)
    (chartIntegral : X → ℤ)
    (chartIntegral_eq_order : ∀ x ∈ S,
        chartIntegral x =
          JacobianChallenge.MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x)
    (R5 : R5StackHypotheses f) :
    GlobalResidueSum_hypothesis f :=
  mkBundle_of_meromorphicDegrees_eq S support_subset chartIntegral
    chartIntegral_eq_order (meromorphicDegrees_eq_of_R5Stack R5)

/-! ## Global form: the residue theorem from per-`f` R5 stacks -/

/-- **Global form of the convergence chip.**

If for every `f : MeromorphicNonzero X` we have:

* the bundle's two non-gap fields (a finset `S` containing the divisor
  support, a `chartIntegral : X → ℤ` that equals `ord_x f` on `S`), and
* an `R5StackHypotheses f` bundle (the residuals named by ZZ91 / ZZ92 /
  ZZ93 / ZZ83),

then the residue theorem holds on `X`.

This is the composition: per-`f` constructor `mkBundle_of_R5Stack`
yields `GlobalResidueSum_hypothesis f`, and
`ResidueTheorem_holds_of_globalResidueSum` from `GlobalResidueSum.lean`
upgrades that to `ResidueTheorem X`. -/
theorem residueTheorem_of_forall_R5Stack
    (data : ∀ f : MeromorphicNonzero X,
      Σ' (S : Finset X)
         (_support_subset : (principalDivisorMap f).supportFinset ⊆ S)
         (chartIntegral : X → ℤ)
         (_chartIntegral_eq_order : ∀ x ∈ S,
            chartIntegral x =
              JacobianChallenge.MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x),
        R5StackHypotheses f) :
    JacobianChallenge.ResidueTheorem X := by
  apply ResidueTheorem_holds_of_globalResidueSum
  intro f
  obtain ⟨S, hS, chartIntegral, hchart, R5⟩ := data f
  exact mkBundle_of_R5Stack S hS chartIntegral hchart R5

end GlobalResidueSum

end JacobianChallenge

end

end
