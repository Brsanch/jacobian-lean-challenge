/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LiftNonConstancyFromContinuity

set_option diagnostics.threshold 100

/-! # Discharge of `LiftNonvanishingGerm` via a named identity-theorem
hypothesis

zz362's `LiftDecomposition` input (ii) `LiftNonvanishingGerm` asks:
for a non-constant `g ∈ L(δp)`, `germLimitLift g` has order strictly
less than `⊤` at every point. Equivalently: `germLimitLift g` is not
"eventually zero on a punctured nhd" at any point.

Under the continuity strengthening
`IsBoundedByDeltaPContinuousAtPole p g`, we have `germLimitLift g = g`
as functions (from
`Topology/LiftNonConstancyFromContinuity.lean`) and the
order-preservation `mmeromorphicOrderAt _ (germLimitLift g) x =
mmeromorphicOrderAt _ g x` (from
`Topology/LiftMeroOrderFromContinuity.lean`). So input (ii) reduces to:

> For a non-constant `g ∈ L(δp)` (satisfying the strengthening),
> `mmeromorphicOrderAt _ g x ≠ ⊤` at every `x`.

This is the **identity theorem for meromorphic functions on a connected
complex 1-manifold**: a meromorphic function that is eventually zero on
a punctured neighbourhood of even a single point is everywhere eventually
zero (in a germ sense), hence — under the strengthening — pointwise
zero, contradicting non-constancy.

The classical identity-theorem statement on a connected manifold is
not at the mathlib pin (`8e3c989...`). The cleanest packaging is the
**named-hypothesis pattern** already used elsewhere in this repository
(cf. `StokesCompactSurfacePartitionOfUnity_hypothesis`,
`PeriodLatticeAnalyticHypotheses`): we expose the identity-theorem
content as a single named `Prop` and discharge (ii) under it.

## What this file delivers

* `MeromorphicIdentityPropagation X` — the named identity-theorem
  hypothesis: for any meromorphic `g`, if its order is `⊤` at some
  `x₀`, then `g =ᶠ[𝓝[≠] y] 0` at every `y` (germ-level identity
  propagation).

* `not_top_order_of_non_const_under_strengthening` — under
  `MeromorphicIdentityPropagation X` and
  `IsBoundedByDeltaPContinuousAtPole p g`, if `g ∉ span ℂ {1}`, then
  `mmeromorphicOrderAt _ g x ≠ ⊤` at every `x`.

* `liftNonvanishingGerm_at_x_via_identity_theorem` — the substantive
  discharge: under both the identity-theorem hypothesis and the
  at-pole continuity strengthening, `mmeromorphicOrderAt _
  (germLimitLift g) x ≠ ⊤` at every `x`.

Composing with the prior three chips (off-pole continuity discharging
(i)/(iii)/(iv); at-pole compatibility discharging (v)), this completes
the architectural reduction of zz362's five-fold LiftDecomposition to
two named hypotheses:

* the universal at-pole-germ-compatible continuity strengthening of
  L(δp) (the operational germ-field refactor); and
* `MeromorphicIdentityPropagation X` (the classical identity theorem,
  citable, not at the pin).

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Filter

set_option linter.unusedSectionVars false

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Named identity-theorem hypothesis for meromorphic functions on
`X`.** If `g` is meromorphic everywhere on the connected manifold `X`
and its meromorphic order is `⊤` at some point `x₀` (i.e. `g` is
eventually zero on a punctured nhd of `x₀`), then `g` is eventually
zero on a punctured nhd of every point.

This is the manifold-level analogue of mathlib's
`meromorphicOrderAt_eq_top_iff` combined with the analytic identity
theorem on a connected manifold. mathlib at the pin has the chart-
level pieces but not the global manifold-level propagation. -/
def MeromorphicIdentityPropagation : Prop :=
  ∀ (g : X → ℂ),
    MMeromorphicOn (𝓘(ℂ, ℂ)) g Set.univ →
    (∃ x₀ : X, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g x₀ = ⊤) →
    ∀ y : X, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g y = ⊤

variable {X}

/-! ## Pointwise zero from "eventually zero on punctured nhd" everywhere

Under the at-pole continuity strengthening, `g(y)` for `y ≠ p` is
determined by punctured-nhd values (continuity). If `g =ᶠ[𝓝[≠] y] 0`
holds at every `y`, then `g y = 0` at every `y ≠ p` (continuity
forces the limit value `0` to be `g y`). At `y = p`, the at-pole
compatibility forces `g p = 0` (since the punctured-nhd limit is `0`).
So `g = 0` as a function.
-/

/-- **Eventually-zero punctured-nhd everywhere implies pointwise zero off `p`.**
For `g` continuous at `y ≠ p` and `g =ᶠ[𝓝[≠] y] 0`, continuity forces
`g y = 0`. -/
lemma eq_zero_off_p_of_eventuallyZero_punctured
    {p : X} {g : X → ℂ}
    (h_cts : ∀ x : X, x ≠ p → ContinuousAt g x)
    (h_punc_zero : ∀ y : X, ∀ᶠ z in 𝓝[≠] y, g z = 0)
    {y : X} (hy : y ≠ p) :
    g y = 0 := by
  -- `Tendsto g (𝓝[≠] y) (𝓝 0)` from `h_punc_zero y` (events filter).
  have h_tend_pun : Tendsto g (𝓝[≠] y) (𝓝 0) := by
    -- Cast eventually-zero into a Tendsto via Tendsto.congr'.
    have : Tendsto (fun _ : X => (0 : ℂ)) (𝓝[≠] y) (𝓝 0) := tendsto_const_nhds
    exact this.congr' ((h_punc_zero y).mono (fun _ hz => hz.symm))
  -- Combine with continuity at `y` to get tendsto on the full nhd.
  have h_cts_y : ContinuousAt g y := h_cts y hy
  -- `ContinuousAt g y ⇒ Tendsto g (𝓝 y) (𝓝 (g y))`.
  have h_tend_full : Tendsto g (𝓝 y) (𝓝 (g y)) := h_cts_y.tendsto
  -- The punctured-nhd limit (=0) and the full-nhd limit (=g y) must agree.
  have h_tend_pun_from_full : Tendsto g (𝓝[≠] y) (𝓝 (g y)) :=
    h_tend_full.mono_left nhdsWithin_le_nhds
  -- Tendsto-unique at NeBot.
  haveI : (𝓝[≠] y).NeBot := MeromorphicNonzero.nhdsNE_neBot y
  exact tendsto_nhds_unique h_tend_pun_from_full h_tend_pun

/-- **Eventually-zero punctured-nhd at `p` implies `g p = 0`** under the
at-pole compatibility. The punctured-nhd limit at `p` is `0`; the
at-pole compatibility forces `g p = 0`. -/
lemma eq_zero_at_p_of_eventuallyZero_punctured
    {p : X} {g : X → ℂ}
    (h_at_pole : ∀ c : ℂ, Tendsto g (𝓝[≠] p) (𝓝 c) → g p = c)
    (h_punc_zero : ∀ y : X, ∀ᶠ z in 𝓝[≠] y, g z = 0) :
    g p = 0 := by
  have h_tend : Tendsto g (𝓝[≠] p) (𝓝 0) := by
    have : Tendsto (fun _ : X => (0 : ℂ)) (𝓝[≠] p) (𝓝 0) := tendsto_const_nhds
    exact this.congr' ((h_punc_zero p).mono (fun _ hz => hz.symm))
  exact h_at_pole 0 h_tend

/-- **Pointwise zero everywhere from eventually-zero punctured-nhd
everywhere**, combining off-pole continuity with at-pole compatibility. -/
lemma eq_zero_everywhere_of_eventuallyZero_punctured
    {p : X} {g : X → ℂ}
    (h : IsBoundedByDeltaPContinuousAtPole X p g)
    (h_punc_zero : ∀ y : X, ∀ᶠ z in 𝓝[≠] y, g z = 0) :
    g = 0 := by
  funext y
  by_cases hyp : y = p
  · subst hyp
    exact eq_zero_at_p_of_eventuallyZero_punctured h.2 h_punc_zero
  · exact eq_zero_off_p_of_eventuallyZero_punctured h.1.continuousAt_off_forall
      h_punc_zero hyp

/-! ## The substantive discharge -/

/-- **`mmeromorphicOrderAt _ g x = ⊤`** unfolds via the chart pullback
to **`meromorphicOrderAt (g ∘ chart.symm) (chart x) = ⊤`**, which by
mathlib's `meromorphicOrderAt_eq_top_iff` is equivalent to the
chart-pullback being eventually zero on a punctured nhd. The
manifold-level statement is `g =ᶠ[𝓝[≠] x] 0` after transporting back
through the chart. -/
lemma eventuallyZero_punctured_of_mmeromorphicOrderAt_eq_top
    {g : X → ℂ} {x : X}
    (h : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g x = ⊤) :
    ∀ᶠ z in 𝓝[≠] x, g z = 0 := by
  -- `mmeromorphicOrderAt = ⊤` unfolds to `meromorphicOrderAt (g ∘ chart.symm) (chart x) = ⊤`.
  have h_chart : meromorphicOrderAt (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = ⊤ := h
  -- Apply mathlib's `meromorphicOrderAt_eq_top_iff`.
  have h_pun_chart : ∀ᶠ z in 𝓝[≠] ((chartAt ℂ x) x),
      (g ∘ (chartAt ℂ x).symm) z = 0 :=
    meromorphicOrderAt_eq_top_iff.mp h_chart
  -- Transport back to a punctured-nhd of `x` via
  -- `MeromorphicNonzero.chart_tendsto_nhdsNE`, the chart maps `𝓝[≠] x`
  -- into `𝓝[≠] (chart x)`.
  have h_chart_tend : Tendsto (chartAt ℂ x) (𝓝[≠] x) (𝓝[≠] ((chartAt ℂ x) x)) :=
    MeromorphicNonzero.chart_tendsto_nhdsNE x
  -- Compose: at `z ∈ 𝓝[≠] x`, `(g ∘ chart.symm) (chart z) = 0`, and
  -- on the chart source, `chart.symm (chart z) = z`, so `g z = 0`.
  have h_pun : ∀ᶠ z in 𝓝[≠] x, (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) z) = 0 :=
    h_chart_tend h_pun_chart
  -- Identify `(g ∘ chart.symm ∘ chart) z = g z` on `chart.source` (nhd of `x`).
  have h_src : (chartAt ℂ x).source ∈ 𝓝 x :=
    (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
  have h_src_NE : (chartAt ℂ x).source ∈ 𝓝[≠] x :=
    nhdsWithin_le_nhds h_src
  filter_upwards [h_pun, h_src_NE] with z hz hz_src
  -- `hz : (g ∘ chart.symm) (chart z) = 0`, `hz_src : z ∈ chart.source`.
  have h_left_inv : (chartAt ℂ x).symm ((chartAt ℂ x) z) = z :=
    (chartAt ℂ x).left_inv hz_src
  -- `(g ∘ chart.symm) (chart z) = g (chart.symm (chart z)) = g z`.
  show g z = 0
  have hz' : g ((chartAt ℂ x).symm ((chartAt ℂ x) z)) = 0 := hz
  rwa [h_left_inv] at hz'

variable (X)

/-- **Substantive non-vanishing order under the named identity-theorem
hypothesis and the at-pole continuity strengthening.** For non-constant
`g ∈ L(δp)` (strengthened), `mmeromorphicOrderAt _ g x ≠ ⊤` at every `x`. -/
theorem not_top_order_of_non_const_under_strengthening
    (h_identity : MeromorphicIdentityPropagation X)
    {p : X} {g : X → ℂ}
    (h_str : IsBoundedByDeltaPContinuousAtPole X p g)
    (h_nc : g ∉ Submodule.span ℂ ({(1 : X → ℂ)} : Set (X → ℂ)))
    (x : X) :
    mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g x ≠ ⊤ := by
  intro h_top
  -- Apply the identity-theorem hypothesis: order ⊤ at one point ⇒
  -- order ⊤ everywhere.
  have h_mero : MMeromorphicOn (𝓘(ℂ, ℂ)) g Set.univ :=
    h_str.toIsBoundedByDeltaP.mmeromorphicOn
  have h_all_top : ∀ y : X, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g y = ⊤ :=
    h_identity g h_mero ⟨x, h_top⟩
  -- Convert each ord = ⊤ into eventually-zero on punctured nhd.
  have h_punc_zero : ∀ y : X, ∀ᶠ z in 𝓝[≠] y, g z = 0 := by
    intro y
    exact eventuallyZero_punctured_of_mmeromorphicOrderAt_eq_top (h_all_top y)
  -- Conclude `g = 0` pointwise under the at-pole strengthening.
  have h_g_zero : g = 0 :=
    eq_zero_everywhere_of_eventuallyZero_punctured h_str h_punc_zero
  -- `g = 0 ∈ span ℂ {1}`, contradicting non-constancy.
  apply h_nc
  rw [h_g_zero]
  exact Submodule.zero_mem _

/-- **Substantive discharge of input (ii)** at every point: under both
the identity-theorem hypothesis and the at-pole continuity
strengthening, `mmeromorphicOrderAt _ (germLimitLift g) x ≠ ⊤` at
every `x`. Uses the order-preservation from
`LiftMeroOrderFromContinuity` to convert the claim about
`germLimitLift g` to a claim about `g`. -/
theorem liftNonvanishingGerm_at_x_via_identity_theorem
    (h_identity : MeromorphicIdentityPropagation X)
    {p : X} {g : X → ℂ}
    (h_str : IsBoundedByDeltaPContinuousAtPole X p g)
    (h_nc : g ∉ Submodule.span ℂ ({(1 : X → ℂ)} : Set (X → ℂ)))
    (x : X) :
    mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (germLimitLift g) x ≠ ⊤ := by
  -- Order preservation under the continuity strengthening.
  have h_eq := germLimitLift_mmeromorphicOrderAt_eq_of_continuous
    (p := p) (g := g) h_str.1.continuousAt_off_forall x
  rw [h_eq]
  exact not_top_order_of_non_const_under_strengthening X h_identity h_str h_nc x

end JacobianChallenge

end
