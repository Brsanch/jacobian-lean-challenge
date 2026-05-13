/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LiftRegularContinuousFromCoherence

set_option diagnostics.threshold 100

/-! # Discharge: regular-continuity of `germLimitLift g` at the marked
point `p` itself, under germ-coherence-at-pole.

zz380 (`LiftRegularContinuousFromCoherence.lean`) discharged the
`x ≠ p` case of `LiftRegularContinuousAt X` from `UniversalGermCoherent
X p`. This chip closes the remaining `x = p` case under the natural
sibling hypothesis

  `UniversalGermCoherentAtPole p` :=
    ∀ g : X → ℂ, IsBoundedByDeltaP p g →
      germLimitLift g =ᶠ[𝓝[≠] p] g

i.e. at the marked pole `p`, every L(δp) element agrees with its
canonicalised lift on a punctured neighbourhood. This is the same
identity-theorem / analytic-continuation content as `GermCoherentOff`,
but extended to include `x = p` (where `g` itself is allowed a simple
pole, but only if the lift's order also drops below `0`; under the
hypothesis `0 ≤ ord_p (lift)`, both functions are forced to be regular
at `p` and therefore agree on the punctured nhd).

## What this chip adds

1. `exists_tendsto_punctured_of_isBoundedByDeltaP_of_order_nonneg`
   — a generalisation of zz365 dropping the `x ≠ p` premise in favour
   of an explicit `0 ≤ mmeromorphicOrderAt _ g x` hypothesis. Works at
   every point, including `x = p`.

2. `continuousAt_germLimitLift_at_p_of_universalGermCoherentAtPole`
   — under `UniversalGermCoherentAtPole p` and `0 ≤ ord_p
   (germLimitLift g)`, the lift is `ContinuousAt p`.

3. `liftRegularContinuousAt_of_universalGermCoherent_both`
   — composes the off-`p` discharge (zz380) with the at-`p` discharge
   to produce `LiftRegularContinuousAt X` from the pair
   `(UniversalGermCoherent, UniversalGermCoherentAtPole)`.

After this chip, `LiftRegularContinuousAt X` is no longer a primitive
input to the RR-thread composition: it factors through two precise
germ-coherence statements (off-pole and at-pole), each of which is
classical identity-theorem content.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Filter

set_option linter.unusedSectionVars false

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Named hypothesis: every L(δp) member is germ-coherent at the
marked pole `p` itself.** The companion to `UniversalGermCoherent X p`
covering the previously-excluded point `x = p`. -/
def UniversalGermCoherentAtPole (p : X) : Prop :=
  ∀ g : X → ℂ, IsBoundedByDeltaP p g →
    germLimitLift g =ᶠ[𝓝[≠] p] g

/-- **Generalisation of zz365 (`exists_tendsto_punctured_…_off_p`)
dropping the `x ≠ p` premise.** For `g ∈ L(δp)` and any `x` (including
`x = p`) at which `g`'s order is non-negative, `g` has a punctured-nhd
limit at `x`. Same proof as zz365 with the order hypothesis taken as
input rather than derived from `x ≠ p`. -/
theorem exists_tendsto_punctured_of_isBoundedByDeltaP_of_order_nonneg
    {p : X} {g : X → ℂ}
    (hg : IsBoundedByDeltaP p g) {x : X}
    (h_ord_g : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g x) :
    ∃ c : ℂ, Filter.Tendsto g (𝓝[≠] x) (𝓝 c) := by
  -- Chart-pullback is MeromorphicAt at (chart x).
  have h_mero_chart : MeromorphicAt (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    hg.mmeromorphicAt x
  -- The hypothesis `h_ord_g` IS the chart-pullback order ≥ 0 by definition.
  have h_ord : 0 ≤ meromorphicOrderAt (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    h_ord_g
  -- Apply mathlib's tendsto-of-nonneg-order to the chart pullback.
  obtain ⟨c, h_tend_chart⟩ :=
    tendsto_nhds_of_meromorphicOrderAt_nonneg h_mero_chart h_ord
  refine ⟨c, ?_⟩
  -- Compose with chart_tendsto_nhdsNE to pull back to a punctured nhd of x.
  have h_comp : Filter.Tendsto ((g ∘ (chartAt ℂ x).symm) ∘ (chartAt ℂ x))
      (𝓝[≠] x) (𝓝 c) :=
    h_tend_chart.comp (MeromorphicNonzero.chart_tendsto_nhdsNE x)
  -- Re-identify with g via chart.left_inv on a neighbourhood of x.
  have h_src : (chartAt ℂ x).source ∈ 𝓝 x :=
    (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
  have h_src_NE : (chartAt ℂ x).source ∈ 𝓝[≠] x :=
    nhdsWithin_le_nhds h_src
  have h_eq : ((g ∘ (chartAt ℂ x).symm) ∘ (chartAt ℂ x)) =ᶠ[𝓝[≠] x] g := by
    filter_upwards [h_src_NE] with y hy_src
    show g ((chartAt ℂ x).symm ((chartAt ℂ x) y)) = g y
    rw [(chartAt ℂ x).left_inv hy_src]
  exact (Filter.Tendsto.congr' h_eq h_comp)

/-- **Substantive discharge of the `x = p` case.** Under
`UniversalGermCoherentAtPole p` and `0 ≤ mmeromorphicOrderAt _
(germLimitLift g) p`, the canonicalised lift is `ContinuousAt` at `p`.

Proof sketch: germ-coherence at `p` transfers the order from `lift` to
`g`, so `g` itself has order ≥ 0 at `p`. The generalised zz365 gives
a punctured-nhd limit `c` for `g` at `p`. By `germLimit_eq_of_tendsto`,
`germLimitLift g p = c`. Transferring the `Tendsto` back to the lift
via germ-coherence and pairing with `continuousAt_iff_punctured_nhds`
gives the result. -/
theorem continuousAt_germLimitLift_at_p_of_universalGermCoherentAtPole
    {p : X} (h_univ_pole : UniversalGermCoherentAtPole X p)
    {g : X → ℂ} (hg_in : IsBoundedByDeltaP p g)
    (h_ord : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (germLimitLift g) p) :
    ContinuousAt (germLimitLift g) p := by
  -- 1. Germ-coherence at p.
  have h_coh : germLimitLift g =ᶠ[𝓝[≠] p] g := h_univ_pole g hg_in
  -- 2. Transport order from lift to g at p, via the punctured-nhd EventuallyEq.
  have h_ord_g : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g p := by
    have h_chart_coh : (germLimitLift g) ∘ (chartAt ℂ p).symm
        =ᶠ[𝓝[≠] ((chartAt ℂ p) p)] g ∘ (chartAt ℂ p).symm :=
      (MeromorphicNonzero.chartSymm_tendsto_nhdsNE p).eventually h_coh
    have h_chart_eq :
        mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (germLimitLift g) p
          = mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g p := by
      change meromorphicOrderAt
            ((germLimitLift g) ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p)
          = meromorphicOrderAt
            (g ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p)
      exact meromorphicOrderAt_congr h_chart_coh
    rw [← h_chart_eq]
    exact h_ord
  -- 3. Punctured-nhd limit of g at p (generalised zz365).
  obtain ⟨c, h_g_tend⟩ :=
    exists_tendsto_punctured_of_isBoundedByDeltaP_of_order_nonneg X hg_in h_ord_g
  -- 4. Identify germLimitLift g p with the limit value.
  have h_val : germLimitLift g p = c := by
    change MeromorphicNonzero.germLimit g p = c
    exact MeromorphicNonzero.germLimit_eq_of_tendsto h_g_tend
  -- 5. Transfer Tendsto from g back to the lift via germ-coherence.
  have h_lift_tend : Filter.Tendsto (germLimitLift g) (𝓝[≠] p) (𝓝 c) :=
    h_g_tend.congr' h_coh.symm
  -- 6. Conclude ContinuousAt via punctured-nhd characterisation.
  rw [continuousAt_iff_punctured_nhds, h_val]
  exact h_lift_tend

/-- **Composition: `LiftRegularContinuousAt X` from the pair
of off-pole and at-pole germ-coherence hypotheses.**

This is the architectural payoff: `LiftRegularContinuousAt X` — input
(iii) in `LiftDecomposition`'s five-fold split, and previously input
#4 in the RR-thread six-input composition — is no longer primitive.
It factors through two precise germ-coherence statements, both of
which are classical identity-theorem content. -/
theorem liftRegularContinuousAt_of_universalGermCoherent_both
    (h_univ : ∀ p : X, UniversalGermCoherent X p)
    (h_univ_pole : ∀ p : X, UniversalGermCoherentAtPole X p) :
    LiftRegularContinuousAt X := by
  intro p g hg_in x h_ord_x
  by_cases hxp : x = p
  · have h_ord_p : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (germLimitLift g) p :=
      hxp ▸ h_ord_x
    rw [hxp]
    exact continuousAt_germLimitLift_at_p_of_universalGermCoherentAtPole X
      (h_univ_pole p) hg_in h_ord_p
  · exact continuousAt_germLimitLift_off_p_of_universalGermCoherent X
      (h_univ p) hg_in hxp

end JacobianChallenge

end
