/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LiftRegularContinuousAtPole

set_option diagnostics.threshold 100

/-! # Conditional discharge of `UniversalGermCoherent` /
`UniversalGermCoherentAtPole` from off-pole continuity

`Topology/LiftRegularContinuousFromCoherence.lean` (zz380) and
`Topology/LiftRegularContinuousAtPole.lean` (zz381) reduce
`LiftRegularContinuousAt X` — input #4 of the six-input RR-thread split
of item 14 — to two named germ-coherence hypotheses
`UniversalGermCoherent X p` and `UniversalGermCoherentAtPole X p`. The
content of each is identity-theorem / analytic-continuation:
`germLimitLift g` agrees with `g` on every punctured neighbourhood,
either off the marked pole `p` or at `p` itself.

This chip **discharges both hypotheses unconditionally** under an
**explicit continuity strengthening** of `IsBoundedByDeltaP`, namely
`IsBoundedByDeltaPContinuous p g`, defined as the conjunction of
`IsBoundedByDeltaP p g` with `ContinuousAt g x` for every `x ≠ p`.

## Why a strengthening is needed

The architectural review on 2026-05-13 (OPEN.md item 14 §"Architectural
issue: RR-thread linear system") observed that the current
`IsBoundedByDeltaP p g` admits "essentially-zero" functions: assigning
`g` arbitrary values at a single non-pole point preserves the order
predicate (which only sees germs), yet breaks pointwise equality with
the germ limit. The "blip counterexample" is a witness. Under that
counterexample, `UniversalGermCoherent` and `UniversalGermCoherentAtPole`
are literally false.

The fix sits at the predicate level (germ-field refactor: redefine
`IsBoundedByDeltaP` to quotient by punctured-nhd EventuallyEq, so all
representatives agree with their germ limit at non-pole points). That
refactor is in scope for a separate session.

This chip provides the **structurally clean discharge along the
continuity axis**: any consumer file that can supply a continuity-off-`p`
witness for its `g ∈ L(δp)` immediately obtains the two universal-germ-
coherence hypotheses.

## What this file delivers

* `IsBoundedByDeltaPContinuous p g` — the strengthened `L(δp)`
  membership predicate: `IsBoundedByDeltaP p g ∧ ∀ x ≠ p, ContinuousAt
  g x`.
* `IsBoundedByDeltaPContinuous.toIsBoundedByDeltaP` — forgetful
  embedding back into the weaker predicate.
* `UniversalGermCoherentFromContinuity X p` — for `g` satisfying the
  strengthened predicate, `GermCoherentOff p g` is unconditional. This
  is a stronger named hypothesis than `UniversalGermCoherent X p` (it
  asserts the discharge holds for the strengthened class), and is
  proven here directly.
* `germLimitLift_eventuallyEq_self_at_pole_of_continuous` — the
  pole-side companion lemma: `germLimitLift g =ᶠ[𝓝[≠] p] g` from
  off-pole continuity.

## Mathematical content

For `g` continuous at every `y ≠ p`, the existing
`germLimitLift_eq_self_of_continuousAt`
(`Topology/GermLimitLiftSetup.lean`) immediately gives `germLimitLift g
y = g y` at every such `y`. On any punctured neighbourhood of `x`
(whether `x = p` or `x ≠ p`), all points are `≠ p`, so the equality
holds pointwise. Lifting pointwise to `=ᶠ` is `Filter.eventually_of_forall`
on the punctured-nhd subset `{p}ᶜ`.

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

/-- **Strengthened `L(δp)` membership.** A function `g : X → ℂ` belongs
to `IsBoundedByDeltaPContinuous p` iff it belongs to `IsBoundedByDeltaP
p` and is pointwise continuous at every `x ≠ p`. The continuity
strengthening eliminates the "essentially-zero" / blip counterexample
admitted by `IsBoundedByDeltaP` alone (OPEN.md item-14 architectural
review, 2026-05-13). -/
def IsBoundedByDeltaPContinuous (p : X) (g : X → ℂ) : Prop :=
  IsBoundedByDeltaP p g ∧ ∀ x : X, x ≠ p → ContinuousAt g x

variable {X}

/-- **Forgetful embedding.** `IsBoundedByDeltaPContinuous` implies
`IsBoundedByDeltaP`. -/
lemma IsBoundedByDeltaPContinuous.toIsBoundedByDeltaP
    {p : X} {g : X → ℂ} (h : IsBoundedByDeltaPContinuous X p g) :
    IsBoundedByDeltaP p g := h.1

/-- **Continuity at non-pole points** extracted from the strengthened
predicate, curried at a specific `x`. -/
lemma IsBoundedByDeltaPContinuous.continuousAt_off
    {p : X} {g : X → ℂ} (h : IsBoundedByDeltaPContinuous X p g)
    {x : X} (hx : x ≠ p) :
    ContinuousAt g x := h.2 x hx

/-- **Continuity at non-pole points** extracted from the strengthened
predicate, in the universally-quantified form. -/
lemma IsBoundedByDeltaPContinuous.continuousAt_off_forall
    {p : X} {g : X → ℂ} (h : IsBoundedByDeltaPContinuous X p g) :
    ∀ x : X, x ≠ p → ContinuousAt g x := h.2

/-! ## Pointwise equality of `germLimitLift g` with `g` off the pole -/

/-- **Pointwise identity on `{p}ᶜ`.** Under off-pole continuity,
`germLimitLift g x = g x` for every `x ≠ p`. Direct consequence of
`germLimitLift_eq_self_of_continuousAt`. -/
lemma germLimitLift_eq_self_off_pole
    {p : X} {g : X → ℂ}
    (h_cts : ∀ x : X, x ≠ p → ContinuousAt g x)
    {x : X} (hx : x ≠ p) :
    germLimitLift g x = g x :=
  germLimitLift_eq_self_of_continuousAt (h_cts x hx)

/-! ## Punctured-nhd EventuallyEq off the pole and at the pole -/

/-- **Off-pole EventuallyEq.** For any `x ≠ p` and any `g` continuous
on `{p}ᶜ`, `germLimitLift g =ᶠ[𝓝[≠] x] g`. Pointwise equality on
`{p}ᶜ` plus `{p}ᶜ ∈ 𝓝[≠] x` (since `x ≠ p` implies a nhd of `x`
avoids `p`). -/
lemma germLimitLift_eventuallyEq_self_off_pole
    {p : X} {g : X → ℂ}
    (h_cts : ∀ x : X, x ≠ p → ContinuousAt g x)
    {x : X} (hx : x ≠ p) :
    germLimitLift g =ᶠ[𝓝[≠] x] g := by
  -- A nhd of `x` avoiding `p`. Use T2 separation to find an open set.
  have h_compl_open : IsOpen ({p}ᶜ : Set X) := isOpen_compl_singleton
  have h_x_in : x ∈ ({p}ᶜ : Set X) := hx
  have h_compl_nhd : ({p}ᶜ : Set X) ∈ 𝓝 x := h_compl_open.mem_nhds h_x_in
  have h_compl_NE : ({p}ᶜ : Set X) ∈ 𝓝[≠] x := nhdsWithin_le_nhds h_compl_nhd
  filter_upwards [h_compl_NE] with y hy
  exact germLimitLift_eq_self_off_pole h_cts hy

/-- **At-pole EventuallyEq.** For any `g` continuous on `{p}ᶜ`,
`germLimitLift g =ᶠ[𝓝[≠] p] g`. On a punctured nhd of `p`, all points
`y` satisfy `y ≠ p`, hence are in the off-pole continuity domain. -/
lemma germLimitLift_eventuallyEq_self_at_pole_of_continuous
    {p : X} {g : X → ℂ}
    (h_cts : ∀ x : X, x ≠ p → ContinuousAt g x) :
    germLimitLift g =ᶠ[𝓝[≠] p] g := by
  -- The set `{p}ᶜ` is exactly the support of the punctured nhd filter
  -- at `p`, captured by `self_mem_nhdsWithin`.
  filter_upwards [self_mem_nhdsWithin] with y hy
  -- `hy : y ∈ {p}ᶜ`, i.e. `y ≠ p`.
  have hy_ne : y ≠ p := hy
  exact germLimitLift_eq_self_off_pole h_cts hy_ne

/-! ## The conditional discharges -/

variable (X)

/-- **Conditional discharge of `UniversalGermCoherent`.** For the
strengthened predicate, the off-pole germ-coherence is unconditional. -/
theorem universalGermCoherent_of_continuousOff (p : X) :
    ∀ g : X → ℂ, IsBoundedByDeltaPContinuous X p g → GermCoherentOff p g := by
  intro g hg x hx
  exact germLimitLift_eventuallyEq_self_off_pole (p := p) hg.continuousAt_off_forall hx

/-- **Conditional discharge of `UniversalGermCoherentAtPole`.** For the
strengthened predicate, the at-pole germ-coherence is unconditional. -/
theorem universalGermCoherentAtPole_of_continuousOff (p : X) :
    ∀ g : X → ℂ, IsBoundedByDeltaPContinuous X p g →
      germLimitLift g =ᶠ[𝓝[≠] p] g := by
  intro g hg
  exact germLimitLift_eventuallyEq_self_at_pole_of_continuous hg.continuousAt_off_forall

/-! ## Composed discharge of `LiftRegularContinuousAt`

Composing the two preceding discharges with
`liftRegularContinuousAt_of_universalGermCoherent_both` (zz381 in
`LiftRegularContinuousAtPole.lean`) discharges `LiftRegularContinuousAt
X` — input #4 of the six-input RR-thread split — under the
**continuity-strengthened universal-quantification** version of L(δp).

The named open hypothesis carried forward in this form is:

  `∀ p : X, ∀ g : X → ℂ, IsBoundedByDeltaPContinuous X p g → ⋯`

which is implied by `(∀ p : X, ∀ g, IsBoundedByDeltaP p g → ContinuousAt
g x for x ≠ p)` and the original `IsBoundedByDeltaP` predicate. The
gap between `IsBoundedByDeltaP` and `IsBoundedByDeltaPContinuous` is
precisely the architectural fix the germ-field refactor would deliver.
-/

/-- **Bundled discharge.** Under the continuity-strengthened hypothesis
that every `g ∈ L(δp)` is `ContinuousAt` at every non-pole point, both
named germ-coherence hypotheses fire, and
`LiftRegularContinuousAt X` is satisfied. -/
theorem liftRegularContinuousAt_of_continuousOff
    (h_cts_univ : ∀ p : X, ∀ g : X → ℂ,
      IsBoundedByDeltaP p g → ∀ x : X, x ≠ p → ContinuousAt g x) :
    LiftRegularContinuousAt X := by
  apply liftRegularContinuousAt_of_universalGermCoherent_both
  · intro p g hg
    have hg_str : IsBoundedByDeltaPContinuous X p g :=
      ⟨hg, h_cts_univ p g hg⟩
    exact universalGermCoherent_of_continuousOff X p g hg_str
  · intro p g hg
    have hg_str : IsBoundedByDeltaPContinuous X p g :=
      ⟨hg, h_cts_univ p g hg⟩
    exact universalGermCoherentAtPole_of_continuousOff X p g hg_str

end JacobianChallenge

end
