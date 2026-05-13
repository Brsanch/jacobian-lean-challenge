/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LiftNonvanishingFromIdentityTheorem
import JacobianChallenge.Topology.RRGenusZeroFinrankChain

set_option diagnostics.threshold 100

/-! # `LiftToMeromorphicNonzero X` from two named hypotheses

This is the final-composition chip of the four-chip
continuity-strengthening-axis arc:

* `UniversalGermCoherentFromContinuity.lean` discharges inputs
  (i)/(iii)/(iv) of zz362's `LiftDecomposition` under
  `IsBoundedByDeltaPContinuous`.
* `LiftMeroOrderFromContinuity.lean` discharges (i) and (iv) more
  fully (`MMeromorphicAt` and order preservation through chart
  pullback).
* `LiftNonConstancyFromContinuity.lean` discharges (v) under
  `IsBoundedByDeltaPContinuousAtPole`.
* `LiftNonvanishingFromIdentityTheorem.lean` discharges (ii) under
  the at-pole strengthening plus the named identity-theorem hypothesis
  `MeromorphicIdentityPropagation X`.

This file composes all four into `LiftToMeromorphicNonzero X` directly,
bypassing the literal five-fold form
`liftToMeromorphicNonzero_of_five_sub_hypotheses` (whose `LiftNotConstant`
input has a universally-quantified-over-`g` signature that isn't
naturally produced by the strengthening discharge — the discharge
naturally restricts to `g ∈ L(δp)`, which is the only context in which
the consumer actually invokes it).

## What this file delivers

* `liftToMeromorphicNonzero_from_strengthening_and_identity` — the
  full discharge of `LiftToMeromorphicNonzero X` from:
  - a universal at-pole-germ-compatible continuity strengthening of
    every `g ∈ L(δp)` (the operational germ-field refactor), and
  - the manifold identity-theorem hypothesis
    `MeromorphicIdentityPropagation X`.

This completes the architectural reduction of the
`LiftToMeromorphicNonzero` content of item 14's RR-thread to exactly
two precise classical inputs. Combined with the prior
`Topology/Item14ForwardFromFiniteDim.lean` discharge of the forward
leg from `[FiniteDimensional] + ExistsSimplePoleGerm + S2ImpliesGenus0`,
item 14's open content is now factored onto:

* **Hodge gap**: `FiniteDimensional ℂ (HolomorphicOneForm X)` (named
  in `Manifold/HodgeFiniteDimensional.lean`).
* **RR existence gap**: `ExistsSimplePoleGermAtSomePoint X` (the
  classical Riemann-Roch consequence at genus 0).
* **Reverse-leg gap**: `S2ImpliesGenus0 X` (geometric-vs-topological
  genus identification, Hodge content).
* **Germ-field refactor**: universal at-pole-germ-compatible continuity
  on L(δp) (operational predicate-level fix).
* **Identity-theorem gap**: `MeromorphicIdentityPropagation X` (classical
  identity theorem on connected complex 1-manifolds).

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff

set_option linter.unusedSectionVars false

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Final composition: `LiftToMeromorphicNonzero X` from two named
hypotheses.**

Under:

1. A universal at-pole-germ-compatible continuity strengthening on
   every `g ∈ L(δp)` (operational form of the germ-field refactor),
   and
2. The manifold identity-theorem hypothesis
   `MeromorphicIdentityPropagation X`,

`LiftToMeromorphicNonzero X` holds: every non-constant `g ∈ L(δp)`
admits a `MeromorphicNonzero X` representative with the same L(δp)
order bounds and non-constancy. The representative is `germLimitLift
g`, the canonicalisation of `g` to its punctured-nhd germ limit. -/
theorem liftToMeromorphicNonzero_from_strengthening_and_identity
    (h_strong_univ : ∀ p : X, ∀ g : X → ℂ,
      IsBoundedByDeltaP p g → IsBoundedByDeltaPContinuousAtPole X p g)
    (h_identity : MeromorphicIdentityPropagation X) :
    LiftToMeromorphicNonzero X := by
  intro p g hg_in hg_nin
  -- The strengthening on this specific (p, g).
  have h_str : IsBoundedByDeltaPContinuousAtPole X p g := h_strong_univ p g hg_in
  -- The off-pole continuity component.
  have h_cts_off : ∀ y : X, y ≠ p → ContinuousAt g y :=
    h_str.1.continuousAt_off_forall
  -- Build the MeromorphicNonzero from the three sub-fields.
  -- Field 1: MMeromorphicOn (germLimitLift g).
  have h_mero : MMeromorphicOn (𝓘(ℂ, ℂ)) (germLimitLift g) Set.univ :=
    germLimitLift_mmeromorphicOn_of_continuous hg_in.mmeromorphicOn h_cts_off
  -- Field 2: non-vanishing germ at every point.
  have h_nonvan : ∀ x, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (germLimitLift g) x ≠ ⊤ :=
    fun x => liftNonvanishingGerm_at_x_via_identity_theorem X h_identity
      h_str hg_nin x
  -- Field 3: regular-continuous at non-pole points. We need:
  --   ∀ x, 0 ≤ ord (germLimitLift g) x → ContinuousAt (germLimitLift g) x.
  -- Under the strengthening, germLimitLift g = g, so continuity of
  -- germLimitLift g reduces to continuity of g, which off-pole holds.
  -- For x = p: under the at-pole strengthening, if order(g) ≥ 0 at p
  -- then g has a punctured-nhd limit (the analytic extension value at
  -- p); the at-pole compatibility forces g(p) to equal that limit, so
  -- g is continuous at p. We don't reproduce this argument here:
  -- under our universal strengthening, the (off-pole continuity)
  -- form of zz380's discharge handles x ≠ p, and the (at-pole
  -- germ-compatibility) form of zz381's companion handles x = p.
  -- The strengthening is precisely what makes both available.
  have h_reg_cts : ∀ x, 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (germLimitLift g) x →
      ContinuousAt (germLimitLift g) x := by
    intro x _h_ord
    -- Under the strengthening, germLimitLift g = g pointwise everywhere.
    have h_eq : germLimitLift g = g :=
      germLimitLift_eq_self_of_continuousAtPole h_str
    rw [h_eq]
    by_cases hxp : x = p
    · -- At p: continuity follows from the at-pole germ-compatibility.
      rw [hxp]
      -- Goal: ContinuousAt g p. Order ≥ 0 at p gives a punctured-nhd
      -- limit of g at p; the at-pole compatibility forces g(p) to
      -- equal that limit, giving full-nhd Tendsto.
      have h_ord_p : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g p := by
        -- Original: 0 ≤ ord (germLimitLift g) x. Substitute x = p,
        -- then use order preservation.
        have h_ord_eq :=
          germLimitLift_mmeromorphicOrderAt_eq_of_continuous
            (p := p) (g := g) h_cts_off p
        have h_at_p : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (germLimitLift g) p := by
          rw [← hxp]; exact _h_ord
        rw [← h_ord_eq]; exact h_at_p
      -- Punctured-nhd limit at p via the generalised zz365.
      obtain ⟨c, h_tend⟩ :=
        exists_tendsto_punctured_of_isBoundedByDeltaP_of_order_nonneg X hg_in h_ord_p
      have h_gp : g p = c := h_str.value_eq_limit h_tend
      rw [continuousAt_iff_punctured_nhds, h_gp]
      exact h_tend
    · -- Off p: continuity is the strengthening's off-pole component.
      exact h_cts_off x hxp
  -- Build the MeromorphicNonzero.
  set f : MeromorphicNonzero X :=
    MeromorphicNonzero.ofRegularContinuous (germLimitLift g) h_mero h_nonvan h_reg_cts
    with hf_def
  -- Assemble the existential. f.toFun = germLimitLift g definitionally.
  refine ⟨f, ?_, ?_, ?_⟩
  · -- Order ≥ 0 off p.
    intro x hx
    show 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (germLimitLift g) x
    -- Order is preserved; ord g x ≥ 0 from hg_in off p.
    rw [germLimitLift_mmeromorphicOrderAt_eq_of_continuous h_cts_off x]
    exact hg_in.order_nonneg_off x hx
  · -- Order ≥ -1 at p.
    show ((-1 : ℤ) : WithTop ℤ) ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (germLimitLift g) p
    rw [germLimitLift_mmeromorphicOrderAt_eq_of_continuous h_cts_off p]
    exact hg_in.order_ge_neg_one_at_p
  · -- ¬ IsConstantMap (germLimitLift g). Use the non-constancy transport.
    exact not_isConstantMap_germLimitLift_of_continuousAtPole_of_non_const
      h_str hg_nin

end JacobianChallenge

end
