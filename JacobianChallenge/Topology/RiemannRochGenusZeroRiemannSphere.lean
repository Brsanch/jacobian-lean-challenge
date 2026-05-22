/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.UniformizationFromRiemannRoch
import JacobianChallenge.Topology.Item14FromRRAndSubsingletonOfSC
import JacobianChallenge.Topology.HolomorphicOneFormSubsingletonOfSimplyConnectedRS
import JacobianChallenge.Manifold.HolomorphicEquivDegreeFiberRefl
import JacobianChallenge.Manifold.IsConstantMapAux

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # `RiemannRochGenusZero RiemannSphere` is unconditional

The Riemann-Roch named hypothesis (open at general genus 0 in tree)
collapses to a triviality on `X = RiemannSphere`: the identity map
`id : RS → RS` is a non-constant degree-1 holomorphic map, witnessing
the conclusion directly without invoking any RR-style argument.

This is an RS-specific *validation* of the structural reduction in
`Topology/Item14FromRRAndSubsingletonOfSC.lean`. The Item-14
biconditional from the two minimal open inputs (RR + holomorphic-1-form
subsingleton-of-SC) collapses to a fully unconditional statement on
RS by combining:

* This file's `riemannRochGenusZero_RiemannSphere` (RR on RS).
* `holomorphicOneFormSubsingletonOfSimplyConnected_RiemannSphere`
  from `Topology/HolomorphicOneFormSubsingletonOfSimplyConnectedRS.lean`
  (the analytic input on RS, also unconditional in tree).

The result is a clean, in-tree, no-axiom proof that
`genus RiemannSphere = 0 ↔ Nonempty (RiemannSphere ≃ₜ StandardS2)` —
not a Basic.lean flip (which is general-X), but a *concrete
unconditional smoke-test* of the 2-input form.

## What ships

* `riemannRochGenusZero_RiemannSphere` — unconditional discharge.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open OnePoint

namespace JacobianChallenge

namespace RiemannSphere

/-- **`RiemannRochGenusZero RiemannSphere` is unconditional.**
Witness: `id : RS → RS` is holomorphic, non-constant
(since `(0 : ℂ).toRiemannSphere ≠ ∞`), and has degree 1
(`degreeFiber_id_eq_one`). -/
theorem riemannRochGenusZero_RiemannSphere :
    JacobianChallenge.RiemannRochGenusZero JacobianChallenge.RiemannSphere := by
  intro _hg
  -- Build the witness `id : RS → RS`.
  refine ⟨id, ?_, ?_, ?_⟩
  · -- ContMDiff ω: the identity is smooth at every order.
    exact contMDiff_id
  · -- Non-constant: RS has at least two distinct points (e.g., ∞ and 0).
    -- Use `not_isConstantMap_iff_exists_pair` (with [Nonempty RS]).
    rw [not_isConstantMap_iff_exists_pair]
    -- Two distinct points: ∞ and `OnePoint.some 0`.
    refine ⟨(∞ : JacobianChallenge.RiemannSphere),
            ((0 : ℂ) : JacobianChallenge.RiemannSphere), ?_⟩
    show (∞ : JacobianChallenge.RiemannSphere)
        ≠ ((0 : ℂ) : JacobianChallenge.RiemannSphere)
    exact OnePoint.infty_ne_coe (0 : ℂ)
  · -- Degree 1: `degreeFiber_id_eq_one` applied to RS (non-subsingleton).
    have hNonSub : ¬ Subsingleton JacobianChallenge.RiemannSphere := by
      intro h
      -- Subsingleton would force ∞ = (0 : ℂ) : RS, contradiction.
      have : (∞ : JacobianChallenge.RiemannSphere)
          = ((0 : ℂ) : JacobianChallenge.RiemannSphere) :=
        Subsingleton.elim _ _
      exact OnePoint.infty_ne_coe (0 : ℂ) this
    -- The identity's `degreeFiber` matches `HolomorphicEquiv.refl.contMDiff_forward`'s.
    -- We need `degreeFiber id contMDiff_id = 1`; the existing lemma is stated
    -- with `HolomorphicEquiv.refl.contMDiff_forward`. They are the same proof
    -- of the same statement (`ContMDiff ω id`), so `degreeFiber` is
    -- proof-irrelevant in its hypothesis — well-definedness is independent
    -- of the smoothness witness.
    have h_id := degreeFiber_id_eq_one (X := JacobianChallenge.RiemannSphere) hNonSub
    -- `h_id : ContMDiff.degreeFiber id HolomorphicEquiv.refl.contMDiff_forward = 1`.
    -- `degreeFiber` only depends on `f`, not on the smoothness proof, so we
    -- can rewrite the proof-argument via `Subsingleton.elim` on Prop-valued
    -- arguments. But `ContMDiff` is `Prop`-valued, so any two proofs are
    -- definitionally equal.
    convert h_id

/-- **Smoke test: Item 14 on RS via the 2-input `RR + h_sub` form.**

Validates the structural reduction in
`Item14FromRRAndSubsingletonOfSC.lean` by composing both unconditional
RS-discharges into the 2-input form. The conclusion
`genus RS = 0 ↔ Nonempty (RS ≃ₜ S²)` is already known unconditionally
on RS via the `existsSimplePoleGerm` route
(`genus_eq_zero_iff_homeo_riemannSphere` in
`HolomorphicOneFormSubsingletonOfSimplyConnectedRS.lean`); this is the
parallel discharge via the RR-route shipped in this session.

Both routes produce the same statement via different proof chains —
useful as a sanity check that the 2-input form composes correctly on a
concrete example. -/
theorem genus_eq_zero_iff_homeo_riemannSphere_via_RR_and_subsingletonOfSC :
    JacobianChallenge.genus JacobianChallenge.RiemannSphere = 0 ↔
      Nonempty (JacobianChallenge.RiemannSphere ≃ₜ JacobianChallenge.StandardS2) :=
  JacobianChallenge.genus_eq_zero_iff_homeo_from_RR_and_subsingletonOfSC
    riemannRochGenusZero_RiemannSphere
    JacobianChallenge.holomorphicOneFormSubsingletonOfSimplyConnected_riemannSphere

end RiemannSphere

end JacobianChallenge

end
