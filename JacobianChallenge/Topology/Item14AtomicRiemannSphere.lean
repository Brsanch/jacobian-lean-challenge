/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Item14FromSimplePoleAndPrimitive
import JacobianChallenge.Topology.HolomorphicOneFormSubsingletonOfSimplyConnectedRS
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Item 14 on RS via the atomic 2-input form (third independent route)

Completes the structural validation of the maximally-atomic 2-input
form shipped in `Item14FromSimplePoleAndPrimitive.lean` by discharging
both atoms unconditionally on `X = RiemannSphere`:

* `hSP : ExistsSimplePoleGermAtSomePoint RS` — already in tree
  (`Topology/HolomorphicOneFormSubsingletonOfSimplyConnectedRS.lean`).
* `h_primitive_exists` on RS — discharged here. Witness: F ≡ 0, which
  is ContMDiff ω (constant) and has mfderiv ≡ 0, matching the eval of
  the unique (zero) holomorphic 1-form on RS (since
  `HolomorphicOneForm RiemannSphere` is subsingleton, every om = 0,
  so `om.eval x = 0` for all x).

The composition `genus_eq_zero_iff_homeo_riemannSphere_via_atomic`
provides a **third independent unconditional Item-14-on-RS proof**
(alongside `genus_eq_zero_iff_homeo_riemannSphere` from
`HolomorphicOneFormSubsingletonOfSimplyConnectedRS.lean` and
`...via_RR_and_subsingletonOfSC` from
`RiemannRochGenusZeroRiemannSphere.lean`).

Multiple independent unconditional proofs of the same concrete
statement validate that the structural factorization is correct (the
2-input atomic form composes to give the right conclusion).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff Topology

namespace JacobianChallenge

namespace RiemannSphere

/-- **Primitive-existence on RS is unconditional.**

Witness: take `F : RS → ℂ` to be the constant zero function. Then `F`
is `ContMDiff ω` (constant maps are smooth at every order), and
`mfderiv F x = 0` for all `x`. Combined with the fact that
`HolomorphicOneForm RiemannSphere` is a `Subsingleton` (every form is
zero), we have `om.eval x = 0 = mfderiv F x` pointwise. -/
theorem primitiveExists_RiemannSphere :
    SimplyConnectedSpace JacobianChallenge.RiemannSphere →
      ∀ om : HolomorphicOneForm JacobianChallenge.RiemannSphere,
        ∃ F : JacobianChallenge.RiemannSphere → ℂ,
          ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F ∧
            ∀ x : JacobianChallenge.RiemannSphere,
              om.eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) F x := by
  intro _hSC om
  -- Witness: F ≡ 0.
  refine ⟨fun _ => 0, ?_, ?_⟩
  · -- ContMDiff ω of the constant zero function.
    exact contMDiff_const
  · -- om.eval x = mfderiv (const 0) x. RHS = 0 by mfderiv_const.
    -- LHS = 0 because om = 0 (HolomorphicOneForm RS subsingleton).
    intro x
    have h_om_zero : om = 0 := Subsingleton.elim _ _
    rw [h_om_zero]
    rw [mfderiv_const]
    -- Goal: HolomorphicOneForm.eval (0 : HolomorphicOneForm RS) x = 0.
    -- Apply HolomorphicOneForm.eval_zero.
    exact HolomorphicOneForm.eval_zero x

/-- **Item 14 on RS via the atomic 2-input form.** Third independent
unconditional proof of `genus RS = 0 ↔ Nonempty (RS ≃ₜ S²)`,
constructed by plugging the unconditional discharges of both atoms
(`existsSimplePoleGermAtSomePoint_RiemannSphere` for the simple-pole
side, this file's `primitiveExists_RiemannSphere` for the
primitive-existence side) into the atomic 2-input form. -/
theorem genus_eq_zero_iff_homeo_riemannSphere_via_atomic :
    JacobianChallenge.genus JacobianChallenge.RiemannSphere = 0 ↔
      Nonempty (JacobianChallenge.RiemannSphere ≃ₜ JacobianChallenge.StandardS2) :=
  JacobianChallenge.genus_eq_zero_iff_homeo_from_simplePoleGerm_and_primitiveExistence
    JacobianChallenge.MeromorphicFunctionField.existsSimplePoleGermAtSomePoint_RiemannSphere
    primitiveExists_RiemannSphere

end RiemannSphere

end JacobianChallenge

end
