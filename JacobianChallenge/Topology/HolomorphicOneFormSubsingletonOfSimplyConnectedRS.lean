/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.S2ImpliesGenus0FromSubsingletonHypothesis
import JacobianChallenge.Topology.Item14ForwardFromCompactConnected
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap
import JacobianChallenge.Manifold.RiemannSphereSimplePole

/-! # `HolomorphicOneFormSubsingletonOfSimplyConnected RiemannSphere` (unconditional)

On the Riemann sphere, `Subsingleton (HolomorphicOneForm RiemannSphere)`
is **unconditional** (via the chart-S-coefficient overlap argument in
`Manifold/RiemannSphereChartSCoeffOverlap.lean`). The
simply-connectedness premise of the named predicate
`HolomorphicOneFormSubsingletonOfSimplyConnected RS` is therefore
vacuous — it can be discharged without any topological input.

This file ships the unconditional discharge as a one-line wrapper for
the `s2ImpliesGenus0_from_subsingletonOfSimplyConnected` pipeline:
specialised to `X = RiemannSphere`, the chain reduces the reverse leg
of item 14 to **zero** classical inputs (since `SimplyConnectedS2` is
also unconditional and the analytic-subsingleton premise is too).

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

/-- **`HolomorphicOneFormSubsingletonOfSimplyConnected RiemannSphere` is
unconditional.** The simply-connectedness premise is vacuous because
`HolomorphicOneForm RiemannSphere` is a `Subsingleton` regardless of
any topological hypothesis (via the unconditional discharge in
`Manifold/RiemannSphereChartSCoeffOverlap.lean`). -/
theorem holomorphicOneFormSubsingletonOfSimplyConnected_riemannSphere :
    HolomorphicOneFormSubsingletonOfSimplyConnected RiemannSphere :=
  fun _ => inferInstance

/-- **`S2ImpliesGenus0 RiemannSphere` is unconditional.** Composes the
unconditional `holomorphicOneFormSubsingletonOfSimplyConnected_riemannSphere`
above with the prior session's `s2ImpliesGenus0_from_subsingletonOfSimplyConnected`
(which uses `simplyConnectedS2_holds` internally). Both classical inputs
to the simple-connectedness route to the reverse leg of item 14 are
**discharged unconditionally on RS**, so this theorem is the
specialisation to `X = RiemannSphere` of the reverse leg with **zero
external hypotheses**. -/
theorem s2ImpliesGenus0_riemannSphere : S2ImpliesGenus0 RiemannSphere :=
  s2ImpliesGenus0_from_subsingletonOfSimplyConnected RiemannSphere
    holomorphicOneFormSubsingletonOfSimplyConnected_riemannSphere

/-- **`Genus0ImpliesS2 RiemannSphere` is unconditional.** Composes
`genus0ImpliesS2_from_existsSimplePoleGerm` (which has
`[FiniteDimensional]` derived internally) with the unconditional
`existsSimplePoleGermAtSomePoint_RiemannSphere`. -/
theorem genus0ImpliesS2_riemannSphere : Genus0ImpliesS2 RiemannSphere :=
  genus0ImpliesS2_from_existsSimplePoleGerm RiemannSphere
    MeromorphicFunctionField.existsSimplePoleGermAtSomePoint_RiemannSphere

/-- **`SurfaceClassificationGenus RiemannSphere` is unconditional.**
Bundles both directions. -/
theorem surfaceClassificationGenus_riemannSphere :
    SurfaceClassificationGenus RiemannSphere where
  genus_zero_to_sphere := genus0ImpliesS2_riemannSphere
  sphere_to_genus_zero := s2ImpliesGenus0_riemannSphere

/-- **Item 14 specialised to RiemannSphere — unconditional biconditional.**
`genus RS = 0 ↔ Nonempty (RS ≃ₜ S²)`. Both directions discharge
unconditionally on RS (genus 0 is trivially true; the homeomorphism is
provided by the chip-arc). -/
theorem genus_eq_zero_iff_homeo_riemannSphere :
    JacobianChallenge.genus RiemannSphere = 0 ↔
      Nonempty (RiemannSphere ≃ₜ StandardS2) :=
  surfaceClassificationGenus_riemannSphere.toIff

end JacobianChallenge

end
