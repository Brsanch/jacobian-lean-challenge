/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HodgeRiemannSphereInstance
import JacobianChallenge.Manifold.HodgeBiholomorphismTransport
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option diagnostics.threshold 100

/-! # Unconditional Hodge-side finite-dimensionality for the Riemann sphere

`Manifold/HodgeRiemannSphereInstance.lean` and
`Manifold/HodgeBiholomorphismTransport.lean` both ship discharges of
`HolomorphicOneFormFiniteDim` that take the open subsingleton input
`Subsingleton (HolomorphicOneForm RiemannSphere)`. With zz274
(`Manifold/RiemannSphereChartSCoeffOverlap.lean`) discharging that
instance unconditionally, the hypothesis is no longer needed.

This file ships:

* The unconditional finite-dimensionality
  `holomorphicOneFormFiniteDim_riemannSphere_unconditional` for the
  Riemann sphere itself.
* The transport version
  `holomorphicOneFormFiniteDim_of_transport_from_riemannSphere_unconditional`
  for an arbitrary `X` with a finite-dim transport from `RiemannSphere`.
* A discharge of the open `Prop`-only statement
  `holomorphicOneFormFiniteDim_riemannSphere_statement`.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-- **Unconditional finite-dimensionality for the Riemann sphere.**
`HolomorphicOneFormFiniteDim RiemannSphere` holds unconditionally, by
combining zz274's subsingleton instance with the linear-algebra
bridge `holomorphicOneFormFiniteDim_riemannSphere_of_subsingleton`. -/
theorem holomorphicOneFormFiniteDim_riemannSphere_unconditional :
    JacobianChallenge.HolomorphicOneFormFiniteDim
      JacobianChallenge.RiemannSphere :=
  holomorphicOneFormFiniteDim_riemannSphere_of_subsingleton
    (inferInstance :
      Subsingleton (HolomorphicOneForm JacobianChallenge.RiemannSphere))

/-- **Discharge of the named `Prop`-only statement
`holomorphicOneFormFiniteDim_riemannSphere_statement`.** Records the
unconditional finite-dimensionality at the `Prop` level for downstream
callers that thread `_statement`-shaped hypotheses. -/
theorem holomorphicOneFormFiniteDim_riemannSphere_statement_holds :
    holomorphicOneFormFiniteDim_riemannSphere_statement :=
  holomorphicOneFormFiniteDim_riemannSphere_unconditional

/-- **Unconditional discharge via finite-dim transport from the
Riemann sphere.** With zz274 supplying the
`Subsingleton (HolomorphicOneForm RiemannSphere)` ingredient, a transport
`HolomorphicOneFormFiniteDimTransport X RiemannSphere` is the *only*
remaining hypothesis required to establish
`HolomorphicOneFormFiniteDim X`. -/
theorem holomorphicOneFormFiniteDim_of_transport_from_riemannSphere_unconditional
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ⊤ X]
    (hT : HolomorphicOneFormFiniteDimTransport X
            JacobianChallenge.RiemannSphere) :
    JacobianChallenge.HolomorphicOneFormFiniteDim X :=
  holomorphicOneFormFiniteDim_of_transport_from_riemannSphere hT
    (inferInstance :
      Subsingleton (HolomorphicOneForm JacobianChallenge.RiemannSphere))

end RiemannSphere

end JacobianChallenge
