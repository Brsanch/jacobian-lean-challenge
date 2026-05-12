/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.S2ImpliesGenus0Discharge
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option diagnostics.threshold 100

/-! # Unconditional reduction of `S2ImpliesGenus0` to the linear-equivalence input

With `zz274` (`Manifold/RiemannSphereChartSCoeffOverlap.lean`) closing
`RiemannSphere.genus_RiemannSphere_statement` unconditionally, the
conditional discharge `s2ImpliesGenus0_of_linearEquiv` in
`Topology/S2ImpliesGenus0Discharge.lean` no longer needs its
`hRS : RiemannSphere.genus_RiemannSphere_statement` argument — we can
supply it from `genus_RiemannSphere_statement_holds`.

This file ships the resulting one-input form: given only a
`HolomorphicOneFormEquivRiemannSphere X` (or the underlying
`HolomorphicOneForm X ≃ₗ[ℂ] HolomorphicOneForm RiemannSphere`), the
reverse direction of `genus_eq_zero_iff_homeo` (challenge item 14)
follows. The only remaining open input is the uniformization-derived
linear equivalence itself.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

namespace JacobianChallenge

/-- **Unconditional reduction.** Given a `ℂ`-linear equivalence between
`HolomorphicOneForm X` and `HolomorphicOneForm RiemannSphere`, the genus
of `X` is zero. The Riemann-sphere genus-zero input is supplied
internally from `RiemannSphere.genus_RiemannSphere_statement_holds`
(`Manifold/RiemannSphereChartSCoeffOverlap.lean`). -/
theorem genus_zero_of_linearEquiv_RiemannSphere_unconditional
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (e : HolomorphicOneForm X ≃ₗ[ℂ]
          HolomorphicOneForm JacobianChallenge.RiemannSphere) :
    JacobianChallenge.genus X = 0 :=
  genus_zero_of_linearEquiv_RiemannSphere e
    RiemannSphere.genus_RiemannSphere_statement_holds

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Unconditional discharge of `S2ImpliesGenus0`.** Replaces
`s2ImpliesGenus0_of_linearEquiv`'s two-input form with a one-input
form: the `hRS : RiemannSphere.genus_RiemannSphere_statement`
hypothesis is supplied internally from the unconditional
`genus_RiemannSphere_statement_holds`. The remaining open input is
the linear equivalence
`HolomorphicOneFormEquivRiemannSphere X`, which classically follows
from uniformization plus pullback of 1-forms. -/
theorem s2ImpliesGenus0_of_linearEquiv_unconditional
    (hEq : HolomorphicOneFormEquivRiemannSphere X) :
    S2ImpliesGenus0 X :=
  s2ImpliesGenus0_of_linearEquiv hEq
    RiemannSphere.genus_RiemannSphere_statement_holds

/-- Specialisation taking the linear equivalence directly (not wrapped
in `Nonempty`). -/
theorem s2ImpliesGenus0_of_linearEquiv_unconditional'
    (e : HolomorphicOneForm X ≃ₗ[ℂ]
          HolomorphicOneForm JacobianChallenge.RiemannSphere) :
    S2ImpliesGenus0 X :=
  s2ImpliesGenus0_of_linearEquiv_unconditional ⟨e⟩

end JacobianChallenge
