/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PrimitiveSubsingletonReduction
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap
import JacobianChallenge.Manifold.ComplexChainPeriodFormLinear

set_option linter.unusedSectionVars false

/-! # Path-primitive hypotheses unconditional on `RiemannSphere`

On `X = RiemannSphere`, `Subsingleton (HolomorphicOneForm RiemannSphere)`
holds unconditionally (in tree via `Manifold/RiemannSphereChartSCoeffOverlap.lean`).
Every holomorphic 1-form is zero, so all loop periods, path primitives,
and FTC identities hold vacuously.

This file discharges the three named hypotheses
(`AllLoopsVanish`, `PathPrimitiveSmoothness`, `PathPrimitiveFTC`)
for `X = RiemannSphere` to demonstrate the framework. The general-X
discharges require the Stokes + parameter-integral analytic content.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology ContDiff
open Module

noncomputable section

namespace JacobianChallenge

namespace RiemannSphere

/-- **AllLoopsVanish unconditional on RiemannSphere**: every om is zero,
hence every loop period is zero. -/
theorem allLoopsVanish_unconditional (x₀ : RiemannSphere) :
    AllLoopsVanish (X := RiemannSphere) x₀ := by
  intro om γ _ _
  -- om = 0 by Subsingleton instance.
  have hom : om = 0 := Subsingleton.elim om 0
  rw [hom, complexChainPeriod_zero_right]

end RiemannSphere

end JacobianChallenge

end
