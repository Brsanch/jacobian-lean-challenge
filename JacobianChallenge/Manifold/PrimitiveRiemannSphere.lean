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

/-- `pathPrimitive` of the zero form is the zero function. -/
private lemma pathPrimitive_zero_form
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) RiemannSphere) (x₀ : RiemannSphere) :
    pathPrimitive h_conn x₀ (0 : HolomorphicOneForm RiemannSphere) = fun _ => 0 := by
  funext x
  unfold pathPrimitive
  rw [complexChainPeriod_zero_right]

/-- **PathPrimitiveSmoothness unconditional on RiemannSphere**: every om
is zero, so `pathPrimitive om` is the constant-zero function, trivially
`ContMDiff`. -/
theorem pathPrimitiveSmoothness_unconditional
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) RiemannSphere) (x₀ : RiemannSphere) :
    PathPrimitiveSmoothness h_conn x₀ := by
  intro om
  have hom : om = 0 := Subsingleton.elim om 0
  rw [hom, pathPrimitive_zero_form h_conn x₀]
  exact contMDiff_const

/-- **PathPrimitiveFTC unconditional on RiemannSphere**: every om is zero,
so `om.eval x = 0` and `mfderiv (pathPrimitive 0) x = mfderiv (const 0) x = 0`. -/
theorem pathPrimitiveFTC_unconditional
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) RiemannSphere) (x₀ : RiemannSphere) :
    PathPrimitiveFTC h_conn x₀ := by
  intro om x
  have hom : om = 0 := Subsingleton.elim om 0
  rw [hom, pathPrimitive_zero_form h_conn x₀]
  -- om.eval x = 0 (since om = 0).
  rw [HolomorphicOneForm.eval_zero]
  -- mfderiv of constant is zero.
  rw [mfderiv_const]
  rfl

end RiemannSphere

end JacobianChallenge

end
