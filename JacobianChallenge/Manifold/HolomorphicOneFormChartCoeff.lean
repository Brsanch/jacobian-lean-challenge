/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneForm
import JacobianChallenge.Manifold.HolomorphicOneFormRealificationLinearity

/-! # Chart-at-`x` coefficient of a `HolomorphicOneForm X`

Generalises `RiemannSphere.chartNCoeff` (the north-chart coefficient of a
holomorphic 1-form on the Riemann sphere) to an arbitrary complex
1-manifold `X`. The carrier of a holomorphic 1-form at a point is a
continuous `ℂ`-linear map `ℂ →L[ℂ] ℂ`, completely determined by its value
at `1 : ℂ`. Pulling back along the canonical chart at `x` gives the
"coefficient of `dz`" function

  `chartCoeffAt om x : ℂ → ℂ`,
  `chartCoeffAt om x z = om.eval ((chartAt ℂ x).symm z) 1`,

defined on all of `ℂ` (well-defined as a Lean function; mathematically
meaningful only on `(chartAt ℂ x).target`).

The follow-up chip will package the analyticity of `chartCoeffAt om x`
on `(chartAt ℂ x).target` (the chart-image open set), via the existing
repo machinery (`cotangentSection_contMDiffAt_iff` +
`contDiff_omega_iff_analyticOnNhd`) that powers
`RiemannSphereChartNHolomorphy.chartNCoeff_contMDiff` in the RS case. The
analyticity is needed to feed `chartCircleIntegralOfFun_eq_zero_of_diffContOnCl`
(closed-form disk-Stokes / Cauchy-Goursat) into the closedness chain of
the `HolomorphicOneFormSubsingletonOfSimplyConnected` arc.

## What this file proves (no `sorry`, no `axiom`)

* `HolomorphicOneForm.chartCoeffAt` — the chart-at-`x` coefficient map.

* `chartCoeffAt_zero`, `chartCoeffAt_add`, `chartCoeffAt_neg`,
  `chartCoeffAt_sub`, `chartCoeffAt_smul` — pointwise linearity in `om`,
  same shape as `chartNCoeff_*` for the Riemann-sphere specialisation.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

namespace HolomorphicOneForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Chart-at-`x` coefficient.** The coefficient of `dz` of a holomorphic
1-form `om` in the canonical chart at `x`, defined as the value of the
cotangent functional at `1 : ℂ` pulled back along `(chartAt ℂ x).symm`.

Mathematically meaningful on `(chartAt ℂ x).target` (the chart image of
the chart domain); extended to all of `ℂ` as a Lean function by the
formula above. -/
def chartCoeffAt (om : HolomorphicOneForm X) (x : X) : ℂ → ℂ :=
  fun z => om.eval ((chartAt ℂ x).symm z) 1

/-! ### Pointwise linearity in `om` -/

@[simp]
theorem chartCoeffAt_zero (x : X) :
    chartCoeffAt (0 : HolomorphicOneForm X) x = 0 := by
  funext z
  simp [chartCoeffAt]

theorem chartCoeffAt_add (om₁ om₂ : HolomorphicOneForm X) (x : X) :
    chartCoeffAt (om₁ + om₂) x = chartCoeffAt om₁ x + chartCoeffAt om₂ x := by
  funext z
  simp [chartCoeffAt]

theorem chartCoeffAt_neg (om : HolomorphicOneForm X) (x : X) :
    chartCoeffAt (-om) x = -chartCoeffAt om x := by
  funext z
  simp [chartCoeffAt]

theorem chartCoeffAt_sub (om₁ om₂ : HolomorphicOneForm X) (x : X) :
    chartCoeffAt (om₁ - om₂) x = chartCoeffAt om₁ x - chartCoeffAt om₂ x := by
  funext z
  simp [chartCoeffAt]

theorem chartCoeffAt_smul (c : ℂ) (om : HolomorphicOneForm X) (x : X) :
    chartCoeffAt (c • om) x = c • chartCoeffAt om x := by
  funext z
  simp [chartCoeffAt, smul_eq_mul]

/-! ### Pointwise unfolding -/

@[simp]
theorem chartCoeffAt_apply (om : HolomorphicOneForm X) (x : X) (z : ℂ) :
    chartCoeffAt om x z = om.eval ((chartAt ℂ x).symm z) 1 := rfl

end HolomorphicOneForm

end JacobianChallenge

end
