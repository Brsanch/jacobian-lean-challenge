/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartContainedLoopVanishingDischarge
import JacobianChallenge.Manifold.HolomorphicOneFormRealComponentLinear
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Structural reduction of `ComplexChainPeriodEqChartIntegral_named`

This file discharges the **structural half** of the chart-coord-
integral identification for `complexChainPeriod (single γ) α` on a
chart-contained closed loop, namely:

    complexChainPeriod (single γ) α
      = ∫_0^1 (α.eval (γ.ambient t)) (γ.velocity t) dt           (∗)

Once (∗) is established, the bridge
`ComplexChainPeriodEqChartIntegral_named` reduces to the **pointwise
chart-pullback identity** `PointwiseChartEvalIdentity`: at each
`t ∈ [0,1]`,
    (α.eval (γ.ambient t)) (γ.velocity t)
      = α.localCoeff basePoint (chartPath t) · deriv chartPath t.

The pointwise identity is the substantive cotangent-bundle content
(coordChange of `α` applied to the chain rule for `chart ∘ γ.ambient`).
This file leaves it as a hypothesis.

## Headline

`complexChainPeriodEqChartIntegral_from_pointwise` — assuming the
pointwise chart-pullback identity (and continuity of the ℂ-valued
integrand `t ↦ (α.eval (γ.ambient t)) (γ.velocity t)` on `[0, 1]`),
the integral-level bridge `ComplexChainPeriodEqChartIntegral_named`
follows.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex MeasureTheory intervalIntegral

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace ChartContainedClosedLoop

/-! ## Pointwise integrand identification -/

/-- The pairing `applyCotangent (realComponent α x) v` equals the real
part of the holomorphic evaluation `((α.eval x) v).re`. -/
lemma applyCotangent_realComponent
    (α : HolomorphicOneForm X) (x : X) (v : ℂ) :
    SmoothPath.applyCotangent (realComponent α x) v
      = ((α.eval x) v).re := by
  unfold SmoothPath.applyCotangent
  -- `cotangentEquiv` is identity-on-data; `realComponent α x = α.realPart x`
  -- definitionally via `toFun = fun x => α.realPart x` of `realComponent`.
  change (α.realPart x) v = ((α.eval x) v).re
  exact HolomorphicOneForm.realPart_apply α x v

/-- The pairing `applyCotangent (imagComponent α x) v` equals the
imaginary part of the holomorphic evaluation `((α.eval x) v).im`. -/
lemma applyCotangent_imagComponent
    (α : HolomorphicOneForm X) (x : X) (v : ℂ) :
    SmoothPath.applyCotangent (imagComponent α x) v
      = ((α.eval x) v).im := by
  unfold SmoothPath.applyCotangent
  change (α.imagPart x) v = ((α.eval x) v).im
  exact HolomorphicOneForm.imagPart_apply α x v

/-! ## Integrand identification for `complexChainPeriod (single γ)` -/

/-- The path integrand of `realComponent α` along `γ` is the real part
of the ℂ-valued holomorphic evaluation along `γ`. -/
lemma integrand_realComponent
    (data : ChartContainedClosedLoop (X := X))
    (α : HolomorphicOneForm X) (t : ℝ) :
    data.γ.integrand (realComponent α) t
      = ((α.eval (data.γ.ambient t)) (data.γ.velocity t)).re := by
  unfold SmoothPath.integrand
  exact applyCotangent_realComponent α (data.γ.ambient t) (data.γ.velocity t)

/-- The path integrand of `imagComponent α` along `γ` is the imaginary
part of the ℂ-valued holomorphic evaluation along `γ`. -/
lemma integrand_imagComponent
    (data : ChartContainedClosedLoop (X := X))
    (α : HolomorphicOneForm X) (t : ℝ) :
    data.γ.integrand (imagComponent α) t
      = ((α.eval (data.γ.ambient t)) (data.γ.velocity t)).im := by
  unfold SmoothPath.integrand
  exact applyCotangent_imagComponent α (data.γ.ambient t) (data.γ.velocity t)

/-! ## Structural bridge: complexChainPeriod = ℂ-valued path integral -/

/-- **Structural bridge (under continuity of the ℂ-valued integrand).**
For a chart-contained closed loop and a holomorphic 1-form, with the
ℂ-valued path integrand
`t ↦ (α.eval (γ.ambient t)) (γ.velocity t)` continuous on `[0, 1]`,

    complexChainPeriod (SmoothChain.single γ) α
      = ∫_0^1 (α.eval (γ.ambient t)) (γ.velocity t) dt. -/
theorem complexChainPeriod_single_eq_complex_integral
    (data : ChartContainedClosedLoop (X := X))
    (α : HolomorphicOneForm X)
    (h_cont : ContinuousOn
      (fun t : ℝ => (α.eval (data.γ.ambient t)) (data.γ.velocity t))
      (Set.Icc (0 : ℝ) 1)) :
    complexChainPeriod (SmoothChain.single data.γ) α
      = ∫ t in (0 : ℝ)..1, (α.eval (data.γ.ambient t)) (data.γ.velocity t) := by
  -- Establish integrability of the real and imaginary parts on [0, 1].
  have h_cont_re : ContinuousOn
      (fun t : ℝ => ((α.eval (data.γ.ambient t)) (data.γ.velocity t)).re)
      (Set.Icc (0 : ℝ) 1) :=
    Complex.continuous_re.continuousOn.comp h_cont (Set.mapsTo_image _ _)
  have h_cont_im : ContinuousOn
      (fun t : ℝ => ((α.eval (data.γ.ambient t)) (data.γ.velocity t)).im)
      (Set.Icc (0 : ℝ) 1) :=
    Complex.continuous_im.continuousOn.comp h_cont (Set.mapsTo_image _ _)
  have h_re_int : IntervalIntegrable
      (fun t : ℝ => ((α.eval (data.γ.ambient t)) (data.γ.velocity t)).re)
      MeasureTheory.volume 0 1 :=
    h_cont_re.intervalIntegrable_of_Icc zero_le_one
  have h_im_int : IntervalIntegrable
      (fun t : ℝ => ((α.eval (data.γ.ambient t)) (data.γ.velocity t)).im)
      MeasureTheory.volume 0 1 :=
    h_cont_im.intervalIntegrable_of_Icc zero_le_one
  -- Unfold complexChainPeriod and chain.integrate_single.
  show ((SmoothChain.integrate (SmoothChain.single data.γ) (realComponent α) : ℝ) : ℂ)
    + Complex.I * ((SmoothChain.integrate (SmoothChain.single data.γ) (imagComponent α) : ℝ) : ℂ)
    = ∫ t in (0 : ℝ)..1, (α.eval (data.γ.ambient t)) (data.γ.velocity t)
  rw [SmoothChain.integrate_single, SmoothChain.integrate_single]
  -- Rewrite each `γ.integrate (·)` as the explicit `∫ γ.integrand`.
  show ((∫ t in (0 : ℝ)..1, data.γ.integrand (realComponent α) t : ℝ) : ℂ)
      + Complex.I *
        ((∫ t in (0 : ℝ)..1, data.γ.integrand (imagComponent α) t : ℝ) : ℂ)
    = ∫ t in (0 : ℝ)..1, (α.eval (data.γ.ambient t)) (data.γ.velocity t)
  -- Rewrite real-valued integrands via the re/im identifications.
  rw [intervalIntegral.integral_congr (g :=
        fun t => ((α.eval (data.γ.ambient t)) (data.γ.velocity t)).re)
        (fun t _ => integrand_realComponent data α t),
      intervalIntegral.integral_congr (g :=
        fun t => ((α.eval (data.γ.ambient t)) (data.γ.velocity t)).im)
        (fun t _ => integrand_imagComponent data α t)]
  -- Push ℝ → ℂ casts inside the integrals via `integral_ofReal`.
  rw [show ((∫ t in (0 : ℝ)..1,
              ((α.eval (data.γ.ambient t)) (data.γ.velocity t)).re : ℝ) : ℂ)
        = ∫ t in (0 : ℝ)..1,
            ((((α.eval (data.γ.ambient t)) (data.γ.velocity t)).re : ℝ) : ℂ)
        from (intervalIntegral.integral_ofReal
          (f := fun t => ((α.eval (data.γ.ambient t)) (data.γ.velocity t)).re)).symm]
  rw [show ((∫ t in (0 : ℝ)..1,
              ((α.eval (data.γ.ambient t)) (data.γ.velocity t)).im : ℝ) : ℂ)
        = ∫ t in (0 : ℝ)..1,
            ((((α.eval (data.γ.ambient t)) (data.γ.velocity t)).im : ℝ) : ℂ)
        from (intervalIntegral.integral_ofReal
          (f := fun t => ((α.eval (data.γ.ambient t)) (data.γ.velocity t)).im)).symm]
  -- Pull `I *` into the integrand via `integral_const_mul`.
  rw [show Complex.I *
        (∫ t in (0 : ℝ)..1,
            ((((α.eval (data.γ.ambient t)) (data.γ.velocity t)).im : ℝ) : ℂ))
        = ∫ t in (0 : ℝ)..1,
            Complex.I *
              ((((α.eval (data.γ.ambient t)) (data.γ.velocity t)).im : ℝ) : ℂ)
        from (intervalIntegral.integral_const_mul (μ := MeasureTheory.volume)
          (a := (0 : ℝ)) (b := 1) Complex.I
          (fun t => ((((α.eval (data.γ.ambient t)) (data.γ.velocity t)).im : ℝ)
                      : ℂ))).symm]
  -- Establish ℂ-valued integrability of the casts.
  have h_re_int' : IntervalIntegrable
      (fun t => ((((α.eval (data.γ.ambient t)) (data.γ.velocity t)).re : ℝ) : ℂ))
      MeasureTheory.volume 0 1 := by
    have : Continuous ((fun (r : ℝ) => (r : ℂ))) := Complex.continuous_ofReal
    have h_cont_re' : ContinuousOn
        (fun t : ℝ => ((((α.eval (data.γ.ambient t)) (data.γ.velocity t)).re
                          : ℝ) : ℂ))
        (Set.Icc (0 : ℝ) 1) :=
      this.continuousOn.comp h_cont_re (Set.mapsTo_image _ _)
    exact h_cont_re'.intervalIntegrable_of_Icc zero_le_one
  have h_im_int' : IntervalIntegrable
      (fun t => Complex.I *
        ((((α.eval (data.γ.ambient t)) (data.γ.velocity t)).im : ℝ) : ℂ))
      MeasureTheory.volume 0 1 := by
    have h_cont_im' : ContinuousOn
        (fun t : ℝ => Complex.I *
          ((((α.eval (data.γ.ambient t)) (data.γ.velocity t)).im : ℝ) : ℂ))
        (Set.Icc (0 : ℝ) 1) := by
      have h_ofReal : Continuous ((fun (r : ℝ) => (r : ℂ))) := Complex.continuous_ofReal
      have h_cast : ContinuousOn
          (fun t : ℝ => ((((α.eval (data.γ.ambient t)) (data.γ.velocity t)).im
                            : ℝ) : ℂ))
          (Set.Icc (0 : ℝ) 1) :=
        h_ofReal.continuousOn.comp h_cont_im (Set.mapsTo_image _ _)
      exact (continuousOn_const (c := Complex.I)).mul h_cast
    exact h_cont_im'.intervalIntegrable_of_Icc zero_le_one
  -- Combine the two interval integrals via `integral_add`.
  rw [← intervalIntegral.integral_add h_re_int' h_im_int']
  -- Pointwise: `(↑z.re : ℂ) + I * (↑z.im : ℂ) = z`.
  refine intervalIntegral.integral_congr ?_
  intro t _
  -- `Complex.re_add_im z : ↑z.re + ↑z.im * I = z`. Commute the `I` factor.
  have h := Complex.re_add_im ((α.eval (data.γ.ambient t)) (data.γ.velocity t))
  show ((((α.eval (data.γ.ambient t)) (data.γ.velocity t)).re : ℝ) : ℂ)
        + Complex.I *
          ((((α.eval (data.γ.ambient t)) (data.γ.velocity t)).im : ℝ) : ℂ)
      = (α.eval (data.γ.ambient t)) (data.γ.velocity t)
  rw [mul_comm Complex.I _]
  exact h

/-! ## Bridge from `PointwiseChartEvalIdentity` -/

/-- **Reduction: `ComplexChainPeriodEqChartIntegral_named` from
`PointwiseChartEvalIdentity` (+ ℂ-integrand continuity).**

Combines the structural bridge `complexChainPeriod_single_eq_complex_integral`
with the pointwise chart-pullback identity. -/
theorem complexChainPeriodEqChartIntegral_from_pointwise
    (data : ChartContainedClosedLoop (X := X))
    (α : HolomorphicOneForm X)
    (h_point : PointwiseChartEvalIdentity data α)
    (h_cont : ContinuousOn
      (fun t : ℝ => (α.eval (data.γ.ambient t)) (data.γ.velocity t))
      (Set.Icc (0 : ℝ) 1)) :
    ComplexChainPeriodEqChartIntegral_named data α := by
  unfold ComplexChainPeriodEqChartIntegral_named
  rw [complexChainPeriod_single_eq_complex_integral data α h_cont]
  refine intervalIntegral.integral_congr ?_
  intro t ht
  have ht_icc : t ∈ Set.Icc (0 : ℝ) 1 := by
    rwa [Set.uIcc_of_le zero_le_one] at ht
  exact h_point t ht_icc

end ChartContainedClosedLoop

end JacobianChallenge

end
