/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartContainedLoopBridgeFromPointwise

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # `complexChainPeriod (single γ) = ∫ (om.eval γ.ambient) γ.velocity`
for ANY smooth path `γ` (no loop hypothesis)

`complexChainPeriod_single_eq_complex_integral` in
`ChartContainedLoopBridgeFromPointwise.lean` is currently scoped to a
`ChartContainedClosedLoop` data bundle. Its proof, however, doesn't
use the loop property (`γ.src = γ.tgt`) or the chart-containment
hypotheses — it's purely structural:

  `complexChainPeriod (single γ) α
     = (∫ γ.integrand (realComponent α)) + I * (∫ γ.integrand (imagComponent α))
     = ∫ (re ((om.eval γ.ambient) γ.velocity)) + I * (∫ im (...))
     = ∫ (re + I * im) = ∫ (om.eval γ.ambient) γ.velocity`.

This file ships the **path-only generalization**: given any smooth
path `γ` and any holomorphic 1-form `α : HolomorphicOneForm X`, with
the ℂ-valued integrand `t ↦ (α.eval (γ.ambient t)) (γ.velocity t)`
continuous on `[0, 1]`, the same identity holds.

This is the **structural half** of the chip-B chart-pulled identity
(`chartLocalPrimitive φ y om x = ∫ chart-coord integrand`) for
`γ := linearInChartSegment φ y x` (which is NOT a loop in general).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex MeasureTheory intervalIntegral

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Path-only integrand identifications (no `ChartContainedClosedLoop`) -/

/-- Path-only generalization of `integrand_realComponent`. -/
lemma integrand_realComponent_general
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) (α : HolomorphicOneForm X) (t : ℝ) :
    γ.integrand (realComponent α) t
      = ((α.eval (γ.ambient t)) (γ.velocity t)).re := by
  unfold SmoothPath.integrand
  exact ChartContainedClosedLoop.applyCotangent_realComponent
    α (γ.ambient t) (γ.velocity t)

/-- Path-only generalization of `integrand_imagComponent`. -/
lemma integrand_imagComponent_general
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) (α : HolomorphicOneForm X) (t : ℝ) :
    γ.integrand (imagComponent α) t
      = ((α.eval (γ.ambient t)) (γ.velocity t)).im := by
  unfold SmoothPath.integrand
  exact ChartContainedClosedLoop.applyCotangent_imagComponent
    α (γ.ambient t) (γ.velocity t)

/-! ## Structural bridge for arbitrary smooth paths -/

/-- **Structural bridge: `complexChainPeriod (single γ) α = ∫ (om.eval γ.ambient) γ.velocity`**
for any smooth path `γ`, under continuity of the ℂ-valued integrand on
`[0, 1]`.

Path-only generalization of
`ChartContainedClosedLoop.complexChainPeriod_single_eq_complex_integral`.
The proof is structurally identical — it expands `complexChainPeriod`
via `realComponent + I * imagComponent`, applies `SmoothChain.integrate_single`
twice, identifies the integrands with `re` / `im` of the holomorphic
evaluation, and combines via the pointwise identity
`(re : ℂ) + I * (im : ℂ) = z`. The loop hypothesis is unused. -/
theorem complexChainPeriod_single_eq_complex_integral_of_path
    (γ : SmoothPath 𝓘(ℝ, ℂ) X)
    (α : HolomorphicOneForm X)
    (h_cont : ContinuousOn
      (fun t : ℝ => (α.eval (γ.ambient t)) (γ.velocity t))
      (Set.Icc (0 : ℝ) 1)) :
    complexChainPeriod (SmoothChain.single γ) α
      = ∫ t in (0 : ℝ)..1, (α.eval (γ.ambient t)) (γ.velocity t) := by
  -- Establish integrability of the real and imaginary parts on `[0, 1]`.
  have h_cont_re : ContinuousOn
      (fun t : ℝ => ((α.eval (γ.ambient t)) (γ.velocity t)).re)
      (Set.Icc (0 : ℝ) 1) :=
    Complex.continuous_re.continuousOn.comp h_cont (Set.mapsTo_image _ _)
  have h_cont_im : ContinuousOn
      (fun t : ℝ => ((α.eval (γ.ambient t)) (γ.velocity t)).im)
      (Set.Icc (0 : ℝ) 1) :=
    Complex.continuous_im.continuousOn.comp h_cont (Set.mapsTo_image _ _)
  have h_re_int : IntervalIntegrable
      (fun t : ℝ => ((α.eval (γ.ambient t)) (γ.velocity t)).re)
      MeasureTheory.volume 0 1 :=
    h_cont_re.intervalIntegrable_of_Icc zero_le_one
  have h_im_int : IntervalIntegrable
      (fun t : ℝ => ((α.eval (γ.ambient t)) (γ.velocity t)).im)
      MeasureTheory.volume 0 1 :=
    h_cont_im.intervalIntegrable_of_Icc zero_le_one
  -- Unfold `complexChainPeriod` and `SmoothChain.integrate_single`.
  show ((SmoothChain.integrate (SmoothChain.single γ) (realComponent α) : ℝ) : ℂ)
    + Complex.I * ((SmoothChain.integrate (SmoothChain.single γ) (imagComponent α) : ℝ) : ℂ)
    = ∫ t in (0 : ℝ)..1, (α.eval (γ.ambient t)) (γ.velocity t)
  rw [SmoothChain.integrate_single, SmoothChain.integrate_single]
  -- Rewrite `γ.integrate (·)` as the explicit `∫ γ.integrand`.
  show ((∫ t in (0 : ℝ)..1, γ.integrand (realComponent α) t : ℝ) : ℂ)
      + Complex.I *
        ((∫ t in (0 : ℝ)..1, γ.integrand (imagComponent α) t : ℝ) : ℂ)
    = ∫ t in (0 : ℝ)..1, (α.eval (γ.ambient t)) (γ.velocity t)
  -- Rewrite real-valued integrands via the re/im identifications.
  rw [intervalIntegral.integral_congr (g :=
        fun t => ((α.eval (γ.ambient t)) (γ.velocity t)).re)
        (fun t _ => integrand_realComponent_general γ α t),
      intervalIntegral.integral_congr (g :=
        fun t => ((α.eval (γ.ambient t)) (γ.velocity t)).im)
        (fun t _ => integrand_imagComponent_general γ α t)]
  -- Push ℝ → ℂ casts inside the integrals.
  rw [show ((∫ t in (0 : ℝ)..1,
              ((α.eval (γ.ambient t)) (γ.velocity t)).re : ℝ) : ℂ)
        = ∫ t in (0 : ℝ)..1,
            ((((α.eval (γ.ambient t)) (γ.velocity t)).re : ℝ) : ℂ)
        from (intervalIntegral.integral_ofReal
          (f := fun t => ((α.eval (γ.ambient t)) (γ.velocity t)).re)).symm]
  rw [show ((∫ t in (0 : ℝ)..1,
              ((α.eval (γ.ambient t)) (γ.velocity t)).im : ℝ) : ℂ)
        = ∫ t in (0 : ℝ)..1,
            ((((α.eval (γ.ambient t)) (γ.velocity t)).im : ℝ) : ℂ)
        from (intervalIntegral.integral_ofReal
          (f := fun t => ((α.eval (γ.ambient t)) (γ.velocity t)).im)).symm]
  -- Pull `I *` into the integrand.
  rw [show Complex.I *
        (∫ t in (0 : ℝ)..1,
            ((((α.eval (γ.ambient t)) (γ.velocity t)).im : ℝ) : ℂ))
        = ∫ t in (0 : ℝ)..1,
            Complex.I *
              ((((α.eval (γ.ambient t)) (γ.velocity t)).im : ℝ) : ℂ)
        from (intervalIntegral.integral_const_mul (μ := MeasureTheory.volume)
          (a := (0 : ℝ)) (b := 1) Complex.I
          (fun t => ((((α.eval (γ.ambient t)) (γ.velocity t)).im : ℝ)
                      : ℂ))).symm]
  -- ℂ-valued integrability of the casts.
  have h_re_int' : IntervalIntegrable
      (fun t => ((((α.eval (γ.ambient t)) (γ.velocity t)).re : ℝ) : ℂ))
      MeasureTheory.volume 0 1 := by
    have h_ofReal : Continuous ((fun (r : ℝ) => (r : ℂ))) := Complex.continuous_ofReal
    have h_cast : ContinuousOn
        (fun t : ℝ => ((((α.eval (γ.ambient t)) (γ.velocity t)).re : ℝ) : ℂ))
        (Set.Icc (0 : ℝ) 1) :=
      h_ofReal.continuousOn.comp h_cont_re (Set.mapsTo_image _ _)
    exact h_cast.intervalIntegrable_of_Icc zero_le_one
  have h_im_int' : IntervalIntegrable
      (fun t => Complex.I *
        ((((α.eval (γ.ambient t)) (γ.velocity t)).im : ℝ) : ℂ))
      MeasureTheory.volume 0 1 := by
    have h_ofReal : Continuous ((fun (r : ℝ) => (r : ℂ))) := Complex.continuous_ofReal
    have h_cast : ContinuousOn
        (fun t : ℝ => ((((α.eval (γ.ambient t)) (γ.velocity t)).im : ℝ) : ℂ))
        (Set.Icc (0 : ℝ) 1) :=
      h_ofReal.continuousOn.comp h_cont_im (Set.mapsTo_image _ _)
    exact ((continuousOn_const (c := Complex.I)).mul h_cast).intervalIntegrable_of_Icc
      zero_le_one
  -- Combine the two interval integrals via `integral_add`.
  rw [← intervalIntegral.integral_add h_re_int' h_im_int']
  -- Pointwise: `(↑z.re : ℂ) + I * (↑z.im : ℂ) = z`.
  refine intervalIntegral.integral_congr ?_
  intro t _
  have h := Complex.re_add_im ((α.eval (γ.ambient t)) (γ.velocity t))
  show ((((α.eval (γ.ambient t)) (γ.velocity t)).re : ℝ) : ℂ)
        + Complex.I *
          ((((α.eval (γ.ambient t)) (γ.velocity t)).im : ℝ) : ℂ)
      = (α.eval (γ.ambient t)) (γ.velocity t)
  rw [mul_comm Complex.I _]
  exact h

end JacobianChallenge

end
