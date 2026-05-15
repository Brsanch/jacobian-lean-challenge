/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.GlobalIntegrandTraceIdentity
import JacobianChallenge.Manifold.MeromorphicNonzeroLevelSetIntegrate
import JacobianChallenge.Manifold.SmoothPathIntegrability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Integrated form of the global integrand-trace identity

Composes:
* `integrate_levelSetChain` (`(levelSetChain).integrate om = ∑ p,
  (sourceFiberPath p).integrate om`).
* `intervalIntegral.integral_finset_sum` (swap finite sum and integral).
* `global_integrand_eq_traceAt_apply` (per-`t` integrand-trace
  identity, holding on `Ioo 0 1`).
* `intervalIntegral.integral_congr_ae'` (boundary `{0, 1}` has measure
  zero).

Headline:

```
SmoothChain.integrate (levelSetChain f β) om
  = ∫ t in (0 : ℝ)..1,
      applyCotangent (traceAt f hnc (hβ_reg (σ t) _) om)
        (mfderiv β (σ t) (mfderiv σ t 1))
```

This is the integrated source-side equality with the traceAt-based
RHS. The next step (σ-reparametrisation) converts the integration
variable `t ↦ σ t = s ∈ [0, 1]` to give the natural line-integral form.

## What ships

* `MeromorphicNonzero.integrate_levelSetChain_eq_traceAt_integral` —
  the integrated form headline.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Integrated form of the global integrand-trace identity.** -/
theorem integrate_levelSetChain_eq_traceAt_integral
    [DecidableEq X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ s ∈ Icc (0 : ℝ) 1, β s ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X) :
    SmoothChain.integrate (f.levelSetChain hnc hβ_smooth hβ_reg) om
      = ∫ t in (0 : ℝ)..1,
          SmoothPath.applyCotangent
            (f.traceAt hnc
              (hβ_reg (Real.smoothTransition t)
                ⟨Real.smoothTransition.nonneg _,
                 Real.smoothTransition.le_one _⟩) om)
            ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (Real.smoothTransition t) :
                ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
                  (β (Real.smoothTransition t)))
              ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.smoothTransition t :
                  ℝ →L[ℝ] ℝ) (1 : ℝ))) := by
  classical
  set hβ0_reg : β 0 ∈ f.regularValueSet :=
    hβ_reg 0 ⟨le_refl _, by norm_num⟩ with hβ0_reg_def
  -- Step 1: Unfold (levelSetChain).integrate to ∑_p (sourceFiberPath p).integrate.
  rw [f.integrate_levelSetChain hnc hβ_smooth hβ_reg om]
  -- Step 2: Each (sourceFiberPath p).integrate = ∫ integrand.
  have h_per_p_int :
      ∀ p ∈ (f.sourceFiber hβ0_reg).attach,
        (f.sourceFiberPath hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).integrate om
        = ∫ t in (0 : ℝ)..1,
            (f.sourceFiberPath hnc hβ_smooth hβ_reg
              ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).integrand om t := by
    intro p _
    rfl
  rw [Finset.sum_congr rfl h_per_p_int]
  -- Step 3: Swap finite sum and interval integral.
  rw [← intervalIntegral.integral_finset_sum
    (s := (f.sourceFiber hβ0_reg).attach)
    (f := fun p t => (f.sourceFiberPath hnc hβ_smooth hβ_reg
      ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).integrand om t)
    (fun p _ => (f.sourceFiberPath hnc hβ_smooth hβ_reg
      ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).intervalIntegrable_integrand om)]
  -- Step 4: Apply integrand identity a.e. on Ioo 0 1 (boundary {1} ⊆ Ioc 0 1
  -- has measure zero).
  apply intervalIntegral.integral_congr_ae
  -- Goal: ∀ᵐ t ∂volume, t ∈ Ι 0 1 → … = …. Ι 0 1 = Ioc 0 1.
  have h_ne_one : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (1 : ℝ) := by
    rw [Filter.eventually_iff, mem_ae_iff]
    have h_eq : {x : ℝ | x ≠ (1 : ℝ)}ᶜ = {(1 : ℝ)} := by
      ext x; simp
    rw [h_eq, MeasureTheory.measure_singleton]
  filter_upwards [h_ne_one] with t ht_ne ht_uIoc
  -- Ι 0 1 = Ioc 0 1.
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht_uIoc
  -- t ∈ Ioc 0 1 and t ≠ 1, so t ∈ Ioo 0 1.
  have ht_Ioo : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨ht_uIoc.1, lt_of_le_of_ne ht_uIoc.2 ht_ne⟩
  exact f.global_integrand_eq_traceAt_apply hnc hβ_smooth hβ_reg om hβ0_reg ht_Ioo

end MeromorphicNonzero

end JacobianChallenge

end
