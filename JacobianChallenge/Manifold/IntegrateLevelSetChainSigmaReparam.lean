/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.IntegrandSigmaSmulFactor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # σ-reparametrisation of the integrate-levelSetChain integral

The headline `integrate_levelSetChain_eq_traceAt_integral_smul`
(`IntegrandSigmaSmulFactor.lean`) gives:

```
SmoothChain.integrate (f.levelSetChain hnc hβ_smooth hβ_reg) om
  = ∫ t in 0..1, derivσ(t) *
      applyCotangent (traceAt … (β(σ t)) om) (mfderiv β (σ t) 1)
```

where `σ := Real.smoothTransition` is the smooth transition function
`ℝ → ℝ` with `σ 0 = 0`, `σ 1 = 1`.

This file applies the **change of variables `s = σ(t)`** via
`intervalIntegral.integral_deriv_smul_comp''` to obtain the cleaner
form

```
SmoothChain.integrate (f.levelSetChain hnc hβ_smooth hβ_reg) om
  = ∫ s in 0..1, applyCotangent (traceAt … (β s) om) (mfderiv β s 1)
```

The change-of-variables theorem requires:

1. `HasDerivAt σ` everywhere — from `Real.smoothTransition.contDiff`.
2. `ContinuousOn derivσ (uIcc 0 1)` — from `Real.smoothTransition.contDiff`
   (continuity of the second derivative; in particular the first
   derivative is continuous everywhere).
3. **Continuity of the new integrand** `g(s) := applyCotangent (traceAt
   … (β s) om) (mfderiv β s 1)` on `σ '' uIcc 0 1` — taken as a
   **named hypothesis** (`IntegrandContinuousAlongBeta`) here. Its
   discharge is the substantive analytic content of the `f-4` → `f-6`
   smoothness chips (mathlib pin lacks `ContMDiffOn.mfderiv` for the
   smoothness of `mfderiv g` as a function of base point, and lacks
   cotangent-pullback continuity infrastructure).

Once `IntegrandContinuousAlongBeta` is discharged, the
σ-reparametrisation closes unconditionally.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Continuity-along-β named hypothesis.** The integrand
`s ↦ applyCotangent (traceAt … (β s) om) (mfderiv β s 1)` is
continuous on `Icc 0 1`.

This is the content of the `f-6` smoothness packaging. Its discharge
requires unbuilt mathlib infrastructure (smoothness of `mfderiv` as a
function of base point on regular nbhds + cotangent-pullback
continuity packaging). Stating it as a named hypothesis isolates the
analytic gap so the σ-reparametrisation closes structurally. -/
def IntegrandContinuousAlongBeta
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (_hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ s ∈ Icc (0 : ℝ) 1, β s ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X) : Prop :=
  ContinuousOn
    (fun s : ℝ =>
      if hs : s ∈ Icc (0 : ℝ) 1 then
        SmoothPath.applyCotangent
          (f.traceAt hnc (hβ_reg s hs) om)
          ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s :
              ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (β s)) (1 : ℝ))
      else (0 : ℝ))
    (Icc (0 : ℝ) 1)

/-! ## σ smoothness helpers -/

private lemma sigma_hasDerivAt (x : ℝ) :
    HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x := by
  have h : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
  exact h.differentiableAt.hasDerivAt

private lemma sigma_deriv_continuous :
    Continuous (deriv Real.smoothTransition) := by
  have h := Real.smoothTransition.contDiff (n := 2)
  exact h.continuous_deriv (by
    -- 1 < 2 in ℕ∞; the condition for continuous_deriv is 1 ≤ n.
    decide)

/-- **σ '' [0,1] = [0,1].** -/
private lemma sigma_image_uIcc_subset :
    Real.smoothTransition '' Set.uIcc (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 := by
  intro y hy
  obtain ⟨t, _, rfl⟩ := hy
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-! ## σ-reparametrisation -/

/-- **σ-reparametrised integrate-levelSetChain identity.**

Conditional on `IntegrandContinuousAlongBeta` (the `f-6` continuity
hypothesis), the integrate-levelSetChain integral is the line
integral of `applyCotangent (traceAt …) (mfderiv β · 1)` along `β`
on `[0, 1]`.

Output form chosen so the integrand is the *if-guarded* function from
`IntegrandContinuousAlongBeta` (avoiding the pi-typed `hβ_reg s hs`
expression in the final integrand for clean composition with
downstream chips). -/
theorem integrate_levelSetChain_eq_traceAt_lineIntegral
    [DecidableEq X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ s ∈ Icc (0 : ℝ) 1, β s ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    (h_cont : f.IntegrandContinuousAlongBeta hnc hβ_smooth hβ_reg om) :
    SmoothChain.integrate (f.levelSetChain hnc hβ_smooth hβ_reg) om
      = ∫ s in (0 : ℝ)..1,
          (if hs : s ∈ Icc (0 : ℝ) 1 then
            SmoothPath.applyCotangent
              (f.traceAt hnc (hβ_reg s hs) om)
              ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s :
                  ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (β s)) (1 : ℝ))
           else (0 : ℝ)) := by
  classical
  -- Start from the σ-factor headline.
  rw [f.integrate_levelSetChain_eq_traceAt_integral_smul hnc hβ_smooth hβ_reg om]
  -- Apply intervalIntegral.integral_deriv_smul_comp.
  -- σ continuous on [0,1].
  have h_cont_σ : ContinuousOn Real.smoothTransition (Set.uIcc (0 : ℝ) 1) :=
    Real.smoothTransition.continuous.continuousOn
  -- HasDerivWithinAt σ derivσ Ioi at every interior point.
  have h_deriv :
      ∀ x ∈ Ioo (min (0:ℝ) 1) (max 0 1),
        HasDerivWithinAt Real.smoothTransition (deriv Real.smoothTransition x) (Ioi x) x := by
    intro x _
    exact (sigma_hasDerivAt x).hasDerivWithinAt
  -- ContinuousOn derivσ uIcc.
  have h_deriv_cont :
      ContinuousOn (deriv Real.smoothTransition) (Set.uIcc (0 : ℝ) 1) :=
    sigma_deriv_continuous.continuousOn
  -- The new integrand: the if-guarded version.
  set g : ℝ → ℝ := fun s =>
    if hs : s ∈ Icc (0 : ℝ) 1 then
      SmoothPath.applyCotangent
        (f.traceAt hnc (hβ_reg s hs) om)
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s :
            ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (β s)) (1 : ℝ))
    else (0 : ℝ) with hg_def
  -- ContinuousOn g (σ '' uIcc 0 1) ← ContinuousOn g (Icc 0 1) restricted.
  have h_g_cont_image :
      ContinuousOn g (Real.smoothTransition '' Set.uIcc (0 : ℝ) 1) :=
    h_cont.mono sigma_image_uIcc_subset
  -- Change of variables. Use the `'`-version (only requires ContinuousOn g
  -- on the image f '' [a, b]) via the HasDerivAt-on-uIcc form; this is a
  -- straightforward consequence of `integral_deriv_smul_comp'`.
  have h_cov := intervalIntegral.integral_deriv_smul_comp'
    (a := (0 : ℝ)) (b := (1 : ℝ))
    (f := Real.smoothTransition) (f' := deriv Real.smoothTransition) (g := g)
    (fun x _ => sigma_hasDerivAt x)
    h_deriv_cont h_g_cont_image
  -- Rewrite σ 0 = 0, σ 1 = 1.
  rw [Real.smoothTransition.zero, Real.smoothTransition.one] at h_cov
  -- LHS shape: σ-headline LHS = ∫ t in 0..1, derivσ(t) * (...)
  --          = ∫ t in 0..1, derivσ(t) • (g ∘ σ) t   (since `*` = `•` on ℝ)
  -- Convert by integral_congr (shape match between * and •-form of (g ∘ σ)).
  have h_inner : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      deriv Real.smoothTransition t *
      SmoothPath.applyCotangent
        (f.traceAt hnc
          (hβ_reg (Real.smoothTransition t)
            ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩) om)
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (Real.smoothTransition t) :
            ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
              (β (Real.smoothTransition t))) (1 : ℝ))
        = deriv Real.smoothTransition t • (g ∘ Real.smoothTransition) t := by
    intro t _
    -- g (σ t) reduces via the if-guard since σ t ∈ Icc 0 1.
    have h_σt_in : Real.smoothTransition t ∈ Icc (0:ℝ) 1 :=
      ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
    show deriv Real.smoothTransition t * _ = deriv Real.smoothTransition t • g (Real.smoothTransition t)
    rw [smul_eq_mul]
    congr 1
    -- Goal: applyCotangent (traceAt _ ⟨nonneg, le_one⟩) ... = g (σ t)
    -- where g (σ t) reduces via dif_pos h_σt_in.
    have hg_at : g (Real.smoothTransition t) =
        SmoothPath.applyCotangent
          (f.traceAt hnc (hβ_reg (Real.smoothTransition t) h_σt_in) om)
          ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (Real.smoothTransition t) :
              ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
                (β (Real.smoothTransition t))) (1 : ℝ)) := by
      simp only [hg_def, dif_pos h_σt_in]
    rw [hg_at]
    -- Both regularity proofs prove the same Prop; proof irrelevance closes
    -- the resulting goal automatically (rw closed it via rfl).
  rw [intervalIntegral.integral_congr h_inner]
  -- Now goal: ∫ t in 0..1, derivσ t • (g ∘ σ) t = ∫ s in 0..1, g s
  exact h_cov

end MeromorphicNonzero

end JacobianChallenge

end
