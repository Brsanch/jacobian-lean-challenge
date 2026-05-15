/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.IntegrateLevelSetChainEqTraceAt
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Factor out `derivσ(t)` from the integrand-trace identity

The integrated identity from `IntegrateLevelSetChainEqTraceAt` has the
RHS:

```
∫ t in 0..1, applyCotangent (traceAt … (β(σ t)) om)
    (mfderiv β (σ t) (mfderiv σ t 1))
```

The composite mfderiv unfolds: `mfderiv σ t 1 = derivσ(t)` (via
`mfderiv_eq_fderiv` on `ℝ → ℝ`), then
`mfderiv β (σ t) (derivσ(t)) = derivσ(t) • mfderiv β (σ t) 1` (by
ℝ-linearity of `mfderiv β (σ t) : ℝ →L[ℝ] TangentSpace _`). Then
`applyCotangent ω (c • v) = c * applyCotangent ω v` (by ContinuousLinearMap
ℝ-linearity). Net:

```
applyCotangent (traceAt … (β(σ t)) om) (mfderiv β (σ t) (mfderiv σ t 1))
  = derivσ(t) * applyCotangent (traceAt … (β(σ t)) om) (mfderiv β (σ t) 1)
```

This `derivσ(t)` factor is exactly the change-of-variables Jacobian
needed for the σ-reparametrisation step. The integrated identity
becomes:

```
SmoothChain.integrate (levelSetChain f β) om
  = ∫ t in 0..1, derivσ(t) *
      applyCotangent (traceAt … (β(σ t)) om) (mfderiv β (σ t) 1)
```

The σ-reparametrisation `s = σ t` (via `intervalIntegral.integral_comp_mul_deriv`)
then converts to:

```
  = ∫ s in 0..1, applyCotangent (traceAt … (β s) om) (mfderiv β s 1)
```

— but that requires the integrand-as-function-of-s to be continuous,
which is the f_*ω smoothness step (separate downstream work).

## What ships

* `MeromorphicNonzero.integrate_levelSetChain_eq_traceAt_integral_smul` —
  derivσ-factored form of the integrated identity.

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

/-- **Per-`t` integrand factorisation: `derivσ(t)` factor.** -/
private lemma applyCotangent_traceAt_mfderiv_smul_factor
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    (t : ℝ)
    (hβσt_reg : β (Real.smoothTransition t) ∈ f.regularValueSet) :
    SmoothPath.applyCotangent
        (f.traceAt hnc hβσt_reg om)
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (Real.smoothTransition t) :
            ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
              (β (Real.smoothTransition t)))
          ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.smoothTransition t :
              ℝ →L[ℝ] ℝ) (1 : ℝ)))
      = (deriv Real.smoothTransition t) *
        SmoothPath.applyCotangent
          (f.traceAt hnc hβσt_reg om)
          ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (Real.smoothTransition t) :
              ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
                (β (Real.smoothTransition t)))
            (1 : ℝ)) := by
  -- mfderiv σ t 1 = derivσ(t).
  have h_mfderiv_σ : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.smoothTransition t :
        ℝ →L[ℝ] ℝ) (1 : ℝ) = deriv Real.smoothTransition t := by
    rw [mfderiv_eq_fderiv]
    rfl
  rw [h_mfderiv_σ]
  -- Let φ := traceAt, ψ := mfderiv β (σ t) typed ℝ →L[ℝ] ℂ, c := derivσ(t).
  set φ := f.traceAt hnc hβσt_reg om with hφ_def
  set ψ : ℝ →L[ℝ] ℂ :=
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (Real.smoothTransition t) :
      ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (β (Real.smoothTransition t))) with hψ_def
  set c : ℝ := deriv Real.smoothTransition t with hc_def
  -- Step (a): ψ c = c • ψ 1.
  have h_psi_eq : ψ c = c • ψ (1 : ℝ) := by
    have h_eq : c = c • (1 : ℝ) := by rw [smul_eq_mul, mul_one]
    conv_lhs => rw [h_eq]
    exact ψ.map_smul c (1 : ℝ)
  -- Step (b): applyCotangent φ (c • w) = c * applyCotangent φ w.
  have h_apply_smul : ∀ w : ℂ,
      SmoothPath.applyCotangent φ (c • w) = c * SmoothPath.applyCotangent φ w := by
    intro w
    unfold SmoothPath.applyCotangent
    simp only [map_smul, smul_eq_mul]
  -- Combine: applyCotangent φ (ψ c) = applyCotangent φ (c • ψ 1) = c * applyCotangent φ (ψ 1).
  show SmoothPath.applyCotangent φ (ψ c) = c * SmoothPath.applyCotangent φ (ψ 1)
  conv_lhs => rw [h_psi_eq]
  exact h_apply_smul (ψ 1)

/-- **Integrated form with `derivσ` factor.**

Combines `integrate_levelSetChain_eq_traceAt_integral` with the
per-`t` `derivσ(t)` factorisation. -/
theorem integrate_levelSetChain_eq_traceAt_integral_smul
    [DecidableEq X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ s ∈ Icc (0 : ℝ) 1, β s ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X) :
    SmoothChain.integrate (f.levelSetChain hnc hβ_smooth hβ_reg) om
      = ∫ t in (0 : ℝ)..1,
          (deriv Real.smoothTransition t) *
          SmoothPath.applyCotangent
            (f.traceAt hnc
              (hβ_reg (Real.smoothTransition t)
                ⟨Real.smoothTransition.nonneg _,
                 Real.smoothTransition.le_one _⟩) om)
            ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (Real.smoothTransition t) :
                ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
                  (β (Real.smoothTransition t))) (1 : ℝ)) := by
  rw [f.integrate_levelSetChain_eq_traceAt_integral hnc hβ_smooth hβ_reg om]
  congr 1
  funext t
  exact f.applyCotangent_traceAt_mfderiv_smul_factor hnc hβ_smooth om t
    (hβ_reg (Real.smoothTransition t)
      ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩)

end MeromorphicNonzero

end JacobianChallenge

end
