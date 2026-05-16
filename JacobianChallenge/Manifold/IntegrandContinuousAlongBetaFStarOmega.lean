/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.IntegrateLevelSetChainSigmaReparam
import JacobianChallenge.Manifold.MeromorphicNonzeroFStarOmegaDef

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `IntegrandContinuousAlongBeta` via the `fStarOmega` pairing

The named hypothesis `MeromorphicNonzero.IntegrandContinuousAlongBeta`
(see `IntegrateLevelSetChainSigmaReparam.lean`) is stated using a
dependent `if-then-else` on `s ∈ Icc 0 1` to type-check the
`hβ_reg s hs` regularity witness inside `traceAt`. This file exposes
the equivalent **un-guarded** form using `fStarOmega`, which extends
`traceAt` by `0` off the regular-value set:

```
∀ s ∈ Icc 0 1, applyCotangent (traceAt f hnc (hβ_reg s hs) om) (mfderiv β s 1)
            = applyCotangent (fStarOmega f hnc om (β s))      (mfderiv β s 1)
```

(via `fStarOmega_apply_of_regular`).

Consequently, downstream discharge of `IntegrandContinuousAlongBeta`
reduces to a plain `ContinuousOn` of the `fStarOmega`-pairing form,
**without** any dependent `if`. The dependent-if was a purely
syntactic obstacle in the σ-reparametrisation chip; this reduction
moves the analytic content into the cleaner non-dependent form.

No `sorry`, no `axiom`. -/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **EqOn bridge.** On `Icc 0 1`, the dependent-if integrand of
`IntegrandContinuousAlongBeta` agrees with the un-guarded pairing of
`fStarOmega` against the velocity. -/
theorem integrandContinuousAlongBeta_eqOn_fStarOmega_pairing
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_reg : ∀ s ∈ Icc (0 : ℝ) 1, β s ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X) :
    (Icc (0 : ℝ) 1).EqOn
      (fun s : ℝ =>
        if hs : s ∈ Icc (0 : ℝ) 1 then
          SmoothPath.applyCotangent
            (f.traceAt hnc (hβ_reg s hs) om)
            ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s :
                ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (β s)) (1 : ℝ))
        else (0 : ℝ))
      (fun s : ℝ =>
        SmoothPath.applyCotangent
          (f.fStarOmega hnc om (β s))
          ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s :
              ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (β s)) (1 : ℝ))) := by
  intro s hs
  -- Dispatch the `if` using `hs`.
  simp only [dif_pos hs]
  -- `fStarOmega_apply_of_regular` converts `fStarOmega` to `traceAt` at
  -- the regular value `β s`.
  rw [f.fStarOmega_apply_of_regular hnc om (hβ_reg s hs)]

/-- **Reduction.** `IntegrandContinuousAlongBeta` follows from
`ContinuousOn` of the un-guarded `fStarOmega` pairing on `Icc 0 1`. -/
theorem integrandContinuousAlongBeta_of_fStarOmega_pairing_continuousOn
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ s ∈ Icc (0 : ℝ) 1, β s ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    (h_cont : ContinuousOn
      (fun s : ℝ =>
        SmoothPath.applyCotangent
          (f.fStarOmega hnc om (β s))
          ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s :
              ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (β s)) (1 : ℝ)))
      (Icc (0 : ℝ) 1)) :
    f.IntegrandContinuousAlongBeta hnc hβ_smooth hβ_reg om := by
  -- `IntegrandContinuousAlongBeta` unfolds to the `if-then-else`
  -- `ContinuousOn`. Transfer via the `EqOn` bridge.
  unfold IntegrandContinuousAlongBeta
  refine h_cont.congr ?_
  intro s hs
  -- `ContinuousOn.congr` needs `EqOn g f S` (goal-side `=` source-side); the
  -- bridge already produces `if-form s = fStarOmega-form s`, which is what we
  -- need (`g = f`).
  exact f.integrandContinuousAlongBeta_eqOn_fStarOmega_pairing hnc hβ_reg om hs

end MeromorphicNonzero

end JacobianChallenge

end
