/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.IntegrandContinuousAlongBetaFStarOmega
import JacobianChallenge.Manifold.ApplyCotangentContinuity

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `IntegrandContinuousAlongBeta` from factor continuities

This file composes the two previously landed reductions —

* `integrandContinuousAlongBeta_of_fStarOmega_pairing_continuousOn`
  (kills the dependent `if-then-else`), and
* `SmoothPath.continuousOn_applyCotangent` (bilinear `clm_apply`
  continuity through `cotangentEquiv`)

— into a single **factor-decomposed** entry point for the discharge of
`MeromorphicNonzero.IntegrandContinuousAlongBeta`.

The downstream caller need only exhibit:

1. **Trace-factor continuity** —
   `ContinuousOn (fun s => (cotangentEquiv (fStarOmega hnc om (β s)) : ℂ →L[ℝ] ℝ)) (Icc 0 1)`.

2. **Velocity-factor continuity** —
   `ContinuousOn (fun s => ((mfderiv β s) 1 : ℂ)) (Icc 0 1)`.

Both are plain `ContinuousOn` statements about concrete functions
(no dependent `if`, no fresh predicates). The first is the analytic
core of the f-4/f-5 packaging (smoothness of `fStarOmega` as a section
on `regularValueSet`); the second is the bundle-trivialised velocity
continuity for a smooth `β : ℝ → RiemannSphere`.

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

/-- **Factor-decomposed entry point** for `IntegrandContinuousAlongBeta`.

Given continuity on `Icc 0 1` of (i) the `fStarOmega`-trace covector
viewed through `cotangentEquiv`, and (ii) the velocity scalar
`mfderiv β · 1`, the named hypothesis
`IntegrandContinuousAlongBeta hnc hβ_smooth hβ_reg om` holds. -/
theorem integrandContinuousAlongBeta_of_factor_continuousOn
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ s ∈ Icc (0 : ℝ) 1, β s ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    (h_trace : ContinuousOn
      (fun s : ℝ =>
        (SmoothPath.cotangentEquiv (f.fStarOmega hnc om (β s)) : ℂ →L[ℝ] ℝ))
      (Icc (0 : ℝ) 1))
    (h_vel : ContinuousOn
      (fun s : ℝ =>
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s :
            ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (β s)) (1 : ℝ) : ℂ))
      (Icc (0 : ℝ) 1)) :
    f.IntegrandContinuousAlongBeta hnc hβ_smooth hβ_reg om := by
  -- Step 1: assemble the bilinear `applyCotangent` continuity from the two
  --         factor continuities via `SmoothPath.continuousOn_applyCotangent`.
  have h_pair :
      ContinuousOn
        (fun s : ℝ =>
          SmoothPath.applyCotangent
            (f.fStarOmega hnc om (β s))
            ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s :
                ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (β s)) (1 : ℝ)))
        (Icc (0 : ℝ) 1) :=
    SmoothPath.continuousOn_applyCotangent
      (γ := β)
      (φ := fun s => f.fStarOmega hnc om (β s))
      (v := fun s =>
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s :
            ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (β s)) (1 : ℝ)))
      h_trace h_vel
  -- Step 2: discharge `IntegrandContinuousAlongBeta` via the `fStarOmega`
  --         pairing form (kills the dependent `if`).
  exact f.integrandContinuousAlongBeta_of_fStarOmega_pairing_continuousOn
    hnc hβ_smooth hβ_reg om h_pair

end MeromorphicNonzero

end JacobianChallenge

end
