/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.FStarOmegaPairingContinuity
import JacobianChallenge.Manifold.IntegrandContinuousAlongBetaFStarOmega
import JacobianChallenge.Manifold.IntegrateLevelSetChainSigmaReparam

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Unconditional `IntegrandContinuousAlongBeta`

Final discharge: combines

* `continuousAt_fStarOmega_pairing` —
  pointwise `ContinuousAt s₀` of the `fStarOmega`-pairing along `β`
  at any `s₀` with `β s₀ ∈ regularValueSet`.

* `integrandContinuousAlongBeta_of_fStarOmega_pairing_continuousOn` —
  reduction of the named hypothesis to `ContinuousOn` of the
  `fStarOmega`-pairing on `Icc 0 1`.

For `β` smooth with `β s ∈ regularValueSet` for all `s ∈ Icc 0 1`,
this yields a fully unconditional discharge of
`MeromorphicNonzero.IntegrandContinuousAlongBeta`.

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

/-- **`ContinuousOn (Icc 0 1)` of the `fStarOmega`-pairing along `β`.**

For `β : ℝ → RiemannSphere` smooth and regular on `Icc 0 1`, and
`om : SmoothOneForm 𝓘(ℝ, ℂ) X`, the pairing
`s ↦ applyCotangent (fStarOmega f hnc om (β s)) (mfderiv β s 1)`
is `ContinuousOn (Icc 0 1)`. Pointwise `ContinuousAt` at each
`s₀ ∈ Icc 0 1` via `continuousAt_fStarOmega_pairing` (using
`β s₀ ∈ regularValueSet` from `hβ_reg`), then `ContinuousAt.continuousWithinAt`. -/
theorem continuousOn_fStarOmega_pairing_Icc01
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ s ∈ Icc (0 : ℝ) 1, β s ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X) :
    ContinuousOn
      (fun s : ℝ => SmoothPath.applyCotangent
        (f.fStarOmega hnc om (β s))
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s) (1 : ℝ)))
      (Icc (0 : ℝ) 1) := by
  intro s₀ hs₀
  exact (f.continuousAt_fStarOmega_pairing hnc hβ_smooth om
    (hβ_reg s₀ hs₀)).continuousWithinAt

/-- **Unconditional `IntegrandContinuousAlongBeta`.**

For `β : ℝ → RiemannSphere` smooth and regular on `Icc 0 1`, and
`om : SmoothOneForm 𝓘(ℝ, ℂ) X`, the named hypothesis
`MeromorphicNonzero.IntegrandContinuousAlongBeta` holds. -/
theorem integrandContinuousAlongBeta_holds
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ s ∈ Icc (0 : ℝ) 1, β s ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X) :
    f.IntegrandContinuousAlongBeta hnc hβ_smooth hβ_reg om :=
  f.integrandContinuousAlongBeta_of_fStarOmega_pairing_continuousOn
    hnc hβ_smooth hβ_reg om
    (f.continuousOn_fStarOmega_pairing_Icc01 hnc hβ_smooth hβ_reg om)

end MeromorphicNonzero

end JacobianChallenge

end
