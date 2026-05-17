/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackGeneral

set_option linter.unusedSectionVars false

/-! # Pullback of holomorphic 1-forms along a constant map = 0

For a constant map `const y₀ : X → Y` (everywhere `y₀`), the pullback
of any holomorphic 1-form is the zero section. Reason: the manifold
derivative `mfderiv (const y₀) x` is the zero map (mathlib's
`mfderiv_const`), so `holCotangentPullbackAt (const y₀) x α = α(y₀) ∘ 0 = 0`.

This is the analytic-Jacobian-level functoriality witness for the
constant-curve-map case (used by
`JacobianAnalyticPushforwardLift.const` and the sister
`PeriodPairingMorphism.const` construction in follow-up chips).
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

namespace HolomorphicOneForm

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-- Pointwise: pullback along a constant map at any `x` is `0`. -/
theorem holCotangentPullbackAt_const (y₀ : Y) (x : X)
    (α : HolomorphicOneForm Y) :
    holCotangentPullbackAt (fun _ : X => y₀) x α = 0 := by
  show (α.toFun ((fun _ : X => y₀) x)).comp
      (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (fun _ : X => y₀) x) = 0
  rw [mfderiv_const]
  -- Composition with the zero CLM = 0.
  exact ContinuousLinearMap.comp_zero _

/-- Pullback of any holomorphic 1-form along a constant map is the zero
section. -/
theorem pullback_const (y₀ : Y) (α : HolomorphicOneForm Y) :
    pullback (fun _ : X => y₀) contMDiff_const α
      = (0 : HolomorphicOneForm X) := by
  apply ContMDiffSection.ext
  intro x
  show (pullback (fun _ : X => y₀) contMDiff_const α).toFun x = 0
  rw [pullback_apply, holCotangentPullbackAt_const]

/-- `pullbackLinearMap` along a constant map is the zero ℂ-linear map. -/
theorem pullbackLinearMap_const (y₀ : Y) :
    pullbackLinearMap (fun _ : X => y₀) contMDiff_const
      = (0 : HolomorphicOneForm Y →ₗ[ℂ] HolomorphicOneForm X) := by
  ext α
  show pullback (fun _ : X => y₀) contMDiff_const α = 0
  exact pullback_const y₀ α

end HolomorphicOneForm

end JacobianChallenge

end
