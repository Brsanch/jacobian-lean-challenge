/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodPairingMorphism
import JacobianChallenge.Manifold.PeriodPairingDataFromSmoothCycle
import JacobianChallenge.Manifold.SmoothChainPush
import JacobianChallenge.Manifold.ContMDiffRealification

set_option linter.unusedSectionVars false

/-! # `PeriodPairingMorphism` from a curve map + adjunction certificate

For a holomorphic curve map `f : X → Y` and the canonical `PeriodPairingData`
`ofSmoothCycle X` / `ofSmoothCycle Y` (whose H1 carriers are
`SmoothCycle 𝓘(ℝ, ℂ) X` and `SmoothCycle 𝓘(ℝ, ℂ) Y`), the `cyclePush`
field of `PeriodPairingMorphism` is naturally given by
`SmoothCycle.pushHom f' hf'` where `f'` and `hf'` are the real-side
versions of `f` and its smoothness.

This file packages that construction as a **convenience constructor**:
given `f`, `hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f`, and the period-
adjunction certificate, produce the full `PeriodPairingMorphism` with
the canonical cyclePush.

The adjunction `complexPeriod (push γ) τ = complexPeriod γ (f^* τ)`
remains the genuinely-new analytic input — classically the
change-of-variables theorem for line integrals plus realification
compatibility.

## Net contribution

* `PeriodPairingMorphism.ofSmoothCycle f hf adjunction :
    PeriodPairingMorphism (PeriodPairingData.ofSmoothCycle X)
                          (PeriodPairingData.ofSmoothCycle Y)`
  Single-input form: f + adjunction certificate.

* Used downstream by `JacobianAnalyticPushforwardLift.ofMorphism` (sister
  `JacobianAnalyticPushforwardLiftOfMorphism.lean`) to assemble the full
  per-curve E+F lift bundle.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-- **`PeriodPairingMorphism` constructor for the smooth-cycle bundle.**
Given a holomorphic curve map `f` and the period-adjunction certificate,
produce the morphism with the canonical `SmoothCycle.pushHom` cycle
push. -/
noncomputable def PeriodPairingMorphism.ofSmoothCycle
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (adjunction :
      ∀ (γ : SmoothCycle 𝓘(ℝ, ℂ) X) (τ : HolomorphicOneForm Y),
        complexPeriod (SmoothCycle.pushHom f (ContMDiff.complex_to_real hf) γ) τ
          = complexPeriod γ (HolomorphicOneForm.pullback f hf τ)) :
    PeriodPairingMorphism (PeriodPairingData.ofSmoothCycle X)
                          (PeriodPairingData.ofSmoothCycle Y) where
  f := f
  contMDiff_f := hf
  cyclePush := SmoothCycle.pushHom f (ContMDiff.complex_to_real hf)
  adjunction := by
    intro γ τ
    -- Unfold pairing on `ofSmoothCycle`: it's `complexPeriodBilinear`,
    -- which (when applied to a cycle and a 1-form) is `complexPeriod`.
    show complexPeriodBilinear (SmoothCycle.pushHom f (ContMDiff.complex_to_real hf) γ) τ
      = complexPeriodBilinear γ (HolomorphicOneForm.pullback f hf τ)
    -- `complexPeriodBilinear γ τ` reduces to `complexPeriod γ τ`.
    -- Check the definitional unfolding.
    show complexPeriod (SmoothCycle.pushHom f (ContMDiff.complex_to_real hf) γ) τ
      = complexPeriod γ (HolomorphicOneForm.pullback f hf τ)
    exact adjunction γ τ

end JacobianChallenge

end
