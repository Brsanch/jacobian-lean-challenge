/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SourceFiberPathIntegrandPullback

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Sum-over-sourceFiber: `applyCotangent` distribution over the finite sum

Pure structural identity: the `applyCotangent` operation is `ℝ`-linear
in the covector argument, hence

```
∑_{p ∈ sourceFiber.attach} applyCotangent (φ p) v
  = applyCotangent (∑_{p} φ p) v
```

is `applyCotangent_finset_sum` (in `CotangentPullbackAtApply.lean`)
specialised to the per-fiber covector
`cotangentPullbackAt sheet_p.g (β(σ t)) ω`.

This chip packages the structural identity. The (richer)
"`Σ_{p ∈ sourceFiber} integrand(sourceFiberPath p) ω t =
applyCotangent (Σ φ p) v`" identity requires the per-fiber chip's
`δ`-existential to be packaged uniformly across the (finite) sourceFiber
— handled in a downstream chip via `Finset.min`-style δ packaging.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`applyCotangent` distributes over the sourceFiber sum of
`cotangentPullbackAt` covectors.** Specialisation of
`applyCotangent_finset_sum`. -/
theorem applyCotangent_sourceFiber_sum_cotangentPullbackAt
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    {t : ℝ}
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    (v : ℝ) :
    let hβ0_reg : β 0 ∈ f.regularValueSet :=
      hβ_reg 0 ⟨le_refl _, by norm_num⟩
    let velocity_at_t : TangentSpace 𝓘(ℝ, ℂ) (β (Real.smoothTransition t)) :=
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (Real.smoothTransition t) :
          ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
            (β (Real.smoothTransition t)))
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.smoothTransition t :
            ℝ →L[ℝ] ℝ) v)
    (∑ p ∈ (f.sourceFiber hβ0_reg).attach,
        SmoothPath.applyCotangent
          (cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
            (f.localSheetData_at_regular hnc
              (f.mem_regularSet_of_preimage_regularValue
                hβ0_reg
                ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property))).g
            (β (Real.smoothTransition t)) om)
          velocity_at_t)
      = SmoothPath.applyCotangent
          (∑ p ∈ (f.sourceFiber hβ0_reg).attach,
            cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
              (f.localSheetData_at_regular hnc
                (f.mem_regularSet_of_preimage_regularValue
                  hβ0_reg
                  ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property))).g
              (β (Real.smoothTransition t)) om)
          velocity_at_t := by
  intro hβ0_reg velocity_at_t
  exact (applyCotangent_finset_sum (I' := 𝓘(ℝ, ℂ)) (Y := RiemannSphere) _ _ _).symm

end MeromorphicNonzero

end JacobianChallenge

end
