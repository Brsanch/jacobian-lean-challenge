/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SourceFiberPathIntegrandChainExpand
import JacobianChallenge.Manifold.CotangentPullbackAtApply

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Per-fiber integrand as a `cotangentPullbackAt`-apply expression

Combines `sourceFiberPath_integrand_chain_expand` with
`applyCotangent_cotangentPullbackAt` to repackage the per-fiber-point
integrand into a cotangent-pullback expression:

```
integrand (sourceFiberPath x) ω t
  = applyCotangent (cotangentPullbackAt sheet_x.g (β(σ t)) ω)
      (mfderiv β (σ t) (mfderiv σ t 1))
```

The right-hand side is the pullback of `ω` by `sheet_x.g` (a covector at
`β(σ t)`), paired with the velocity of `β ∘ σ` at `t` (a tangent vector
at `β(σ t)`).

Summing over `x ∈ sourceFiber` will (in a future chip) give

```
Σ_x integrand(...) = applyCotangent (Σ_x cotangentPullbackAt sheet_x.g v ω) (β'(σ t) σ'(t))
                   = applyCotangent (traceAt(ω) at v) (β'(σ t) σ'(t))
```

modulo the bijection between `sourceFiber` (preimages of `β(0)`) and
`fiberFinset hv` (preimages of `β(σ t)`).

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

/-- **Per-fiber-point integrand as a `cotangentPullbackAt`-apply.** -/
theorem sourceFiberPath_integrand_eq_cotangentPullbackAt_apply
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    {x : X} (hx : f.toRiemannSphere x = β 0)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ t ∈ Ioo (0 : ℝ) δ,
        (∀ h_sheet_g_real : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
            (f.localSheetData_at_regular hnc
              (f.mem_regularSet_of_preimage_regularValue
                (hβ_reg 0 ⟨le_refl _, by norm_num⟩) hx)).g
            (β (Real.smoothTransition t)),
          (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).integrand om t
            = SmoothPath.applyCotangent
                (cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
                  (f.localSheetData_at_regular hnc
                    (f.mem_regularSet_of_preimage_regularValue
                      (hβ_reg 0 ⟨le_refl _, by norm_num⟩) hx)).g
                  (β (Real.smoothTransition t)) om)
                ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (Real.smoothTransition t) :
                    ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
                      (β (Real.smoothTransition t)))
                  ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.smoothTransition t :
                      ℝ →L[ℝ] ℝ) (1 : ℝ)))) := by
  obtain ⟨δ, hδ_pos, hδ_le, hδ_expand⟩ :=
    f.sourceFiberPath_integrand_chain_expand hnc hβ_smooth hβ_reg hx om
  refine ⟨δ, hδ_pos, hδ_le, fun t ht h_sheet_g_real => ?_⟩
  rw [hδ_expand t ht h_sheet_g_real]
  -- Rewrite `applyCotangent (ω(sheet.g v)) (mfderiv sheet.g v w) =
  --          applyCotangent (cotangentPullbackAt sheet.g v ω) w`
  exact (applyCotangent_cotangentPullbackAt
    (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
    (f.localSheetData_at_regular hnc
      (f.mem_regularSet_of_preimage_regularValue
        (hβ_reg 0 ⟨le_refl _, by norm_num⟩) hx)).g
    (β (Real.smoothTransition t)) om
    ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (Real.smoothTransition t))
      ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.smoothTransition t) (1 : ℝ)))).symm

end MeromorphicNonzero

end JacobianChallenge

end
