/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SourceFiberPathAmbientSheetEq
import JacobianChallenge.Manifold.SheetGBetaSigmaChainRule

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Per-fiber-point integrand expansion via chain rule

Combines:

* `sourceFiberPath_integrand_eq_sheet_chain_locally`
  (`SourceFiberPathAmbientSheetEq.lean`) — on `Ioo 0 δ`,
  `integrand(sourceFiberPath x) ω t = applyCotangent (ω(sheet.g(β(σ t)))) (mfderiv (sheet.g ∘ β ∘ σ) t 1)`.

* `mfderiv_localSheet_g_beta_sigma_chain_at_base`
  (`SheetGBetaSigmaChainRule.lean`) — chain rule decomposing
  `mfderiv (sheet.g ∘ β ∘ σ) t 1` into
  `mfderiv sheet.g (β(σ t)) (mfderiv β (σ t) (mfderiv σ t 1))`.

Result: on `Ioo 0 δ` with `δ > 0` small enough that
`(sourceFiberPath x).ambient t = sheet.g (β (σ t))`, the integrand reads

```
integrand (sourceFiberPath x) ω t
  = applyCotangent (ω (sheet_x.g (β (σ t))))
      (mfderiv sheet_x.g (β(σ t)) (mfderiv β (σ t) (mfderiv σ t 1)))
```

The chain-rule hypothesis (smoothness of `sheet_x.g` at `β (σ t)`) is
discharged at `t = 0` via the base-point smoothness; for `t ∈ Ioo 0 δ`,
the smoothness needs propagation through an open neighborhood — see
`exists_contMDiffOn_localSheet_g_near_basePoint`. We take `δ` small
enough that `β(σ t)` lies in that neighborhood (smaller than the δ from
the ambient-equality lemma); a `min` of two δ's suffices, which is the
next-chip step.

This chip ships the version at `t = 0` (or any `t` with the
realified smoothness manually supplied). The open-neighborhood
extension is then mechanical.

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

/-- **Per-fiber-point integrand expansion via the chain rule.**
For each `t ∈ Ioo 0 δ` with `δ` from
`sourceFiberPath_ambient_eq_sheet_g_locally`, AND with realified
smoothness of `sheet_x.g` at `β (σ t)` available, the integrand of
`sourceFiberPath x` against `ω` factorizes through chain rule:

```
integrand (sourceFiberPath x) ω t
  = applyCotangent (ω (sheet_x.g (β (σ t))))
      (mfderiv sheet_x.g (β(σ t))
        (mfderiv β (σ t) (mfderiv σ t 1)))
```

The realified-smoothness hypothesis is the explicit input; in the
companion downstream chip the user takes `δ` smaller to land in the
open neighborhood from
`exists_contMDiffOn_localSheet_g_near_basePoint`. -/
theorem sourceFiberPath_integrand_chain_expand
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
                (om ((f.localSheetData_at_regular hnc
                    (f.mem_regularSet_of_preimage_regularValue
                      (hβ_reg 0 ⟨le_refl _, by norm_num⟩) hx)).g
                    (β (Real.smoothTransition t))))
                ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
                    (f.localSheetData_at_regular hnc
                      (f.mem_regularSet_of_preimage_regularValue
                        (hβ_reg 0 ⟨le_refl _, by norm_num⟩) hx)).g
                    (β (Real.smoothTransition t)) :
                  TangentSpace 𝓘(ℝ, ℂ) (β (Real.smoothTransition t))
                    →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
                      ((f.localSheetData_at_regular hnc
                        (f.mem_regularSet_of_preimage_regularValue
                          (hβ_reg 0 ⟨le_refl _, by norm_num⟩) hx)).g
                        (β (Real.smoothTransition t))))
                  ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (Real.smoothTransition t) :
                      ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
                        (β (Real.smoothTransition t)))
                    ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.smoothTransition t :
                        ℝ →L[ℝ] ℝ) (1 : ℝ))))) := by
  obtain ⟨δ, hδ_pos, hδ_le, hδ_int⟩ :=
    f.sourceFiberPath_integrand_eq_sheet_chain_locally hnc hβ_smooth hβ_reg hx om
  refine ⟨δ, hδ_pos, hδ_le, fun t ht h_sheet_g_real => ?_⟩
  -- Use the integrand lemma to rewrite to chart expression.
  rw [hδ_int t ht]
  -- Now apply the chain rule.
  congr 1
  apply mfderiv_sheet_g_beta_sigma_chain h_sheet_g_real
  · exact hβ_smooth.contMDiffAt
  · have h : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) Real.smoothTransition t :=
      (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).contDiffAt.contMDiffAt
    exact h.of_le (by decide)

end MeromorphicNonzero

end JacobianChallenge

end
