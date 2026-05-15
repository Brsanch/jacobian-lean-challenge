/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroSourceFiberPathSheetEq
import JacobianChallenge.Manifold.SmoothPathVelocityFromFun

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `sourceFiberPath.ambient` identification with `sheet.g ∘ β ∘ σ`

`sourceFiberPath_toPath_extend_eq_sheet_g_locally` gives the
identification at the `toPath.extend` level. This chip lifts the same
identification to the `ambient` level (which is what the
`SmoothPath.velocity` / `integrand` API consumes), using
`ambient_eq_on_unitInterval`'s bridge.

The result: there is a `δ ∈ (0, 1]` such that for every `t ∈ Icc 0 δ`,
`(sourceFiberPath x).ambient t = sheet.g (β (σ t))`.

Combined with `SmoothPathVelocityFromFun`'s
`integrand_eq_of_ambient_eqOn_Icc_fun`, this gives the per-fiber-point
integrand identification on `Ioo 0 δ`:

```
integrand (sourceFiberPath x) ω t
  = applyCotangent (ω (sheet.g (β (σ t))))
      ((mfderiv (sheet.g ∘ β ∘ σ) t) 1)
```

This is the **first segment of the chain-rule pathway** for the
level-set chain integral.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter unitInterval
open scoped Manifold ContDiff Topology

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Lift `toPath.extend` identification to `ambient` -/

/-- **`sourceFiberPath.ambient` matches `sheet.g ∘ β ∘ σ` on `[0, δ]`
for some `δ ∈ (0, 1]`.** Lifts `sourceFiberPath_toPath_extend_eq_sheet_g_locally`
through `ambient_eq_on_unitInterval` (which holds on `unitInterval`,
i.e., for `t ∈ [0, 1]`, which `[0, δ]` contains since `δ ≤ 1`). -/
theorem sourceFiberPath_ambient_eq_sheet_g_locally
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    {x : X} (hx : f.toRiemannSphere x = β 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ t ∈ Icc (0 : ℝ) δ,
        (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).ambient t
          = (f.localSheetData_at_regular hnc
              (f.mem_regularSet_of_preimage_regularValue
                (hβ_reg 0 ⟨le_refl _, by norm_num⟩) hx)).g
              (β (Real.smoothTransition t)) := by
  obtain ⟨δ, hδ_pos, hδ_le, hδ_eq⟩ :=
    f.sourceFiberPath_toPath_extend_eq_sheet_g_locally hnc hβ_smooth hβ_reg hx
  refine ⟨δ, hδ_pos, hδ_le, fun t ht => ?_⟩
  -- Bridge `toPath.extend t = ambient t` via the unit-interval coercion.
  have ht_unit : t ∈ unitInterval := ⟨ht.1, le_trans ht.2 hδ_le⟩
  have h_ext_eq_amb :
      (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath.extend t
        = (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).ambient t := by
    -- `toPath.extend t = toPath ⟨t, ht_unit⟩` (since t ∈ [0, 1]).
    -- And `ambient t.val = toPath t` by `ambient_eq_on_unitInterval`.
    have h_ext : (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath.extend t
        = (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath ⟨t, ht_unit⟩ :=
      Path.extend_apply _ ht_unit
    have h_amb := SmoothPath.ambient_eq_on_unitInterval
      (f.sourceFiberPath hnc hβ_smooth hβ_reg hx) ⟨t, ht_unit⟩
    -- `h_amb : ambient ⟨t, ht_unit⟩.val = toPath ⟨t, ht_unit⟩`, i.e.
    -- `ambient t = toPath ⟨t, ht_unit⟩`.
    rw [h_ext, ← h_amb]
  rw [← h_ext_eq_amb]
  exact hδ_eq t ht

/-! ## Per-fiber-point integrand identification on the sub-interval -/

/-- **Per-fiber-point integrand identification on `Ioo 0 δ`.** Combines
`sourceFiberPath_ambient_eq_sheet_g_locally` with
`SmoothPath.integrand_eq_of_ambient_eqOn_Icc_fun`. -/
theorem sourceFiberPath_integrand_eq_sheet_chain_locally
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    {x : X} (hx : f.toRiemannSphere x = β 0)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ t ∈ Ioo (0 : ℝ) δ,
        (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).integrand om t
          = SmoothPath.applyCotangent
              (om ((f.localSheetData_at_regular hnc
                  (f.mem_regularSet_of_preimage_regularValue
                    (hβ_reg 0 ⟨le_refl _, by norm_num⟩) hx)).g
                  (β (Real.smoothTransition t))))
              ((mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ))
                (fun u : ℝ =>
                  (f.localSheetData_at_regular hnc
                    (f.mem_regularSet_of_preimage_regularValue
                      (hβ_reg 0 ⟨le_refl _, by norm_num⟩) hx)).g
                    (β (Real.smoothTransition u))) t :
                ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
                  ((f.localSheetData_at_regular hnc
                    (f.mem_regularSet_of_preimage_regularValue
                      (hβ_reg 0 ⟨le_refl _, by norm_num⟩) hx)).g
                    (β (Real.smoothTransition t)))) (1 : ℝ)) := by
  obtain ⟨δ, hδ_pos, hδ_le, hδ_eq⟩ :=
    f.sourceFiberPath_ambient_eq_sheet_g_locally hnc hβ_smooth hβ_reg hx
  refine ⟨δ, hδ_pos, hδ_le, fun t ht => ?_⟩
  exact SmoothPath.integrand_eq_of_ambient_eqOn_Icc_fun hδ_eq om ht

end MeromorphicNonzero

end JacobianChallenge

end
