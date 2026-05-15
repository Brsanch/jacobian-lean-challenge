/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalSheetSmoothOn
import JacobianChallenge.Manifold.MeromorphicNonzeroPushforwardReal
import JacobianChallenge.Manifold.MeromorphicNonzeroLevelSetChain

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Realified `sheet.g` smoothness eventually near `t = 0`

For a non-constant `f : MeromorphicNonzero X`, a smooth `β : ℝ →
RiemannSphere` regular on `[0, 1]`, and any fibre point `x ∈ sourceFiber
hβ0_reg`, the local sheet inverse `sheet_x.g` is `ContMDiffOn ω` on a
neighbourhood of `f.toRiemannSphere x = β 0`
(`exists_contMDiffOn_localSheet_g_near_basePoint`). Realifying via
`ContMDiffAt.complex_to_real`, then composing through continuity of
`β ∘ σ` at `0`, gives:

  `∀ᶠ t in 𝓝 0, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ sheet_x.g (β(σ t))`

This is the per-fibre dischargeable form of the per-`t` chain rule's
`h_sheet_g_real` hypothesis. Uniform-over-`sourceFiber` form via
`Filter.eventually_all`.

## What ships

* `MeromorphicNonzero.eventually_sheet_g_real_smooth` — per-fibre
  filter form of realified sheet.g smoothness.

* `MeromorphicNonzero.eventually_forall_sheet_g_real_smooth` —
  uniform-over-`sourceFiber` filter form.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Per-fibre realified `sheet.g` smoothness eventually near `0`.** -/
theorem eventually_sheet_g_real_smooth
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet)
    {x : X} (hx : f.toRiemannSphere x = β 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        (f.localSheetData_at_regular hnc
          (f.mem_regularSet_of_preimage_regularValue
            (hβ_reg 0 ⟨le_refl _, by norm_num⟩) hx)).g
        (β (Real.smoothTransition t)) := by
  classical
  set hx_reg : x ∈ f.regularSet :=
    f.mem_regularSet_of_preimage_regularValue
      (hβ_reg 0 ⟨le_refl _, by norm_num⟩) hx with hx_reg_def
  -- ContMDiffOn ω on an open nbhd `u ∋ f.toRiemannSphere x`.
  obtain ⟨u, hu_nhds, hu_smooth⟩ :=
    f.exists_contMDiffOn_localSheet_g_near_basePoint hnc hx_reg
  -- Shrink to an open subset u_o ∋ f.toRiemannSphere x with u_o ⊆ u.
  obtain ⟨u_o, hu_o_sub, hu_o_open, hu_o_mem⟩ := mem_nhds_iff.mp hu_nhds
  -- Continuity of β ∘ σ at 0.
  have hβσ_cont : Continuous (fun t : ℝ => β (Real.smoothTransition t)) :=
    hβ_smooth.continuous.comp Real.smoothTransition.continuous
  -- (β ∘ σ) ⁻¹' u_o ∈ 𝓝 0.
  have h0_in_pre : (0 : ℝ) ∈ (fun t : ℝ => β (Real.smoothTransition t)) ⁻¹' u_o := by
    simp only [Set.mem_preimage, Real.smoothTransition.zero]
    rw [← hx]; exact hu_o_mem
  have h_pre_nhds : (fun t : ℝ => β (Real.smoothTransition t)) ⁻¹' u_o ∈ 𝓝 (0 : ℝ) :=
    (hβσ_cont.isOpen_preimage _ hu_o_open).mem_nhds h0_in_pre
  filter_upwards [h_pre_nhds] with t htu
  -- β(σ t) ∈ u_o ⊆ u, so sheet.g is ContMDiffAt 𝓘(ℂ,ℂ) ω at β(σ t) (via hu_smooth).
  have hβt_u : β (Real.smoothTransition t) ∈ u := hu_o_sub htu
  have h_omega : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (f.localSheetData_at_regular hnc hx_reg).g (β (Real.smoothTransition t)) :=
    hu_smooth.contMDiffAt (mem_of_superset (hu_o_open.mem_nhds htu) hu_o_sub)
  -- Realify.
  exact ContMDiffAt.complex_to_real h_omega

/-- **Uniform-over-`sourceFiber` form of realified sheet.g smoothness eventually.** -/
theorem eventually_forall_sheet_g_real_smooth
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ p : { x : X // x ∈ f.sourceFiber
          (hβ_reg 0 ⟨le_refl _, by norm_num⟩) },
        ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
          (f.localSheetData_at_regular hnc
            (f.mem_regularSet_of_preimage_regularValue
              (hβ_reg 0 ⟨le_refl _, by norm_num⟩)
              ((f.mem_sourceFiber_iff
                (hβ_reg 0 ⟨le_refl _, by norm_num⟩) p.val).mp p.property))).g
          (β (Real.smoothTransition t)) := by
  classical
  rw [Filter.eventually_all]
  intro p
  exact f.eventually_sheet_g_real_smooth hnc hβ_smooth hβ_reg
    ((f.mem_sourceFiber_iff
      (hβ_reg 0 ⟨le_refl _, by norm_num⟩) p.val).mp p.property)

end MeromorphicNonzero

end JacobianChallenge

end
