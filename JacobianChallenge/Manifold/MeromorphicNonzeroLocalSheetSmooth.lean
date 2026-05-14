/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalSheet
import JacobianChallenge.Manifold.ContMDiffAnalyticBridge

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Smoothness of the manifold local sheet inverse at the base point

For `f : MeromorphicNonzero X` with non-constant `f.toRiemannSphere`
and a regular point `x₀ ∈ f.regularSet`, the local sheet inverse
`(f.localSheetData_at_regular hnc hx₀).g : RiemannSphere → X` is
`ContMDiffAt` at the base value `f.toRiemannSphere x₀` with regularity
`ω` (analytic).

## Argument

`sheet.g = manifoldLocalOph.symm` whose underlying function is
`c.symm ∘ φ.symm ∘ d`, where `c := chartAt ℂ x₀`,
`d := chartAt ℂ v₀`, and `φ := chartPullback_oph` (chip 6).

Apply `contMDiffAt_omega_of_analyticAt_chart_pullback`
(`ContMDiffAnalyticBridge.lean`) at `v₀`.  Hypotheses:

* `ContinuousAt sheet.g v₀` — true because `sheet.g` is the underlying
  function of `manifoldLocalOph.symm`, which is continuous on its
  source `manifoldLocalOph.target ∋ v₀`.

* Chart pullback `c ∘ sheet.g ∘ d.symm` is `AnalyticAt` at `d v₀`.
  On the open set `S := d.target ∩ φ.target ∩ φ.symm⁻¹' c.target`
  containing `d v₀`, the chart pullback equals `φ.symm` pointwise
  (chart-side cancellation via `d.right_inv` and `c.right_inv`).
  `φ.symm` is `AnalyticAt` at `d v₀` from the analytic IFT used in
  `chartPullback_oph`.

`AnalyticAt.congr` propagates analyticity along this local equality.

## What ships

* `MeromorphicNonzero.contMDiffAt_localSheet_g_at_basePoint` — headline
  `ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω sheet.g (f.toRiemannSphere x₀)`.

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

/-- **Smoothness of the manifold local sheet's inverse at the base
point.**  Regularity `ω` (analytic). -/
theorem contMDiffAt_localSheet_g_at_basePoint
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {x₀ : X} (hx₀_reg : x₀ ∈ f.regularSet) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (f.localSheetData_at_regular hnc hx₀_reg).g
      (f.toRiemannSphere x₀) := by
  classical
  set v₀ : RiemannSphere := f.toRiemannSphere x₀ with hv₀_def
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀ with hc_def
  set d : OpenPartialHomeomorph RiemannSphere ℂ := chartAt ℂ v₀ with hd_def
  set φ : OpenPartialHomeomorph ℂ ℂ := f.chartPullback_oph hnc hx₀_reg with hφ_def
  set M : OpenPartialHomeomorph X RiemannSphere :=
    f.manifoldLocalOph hnc hx₀_reg with hM_def
  -- `sheet.g = M.symm` as functions.
  have h_sheet_g_eq : (f.localSheetData_at_regular hnc hx₀_reg).g
      = (M.symm : RiemannSphere → X) := rfl
  rw [h_sheet_g_eq]
  -- Useful precomputed facts.
  have hv₀_d : v₀ ∈ d.source := mem_chart_source ℂ v₀
  have hx₀_c : x₀ ∈ c.source := mem_chart_source ℂ x₀
  have hcx₀_φ : c x₀ ∈ φ.source := f.mem_source_chartPullback_oph hnc hx₀_reg
  have hcx₀_ct : c x₀ ∈ c.target := c.map_source hx₀_c
  -- φ (c x₀) = d v₀.
  have hφcx₀ : (φ : ℂ → ℂ) (c x₀) = d v₀ := by
    rw [f.coe_chartPullback_oph hnc hx₀_reg]
    unfold chartPullback
    show ((chartAt ℂ v₀) ∘ f.toRiemannSphere ∘ (chartAt ℂ x₀).symm) (c x₀)
        = d v₀
    rw [Function.comp_apply, Function.comp_apply, c.left_inv hx₀_c]
  have hdv₀_φt : d v₀ ∈ φ.target := by
    rw [← hφcx₀]; exact φ.map_source hcx₀_φ
  have hdv₀_dt : d v₀ ∈ d.target := d.map_source hv₀_d
  -- φ.symm (d v₀) = c x₀.
  have hφsymm_dv₀ : (φ.symm : ℂ → ℂ) (d v₀) = c x₀ := by
    rw [← hφcx₀]; exact φ.left_inv hcx₀_φ
  have hφsymm_dv₀_ct : (φ.symm : ℂ → ℂ) (d v₀) ∈ c.target := by
    rw [hφsymm_dv₀]; exact hcx₀_ct
  -- M.symm v₀ = x₀.
  have hM_symm_v₀ : M.symm v₀ = x₀ := by
    have hx₀_src : x₀ ∈ M.source := f.mem_source_manifoldLocalOph hnc hx₀_reg
    have h_apply : (M : X → RiemannSphere) x₀ = v₀ :=
      f.manifoldLocalOph_apply hnc hx₀_reg hx₀_src
    have h_left : M.symm ((M : X → RiemannSphere) x₀) = x₀ := M.left_inv hx₀_src
    rw [h_apply] at h_left
    exact h_left
  -- Apply the bridge theorem at the manifold level.
  refine JacobianChallenge.ContMDiff.Owed.degree.contMDiffAt_omega_of_analyticAt_chart_pullback
    ?hcont ?hA
  case hcont =>
    -- M.symm is continuous on M.target ∋ v₀.
    have hv₀_tgt : v₀ ∈ M.target := f.mem_target_manifoldLocalOph hnc hx₀_reg
    exact M.continuousOn_symm.continuousAt (M.open_target.mem_nhds hv₀_tgt)
  case hA =>
    -- After hM_symm_v₀, the outer chart is `c = chartAt ℂ x₀`.
    show AnalyticAt ℂ ((chartAt ℂ (M.symm v₀)) ∘ M.symm ∘ (chartAt ℂ v₀).symm)
      ((chartAt ℂ v₀) v₀)
    rw [hM_symm_v₀]
    -- Now: AnalyticAt ℂ (c ∘ M.symm ∘ d.symm) (d v₀).
    -- `φ.symm` is AnalyticAt at d v₀ (from chartPullback_oph + IFT).
    have hφ_an : AnalyticAt ℂ (φ.symm : ℂ → ℂ) (d v₀) := by
      have h_an_ψ : AnalyticAt ℂ (f.chartPullback x₀) ((chartAt ℂ x₀) x₀) :=
        f.analyticAt_chartPullback x₀
      have h_dne : deriv (f.chartPullback x₀) ((chartAt ℂ x₀) x₀) ≠ 0 :=
        f.deriv_chartPullback_ne_zero_of_regular hnc hx₀_reg
      have h_inv_an_raw : AnalyticAt ℂ
          (h_an_ψ.hasStrictDerivAt.localInverse
              (f.chartPullback x₀) _ ((chartAt ℂ x₀) x₀) h_dne)
          (f.chartPullback x₀ ((chartAt ℂ x₀) x₀)) :=
        h_an_ψ.analyticAt_localInverse h_dne
      have h_localInv_eq :
          h_an_ψ.hasStrictDerivAt.localInverse
              (f.chartPullback x₀) _ ((chartAt ℂ x₀) x₀) h_dne
            = (φ.symm : ℂ → ℂ) := rfl
      rw [h_localInv_eq] at h_inv_an_raw
      have h_pt_eq : f.chartPullback x₀ ((chartAt ℂ x₀) x₀) = d v₀ := by
        unfold chartPullback
        show ((chartAt ℂ v₀) ∘ f.toRiemannSphere ∘ (chartAt ℂ x₀).symm) (c x₀)
            = d v₀
        rw [Function.comp_apply, Function.comp_apply, c.left_inv hx₀_c]
      rw [h_pt_eq] at h_inv_an_raw
      exact h_inv_an_raw
    -- Local equality `c ∘ M.symm ∘ d.symm = φ.symm` on an open nbhd of d v₀.
    have h_local_eq :
        (c ∘ M.symm ∘ d.symm : ℂ → ℂ) =ᶠ[𝓝 (d v₀)] (φ.symm : ℂ → ℂ) := by
      -- Agreement set.
      set S : Set ℂ :=
        d.target ∩ (φ.target ∩ φ.symm ⁻¹' c.target) with hS_def
      have hS_open : IsOpen S := by
        refine d.open_target.inter ?_
        have hcont : ContinuousOn (φ.symm : ℂ → ℂ) φ.target := φ.continuousOn_symm
        exact hcont.isOpen_inter_preimage φ.open_target c.open_target
      have hd_v₀_S : d v₀ ∈ S := ⟨hdv₀_dt, hdv₀_φt, hφsymm_dv₀_ct⟩
      refine eventually_of_mem (hS_open.mem_nhds hd_v₀_S) ?_
      intro y hy
      obtain ⟨hy_dt, hy_φt, hy_φsymm_ct⟩ := hy
      -- Underlying function unfold: M.symm y = c.symm (φ.symm (d y)).
      have hM_symm_eq : ∀ z : RiemannSphere,
          M.symm z = c.symm (φ.symm (d z)) := by
        intro z
        -- M = (c.trans (φ'.trans d.symm)).restrOpen ...
        -- M.symm.coe = (c.trans (φ'.trans d.symm)).symm.coe = c.symm ∘ φ.symm ∘ d
        rfl
      -- Compute (c ∘ M.symm ∘ d.symm) y.
      show c (M.symm (d.symm y)) = φ.symm y
      rw [hM_symm_eq]
      -- c (c.symm (φ.symm (d (d.symm y)))) = c (c.symm (φ.symm y))
      --                                    = φ.symm y.
      have h_dr : d (d.symm y) = y := d.right_inv hy_dt
      rw [h_dr]
      have h_cr : c (c.symm (φ.symm y)) = φ.symm y :=
        c.right_inv hy_φsymm_ct
      exact h_cr
    exact hφ_an.congr h_local_eq.symm

end MeromorphicNonzero

end JacobianChallenge

end
