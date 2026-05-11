/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.NormFMUnconditional
import JacobianChallenge.Manifold.LocalBiholomorphism
import JacobianChallenge.Manifold.NormPushforwardGlobal

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Continuity of `NormFM` at regular values (under the no-pole hypothesis)

Framework chip for the `regular_continuousAt` field of the (eventual)
`MeromorphicNonzero Y` packaging of `NormFM`.

The two outputs:

* `exists_local_section_at_regular_preimage` — at a regular value `y₀ ∉
  criticalValuesGeneral f` and a preimage `x ∈ f⁻¹{y₀}`, there is a
  continuous local section `σ_x : Y → X` defined on an open neighbourhood
  `V_x` of `y₀` with `σ_x y₀ = x`, `f ∘ σ_x = id` on `V_x`, and `σ_x`
  continuous at `y₀`.

  Built from `AnalyticAt.exists_local_biholomorphism` applied to the
  chart-pullback `F := chartAt ℂ y₀ ∘ f ∘ (chartAt ℂ x).symm`, whose
  derivative at `chartAt ℂ x x` is nonzero precisely because `y₀` is a
  regular value (via `deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood`).
-/

@[expose] public section

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace JacobianChallenge
namespace Manifold

universe u v

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable {Y : Type v}
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-- **Local section at a regular preimage.**

At a regular value `y₀ ∉ criticalValuesGeneral f` and a preimage `x` with
`f x = y₀`, there exist an open neighbourhood `V` of `y₀` and a function
`σ : Y → X` with `σ y₀ = x`, `σ` continuous at `y₀`, and `f (σ y) = y`
for every `y ∈ V`.

Construction: chart pullback `F := chartAt ℂ y₀ ∘ f ∘ (chartAt ℂ x).symm`
has nonzero derivative at `c x` (by the regularity of `y₀`), so
`AnalyticAt.exists_local_biholomorphism` produces a planar local inverse
`φ_inv`. Lift back through charts: `σ y := (chartAt ℂ x).symm (φ_inv
((chartAt ℂ y₀) y))`. The right-inverse relation `F (φ_inv z) = z` plus
chart injectivity on the source give `f ∘ σ = id`. -/
theorem exists_local_section_at_regular_preimage
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f)
    {y₀ : Y} (hy₀ : y₀ ∉ criticalValuesGeneral f)
    (x : X) (hxy : f x = y₀) :
    ∃ V : Set Y, IsOpen V ∧ y₀ ∈ V ∧
    ∃ σ : Y → X, σ y₀ = x ∧ ContinuousAt σ y₀ ∧ ∀ y ∈ V, f (σ y) = y := by
  classical
  -- Chart abbreviations.
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc_def
  set d : OpenPartialHomeomorph Y ℂ := chartAt ℂ y₀ with hd_def
  have hxc : x ∈ c.source := mem_chart_source ℂ x
  have hy₀d : y₀ ∈ d.source := mem_chart_source ℂ y₀
  -- The chart pullback `F`.
  set F : ℂ → ℂ := d ∘ f ∘ c.symm with hF_def
  -- Local injectivity of `f` at `x` from `y₀ ∉ criticalValuesGeneral f`.
  have hx_not_crit : x ∉ criticalSetGeneral f := by
    intro hx_crit; exact hy₀ ⟨x, hx_crit, hxy⟩
  have h_inj : ∃ U ∈ 𝓝 x, Set.InjOn f U := by
    by_contra h
    apply hx_not_crit
    show ¬ ∃ U ∈ 𝓝 x, Set.InjOn f U
    exact h
  -- `F` analytic at `c x` (chart pullback of a `C^ω` map at any point).
  have hF_an : _root_.AnalyticAt ℂ ((chartAt ℂ (f x)) ∘ f ∘ c.symm) (c x) :=
    JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback
      hf x
  -- Replace `chartAt ℂ (f x)` by `d` using `hxy`.
  have hcd : (chartAt ℂ (f x)) = d := by
    show (chartAt ℂ (f x)) = (chartAt ℂ y₀); rw [hxy]
  rw [hcd] at hF_an
  -- Derivative nonzero (regularity).
  have h_deriv_raw :
      deriv ((chartAt ℂ (f x)) ∘ f ∘ c.symm) (c x) ≠ 0 :=
    JacobianChallenge.ContMDiff.Owed.degree.deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood
      hf hnc x h_inj
  have h_deriv : deriv F (c x) ≠ 0 := by
    have : deriv F (c x) = deriv ((chartAt ℂ (f x)) ∘ f ∘ c.symm) (c x) := by
      rw [hF_def, hcd]
    rw [this]; exact h_deriv_raw
  -- Apply `AnalyticAt.exists_local_biholomorphism` at `c x`.
  obtain ⟨U₁, hU₁_nhds, V₁, hV₁_nhds, φ_inv, _hMaps_F_U₁_V₁,
          hMaps_φ_V₁_U₁, hLeftInv, hRightInv, hφ_analytic⟩ :=
    AnalyticAt.exists_local_biholomorphism hF_an h_deriv
  -- `F (c x) = d y₀`: rewrite via `hxy`.
  have hF_cx : F (c x) = d y₀ := by
    show (d ∘ f ∘ c.symm) (c x) = d y₀
    have h_inv : c.symm (c x) = x := c.left_inv hxc
    simp [Function.comp, h_inv, hxy]
  -- `φ_inv (d y₀) = c x` via `LeftInvOn φ_inv F U₁` applied at `x ∈ U₁` (where U₁ is a nhds of c x).
  have hcx_in_U₁ : c x ∈ U₁ := mem_of_mem_nhds hU₁_nhds
  have hφ_dy₀ : φ_inv (d y₀) = c x := by
    have h1 : φ_inv (F (c x)) = c x := hLeftInv hcx_in_U₁
    rw [← hF_cx]; exact h1
  -- φ_inv continuous at d y₀. (analytic_at returns ContinuousAt at F (c x); rewrite.)
  have hφ_cont_raw : ContinuousAt φ_inv (F (c x)) := hφ_analytic.continuousAt
  have hφ_cont : ContinuousAt φ_inv (d y₀) := by rw [← hF_cx]; exact hφ_cont_raw
  -- d continuous at y₀ (chart structure, y₀ in source).
  have hd_cont : ContinuousAt d y₀ :=
    (d.continuousOn_toFun.continuousAt (d.open_source.mem_nhds hy₀d))
  -- c.symm continuous at φ_inv (d y₀) = c x. c.symm is continuous on c.target, c x ∈ c.target.
  have hcx_target : c x ∈ c.target := c.map_source hxc
  have hc_symm_cont : ContinuousAt c.symm (c x) :=
    c.continuousOn_invFun.continuousAt (c.open_target.mem_nhds hcx_target)
  have hc_symm_cont' : ContinuousAt c.symm (φ_inv (d y₀)) := by
    rw [hφ_dy₀]; exact hc_symm_cont
  -- σ.
  set σ : Y → X := fun y => c.symm (φ_inv (d y)) with hσ_def
  -- σ y₀ = x.
  have hσ_y₀ : σ y₀ = x := by
    show c.symm (φ_inv (d y₀)) = x
    rw [hφ_dy₀]; exact c.left_inv hxc
  -- ContinuousAt σ y₀: composition. Use Function.comp explicitly so Lean splits correctly.
  set fdY : Y → ℂ := fun y => φ_inv (d y) with hfdY_def
  have h_fdY_cont : ContinuousAt fdY y₀ := hφ_cont.comp hd_cont
  have hc_symm_at : ContinuousAt c.symm (fdY y₀) := by
    show ContinuousAt c.symm (φ_inv (d y₀)); exact hc_symm_cont'
  have hσ_cont : ContinuousAt σ y₀ := by
    have h_comp : ContinuousAt (c.symm ∘ fdY) y₀ := hc_symm_at.comp h_fdY_cont
    -- σ y = (c.symm ∘ fdY) y by rfl.
    exact h_comp
  -- Now shrink V to enforce: y ∈ V ⇒ d y ∈ V₁ ∩ φ_inv⁻¹ c.target ∧ f (σ y) ∈ d.source.
  -- (i) d y ∈ V₁: V₁ ∈ 𝓝 (d y₀), d continuous at y₀ ⇒ d ⁻¹' V₁ ∈ 𝓝 y₀.
  have hV₁_nhds' : V₁ ∈ 𝓝 (d y₀) := by rw [← hF_cx]; exact hV₁_nhds
  have hV₁_pre : d ⁻¹' V₁ ∈ 𝓝 y₀ := hd_cont.preimage_mem_nhds hV₁_nhds'
  -- (ii) φ_inv (d y) ∈ c.target: c.target ∈ 𝓝 (c x) [open + cx ∈ target]; via φ_inv ∘ d continuous at y₀.
  have hc_target_nhds : c.target ∈ 𝓝 (c x) := c.open_target.mem_nhds hcx_target
  have hφd_pre : (φ_inv ∘ d) ⁻¹' c.target ∈ 𝓝 y₀ := by
    have h_φd_cont : ContinuousAt (φ_inv ∘ d) y₀ := hφ_cont.comp hd_cont
    have h_target_at_y₀ : c.target ∈ 𝓝 ((φ_inv ∘ d) y₀) := by
      have : (φ_inv ∘ d) y₀ = c x := by
        show φ_inv (d y₀) = c x; exact hφ_dy₀
      rw [this]; exact hc_target_nhds
    exact h_φd_cont.preimage_mem_nhds h_target_at_y₀
  -- (iii) f (σ y) ∈ d.source: σ continuous at y₀, f continuous, f (σ y₀) = f x = y₀ ∈ d.source.
  have hd_source_nhds : d.source ∈ 𝓝 y₀ := d.open_source.mem_nhds hy₀d
  have hfσ_pre : (f ∘ σ) ⁻¹' d.source ∈ 𝓝 y₀ := by
    have hf_cont : Continuous f := hf.continuous
    have hfσ_cont : ContinuousAt (f ∘ σ) y₀ := hf_cont.continuousAt.comp hσ_cont
    have h_at_y₀ : d.source ∈ 𝓝 ((f ∘ σ) y₀) := by
      have : (f ∘ σ) y₀ = y₀ := by
        show f (σ y₀) = y₀; rw [hσ_y₀]; exact hxy
      rw [this]; exact hd_source_nhds
    exact hfσ_cont.preimage_mem_nhds h_at_y₀
  -- (iv) y ∈ d.source: needed for d.injOn (d y = d y' ⇒ y = y').
  -- Already in hd_source_nhds.
  -- Intersect (i)–(iv) and extract an open subset around y₀.
  have h_inter : (d ⁻¹' V₁) ∩ ((φ_inv ∘ d) ⁻¹' c.target) ∩ ((f ∘ σ) ⁻¹' d.source)
                    ∩ d.source ∈ 𝓝 y₀ :=
    Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hV₁_pre hφd_pre) hfσ_pre)
      hd_source_nhds
  obtain ⟨V, hV_sub, hV_open, hy₀V⟩ := mem_nhds_iff.mp h_inter
  refine ⟨V, hV_open, hy₀V, σ, hσ_y₀, hσ_cont, ?_⟩
  intro y hyV
  -- Extract the four memberships.
  have hV_facts := hV_sub hyV
  obtain ⟨⟨⟨hdy_V₁, hφdy_target⟩, hfσy_source⟩, hy_dsource⟩ := hV_facts
  -- σ y = c.symm (φ_inv (d y)).
  have h_σy : σ y = c.symm (φ_inv (d y)) := rfl
  -- φ_inv (d y) ∈ c.target ⇒ c.symm (φ_inv (d y)) ∈ c.source.
  have h_σy_csource : σ y ∈ c.source := by
    rw [h_σy]; exact c.map_target hφdy_target
  -- c (σ y) = φ_inv (d y).
  have h_c_σy : c (σ y) = φ_inv (d y) := by
    show c (c.symm (φ_inv (d y))) = φ_inv (d y)
    exact c.right_inv hφdy_target
  -- F (c (σ y)) = d y, via RightInvOn φ_inv F V₁.
  have h_F_c_σy : F (c (σ y)) = d y := by
    rw [h_c_σy]; exact hRightInv hdy_V₁
  -- Unfold F: F (c (σ y)) = (d ∘ f ∘ c.symm) (c (σ y)) = d (f (c.symm (c (σ y)))).
  -- And c.symm (c (σ y)) = σ y (since σ y ∈ c.source).
  have h_csym : c.symm (c (σ y)) = σ y := c.left_inv h_σy_csource
  have h_d_fσy : d (f (σ y)) = d y := by
    have : (d ∘ f ∘ c.symm) (c (σ y)) = d (f (σ y)) := by
      show d (f (c.symm (c (σ y)))) = d (f (σ y))
      rw [h_csym]
    rw [← this]
    show F (c (σ y)) = d y
    exact h_F_c_σy
  -- f (σ y) ∈ d.source (from hfσy_source) and y ∈ d.source: d.injOn forces f (σ y) = y.
  have hfσy_dsource : f (σ y) ∈ d.source := hfσy_source
  have := d.injOn hfσy_dsource hy_dsource h_d_fσy
  exact this

/-- **Coherent local sections at a regular value.**

At a regular value `y₀ ∉ criticalValuesGeneral f`, package one local
section per fibre point on a common open neighbourhood `V` of `y₀`.

Built by applying `exists_local_section_at_regular_preimage` at each
`x ∈ (f⁻¹{y₀}).toFinset` and intersecting the per-`x` neighbourhoods.
-/
theorem exists_coherent_local_sections_at_regular_value
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f)
    {y₀ : Y} (hy₀ : y₀ ∉ criticalValuesGeneral f) :
    ∃ (hF₀ : (f ⁻¹' {y₀}).Finite)
      (σ : X → Y → X)
      (V : Set Y),
      IsOpen V ∧ y₀ ∈ V ∧
      (∀ x ∈ hF₀.toFinset, σ x y₀ = x) ∧
      (∀ x ∈ hF₀.toFinset, ContinuousAt (σ x) y₀) ∧
      (∀ x ∈ hF₀.toFinset, ∀ y ∈ V, f (σ x y) = y) := by
  classical
  have hF₀ : (f ⁻¹' {y₀}).Finite :=
    JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional
      f hf hnc y₀
  set FF₀ : Finset X := hF₀.toFinset with hFF₀_def
  -- Per-x existential.
  have h_each : ∀ x ∈ FF₀, ∃ V : Set Y, IsOpen V ∧ y₀ ∈ V ∧
      ∃ σ : Y → X, σ y₀ = x ∧ ContinuousAt σ y₀ ∧ ∀ y ∈ V, f (σ y) = y := by
    intro x hx
    have hx_fibre : x ∈ f ⁻¹' {y₀} := hF₀.mem_toFinset.mp hx
    have hxy : f x = y₀ := hx_fibre
    exact exists_local_section_at_regular_preimage hf hnc hy₀ x hxy
  choose V_fn hV_open hy₀V σ_fn hσ_y₀ hσ_cont hf_σ using h_each
  -- Build non-dependent V_fn' and σ_fn' over X.
  set V_fn' : X → Set Y := fun x =>
    if h : x ∈ FF₀ then V_fn x h else Set.univ with hV_fn'_def
  set σ_fn' : X → Y → X := fun x =>
    if h : x ∈ FF₀ then σ_fn x h else fun _ => x with hσ_fn'_def
  -- V := ⋂ x ∈ FF₀, V_fn' x.
  set V : Set Y := ⋂ x ∈ FF₀, V_fn' x with hV_def
  -- IsOpen V.
  have hV_open' : IsOpen V := by
    refine isOpen_biInter_finset ?_
    intro x hx
    show IsOpen (V_fn' x)
    rw [hV_fn'_def]
    show IsOpen (if h : x ∈ FF₀ then V_fn x h else (Set.univ : Set Y))
    rw [dif_pos hx]; exact hV_open x hx
  -- y₀ ∈ V.
  have hy₀_V : y₀ ∈ V := by
    rw [hV_def, Set.mem_iInter₂]
    intro x hx
    show y₀ ∈ V_fn' x
    rw [hV_fn'_def]
    show y₀ ∈ (if h : x ∈ FF₀ then V_fn x h else (Set.univ : Set Y))
    rw [dif_pos hx]; exact hy₀V x hx
  refine ⟨hF₀, σ_fn', V, hV_open', hy₀_V, ?_, ?_, ?_⟩
  · intro x hx
    show σ_fn' x y₀ = x
    rw [hσ_fn'_def]
    show (if h : x ∈ FF₀ then σ_fn x h else fun _ => x) y₀ = x
    rw [dif_pos hx]; exact hσ_y₀ x hx
  · intro x hx
    show ContinuousAt (σ_fn' x) y₀
    rw [hσ_fn'_def]
    show ContinuousAt (if h : x ∈ FF₀ then σ_fn x h else fun _ => x) y₀
    rw [dif_pos hx]; exact hσ_cont x hx
  · intro x hx y hyV
    have hy_Vfn' : y ∈ V_fn' x := by
      have h_mem : y ∈ ⋂ x' ∈ FF₀, V_fn' x' := hyV
      rw [Set.mem_iInter₂] at h_mem
      exact h_mem x hx
    have hy_Vfn : y ∈ V_fn x hx := by
      have heq : V_fn' x = V_fn x hx := by
        show (if h : x ∈ FF₀ then V_fn x h else (Set.univ : Set Y)) = V_fn x hx
        rw [dif_pos hx]
      rw [heq] at hy_Vfn'; exact hy_Vfn'
    have : σ_fn' x = σ_fn x hx := by
      show (if h : x ∈ FF₀ then σ_fn x h else fun _ => x) = σ_fn x hx
      rw [dif_pos hx]
    rw [this]
    exact hf_σ x hx y hy_Vfn

/-! Continuity of `NormFM` at a regular value (next chip) builds on
`exists_coherent_local_sections_at_regular_value` plus
`g.regular_continuousAt` at each non-pole preimage to obtain continuity
of the finite product. -/

end Manifold
end JacobianChallenge

end
