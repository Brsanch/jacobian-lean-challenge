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

/-- **`NormFM` agrees with the section product on a neighbourhood of a
regular value.**

At a regular value `y₀`, there exist a finite fibre witness `hF₀`, a
section function `σ : X → Y → X`, and a neighbourhood `V` of `y₀` on
which `NormFM f hf hnc g y = ∏ x ∈ hF₀.toFinset, g (σ x y)`.

Construction: combine `exists_coherent_local_sections_at_regular_value`
(for the `σ`) with `fibre_disjoint_chart_radius_decomposition` (for the
ambient chart-disks `D_x` that pin each `σ x y` to be the unique fibre
point in `D_x`) and `criticalValues_finite_general` (to restrict to a
punctured neighbourhood of regular values where ramification indices
collapse to `1`). -/
theorem NormFM_eventuallyEq_section_product_at_regular_value
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f)
    (g : MeromorphicNonzero X)
    {y₀ : Y} (hy₀ : y₀ ∉ criticalValuesGeneral f) :
    ∃ (hF₀ : (f ⁻¹' {y₀}).Finite) (σ : X → Y → X),
      (∀ x ∈ hF₀.toFinset, σ x y₀ = x) ∧
      (∀ x ∈ hF₀.toFinset, ContinuousAt (σ x) y₀) ∧
      (NormFM f hf hnc g) =ᶠ[𝓝 y₀]
        (fun y => ∏ x ∈ hF₀.toFinset, g.toFun (σ x y)) := by
  classical
  -- Step 1: coherent local sections.
  obtain ⟨hF₀, σ, V_sec, hVsec_open, hy₀_Vsec, hσ_y₀, hσ_cont, hf_σ_id⟩ :=
    exists_coherent_local_sections_at_regular_value hf hnc hy₀
  set FF₀ : Finset X := hF₀.toFinset with hFF₀_def
  -- Step 2: fibre-disjoint chart-radius decomposition.
  obtain ⟨hF₀', ε_fn, V_disj, hVdisj_open, hy₀_Vdisj, hε_pos,
          hD_pwd, hVdisj_pre_sub, h_count⟩ :=
    fibre_disjoint_chart_radius_decomposition f hf hnc y₀
  -- Coerce hF₀' to hF₀ via subsingleton: both are `(f⁻¹{y₀}).Finite` proofs;
  -- their toFinset's coincide.
  have hFF_eq : hF₀'.toFinset = FF₀ := by
    show hF₀'.toFinset = hF₀.toFinset
    exact (Set.Finite.toFinset_inj).mpr rfl
  -- D_x abbreviation aligned to fibre_disjoint shape.
  set D : X → Set X := fun x =>
    (chartAt ℂ x).source ∩
      (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x)
        (if h : x ∈ hF₀'.toFinset then ε_fn x h else 0) with hD_def
  -- For x ∈ FF₀, σ x continuous at y₀ with σ x y₀ = x, and D x ∋ x is open.
  -- So {y : σ x y ∈ D x} is a nbhd of y₀ for each x.
  have hD_open : ∀ x ∈ FF₀, IsOpen (D x) := by
    intro x hx
    have hx' : x ∈ hF₀'.toFinset := hFF_eq ▸ hx
    show IsOpen ((chartAt ℂ x).source ∩
        (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x)
          (if h : x ∈ hF₀'.toFinset then ε_fn x h else 0))
    rw [show (if h : x ∈ hF₀'.toFinset then ε_fn x h else 0) = ε_fn x hx'
        from dif_pos hx']
    have hco : ContinuousOn (chartAt ℂ x) (chartAt ℂ x).source :=
      (chartAt ℂ x).continuousOn_toFun
    exact hco.isOpen_inter_preimage (chartAt ℂ x).open_source Metric.isOpen_ball
  have hxD : ∀ x ∈ FF₀, x ∈ D x := by
    intro x hx
    have hx' : x ∈ hF₀'.toFinset := hFF_eq ▸ hx
    show x ∈ (chartAt ℂ x).source ∩
      (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x)
        (if h : x ∈ hF₀'.toFinset then ε_fn x h else 0)
    rw [show (if h : x ∈ hF₀'.toFinset then ε_fn x h else 0) = ε_fn x hx'
        from dif_pos hx']
    refine ⟨mem_chart_source ℂ x, ?_⟩
    show (chartAt ℂ x) x ∈ Metric.ball ((chartAt ℂ x) x) (ε_fn x hx')
    exact Metric.mem_ball_self (hε_pos x hx')
  -- Per-x preimage shrink: σ x ⁻¹' D x is a nbhd of y₀.
  have h_σ_D_nhds : ∀ x ∈ FF₀, σ x ⁻¹' D x ∈ 𝓝 y₀ := by
    intro x hx
    have hD_x_nhds : D x ∈ 𝓝 x := (hD_open x hx).mem_nhds (hxD x hx)
    have h_σ_x_at_y₀ : D x ∈ 𝓝 (σ x y₀) := by
      rw [hσ_y₀ x hx]; exact hD_x_nhds
    exact (hσ_cont x hx).preimage_mem_nhds h_σ_x_at_y₀
  -- Build V₁ : the set on which σ x y ∈ D x for every x ∈ FF₀.
  set V₁ : Set Y := ⋂ x ∈ FF₀, σ x ⁻¹' D x with hV₁_def
  have hV₁_nhds : V₁ ∈ 𝓝 y₀ := by
    rw [hV₁_def]
    exact (Filter.biInter_finset_mem FF₀).mpr h_σ_D_nhds
  -- Step 3: shrink to avoid critical values other than y₀.
  have h_cv_fin : (criticalValuesGeneral f).Finite :=
    criticalValues_finite_general f hf hnc
  have h_bad : (criticalValuesGeneral f \ {y₀}).Finite := h_cv_fin.diff
  have h_bad_closed : IsClosed (criticalValuesGeneral f \ {y₀}) := h_bad.isClosed
  have h_bad_compl_open : IsOpen (criticalValuesGeneral f \ {y₀})ᶜ :=
    h_bad_closed.isOpen_compl
  have hy₀_compl : y₀ ∈ (criticalValuesGeneral f \ {y₀})ᶜ := by
    intro hbad; exact hbad.2 rfl
  have h_compl_nhds : (criticalValuesGeneral f \ {y₀})ᶜ ∈ 𝓝 y₀ :=
    h_bad_compl_open.mem_nhds hy₀_compl
  -- Build the working V_work = V_sec ∩ V_disj ∩ V₁ ∩ (CV \ {y₀})ᶜ as nbhd of y₀.
  have hV_work_nhds :
      V_sec ∩ V_disj ∩ V₁ ∩ (criticalValuesGeneral f \ {y₀})ᶜ ∈ 𝓝 y₀ := by
    refine Filter.inter_mem (Filter.inter_mem (Filter.inter_mem ?_ ?_) hV₁_nhds)
      h_compl_nhds
    · exact hVsec_open.mem_nhds hy₀_Vsec
    · exact hVdisj_open.mem_nhds hy₀_Vdisj
  -- Refine to refine. For y in V_work, prove NormFM y = ∏ g(σ x y).
  refine ⟨hF₀, σ, hσ_y₀, hσ_cont, ?_⟩
  -- Eventually-equal: for y in V_work, NormFM y = ∏ x ∈ FF₀, g (σ x y).
  refine Filter.eventually_iff_exists_mem.mpr
    ⟨_, hV_work_nhds, fun y hy => ?_⟩
  obtain ⟨⟨⟨hy_Vsec, hy_Vdisj⟩, hy_V₁⟩, hy_compl⟩ := hy
  -- hy_compl: y ∉ criticalValuesGeneral f \ {y₀}, so either y = y₀ or y is regular.
  have hy_reg : y ∉ criticalValuesGeneral f := by
    intro hcv
    by_cases hy_eq : y = y₀
    · rw [hy_eq] at hcv; exact hy₀ hcv
    · exact hy_compl ⟨hcv, hy_eq⟩
  -- Each σ x y ∈ D x.
  have hσ_xy_D : ∀ x ∈ FF₀, σ x y ∈ D x := by
    intro x hx
    have h1 : y ∈ σ x ⁻¹' D x := by
      have h_iI : y ∈ ⋂ x' ∈ FF₀, σ x' ⁻¹' D x' := hy_V₁
      rw [Set.mem_iInter₂] at h_iI
      exact h_iI x hx
    exact h1
  -- Each σ x y is in the fibre over y.
  have hσ_xy_fibre : ∀ x ∈ FF₀, f (σ x y) = y := by
    intro x hx
    exact hf_σ_id x hx y hy_Vsec
  -- Step 4: rewrite LHS via NormFM_at_regular_value (uses hy_reg).
  -- NormFM y = ∏ z ∈ (fibres_finite y).toFinset, g z.
  -- Use the unconditional witness for y.
  -- Step 5: bijection FF₀ → (fibres_finite y).toFinset via x ↦ σ x y.
  set hFy : (f ⁻¹' {y}).Finite :=
    JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional
      f hf hnc y with hFy_def
  rw [NormFM_at_regular_value hf hnc g hy_reg]
  -- Goal: ∏ z ∈ hFy.toFinset, g z = ∏ x ∈ FF₀, g (σ x y).
  -- Use Finset.prod_bij in the reverse direction:
  -- i : FF₀ → hFy.toFinset, i x hx := σ x y.
  symm
  refine Finset.prod_bij (fun x _ => σ x y) ?_ ?_ ?_ ?_
  · -- Membership: σ x y ∈ hFy.toFinset, since f(σ x y) = y.
    intro x hx
    show σ x y ∈ hFy.toFinset
    rw [hFy.mem_toFinset]
    show f (σ x y) = y
    exact hσ_xy_fibre x hx
  · -- Injective on FF₀: σ x y = σ x' y → x = x'.
    -- Use that σ x y ∈ D x, D pairwise disjoint, x ↦ x is in D x.
    intro x hx x' hx' h_eq
    -- h_eq beta-reduces to σ x y = σ x' y.
    have h_eq' : σ x y = σ x' y := h_eq
    by_contra h_ne
    have hxFF' : x ∈ hF₀'.toFinset := hFF_eq ▸ hx
    have hx'FF' : x' ∈ hF₀'.toFinset := hFF_eq ▸ hx'
    have hdisj : Disjoint (D x) (D x') := by
      have := hD_pwd hxFF' hx'FF' h_ne
      convert this using 1 <;> rfl
    have hin_x : σ x y ∈ D x := hσ_xy_D x hx
    have hin_x' : σ x y ∈ D x' := by rw [h_eq']; exact hσ_xy_D x' hx'
    exact (Set.disjoint_iff.mp hdisj ⟨hin_x, hin_x'⟩).elim
  · -- Surjective: every z ∈ hFy.toFinset arises as σ x y for some x ∈ FF₀.
    intro z hz
    have hz_fibre : z ∈ f ⁻¹' {y} := hFy.mem_toFinset.mp hz
    -- z ∈ f⁻¹V_disj, so z ∈ ⋃ x ∈ hF₀'.toFinset, D x.
    have hz_pre_Vdisj : z ∈ f ⁻¹' V_disj := by
      show f z ∈ V_disj
      have : f z = y := hz_fibre
      rw [this]; exact hy_Vdisj
    have hz_union : z ∈ ⋃ x ∈ hF₀'.toFinset, D x :=
      hVdisj_pre_sub hz_pre_Vdisj
    rw [Set.mem_iUnion₂] at hz_union
    obtain ⟨x, hxFF', hz_in_Dx⟩ := hz_union
    have hxFF : x ∈ FF₀ := hFF_eq ▸ hxFF'
    refine ⟨x, hxFF, ?_⟩
    -- Need: σ x y = z. Both σ x y and z are in D x ∩ f⁻¹{y}.
    -- If y = y₀: both equal x? σ x y₀ = x. But z ∈ f⁻¹{y₀} and z ∈ D x, with
    -- y₀ regular so ramif = 1 and unique preimage in D x is x itself.
    -- If y ≠ y₀: h_count gives ncard (D x ∩ f⁻¹{y}) = ramif = 1.
    -- Both cases: |D x ∩ f⁻¹{y}| = 1 ⇒ σ x y = z.
    by_cases hy_eq : y = y₀
    · -- y = y₀: σ x y = σ x y₀ = x. Need to show z = x (then σ x y = z).
      -- z ∈ f⁻¹{y₀} = FF₀ as a set, so z ∈ FF₀. Then z ∈ D z. Combined with
      -- z ∈ D x and pairwise disjointness of D's, z = x.
      have hz_in_FF₀ : z ∈ FF₀ := by
        rw [hFF₀_def, hF₀.mem_toFinset]
        show z ∈ f ⁻¹' {y₀}
        have hfz_y : f z = y := hz_fibre
        rw [hy_eq] at hfz_y; exact hfz_y
      have hz_in_Dz : z ∈ D z := hxD z hz_in_FF₀
      have hz_eq_x : z = x := by
        by_contra h_neq
        have hz_FF' : z ∈ hF₀'.toFinset := hFF_eq ▸ hz_in_FF₀
        have hdisj : Disjoint (D z) (D x) := by
          have := hD_pwd hz_FF' hxFF' h_neq
          convert this using 1 <;> rfl
        exact (Set.disjoint_iff.mp hdisj ⟨hz_in_Dz, hz_in_Dx⟩).elim
      show (fun a _ => σ a y) x hxFF = z
      simp only []
      rw [hy_eq, hσ_y₀ x hxFF, hz_eq_x]
    · -- y ≠ y₀: use h_count.
      have h_ncard : (f ⁻¹' {y} ∩ D x).ncard = manifoldRamificationIndex f x := by
        have h_ε_eq : (if h : x ∈ hF₀'.toFinset then ε_fn x h else 0) = ε_fn x hxFF' :=
          dif_pos hxFF'
        have h_D_eq : D x =
            (chartAt ℂ x).source ∩
              (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) (ε_fn x hxFF') := by
          show (chartAt ℂ x).source ∩
              (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x)
                (if h : x ∈ hF₀'.toFinset then ε_fn x h else 0) =
              (chartAt ℂ x).source ∩
              (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) (ε_fn x hxFF')
          rw [h_ε_eq]
        rw [h_D_eq]
        exact h_count y hy_Vdisj hy_eq x hxFF'
      have h_ramif : manifoldRamificationIndex f x = 1 :=
        manifoldRamificationIndex_eq_one_at_regular_value_preimage hf hnc hy₀
          (show x ∈ f ⁻¹' {y₀} from hF₀.mem_toFinset.mp hxFF)
      rw [h_ramif] at h_ncard
      -- (f⁻¹{y} ∩ D x).ncard = 1. σ x y ∈ that, z ∈ that. Hence equal.
      have hσxy_in : σ x y ∈ f ⁻¹' {y} ∩ D x :=
        ⟨hσ_xy_fibre x hxFF, hσ_xy_D x hxFF⟩
      have hz_in : z ∈ f ⁻¹' {y} ∩ D x := ⟨hz_fibre, hz_in_Dx⟩
      have h_fin : (f ⁻¹' {y} ∩ D x).Finite :=
        Set.finite_of_ncard_ne_zero (by rw [h_ncard]; norm_num)
      -- ncard = 1 ⇒ pairs in the set are equal.
      have h_card_sub_a : ({σ x y} : Set X).ncard = 1 := Set.ncard_singleton _
      have h_sub_a : ({σ x y} : Set X) ⊆ f ⁻¹' {y} ∩ D x := by
        intro c hc; rw [Set.mem_singleton_iff] at hc; rw [hc]; exact hσxy_in
      have h_le : (f ⁻¹' {y} ∩ D x).ncard ≤ ({σ x y} : Set X).ncard := by
        rw [h_ncard, h_card_sub_a]
      have h_eq_set : ({σ x y} : Set X) = f ⁻¹' {y} ∩ D x :=
        Set.eq_of_subset_of_ncard_le h_sub_a h_le h_fin
      have hz_in_singleton : z ∈ ({σ x y} : Set X) := by
        rw [h_eq_set]; exact hz_in
      rw [Set.mem_singleton_iff] at hz_in_singleton
      exact hz_in_singleton.symm
  · -- Value: g.toFun (σ x y) = g.toFun (σ x y).
    intros; rfl

end Manifold
end JacobianChallenge

end
