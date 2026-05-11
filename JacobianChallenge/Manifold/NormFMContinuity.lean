/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.NormFMUnconditional
import JacobianChallenge.Manifold.NormFMPrincipalDivisor
import JacobianChallenge.Manifold.LocalBiholomorphism
import JacobianChallenge.Manifold.NormPushforwardGlobal
import Mathlib.Topology.Perfect
import Mathlib.Topology.Algebra.Module.PerfectSpace

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

/-- **Continuity of `NormFM` at a regular value with no preimage poles.**

If `y₀` is a regular value of `f` and every preimage `x ∈ f⁻¹{y₀}` is a
non-pole point of `g` (i.e. `0 ≤ mmero g x`), then
`NormFM f hf hnc g` is continuous at `y₀`.

Proof: by `NormFM_eventuallyEq_section_product_at_regular_value`,
`NormFM` agrees on a neighbourhood of `y₀` with the section product
`y ↦ ∏ x ∈ FF₀, g (σ x y)`. Each `g ∘ σ x` is continuous at `y₀` via
`g.regular_continuousAt` at `x` (non-pole) and `σ x` continuous at `y₀`.
The Finset product of continuous functions is continuous; transferring
via the EventuallyEq finishes. -/
theorem NormFM_continuousAt_of_regular_and_no_poles
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f)
    (g : MeromorphicNonzero X)
    {y₀ : Y} (hy₀ : y₀ ∉ criticalValuesGeneral f)
    (hg_nonpole : ∀ x ∈ f ⁻¹' {y₀},
        0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g.toFun x) :
    ContinuousAt (NormFM f hf hnc g) y₀ := by
  classical
  obtain ⟨hF₀, σ, hσ_y₀, hσ_cont, h_eventually⟩ :=
    NormFM_eventuallyEq_section_product_at_regular_value hf hnc g hy₀
  -- For each x ∈ hF₀.toFinset, `g ∘ σ x` is continuous at y₀.
  have h_each :
      ∀ x ∈ hF₀.toFinset, ContinuousAt (fun y => g.toFun (σ x y)) y₀ := by
    intro x hx
    have hx_fibre : x ∈ f ⁻¹' {y₀} := hF₀.mem_toFinset.mp hx
    have hg_at_x : ContinuousAt g.toFun x :=
      g.regular_continuousAt x (hg_nonpole x hx_fibre)
    have hg_at_σ : ContinuousAt g.toFun (σ x y₀) := by
      rw [hσ_y₀ x hx]; exact hg_at_x
    exact hg_at_σ.comp (hσ_cont x hx)
  -- Finset product is continuous: package via `tendsto_finset_prod`.
  have h_prod :
      ContinuousAt (fun y => ∏ x ∈ hF₀.toFinset, g.toFun (σ x y)) y₀ := by
    show Tendsto (fun y => ∏ x ∈ hF₀.toFinset, g.toFun (σ x y)) (𝓝 y₀)
      (𝓝 (∏ x ∈ hF₀.toFinset, g.toFun (σ x y₀)))
    exact tendsto_finset_prod hF₀.toFinset
      (fun x hx => (h_each x hx : Tendsto _ _ _))
  -- Transfer continuity via EventuallyEq.
  exact h_prod.congr h_eventually.symm

/-- **Non-negativity of `NormFM`'s order under no-pole preimages.**

If every preimage `x ∈ f⁻¹{y}` of `y` is a non-pole point of `g`
(`0 ≤ mmero g x`), then `0 ≤ mmero NormFM y`.

Proof: the fibre sum identity
`mmero NormFM y = ∑ x ∈ FF, mmero g x` reduces non-negativity to
`Finset.sum_nonneg`. This is the order-side of the no-pole hypothesis
that fed `regular_continuousAt` in the framework: the regularized
form's `if 0 ≤ mmero ...` branch fires precisely when this lemma's
hypothesis holds. -/
lemma NormFM_mmeromorphicOrderAt_nonneg_of_no_poles
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f)
    (g : MeromorphicNonzero X)
    {y : Y} (hg_nonpole : ∀ x ∈ f ⁻¹' {y},
        0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g.toFun x) :
    0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (NormFM f hf hnc g) y := by
  classical
  obtain ⟨FF, h_fibre, h_eq⟩ := NormFM_mmeromorphicOrderAt_eq_fibre_sum hf hnc g y
  rw [h_eq]
  apply Finset.sum_nonneg
  intro x _
  exact hg_nonpole x.val (show x.val ∈ f ⁻¹' {y} from h_fibre x.val x.property)

/-- **Punctured neighbourhood is `NeBot` on a `ChartedSpace ℂ`.**

The chart at `y` is an open partial homeomorphism into the perfect
space `ℂ`. Lifting `PerfectSpace.not_isolated` for `c y ∈ ℂ` through
`c.symm` (continuous on `c.target`) gives that `𝓝[≠] y` is `NeBot` in
`Y`. -/
lemma nhdsWithin_compl_singleton_neBot
    {Z : Type*} [TopologicalSpace Z] [T1Space Z] [ChartedSpace ℂ Z]
    (z : Z) : Filter.NeBot (𝓝[≠] z) := by
  rw [← mem_closure_iff_nhdsWithin_neBot]
  -- Show z ∈ closure ({z}ᶜ): every open nbhd of z contains a point ≠ z.
  rw [mem_closure_iff]
  intro V hV_open hzV
  set c : OpenPartialHomeomorph Z ℂ := chartAt ℂ z
  have hzs : z ∈ c.source := mem_chart_source ℂ z
  have hczt : c z ∈ c.target := c.map_source hzs
  have h_open_img : IsOpen (c '' (V ∩ c.source) ∩ c.target) := by
    have h_inter_open : IsOpen (V ∩ c.source) := hV_open.inter c.open_source
    exact (c.isOpen_image_of_subset_source h_inter_open Set.inter_subset_right).inter
      c.open_target
  have hcz_in : c z ∈ c '' (V ∩ c.source) ∩ c.target :=
    ⟨⟨z, ⟨hzV, hzs⟩, rfl⟩, hczt⟩
  -- ℂ is perfect: every open nbhd of (c z) contains a w ≠ c z.
  haveI : Filter.NeBot (𝓝[≠] (c z)) := PerfectSpace.not_isolated _
  have hcz_closure : c z ∈ closure ({c z}ᶜ) := mem_closure_iff_nhdsWithin_neBot.mpr (by infer_instance)
  rw [mem_closure_iff] at hcz_closure
  obtain ⟨w, ⟨⟨z', ⟨hz'_V, hz'_s⟩, hz'_eq⟩, hw_t⟩, hw_ne_singleton⟩ :=
    hcz_closure (c '' (V ∩ c.source) ∩ c.target) h_open_img hcz_in
  have hw_ne : w ≠ c z := hw_ne_singleton
  refine ⟨z', ⟨hz'_V, ?_⟩⟩
  intro h_eq
  apply hw_ne
  rw [← hz'_eq, h_eq]

/-- **At a regular value with no preimage poles, `NormFM_regularized = NormFM`.**

Composes:
* `NormFM_mmeromorphicOrderAt_nonneg_of_no_poles` (ZZ245) → the
  `0 ≤ mmero NormFM y` branch of `NormFM_regularized` fires.
* `NormFM_continuousAt_of_regular_and_no_poles` (ZZ244) → `NormFM` is
  continuous at `y`, so its limit over `𝓝[≠] y` (which is `NeBot` by
  `nhdsWithin_compl_singleton_neBot`) equals `NormFM y`.

Hence the regularization override at `y` produces the literal value.
This is the unfold the framework needs to identify the regularized
function with `NormFM` on the open dense set of regular no-pole
points. -/
lemma NormFM_regularized_eq_NormFM_at_regular_no_poles
    [Nonempty Y]
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f)
    (g : MeromorphicNonzero X)
    {y : Y} (hy_reg : y ∉ criticalValuesGeneral f)
    (hg_nonpole : ∀ x ∈ f ⁻¹' {y},
        0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g.toFun x) :
    NormFM_regularized hf hnc g y = NormFM f hf hnc g y := by
  have h_nonneg :=
    NormFM_mmeromorphicOrderAt_nonneg_of_no_poles hf hnc g hg_nonpole
  rw [NormFM_regularized_of_nonneg hf hnc g h_nonneg]
  haveI : Filter.NeBot (𝓝[≠] y) := nhdsWithin_compl_singleton_neBot y
  have h_cont : ContinuousAt (NormFM f hf hnc g) y :=
    NormFM_continuousAt_of_regular_and_no_poles hf hnc g hy_reg hg_nonpole
  have h_tendsto :
      Tendsto (NormFM f hf hnc g) (𝓝[≠] y) (𝓝 (NormFM f hf hnc g y)) :=
    h_cont.tendsto.mono_left nhdsWithin_le_nhds
  exact h_tendsto.limUnder_eq

/-! ## Pole-cancellation infrastructure for `NormFM_regularized`

The framework's `regular_continuousAt` field needs `NormFM_regularized`
continuous at every `y₀` with `0 ≤ mmero NormFM_regularized y₀`, including
the harder case where `y₀` has some preimage poles whose orders cancel
in the fibre sum.

The chain (ZZ247→ZZ250→ZZ252) establishes:
* ZZ247 — manifold lift of `tendsto_nhds_of_meromorphicOrderAt_nonneg`.
* ZZ248 — order stability: `0 ≤ mmero g x` ⇒ `g` is analytic on a chart
  ball around `x`, hence `mmero g x' = 0` on the punctured ball.
* ZZ249/250 — for `y` in a punctured nbhd of `y₀`, every preimage of `y`
  via the local section is non-pole, so `mmero NormFM y = 0`.
* ZZ252 — combines to get `NormFM_regularized` continuous at `y₀`. -/

/-- **Manifold version of `tendsto_nhds_of_meromorphicOrderAt_nonneg`.**

If `f : Z → ℂ` is meromorphic at `z` (in the manifold sense) with
non-negative order, then `f` has a limit along the punctured
neighbourhood `𝓝[≠] z`.

Proof: unfold both hypotheses to the chart-pullback `f ∘ c.symm` at
`c z`, apply mathlib's planar `tendsto_nhds_of_meromorphicOrderAt_nonneg`,
and push the conclusion back through `c` (continuous + injective on
`c.source`). -/
lemma tendsto_nhds_of_mmeromorphicOrderAt_nonneg
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    (I : ModelWithCorners ℂ ℂ ℂ) {fZ : Z → ℂ} {z : Z}
    (hfZ : MMeromorphicAt I fZ z)
    (ho : 0 ≤ mmeromorphicOrderAt I fZ z) :
    ∃ L, Tendsto fZ (𝓝[≠] z) (𝓝 L) := by
  classical
  set c : OpenPartialHomeomorph Z ℂ := chartAt ℂ z with hc_def
  have hz_src : z ∈ c.source := mem_chart_source ℂ z
  have hF : MeromorphicAt (fZ ∘ c.symm) (c z) := hfZ
  have hF_ord : 0 ≤ meromorphicOrderAt (fZ ∘ c.symm) (c z) := ho
  obtain ⟨L, hL⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hF hF_ord
  refine ⟨L, ?_⟩
  -- Tendsto c (𝓝[≠] z) (𝓝[≠] (c z)).
  have hc_cont : ContinuousAt c z :=
    c.continuousOn_toFun.continuousAt (c.open_source.mem_nhds hz_src)
  have h_src_nhds : c.source ∈ 𝓝 z := c.open_source.mem_nhds hz_src
  have hc_tendsto_punctured : Tendsto c (𝓝[≠] z) (𝓝[≠] (c z)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hc_cont.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    have h_src_W : c.source ∈ 𝓝[≠] z := nhdsWithin_le_nhds h_src_nhds
    filter_upwards [h_src_W, self_mem_nhdsWithin] with z' hz'_src hz'_ne h_eq
    apply hz'_ne
    exact c.injOn hz'_src hz_src h_eq
  -- Compose with hL.
  have h_comp : Tendsto ((fZ ∘ c.symm) ∘ c) (𝓝[≠] z) (𝓝 L) :=
    hL.comp hc_tendsto_punctured
  -- Eventually on c.source, (f ∘ c.symm) ∘ c = f.
  apply h_comp.congr'
  have h_src_W : c.source ∈ 𝓝[≠] z := nhdsWithin_le_nhds h_src_nhds
  filter_upwards [h_src_W] with z' hz'_src
  show fZ (c.symm (c z')) = fZ z'
  rw [c.left_inv hz'_src]

/-- **σ-stability of non-negativity of `mmero g`.**

For a local section `σ : Y → X` with `σ y₀ = x₀` and `f (σ y) = y` on a
nbhd of `y₀`, the order `mmero g (σ y)` is non-negative on a punctured
neighbourhood of `y₀`, regardless of whether `g` has a pole at `x₀`.

Proof: `g.toFun` is meromorphic at `x₀` (`g.meromorphic`), so by
`MeromorphicAt.eventually_analyticAt` for the chart pullback at `x₀`,
the chart pullback is analytic in a punctured chart ball. The section
`σ` maps `y₀` to `x₀` and is continuous; for `y ≠ y₀`, the section
property `f ∘ σ = id` forces `σ y ≠ x₀` (else `y = f x₀ = y₀`). Hence
`σ y` enters the punctured chart ball where `g` is analytic; combined
with chart independence of `mmero` and `AnalyticAt.meromorphicOrderAt_nonneg`,
this gives `0 ≤ mmero g (σ y)`. -/
lemma eventually_zero_le_mmero_at_section
    {f : X → Y} (g : MeromorphicNonzero X)
    {x₀ : X} {y₀ : Y} (hx₀_y₀ : f x₀ = y₀)
    {σ : Y → X}
    (hσ_y₀ : σ y₀ = x₀) (hσ_cont : ContinuousAt σ y₀)
    (hf_σ : ∀ᶠ y in 𝓝 y₀, f (σ y) = y) :
    ∀ᶠ y in 𝓝[≠] y₀, 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g.toFun (σ y) := by
  classical
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀ with hc_def
  have hx₀_src : x₀ ∈ c.source := mem_chart_source ℂ x₀
  have hg_mero : MMeromorphicAt (𝓘(ℂ, ℂ)) g.toFun x₀ := g.meromorphic x₀ trivial
  have hF_mero : MeromorphicAt (g.toFun ∘ c.symm) (c x₀) := hg_mero
  have h_eventually_an :
      ∀ᶠ w in 𝓝[≠] (c x₀), AnalyticAt ℂ (g.toFun ∘ c.symm) w :=
    hF_mero.eventually_analyticAt
  have hc_cont : ContinuousAt c x₀ :=
    c.continuousOn_toFun.continuousAt (c.open_source.mem_nhds hx₀_src)
  have h_σ_src : ∀ᶠ y in 𝓝 y₀, σ y ∈ c.source := by
    have h_src_at_x₀ : c.source ∈ 𝓝 (σ y₀) := by
      rw [hσ_y₀]; exact c.open_source.mem_nhds hx₀_src
    exact hσ_cont.preimage_mem_nhds h_src_at_x₀
  -- (c ∘ σ) y₀ = c x₀.
  have h_cσ_y₀ : (c ∘ σ) y₀ = c x₀ := by show c (σ y₀) = c x₀; rw [hσ_y₀]
  have h_cσ_cont : ContinuousAt (c ∘ σ) y₀ := by
    have h_at_x₀ : ContinuousAt c (σ y₀) := by rw [hσ_y₀]; exact hc_cont
    exact h_at_x₀.comp hσ_cont
  -- Tendsto (c ∘ σ) (𝓝[≠] y₀) (𝓝[≠] (c x₀)).
  have h_cσ_tendsto_punc : Tendsto (c ∘ σ) (𝓝[≠] y₀) (𝓝[≠] (c x₀)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h_tend : Tendsto (c ∘ σ) (𝓝 y₀) (𝓝 (c x₀)) := by
        rw [← h_cσ_y₀]; exact h_cσ_cont.tendsto
      exact h_tend.mono_left nhdsWithin_le_nhds
    · -- Eventually c (σ y) ≠ c x₀: use f σ y = y, y ≠ y₀, σ y ∈ c.source.
      have h_σ_src_W : ∀ᶠ y in 𝓝[≠] y₀, σ y ∈ c.source :=
        h_σ_src.filter_mono nhdsWithin_le_nhds
      have hf_σ_W : ∀ᶠ y in 𝓝[≠] y₀, f (σ y) = y :=
        hf_σ.filter_mono nhdsWithin_le_nhds
      filter_upwards [h_σ_src_W, hf_σ_W, self_mem_nhdsWithin]
        with y hy_src hfy_eq hy_ne h_eq
      -- h_eq : (c ∘ σ) y = c x₀, i.e. c (σ y) = c x₀.
      apply hy_ne
      -- c injective on source: c (σ y) = c x₀ + σ y ∈ source + x₀ ∈ source → σ y = x₀.
      have h_σy_eq : σ y = x₀ := c.injOn hy_src hx₀_src h_eq
      -- Then y = f (σ y) = f x₀ = y₀.
      show y ∈ ({y₀} : Set Y)
      rw [Set.mem_singleton_iff, ← hfy_eq, h_σy_eq, hx₀_y₀]
  -- Pull back analyticity.
  have h_pulled :
      ∀ᶠ y in 𝓝[≠] y₀, AnalyticAt ℂ (g.toFun ∘ c.symm) ((c ∘ σ) y) :=
    h_cσ_tendsto_punc h_eventually_an
  have h_σ_src_W : ∀ᶠ y in 𝓝[≠] y₀, σ y ∈ c.source :=
    h_σ_src.filter_mono nhdsWithin_le_nhds
  filter_upwards [h_pulled, h_σ_src_W] with y h_an h_src
  have h_ord_eq :
      mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g.toFun (σ y)
        = meromorphicOrderAt (g.toFun ∘ c.symm) (c (σ y)) :=
    mmeromorphicOrderAt_eq_of_isManifold (chart_mem_atlas ℂ x₀) h_src
  rw [h_ord_eq]
  exact h_an.meromorphicOrderAt_nonneg

/-- **Eventual non-negativity of `mmero g` at all local sections.**

Composes `exists_coherent_local_sections_at_regular_value` (ZZ242) with
`eventually_zero_le_mmero_at_section` (ZZ248) applied per `x ∈ FF₀`,
followed by `Filter.eventually_all_finset`. Result: a punctured
neighbourhood of `y₀` on which every section value `σ x y` is a
non-pole of `g`. -/
lemma eventually_zero_le_mmero_at_all_sections
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f)
    (g : MeromorphicNonzero X)
    {y₀ : Y} (hy₀ : y₀ ∉ criticalValuesGeneral f) :
    ∃ (hF₀ : (f ⁻¹' {y₀}).Finite) (σ : X → Y → X)
      (V : Set Y), IsOpen V ∧ y₀ ∈ V ∧
      (∀ x ∈ hF₀.toFinset, σ x y₀ = x) ∧
      (∀ x ∈ hF₀.toFinset, ContinuousAt (σ x) y₀) ∧
      (∀ x ∈ hF₀.toFinset, ∀ y ∈ V, f (σ x y) = y) ∧
      (∀ᶠ y in 𝓝[≠] y₀, ∀ x ∈ hF₀.toFinset,
        0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g.toFun (σ x y)) := by
  classical
  obtain ⟨hF₀, σ, V, hV_open, hy₀_V, hσ_y₀, hσ_cont, hf_σ_id⟩ :=
    exists_coherent_local_sections_at_regular_value hf hnc hy₀
  refine ⟨hF₀, σ, V, hV_open, hy₀_V, hσ_y₀, hσ_cont, hf_σ_id, ?_⟩
  -- For each x ∈ FF₀, σ x is a section, so ZZ248 applies.
  have h_per_x : ∀ x ∈ hF₀.toFinset, ∀ᶠ y in 𝓝[≠] y₀,
      0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g.toFun (σ x y) := by
    intro x hx
    have hx_fibre : x ∈ f ⁻¹' {y₀} := hF₀.mem_toFinset.mp hx
    have hfx_y₀ : f x = y₀ := hx_fibre
    have hf_σ_x : ∀ᶠ y in 𝓝 y₀, f (σ x y) = y := by
      have hV_nhds : V ∈ 𝓝 y₀ := hV_open.mem_nhds hy₀_V
      filter_upwards [hV_nhds] with y hyV
      exact hf_σ_id x hx y hyV
    exact eventually_zero_le_mmero_at_section g hfx_y₀
      (hσ_y₀ x hx) (hσ_cont x hx) hf_σ_x
  -- Finite intersection over FF₀.
  rw [Filter.eventually_all_finset]
  exact h_per_x

end Manifold
end JacobianChallenge

end
