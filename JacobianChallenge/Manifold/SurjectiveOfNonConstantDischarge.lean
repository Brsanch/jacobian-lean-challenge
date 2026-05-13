/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ContMDiffOmegaAnalytic
import JacobianChallenge.Manifold.AnalyticContinuationGlobalization
import JacobianChallenge.Manifold.DegreeOneSurjective
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Topology.LocallyConstant.Basic

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `Surjective_of_NonConstant_Analytic_Manifold X Y` UNCONDITIONALLY

This chip discharges input #3 of the item-14 six-input composition:
non-constant `C^ω` maps between compact connected complex 1-manifolds are
surjective. The proof has three legs:

1. **Identity-theorem clopen-globalisation** (this file's
   `globally_const_of_isLocConstAt`): if `f` is locally constant at *any*
   single point, then `f` is globally constant on `X`. Uses the within-
   one-chart identity-theorem helpers (already in the repo:
   `eqOn_const_of_preconnected_of_eventuallyEq`) plus the `ContMDiff …
   ω → AnalyticAt` bridge (`contMDiff_omega_analyticAt_chart_pullback`).

2. **Image is closed and non-empty** (standard: compact image in T2 is
   closed; `X` non-empty from `ConnectedSpace`).

3. **Image is open** (this file's `surjective_of_NonConstant_holds`):
   at every `y₀ = f x₀ ∈ image`, mathlib's `AnalyticAt.
   eventually_constant_or_nhds_le_map_nhds` applied to the chart pullback
   gives a dichotomy. The locally-constant branch yields a contradiction
   via leg 1; the open-map branch is filter-chased back to give
   `range f ∈ 𝓝 y₀`.

Clopen-non-empty in connected `Y` then gives `range f = univ`, i.e. `f`
surjective.

No `sorry`, no `axiom`.
-/

noncomputable section

open Set Filter Topology Metric
open scoped Manifold ContDiff Topology

namespace JacobianChallenge

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-- `f` is **locally constant at `x`**: there is a neighbourhood of `x` on
which `f` takes the value `f x`. -/
abbrev IsLocConstAt (f : X → Y) (x : X) : Prop := ∀ᶠ y in 𝓝 x, f y = f x

/-! ## `LocConst f` is open

If `f` is locally constant on some open `W ∋ x`, then for every `y ∈ W`,
the same `W` witnesses local constancy at `y`. -/

lemma isOpen_setOf_isLocConstAt {f : X → Y} :
    IsOpen {x : X | IsLocConstAt f x} := by
  rw [isOpen_iff_eventually]
  intro x hx
  obtain ⟨W, hW_eq, hW_open, hxW⟩ := _root_.eventually_nhds_iff.mp hx
  rw [eventually_iff_exists_mem]
  refine ⟨W, hW_open.mem_nhds hxW, ?_⟩
  intro y hyW
  show ∀ᶠ z in 𝓝 y, f z = f y
  rw [_root_.eventually_nhds_iff]
  refine ⟨W, ?_, hW_open, hyW⟩
  intro z hzW
  rw [hW_eq z hzW, hW_eq y hyW]

/-! ## `LocConst f` is closed (identity-theorem core)

At any limit point `t` of `LocConst f`, pick a nearby `LocConst` point
`x'` and apply the within-one-chart identity theorem at the chart of
`t`. -/

lemma isClosed_setOf_isLocConstAt {f : X → Y}
    (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f) :
    IsClosed {x : X | IsLocConstAt f x} := by
  rw [← closure_subset_iff_isClosed]
  intro t ht
  show IsLocConstAt f t
  set chartX := chartAt ℂ t with hchartX_def
  set chartY := chartAt ℂ (f t) with hchartY_def
  set p₀ : ℂ := chartX t with hp₀_def
  have ht_source : t ∈ chartX.source := mem_chart_source ℂ t
  have hp₀_target : p₀ ∈ chartX.target := chartX.map_source ht_source
  have hft_source : f t ∈ chartY.source := mem_chart_source ℂ (f t)
  have hf_cts : Continuous f := hf.continuous
  -- V := chartX.source ∩ f⁻¹(chartY.source) — open nbhd of t.
  set V : Set X := chartX.source ∩ f ⁻¹' chartY.source with hV_def
  have hV_open : IsOpen V :=
    chartX.open_source.inter (hf_cts.isOpen_preimage _ chartY.open_source)
  -- g chart pullback AnalyticAt; AnalyticOnNhd on some open N₀ ∋ p₀.
  have h_g_an : AnalyticAt ℂ (chartY ∘ f ∘ chartX.symm) p₀ :=
    JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback
      hf t
  obtain ⟨N, hN_mem, hN_an⟩ := h_g_an.eventually_analyticAt.exists_mem
  rw [_root_.mem_nhds_iff] at hN_mem
  obtain ⟨N₀, hN₀_sub_N, hN₀_open, hp₀_N₀⟩ := hN_mem
  -- chartX '' V open in ℂ.
  have hChartV_open : IsOpen (chartX '' V) :=
    chartX.isOpen_image_of_subset_source hV_open (fun _ hy => hy.1)
  have hp₀_chartV : p₀ ∈ chartX '' V :=
    ⟨t, ⟨ht_source, hft_source⟩, rfl⟩
  -- Open ball B(p₀, ε) ⊆ N₀ ∩ chartX.target ∩ chartX '' V.
  set Ω : Set ℂ := N₀ ∩ chartX.target ∩ chartX '' V
  have hΩ_open : IsOpen Ω :=
    (hN₀_open.inter chartX.open_target).inter hChartV_open
  have hp₀_Ω : p₀ ∈ Ω := ⟨⟨hp₀_N₀, hp₀_target⟩, hp₀_chartV⟩
  obtain ⟨ε, hε_pos, hball_sub_Ω⟩ : ∃ ε > 0, ball p₀ ε ⊆ Ω :=
    Metric.isOpen_iff.mp hΩ_open p₀ hp₀_Ω
  set B : Set ℂ := ball p₀ ε
  have hB_sub_N₀ : B ⊆ N₀ := fun z hz => (hball_sub_Ω hz).1.1
  have hB_sub_target : B ⊆ chartX.target := fun z hz => (hball_sub_Ω hz).1.2
  have hB_sub_chartV : B ⊆ chartX '' V := fun z hz => (hball_sub_Ω hz).2
  have hp₀_B : p₀ ∈ B := Metric.mem_ball_self hε_pos
  have hB_preconn : IsPreconnected B :=
    (convex_ball p₀ ε).isPreconnected
  -- N' := chartX.symm '' B — open nbhd of t in X, contained in V.
  set N' : Set X := chartX.symm '' B
  have hN'_open : IsOpen N' :=
    chartX.isOpen_image_symm_of_subset_target Metric.isOpen_ball hB_sub_target
  have hN'_sub_V : N' ⊆ V := by
    intro x hx
    obtain ⟨z, hzB, hzx⟩ := hx
    obtain ⟨v, hvV, hvz⟩ := hB_sub_chartV hzB
    have : chartX.symm z = v := by
      rw [← hvz]; exact chartX.left_inv hvV.1
    rw [← hzx, this]; exact hvV
  have ht_N' : t ∈ N' := ⟨p₀, hp₀_B, chartX.left_inv ht_source⟩
  -- Pick a LocConst point x' near t.
  have hN'_nhds : N' ∈ 𝓝 t := hN'_open.mem_nhds ht_N'
  rw [mem_closure_iff_nhds] at ht
  obtain ⟨x', hx'_N', hx'_locc⟩ := ht N' hN'_nhds
  -- W open nbhd of x' on which f = f x', contained in N'.
  obtain ⟨W₀, hW₀_eq, hW₀_open, hx'W₀⟩ := _root_.eventually_nhds_iff.mp hx'_locc
  set W : Set X := W₀ ∩ N'
  have hW_open : IsOpen W := hW₀_open.inter hN'_open
  have hx'_W : x' ∈ W := ⟨hx'W₀, hx'_N'⟩
  have hW_sub_W₀ : W ⊆ W₀ := fun _ hy => hy.1
  have hW_sub_N' : W ⊆ N' := fun _ hy => hy.2
  have hW_sub_V : W ⊆ V := fun _ hy => hN'_sub_V (hW_sub_N' hy)
  have hW_eq : ∀ y ∈ W, f y = f x' := fun y hy => hW₀_eq y (hW_sub_W₀ hy)
  -- chartX '' W open ⊆ B, contains z' := chartX x'.
  have hChartW_open : IsOpen (chartX '' W) :=
    chartX.isOpen_image_of_subset_source hW_open (fun y hy => (hW_sub_V hy).1)
  have hChartW_sub_B : chartX '' W ⊆ B := by
    intro z hz
    obtain ⟨y, hyW, hyz⟩ := hz
    obtain ⟨z', hz'B, hz'y⟩ := hW_sub_N' hyW
    have hy_source : y ∈ chartX.source := (hW_sub_V hyW).1
    have h_chartXy : chartX y = z' := by
      rw [← hz'y, chartX.right_inv (hB_sub_target hz'B)]
    rw [← hyz, h_chartXy]; exact hz'B
  set z' : ℂ := chartX x'
  have hz'_chartW : z' ∈ chartX '' W := ⟨x', hx'_W, rfl⟩
  have hz'_B : z' ∈ B := hChartW_sub_B hz'_chartW
  -- g AnalyticOnNhd on B; equals constant c := chartY (f x') on chartX '' W.
  set c : ℂ := chartY (f x')
  have hg_AOnB : AnalyticOnNhd ℂ (chartY ∘ f ∘ chartX.symm) B := by
    intro z hz
    exact hN_an z (hN₀_sub_N (hB_sub_N₀ hz))
  have hg_const_W : ∀ z ∈ chartX '' W,
      (chartY ∘ f ∘ chartX.symm) z = c := by
    intro z hz
    obtain ⟨y, hyW, hyz⟩ := hz
    have hy_source : y ∈ chartX.source := (hW_sub_V hyW).1
    show chartY (f (chartX.symm z)) = c
    rw [← hyz, chartX.left_inv hy_source]
    show chartY (f y) = chartY (f x')
    rw [hW_eq y hyW]
  have hg_evconst_z' :
      (chartY ∘ f ∘ chartX.symm) =ᶠ[𝓝 z'] (fun _ => c) :=
    Filter.eventually_of_mem (hChartW_open.mem_nhds hz'_chartW) hg_const_W
  -- Identity theorem: g = c on B.
  have hg_eqOn_B : EqOn (chartY ∘ f ∘ chartX.symm) (fun _ => c) B :=
    JacobianChallenge.ContMDiff.Owed.degree.eqOn_const_of_preconnected_of_eventuallyEq
      hg_AOnB hB_preconn hz'_B hg_evconst_z'
  -- chartY (f t) = c, so on N' we have chartY (f y) = chartY (f t).
  have hg_at_p₀ : chartY (f t) = c := by
    have h_inv : chartX.symm p₀ = t := chartX.left_inv ht_source
    have heq : (chartY ∘ f ∘ chartX.symm) p₀ = c := hg_eqOn_B hp₀_B
    have : chartY (f (chartX.symm p₀)) = c := heq
    rw [h_inv] at this
    exact this
  have h_f_eq_on_N' : ∀ y ∈ N', f y = f t := by
    intro y hyN'
    have hy_V : y ∈ V := hN'_sub_V hyN'
    have hy_source : y ∈ chartX.source := hy_V.1
    have hfy_source : f y ∈ chartY.source := hy_V.2
    obtain ⟨z, hzB, hzy⟩ := hyN'
    have h_chartXy : chartX y = z := by
      rw [← hzy, chartX.right_inv (hB_sub_target hzB)]
    have h_eq_c : (chartY ∘ f ∘ chartX.symm) (chartX y) = c := by
      rw [h_chartXy]; exact hg_eqOn_B hzB
    have h_chartXy_inv : chartX.symm (chartX y) = y := chartX.left_inv hy_source
    have h_chartY_fy : chartY (f y) = c := by
      have h2 : chartY (f (chartX.symm (chartX y))) = c := h_eq_c
      rw [h_chartXy_inv] at h2
      exact h2
    have h_eq_chartY : chartY (f y) = chartY (f t) := by
      rw [h_chartY_fy, ← hg_at_p₀]
    exact chartY.injOn hfy_source hft_source h_eq_chartY
  show ∀ᶠ y in 𝓝 t, f y = f t
  exact Filter.eventually_of_mem (hN'_open.mem_nhds ht_N') h_f_eq_on_N'

/-! ## Locally constant at one point ⇒ globally constant -/

/-- **Clopen-globalisation of local constancy.** If `f` is locally constant
at some `x₀`, and `f` is `C^ω`, then `f` is globally constant on connected
`X`. -/
theorem globally_const_of_isLocConstAt {f : X → Y}
    (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f) {x₀ : X}
    (hx₀ : IsLocConstAt f x₀) :
    ∀ x : X, f x = f x₀ := by
  have h_open : IsOpen {x : X | IsLocConstAt f x} := isOpen_setOf_isLocConstAt
  have h_closed : IsClosed {x : X | IsLocConstAt f x} :=
    isClosed_setOf_isLocConstAt hf
  have h_clopen : IsClopen {x : X | IsLocConstAt f x} := ⟨h_closed, h_open⟩
  have h_nonempty : ({x : X | IsLocConstAt f x}).Nonempty := ⟨x₀, hx₀⟩
  have h_locc_univ : {x : X | IsLocConstAt f x} = Set.univ := by
    rcases isClopen_iff.mp h_clopen with h | h
    · exact absurd h h_nonempty.ne_empty
    · exact h
  -- Every x ∈ LocConst, hence IsLocallyConstant f.
  have h_locallyConstant : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have : x ∈ {x : X | IsLocConstAt f x} := by rw [h_locc_univ]; trivial
    exact this
  exact fun x => h_locallyConstant.apply_eq_of_preconnectedSpace x x₀

/-! ## Image is open at every point in the image -/

/-- **Image-is-open from the chart-level open-map dichotomy.** If `f` is
`ContMDiff … ω` and non-constant, then at every `x₀`, the image of `f`
contains an open neighbourhood of `f x₀`. -/
lemma range_mem_nhds_of_nonConstant {f : X → Y}
    (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (x₀ : X) :
    Set.range f ∈ 𝓝 (f x₀) := by
  set chartX := chartAt ℂ x₀ with hchartX_def
  set chartY := chartAt ℂ (f x₀) with hchartY_def
  set p₀ : ℂ := chartX x₀ with hp₀_def
  have hx₀_source : x₀ ∈ chartX.source := mem_chart_source ℂ x₀
  have hp₀_target : p₀ ∈ chartX.target := chartX.map_source hx₀_source
  have hfx₀_source : f x₀ ∈ chartY.source := mem_chart_source ℂ (f x₀)
  have hf_cts : Continuous f := hf.continuous
  -- V := chartX.source ∩ f⁻¹(chartY.source) — open nbhd of x₀.
  set V : Set X := chartX.source ∩ f ⁻¹' chartY.source
  have hV_open : IsOpen V :=
    chartX.open_source.inter (hf_cts.isOpen_preimage _ chartY.open_source)
  have hx₀_V : x₀ ∈ V := ⟨hx₀_source, hfx₀_source⟩
  -- g chart pullback AnalyticAt at p₀.
  have h_g_an : AnalyticAt ℂ (chartY ∘ f ∘ chartX.symm) p₀ :=
    JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback
      hf x₀
  -- Dichotomy: locally constant at p₀, or open map at p₀.
  rcases h_g_an.eventually_constant_or_nhds_le_map_nhds with h_lc | h_open
  · -- Locally constant branch: derive f locally constant at x₀, contradict hnc.
    exfalso
    -- h_lc : ∀ᶠ z in 𝓝 p₀, (chartY ∘ f ∘ chartX.symm) z = (chartY ∘ f ∘ chartX.symm) p₀.
    -- Want IsLocConstAt f x₀.
    have hloc : IsLocConstAt f x₀ := by
      show ∀ᶠ y in 𝓝 x₀, f y = f x₀
      -- Use continuity of chartX at x₀ to pull h_lc back, then chart injectivity.
      have h_chartX_cts : ContinuousAt chartX x₀ :=
        chartX.continuousAt hx₀_source
      have h_chartX_tendsto :
          Filter.Tendsto chartX (𝓝 x₀) (𝓝 p₀) := h_chartX_cts
      have h_lc_x₀ : ∀ᶠ y in 𝓝 x₀,
          (chartY ∘ f ∘ chartX.symm) (chartX y) =
            (chartY ∘ f ∘ chartX.symm) p₀ :=
        h_chartX_tendsto.eventually h_lc
      -- Combine with the open V (chart-source ∩ f-preim source).
      have hV_nhds : V ∈ 𝓝 x₀ := hV_open.mem_nhds hx₀_V
      filter_upwards [h_lc_x₀, hV_nhds] with y hyEq hyV
      -- hyV : y ∈ V, so y ∈ chartX.source and f y ∈ chartY.source.
      -- hyEq : chartY (f (chartX.symm (chartX y))) = chartY (f (chartX.symm p₀)).
      have h_chartXy_inv : chartX.symm (chartX y) = y :=
        chartX.left_inv hyV.1
      have h_chartXp₀_inv : chartX.symm p₀ = x₀ :=
        chartX.left_inv hx₀_source
      have h_eq_chartY : chartY (f y) = chartY (f x₀) := by
        have h := hyEq
        show chartY (f y) = chartY (f x₀)
        have : chartY (f (chartX.symm (chartX y))) =
            chartY (f (chartX.symm p₀)) := h
        rw [h_chartXy_inv, h_chartXp₀_inv] at this
        exact this
      exact chartY.injOn hyV.2 hfx₀_source h_eq_chartY
    -- f globally constant ⇒ IsConstantMap f.
    have h_glob : ∀ x, f x = f x₀ := globally_const_of_isLocConstAt hf hloc
    exact hnc ⟨f x₀, h_glob⟩
  · -- Open-map branch: 𝓝 (chartY (f x₀)) ≤ map (chartY ∘ f ∘ chartX.symm) (𝓝 p₀).
    -- Pull back via chartY.symm to get range f ∈ 𝓝 (f x₀).
    -- The key witness: take the set chartX '' V open ⊆ chartX.target.
    -- Its image under g is chartY '' (f '' V) ⊆ chartY.target, an element of map g (𝓝 p₀).
    have h_chartV_open : IsOpen (chartX '' V) :=
      chartX.isOpen_image_of_subset_source hV_open (fun _ hy => hy.1)
    have hp₀_chartV : p₀ ∈ chartX '' V := ⟨x₀, hx₀_V, rfl⟩
    have h_chartV_nhds : chartX '' V ∈ 𝓝 p₀ :=
      h_chartV_open.mem_nhds hp₀_chartV
    -- The image under g of chartX '' V.
    -- For z = chartX v (v ∈ V), g z = chartY (f v) (using v ∈ chartX.source).
    -- So g '' (chartX '' V) = chartY '' (f '' V).
    have h_g_image_eq :
        (chartY ∘ f ∘ chartX.symm) '' (chartX '' V) = chartY '' (f '' V) := by
      ext z
      constructor
      · rintro ⟨w, ⟨v, hvV, hvw⟩, hwz⟩
        refine ⟨f v, ⟨v, hvV, rfl⟩, ?_⟩
        have : (chartY ∘ f ∘ chartX.symm) w = chartY (f (chartX.symm w)) := rfl
        rw [this] at hwz
        rw [← hwz, ← hvw, chartX.left_inv hvV.1]
      · rintro ⟨y, ⟨v, hvV, hvy⟩, hyz⟩
        refine ⟨chartX v, ⟨v, hvV, rfl⟩, ?_⟩
        show (chartY ∘ f ∘ chartX.symm) (chartX v) = z
        have : (chartY ∘ f ∘ chartX.symm) (chartX v) =
            chartY (f (chartX.symm (chartX v))) := rfl
        rw [this, chartX.left_inv hvV.1, hvy, hyz]
    -- chartY '' (f '' V) ∈ 𝓝 (chartY (f x₀)).
    have h_g_image_nhds_gp₀ :
        (chartY ∘ f ∘ chartX.symm) '' (chartX '' V)
          ∈ 𝓝 ((chartY ∘ f ∘ chartX.symm) p₀) :=
      h_open (Filter.image_mem_map h_chartV_nhds)
    have h_g_p₀_eq : (chartY ∘ f ∘ chartX.symm) p₀ = chartY (f x₀) := by
      show chartY (f (chartX.symm p₀)) = chartY (f x₀)
      rw [chartX.left_inv hx₀_source]
    have h_chartY_image_nhds :
        chartY '' (f '' V) ∈ 𝓝 (chartY (f x₀)) := by
      rw [← h_g_image_eq, ← h_g_p₀_eq]
      exact h_g_image_nhds_gp₀
    -- Extract an open W' ⊆ chartY.target with chartY (f x₀) ∈ W' ⊆ chartY '' (f '' V).
    obtain ⟨W', hW'_sub, hW'_open, hW'_mem⟩ :=
      _root_.mem_nhds_iff.mp h_chartY_image_nhds
    set W'' : Set ℂ := W' ∩ chartY.target
    have hW''_open : IsOpen W'' := hW'_open.inter chartY.open_target
    have hW''_mem : chartY (f x₀) ∈ W'' :=
      ⟨hW'_mem, chartY.map_source hfx₀_source⟩
    have hW''_sub_target : W'' ⊆ chartY.target := fun _ h => h.2
    -- chartY.symm '' W'' open in Y, contained in chartY.source, contains f x₀.
    have h_symmW_open : IsOpen (chartY.symm '' W'') :=
      chartY.isOpen_image_symm_of_subset_target hW''_open hW''_sub_target
    have h_fx₀_symmW : f x₀ ∈ chartY.symm '' W'' :=
      ⟨chartY (f x₀), hW''_mem, chartY.left_inv hfx₀_source⟩
    -- chartY.symm '' W'' ⊆ range f.
    have h_symmW_sub_range : chartY.symm '' W'' ⊆ Set.range f := by
      intro y hy
      obtain ⟨z, hzW'', hzy⟩ := hy
      have hzW' : z ∈ W' := hzW''.1
      have h_z_in_chartY_image : z ∈ chartY '' (f '' V) := hW'_sub hzW'
      obtain ⟨v', ⟨v, hvV, hv_eq_v'⟩, hv'_z⟩ := h_z_in_chartY_image
      refine ⟨v, ?_⟩
      have h_v'_eq : v' = f v := hv_eq_v'.symm
      have h_chartY_fv_z : chartY (f v) = z := by rw [← h_v'_eq]; exact hv'_z
      have hfv_source : f v ∈ chartY.source := hvV.2
      have : chartY.symm z = f v := by
        rw [← h_chartY_fv_z, chartY.left_inv hfv_source]
      rw [← hzy, this]
    -- Range contains an open nbhd of f x₀.
    exact Filter.mem_of_superset (h_symmW_open.mem_nhds h_fx₀_symmW)
      h_symmW_sub_range

/-! ## Image is open: as a set -/

lemma isOpen_range_of_nonConstant {f : X → Y}
    (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) :
    IsOpen (Set.range f) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x₀, hx₀⟩
  rw [← hx₀]
  exact range_mem_nhds_of_nonConstant hf hnc x₀

/-! ## Surjectivity discharge -/

theorem surjective_of_NonConstant_Analytic_Manifold_holds :
    Surjective_of_NonConstant_Analytic_Manifold X Y := by
  intro f hf hnc
  -- Image is open (above), closed (compact image in T2), non-empty (X non-empty).
  have h_open : IsOpen (Set.range f) := isOpen_range_of_nonConstant hf hnc
  have h_closed : IsClosed (Set.range f) := by
    rw [← Set.image_univ]
    exact (isCompact_univ.image hf.continuous).isClosed
  have h_clopen : IsClopen (Set.range f) := ⟨h_closed, h_open⟩
  have h_nonempty : (Set.range f).Nonempty := Set.range_nonempty f
  -- Clopen, non-empty in connected Y ⇒ range f = univ.
  have h_eq_univ : Set.range f = Set.univ := by
    rcases isClopen_iff.mp h_clopen with h | h
    · exact absurd h h_nonempty.ne_empty
    · exact h
  -- Range = univ ⇒ surjective.
  rw [Set.range_eq_univ] at h_eq_univ
  exact h_eq_univ

end JacobianChallenge

end
