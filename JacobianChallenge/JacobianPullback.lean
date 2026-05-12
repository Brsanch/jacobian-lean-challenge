/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.JacobianPushforward
import JacobianChallenge.Divisor.FiberPullbackWeighted
import JacobianChallenge.Manifold.ContMDiffOmegaAnalytic
import JacobianChallenge.Manifold.RamificationIndex

set_option diagnostics.threshold 100

/-! # Honest pullback descent (ZZ256e, 2026-05-11)

Discharges the `h_desc` hypothesis of `Pic0.pullbackWeighted` for smooth
holomorphic non-constant `f : X → Y` via the manifold-level composition
`g.compSmooth f` (sister chip to P1.4).
-/

noncomputable section

open scoped ContDiff Manifold Topology
open Filter Set

namespace JacobianChallenge

universe u v

variable {X : Type u}
  [TopologicalSpace X] [ChartedSpace ℂ X]
variable {Y : Type v}
  [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-! ## Step 1: Manifold-level composition of MMeromorphicAt with ContMDiff ω -/

/-- For `f : X → Y` smooth holomorphic and `g : Y → ℂ` meromorphic at `f x`,
the composition `g ∘ f` is meromorphic at `x`. Proved by chart pullback:
the planar form `(g ∘ f) ∘ chartX.symm` equals `(g ∘ chartY.symm) ∘
(chartY ∘ f ∘ chartX.symm)` locally, which is `meromorphic ∘ analytic`. -/
lemma MMeromorphicAt.compSmooth
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f) {x : X}
    {g : Y → ℂ} (hg : MMeromorphicAt (𝓘(ℂ, ℂ)) g (f x)) :
    MMeromorphicAt (𝓘(ℂ, ℂ)) (g ∘ f) x := by
  -- Target after unfolding: `MeromorphicAt ((g ∘ f) ∘ chartX.symm) (chartX x)`.
  show MeromorphicAt ((g ∘ f) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀_def
  set F : ℂ → ℂ := (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm with hF_def
  set h : ℂ → ℂ := g ∘ (chartAt ℂ (f x)).symm with hh_def
  -- `F z₀ = chartY (f x)` by chart left-inverse on the source.
  have hF_z₀ : F z₀ = (chartAt ℂ (f x)) (f x) := by
    show (chartAt ℂ (f x)) (f ((chartAt ℂ x).symm ((chartAt ℂ x) x)))
        = (chartAt ℂ (f x)) (f x)
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  -- `h` is meromorphic at `F z₀` (= chart-pullback def of `g.meromorphic` at `f x`).
  have hh_at_Fz₀ : MeromorphicAt h (F z₀) := by
    rw [hF_z₀]; exact hg
  -- `F` is analytic at `z₀`.
  have hF_an : AnalyticAt ℂ F z₀ :=
    JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback hf x
  -- `(h ∘ F)` is meromorphic at `z₀`.
  have h_comp : MeromorphicAt (h ∘ F) z₀ := hh_at_Fz₀.comp_analyticAt hF_an
  -- Eventual equality: `(g ∘ f) ∘ chartX.symm =ᶠ[𝓝 z₀] h ∘ F`.
  have hEq : ((g ∘ f) ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 z₀] (h ∘ F) := by
    -- For z in a small nbhd of z₀, chartX.symm z is near x, so f(chartX.symm z)
    -- is near f x and lies in chartY.source, where chartY.symm ∘ chartY = id.
    have hX_src : (chartAt ℂ x).target ∈ 𝓝 z₀ :=
      (chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x)
    -- The set `{z | chartX.symm z ∈ X-domain}` is open and contains z₀, but
    -- more precisely we want `{z | f(chartX.symm z) ∈ chartY.source}`.
    have hY_src_nhd : (chartAt ℂ (f x)).source ∈ 𝓝 (f x) :=
      (chartAt ℂ (f x)).open_source.mem_nhds (mem_chart_source ℂ (f x))
    -- Continuity of `f ∘ chartX.symm` at z₀: f is continuous (from ContMDiff),
    -- chartX.symm continuous on its target.
    have hf_cont : Continuous f := hf.continuous
    have hSymm_cont : ContinuousAt (chartAt ℂ x).symm z₀ := by
      apply (chartAt ℂ x).continuousAt_symm
      exact mem_chart_target ℂ x
    have h_eval : (chartAt ℂ x).symm z₀ = x :=
      (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
    have hf_symm_cont : ContinuousAt (f ∘ (chartAt ℂ x).symm) z₀ := by
      have := hf_cont.continuousAt.comp hSymm_cont
      exact this
    -- Preimage of chartY.source under f ∘ chartX.symm is in 𝓝 z₀.
    have hPre : (f ∘ (chartAt ℂ x).symm) ⁻¹' (chartAt ℂ (f x)).source ∈ 𝓝 z₀ := by
      apply hf_symm_cont.preimage_mem_nhds
      simp only [Function.comp, h_eval]
      exact hY_src_nhd
    -- On this preimage, the equality holds.
    filter_upwards [hPre] with z hz
    -- hz : (f ∘ chartX.symm) z ∈ chartY.source. Unfold composition.
    change f ((chartAt ℂ x).symm z) ∈ (chartAt ℂ (f x)).source at hz
    show g (f ((chartAt ℂ x).symm z))
        = g ((chartAt ℂ (f x)).symm ((chartAt ℂ (f x)) (f ((chartAt ℂ x).symm z))))
    rw [(chartAt ℂ (f x)).left_inv hz]
  exact h_comp.congr (hEq.symm.filter_mono nhdsWithin_le_nhds)

/-! ## Step 2: Order identity at the composition

For `f : X → Y` smooth holomorphic non-constant and `g : MeromorphicNonzero Y`,
the order at the composition equals (ramification index) · (order at `f x`):
`mmero (g.toFun ∘ f) x = manifoldRamificationIndex f x · mmero g.toFun (f x)`.

This is the manifold lift of `MeromorphicAt.meromorphicOrderAt_comp`. -/

/-- The chart-pullback `F := chartY ∘ f ∘ chartX.symm` is NOT eventually constant
at `z₀ := chartX x` when `f` is smooth holomorphic non-constant. -/
lemma not_eventuallyConst_chart_pullback
    [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X]
    [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (x : X) :
    ¬ Filter.EventuallyConst
        ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) (𝓝 ((chartAt ℂ x) x)) := by
  -- Use the unconditional `ChartPullbackNotEventuallyConstHypothesis` discharge.
  set z₀ : ℂ := (chartAt ℂ x) x
  set F : ℂ → ℂ := (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm
  have hClop :=
    JacobianChallenge.ContMDiff.Owed.degree.clopennessOfLocallyConst_holds (X := X) (Y := Y)
  have hChartNEC :=
    JacobianChallenge.ContMDiff.Owed.degree.chartPullbackNotEventuallyConst_of_clopennessOfLocallyConst
      hClop
  have hFne : ¬ ∀ᶠ z in 𝓝 z₀, F z = (chartAt ℂ (f x)) (f x) :=
    hChartNEC f hf hnc (f x) x rfl
  -- `EventuallyConst F (𝓝 z₀)` ⇒ the constant must be `F z₀ = chartY (f x)`.
  intro hev
  apply hFne
  -- From hev, get a constant `c` such that `F =ᶠ[𝓝 z₀] (fun _ => c)`. By continuity
  -- at z₀ (a neighborhood point), `c = F z₀ = chartY (f x)`.
  rw [Filter.eventuallyConst_iff_exists_eventuallyEq] at hev
  obtain ⟨c, hev⟩ := hev
  have hFz₀ : F z₀ = c := hev.self_of_nhds
  have hFz₀_val : F z₀ = (chartAt ℂ (f x)) (f x) := by
    show (chartAt ℂ (f x)) (f ((chartAt ℂ x).symm ((chartAt ℂ x) x)))
        = (chartAt ℂ (f x)) (f x)
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  filter_upwards [hev] with z hz
  -- hz : F z = c. Want F z = chartY (f x). Use c = F z₀ = chartY (f x).
  rw [hz, ← hFz₀, hFz₀_val]

/-- The order at the composition is the product of `mmero g (f x)` and the
ramification index (lifted to `WithTop ℤ`). Manifold lift of mathlib's
`MeromorphicAt.meromorphicOrderAt_comp`. -/
lemma mmeromorphicOrderAt_compSmooth
    [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X]
    [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (x : X)
    {g : Y → ℂ} (hg : MMeromorphicAt (𝓘(ℂ, ℂ)) g (f x)) :
    mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (g ∘ f) x
      = (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g (f x))
          * ((analyticOrderAt
              (fun z => ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z
                       - ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
              ((chartAt ℂ x) x)).map Nat.cast) := by
  set z₀ : ℂ := (chartAt ℂ x) x
  set F : ℂ → ℂ := (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm
  set h : ℂ → ℂ := g ∘ (chartAt ℂ (f x)).symm
  -- F is analytic at z₀.
  have hF_an : AnalyticAt ℂ F z₀ :=
    JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback hf x
  -- F z₀ = chartY (f x).
  have hF_z₀ : F z₀ = (chartAt ℂ (f x)) (f x) := by
    show (chartAt ℂ (f x)) (f ((chartAt ℂ x).symm ((chartAt ℂ x) x)))
        = (chartAt ℂ (f x)) (f x)
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  -- h is meromorphic at F z₀.
  have hh_at_Fz₀ : MeromorphicAt h (F z₀) := by
    rw [hF_z₀]; exact hg
  -- F is not eventually constant at z₀.
  have hF_nec : ¬ Filter.EventuallyConst F (𝓝 z₀) :=
    not_eventuallyConst_chart_pullback hf hnc x
  -- Eventual equality of planar form with h ∘ F (same as in compSmooth proof).
  have hEq : ((g ∘ f) ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 z₀] (h ∘ F) := by
    have hY_src_nhd : (chartAt ℂ (f x)).source ∈ 𝓝 (f x) :=
      (chartAt ℂ (f x)).open_source.mem_nhds (mem_chart_source ℂ (f x))
    have hf_cont : Continuous f := hf.continuous
    have hSymm_cont : ContinuousAt (chartAt ℂ x).symm z₀ := by
      apply (chartAt ℂ x).continuousAt_symm
      exact mem_chart_target ℂ x
    have h_eval : (chartAt ℂ x).symm z₀ = x :=
      (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
    have hf_symm_cont : ContinuousAt (f ∘ (chartAt ℂ x).symm) z₀ :=
      hf_cont.continuousAt.comp hSymm_cont
    have hPre : (f ∘ (chartAt ℂ x).symm) ⁻¹' (chartAt ℂ (f x)).source ∈ 𝓝 z₀ := by
      apply hf_symm_cont.preimage_mem_nhds
      simp only [Function.comp, h_eval]
      exact hY_src_nhd
    filter_upwards [hPre] with z hz
    change f ((chartAt ℂ x).symm z) ∈ (chartAt ℂ (f x)).source at hz
    show g (f ((chartAt ℂ x).symm z))
        = g ((chartAt ℂ (f x)).symm ((chartAt ℂ (f x)) (f ((chartAt ℂ x).symm z))))
    rw [(chartAt ℂ (f x)).left_inv hz]
  -- Unfold both sides' mmeromorphicOrderAt to the planar form.
  change meromorphicOrderAt ((g ∘ f) ∘ (chartAt ℂ x).symm) z₀
        = meromorphicOrderAt (g ∘ (chartAt ℂ (f x)).symm) ((chartAt ℂ (f x)) (f x))
            * (analyticOrderAt (fun z => F z - F z₀) z₀).map Nat.cast
  -- Replace LHS function via eventual equality (planar congr; weaken to nhdsNE).
  rw [meromorphicOrderAt_congr (hEq.filter_mono nhdsWithin_le_nhds)]
  -- LHS is `meromorphicOrderAt (h ∘ F) z₀`. Apply mathlib's comp lemma.
  rw [MeromorphicAt.meromorphicOrderAt_comp hh_at_Fz₀ hF_an hF_nec, hF_z₀]

/-- The analytic order of the chart-pullback shift is a finite natural number
when `f` is smooth holomorphic non-constant. -/
lemma analyticOrderAt_chart_pullback_ne_top
    [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X]
    [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (x : X) :
    analyticOrderAt
      (fun z => ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z
              - ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
      ((chartAt ℂ x) x) ≠ ⊤ := by
  set z₀ : ℂ := (chartAt ℂ x) x
  set F : ℂ → ℂ := (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm
  have hF_an : AnalyticAt ℂ F z₀ :=
    JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback hf x
  have hF_nec : ¬ Filter.EventuallyConst F (𝓝 z₀) :=
    not_eventuallyConst_chart_pullback hf hnc x
  -- Direct iff: EventuallyConst F (𝓝 z₀) ↔ analyticOrderAt (F · - F z₀) z₀ = ⊤
  intro h_top
  exact hF_nec (eventuallyConst_iff_analyticOrderAt_sub_eq_top.mpr h_top)

/-! ## Step 3: Package `g.compSmooth f` as `MeromorphicNonzero X` -/

/-- The MeromorphicNonzero composition `g ∘ f` for `g : MeromorphicNonzero Y`
and `f : X → Y` smooth holomorphic non-constant. -/
noncomputable def MeromorphicNonzero.compSmooth
    [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X]
    [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    (g : MeromorphicNonzero Y)
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) :
    MeromorphicNonzero X where
  toFun := g.toFun ∘ f
  meromorphic := fun x _ =>
    MMeromorphicAt.compSmooth hf (g.meromorphic (f x) (Set.mem_univ _))
  nonvanishing_germ := by
    intro x
    rw [mmeromorphicOrderAt_compSmooth hf hnc x (g.meromorphic (f x) (Set.mem_univ _))]
    -- Both factors not ⊤; product not ⊤.
    have h1 : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g.toFun (f x) ≠ ⊤ := g.nonvanishing_germ (f x)
    have h2 : (analyticOrderAt _ ((chartAt ℂ x) x)) ≠ ⊤ :=
      analyticOrderAt_chart_pullback_ne_top hf hnc x
    -- Extract finite values via WithTop.ne_top_iff_exists.
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp h1
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h2
    rw [← ha, ← hn]
    simp only [ENat.map_coe, ← WithTop.coe_mul]
    exact WithTop.coe_ne_top
  regular_continuousAt := by
    intro x h_nonneg
    have h_id := mmeromorphicOrderAt_compSmooth hf hnc x
      (g.meromorphic (f x) (Set.mem_univ _))
    -- Extract finite values for both factors.
    have h_a_ne_top : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g.toFun (f x) ≠ ⊤ :=
      g.nonvanishing_germ (f x)
    have h_b_ne_top : (analyticOrderAt _ ((chartAt ℂ x) x)) ≠ ⊤ :=
      analyticOrderAt_chart_pullback_ne_top hf hnc x
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp h_a_ne_top
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h_b_ne_top
    -- Show n ≥ 1: at vanishing point, analyticOrderAt ≠ 0.
    have hF_an : AnalyticAt ℂ
        ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
      JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback hf x
    have hAn_sub : AnalyticAt ℂ
        (fun z => ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z
                - ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
        ((chartAt ℂ x) x) := hF_an.sub analyticAt_const
    have h_vanish_val : (fun z =>
        ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z
          - ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
        ((chartAt ℂ x) x) = 0 := sub_self _
    have h_b_ne_zero : analyticOrderAt _ ((chartAt ℂ x) x) ≠ 0 :=
      hAn_sub.analyticOrderAt_ne_zero.mpr h_vanish_val
    rw [← hn] at h_b_ne_zero
    have hn_pos : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h] at h_b_ne_zero
      · exact h
    -- Now `0 ≤ mmero g (f x) * (n : ℤ)` with `n ≥ 1` ⇒ `0 ≤ mmero g (f x)`.
    rw [h_id, ← ha, ← hn] at h_nonneg
    simp only [ENat.map_coe, ← WithTop.coe_mul, ← WithTop.coe_zero, WithTop.coe_le_coe]
      at h_nonneg
    have h_a_nonneg : (0 : ℤ) ≤ a := by
      have hn_pos_z : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn_pos
      nlinarith [h_nonneg, hn_pos_z]
    have h_a_nonneg_top : (0 : WithTop ℤ) ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g.toFun (f x) := by
      rw [← ha]
      exact_mod_cast h_a_nonneg
    have h_g_cont : ContinuousAt g.toFun (f x) := g.regular_continuousAt (f x) h_a_nonneg_top
    exact h_g_cont.comp hf.continuous.continuousAt

/-! ## Step 4: Divisor identity

For `f : X → Y` smooth holomorphic non-constant and `g : MeromorphicNonzero Y`:
`divPullbackWeighted f hf manifoldRamificationIndex N hN_total (principalDivisorMap g)
  = principalDivisorMap (g.compSmooth f hf hnc)` as `Div X`. -/

/-- Pointwise: the principal divisor of the composition equals the weighted
fiber-sum-pullback of the principal divisor, evaluated at any `x : X`. -/
lemma principalDivisorMap_compSmooth_apply
    [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X]
    [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f)
    (g : MeromorphicNonzero Y) (x : X) :
    ((principalDivisorMap (g.compSmooth hf hnc) : Div X) : X → ℤ) x
      = ((principalDivisorMap g : Div Y) : Y → ℤ) (f x)
          * (JacobianChallenge.Manifold.manifoldRamificationIndex f x : ℤ) := by
  -- LHS = orderFun (g ∘ f) x = (mmero (g ∘ f) x).untop₀.
  rw [principalDivisorMap_apply]
  show (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) ((g.compSmooth hf hnc).toFun) x).untop₀ =
      (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g.toFun (f x)).untop₀ *
        (JacobianChallenge.Manifold.manifoldRamificationIndex f x : ℤ)
  -- (g.compSmooth hf hnc).toFun = g.toFun ∘ f by def.
  change (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (g.toFun ∘ f) x).untop₀ =
      (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g.toFun (f x)).untop₀ *
        (JacobianChallenge.Manifold.manifoldRamificationIndex f x : ℤ)
  rw [mmeromorphicOrderAt_compSmooth hf hnc x (g.meromorphic (f x) (Set.mem_univ _))]
  -- Now compute (a * b.map Nat.cast).untop₀ = a.untop₀ * b.toNat.
  have h_a_ne_top : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g.toFun (f x) ≠ ⊤ :=
    g.nonvanishing_germ (f x)
  have h_b_ne_top : (analyticOrderAt _ ((chartAt ℂ x) x)) ≠ ⊤ :=
    analyticOrderAt_chart_pullback_ne_top hf hnc x
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp h_a_ne_top
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h_b_ne_top
  rw [← ha, ← hn]
  simp only [ENat.map_coe, ← WithTop.coe_mul, WithTop.untop₀_coe]
  -- Goal: a * (n : ℤ) = a * manifoldRamificationIndex.
  -- manifoldRamificationIndex f x = (analyticOrderAt ...).toNat. With hn, this is n.
  congr 1
  show (n : ℤ) = (JacobianChallenge.Manifold.manifoldRamificationIndex f x : ℤ)
  rw [JacobianChallenge.Manifold.manifoldRamificationIndex_eq]
  rw [← hn]
  rfl

/-- Pointwise evaluation of `fiberSumWeightedFun f h e D` at `x : X`:
equals `D(f x) * e(x)`. -/
lemma Div.fiberSumWeightedFun_apply
    [T2Space X] [CompactSpace X]
    [T2Space Y] [CompactSpace Y]
    [DecidableEq X]
    (f : X → Y) (h_finite : ∀ y, (f ⁻¹' {y}).Finite) (e : X → ℕ)
    (D : Div Y) (x : X) :
    ((Div.fiberSumWeightedFun f h_finite e D : Div X) : X → ℤ) x
      = (D : Y → ℤ) (f x) * (e x : ℤ) := by
  classical
  unfold Div.fiberSumWeightedFun
  rw [Function.locallyFinsuppWithin.coe_sum]
  simp only [Finset.sum_apply]
  -- Each summand y evaluates pointwise to: D y * (e x if f x = y else 0).
  have h_inner : ∀ y ∈ D.supportFinset,
      (((D : Y → ℤ) y • (∑ x' ∈ (h_finite y).toFinset,
                            (e x' : ℤ) • (Div.single x' : Div X))) : Div X) x
        = (D : Y → ℤ) y * (if f x = y then (e x : ℤ) else 0) := by
    intro y _
    rw [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, smul_eq_mul]
    congr 1
    -- Goal: (∑ x' ∈ (h_finite y).toFinset, (e x' : ℤ) • single x') x = ...
    -- Rewrite sum-apply
    have h_x_pt : ∀ x' ∈ (h_finite y).toFinset,
        ((((e x' : ℤ) • (Div.single x' : Div X)) : Div X) : X → ℤ) x
          = (e x' : ℤ) * (if x = x' then 1 else 0) :=
      fun x' _ => Div.zsmul_single_apply (e x' : ℤ) x' x
    show (((∑ x' ∈ (h_finite y).toFinset, (e x' : ℤ) • (Div.single x' : Div X)) : Div X) : X → ℤ) x
          = if f x = y then (e x : ℤ) else 0
    rw [Function.locallyFinsuppWithin.coe_sum]
    simp only [Finset.sum_apply]
    rw [Finset.sum_congr rfl h_x_pt]
    by_cases hfx : f x = y
    · -- x ∈ (h_finite y).toFinset
      have h_mem : x ∈ (h_finite y).toFinset := by
        rw [Set.Finite.mem_toFinset]; exact hfx
      rw [if_pos hfx]
      rw [Finset.sum_eq_single x]
      · simp
      · intros x' _ hx'_ne
        rw [if_neg (Ne.symm hx'_ne), mul_zero]
      · intro h_not; exact absurd h_mem h_not
    · -- All terms zero.
      rw [if_neg hfx]
      apply Finset.sum_eq_zero
      intros x' hx'
      rw [Set.Finite.mem_toFinset] at hx'
      by_cases h_eq : x = x'
      · exfalso; apply hfx; rw [h_eq]; exact hx'
      · rw [if_neg h_eq, mul_zero]
  rw [Finset.sum_congr rfl h_inner]
  -- Now sum = ∑ y ∈ supp D, D y * (e x if f x = y else 0)
  --        = D (f x) * e x.
  by_cases hfx_supp : f x ∈ D.supportFinset
  · rw [Finset.sum_eq_single (f x)]
    · rw [if_pos rfl]
    · intros y _ hy_ne
      rw [if_neg hy_ne.symm, mul_zero]
    · intro h_not; exact absurd hfx_supp h_not
  · -- f x ∉ supp ⇒ D (f x) = 0.
    have hD_zero : (D : Y → ℤ) (f x) = 0 := by
      by_contra h_ne
      exact hfx_supp (Div.mem_supportFinset.mpr h_ne)
    rw [hD_zero, zero_mul]
    apply Finset.sum_eq_zero
    intros y _
    by_cases hfxy : f x = y
    · -- f x = y ⇒ y = f x ⇒ y ∉ supp ⇒ D y = 0.
      have : (D : Y → ℤ) y = 0 := by rw [← hfxy]; exact hD_zero
      rw [this, zero_mul]
    · rw [if_neg hfxy, mul_zero]

/-- The full divisor identity: weighted fiber-sum-pullback of the principal
divisor of `g` is the principal divisor of `g.compSmooth f hf hnc`. -/
lemma fiberSumWeighted_principalDivisorMap
    [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X]
    [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    [DecidableEq X]
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f)
    (h_finite : ∀ y, (f ⁻¹' {y}).Finite)
    (g : MeromorphicNonzero Y) :
    Div.fiberSumWeighted (X := X) (Y := Y) f h_finite
      (JacobianChallenge.Manifold.manifoldRamificationIndex f)
      (principalDivisorMap g)
      = (principalDivisorMap (g.compSmooth hf hnc) : Div X) := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  rw [principalDivisorMap_compSmooth_apply hf hnc g x]
  rw [Div.fiberSumWeighted_apply]
  exact Div.fiberSumWeightedFun_apply f h_finite _ _ x

/-! ## Step 5: The descent -/

/-- The descent obligation for `Pic0.pullbackWeighted` discharges
unconditionally when `f` is smooth holomorphic non-constant: principal
divisors pull back to principal divisors via the weighted fiber sum
with `e := manifoldRamificationIndex f`. -/
theorem Pic0.divPullbackWeighted_descent_of_smooth
    [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X]
    [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    [DecidableEq X]
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f)
    (h_finite : ∀ y, (f ⁻¹' {y}).Finite) (N : ℕ)
    (hN_total : ∀ y, (∑ x ∈ (h_finite y).toFinset,
                        JacobianChallenge.Manifold.manifoldRamificationIndex f x) = N) :
    (PrincDiv Y).addSubgroupOf (Div0 Y) ≤
      ((PrincDiv X).addSubgroupOf (Div0 X)).comap
        (Pic0.divPullbackWeighted f h_finite
          (JacobianChallenge.Manifold.manifoldRamificationIndex f) N hN_total) := by
  -- Unfold PrincDiv = PrincDivHonestCandidate definitionally.
  show (PrincDivHonestCandidate Y).addSubgroupOf (Div0 Y) ≤
      ((PrincDivHonestCandidate X).addSubgroupOf (Div0 X)).comap _
  -- It suffices to show the underlying-Div map `Div.fiberSumWeighted f h e`
  -- sends `PrincDivHonestCandidate Y` into `PrincDivHonestCandidate X`.
  -- Then the .addSubgroupOf (Div0 _) version follows by intersection.
  have h_Div_map :
      PrincDivHonestCandidate Y ≤
        AddSubgroup.comap (Div.fiberSumWeighted f h_finite
            (JacobianChallenge.Manifold.manifoldRamificationIndex f))
          (PrincDivHonestCandidate X) := by
    unfold PrincDivHonestCandidate
    rw [AddSubgroup.closure_le]
    rintro D' ⟨g, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    show Div.fiberSumWeighted f h_finite
            (JacobianChallenge.Manifold.manifoldRamificationIndex f)
            (principalDivisorMap g)
          ∈ AddSubgroup.closure (Set.range (principalDivisorMap (X := X)))
    rw [fiberSumWeighted_principalDivisorMap hf hnc h_finite g]
    exact AddSubgroup.subset_closure ⟨g.compSmooth hf hnc, rfl⟩
  -- Now lift to the .addSubgroupOf (Div0) version.
  intro D hD
  rw [AddSubgroup.mem_addSubgroupOf] at hD
  rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
  show (Pic0.divPullbackWeighted f h_finite
            (JacobianChallenge.Manifold.manifoldRamificationIndex f) N hN_total D
          : Div X) ∈ PrincDivHonestCandidate X
  rw [Pic0.divPullbackWeighted_coe]
  have := h_Div_map hD
  rw [AddSubgroup.mem_comap] at this
  exact this

end JacobianChallenge

end
