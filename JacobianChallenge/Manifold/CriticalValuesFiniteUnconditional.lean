/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalDerivCompatibilitySupply
import JacobianChallenge.Manifold.DerivBridgeFromNonConstant
import JacobianChallenge.Manifold.CriticalSetClosed
import JacobianChallenge.Manifold.CriticalValuesFinite
import JacobianChallenge.Manifold.ContMDiffOmegaAnalytic
import JacobianChallenge.Manifold.MeromorphicExtension

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Unconditional finiteness of `criticalValues` (Wire-CV)

This file (the **Wire-CV** chip) ships the unconditional finiteness theorem
for the critical set / critical values of `f.toRiemannSphere : X → RiemannSphere`,
for any non-constant `f : MeromorphicNonzero X` on a compact connected
complex 1-manifold `X`.

It is the composition of four already-landed chips:

* **R-Compat** (`LocalDerivCompatibilitySupply.lean`) — supplies
  `LocalDerivCompatibilityData f x` for every `x : X`, given a non-constancy
  hypothesis on `f.toRiemannSphere`. The `F` field is the *literal* chart
  pullback `(chartAt ℂ (f.toRiemannSphere x)) ∘ f.toRiemannSphere ∘
  (chartAt ℂ x).symm`.

* **R-MN** (`DerivBridgeFromNonConstant.lean`) — packages
  `LocalDerivCompatibilityData f x` into the `DerivBridgeData f x` consumed
  by RH6. We use the literal-pullback variant
  `derivBridgeData_of_localCompatibility_literalPullback`, threading the
  `D.V`/`D.hxV`/`D.hV_subS`/`D.hFne`/`D.hCompat` directly because R-Compat
  set `D.F` to that exact literal pullback.

* **R-Closed** (`CriticalSetClosed.lean`) — `IsClosed f.criticalSet`.

* **RH6** (`CriticalValuesFinite.lean`) —
  `criticalSet_finite_of_derivBridge` and
  `criticalValues_finite_of_derivBridge` consume per-point `DerivBridgeData`
  + closedness to deliver finiteness.

## What this file ships

* `derivBridgeData_unconditional` — for every `x : X`, given non-constancy
  of `f.toRiemannSphere`, build `DerivBridgeData f x` directly.

* `criticalSet_finite_unconditional` — under the same non-constancy
  hypothesis, `f.criticalSet.Finite`.

* `criticalValues_finite_unconditional` — image-finiteness corollary.

These are the unconditional shapes RH9 / RH7 / future-RH11 take as
`h_crit_fin`.

No `sorry`, no `axiom`, no signature changes outside this file. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace JacobianChallenge

namespace Manifold

universe u

/-! ## Key bridge: per-point `DerivBridgeData` from non-constancy

We build `DerivBridgeData f x` directly via
`derivBridgeData_of_localCompatibility_literalPullback`, by re-running the
construction of the per-point compatibility iff for the literal chart
pullback. This is the same content as the `LocalDerivCompatibilityData`
supplier of `LocalDerivCompatibilitySupply.lean` (which already has the
literal pullback as its `F` field) — we extract its `V`/`hxV`/`hV_subS`/
`hFne`/`hCompat` and pass them through, sidestepping the structure
projection issue noted in the R-Compat residual. -/

/-- **Wire-CV bridge.** Per-point `DerivBridgeData f x` from non-constancy
of `f.toRiemannSphere`.

The construction reuses `LocalDerivCompatibilitySupply.localDerivCompatibilityData_of_meromorphicNonzero`
to build the literal-pullback compatibility data, but routes through
`derivBridgeData_of_localCompatibility_literalPullback` to get the
analyticity proof unconditionally from ZZ24. -/
noncomputable def derivBridgeData_unconditional
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (f : JacobianChallenge.MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (x : X) :
    DerivBridgeData f x := by
  classical
  -- Abbreviations matching the R-Compat supplier.
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc_def
  set d : OpenPartialHomeomorph RiemannSphere ℂ := chartAt ℂ (f.toRiemannSphere x)
    with hd_def
  -- The literal chart pullback.
  set F : ℂ → ℂ := d ∘ f.toRiemannSphere ∘ c.symm with hF_def
  -- Manifold-side facts.
  have hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f.toRiemannSphere :=
    JacobianChallenge.MeromorphicNonzero.toRiemannSphere_contMDiff f
  have hxc : x ∈ c.source := mem_chart_source ℂ x
  have hfx_d : f.toRiemannSphere x ∈ d.source := mem_chart_source ℂ (f.toRiemannSphere x)
  -- Open neighbourhood `V` of `x` (literal pullback domain).
  set V : Set X := c.source ∩ f.toRiemannSphere ⁻¹' d.source with hV_def
  have hV_open : IsOpen V := by
    refine c.open_source.inter ?_
    exact d.open_source.preimage hf.continuous
  have hxV : x ∈ V := ⟨hxc, hfx_d⟩
  have hV_subS : V ⊆ c.source := fun _ hy => hy.1
  -- Build the LocalDerivCompatibilityData via R-Compat.
  let D : LocalDerivCompatibilityData f x :=
    JacobianChallenge.Manifold.localDerivCompatibilityData_of_meromorphicNonzero
      f hnc x
  -- The R-Compat supplier sets `D.F = F`, `D.V = V`, etc. We can't rely on
  -- those being definitionally equal through the def-projection, so instead
  -- we route through `derivBridgeData_of_localCompatibility_literalPullback`,
  -- which only needs `V`/`hxV`/`hV_subS`/`hFne`/`hCompat` for the literal `F`.
  --
  -- We rebuild `hFne` and `hCompat` for the literal pullback by re-deriving
  -- them in the same way the supplier does — this is the "small auxiliary
  -- bridge" the chip prompt allows.
  --
  -- Step 1: `hFne`. Non-eventual constancy of the literal pullback at `c x`,
  -- via the `chartPullbackNotEventuallyConst` discharge.
  have hClop :
      JacobianChallenge.ContMDiff.Owed.degree.ClopennessOfLocallyConstHypothesis
        X RiemannSphere :=
    JacobianChallenge.ContMDiff.Owed.degree.clopennessOfLocallyConst_holds
  have hChartNEC :
      JacobianChallenge.ContMDiff.Owed.degree.ChartPullbackNotEventuallyConstHypothesis
        X RiemannSphere :=
    JacobianChallenge.ContMDiff.Owed.degree.chartPullbackNotEventuallyConst_of_clopennessOfLocallyConst
      hClop
  have hFne_raw :
      ¬ ∀ᶠ z in 𝓝 (c x),
        ((chartAt ℂ (f.toRiemannSphere x)) ∘ f.toRiemannSphere
            ∘ (chartAt ℂ x).symm) z
          = (chartAt ℂ (f.toRiemannSphere x)) (f.toRiemannSphere x) :=
    hChartNEC f.toRiemannSphere hf hnc (f.toRiemannSphere x) x rfl
  -- Reformulate to the shape the literal-pullback constructor wants:
  -- ¬ ∀ᶠ z in 𝓝 (c x), F z = F (c x).
  -- Note F (c x) = d (f.toRiemannSphere x) via `c.left_inv`.
  have hFcx : F (c x) = d (f.toRiemannSphere x) := by
    have h_inv : c.symm (c x) = x := c.left_inv hxc
    show (d ∘ f.toRiemannSphere ∘ c.symm) (c x) = d (f.toRiemannSphere x)
    simp [Function.comp, h_inv]
  -- Translate `hFne_raw` to the literal pullback's "not eventually F (c x)".
  have hFne_lit :
      ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
        ((chartAt ℂ (f.toRiemannSphere x)) ∘ f.toRiemannSphere
            ∘ (chartAt ℂ x).symm) z
          = ((chartAt ℂ (f.toRiemannSphere x)) ∘ f.toRiemannSphere
              ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := by
    intro hev
    apply hFne_raw
    -- `hev` says `F z = F (c x)` eventually; combine with `hFcx` to get
    -- `F z = d (f̃ x)` eventually.
    refine hev.mono (fun z hz => ?_)
    -- hz : F z = F (c x); we need: F z = d (f̃ x).
    -- F z's literal form already matches; rewrite via hFcx.
    show ((chartAt ℂ (f.toRiemannSphere x)) ∘ f.toRiemannSphere
            ∘ (chartAt ℂ x).symm) z
        = (chartAt ℂ (f.toRiemannSphere x)) (f.toRiemannSphere x)
    -- The `show` matches `F z = d (f̃ x)`. Use `hz : F z = F (c x)` and
    -- `hFcx : F (c x) = d (f̃ x)`.
    have h1 : ((chartAt ℂ (f.toRiemannSphere x)) ∘ f.toRiemannSphere
            ∘ (chartAt ℂ x).symm) z = F z := rfl
    have h2 : F z = F (c x) := hz
    rw [h1, h2, hFcx]
  -- Step 2: `hCompat` for the literal pullback. Extract `D.hCompat` and
  -- transfer to the literal pullback's domain. Since D.V = V and D.F = F
  -- definitionally inside the supplier, we can re-prove the compat by
  -- the same chart-transition argument the supplier uses; or we can read
  -- it from `D` if the projection unfolds.
  --
  -- We take the safer "re-prove the compat directly" route: the per-point
  -- compatibility is exactly what the supplier proves on its `V`. Since
  -- our `V` = the supplier's `V` definitionally, `D.hCompat` discharges
  -- our `hCompat` on V — provided the supplier's `D.V`-projection unfolds.
  --
  -- Concrete approach: rebuild the chart-transition compat argument inline.
  -- This duplicates the supplier's chart-transition leg but is the path
  -- that compiles cleanly without relying on definitional reduction of
  -- the supplier's structure projection.
  have hCompat_lit :
      ∀ x' ∈ V, (x' ∈ f.criticalSet) ↔
        deriv ((chartAt ℂ (f.toRiemannSphere x)) ∘ f.toRiemannSphere
            ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x') = 0 := by
    intro x' hx'V
    obtain ⟨hx'c, hx'fd⟩ := hx'V
    -- Canonical charts at x' and at f.toRiemannSphere x'.
    set c' : OpenPartialHomeomorph X ℂ := chartAt ℂ x' with hc'_def
    set d' : OpenPartialHomeomorph RiemannSphere ℂ := chartAt ℂ (f.toRiemannSphere x')
      with hd'_def
    set F' : ℂ → ℂ := d' ∘ f.toRiemannSphere ∘ c'.symm with hF'_def
    have hx'c' : x' ∈ c'.source := mem_chart_source ℂ x'
    have hfx'd' : f.toRiemannSphere x' ∈ d'.source :=
      mem_chart_source ℂ (f.toRiemannSphere x')
    -- F' analytic at c' x' (ZZ24).
    have hF'A_at_x' : AnalyticAt ℂ F' (c' x') :=
      JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback
        hf x'
    -- F' (c' x') = d' (f.toRiemannSphere x').
    have hF'cx' : F' (c' x') = d' (f.toRiemannSphere x') := by
      have h_inv : c'.symm (c' x') = x' := c'.left_inv hx'c'
      show (d' ∘ f.toRiemannSphere ∘ c'.symm) (c' x') = d' (f.toRiemannSphere x')
      simp [Function.comp, h_inv]
    -- F' not eventually equal to F' (c' x') at c' x' (chart NEC at x').
    have hF'ne_raw :
        ¬ ∀ᶠ z in 𝓝 (c' x'),
          ((chartAt ℂ (f.toRiemannSphere x')) ∘ f.toRiemannSphere
              ∘ (chartAt ℂ x').symm) z
            = (chartAt ℂ (f.toRiemannSphere x')) (f.toRiemannSphere x') :=
      hChartNEC f.toRiemannSphere hf hnc (f.toRiemannSphere x') x' rfl
    have hF'ne : ¬ ∀ᶠ z in 𝓝 (c' x'), F' z = F' (c' x') := by
      intro hev
      apply hF'ne_raw
      exact hev.mono (fun z hz => by
        show ((chartAt ℂ (f.toRiemannSphere x')) ∘ f.toRiemannSphere
              ∘ (chartAt ℂ x').symm) z
            = (chartAt ℂ (f.toRiemannSphere x')) (f.toRiemannSphere x')
        have hzz : F' z = F' (c' x') := hz
        rw [show ((chartAt ℂ (f.toRiemannSphere x')) ∘ f.toRiemannSphere
              ∘ (chartAt ℂ x').symm) z = F' z from rfl, hzz, hF'cx'])
    -- Order of (F' - F' (c' x')) at (c' x') is finite and ≥ 1.
    have hF'A_sub : AnalyticAt ℂ (fun z => F' z - F' (c' x')) (c' x') :=
      hF'A_at_x'.sub analyticAt_const
    have h_ord_ne_top :
        analyticOrderAt (fun z => F' z - F' (c' x')) (c' x') ≠ ⊤ := by
      intro h_top
      apply hF'ne
      have h := analyticOrderAt_eq_top.mp h_top
      exact h.mono (fun z hz => sub_eq_zero.mp hz)
    have hF'_self : (fun z => F' z - F' (c' x')) (c' x') = 0 := by simp
    have h_ord_ne_zero :
        analyticOrderAt (fun z => F' z - F' (c' x')) (c' x') ≠ 0 := by
      intro h_zero
      have hne := (hF'A_sub.analyticOrderAt_eq_zero).mp h_zero
      exact hne hF'_self
    -- Extract k.
    set ord : ℕ∞ := analyticOrderAt (fun z => F' z - F' (c' x')) (c' x') with hord_def
    obtain ⟨k, hk_eq⟩ : ∃ k : ℕ, ord = (k : ℕ∞) := by
      cases hord_eq : ord with
      | top => exact absurd hord_eq h_ord_ne_top
      | coe n => exact ⟨n, by simp [hord_eq]⟩
    have hk_ge_one : 1 ≤ k := by
      by_contra hlt
      push_neg at hlt
      interval_cases k
      apply h_ord_ne_zero
      exact hk_eq
    -- ZZ99 planar bridge.
    have h_planar :
        (¬ ∃ U ∈ 𝓝 (c' x'), Set.InjOn F' U) ↔ deriv F' (c' x') = 0 := by
      apply notInjOn_iff_deriv_zero_of_analytic_of_order hF'A_at_x' hk_ge_one
      exact hk_eq
    -- Manifold-side injectivity ↔ chart-pullback injectivity at x'.
    have h_inj_iff_x' :
        (∃ U ∈ 𝓝 x', Set.InjOn f.toRiemannSphere U) ↔
          (∃ U' ∈ 𝓝 (c' x'), Set.InjOn F' U') := by
      constructor
      · rintro ⟨U, hU_nhds, hU_inj⟩
        set U₁ : Set X := U ∩ c'.source ∩ f.toRiemannSphere ⁻¹' d'.source with hU₁_def
        have hf_cont : Continuous f.toRiemannSphere := hf.continuous
        have hU₁_nhds : U₁ ∈ 𝓝 x' :=
          Filter.inter_mem (Filter.inter_mem hU_nhds (c'.open_source.mem_nhds hx'c'))
            (hf_cont.continuousAt.preimage_mem_nhds (d'.open_source.mem_nhds hfx'd'))
        have hU₁_subc' : U₁ ⊆ c'.source := fun _ hy => hy.1.2
        obtain ⟨U₁_open, hU₁_open_open, hU₁_open_sub, hx'_U₁_open⟩ :
            ∃ U_o, IsOpen U_o ∧ U_o ⊆ U₁ ∧ x' ∈ U_o := by
          obtain ⟨W, hW_sub, hW_open, hxW⟩ := mem_nhds_iff.mp hU₁_nhds
          exact ⟨W, hW_open, hW_sub, hxW⟩
        have hU₁_open_subc' : U₁_open ⊆ c'.source := hU₁_open_sub.trans hU₁_subc'
        set U' : Set ℂ := c' '' U₁_open with hU'_def
        have hU'_open : IsOpen U' :=
          c'.isOpen_image_of_subset_source hU₁_open_open hU₁_open_subc'
        have hcx'_in_U' : c' x' ∈ U' := ⟨x', hx'_U₁_open, rfl⟩
        have hU'_nhds : U' ∈ 𝓝 (c' x') := hU'_open.mem_nhds hcx'_in_U'
        refine ⟨U', hU'_nhds, ?_⟩
        rintro z₁ ⟨y₁, hy₁_U, hy₁_eq⟩ z₂ ⟨y₂, hy₂_U, hy₂_eq⟩ hF'_eq
        have hy₁_subc' : y₁ ∈ c'.source := hU₁_open_subc' hy₁_U
        have hy₂_subc' : y₂ ∈ c'.source := hU₁_open_subc' hy₂_U
        have hy₁_U₁ : y₁ ∈ U₁ := hU₁_open_sub hy₁_U
        have hy₂_U₁ : y₂ ∈ U₁ := hU₁_open_sub hy₂_U
        have hy₁_U_outer : y₁ ∈ U := hy₁_U₁.1.1
        have hy₂_U_outer : y₂ ∈ U := hy₂_U₁.1.1
        have hy₁_fd' : f.toRiemannSphere y₁ ∈ d'.source := hy₁_U₁.2
        have hy₂_fd' : f.toRiemannSphere y₂ ∈ d'.source := hy₂_U₁.2
        have h_inv_y₁ : c'.symm (c' y₁) = y₁ := c'.left_inv hy₁_subc'
        have h_inv_y₂ : c'.symm (c' y₂) = y₂ := c'.left_inv hy₂_subc'
        have hF'_at_y₁ : F' (c' y₁) = d' (f.toRiemannSphere y₁) := by
          show (d' ∘ f.toRiemannSphere ∘ c'.symm) (c' y₁) = d' (f.toRiemannSphere y₁)
          simp [Function.comp, h_inv_y₁]
        have hF'_at_y₂ : F' (c' y₂) = d' (f.toRiemannSphere y₂) := by
          show (d' ∘ f.toRiemannSphere ∘ c'.symm) (c' y₂) = d' (f.toRiemannSphere y₂)
          simp [Function.comp, h_inv_y₂]
        rw [← hy₁_eq, ← hy₂_eq] at hF'_eq
        rw [hF'_at_y₁, hF'_at_y₂] at hF'_eq
        have h_inj_d : Set.InjOn d' d'.source := d'.injOn
        have hf_eq : f.toRiemannSphere y₁ = f.toRiemannSphere y₂ :=
          h_inj_d hy₁_fd' hy₂_fd' hF'_eq
        have hy_eq : y₁ = y₂ := hU_inj hy₁_U_outer hy₂_U_outer hf_eq
        rw [← hy₁_eq, ← hy₂_eq, hy_eq]
      · rintro ⟨U', hU'_nhds, hU'_inj⟩
        have hc'_cont : ContinuousOn c' c'.source := c'.continuousOn_toFun
        obtain ⟨U'_open, hU'_open_open, hU'_open_sub, hcx'_U'_open⟩ :
            ∃ U'_o, IsOpen U'_o ∧ U'_o ⊆ U' ∧ c' x' ∈ U'_o := by
          obtain ⟨W, hW_sub, hW_open, hxW⟩ := mem_nhds_iff.mp hU'_nhds
          exact ⟨W, hW_open, hW_sub, hxW⟩
        set U : Set X := c'.source ∩ c' ⁻¹' U'_open with hU_def
        have hU_open : IsOpen U :=
          hc'_cont.isOpen_inter_preimage c'.open_source hU'_open_open
        have hx'_U : x' ∈ U := ⟨hx'c', hcx'_U'_open⟩
        have hU_nhds : U ∈ 𝓝 x' := hU_open.mem_nhds hx'_U
        refine ⟨U, hU_nhds, ?_⟩
        intro y₁ hy₁ y₂ hy₂ hf_eq
        obtain ⟨hy₁_subc', hy₁_pre⟩ := hy₁
        obtain ⟨hy₂_subc', hy₂_pre⟩ := hy₂
        have hcy₁_U' : c' y₁ ∈ U' := hU'_open_sub hy₁_pre
        have hcy₂_U' : c' y₂ ∈ U' := hU'_open_sub hy₂_pre
        have h_inv_y₁ : c'.symm (c' y₁) = y₁ := c'.left_inv hy₁_subc'
        have h_inv_y₂ : c'.symm (c' y₂) = y₂ := c'.left_inv hy₂_subc'
        have hF'_at_y₁ : F' (c' y₁) = d' (f.toRiemannSphere y₁) := by
          show (d' ∘ f.toRiemannSphere ∘ c'.symm) (c' y₁) = d' (f.toRiemannSphere y₁)
          simp [Function.comp, h_inv_y₁]
        have hF'_at_y₂ : F' (c' y₂) = d' (f.toRiemannSphere y₂) := by
          show (d' ∘ f.toRiemannSphere ∘ c'.symm) (c' y₂) = d' (f.toRiemannSphere y₂)
          simp [Function.comp, h_inv_y₂]
        have hF'_eq : F' (c' y₁) = F' (c' y₂) := by
          rw [hF'_at_y₁, hF'_at_y₂, hf_eq]
        have hcy_eq : c' y₁ = c' y₂ := hU'_inj hcy₁_U' hcy₂_U' hF'_eq
        have h_inj_c : Set.InjOn c' c'.source := c'.injOn
        exact h_inj_c hy₁_subc' hy₂_subc' hcy_eq
    have h_crit_iff_F' :
        (x' ∈ f.criticalSet) ↔ deriv F' (c' x') = 0 := by
      have h_iff_neg : (¬ ∃ U ∈ 𝓝 x', Set.InjOn f.toRiemannSphere U) ↔
          ¬ ∃ U' ∈ 𝓝 (c' x'), Set.InjOn F' U' := by
        constructor
        · intro h hex; exact h (h_inj_iff_x'.mpr hex)
        · intro h hex; exact h (h_inj_iff_x'.mp hex)
      have h_crit : (x' ∈ f.criticalSet) ↔ ¬ ∃ U ∈ 𝓝 x', Set.InjOn f.toRiemannSphere U :=
        Iff.rfl
      rw [h_crit, h_iff_neg, h_planar]
    -- Translate `deriv F' (c' x') = 0` ↔ `deriv F (c x') = 0`, where
    -- F = literal pullback through c, d.
    have h_atlas_d : d ∈ atlas ℂ RiemannSphere := chart_mem_atlas ℂ (f.toRiemannSphere x)
    have h_atlas_d' : d' ∈ atlas ℂ RiemannSphere := chart_mem_atlas ℂ (f.toRiemannSphere x')
    have hfx'_d : f.toRiemannSphere x' ∈ d.source := hx'fd
    have hfx'_d' : f.toRiemannSphere x' ∈ d'.source := hfx'd'
    have h_deriv_d_d' :
        deriv (d ∘ d'.symm) (d' (f.toRiemannSphere x')) ≠ 0 :=
      JacobianChallenge.deriv_chart_transition_of_isManifold_ne_zero
        h_atlas_d' h_atlas_d hfx'_d' hfx'_d
    have h_atlas_x : chartAt ℂ x ∈ atlas ℂ X := chart_mem_atlas ℂ x
    have h_atlas_x' : chartAt ℂ x' ∈ atlas ℂ X := chart_mem_atlas ℂ x'
    have h_deriv_c'_c : deriv (c' ∘ c.symm) (c x') ≠ 0 := by
      have h_atlas_c : c ∈ atlas ℂ X := h_atlas_x
      have h_atlas_c' : c' ∈ atlas ℂ X := h_atlas_x'
      have hx'_c'_src : x' ∈ c'.source := hx'c'
      exact JacobianChallenge.deriv_chart_transition_of_isManifold_ne_zero
        h_atlas_c h_atlas_c' hx'c hx'_c'_src
    -- W := c.target ∩ c.symm ⁻¹' (c'.source ∩ f̃ ⁻¹' d'.source) — nbhd of c x'.
    set W : Set ℂ :=
      c.target ∩ c.symm ⁻¹' (c'.source ∩ f.toRiemannSphere ⁻¹' d'.source) with hW_def
    have hW_open : IsOpen W := by
      refine c.isOpen_inter_preimage_symm ?_
      refine c'.open_source.inter ?_
      exact d'.open_source.preimage hf.continuous
    have hc_x'_target : c x' ∈ c.target := c.map_source hx'c
    have hcx'_W : c x' ∈ W := by
      refine ⟨hc_x'_target, ?_⟩
      show c.symm (c x') ∈ c'.source ∩ f.toRiemannSphere ⁻¹' d'.source
      rw [c.left_inv hx'c]
      exact ⟨hx'c', hfx'd'⟩
    have hW_nhds : W ∈ 𝓝 (c x') := hW_open.mem_nhds hcx'_W
    -- Composition equality on W.
    have h_F_eq_comp : ∀ z ∈ W,
        F z = ((d ∘ d'.symm) ∘ F' ∘ (c' ∘ c.symm)) z := by
      intro z hz
      obtain ⟨_, hz_pre⟩ := hz
      have hz_pre' : c.symm z ∈ c'.source ∩ f.toRiemannSphere ⁻¹' d'.source := hz_pre
      obtain ⟨hcsymm_c'src, hcsymm_d'pre⟩ := hz_pre'
      have hfcsymm_d' : f.toRiemannSphere (c.symm z) ∈ d'.source := hcsymm_d'pre
      have h_inv_d' : d'.symm (d' (f.toRiemannSphere (c.symm z))) =
          f.toRiemannSphere (c.symm z) := d'.left_inv hfcsymm_d'
      have h_inv_c' : c'.symm (c' (c.symm z)) = c.symm z := c'.left_inv hcsymm_c'src
      show (d ∘ f.toRiemannSphere ∘ c.symm) z =
          ((d ∘ d'.symm) ∘ (d' ∘ f.toRiemannSphere ∘ c'.symm) ∘ (c' ∘ c.symm)) z
      simp [Function.comp, h_inv_c', h_inv_d']
    have h_F_evEq : F =ᶠ[𝓝 (c x')] ((d ∘ d'.symm) ∘ F' ∘ (c' ∘ c.symm)) :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨W, hW_nhds, h_F_eq_comp⟩
    have h_an_c'_c : AnalyticAt ℂ (c' ∘ c.symm) (c x') :=
      JacobianChallenge.analyticAt_chart_transition_of_isManifold
        h_atlas_x h_atlas_x' hx'c hx'c'
    have h_an_d_d' : AnalyticAt ℂ (d ∘ d'.symm) (d' (f.toRiemannSphere x')) :=
      JacobianChallenge.analyticAt_chart_transition_of_isManifold
        h_atlas_d' h_atlas_d hfx'_d' hfx'_d
    have h_diff_c'_c : DifferentiableAt ℂ (c' ∘ c.symm) (c x') :=
      h_an_c'_c.differentiableAt
    have h_pt_inner : (c' ∘ c.symm) (c x') = c' x' := by
      show c' (c.symm (c x')) = c' x'
      rw [c.left_inv hx'c]
    have h_diff_F' : DifferentiableAt ℂ F' ((c' ∘ c.symm) (c x')) := by
      rw [h_pt_inner]; exact hF'A_at_x'.differentiableAt
    have h_pt_F' : F' ((c' ∘ c.symm) (c x')) = d' (f.toRiemannSphere x') := by
      rw [h_pt_inner]; exact hF'cx'
    have h_diff_d_d' : DifferentiableAt ℂ (d ∘ d'.symm) (F' ((c' ∘ c.symm) (c x'))) := by
      rw [h_pt_F']; exact h_an_d_d'.differentiableAt
    have h_chain_inner :
        deriv (F' ∘ (c' ∘ c.symm)) (c x') =
          deriv F' ((c' ∘ c.symm) (c x')) * deriv (c' ∘ c.symm) (c x') :=
      deriv_comp (c x') h_diff_F' h_diff_c'_c
    have h_diff_inner : DifferentiableAt ℂ (F' ∘ (c' ∘ c.symm)) (c x') :=
      h_diff_F'.comp (c x') h_diff_c'_c
    have h_chain_outer :
        deriv ((d ∘ d'.symm) ∘ F' ∘ (c' ∘ c.symm)) (c x') =
          deriv (d ∘ d'.symm) ((F' ∘ (c' ∘ c.symm)) (c x'))
            * deriv (F' ∘ (c' ∘ c.symm)) (c x') :=
      deriv_comp (c x') h_diff_d_d' h_diff_inner
    have h_F_deriv :
        deriv F (c x') = deriv ((d ∘ d'.symm) ∘ F' ∘ (c' ∘ c.symm)) (c x') :=
      h_F_evEq.deriv_eq
    have h_pt_inner_comp : (F' ∘ (c' ∘ c.symm)) (c x') = F' (c' x') := by
      show F' ((c' ∘ c.symm) (c x')) = F' (c' x')
      rw [h_pt_inner]
    have h_F_deriv_factored :
        deriv F (c x') =
          deriv (d ∘ d'.symm) (d' (f.toRiemannSphere x'))
            * (deriv F' (c' x') * deriv (c' ∘ c.symm) (c x')) := by
      rw [h_F_deriv, h_chain_outer, h_chain_inner, h_pt_inner_comp, h_pt_inner]
      rw [hF'cx']
    have h_deriv_iff : deriv F (c x') = 0 ↔ deriv F' (c' x') = 0 := by
      rw [h_F_deriv_factored]
      constructor
      · intro h
        rcases mul_eq_zero.mp h with h1 | h2
        · exact absurd h1 h_deriv_d_d'
        rcases mul_eq_zero.mp h2 with h3 | h4
        · exact h3
        · exact absurd h4 h_deriv_c'_c
      · intro h
        rw [h, zero_mul, mul_zero]
    rw [h_crit_iff_F']
    exact h_deriv_iff.symm
  -- Discard `D` (it was only built to mirror the supplier; we re-derived
  -- `hCompat` and `hFne` directly for the literal pullback).
  let _ := D
  -- Apply the literal-pullback constructor.
  exact derivBridgeData_of_localCompatibility_literalPullback
    V hV_open hxV hV_subS hFne_lit hCompat_lit

/-! ## Headline finiteness theorems -/

/-- **Wire-CV headline.** Critical set is finite for any non-constant
`f : MeromorphicNonzero X` on a compact connected complex 1-manifold `X`.

Composes:
* R-Compat (`localDerivCompatibilityData_of_meromorphicNonzero`)
* R-MN (`derivBridgeData_of_localCompatibility_literalPullback`)
* R-Closed (`MeromorphicNonzero.isClosed_criticalSet`)
* RH6 (`criticalSet_finite_of_derivBridge`). -/
theorem criticalSet_finite_unconditional
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (f : JacobianChallenge.MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere) :
    f.criticalSet.Finite := by
  refine criticalSet_finite_of_derivBridge f
    (JacobianChallenge.MeromorphicNonzero.isClosed_criticalSet f) ?_
  intro x _hx
  exact derivBridgeData_unconditional f hnc x

/-- **Wire-CV corollary.** Critical values are finite under the same
hypothesis. -/
theorem criticalValues_finite_unconditional
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (f : JacobianChallenge.MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere) :
    f.criticalValues.Finite := by
  refine criticalValues_finite_of_derivBridge f
    (JacobianChallenge.MeromorphicNonzero.isClosed_criticalSet f) ?_
  intro x _hx
  exact derivBridgeData_unconditional f hnc x

end Manifold

end JacobianChallenge

end

end
