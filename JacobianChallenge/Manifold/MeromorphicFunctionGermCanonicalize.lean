/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicFunctionGermIdentityCorollary

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Germ-side `LiftToMeromorphicNonzero`: canonicalisation + composition

This file ships the **full germ-side analog** of
`JacobianChallenge.LiftToMeromorphicNonzero` from
`Topology/RRGenusZeroFinrankChain.lean`, completing the rebuild of the
Riemann-Roch lifting chain on the honest germ ambient.

## Overview of the construction

Given an `MMer X` representative `f` of a non-zero germ:

1. **All orders finite** (`MMer.AllOrdersNeTop`) — by the identity
   theorem corollary from `MeromorphicFunctionGermIdentityCorollary.
   lean`. The hypothesis `mk f ≠ 0` upgrades to "no point is
   essentially zero".
2. **Punctured continuity** (`MMer.continuousAt_punctured_of_all
   OrdersNeTop`) — the load-bearing technical lemma. At every `y`,
   the Laurent decomposition `f.toFun ∘ chart.symm =ᶠ[𝓝[≠] (chart y)]
   z ↦ (z - chart y)^n • g_y(z)` (mathlib's
   `meromorphicOrderAt_eq_int_iff`) intersected with the analytic
   neighborhood of `g_y` produces an open chart-nhd of `(chart y)`
   on which the chart pullback equals an analytic-times-zpow rep
   pointwise. So `f.toFun` is continuous at every `w ≠ y` in a
   chart-nhd of `y`.
3. **germLimit-EventuallyEq** (`MMer.germLimit_eventuallyEq_self`) —
   continuity at `w` ⇒ Tendsto at `w` ⇒ `germLimit f.toFun w =
   f.toFun w`. Hence `germLimit f.toFun =ᶠ[𝓝[≠] y] f.toFun` at every
   `y`.
4. **Canonicalisation** (`MMer.canonicalize`) — define
   `f_canon := germLimit f.toFun`. By the EvEq, `f_canon` is meromorphic
   (chart-side `MeromorphicAt.congr`) and has the same order at every
   point.
5. **Continuity at regulars** (`MMer.canonicalize_continuousAt_of_
   orderNonneg`) — at every `y` with `order ≥ 0`, `f_canon y` is the
   chart-side punctured limit, hence continuous.
6. **Package** as `MMer.toMeromorphicNonzero` and compose with the
   previous chips for the final `liftToMeromorphicNonzero_germ`
   theorem.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set
open JacobianChallenge.MeromorphicNonzero
  (germLimit germLimit_eq_of_tendsto germLimit_eq_self_of_not_tendsto
   chartSymm_tendsto_nhdsNE chart_tendsto_nhdsNE nhdsNE_neBot)

namespace JacobianChallenge.MeromorphicFunctionField

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## `MMer.AllOrdersNeTop` predicate -/

/-- Predicate: `∀ y, mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun y ≠ ⊤`. -/
def MMer.AllOrdersNeTop (f : MMer X) : Prop :=
  ∀ y : X, mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y ≠ ⊤

/-- Representatives of non-zero germs have `AllOrdersNeTop`. -/
lemma MMer.allOrdersNeTop_of_mk_ne_zero
    {f : MMer X}
    (h : (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm X) ≠ 0) :
    MMer.AllOrdersNeTop f :=
  MeromorphicFunctionGerm.allOrdersNeTop_of_ne_zero h

/-! ## Punctured continuity: the load-bearing lemma

Under `AllOrdersNeTop`, the function `f.toFun` is continuous at every
point of a punctured chart-neighborhood of every `y`. The mechanism
is the Laurent decomposition (mathlib's `meromorphicOrderAt_eq_int_
iff`) intersected with the analytic neighborhood of the leading
nonzero coefficient `g_y`. -/

/-- Helper: the Laurent rep `(z - z₀) ^ n • g z` is `ContinuousAt z`
when `g` is `AnalyticAt z` and `z ≠ z₀`. -/
private lemma laurent_continuousAt
    {z₀ z : ℂ} (hz : z ≠ z₀) {n : ℤ} {g : ℂ → ℂ}
    (hg_an : AnalyticAt ℂ g z) :
    ContinuousAt (fun w => (w - z₀) ^ n • g w) z := by
  -- `w ↦ w - z₀` is analytic, nonzero at z (since z ≠ z₀), hence zpow analytic.
  have h_sub_an : AnalyticAt ℂ (fun w : ℂ => w - z₀) z :=
    (analyticAt_id (𝕜 := ℂ) (z := z)).sub analyticAt_const
  have h_sub_ne : (fun w : ℂ => w - z₀) z ≠ 0 := by
    show z - z₀ ≠ 0
    exact sub_ne_zero.mpr hz
  have h_zpow_an : AnalyticAt ℂ (fun w : ℂ => (w - z₀) ^ n) z :=
    h_sub_an.zpow h_sub_ne
  have h_smul_an : AnalyticAt ℂ (fun w : ℂ => (w - z₀) ^ n • g w) z :=
    h_zpow_an.smul hg_an
  exact h_smul_an.continuousAt

/-- **Load-bearing lemma**: under `AllOrdersNeTop`, `f.toFun` is
continuous at every `w` in a punctured neighborhood of every `y`. -/
lemma MMer.continuousAt_punctured_of_allOrdersNeTop
    {f : MMer X} (hf : MMer.AllOrdersNeTop f) (y : X) :
    ∀ᶠ w in 𝓝[≠] y, ContinuousAt f.toFun w := by
  -- Extract the Laurent decomposition at chart_y(y).
  have h_chart_mero : MeromorphicAt (f.toFun ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) :=
    f.mmero y trivial
  set n : ℤ := (mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y).untop₀ with hn_def
  have h_order_eq : meromorphicOrderAt (f.toFun ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y)
      = (n : WithTop ℤ) :=
    (WithTop.coe_untop₀_of_ne_top (hf y)).symm
  rcases (meromorphicOrderAt_eq_int_iff h_chart_mero).mp h_order_eq with
    ⟨g_y, hg_an, _hg_ne, hg_evEq⟩
  -- `hg_evEq : ∀ᶠ z in 𝓝[≠] (chart y), f.toFun ∘ chart.symm z = (z - chart y)^n • g_y z`.
  -- Step: extract open U with `chart y ∈ U` on which the Laurent rep holds off `chart y`.
  rw [eventually_nhdsWithin_iff] at hg_evEq
  rcases mem_nhds_iff.mp hg_evEq with ⟨U₀, hU₀_sub, hU₀_open, hU₀_mem⟩
  -- Extract analytic-nhd of g_y at chart_y(y).
  have h_g_evAn : ∀ᶠ z in 𝓝 ((chartAt ℂ y) y), AnalyticAt ℂ g_y z :=
    hg_an.eventually_analyticAt
  rcases mem_nhds_iff.mp h_g_evAn with ⟨U₁, hU₁_sub, hU₁_open, hU₁_mem⟩
  -- Intersect with chart.target so chart.symm is defined on the relevant region.
  set V : Set ℂ := U₀ ∩ U₁ ∩ (chartAt ℂ y).target with hV_def
  have hV_open : IsOpen V :=
    (hU₀_open.inter hU₁_open).inter (chartAt ℂ y).open_target
  have hV_mem : (chartAt ℂ y) y ∈ V :=
    ⟨⟨hU₀_mem, hU₁_mem⟩,
     (chartAt ℂ y).map_source (mem_chart_source ℂ y)⟩
  -- Manifold-side open: `(chart_y) ⁻¹' V ∩ chart_y.source`.
  set Wmfd : Set X := (chartAt ℂ y).source ∩ (chartAt ℂ y) ⁻¹' V with hWmfd_def
  have hWmfd_open : IsOpen Wmfd :=
    (chartAt ℂ y).continuousOn_toFun.isOpen_inter_preimage
      (chartAt ℂ y).open_source hV_open
  have hy_in_W : y ∈ Wmfd := by
    refine ⟨mem_chart_source ℂ y, ?_⟩
    show (chartAt ℂ y) y ∈ V
    exact hV_mem
  -- For w in Wmfd, w ≠ y, show ContinuousAt f.toFun w.
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hWmfd_open.mem_nhds hy_in_W] with w hw_in hw_ne
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw_ne
  obtain ⟨hw_src, hw_pre⟩ := hw_in
  set z : ℂ := (chartAt ℂ y) w with hz_def
  have hz_in_V : z ∈ V := hw_pre
  have hz_in_U₀ : z ∈ U₀ := hz_in_V.1.1
  have hz_in_U₁ : z ∈ U₁ := hz_in_V.1.2
  have hz_in_target : z ∈ (chartAt ℂ y).target := hz_in_V.2
  have hz_ne : z ≠ (chartAt ℂ y) y := by
    intro h_eq
    apply hw_ne
    have hsymm_w : (chartAt ℂ y).symm z = w := (chartAt ℂ y).left_inv hw_src
    have hsymm_y : (chartAt ℂ y).symm ((chartAt ℂ y) y) = y :=
      (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
    rw [← hsymm_w, h_eq, hsymm_y]
  -- g_y is analytic at z.
  have hg_an_at_z : AnalyticAt ℂ g_y z := hU₁_sub hz_in_U₁
  -- The Laurent rep is ContinuousAt z.
  have h_laurent_cts : ContinuousAt
      (fun z' : ℂ => (z' - (chartAt ℂ y) y) ^ n • g_y z') z :=
    laurent_continuousAt hz_ne hg_an_at_z
  -- `f.toFun ∘ chart.symm` agrees with the Laurent rep on `U₀ \ {chart y}` (open),
  -- which is an open nhd of z. By EventuallyEq.continuousAt_iff,
  -- `f.toFun ∘ chart.symm` is ContinuousAt z.
  have h_U₀_minus_y_open : IsOpen (U₀ \ {(chartAt ℂ y) y}) :=
    hU₀_open.sdiff isClosed_singleton
  have hz_in_minus : z ∈ U₀ \ {(chartAt ℂ y) y} := ⟨hz_in_U₀, by simp [hz_ne]⟩
  have h_laurent_evEq : (f.toFun ∘ (chartAt ℂ y).symm)
      =ᶠ[𝓝 z]
      (fun z' : ℂ => (z' - (chartAt ℂ y) y) ^ n • g_y z') := by
    filter_upwards [h_U₀_minus_y_open.mem_nhds hz_in_minus] with z' hz'
    obtain ⟨hz'_U₀, hz'_ne_chart⟩ := hz'
    simp only [Set.mem_singleton_iff] at hz'_ne_chart
    exact hU₀_sub hz'_U₀ hz'_ne_chart
  have h_chart_pullback_cts : ContinuousAt (f.toFun ∘ (chartAt ℂ y).symm) z :=
    (continuousAt_congr h_laurent_evEq).mpr h_laurent_cts
  -- Pull back through `chart_y` to get manifold-side ContinuousAt.
  have h_chart_cts_at_w : ContinuousAt (chartAt ℂ y) w :=
    ((chartAt ℂ y).continuousOn_toFun.continuousAt
      ((chartAt ℂ y).open_source.mem_nhds hw_src))
  have h_chart_at_w_eq : (chartAt ℂ y) w = z := hz_def.symm
  -- ContinuousAt of composition + manifold-side identity on chart.source.
  have h_compose_cts : ContinuousAt
      ((f.toFun ∘ (chartAt ℂ y).symm) ∘ (chartAt ℂ y)) w := by
    have h_chart_cts' : ContinuousAt (chartAt ℂ y) w := h_chart_cts_at_w
    have : ContinuousAt (f.toFun ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) w) := by
      rw [h_chart_at_w_eq]; exact h_chart_pullback_cts
    exact this.comp h_chart_cts'
  -- Identify `(f.toFun ∘ chart.symm) ∘ chart_y = f.toFun` on chart_y.source nhd of w.
  have h_id_on_src : ((f.toFun ∘ (chartAt ℂ y).symm) ∘ (chartAt ℂ y))
      =ᶠ[𝓝 w] f.toFun := by
    filter_upwards [(chartAt ℂ y).open_source.mem_nhds hw_src] with w' hw'_src
    show f.toFun ((chartAt ℂ y).symm ((chartAt ℂ y) w')) = f.toFun w'
    rw [(chartAt ℂ y).left_inv hw'_src]
  exact (continuousAt_congr h_id_on_src).mp h_compose_cts

/-! ## germLimit-EventuallyEq

Under `AllOrdersNeTop`, the germLimit of `f.toFun` is punctured-EvEq
to `f.toFun` itself. This is the bridge for the canonicalisation. -/

/-- Under `AllOrdersNeTop`, `germLimit f.toFun =ᶠ[𝓝[≠] y] f.toFun` for
every `y`. -/
lemma MMer.germLimit_eventuallyEq_self
    {f : MMer X} (hf : MMer.AllOrdersNeTop f) (y : X) :
    germLimit f.toFun =ᶠ[𝓝[≠] y] f.toFun := by
  -- At w near y, w ≠ y, f.toFun is ContinuousAt w (the punctured-continuity lemma).
  -- ContinuousAt ⇒ Tendsto on 𝓝[≠] w ⇒ germLimit picks f.toFun w.
  filter_upwards [MMer.continuousAt_punctured_of_allOrdersNeTop hf y] with w h_cts_w
  show germLimit f.toFun w = f.toFun w
  have h_tend : Filter.Tendsto f.toFun (𝓝[≠] w) (𝓝 (f.toFun w)) :=
    h_cts_w.tendsto.mono_left nhdsWithin_le_nhds
  exact germLimit_eq_of_tendsto h_tend

/-! ## Canonicalisation: from `MMer X` + `AllOrdersNeTop` to a
canonical `MMer X` with the same germ and additional continuity. -/

/-- The germLimit-canonicalised `MMer`. Its `toFun` is the punctured-
neighborhood limit of the original `f.toFun` (or the original value
if no limit exists). Meromorphic by `MeromorphicAt.congr` with `f`,
since `germLimit f.toFun =ᶠ[𝓝[≠] y] f.toFun` (chart-pulled back). -/
noncomputable def MMer.canonicalize
    (f : MMer X) (hf : MMer.AllOrdersNeTop f) : MMer X where
  toFun := germLimit f.toFun
  mmero := by
    intro y _
    -- Show MeromorphicAt ((germLimit f.toFun) ∘ chart.symm) (chart y).
    have h_chart_evEq : (germLimit f.toFun) ∘ (chartAt ℂ y).symm
        =ᶠ[𝓝[≠] ((chartAt ℂ y) y)] f.toFun ∘ (chartAt ℂ y).symm :=
      (chartSymm_tendsto_nhdsNE y).eventually (MMer.germLimit_eventuallyEq_self hf y)
    have h_chart_f_mero : MeromorphicAt (f.toFun ∘ (chartAt ℂ y).symm)
        ((chartAt ℂ y) y) := f.mmero y trivial
    exact h_chart_f_mero.congr h_chart_evEq.symm

@[simp] lemma MMer.canonicalize_toFun
    (f : MMer X) (hf : MMer.AllOrdersNeTop f) :
    (MMer.canonicalize f hf).toFun = germLimit f.toFun := rfl

/-- The canonicalised representative is in the same germ class as the
original. -/
lemma MMer.canonicalize_mk_eq
    (f : MMer X) (hf : MMer.AllOrdersNeTop f) :
    (MeromorphicFunctionGerm.mk (MMer.canonicalize f hf) :
      MeromorphicFunctionGerm X)
      = MeromorphicFunctionGerm.mk f := by
  apply Quotient.sound
  intro y
  show (MMer.canonicalize f hf).toFun =ᶠ[𝓝[≠] y] f.toFun
  exact MMer.germLimit_eventuallyEq_self hf y

/-- Canonicalisation preserves the chart-side order at every point. -/
lemma MMer.canonicalize_order_eq
    (f : MMer X) (hf : MMer.AllOrdersNeTop f) (y : X) :
    mmeromorphicOrderAt 𝓘(ℂ, ℂ) (MMer.canonicalize f hf).toFun y
      = mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y := by
  show meromorphicOrderAt ((MMer.canonicalize f hf).toFun ∘ (chartAt ℂ y).symm)
      ((chartAt ℂ y) y)
      = meromorphicOrderAt (f.toFun ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y)
  apply meromorphicOrderAt_congr
  exact (chartSymm_tendsto_nhdsNE y).eventually
    (MMer.germLimit_eventuallyEq_self hf y)

/-- Canonicalisation preserves the `AllOrdersNeTop` property. -/
lemma MMer.canonicalize_allOrdersNeTop
    (f : MMer X) (hf : MMer.AllOrdersNeTop f) :
    MMer.AllOrdersNeTop (MMer.canonicalize f hf) := by
  intro y
  rw [MMer.canonicalize_order_eq f hf y]
  exact hf y

/-! ## `regular_continuousAt` for the canonicalised function -/

/-- At every `y` with `mmeromorphicOrderAt ... ≥ 0`, the canonicalised
function is `ContinuousAt y`. -/
lemma MMer.canonicalize_continuousAt_of_orderNonneg
    (f : MMer X) (hf : MMer.AllOrdersNeTop f) (y : X)
    (h_reg : 0 ≤ mmeromorphicOrderAt 𝓘(ℂ, ℂ) (MMer.canonicalize f hf).toFun y) :
    ContinuousAt (MMer.canonicalize f hf).toFun y := by
  -- At y, the chart pullback `f.toFun ∘ chart.symm` has order ≥ 0 (by canonicalize_order_eq).
  -- So Tendsto exists to some `c : ℂ` (mathlib `tendsto_nhds_of_meromorphicOrderAt_nonneg`).
  -- Pull back to manifold side. germLimit picks c. On punctured nhd, germLimit ≡ f.toFun,
  -- and f.toFun ≡ Laurent rep ≡ tends to c. So germLimit f.toFun at y = c, and ContinuousAt.
  rw [MMer.canonicalize_order_eq f hf y] at h_reg
  have h_chart_mero : MeromorphicAt (f.toFun ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) :=
    f.mmero y trivial
  obtain ⟨c, h_chart_tend⟩ :=
    tendsto_nhds_of_meromorphicOrderAt_nonneg h_chart_mero h_reg
  -- Transport to manifold side.
  have h_mfd_tend : Filter.Tendsto f.toFun (𝓝[≠] y) (𝓝 c) := by
    have h_compose : Filter.Tendsto
        ((f.toFun ∘ (chartAt ℂ y).symm) ∘ (chartAt ℂ y))
        (𝓝[≠] y) (𝓝 c) :=
      h_chart_tend.comp (chart_tendsto_nhdsNE y)
    apply h_compose.congr'
    have h_src_mem : (chartAt ℂ y).source ∈ 𝓝[≠] y :=
      nhdsWithin_le_nhds
        ((chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y))
    filter_upwards [h_src_mem] with z hz
    show f.toFun ((chartAt ℂ y).symm ((chartAt ℂ y) z)) = f.toFun z
    rw [(chartAt ℂ y).left_inv hz]
  -- germLimit f.toFun y = c (by germLimit_eq_of_tendsto).
  have h_germLimit_y : germLimit f.toFun y = c := germLimit_eq_of_tendsto h_mfd_tend
  -- Show ContinuousAt: by `continuousAt_iff_punctured_nhds` (Tendsto from 𝓝[≠] y matches value at y).
  show ContinuousAt (germLimit f.toFun) y
  rw [continuousAt_iff_punctured_nhds]
  rw [h_germLimit_y]
  -- Need: Tendsto (germLimit f.toFun) (𝓝[≠] y) (𝓝 c).
  -- Use h_mfd_tend (Tendsto f.toFun) congr'd with germLimit_eventuallyEq_self.
  apply h_mfd_tend.congr'
  exact (MMer.germLimit_eventuallyEq_self hf y).symm

/-! ## Packaging: `MMer.toMeromorphicNonzero` -/

/-- Build a `MeromorphicNonzero X` from an `MMer X` whose germ is
non-zero (equivalently: `AllOrdersNeTop`). -/
noncomputable def MMer.toMeromorphicNonzero
    (f : MMer X) (hf : MMer.AllOrdersNeTop f) :
    MeromorphicNonzero X where
  toFun := (MMer.canonicalize f hf).toFun
  meromorphic := (MMer.canonicalize f hf).mmero
  nonvanishing_germ := MMer.canonicalize_allOrdersNeTop f hf
  regular_continuousAt := MMer.canonicalize_continuousAt_of_orderNonneg f hf

@[simp] lemma MMer.toMeromorphicNonzero_toFun
    (f : MMer X) (hf : MMer.AllOrdersNeTop f) :
    (MMer.toMeromorphicNonzero f hf).toFun = germLimit f.toFun := rfl

/-- The `MeromorphicNonzero` representative preserves the order at every
point of the original `f`. -/
lemma MMer.toMeromorphicNonzero_order_eq
    (f : MMer X) (hf : MMer.AllOrdersNeTop f) (y : X) :
    mmeromorphicOrderAt 𝓘(ℂ, ℂ) (MMer.toMeromorphicNonzero f hf).toFun y
      = mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y :=
  MMer.canonicalize_order_eq f hf y

/-! ## Final composition: germ-side `liftToMeromorphicNonzero` -/

/-- **Germ-side `liftToMeromorphicNonzero`.** Given a non-constant
germ `φ` in `linearSystemGermDeltaP p`, produce a `MeromorphicNonzero
X` with the same order bounds and non-constancy. The germ-side analog
of `JacobianChallenge.LiftToMeromorphicNonzero`. -/
theorem MeromorphicFunctionGerm.liftToMeromorphicNonzero
    {p : X} {φ : MeromorphicFunctionGerm X}
    (hφ_in : φ ∈ linearSystemGermDeltaP p)
    (hφ_not : φ ∉ constantsGerm X) :
    ∃ f : MeromorphicNonzero X,
      (∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun x) ∧
      (((-1 : ℤ) : WithTop ℤ) ≤ mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun p) ∧
      ¬ JacobianChallenge.IsConstantMap f.toFun := by
  -- Pick a representative.
  rcases φ with ⟨f⟩
  -- φ ≠ 0 (constantsGerm contains 0).
  have h_ne_zero : (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm X) ≠ 0 := by
    intro h_zero
    apply hφ_not
    show (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm X) ∈ constantsGerm X
    rw [h_zero]
    exact Submodule.zero_mem _
  have hf_all : MMer.AllOrdersNeTop f :=
    MMer.allOrdersNeTop_of_mk_ne_zero h_ne_zero
  -- Order bounds (germ-side ⇒ representative-side via orderAt_mk).
  have hφ_in' : IsBoundedByDeltaPGerm p (MeromorphicFunctionGerm.mk f) := hφ_in
  rw [IsBoundedByDeltaPGerm_mk_iff] at hφ_in'
  obtain ⟨hf_p, hf_off⟩ := hφ_in'
  -- Build the MeromorphicNonzero.
  refine ⟨MMer.toMeromorphicNonzero f hf_all, ?_, ?_, ?_⟩
  · intro x hx
    rw [MMer.toMeromorphicNonzero_order_eq f hf_all x]
    exact hf_off x hx
  · rw [MMer.toMeromorphicNonzero_order_eq f hf_all p]
    exact hf_p
  · -- Non-constancy: if `(f_canon).toFun` were constant, its germ would be a constant germ,
    -- but φ ∉ constantsGerm by assumption. (canonicalise preserves the germ.)
    intro h_const
    apply hφ_not
    -- `h_const : IsConstantMap (toMeromorphicNonzero f hf_all).toFun`, i.e., ∃ c, ∀ x, ... = c.
    -- The canonicalised function's germ equals the original germ via `canonicalize_mk_eq`.
    -- A globally-constant function has germ in `Submodule.span ℂ {1} = constantsGerm`.
    rcases h_const with ⟨c, hc⟩
    -- `hc : ∀ x, (toMeromorphicNonzero f hf_all).toFun x = c`. So
    -- `(toMeromorphicNonzero f hf_all).toFun = fun _ => c` literally.
    have h_canon_eq_const :
        (MMer.toMeromorphicNonzero f hf_all).toFun = (fun _ : X => c) := by
      funext x; exact hc x
    -- Hence `mk f = mk (canonicalize f hf_all) = mk (MMer.const c)`.
    have h_mk_eq : (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm X)
        = MeromorphicFunctionGerm.mk (MMer.const c) := by
      rw [← MMer.canonicalize_mk_eq f hf_all]
      apply Quotient.sound
      intro y
      show (MMer.canonicalize f hf_all).toFun =ᶠ[𝓝[≠] y] (MMer.const c).toFun
      apply Filter.Eventually.of_forall
      intro z
      show (MMer.canonicalize f hf_all).toFun z = (MMer.const c).toFun z
      show (MMer.toMeromorphicNonzero f hf_all).toFun z = c
      exact hc z
    -- `mk (MMer.const c) = c • 1` in the germ field, which is in `constantsGerm = span ℂ {1}`.
    show (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm X) ∈ constantsGerm X
    rw [h_mk_eq]
    -- `mk (MMer.const c) = c • 1`: pointwise `c = c * 1`.
    have h_const_smul : (MeromorphicFunctionGerm.mk (MMer.const c) : MeromorphicFunctionGerm X)
        = c • (1 : MeromorphicFunctionGerm X) := by
      show MeromorphicFunctionGerm.mk (MMer.const c) =
        c • MeromorphicFunctionGerm.mk (1 : MMer X)
      rw [MeromorphicFunctionGerm.mk_smul]
      apply Quotient.sound
      intro y
      show (MMer.const c).toFun =ᶠ[𝓝[≠] y] (c • (1 : MMer X)).toFun
      apply Filter.Eventually.of_forall
      intro z
      show c = c • (1 : MMer X).toFun z
      show c = c • (1 : ℂ)
      rw [smul_eq_mul, mul_one]
    rw [h_const_smul]
    show c • (1 : MeromorphicFunctionGerm X) ∈ constantsGerm X
    exact Submodule.smul_mem _ c (one_mem_constantsGerm X)

end JacobianChallenge.MeromorphicFunctionField

end
