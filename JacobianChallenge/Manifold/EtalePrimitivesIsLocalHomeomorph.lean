/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.EtalePrimitives
import JacobianChallenge.Manifold.ChartLocalPrimitiveOverlapLocallyConst
import Mathlib.Topology.IsLocalHomeomorph

set_option linter.unusedSectionVars false

/-! # The étale projection `proj : EtalePrimitives om → X` is a local homeomorphism

Third file of the étale-space arc (Alt B of `AUDIT_LOOP_PERIOD_VANISHES.md`).
Upgrades the projection
`proj : EtalePrimitives om → X` from continuous (Chip 1) to a local
homeomorphism, using Chip 2's overlap-local-constancy keystone for
continuity of the section side.

## Construction

For each base point `(y, c_off) : X × ℂ` we build an
`OpenPartialHomeomorph (EtalePrimitives om) X`:

* `source := basicSheet om y (convexBallChartAt y).source rfl c_off`
    — the graph of `x ↦ ⟨x, F_y(x) + c_off⟩` over the convex-ball chart
      source at `y`.
* `target := (convexBallChartAt y).source` — the open chart-ball-source
    in `X`.
* `toFun := proj om` (restricted) — globally continuous by Chip 1.
* `invFun := chartSectionTotal om y c_off` — extended to all of `X` by
    a `dite` on chart-source membership.

The continuity of `chartSectionTotal` on `(convexBallChartAt y).source`
is the substantive new content: for each generating basic sheet
`B = basicSheet om y' V' _ c'_off` of the étale topology, the preimage
under `chartSectionTotal` is exactly the level set
`{x ∈ V_y ∩ V' : F_y(x) − F_{y'}(x) = c'_off − c_off}`, which is open
by Chip 2's `chartLocalPrimitive_diff_locallyConstant_at_overlap`.

## What this file ships

* `chartSectionTotal om y c_off : X → EtalePrimitives om` — the total
  form of `chartSection`.
* `chartSection_primValue_eq_localPrimitiveAtBallCenter_add` — bridges
  the chartSection-`Max` value to the `ExtendMax` total wrapper used in
  the overlap-local-constancy lemma.
* `chartSectionTotal_preimage_basicSheet_isOpen` — Chip-2-powered
  openness of the preimage.
* `continuousOn_chartSectionTotal` — continuity on the chart-ball source.
* `etaleTrivialization om y c_off` — the
  `OpenPartialHomeomorph (EtalePrimitives om) X`.
* `isLocalHomeomorph_proj : IsLocalHomeomorph (proj om)` — main theorem.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set Filter TopologicalSpace Classical

namespace JacobianChallenge

namespace EtalePrimitives

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  {om : HolomorphicOneForm X}

/-! ## Bridge: `chartSection` value to `localPrimitiveAtBallCenter` -/

/-- **Bridge identity.** On the chart-ball source at `y`, the primValue of
`chartSection om y c_off x hx` equals `localPrimitiveAtBallCenter om y x + c_off`.
Uses `chartLocalPrimitiveExtendMax_eq_chartLocalPrimitiveMax` for the
`Max ↔ ExtendMax` identification on the source. -/
lemma chartSection_primValue_eq_localPrimitiveAtBallCenter_add
    (om : HolomorphicOneForm X) (y : X) (c_off : ℂ)
    (x : X) (hx : x ∈ (convexBallChartAt y).source) :
    (chartSection om y c_off x hx).primValue
      = localPrimitiveAtBallCenter om y x + c_off := by
  unfold localPrimitiveAtBallCenter
  rw [chartSection_primValue,
      chartLocalPrimitiveExtendMax_eq_chartLocalPrimitiveMax
        (convexBallChartAt y) (convexBallChartAt_mem_maximalAtlas_real y)
        (convexBallChartAt_target_convex y) y
        (convexBallChartAt_x_mem_source y) om x hx]

/-! ## Total form of `chartSection` -/

/-- **Total form of `chartSection`.** Returns
`chartSection om y c_off x hx` on the chart-ball source at `y`, and the
trivial placeholder `⟨x, 0⟩` outside. The placeholder's `point` is `x`
on the nose, so `proj ∘ chartSectionTotal = id` everywhere. -/
noncomputable def chartSectionTotal (om : HolomorphicOneForm X) (y : X) (c_off : ℂ)
    (x : X) : EtalePrimitives om :=
  if hx : x ∈ (convexBallChartAt y).source then
    chartSection om y c_off x hx
  else
    ⟨x, 0⟩

lemma chartSectionTotal_apply_of_mem
    (om : HolomorphicOneForm X) (y : X) (c_off : ℂ)
    (x : X) (hx : x ∈ (convexBallChartAt y).source) :
    chartSectionTotal om y c_off x = chartSection om y c_off x hx := by
  unfold chartSectionTotal; rw [dif_pos hx]

@[simp] lemma proj_chartSectionTotal
    (om : HolomorphicOneForm X) (y : X) (c_off : ℂ) (x : X) :
    proj om (chartSectionTotal om y c_off x) = x := by
  unfold chartSectionTotal
  split_ifs with hx
  · simp
  · rfl

/-- **Inverse identity on the basic sheet.** For `e` in the basic sheet at
`(y, V, c_off)` with `V = (convexBallChartAt y).source`, applying
`chartSectionTotal om y c_off` to `proj om e` recovers `e`. -/
lemma chartSectionTotal_proj_of_mem_basicSheet
    (om : HolomorphicOneForm X) (y : X) (c_off : ℂ)
    {e : EtalePrimitives om}
    (he : e ∈ basicSheet om y (convexBallChartAt y).source
            (subset_refl _) c_off) :
    chartSectionTotal om y c_off (proj om e) = e := by
  have hpt : e.point ∈ (convexBallChartAt y).source :=
    basicSheet_point_mem om y _ _ _ he
  have hval : e.primValue
      = chartLocalPrimitiveMax (convexBallChartAt y)
          (convexBallChartAt_mem_maximalAtlas_real y)
          (convexBallChartAt_target_convex y) y
          (convexBallChartAt_x_mem_source y) om e.point hpt + c_off :=
    basicSheet_primValue_eq om y _ _ _ he
  apply EtalePrimitives.ext
  · show (chartSectionTotal om y c_off (proj om e)).point = e.point
    rw [proj_apply]
    show (chartSectionTotal om y c_off e.point).point = e.point
    rw [chartSectionTotal_apply_of_mem _ _ _ _ hpt, chartSection_point]
  · show (chartSectionTotal om y c_off (proj om e)).primValue = e.primValue
    rw [proj_apply]
    rw [chartSectionTotal_apply_of_mem _ _ _ _ hpt, chartSection_primValue]
    exact hval.symm

/-! ## Membership characterisation of `chartSectionTotal` in a basic sheet -/

/-- **Membership characterisation.** For `x ∈ (convexBallChartAt y).source`,
`chartSectionTotal om y c_off x ∈ basicSheet om y' V' hV'_sub c'_off`
iff `x ∈ V'` and `F_y(x) − F_{y'}(x) = c'_off − c_off`
(in terms of `localPrimitiveAtBallCenter`).

This is the algebraic core of the continuity proof. -/
lemma chartSectionTotal_mem_basicSheet_iff
    (om : HolomorphicOneForm X) (y : X) (c_off : ℂ) (y' : X) (V' : Set X)
    (hV'_sub : V' ⊆ (convexBallChartAt y').source) (c'_off : ℂ)
    (x : X) (hx_y : x ∈ (convexBallChartAt y).source) :
    chartSectionTotal om y c_off x ∈ basicSheet om y' V' hV'_sub c'_off ↔
      x ∈ V' ∧
        localPrimitiveAtBallCenter om y x - localPrimitiveAtBallCenter om y' x
          = c'_off - c_off := by
  constructor
  · rintro ⟨x', hx'_V', hsec_eq⟩
    rw [chartSectionTotal_apply_of_mem _ _ _ _ hx_y] at hsec_eq
    -- Compare points: x = x' from `.point` projection.
    have h_point : x = x' := by
      have := congrArg EtalePrimitives.point hsec_eq
      simpa [chartSection_point] using this
    subst h_point
    refine ⟨hx'_V', ?_⟩
    -- Compare primValues: F_y(x) + c_off = F_{y'}(x) + c'_off.
    have h_val :
        localPrimitiveAtBallCenter om y x + c_off
          = localPrimitiveAtBallCenter om y' x + c'_off := by
      have h := congrArg EtalePrimitives.primValue hsec_eq
      rw [chartSection_primValue_eq_localPrimitiveAtBallCenter_add,
          chartSection_primValue_eq_localPrimitiveAtBallCenter_add] at h
      exact h
    linear_combination h_val
  · rintro ⟨hxV', h_diff⟩
    refine ⟨x, hxV', ?_⟩
    apply EtalePrimitives.ext
    · rw [chartSectionTotal_apply_of_mem _ _ _ _ hx_y, chartSection_point,
          chartSection_point]
    · rw [chartSectionTotal_apply_of_mem _ _ _ _ hx_y,
          chartSection_primValue_eq_localPrimitiveAtBallCenter_add,
          chartSection_primValue_eq_localPrimitiveAtBallCenter_add]
      linear_combination h_diff

/-! ## Openness of `chartSectionTotal`-preimage of a basic sheet -/

/-- **Preimage of a basic sheet is open in the chart-ball source at `y`.**
Uses Chip 2's `chartLocalPrimitive_diff_locallyConstant_at_overlap` for
local constancy of the chart-transition difference. -/
lemma chartSectionTotal_preimage_basicSheet_isOpen
    (om : HolomorphicOneForm X) (y : X) (c_off : ℂ)
    (y' : X) (V' : Set X) (hV'_open : IsOpen V')
    (hV'_sub : V' ⊆ (convexBallChartAt y').source) (c'_off : ℂ) :
    IsOpen ((convexBallChartAt y).source ∩
      chartSectionTotal om y c_off ⁻¹' (basicSheet om y' V' hV'_sub c'_off)) := by
  -- For every point in the preimage, find an open neighborhood inside the
  -- preimage. Use Chip 2 at each such point.
  rw [isOpen_iff_forall_mem_open]
  intro x hx_in
  obtain ⟨hx_y, hx_pre⟩ := hx_in
  -- Unfold the preimage membership.
  rw [Set.mem_preimage,
      chartSectionTotal_mem_basicSheet_iff om y c_off y' V' hV'_sub c'_off x hx_y]
    at hx_pre
  obtain ⟨hx_V', h_diff_x⟩ := hx_pre
  have hx_y' : x ∈ (convexBallChartAt y').source := hV'_sub hx_V'
  -- Chip 2: locally constant on the overlap.
  obtain ⟨U, hU_open, hxU, hU_sub_y, hU_sub_y', hU_const⟩ :=
    chartLocalPrimitive_diff_locallyConstant_at_overlap om y y' x hx_y hx_y'
  -- Refine `U` to `U ∩ V'` (also open, also in the overlap, also containing `x`).
  refine ⟨U ∩ V', ?_, hU_open.inter hV'_open, ⟨hxU, hx_V'⟩⟩
  -- Show U ∩ V' is in the preimage.
  intro x'' hx''
  obtain ⟨hx''_U, hx''_V'⟩ := hx''
  have hx''_y : x'' ∈ (convexBallChartAt y).source := hU_sub_y hx''_U
  refine ⟨hx''_y, ?_⟩
  rw [Set.mem_preimage,
      chartSectionTotal_mem_basicSheet_iff om y c_off y' V' hV'_sub c'_off x'' hx''_y]
  refine ⟨hx''_V', ?_⟩
  -- Apply local constancy: F_y(x'') − F_{y'}(x'') = F_y(x) − F_{y'}(x) = c'_off − c_off.
  have h_const := hU_const x'' hx''_U
  -- h_const :
  --   localPrimitiveAtBallCenter om y x'' - localPrimitiveAtBallCenter om y' x''
  --     = localPrimitiveAtBallCenter om y x - localPrimitiveAtBallCenter om y' x
  rw [h_const]
  exact h_diff_x

/-! ## Continuity of `chartSectionTotal` on the chart-ball source -/

/-- **`chartSectionTotal om y c_off` is continuous on
`(convexBallChartAt y).source`.** The étale topology is the
`generateFrom` of the basic sheets, so continuity reduces to openness of
preimages of basic sheets, given by
`chartSectionTotal_preimage_basicSheet_isOpen`. -/
lemma continuousOn_chartSectionTotal
    (om : HolomorphicOneForm X) (y : X) (c_off : ℂ) :
    ContinuousOn (chartSectionTotal om y c_off) (convexBallChartAt y).source := by
  intro x hx
  rw [ContinuousWithinAt]
  -- Reduce to `Tendsto` into a `generateFrom` neighborhood filter.
  -- The topology on `EtalePrimitives om` IS `generateFrom (basicSheets om)`
  -- by the instance definition, so `𝓝 …` unfolds.
  rw [show (𝓝 (chartSectionTotal om y c_off x) :
      Filter (EtalePrimitives om))
      = @nhds (EtalePrimitives om)
          (TopologicalSpace.generateFrom (basicSheets om))
          (chartSectionTotal om y c_off x) from rfl,
      tendsto_nhds_generateFrom_iff]
  intro B hB hxB
  -- B is a basic sheet.
  obtain ⟨y', V', hV'_open, hV'_sub, c'_off, hB_eq⟩ := hB
  subst hB_eq
  -- Preimage is open by the preceding lemma.
  have h_open :=
    chartSectionTotal_preimage_basicSheet_isOpen
      om y c_off y' V' hV'_open hV'_sub c'_off
  -- We need `chartSectionTotal om y c_off ⁻¹' (basicSheet …) ∈ 𝓝[source] x`.
  -- The preimage we proved open is `source ∩ preimage`. Since `source` is
  -- a neighborhood of `x` and our intersected set is open and contains `x`,
  -- it is a `𝓝[source]`-set.
  have h_open_src : IsOpen ((convexBallChartAt y).source :
      Set X) := (convexBallChartAt y).open_source
  have hx_in_pre :
      x ∈ (convexBallChartAt y).source ∩
        chartSectionTotal om y c_off ⁻¹' (basicSheet om y' V' hV'_sub c'_off) :=
    ⟨hx, hxB⟩
  -- Show inclusion into the desired neighborhood.
  rw [mem_nhdsWithin]
  refine ⟨(convexBallChartAt y).source ∩
            chartSectionTotal om y c_off ⁻¹' (basicSheet om y' V' hV'_sub c'_off),
          h_open, hx_in_pre, ?_⟩
  intro x' hx'
  exact hx'.1.2

/-! ## The trivialization OpenPartialHomeomorph at `(y, c_off)` -/

/-- **Trivialization `PartialEquiv`** at base `(y, c_off)`. Forward map is
`proj`; inverse is `chartSectionTotal om y c_off`. Source is the basic
sheet over the chart-ball source at `y`; target is the chart-ball source
itself. -/
def trivializationPartialEquiv
    (om : HolomorphicOneForm X) (y : X) (c_off : ℂ) :
    PartialEquiv (EtalePrimitives om) X where
  toFun := proj om
  invFun := chartSectionTotal om y c_off
  source := basicSheet om y (convexBallChartAt y).source (subset_refl _) c_off
  target := (convexBallChartAt y).source
  map_source' _ he := basicSheet_point_mem om y _ _ _ he
  map_target' x hx :=
    ⟨x, hx, chartSectionTotal_apply_of_mem om y c_off x hx⟩
  left_inv' _ he := chartSectionTotal_proj_of_mem_basicSheet om y c_off he
  right_inv' x _ := proj_chartSectionTotal om y c_off x

/-- **Trivialization `OpenPartialHomeomorph`** at base `(y, c_off)`. -/
noncomputable def etaleTrivialization
    (om : HolomorphicOneForm X) (y : X) (c_off : ℂ) :
    OpenPartialHomeomorph (EtalePrimitives om) X where
  toPartialEquiv := trivializationPartialEquiv om y c_off
  open_source := by
    show IsOpen (basicSheet om y (convexBallChartAt y).source (subset_refl _) c_off)
    exact basicSheet_isOpen om y _
      (convexBallChartAt y).open_source (subset_refl _) c_off
  open_target := by
    show IsOpen ((convexBallChartAt y).source : Set X)
    exact (convexBallChartAt y).open_source
  continuousOn_toFun := by
    show ContinuousOn (proj om)
      (basicSheet om y (convexBallChartAt y).source (subset_refl _) c_off)
    exact (continuous_proj om).continuousOn
  continuousOn_invFun := by
    show ContinuousOn (chartSectionTotal om y c_off) (convexBallChartAt y).source
    exact continuousOn_chartSectionTotal om y c_off

@[simp] lemma etaleTrivialization_apply
    (om : HolomorphicOneForm X) (y : X) (c_off : ℂ) :
    ⇑(etaleTrivialization om y c_off) = proj om := rfl

@[simp] lemma etaleTrivialization_source
    (om : HolomorphicOneForm X) (y : X) (c_off : ℂ) :
    (etaleTrivialization om y c_off).source
      = basicSheet om y (convexBallChartAt y).source (subset_refl _) c_off := rfl

/-! ## Main theorem: `proj` is a local homeomorphism -/

/-- **The étale projection `proj om : EtalePrimitives om → X` is a local
homeomorphism.** For each `e : EtalePrimitives om`, the trivialization
`etaleTrivialization om e.point e.primValue` is a local
`OpenPartialHomeomorph` containing `e` in its source, and `proj om` agrees
with it on that source (trivially, since the partial-equiv's `toFun` IS
`proj om`). -/
theorem isLocalHomeomorph_proj (om : HolomorphicOneForm X) :
    IsLocalHomeomorph (proj om) := by
  refine IsLocalHomeomorph.mk (f := proj om) ?_
  intro e
  refine ⟨etaleTrivialization om e.point e.primValue, ?_, ?_⟩
  · -- `e` is in the source: basic sheet at (e.point, source, e.primValue).
    show e ∈ basicSheet om e.point (convexBallChartAt e.point).source
      (subset_refl _) e.primValue
    -- Use `self_mem_basicSheet` at `y := e.point`, `c_off := e.primValue`.
    -- That gives `⟨e.point, e.primValue⟩ ∈ basicSheet …`; rewrite via `ext`.
    have h_self :
        (⟨e.point, e.primValue⟩ : EtalePrimitives om)
          ∈ basicSheet om e.point (convexBallChartAt e.point).source
              (subset_refl _) e.primValue := by
      apply self_mem_basicSheet om e.point _ (subset_refl _)
      exact convexBallChartAt_x_mem_source e.point
    -- `e = ⟨e.point, e.primValue⟩` by η.
    have h_eta : e = (⟨e.point, e.primValue⟩ : EtalePrimitives om) := by
      cases e; rfl
    rw [h_eta]; exact h_self
  · -- `proj om` agrees with the partial-equiv's toFun on the source — by `rfl`.
    intro x _
    rfl

end EtalePrimitives

end JacobianChallenge

end
