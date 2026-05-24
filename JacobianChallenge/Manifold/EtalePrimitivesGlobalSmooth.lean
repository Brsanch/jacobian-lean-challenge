/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.EtalePrimitivesGlobalSection

set_option linter.unusedSectionVars false

/-! # Smoothness of the global primitive on simply-connected `X` (Chip 4d)

Upgrades `globalPrimitive om x₀ : X → ℂ` (Chip 4c) from continuous to
`ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω`, on arbitrary compact connected
simply-connected complex 1-manifold X with
`IsManifold (𝓘(ℂ, ℂ)) ω X`.

## Strategy

For each `x : X`, set `c_x := (globalSection om x₀ x).primValue` and
`B_x := basicSheet om x (convexBallChartAt x).source rfl c_x`. The
preimage `u_x := globalSection om x₀ ⁻¹' B_x` is an open neighborhood
of `x` (continuous preimage of an open set; `x ∈ u_x` since
`globalSection om x₀ x = ⟨x, c_x⟩` lies in `B_x` by `self_mem_basicSheet`).

On `u_x`, every `x'` satisfies `globalSection om x₀ x' ∈ B_x`, so by
`basicSheet_primValue_eq` + the
`chartLocalPrimitiveExtendMax_eq_chartLocalPrimitiveMax` bridge,

```
globalPrimitive om x₀ x' = localPrimitiveAtBallCenter om x x' + c_x.
```

The RHS is `ContMDiffOn ω` on `(convexBallChartAt x).source ⊇ u_x` via
the cascade's `localPrimitiveAtBallCenter_contMDiffOn` (Chip 2) plus a
constant. Apply `ContMDiffOn.congr` to transport this to
`ContMDiffOn ω globalPrimitive u_x`. Conclude global
`ContMDiff` via `contMDiff_of_locally_contMDiffOn`.

## What this file ships

* `globalSection_preimage_basicSheet_isOpen` — `u_x` is open.
* `globalSection_self_mem_basicSheet_preimage` — `x ∈ u_x`.
* `globalSection_preimage_basicSheet_subset_chartBall` —
  `u_x ⊆ (convexBallChartAt x).source`.
* `globalPrimitive_eqOn_localPrimitiveAtBallCenter_add_const` — the key
  agreement on `u_x`.
* `contMDiffOn_globalPrimitive_on_chartBall_preimage` — `ContMDiffOn ω
  globalPrimitive u_x`.
* `contMDiff_globalPrimitive : ContMDiff … ω (globalPrimitive om x₀)` —
  main theorem.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set Filter

namespace JacobianChallenge

namespace EtalePrimitives

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [SimplyConnectedSpace X]
  {om : HolomorphicOneForm X}

/-! ## The chart-ball preimage `u_x` -/

/-- **`u_x` is open.** Continuous preimage of an open basic sheet. -/
lemma globalSection_preimage_basicSheet_isOpen
    (om : HolomorphicOneForm X) (x₀ x : X) :
    IsOpen ((globalSection om x₀) ⁻¹'
      basicSheet om x (convexBallChartAt x).source (subset_refl _)
        ((globalSection om x₀) x).primValue) :=
  (basicSheet_isOpen om x _ (convexBallChartAt x).open_source
    (subset_refl _) _).preimage (globalSection om x₀).continuous

/-- **`x ∈ u_x`.** The section at `x` is `⟨x, c_x⟩`, which lies in the
basic sheet at `(x, source, c_x)` by `self_mem_basicSheet`. -/
lemma globalSection_self_mem_basicSheet_preimage
    (om : HolomorphicOneForm X) (x₀ x : X) :
    x ∈ (globalSection om x₀) ⁻¹'
      basicSheet om x (convexBallChartAt x).source (subset_refl _)
        ((globalSection om x₀) x).primValue := by
  show (globalSection om x₀) x ∈
    basicSheet om x (convexBallChartAt x).source (subset_refl _)
      ((globalSection om x₀) x).primValue
  -- Rewrite `globalSection om x₀ x` as `⟨x, ((globalSection om x₀) x).primValue⟩`
  -- using `globalSection_point` for the `.point = x` equation.
  have h_eta : (globalSection om x₀) x =
      (⟨x, ((globalSection om x₀) x).primValue⟩ : EtalePrimitives om) :=
    EtalePrimitives.ext (globalSection_point om x₀ x) rfl
  rw [h_eta]
  exact self_mem_basicSheet om x _ (subset_refl _)
    (convexBallChartAt_x_mem_source x) _

/-- **`u_x ⊆ source(x)`.** Every `x' ∈ u_x` has `x' ∈ (convexBallChartAt x).source`
since `globalSection om x₀ x'` lies in the basic sheet (which projects
into source) and `proj om ∘ globalSection = id`. -/
lemma globalSection_preimage_basicSheet_subset_chartBall
    (om : HolomorphicOneForm X) (x₀ x : X) :
    (globalSection om x₀) ⁻¹'
      basicSheet om x (convexBallChartAt x).source (subset_refl _)
        ((globalSection om x₀) x).primValue
      ⊆ (convexBallChartAt x).source := by
  intro x' hx'
  -- hx' : globalSection om x₀ x' ∈ basicSheet om x (source x) _ c_x
  have h_section_in_source :
      ((globalSection om x₀) x').point ∈ (convexBallChartAt x).source :=
    basicSheet_point_mem om x _ _ _ hx'
  rwa [globalSection_point om x₀ x'] at h_section_in_source

/-! ## Agreement of `globalPrimitive` with `localPrimitiveAtBallCenter` on `u_x` -/

/-- **Key agreement.** On `u_x`, the global primitive equals the
chart-local primitive at `x` plus the constant `c_x =
(globalSection om x₀ x).primValue`. -/
lemma globalPrimitive_eqOn_localPrimitiveAtBallCenter_add_const
    (om : HolomorphicOneForm X) (x₀ x : X) :
    EqOn (globalPrimitive om x₀)
         (fun x' => localPrimitiveAtBallCenter om x x'
                    + ((globalSection om x₀) x).primValue)
         ((globalSection om x₀) ⁻¹'
           basicSheet om x (convexBallChartAt x).source (subset_refl _)
             ((globalSection om x₀) x).primValue) := by
  intro x' hx'
  -- Unfold basicSheet membership.
  obtain ⟨p, hp_V, h_sec_eq⟩ := hx'
  -- p ∈ source(x), and globalSection om x₀ x' = chartSection om x c_x p _
  -- Compare points: p = x' via `globalSection_point` + `chartSection_point`.
  have h_p_eq_x' : p = x' := by
    have h_point := congrArg EtalePrimitives.point h_sec_eq
    -- h_point : (globalSection om x₀ x').point = (chartSection om x c_x p _).point = p
    rw [globalSection_point, chartSection_point] at h_point
    exact h_point.symm
  -- Compare primValues, with `p = x'` substituted.
  have h_primValue := congrArg EtalePrimitives.primValue h_sec_eq
  -- h_primValue : (globalSection om x₀ x').primValue
  --             = (chartSection om x c_x p (subset_refl _ hp_V)).primValue
  rw [chartSection_primValue_eq_localPrimitiveAtBallCenter_add] at h_primValue
  -- h_primValue : (globalSection om x₀ x').primValue
  --             = localPrimitiveAtBallCenter om x p + c_x
  show ((globalSection om x₀) x').primValue
       = localPrimitiveAtBallCenter om x x'
         + ((globalSection om x₀) x).primValue
  rw [h_primValue, h_p_eq_x']

/-! ## ContMDiffOn `globalPrimitive` on the chart-ball preimage -/

/-- **`ContMDiffOn ω globalPrimitive u_x`.** Combines the agreement above
with the cascade's `localPrimitiveAtBallCenter_contMDiffOn` and the
constant-function smoothness. -/
lemma contMDiffOn_globalPrimitive_on_chartBall_preimage
    (om : HolomorphicOneForm X) (x₀ x : X) :
    ContMDiffOn (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (globalPrimitive om x₀)
      ((globalSection om x₀) ⁻¹'
        basicSheet om x (convexBallChartAt x).source (subset_refl _)
          ((globalSection om x₀) x).primValue) := by
  -- The function `localPrimitiveAtBallCenter om x + (const c_x)` is
  -- `ContMDiffOn ω` on `source(x) ⊇ u_x`.
  have h_local : ContMDiffOn (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (fun x' => localPrimitiveAtBallCenter om x x'
                 + ((globalSection om x₀) x).primValue)
      (convexBallChartAt x).source :=
    (localPrimitiveAtBallCenter_contMDiffOn om x).add contMDiffOn_const
  -- Restrict to u_x.
  have h_local_on_ux := h_local.mono
    (globalSection_preimage_basicSheet_subset_chartBall om x₀ x)
  -- Transport via congruence.
  exact h_local_on_ux.congr
    (globalPrimitive_eqOn_localPrimitiveAtBallCenter_add_const om x₀ x)

/-! ## Main theorem: global smoothness -/

/-- **The global primitive is `ContMDiff ω` on arbitrary
simply-connected `X`.** Glues the chart-ball local smoothness via
`contMDiff_of_locally_contMDiffOn`. -/
theorem contMDiff_globalPrimitive (om : HolomorphicOneForm X) (x₀ : X) :
    ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (globalPrimitive om x₀) := by
  apply contMDiff_of_locally_contMDiffOn
  intro x
  refine ⟨(globalSection om x₀) ⁻¹'
            basicSheet om x (convexBallChartAt x).source (subset_refl _)
              ((globalSection om x₀) x).primValue,
          globalSection_preimage_basicSheet_isOpen om x₀ x,
          globalSection_self_mem_basicSheet_preimage om x₀ x,
          contMDiffOn_globalPrimitive_on_chartBall_preimage om x₀ x⟩

end EtalePrimitives

end JacobianChallenge

end
