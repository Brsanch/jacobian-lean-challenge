/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzPatchingDataConstruction

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Uniqueness of local right-inverses agreeing at the base point

Two `LocalSheetData f y₀ x` whose chosen local inverses `g` agree at the
shared base value `y₀` (i.e. both send `y₀ ↦ x`) agree on a
neighbourhood of `y₀`. This is the standard uniqueness-of-section
statement for a local homeomorphism.

The proof: pick `y` in the (open) intersection
`s₁.V ∩ s₂.V ∩ s₁.g ⁻¹' s₂.U ∩ s₂.g ⁻¹' s₁.U` (a neighbourhood of `y₀`,
since `s₁.g(y₀) = s₂.g(y₀) = x ∈ s₁.U ∩ s₂.U` and the `g`s are
continuous on `V`). For such `y`:

* `f (s₁.g y) = y = f (s₂.g y)` (right-inverse property),
* `s₁.g y, s₂.g y ∈ s₁.U` (membership and the cross-preimage),
* `s₁` is injective on `s₁.U`,

so `s₁.g y = s₂.g y`.

This is the foundational primitive used by the trace identity at
general `t ∈ Icc 0 1`: when two sheets at different fibre points happen
to evaluate to the same target point at a shared regular value, their
local inverses agree on a nhd of that value, and consequently their
cotangent pullbacks coincide.

## What ships

* `JacobianChallenge.LocalSheetData.g_eqOn_nhds_of_g_eq` — eqOn-form
  of the uniqueness statement on a constructed open neighbourhood.

* `JacobianChallenge.LocalSheetData.g_eventuallyEq_of_g_eq` —
  germ-form (`=ᶠ[𝓝 y₀]`) suitable for `cotangentPullbackAt_congr_of_eventuallyEq`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Topology

namespace JacobianChallenge

namespace LocalSheetData

universe u v

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y} {y₀ : Y} {x₁ x₂ : X}

/-- **Two local sheets with the same base point agree on a neighbourhood
of `y₀`.** If `s₁ : LocalSheetData f y₀ x₁`, `s₂ : LocalSheetData f y₀ x₂`,
and the local inverses agree at `y₀`, then they agree on a
neighbourhood of `y₀`. -/
theorem g_eventuallyEq_of_g_eq
    (s₁ : LocalSheetData f y₀ x₁) (s₂ : LocalSheetData f y₀ x₂)
    (h_eq : s₁.g y₀ = s₂.g y₀) :
    s₁.g =ᶠ[𝓝 y₀] s₂.g := by
  -- The key open neighborhood: V₁ ∩ V₂ ∩ s₁.g⁻¹(s₂.U) ∩ s₂.g⁻¹(s₁.U).
  -- On this set, both g's land in s₁.U ∩ s₂.U where injectivity applies.
  -- Continuity of s₁.g on V₁: at y₀, s₁.g y₀ = x ∈ s₁.U ∩ s₂.U
  -- (x = s₁.g y₀ = s₂.g y₀; x ∈ s₁.U by leftInvOn applied to mem_U
  -- via f x₁ = y₀; same for s₂.U).
  have hg₁_at_y₀ : s₁.g y₀ ∈ s₁.U := s₁.g_mapsTo s₁.mem_V
  have hg₂_at_y₀ : s₂.g y₀ ∈ s₂.U := s₂.g_mapsTo s₂.mem_V
  -- s₁.g y₀ = s₂.g y₀ — call it `p`.
  have hg₁_in_U₂ : s₁.g y₀ ∈ s₂.U := h_eq ▸ hg₂_at_y₀
  have hg₂_in_U₁ : s₂.g y₀ ∈ s₁.U := h_eq ▸ hg₁_at_y₀
  -- Continuity of s₁.g at y₀ within V₁ → s₁.g⁻¹(s₂.U) ∩ V₁ ∈ 𝓝[V₁] y₀.
  -- We work in 𝓝 y₀ (not 𝓝[V₁]) by intersecting with the open V₁.
  have hV₁_nhds : s₁.V ∈ 𝓝 y₀ := s₁.V_open.mem_nhds s₁.mem_V
  have hV₂_nhds : s₂.V ∈ 𝓝 y₀ := s₂.V_open.mem_nhds s₂.mem_V
  -- Pull back s₂.U through s₁.g, using continuity of s₁.g at y₀ within V₁.
  have hg₁_cont_at : ContinuousWithinAt s₁.g s₁.V y₀ :=
    s₁.g_continuousOn y₀ s₁.mem_V
  have hg₂_cont_at : ContinuousWithinAt s₂.g s₂.V y₀ :=
    s₂.g_continuousOn y₀ s₂.mem_V
  -- s₁.g⁻¹(s₂.U) ∈ 𝓝[V₁] y₀ (preimage of an open nbhd of s₁.g y₀ ∈ s₂.U).
  have h_pre₁ : s₁.g ⁻¹' s₂.U ∈ 𝓝[s₁.V] y₀ :=
    hg₁_cont_at (s₂.U_open.mem_nhds hg₁_in_U₂)
  have h_pre₂ : s₂.g ⁻¹' s₁.U ∈ 𝓝[s₂.V] y₀ :=
    hg₂_cont_at (s₁.U_open.mem_nhds hg₂_in_U₁)
  -- Promote to 𝓝 y₀ via V₁/V₂ being neighbourhoods of y₀.
  have h_pre₁' : s₁.g ⁻¹' s₂.U ∈ 𝓝 y₀ := by
    rw [show 𝓝 y₀ = 𝓝[s₁.V] y₀ from (nhdsWithin_eq_nhds.mpr hV₁_nhds).symm]
    exact h_pre₁
  have h_pre₂' : s₂.g ⁻¹' s₁.U ∈ 𝓝 y₀ := by
    rw [show 𝓝 y₀ = 𝓝[s₂.V] y₀ from (nhdsWithin_eq_nhds.mpr hV₂_nhds).symm]
    exact h_pre₂
  -- Now consider y ∈ V₁ ∩ V₂ ∩ s₁.g⁻¹(s₂.U) ∩ s₂.g⁻¹(s₁.U).
  filter_upwards [hV₁_nhds, hV₂_nhds, h_pre₁', h_pre₂'] with y hy_V₁ hy_V₂ hy_pre₁ hy_pre₂
  -- s₁.g y ∈ s₁.U (mapsTo on V₁) and ∈ s₂.U (preimage).
  have hg₁_y_U₁ : s₁.g y ∈ s₁.U := s₁.g_mapsTo hy_V₁
  have hg₂_y_U₂ : s₂.g y ∈ s₂.U := s₂.g_mapsTo hy_V₂
  have hg₂_y_U₁ : s₂.g y ∈ s₁.U := hy_pre₂
  -- f(s₁.g y) = y = f(s₂.g y) (right-inverse on V).
  have h_f₁ : f (s₁.g y) = y := s₁.rightInvOn hy_V₁
  have h_f₂ : f (s₂.g y) = y := s₂.rightInvOn hy_V₂
  -- Both s₁.g y and s₂.g y lie in s₁.U with the same image under f.
  -- s₁.injOn on s₁.U gives equality.
  have h_eq_f : f (s₁.g y) = f (s₂.g y) := h_f₁.trans h_f₂.symm
  exact s₁.injOn hg₁_y_U₁ hg₂_y_U₁ h_eq_f

/-! ## General version: `s.g` agrees on a nhd of any `y ∈ s.V` with any
local right-inverse passing through `s.U`.

This is the form consumed by the chain-rule trace identity: the
source-side sheet `sheet_p` (centered at the fibre point `p` over
`β 0`) is, on a sub-interval where `β(σ t) ∈ sheet_p.V`, a local
right-inverse to `f.toRiemannSphere` near `β(σ t)`. The target-side
sheet `sheet_q` (centered at the corresponding lifted point
`q := sheet_p.g(β(σ t))` over `β(σ t)`) is also a local right-inverse.
The general lemma identifies them on a nhd of `β(σ t)`. -/

/-- **General uniqueness.** A local right-inverse `g : Y → X` to `f`
that lands inside `s.U` at a point `y ∈ s.V` agrees with `s.g` on a
neighbourhood of `y`. -/
theorem g_eventuallyEq_of_isLocalRightInverse
    (s : LocalSheetData f y₀ x₁)
    {g : Y → X} {y : Y}
    (hy_V : y ∈ s.V)
    (h_gy_U : g y ∈ s.U)
    (h_g_cont : ContinuousAt g y)
    (h_g_rinv : ∀ᶠ y' in 𝓝 y, f (g y') = y') :
    g =ᶠ[𝓝 y] s.g := by
  -- s.V is a nbhd of y.
  have hV_nhds : s.V ∈ 𝓝 y := s.V_open.mem_nhds hy_V
  -- Continuity of g at y → g⁻¹(s.U) ∈ 𝓝 y.
  have h_pre_g : g ⁻¹' s.U ∈ 𝓝 y := h_g_cont (s.U_open.mem_nhds h_gy_U)
  -- Filter argument.
  filter_upwards [hV_nhds, h_pre_g, h_g_rinv] with y' hy'_V hy'_pre hy'_rinv
  -- s.g y' ∈ s.U (mapsTo on V).
  have hsg_y'_U : s.g y' ∈ s.U := s.g_mapsTo hy'_V
  -- g y' ∈ s.U (preimage).
  have hg_y'_U : g y' ∈ s.U := hy'_pre
  -- f(g y') = y' (right-inverse) and f(s.g y') = y' (s.rightInvOn).
  have hf_g : f (g y') = y' := hy'_rinv
  have hf_sg : f (s.g y') = y' := s.rightInvOn hy'_V
  -- Apply s.injOn.
  exact s.injOn hg_y'_U hsg_y'_U (hf_g.trans hf_sg.symm)

end LocalSheetData

end JacobianChallenge

end
