/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroRegularValueSet
import JacobianChallenge.Manifold.MeromorphicNonzeroFiberFinite
import JacobianChallenge.Manifold.CriticalSetClosed

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Uniqueness of path lift along regular values

For `f : MeromorphicNonzero X`, a continuous path `β : ℝ →
RiemannSphere` whose image lies in `f.regularValueSet`, and two
continuous lifts `γ₁, γ₂ : ℝ → X` of `β` (`f.toRiemannSphere ∘ γᵢ =
β`) that agree at *some* point `t₀`, the lifts agree at *every* point.

## Argument

Let `T := {t | γ₁ t = γ₂ t}`.

* `T` is closed: the equalizer of two continuous functions into a `T2`
  space.
* `T` is open: at any `t ∈ T`, set `x* := γ₁ t = γ₂ t`. Since `β t =
  f.toRiemannSphere x*` is in `regularValueSet`, `x*` is a regular
  point (preimage of regular value is regular).  Let `U` be a local
  injectivity neighbourhood of `x*` (`x* ∈ regularSet` definition).
  By continuity of `γ₁`, `γ₂` at `t`, both `γ₁⁻¹ U` and `γ₂⁻¹ U` are
  neighbourhoods of `t` in `ℝ`.  On their intersection, `γ₁ s, γ₂ s ∈
  U` and `f.toRiemannSphere (γ₁ s) = β s = f.toRiemannSphere (γ₂ s)`,
  so `γ₁ s = γ₂ s` by local injectivity.
* `T` is non-empty (contains `t₀`).
* `ℝ` is preconnected and `T` is clopen, so `T = ℝ`.

## What ships

* `MeromorphicNonzero.path_lift_unique` — `γ₁ = γ₂` (as functions
  `ℝ → X`).

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Uniqueness of path lift along regular values.** -/
theorem path_lift_unique
    (f : MeromorphicNonzero X)
    {β : ℝ → RiemannSphere}
    (hβ_reg : ∀ t : ℝ, β t ∈ f.regularValueSet)
    {γ₁ γ₂ : ℝ → X}
    (hγ₁_cont : Continuous γ₁)
    (hγ₂_cont : Continuous γ₂)
    (hγ₁_lift : ∀ t, f.toRiemannSphere (γ₁ t) = β t)
    (hγ₂_lift : ∀ t, f.toRiemannSphere (γ₂ t) = β t)
    {t₀ : ℝ}
    (h_start : γ₁ t₀ = γ₂ t₀) :
    γ₁ = γ₂ := by
  classical
  set T : Set ℝ := {t | γ₁ t = γ₂ t} with hT_def
  -- T is closed: equalizer of two continuous functions into T2 X.
  have hT_closed : IsClosed T := isClosed_eq hγ₁_cont hγ₂_cont
  -- T is non-empty (contains t₀).
  have hT_t₀ : t₀ ∈ T := h_start
  -- T is open.
  have hT_open : IsOpen T := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    -- ht : γ₁ t = γ₂ t. Let x* := γ₁ t.
    set x_star : X := γ₁ t with hx_star_def
    have hγ₁t : γ₁ t = x_star := rfl
    have hγ₂t : γ₂ t = x_star := ht.symm
    -- x* is regular (preimage of β t ∈ regularValueSet).
    have h_fx_star : f.toRiemannSphere x_star = β t := hγ₁_lift t
    have hx_star_reg : x_star ∈ f.regularSet :=
      f.mem_regularSet_of_preimage_regularValue (hβ_reg t) h_fx_star
    -- Local injectivity neighbourhood at x*.
    obtain ⟨U, hU_nhds, hU_inj⟩ := hx_star_reg
    -- Preimages of U under γ₁ and γ₂ are nhds of t.
    have hpre₁_nhds : γ₁ ⁻¹' U ∈ 𝓝 t :=
      hγ₁_cont.continuousAt.preimage_mem_nhds (by rw [hγ₁t]; exact hU_nhds)
    have hpre₂_nhds : γ₂ ⁻¹' U ∈ 𝓝 t :=
      hγ₂_cont.continuousAt.preimage_mem_nhds (by rw [hγ₂t]; exact hU_nhds)
    have h_inter_nhds : γ₁ ⁻¹' U ∩ γ₂ ⁻¹' U ∈ 𝓝 t :=
      Filter.inter_mem hpre₁_nhds hpre₂_nhds
    refine Filter.mem_of_superset h_inter_nhds ?_
    intro s ⟨hs₁, hs₂⟩
    -- γ₁ s ∈ U, γ₂ s ∈ U, f.toRS (γ₁ s) = f.toRS (γ₂ s).
    have h_eq_fs : f.toRiemannSphere (γ₁ s) = f.toRiemannSphere (γ₂ s) := by
      rw [hγ₁_lift s, hγ₂_lift s]
    show γ₁ s = γ₂ s
    exact hU_inj hs₁ hs₂ h_eq_fs
  -- T is clopen in connected ℝ, contains t₀, hence T = ℝ.
  have hT_univ : T = Set.univ := by
    have hT_clopen : IsClopen T := ⟨hT_closed, hT_open⟩
    exact hT_clopen.eq_univ ⟨t₀, hT_t₀⟩
  -- Extract γ₁ = γ₂.
  funext t
  have : t ∈ T := by rw [hT_univ]; exact mem_univ t
  exact this

end MeromorphicNonzero

end JacobianChallenge

end
