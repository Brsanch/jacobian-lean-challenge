/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroPathLiftUnique
import Mathlib.Topology.Connected.Basic

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Partial-domain uniqueness of path lift

Strengthens chip 16 (`path_lift_unique`) to the case where the lifts
agree only on a closed interval `Icc a b`, not on all of ℝ.

The clopen argument works the same way, but restricted to the
connected subspace `Icc a b`.

## What ships

* `MeromorphicNonzero.path_lift_eqOn_Icc` — `Set.EqOn γ₁ γ₂ (Icc a b)`.

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

/-- **Partial-domain uniqueness of path lift.**

Two continuous lifts of `β` on `Icc a b`, with `β` taking regular values
on `Icc a b` and agreeing at some `t₀ ∈ Icc a b`, agree on all of
`Icc a b`. -/
theorem path_lift_eqOn_Icc
    (f : MeromorphicNonzero X)
    {β : ℝ → RiemannSphere}
    {a b : ℝ}
    (hβ_reg : ∀ t ∈ Icc a b, β t ∈ f.regularValueSet)
    {γ₁ γ₂ : ℝ → X}
    (hγ₁_cont : Continuous γ₁)
    (hγ₂_cont : Continuous γ₂)
    (hγ₁_lift : ∀ t ∈ Icc a b, f.toRiemannSphere (γ₁ t) = β t)
    (hγ₂_lift : ∀ t ∈ Icc a b, f.toRiemannSphere (γ₂ t) = β t)
    {t₀ : ℝ} (ht₀_mem : t₀ ∈ Icc a b)
    (h_start : γ₁ t₀ = γ₂ t₀) :
    Set.EqOn γ₁ γ₂ (Icc a b) := by
  classical
  -- Work on the subspace Icc a b.  T := {t ∈ Icc a b | γ₁ t = γ₂ t}
  -- is clopen in `Icc a b` and non-empty (contains ⟨t₀, ht₀_mem⟩),
  -- so T = univ on `Icc a b`.
  set S : Set (Icc a b) :=
    {p : Icc a b | γ₁ p.val = γ₂ p.val} with hS_def
  -- S is closed in `Icc a b` (subspace topology).
  have hS_closed : IsClosed S := by
    have hcont₁ : Continuous (fun p : Icc a b => γ₁ p.val) :=
      hγ₁_cont.comp continuous_subtype_val
    have hcont₂ : Continuous (fun p : Icc a b => γ₂ p.val) :=
      hγ₂_cont.comp continuous_subtype_val
    exact isClosed_eq hcont₁ hcont₂
  -- S is open in `Icc a b`.
  have hS_open : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    set x_star : X := γ₁ p.val with hx_star_def
    have hγ₁p : γ₁ p.val = x_star := rfl
    have hγ₂p : γ₂ p.val = x_star := hp.symm
    -- β p.val ∈ regularValueSet ⇒ x_star ∈ regularSet (preimage).
    have hβp_reg : β p.val ∈ f.regularValueSet := hβ_reg p.val p.property
    have h_fx_star : f.toRiemannSphere x_star = β p.val := hγ₁_lift p.val p.property
    have hx_star_reg : x_star ∈ f.regularSet :=
      f.mem_regularSet_of_preimage_regularValue hβp_reg h_fx_star
    -- Local injectivity nbhd at x_star (in X).
    obtain ⟨U, hU_nhds, hU_inj⟩ := hx_star_reg
    -- Preimages under γ₁, γ₂ are nbhds in ℝ.
    have hpre₁_nhds : γ₁ ⁻¹' U ∈ 𝓝 p.val :=
      hγ₁_cont.continuousAt.preimage_mem_nhds (by rw [hγ₁p]; exact hU_nhds)
    have hpre₂_nhds : γ₂ ⁻¹' U ∈ 𝓝 p.val :=
      hγ₂_cont.continuousAt.preimage_mem_nhds (by rw [hγ₂p]; exact hU_nhds)
    -- Intersection is a nbhd of p in (Icc a b, subspace topology).
    have h_inter_nhds : γ₁ ⁻¹' U ∩ γ₂ ⁻¹' U ∈ 𝓝 p.val :=
      Filter.inter_mem hpre₁_nhds hpre₂_nhds
    -- Pull back to subspace.
    have h_sub_nhds : (Subtype.val : Icc a b → ℝ) ⁻¹' (γ₁ ⁻¹' U ∩ γ₂ ⁻¹' U)
        ∈ 𝓝 p :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds h_inter_nhds
    refine Filter.mem_of_superset h_sub_nhds ?_
    intro q hq
    have hq_val_mem : q.val ∈ γ₁ ⁻¹' U ∩ γ₂ ⁻¹' U := hq
    obtain ⟨hq₁, hq₂⟩ := hq_val_mem
    -- f.toRS (γ₁ q.val) = β q.val = f.toRS (γ₂ q.val).
    have h_eq_fs : f.toRiemannSphere (γ₁ q.val)
        = f.toRiemannSphere (γ₂ q.val) := by
      rw [hγ₁_lift q.val q.property, hγ₂_lift q.val q.property]
    show γ₁ q.val = γ₂ q.val
    exact hU_inj hq₁ hq₂ h_eq_fs
  -- T = univ in Icc a b via IsClopen.eq_univ.
  have hS_clopen : IsClopen S := ⟨hS_closed, hS_open⟩
  have hS_nonempty : S.Nonempty := ⟨⟨t₀, ht₀_mem⟩, h_start⟩
  -- Icc a b is preconnected: needs `PreconnectedSpace (Icc a b)`.
  haveI : PreconnectedSpace (Icc a b) :=
    Subtype.preconnectedSpace (isPreconnected_Icc)
  have hS_univ : S = Set.univ := hS_clopen.eq_univ hS_nonempty
  -- Extract EqOn.
  intro t ht
  have : (⟨t, ht⟩ : Icc a b) ∈ S := by rw [hS_univ]; exact mem_univ _
  exact this

end MeromorphicNonzero

end JacobianChallenge

end
