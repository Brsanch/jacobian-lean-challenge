/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroPathLiftUniqueOn

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Partial-domain path-lift uniqueness with `ContinuousOn` hypotheses

Sister to `MeromorphicNonzeroPathLiftUniqueOn.lean`'s
`path_lift_eqOn_Icc`, generalised to take `ContinuousOn γᵢ (Icc a b)`
in place of global `Continuous γᵢ`. This is the variant needed to
identify `(sourceFiberPath p).toPath` with `sheet_p.g ∘ β ∘ σ` on a
sub-interval where `sheet_p.g` is only locally defined (continuous
on a neighborhood of `β(σ ·)`'s image but not globally).

The proof mirrors `path_lift_eqOn_Icc` exactly. The only adjustment is
the source of `Continuous (s.restrict γᵢ) = Continuous (fun p : Icc a b
=> γᵢ p.val)`: instead of `hγᵢ_cont.comp continuous_subtype_val` from a
global `Continuous γᵢ`, we use `hγᵢ_contOn.restrict` from
`ContinuousOn γᵢ (Icc a b)`.

The `preimage_mem_nhds` step similarly stays inside the subspace via
`(s.restrict γ).continuousAt.preimage_mem_nhds`.

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

/-- **Partial-domain uniqueness of path lift, `ContinuousOn` variant.**

Two lifts of `β` on `Icc a b` that are merely `ContinuousOn (Icc a b)`
(not globally continuous on ℝ) and agree at some `t₀ ∈ Icc a b` must
agree on all of `Icc a b`.

The proof is identical to `path_lift_eqOn_Icc`'s clopen argument in the
subspace topology, with `ContinuousOn.restrict` replacing
`Continuous.comp continuous_subtype_val`. -/
theorem path_lift_eqOn_Icc_of_continuousOn
    (f : MeromorphicNonzero X)
    {β : ℝ → RiemannSphere}
    {a b : ℝ}
    (hβ_reg : ∀ t ∈ Icc a b, β t ∈ f.regularValueSet)
    {γ₁ γ₂ : ℝ → X}
    (hγ₁_contOn : ContinuousOn γ₁ (Icc a b))
    (hγ₂_contOn : ContinuousOn γ₂ (Icc a b))
    (hγ₁_lift : ∀ t ∈ Icc a b, f.toRiemannSphere (γ₁ t) = β t)
    (hγ₂_lift : ∀ t ∈ Icc a b, f.toRiemannSphere (γ₂ t) = β t)
    {t₀ : ℝ} (ht₀_mem : t₀ ∈ Icc a b)
    (h_start : γ₁ t₀ = γ₂ t₀) :
    Set.EqOn γ₁ γ₂ (Icc a b) := by
  classical
  -- Subspace-level restrictions are continuous.
  have hcont₁_sub : Continuous (fun p : Icc a b => γ₁ p.val) :=
    continuousOn_iff_continuous_restrict.mp hγ₁_contOn
  have hcont₂_sub : Continuous (fun p : Icc a b => γ₂ p.val) :=
    continuousOn_iff_continuous_restrict.mp hγ₂_contOn
  -- S := {p ∈ Icc a b | γ₁ p.val = γ₂ p.val} (subspace).
  set S : Set (Icc a b) :=
    {p : Icc a b | γ₁ p.val = γ₂ p.val} with hS_def
  -- S is closed in `Icc a b`.
  have hS_closed : IsClosed S := isClosed_eq hcont₁_sub hcont₂_sub
  -- S is open in `Icc a b`.
  have hS_open : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    set x_star : X := γ₁ p.val with hx_star_def
    have hγ₁p : γ₁ p.val = x_star := rfl
    have hγ₂p : γ₂ p.val = x_star := hp.symm
    have hβp_reg : β p.val ∈ f.regularValueSet := hβ_reg p.val p.property
    have h_fx_star : f.toRiemannSphere x_star = β p.val :=
      hγ₁_lift p.val p.property
    have hx_star_reg : x_star ∈ f.regularSet :=
      f.mem_regularSet_of_preimage_regularValue hβp_reg h_fx_star
    obtain ⟨U, hU_nhds, hU_inj⟩ := hx_star_reg
    -- Preimages under the subspace restrictions are nbhds in the subspace.
    have hpre₁_sub_nhds :
        (fun q : Icc a b => γ₁ q.val) ⁻¹' U ∈ 𝓝 p := by
      have h_cont_at : ContinuousAt (fun q : Icc a b => γ₁ q.val) p :=
        hcont₁_sub.continuousAt
      have h_U_at_p : U ∈ 𝓝 (γ₁ p.val) := by rw [hγ₁p]; exact hU_nhds
      exact h_cont_at.preimage_mem_nhds h_U_at_p
    have hpre₂_sub_nhds :
        (fun q : Icc a b => γ₂ q.val) ⁻¹' U ∈ 𝓝 p := by
      have h_cont_at : ContinuousAt (fun q : Icc a b => γ₂ q.val) p :=
        hcont₂_sub.continuousAt
      have h_U_at_p : U ∈ 𝓝 (γ₂ p.val) := by rw [hγ₂p]; exact hU_nhds
      exact h_cont_at.preimage_mem_nhds h_U_at_p
    have h_inter_sub_nhds :
        ((fun q : Icc a b => γ₁ q.val) ⁻¹' U)
          ∩ ((fun q : Icc a b => γ₂ q.val) ⁻¹' U) ∈ 𝓝 p :=
      Filter.inter_mem hpre₁_sub_nhds hpre₂_sub_nhds
    refine Filter.mem_of_superset h_inter_sub_nhds ?_
    intro q hq
    obtain ⟨hq₁, hq₂⟩ := hq
    have h_eq_fs : f.toRiemannSphere (γ₁ q.val)
        = f.toRiemannSphere (γ₂ q.val) := by
      rw [hγ₁_lift q.val q.property, hγ₂_lift q.val q.property]
    show γ₁ q.val = γ₂ q.val
    exact hU_inj hq₁ hq₂ h_eq_fs
  -- Clopen + nonempty ⇒ S = univ via PreconnectedSpace.
  have hS_clopen : IsClopen S := ⟨hS_closed, hS_open⟩
  have hS_nonempty : S.Nonempty := ⟨⟨t₀, ht₀_mem⟩, h_start⟩
  haveI : PreconnectedSpace (Icc a b) :=
    Subtype.preconnectedSpace (isPreconnected_Icc)
  have hS_univ : S = Set.univ := hS_clopen.eq_univ hS_nonempty
  intro t ht
  have : (⟨t, ht⟩ : Icc a b) ∈ S := by rw [hS_univ]; exact mem_univ _
  exact this

end MeromorphicNonzero

end JacobianChallenge

end
