/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SourceFiberPathAmbientImageAt
import JacobianChallenge.Manifold.MeromorphicNonzeroFiberFinsetCard

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Surjectivity of `sourceFiberPath.toPath.extend t` onto the fiber at `β(σ t)`

The `t = 1` case is `sourceFiberPath_tgt_surjOn` (heavy time-reversal
argument). For the chain-rule pathway we need surjectivity at **every**
`t ∈ Icc 0 1`. Re-running the time-reversal argument is wasteful: a
finite-set cardinality argument suffices.

## Argument

Let `S := f.sourceFiber hβ0_reg = f.fiberFinset hβ0_reg`,
`T := f.fiberFinset hβσt_reg`, and let
`Φ p := (sourceFiberPath p).toPath.extend t`.

* `card S = card T` by `fiberFinset_card_const`
  (`MeromorphicNonzeroFiberFinsetCard.lean`): both `S` and `T` are
  fibres at regular values, hence have the same cardinality
  (= `degreeFiber f.toRiemannSphere`).
* The image of `S.attach` under `Φ` lies in `T`
  (`sourceFiberPath_toPath_extend_image_subset_fiberFinset_at`).
* `Φ` is `Set.InjOn` over `S.attach`
  (`sourceFiberPath_toPath_extend_injOn_attach_at`).
* `card (S.attach.image Φ) = card S.attach = card S` by injectivity.
* From `image ⊆ T` and `card image = card T`, conclude `image = T`
  (`Finset.eq_of_subset_of_card_le`).
* Hence every `y ∈ T` is in the image: surjectivity.

## What ships

* `MeromorphicNonzero.sourceFiberPath_toPath_extend_image_eq_fiberFinset_at`
  — Finset equality `image = fiberFinset` at any `t ∈ Icc 0 1`.
* `MeromorphicNonzero.sourceFiberPath_toPath_extend_surjOn_at` —
  surjectivity statement: for every `y ∈ fiberFinset (β(σ t))`, there
  exists `x ∈ sourceFiber` with `(sourceFiberPath x).toPath.extend t = y`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff unitInterval

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Image of `sourceFiber.attach` under `(sourceFiberPath ·).toPath.extend t`
equals `fiberFinset (β(σ t))`** for any `t ∈ Icc 0 1`.

The proof composes:
* image ⊆ fiberFinset (`sourceFiberPath_toPath_extend_image_subset_fiberFinset_at`),
* `Set.InjOn` of the map (`sourceFiberPath_toPath_extend_injOn_attach_at`),
* card equality `sourceFiber.card = fiberFinset.card` via
  `fiberFinset_card_const`,
giving `card image = card fiberFinset` and hence (subset + equal card)
equality. -/
theorem sourceFiberPath_toPath_extend_image_eq_fiberFinset_at
    [DecidableEq X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hβσt_reg : β (Real.smoothTransition t) ∈ f.regularValueSet) :
    let hβ0_reg : β 0 ∈ f.regularValueSet :=
      hβ_reg 0 ⟨le_refl _, by norm_num⟩
    (f.sourceFiber hβ0_reg).attach.image
        (fun p => (f.sourceFiberPath hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).toPath.extend t)
      = f.fiberFinset hβσt_reg := by
  classical
  intro hβ0_reg
  -- Abbreviations.
  set S : Finset X := f.sourceFiber hβ0_reg with hS_def
  set T : Finset X := f.fiberFinset hβσt_reg with hT_def
  set Φ : { x // x ∈ S } → X := fun p =>
    (f.sourceFiberPath hnc hβ_smooth hβ_reg
      ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).toPath.extend t
    with hΦ_def
  -- Image inclusion: image ⊆ T.
  have h_subset : S.attach.image Φ ⊆ T :=
    f.sourceFiberPath_toPath_extend_image_subset_fiberFinset_at hnc hβ_smooth hβ_reg
      ht hβσt_reg
  -- Injectivity on attach.
  have h_inj : Set.InjOn Φ (S.attach : Set _) :=
    f.sourceFiberPath_toPath_extend_injOn_attach_at hnc hβ_smooth hβ_reg ht
  -- Card of image = card of S (via injectivity).
  have h_card_image : (S.attach.image Φ).card = S.card := by
    rw [Finset.card_image_of_injOn h_inj]
    exact S.card_attach
  -- S = sourceFiber hβ0_reg = fiberFinset hβ0_reg definitionally.
  have hS_eq : S = f.fiberFinset hβ0_reg := rfl
  -- Card of S = card of T via fiberFinset_card_const.
  have h_card_S_T : S.card = T.card := by
    rw [hS_eq]
    exact f.fiberFinset_card_const hnc hβ0_reg hβσt_reg
  -- Hence card of image = card of T.
  have h_card_image_T : (S.attach.image Φ).card = T.card := by
    rw [h_card_image, h_card_S_T]
  -- Subset + equal card ⇒ equality.
  exact Finset.eq_of_subset_of_card_le h_subset h_card_image_T.ge

/-- **Surjectivity of `(sourceFiberPath ·).toPath.extend t` at any `t ∈ Icc 0 1`.**

Every `y ∈ f.fiberFinset (β(σ t))` is of the form
`(sourceFiberPath x).toPath.extend t` for some `x ∈ sourceFiber`. -/
theorem sourceFiberPath_toPath_extend_surjOn_at
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hβσt_reg : β (Real.smoothTransition t) ∈ f.regularValueSet)
    {y : X} (hy : y ∈ f.fiberFinset hβσt_reg) :
    let _hβ0_reg : β 0 ∈ f.regularValueSet :=
      hβ_reg 0 ⟨le_refl _, by norm_num⟩
    ∃ (x : X) (hx : f.toRiemannSphere x = β 0),
      (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath.extend t = y := by
  classical
  intro _hβ0_reg
  set hβ0_reg : β 0 ∈ f.regularValueSet :=
    hβ_reg 0 ⟨le_refl _, by norm_num⟩
  -- y ∈ image of S.attach under Φ.
  have h_image_eq :=
    f.sourceFiberPath_toPath_extend_image_eq_fiberFinset_at hnc hβ_smooth hβ_reg
      ht hβσt_reg
  -- hβ0_reg here matches the let-binding in h_image_eq's statement.
  have hy_in_image : y ∈ (f.sourceFiber hβ0_reg).attach.image
      (fun p => (f.sourceFiberPath hnc hβ_smooth hβ_reg
        ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).toPath.extend t) := by
    rw [h_image_eq]; exact hy
  rw [Finset.mem_image] at hy_in_image
  obtain ⟨p, _, h_eq⟩ := hy_in_image
  refine ⟨p.val, (f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property, ?_⟩
  exact h_eq

/-- **Bijection-flavour packaging.** The map
`p ↦ (sourceFiberPath p).toPath.extend t` is a bijection
`sourceFiber.attach → fiberFinset (β(σ t))` (as `Set.BijOn`-style: the
target equality is the headline image-eq lemma; injectivity is the
existing `sourceFiberPath_toPath_extend_injOn_attach_at`). -/
theorem sourceFiberPath_toPath_extend_bijOn_at
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hβσt_reg : β (Real.smoothTransition t) ∈ f.regularValueSet) :
    let hβ0_reg : β 0 ∈ f.regularValueSet :=
      hβ_reg 0 ⟨le_refl _, by norm_num⟩
    Set.BijOn
      (fun p : (f.sourceFiber hβ0_reg) =>
        (f.sourceFiberPath hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).toPath.extend t)
      ((f.sourceFiber hβ0_reg).attach : Set _)
      (f.fiberFinset hβσt_reg : Set _) := by
  classical
  intro hβ0_reg
  refine ⟨?_, ?_, ?_⟩
  · -- MapsTo: image of attach ⊆ fiberFinset.
    intro p _
    exact f.sourceFiberPath_toPath_extend_mem_fiberFinset_at hnc hβ_smooth hβ_reg
      ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property) ht hβσt_reg
  · -- InjOn.
    exact f.sourceFiberPath_toPath_extend_injOn_attach_at hnc hβ_smooth hβ_reg ht
  · -- SurjOn.
    intro y hy
    have h_image_eq :=
      f.sourceFiberPath_toPath_extend_image_eq_fiberFinset_at hnc hβ_smooth hβ_reg
        ht hβσt_reg
    have hy_finset : y ∈ f.fiberFinset hβσt_reg := hy
    have hy_in_image : y ∈ (f.sourceFiber hβ0_reg).attach.image
        (fun p => (f.sourceFiberPath hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).toPath.extend t) := by
      rw [h_image_eq]; exact hy_finset
    rw [Finset.mem_image] at hy_in_image
    obtain ⟨p, hp, h_eq⟩ := hy_in_image
    exact ⟨p, hp, h_eq⟩

end MeromorphicNonzero

end JacobianChallenge

end
