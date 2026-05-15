/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroFiberFinsetCard
import JacobianChallenge.Manifold.DisjointFibreNbhds

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `fiberFinset` is locally constant: per-sheet labelling on a nbhd of a regular value

For `f : MeromorphicNonzero X` non-constant and `v₀ ∈ f.regularValueSet`,
the fibre `f⁻¹({v₀})` is a finite set of points
`{p₁, …, p_d}` where `d = degreeFiber f.toRiemannSphere`. Each fibre
point `pᵢ` has a local biholomorphism sheet `sheetᵢ := f.localSheetData_at_regular hnc hpᵢ_reg`
with `sheetᵢ.V` an open nbhd of `v₀` in `RiemannSphere`,
`sheetᵢ.U` an open nbhd of `pᵢ` in `X`, and `sheetᵢ.g : RiemannSphere → X`
a local right-inverse: `f ∘ sheetᵢ.g = id` on `sheetᵢ.V`.

This file packages the **local labelling**: there is an open nbhd `W`
of `v₀` (lying inside `regularValueSet`) such that for every `v ∈ W`,
the map `pᵢ ↦ sheetᵢ.g v` is a Finset bijection
`f.fiberFinset hv₀ ≃ f.fiberFinset hv`. Concretely:

* `localFiberLabelingNbhd` — the open nbhd `W ∋ v₀`.
* Membership / image: `sheetᵢ.g v ∈ f.fiberFinset hv` for every `pᵢ`.
* `Set.InjOn` of `pᵢ ↦ sheetᵢ.g v` on `(f.fiberFinset hv₀).attach`,
  via pairwise-disjoint shrunken `Wᵢ ⊆ sheetᵢ.U` from
  `JacobianChallenge.Manifold.exists_disjoint_open_nbhds_in_of_finite`.
* Finset image equality `image = fiberFinset` from cardinality
  invariance (`fiberFinset_card_const`).

This is the **prerequisite for moving the trace's `Finset.sum` outside
the regularity-of-`v` smoothness witness** (chip `f-3`): on the
labelled nbhd, `traceAt f v om` becomes a sum over a fixed
(`v₀`-indexed) Finset of cotangent pullbacks of fixed sheets.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Per-fibre-point sheet at a regular value -/

/-- The local sheet at a fibre point of a regular value. Bundles
`localSheetData_at_regular` applied to the regularity of the fibre
point (extracted via `mem_regularSet_of_preimage_regularValue`). -/
noncomputable def fiberSheetAt
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet)
    (p : f.fiberFinset hv₀) :
    JacobianChallenge.LocalSheetData f.toRiemannSphere
      (f.toRiemannSphere p.val) p.val :=
  f.localSheetData_at_regular hnc
    (f.mem_regularSet_of_preimage_regularValue hv₀
      ((f.mem_fiberFinset_iff hv₀ p.val).mp p.property))

/-- `f.toRiemannSphere p = v₀` for `p ∈ f.fiberFinset hv₀`. -/
lemma toRiemannSphere_of_mem_fiberFinset
    (f : MeromorphicNonzero X)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet)
    (p : f.fiberFinset hv₀) :
    f.toRiemannSphere p.val = v₀ :=
  (f.mem_fiberFinset_iff hv₀ p.val).mp p.property

/-- `v₀ ∈ (fiberSheetAt f hnc hv₀ p).V`. -/
lemma mem_V_fiberSheetAt
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet)
    (p : f.fiberFinset hv₀) :
    v₀ ∈ (f.fiberSheetAt hnc hv₀ p).V :=
  Set.mem_of_eq_of_mem
    (f.toRiemannSphere_of_mem_fiberFinset hv₀ p).symm
    (f.fiberSheetAt hnc hv₀ p).mem_V

/-! ## Disjoint shrunk neighbourhoods -/

/-- The "V-input" passed to `JacobianChallenge.Manifold.exists_disjoint_open_nbhds_in_of_finite`: each
fibre point gets its own sheet's `.U`. Off the fibre the choice is `univ`
(irrelevant since the spec only constrains `x ∈ fiberFinset`). -/
private noncomputable def fibreSheetUSel
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet) :
    X → Set X := by
  classical
  exact fun x =>
    if hx : x ∈ f.fiberFinset hv₀ then
      (f.fiberSheetAt hnc hv₀ ⟨x, hx⟩).U
    else
      (Set.univ : Set X)

private lemma fibreSheetUSel_isOpen
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet)
    {x : X} (hx : x ∈ ((f.fiberFinset hv₀) : Set X)) :
    IsOpen (f.fibreSheetUSel hnc hv₀ x) := by
  have hx' : x ∈ f.fiberFinset hv₀ := Finset.mem_coe.mp hx
  unfold fibreSheetUSel
  simp only [dif_pos hx']
  exact (f.fiberSheetAt hnc hv₀ ⟨x, hx'⟩).U_open

private lemma mem_fibreSheetUSel_self
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet)
    {x : X} (hx : x ∈ ((f.fiberFinset hv₀) : Set X)) :
    x ∈ f.fibreSheetUSel hnc hv₀ x := by
  have hx' : x ∈ f.fiberFinset hv₀ := Finset.mem_coe.mp hx
  unfold fibreSheetUSel
  simp only [dif_pos hx']
  exact (f.fiberSheetAt hnc hv₀ ⟨x, hx'⟩).mem_U

/-- **Pairwise-disjoint open neighbourhoods of fibre points, each inside the
corresponding sheet's `.U`.** -/
noncomputable def disjointFibreNbhd
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet) :
    X → Set X :=
  Classical.choose
    (JacobianChallenge.Manifold.exists_disjoint_open_nbhds_in_of_finite (Finset.finite_toSet _)
      (V := f.fibreSheetUSel hnc hv₀)
      (fun _ hx => f.fibreSheetUSel_isOpen hnc hv₀ hx)
      (fun _ hx => f.mem_fibreSheetUSel_self hnc hv₀ hx))

private lemma disjointFibreNbhd_spec
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet) :
    (∀ x ∈ ((f.fiberFinset hv₀) : Set X),
        x ∈ f.disjointFibreNbhd hnc hv₀ x ∧
        IsOpen (f.disjointFibreNbhd hnc hv₀ x) ∧
        f.disjointFibreNbhd hnc hv₀ x ⊆ f.fibreSheetUSel hnc hv₀ x) ∧
    (((f.fiberFinset hv₀) : Set X)).PairwiseDisjoint
        (f.disjointFibreNbhd hnc hv₀) :=
  Classical.choose_spec
    (JacobianChallenge.Manifold.exists_disjoint_open_nbhds_in_of_finite (Finset.finite_toSet _)
      (V := f.fibreSheetUSel hnc hv₀)
      (fun _ hx => f.fibreSheetUSel_isOpen hnc hv₀ hx)
      (fun _ hx => f.mem_fibreSheetUSel_self hnc hv₀ hx))

lemma mem_disjointFibreNbhd_self
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet)
    (p : f.fiberFinset hv₀) :
    p.val ∈ f.disjointFibreNbhd hnc hv₀ p.val :=
  ((f.disjointFibreNbhd_spec hnc hv₀).1 p.val
    ((Finset.mem_coe).mpr p.property)).1

lemma disjointFibreNbhd_isOpen
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet)
    (p : f.fiberFinset hv₀) :
    IsOpen (f.disjointFibreNbhd hnc hv₀ p.val) :=
  ((f.disjointFibreNbhd_spec hnc hv₀).1 p.val
    ((Finset.mem_coe).mpr p.property)).2.1

lemma disjointFibreNbhd_subset_U
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet)
    (p : f.fiberFinset hv₀) :
    f.disjointFibreNbhd hnc hv₀ p.val ⊆ (f.fiberSheetAt hnc hv₀ p).U := by
  have h := ((f.disjointFibreNbhd_spec hnc hv₀).1 p.val
    ((Finset.mem_coe).mpr p.property)).2.2
  -- h : disjointFibreNbhd p.val ⊆ fibreSheetUSel p.val
  -- and fibreSheetUSel p.val = (fiberSheetAt p).U since p.val ∈ fiberFinset.
  intro x hx
  have h_mem := h hx
  unfold fibreSheetUSel at h_mem
  rw [dif_pos p.property] at h_mem
  exact h_mem

lemma disjointFibreNbhd_pairwiseDisjoint
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet) :
    (((f.fiberFinset hv₀) : Set X)).PairwiseDisjoint
        (f.disjointFibreNbhd hnc hv₀) :=
  (f.disjointFibreNbhd_spec hnc hv₀).2

/-! ## The local labelling neighbourhood -/

/-- **Local labelling neighbourhood of `v₀`.** The intersection of
`(fiberSheetAt p).V ∩ (fiberSheetAt p).g ⁻¹' (disjointFibreNbhd p.val)`
over all fibre points `p`, intersected with `regularValueSet`.

For `v` in this nbhd, `(fiberSheetAt p).g v` lies in
`disjointFibreNbhd p.val ⊆ (fiberSheetAt p).U`, and these target sets
are pairwise disjoint, giving injectivity of the labelling map. -/
noncomputable def localFiberLabelingNbhd
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet) :
    Set RiemannSphere :=
  (⋂ p : f.fiberFinset hv₀,
    (f.fiberSheetAt hnc hv₀ p).V ∩
      (f.fiberSheetAt hnc hv₀ p).g ⁻¹' (f.disjointFibreNbhd hnc hv₀ p.val))
    ∩ f.regularValueSet

lemma localFiberLabelingNbhd_isOpen
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet) :
    IsOpen (f.localFiberLabelingNbhd hnc hv₀) := by
  classical
  unfold localFiberLabelingNbhd
  refine IsOpen.inter ?_ (f.regularValueSet_isOpen hnc)
  -- A finite intersection of opens.
  refine isOpen_iInter_of_finite ?_
  intro p
  -- Each factor is `V ∩ g ⁻¹' (disjointFibreNbhd p.val)`, which is open
  -- by `ContinuousOn.isOpen_inter_preimage`.
  exact (f.fiberSheetAt hnc hv₀ p).g_continuousOn.isOpen_inter_preimage
    (f.fiberSheetAt hnc hv₀ p).V_open
    (f.disjointFibreNbhd_isOpen hnc hv₀ p)

lemma mem_localFiberLabelingNbhd_self
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet) :
    v₀ ∈ f.localFiberLabelingNbhd hnc hv₀ := by
  classical
  refine ⟨?_, hv₀⟩
  rw [Set.mem_iInter]
  intro p
  refine ⟨f.mem_V_fiberSheetAt hnc hv₀ p, ?_⟩
  -- preimage: g v₀ = p.val, and p.val ∈ disjointFibreNbhd p.val.
  rw [Set.mem_preimage]
  -- (fiberSheetAt p).g v₀ = p.val by sheet.leftInvOn applied at p.val:
  -- `f p.val = v₀` and `g (f p.val) = p.val` on U; we have p.val ∈ sheet.U.
  have h_g_v0 : (f.fiberSheetAt hnc hv₀ p).g v₀ = p.val := by
    have hp_in_U : p.val ∈ (f.fiberSheetAt hnc hv₀ p).U :=
      (f.fiberSheetAt hnc hv₀ p).mem_U
    have hf_p : f.toRiemannSphere p.val = v₀ :=
      f.toRiemannSphere_of_mem_fiberFinset hv₀ p
    have h_left := (f.fiberSheetAt hnc hv₀ p).leftInvOn hp_in_U
    -- h_left : (fiberSheetAt p).g (f.toRiemannSphere p.val) = p.val
    -- Use congrArg on `(fiberSheetAt p).g` applied to `hf_p` to bridge.
    have h_g : (f.fiberSheetAt hnc hv₀ p).g (f.toRiemannSphere p.val)
        = (f.fiberSheetAt hnc hv₀ p).g v₀ :=
      congrArg (f.fiberSheetAt hnc hv₀ p).g hf_p
    exact h_g.symm.trans h_left
  rw [h_g_v0]
  exact f.mem_disjointFibreNbhd_self hnc hv₀ p

lemma localFiberLabelingNbhd_subset_regularValueSet
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet) :
    f.localFiberLabelingNbhd hnc hv₀ ⊆ f.regularValueSet :=
  fun _ hv => hv.2

/-! ## Membership / image inclusion -/

/-- For `v` in the labelling nbhd, the sheet's `g v` lies in `disjointFibreNbhd p`. -/
lemma fiberSheetAt_g_mem_disjointFibreNbhd
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet)
    (p : f.fiberFinset hv₀)
    {v : RiemannSphere} (hv : v ∈ f.localFiberLabelingNbhd hnc hv₀) :
    (f.fiberSheetAt hnc hv₀ p).g v ∈ f.disjointFibreNbhd hnc hv₀ p.val := by
  classical
  have h_iInter := hv.1
  rw [Set.mem_iInter] at h_iInter
  exact (h_iInter p).2

/-- For `v` in the labelling nbhd, `v ∈ (fiberSheetAt p).V`. -/
lemma mem_V_of_mem_localFiberLabelingNbhd
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet)
    (p : f.fiberFinset hv₀)
    {v : RiemannSphere} (hv : v ∈ f.localFiberLabelingNbhd hnc hv₀) :
    v ∈ (f.fiberSheetAt hnc hv₀ p).V := by
  classical
  have h_iInter := hv.1
  rw [Set.mem_iInter] at h_iInter
  exact (h_iInter p).1

/-- For `v` in the labelling nbhd, `(fiberSheetAt p).g v ∈ fiberFinset f hv'`
where `hv' : v ∈ regularValueSet`. The fact `f (g v) = v` comes from
`sheet.rightInvOn` applied at `v ∈ sheet.V`. -/
lemma fiberSheetAt_g_mem_fiberFinset
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet)
    (p : f.fiberFinset hv₀)
    {v : RiemannSphere} (hv : v ∈ f.localFiberLabelingNbhd hnc hv₀)
    (hv' : v ∈ f.regularValueSet) :
    (f.fiberSheetAt hnc hv₀ p).g v ∈ f.fiberFinset hv' := by
  rw [f.mem_fiberFinset_iff hv']
  exact (f.fiberSheetAt hnc hv₀ p).rightInvOn
    (f.mem_V_of_mem_localFiberLabelingNbhd hnc hv₀ p hv)

/-! ## Injectivity via disjoint shrunk nbhds -/

/-- **`Set.InjOn` of the labelling map** `p ↦ (fiberSheetAt p).g v` for
`v ∈ localFiberLabelingNbhd`. Distinct fibre points produce values in
pairwise-disjoint `disjointFibreNbhd`s, so cannot collide. -/
theorem fiberSheetAt_g_injOn
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet)
    {v : RiemannSphere} (hv : v ∈ f.localFiberLabelingNbhd hnc hv₀) :
    Set.InjOn (fun p : f.fiberFinset hv₀ => (f.fiberSheetAt hnc hv₀ p).g v)
      ((f.fiberFinset hv₀).attach : Set _) := by
  classical
  intro p₁ _ p₂ _ h_eq
  -- Beta-reduce the lambda in h_eq.
  simp only at h_eq
  by_contra hne
  -- p₁ ≠ p₂ as Subtype, so their values differ.
  have h_val_ne : p₁.val ≠ p₂.val := fun heq => hne (Subtype.ext heq)
  -- Both are in fiberFinset (as Set X).
  have hp₁ : p₁.val ∈ ((f.fiberFinset hv₀) : Set X) :=
    (Finset.mem_coe).mpr p₁.property
  have hp₂ : p₂.val ∈ ((f.fiberFinset hv₀) : Set X) :=
    (Finset.mem_coe).mpr p₂.property
  -- Disjoint: disjointFibreNbhd p₁.val and disjointFibreNbhd p₂.val.
  have h_disj := f.disjointFibreNbhd_pairwiseDisjoint hnc hv₀ hp₁ hp₂ h_val_ne
  -- Both values belong to their respective disjoint nbhds.
  have h₁ : (f.fiberSheetAt hnc hv₀ p₁).g v ∈ f.disjointFibreNbhd hnc hv₀ p₁.val :=
    f.fiberSheetAt_g_mem_disjointFibreNbhd hnc hv₀ p₁ hv
  have h₂ : (f.fiberSheetAt hnc hv₀ p₂).g v ∈ f.disjointFibreNbhd hnc hv₀ p₂.val :=
    f.fiberSheetAt_g_mem_disjointFibreNbhd hnc hv₀ p₂ hv
  -- Combine via h_eq: the same point lies in both disjoint sets.
  rw [h_eq] at h₁
  -- h₁ : (fiberSheetAt p₂).g v ∈ disjointFibreNbhd p₁.val
  -- h₂ : (fiberSheetAt p₂).g v ∈ disjointFibreNbhd p₂.val
  have h_inter :
      (f.fiberSheetAt hnc hv₀ p₂).g v
        ∈ f.disjointFibreNbhd hnc hv₀ p₁.val
            ∩ f.disjointFibreNbhd hnc hv₀ p₂.val := ⟨h₁, h₂⟩
  rw [Set.disjoint_iff_inter_eq_empty.mp h_disj] at h_inter
  exact h_inter.elim

/-! ## Finset image equals fiberFinset, via cardinality -/

/-- **Image of `(fiberFinset hv₀).attach` under `p ↦ (fiberSheetAt p).g v`
equals `fiberFinset f hv'`** for `v ∈ localFiberLabelingNbhd`.

By `InjOn` (above), `image ⊆ fiberFinset hv'` (each summand lies there
by `fiberSheetAt_g_mem_fiberFinset`), and the cardinalities match
(`fiberFinset_card_const`). The Finset equality follows from
`Finset.eq_of_subset_of_card_le`. -/
theorem fiberSheetAt_g_image_eq_fiberFinset
    [DecidableEq X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet)
    {v : RiemannSphere} (hv : v ∈ f.localFiberLabelingNbhd hnc hv₀)
    (hv' : v ∈ f.regularValueSet) :
    (f.fiberFinset hv₀).attach.image
        (fun p => (f.fiberSheetAt hnc hv₀ p).g v)
      = f.fiberFinset hv' := by
  classical
  -- Image ⊆ fiberFinset.
  have h_subset : (f.fiberFinset hv₀).attach.image
        (fun p => (f.fiberSheetAt hnc hv₀ p).g v)
      ⊆ f.fiberFinset hv' := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨p, _, rfl⟩ := hx
    exact f.fiberSheetAt_g_mem_fiberFinset hnc hv₀ p hv hv'
  -- Card equality.
  have h_card_image :
      ((f.fiberFinset hv₀).attach.image
          (fun p => (f.fiberSheetAt hnc hv₀ p).g v)).card
        = (f.fiberFinset hv₀).attach.card := by
    apply Finset.card_image_of_injOn
    exact f.fiberSheetAt_g_injOn hnc hv₀ hv
  have h_card_attach :
      (f.fiberFinset hv₀).attach.card = (f.fiberFinset hv₀).card :=
    Finset.card_attach
  have h_card_const : (f.fiberFinset hv₀).card = (f.fiberFinset hv').card :=
    f.fiberFinset_card_const hnc hv₀ hv'
  -- card image = card fiberFinset hv'
  have h_card_eq :
      ((f.fiberFinset hv₀).attach.image
          (fun p => (f.fiberSheetAt hnc hv₀ p).g v)).card
        = (f.fiberFinset hv').card := by
    rw [h_card_image, h_card_attach, h_card_const]
  exact Finset.eq_of_subset_of_card_le h_subset (h_card_eq.symm.le)

end MeromorphicNonzero

end JacobianChallenge

end
