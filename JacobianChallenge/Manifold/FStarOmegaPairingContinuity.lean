/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SheetCotPullbackPairingContinuity
import JacobianChallenge.Manifold.FStarOmegaLocalAt
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalSheetSmoothOn
import JacobianChallenge.Manifold.RiemannSphereRealManifold
import JacobianChallenge.Manifold.CotangentPullbackAtApply

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `fStarOmega`-pairing continuity along `β` at a regular value

For a non-constant `f : MeromorphicNonzero X`, a smooth
`β : ℝ → RiemannSphere`, and a parameter `s₀` with
`β s₀ ∈ f.regularValueSet`, the pairing

  `s ↦ applyCotangent (fStarOmega f hnc om (β s)) (mfderiv β s 1)`

is `ContinuousAt s₀`.

The proof composes:

* `fStarOmega_eq_sum_sheetCotPullback_at_v0` (`f-3`) — fixed-Finset
  rewrite of `fStarOmega` on the labelling nbhd of `β s₀`.
* `applyCotangent_finset_sum` — pairing distributes over the sum.
* `continuousAt_sheetCotPullback_pairing` (per-sheet chip) — each
  summand is `ContinuousAt s₀`.
* Finset induction with `ContinuousAt.add` — sum of `ContinuousAt`
  is `ContinuousAt`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Helper: `ContinuousAt` of a `Finset` sum.** Standard Finset
induction with `ContinuousAt.add`. -/
private lemma continuousAt_finset_sum_of
    {α : Type*} (S : Finset α) {F : α → ℝ → ℝ} {s₀ : ℝ}
    (h : ∀ p ∈ S, ContinuousAt (F p) s₀) :
    ContinuousAt (fun s => ∑ p ∈ S, F p s) s₀ := by
  classical
  induction S using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact continuousAt_const
  | insert q T hqT ih =>
    have h_q : ContinuousAt (F q) s₀ := h q (Finset.mem_insert_self q T)
    have h_T : ∀ p ∈ T, ContinuousAt (F p) s₀ := fun p hp =>
      h p (Finset.mem_insert_of_mem hp)
    have h_T_sum : ContinuousAt (fun s => ∑ p ∈ T, F p s) s₀ := ih h_T
    have h_add : ContinuousAt
        (fun s => F q s + ∑ p ∈ T, F p s) s₀ :=
      h_q.add h_T_sum
    refine h_add.congr ?_
    refine Filter.Eventually.of_forall fun s => ?_
    simp only [Finset.sum_insert hqT]

/-- **`fStarOmega`-pairing continuity along `β` at a regular value of `β s₀`.**

Composes the `f-3` fixed-Finset rewrite of `fStarOmega` on the
labelling nbhd of `β s₀` with the per-sheet `ContinuousAt` chip. -/
theorem continuousAt_fStarOmega_pairing
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    {s₀ : ℝ} (hβs₀_reg : β s₀ ∈ f.regularValueSet) :
    ContinuousAt
      (fun s => SmoothPath.applyCotangent
        (f.fStarOmega hnc om (β s))
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s) (1 : ℝ))) s₀ := by
  classical
  -- Labelling nbhd `U` of `β s₀`, open, ⊆ regularValueSet.
  set U : Set RiemannSphere := f.localFiberLabelingNbhd hnc hβs₀_reg with hU_def
  have hU_open : IsOpen U := f.localFiberLabelingNbhd_isOpen hnc hβs₀_reg
  have hβs₀_in_U : β s₀ ∈ U := f.mem_localFiberLabelingNbhd_self hnc hβs₀_reg
  -- Preimage `W := β ⁻¹' U` open in ℝ, contains `s₀`.
  set W : Set ℝ := β ⁻¹' U with hW_def
  have hW_open : IsOpen W := hU_open.preimage hβ_smooth.continuous
  have hs₀_in_W : s₀ ∈ W := hβs₀_in_U
  -- Per-sheet `ContinuousAt s₀` for each `p ∈ fiberFinset hβs₀_reg.attach`.
  have h_per_sheet :
      ∀ p ∈ (f.fiberFinset hβs₀_reg).attach,
        ContinuousAt
          (fun s : ℝ => SmoothPath.applyCotangent
            (f.sheetCotPullback hnc
              (f.mem_regularSet_of_preimage_regularValue hβs₀_reg
                ((f.mem_fiberFinset_iff hβs₀_reg p.val).mp p.property))
              (β s) om)
            ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s) (1 : ℝ))) s₀ := by
    intro p _
    set hp_reg : p.val ∈ f.regularSet :=
      f.mem_regularSet_of_preimage_regularValue hβs₀_reg
        ((f.mem_fiberFinset_iff hβs₀_reg p.val).mp p.property) with hp_reg_def
    -- Get an open nbhd `u_p` of `f.toRiemannSphere p = β s₀` (after
    -- adjusting for the fact that for p ∈ fiberFinset hβs₀_reg, we have
    -- f.toRiemannSphere p.val = β s₀) on which sheet_p.g is `ContMDiffOn ω`.
    obtain ⟨u_p, hu_p_nhds, hu_p_smooth_ω⟩ :=
      f.exists_contMDiffOn_localSheet_g_near_basePoint hnc hp_reg
    -- Extract an open subset.
    rw [mem_nhds_iff] at hu_p_nhds
    obtain ⟨u_p_o, hu_p_o_sub, hu_p_o_open, hu_p_o_mem⟩ := hu_p_nhds
    -- f.toRiemannSphere p.val = β s₀ so β s₀ ∈ u_p_o ⊆ u_p.
    have hp_to_v₀ : f.toRiemannSphere p.val = β s₀ :=
      (f.mem_fiberFinset_iff hβs₀_reg p.val).mp p.property
    have hβs₀_in_u_p_o : β s₀ ∈ u_p_o := hp_to_v₀ ▸ hu_p_o_mem
    -- Restrict ω-smoothness from u_p to u_p_o, then realify.
    have hu_p_o_smooth_ω : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
        (f.localSheetData_at_regular hnc hp_reg).g u_p_o :=
      hu_p_smooth_ω.mono hu_p_o_sub
    have hu_p_o_smooth_real : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        (f.localSheetData_at_regular hnc hp_reg).g u_p_o :=
      JacobianChallenge.ContMDiffOn.complex_to_real_of_isOpen
        hu_p_o_open hu_p_o_smooth_ω
    -- Apply per-sheet chip.
    exact continuousAt_sheetCotPullback_pairing f hnc hp_reg hβ_smooth om
      hu_p_o_open hβs₀_in_u_p_o hu_p_o_smooth_real
  -- Sum of `ContinuousAt s₀` is `ContinuousAt s₀`.
  have h_sum_cont : ContinuousAt
      (fun s : ℝ => ∑ p ∈ (f.fiberFinset hβs₀_reg).attach,
        SmoothPath.applyCotangent
          (f.sheetCotPullback hnc
            (f.mem_regularSet_of_preimage_regularValue hβs₀_reg
              ((f.mem_fiberFinset_iff hβs₀_reg p.val).mp p.property))
            (β s) om)
          ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s) (1 : ℝ))) s₀ :=
    continuousAt_finset_sum_of (f.fiberFinset hβs₀_reg).attach h_per_sheet
  -- EqOn `W`: `fStarOmega` pairing = the Finset sum (via `f-3` + pairing-sum-distrib).
  have h_eq : W.EqOn
      (fun s => SmoothPath.applyCotangent
        (f.fStarOmega hnc om (β s))
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s) (1 : ℝ)))
      (fun s : ℝ => ∑ p ∈ (f.fiberFinset hβs₀_reg).attach,
        SmoothPath.applyCotangent
          (f.sheetCotPullback hnc
            (f.mem_regularSet_of_preimage_regularValue hβs₀_reg
              ((f.mem_fiberFinset_iff hβs₀_reg p.val).mp p.property))
            (β s) om)
          ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s) (1 : ℝ))) := by
    intro s hs
    -- hs : β s ∈ U = labelling nbhd
    show SmoothPath.applyCotangent (f.fStarOmega hnc om (β s))
          ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s) (1 : ℝ))
        = ∑ p ∈ (f.fiberFinset hβs₀_reg).attach,
            SmoothPath.applyCotangent
              (f.sheetCotPullback hnc
                (f.mem_regularSet_of_preimage_regularValue hβs₀_reg
                  ((f.mem_fiberFinset_iff hβs₀_reg p.val).mp p.property))
                (β s) om)
              ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s) (1 : ℝ))
    rw [f.fStarOmega_eq_sum_sheetCotPullback_at_v0 hnc om hβs₀_reg hs,
        applyCotangent_finset_sum]
  -- `EqOn` on open `W` → `EventuallyEq` → `ContinuousAt.congr`.
  refine h_sum_cont.congr ?_
  exact (h_eq.eventuallyEq_of_mem (hW_open.mem_nhds hs₀_in_W)).symm

end MeromorphicNonzero

end JacobianChallenge

end
