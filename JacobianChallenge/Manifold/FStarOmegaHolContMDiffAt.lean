/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SheetCotangentPullbackContMDiffAt
import JacobianChallenge.Manifold.FStarOmegaHolLocalAt
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # `fStarOmegaHol` is `ContMDiffAt ω` at every regular value

Holomorphic-side analogue of
`MeromorphicNonzero.fStarOmega_contMDiffAt`
(`Manifold/FStarOmegaContMDiffAt.lean`). For a non-constant
`f : MeromorphicNonzero X`, a holomorphic 1-form
`α : HolomorphicOneForm X`, and a regular value
`v₀ ∈ f.regularValueSet`, the total-space lift of
`f.fStarOmegaHol hnc α` is
`ContMDiffAt 𝓘(ℂ, ℂ) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω` at `v₀`.

Proof structure (mirrors the realified case):

* `fStarOmegaHol_eq_sum_holSheetCotPullback_at_v0` — fixed-Finset
  rewrite on the labelling neighbourhood of `v₀`.
* `sheetPullbackSection_contMDiffAt` — per-sheet `ContMDiffAt ω` at the
  regular value (sub-chip A, holomorphic per-sheet smoothness shipped
  in `Manifold/SheetCotangentPullbackContMDiffAt.lean`).
* `ContMDiffAt.sum_section` (mathlib `SmoothSection.lean`) — sum
  smoothness for cotangent-bundle sections.
* `ContMDiffAt.congr_of_eventuallyEq` — transfer from the explicit
  Finset sum to `fStarOmegaHol` via the labelling-nbhd equality.

`holSheetCotPullback hnc hp_reg v α` is definitionally equal to
`localSheetPullbackPointwise sheet_p.g α v`, so
`sheetPullbackSection_contMDiffAt` applies directly.

No `sorry`, no `axiom`. -/

open Set Filter Bundle
open scoped Manifold ContDiff Topology Bundle

noncomputable section

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Wrapper: per-sheet `holSheetCotPullback` is `ContMDiffAt ω`.**

Mirrors `MeromorphicNonzero.sheetCotPullback_contMDiffAt` (realified)
but for the holomorphic bundle. `holSheetCotPullback hnc hp_reg v α`
unfolds to `holCotangentPullbackAt sheet.g v α`, which is
definitionally equal to `localSheetPullbackPointwise sheet.g α v`; so
`sheetPullbackSection_contMDiffAt` (sub-chip A) applies directly. -/
theorem holSheetCotPullback_contMDiffAt
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {p : X} (hp_reg : p ∈ f.regularSet)
    (α : HolomorphicOneForm X) :
    ContMDiffAt (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun v : RiemannSphere => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) v
        (f.holSheetCotPullback hnc hp_reg v α))
      (f.toRiemannSphere p) := by
  unfold holSheetCotPullback holCotangentPullbackAt
  exact pullbackSection_contMDiffAt_of_localSheet
    (g := (f.localSheetData_at_regular hnc hp_reg).g)
    (f.contMDiffAt_localSheet_g_at_basePoint hnc hp_reg) α

/-- **`fStarOmegaHol α` is `ContMDiffAt ω` at a regular value.**

For every regular value `v₀ ∈ f.regularValueSet`, the section
`v ↦ TotalSpace.mk' (ℂ →L[ℂ] ℂ) v (f.fStarOmegaHol hnc α v)` is
`ContMDiffAt 𝓘(ℂ, ℂ) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω` at `v₀`. -/
theorem fStarOmegaHol_contMDiffAt
    [DecidableEq X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (α : HolomorphicOneForm X)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet) :
    ContMDiffAt (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun v : RiemannSphere => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) v
        (f.fStarOmegaHol hnc α v))
      v₀ := by
  classical
  -- Per-summand: each `v ↦ holSheetCotPullback p v α` is `ContMDiffAt ω` at `v₀`.
  have h_per_sheet :
      ∀ p ∈ (f.fiberFinset hv₀).attach,
        ContMDiffAt (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
          (fun v : RiemannSphere => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) v
            (f.holSheetCotPullback hnc
              (f.mem_regularSet_of_preimage_regularValue hv₀
                ((f.mem_fiberFinset_iff hv₀ p.val).mp p.property))
              v α)) v₀ := by
    intro p _
    have hp_reg : p.val ∈ f.regularSet :=
      f.mem_regularSet_of_preimage_regularValue hv₀
        ((f.mem_fiberFinset_iff hv₀ p.val).mp p.property)
    have hp_to_v₀ : f.toRiemannSphere p.val = v₀ :=
      (f.mem_fiberFinset_iff hv₀ p.val).mp p.property
    have h := f.holSheetCotPullback_contMDiffAt hnc hp_reg α
    rw [hp_to_v₀] at h
    exact h
  -- Sum smoothness via mathlib's `ContMDiffAt.sum_section`.
  have h_sum :
      ContMDiffAt (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
        (fun v : RiemannSphere => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) v
          (∑ p ∈ (f.fiberFinset hv₀).attach,
            f.holSheetCotPullback hnc
              (f.mem_regularSet_of_preimage_regularValue hv₀
                ((f.mem_fiberFinset_iff hv₀ p.val).mp p.property))
              v α)) v₀ :=
    ContMDiffAt.sum_section h_per_sheet
  -- Bridge to `fStarOmegaHol` via the labelling-nbhd equality.
  refine h_sum.congr_of_eventuallyEq ?_
  have h_labelling_nbhd :
      f.localFiberLabelingNbhd hnc hv₀ ∈ nhds v₀ :=
    (f.localFiberLabelingNbhd_isOpen hnc hv₀).mem_nhds
      (f.mem_localFiberLabelingNbhd_self hnc hv₀)
  filter_upwards [h_labelling_nbhd] with v hv
  show Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) v (f.fStarOmegaHol hnc α v)
    = Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) v _
  congr 1
  exact f.fStarOmegaHol_eq_sum_holSheetCotPullback_at_v0 hnc α hv₀ hv

end MeromorphicNonzero

end JacobianChallenge

end
