/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SheetCotPullbackContMDiffAtReal
import JacobianChallenge.Manifold.FStarOmegaLocalAt
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # `fStarOmega` is `ContMDiffAt ∞` at every regular value

For a non-constant `f : MeromorphicNonzero X`, a smooth real 1-form
`om : SmoothOneForm 𝓘(ℝ, ℂ) X`, and a regular value
`v₀ ∈ f.regularValueSet`, the total-space lift of `fStarOmega f hnc om`
is `ContMDiffAt 𝓘(ℝ, ℂ) ((𝓘(ℝ, ℂ)).prod 𝓘(ℝ, ℂ →L[ℝ] ℝ)) ∞` at `v₀`.

The proof composes:

* `FStarOmegaLocalAt.fStarOmega_eq_sum_sheetCotPullback_at_v0` —
  fixed-Finset rewrite on the labelling neighbourhood of `v₀`.
* `sheetCotPullback_contMDiffAt` (sub-chip B', realified per-sheet
  smoothness) — each summand is `ContMDiffAt` at the regular value.
* `ContMDiffAt.sum_section` (mathlib `SmoothSection.lean`) — sum
  smoothness for cotangent-bundle sections.
* `ContMDiffAt.congr_of_eventuallyEq` — transfer from the explicit
  Finset sum to `fStarOmega` via the labelling-nbhd equality.

This is the pointwise core of `f_*om` smoothness on the regular set.
Subsequent chip (`SmoothOneFormOn` packaging) globalises via
`ContMDiffOn = ContMDiffAt-on-every-point`.

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

/-- **`fStarOmega om` is `ContMDiffAt ∞` at a regular value.**

For every regular value `v₀ ∈ f.regularValueSet`, the section
`v ↦ TotalSpace.mk' (ℂ →L[ℝ] ℝ) v (f.fStarOmega hnc om v)` is
`ContMDiffAt 𝓘(ℝ, ℂ) ((𝓘(ℝ, ℂ)).prod 𝓘(ℝ, ℂ →L[ℝ] ℝ)) ∞` at `v₀`.

The Finset over which we sum is `f.fiberFinset hv₀`, fixed once at `v₀`
(this is exactly the labelling-nbhd Finset that
`FStarOmegaLocalAt.fStarOmega_eq_sum_sheetCotPullback_at_v0` ranges over). -/
theorem fStarOmega_contMDiffAt
    [DecidableEq X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (om : SmoothOneForm (𝓘(ℝ, ℂ)) X)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet) :
    ContMDiffAt (𝓘(ℝ, ℂ)) ((𝓘(ℝ, ℂ)).prod 𝓘(ℝ, ℂ →L[ℝ] ℝ)) ⊤
      (fun v : RiemannSphere => Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) v
        (f.fStarOmega hnc om v))
      v₀ := by
  classical
  -- Per-summand: each `v ↦ sheetCotPullback p v om` is `ContMDiffAt` at `v₀`.
  have h_per_sheet :
      ∀ p ∈ (f.fiberFinset hv₀).attach,
        ContMDiffAt (𝓘(ℝ, ℂ)) ((𝓘(ℝ, ℂ)).prod 𝓘(ℝ, ℂ →L[ℝ] ℝ)) ⊤
          (fun v : RiemannSphere => Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) v
            (f.sheetCotPullback hnc
              (f.mem_regularSet_of_preimage_regularValue hv₀
                ((f.mem_fiberFinset_iff hv₀ p.val).mp p.property))
              v om)) v₀ := by
    intro p _
    have hp_reg : p.val ∈ f.regularSet :=
      f.mem_regularSet_of_preimage_regularValue hv₀
        ((f.mem_fiberFinset_iff hv₀ p.val).mp p.property)
    have hp_to_v₀ : f.toRiemannSphere p.val = v₀ :=
      (f.mem_fiberFinset_iff hv₀ p.val).mp p.property
    have h := f.sheetCotPullback_contMDiffAt hnc hp_reg om
    rw [hp_to_v₀] at h
    exact h
  -- Sum smoothness via mathlib's `ContMDiffAt.sum_section`.
  have h_sum :
      ContMDiffAt (𝓘(ℝ, ℂ)) ((𝓘(ℝ, ℂ)).prod 𝓘(ℝ, ℂ →L[ℝ] ℝ)) ⊤
        (fun v : RiemannSphere => Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) v
          (∑ p ∈ (f.fiberFinset hv₀).attach,
            f.sheetCotPullback hnc
              (f.mem_regularSet_of_preimage_regularValue hv₀
                ((f.mem_fiberFinset_iff hv₀ p.val).mp p.property))
              v om)) v₀ :=
    ContMDiffAt.sum_section h_per_sheet
  -- Bridge to `fStarOmega` via the labelling-nbhd equality.
  refine h_sum.congr_of_eventuallyEq ?_
  have h_labelling_nbhd :
      f.localFiberLabelingNbhd hnc hv₀ ∈ nhds v₀ :=
    (f.localFiberLabelingNbhd_isOpen hnc hv₀).mem_nhds
      (f.mem_localFiberLabelingNbhd_self hnc hv₀)
  filter_upwards [h_labelling_nbhd] with v hv
  -- Pointwise: at every `v` in the labelling nbhd, fStarOmega = Finset sum.
  show Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) v (f.fStarOmega hnc om v)
    = Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) v _
  congr 1
  exact f.fStarOmega_eq_sum_sheetCotPullback_at_v0 hnc om hv₀ hv

end MeromorphicNonzero

end JacobianChallenge

end
