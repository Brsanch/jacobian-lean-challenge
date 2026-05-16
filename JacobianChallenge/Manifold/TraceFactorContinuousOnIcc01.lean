/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.TraceFactorContinuousOnAlongBeta

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Trace-factor `ContinuousOn (Icc 0 1)` via pointwise labelling-nbhd cover

Glues `continuousOn_cotangentEquiv_fStarOmega_along_beta_on_preimage`
into a global `ContinuousOn (Icc 0 1)` statement by the standard
pointwise `ContinuousWithinAt`-at-every-point pattern:

For each `s₀ ∈ Icc 0 1`, the labelling nbhd `U(β s₀) :=
localFiberLabelingNbhd hnc (hβ_reg s₀ hs₀)` is open, contains `β s₀`,
and is ⊆ `regularValueSet`. Its preimage `β ⁻¹ U(β s₀)` is open in ℝ
and contains `s₀`. On this open preimage, the prior chip gives
`ContinuousOn` of the trace-factor — hence `ContinuousWithinAt` at
`s₀` within `Icc 0 1`. Pointwise aggregation gives
`ContinuousOn (Icc 0 1)`.

The remaining analytic input is the **universal-quantified per-sheet
continuity hypothesis** `h_per_sheet_univ`: for every regular value
`v₀ : RiemannSphere`, the per-sheet cotangent-pullback continuities on
the labelling nbhd at `v₀`. This is the natural API for the
forthcoming `cotangentPullbackAt` smoothness/continuity chip.

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

/-- **Trace-factor `ContinuousOn (Icc 0 1)`** via pointwise gluing of
labelling-nbhd preimages.

Given the universal per-sheet ContinuousOn input
`h_per_sheet_univ`, the trace-factor
`s ↦ cotangentEquiv (fStarOmega om (β s))` is `ContinuousOn (Icc 0 1)`. -/
theorem continuousOn_cotangentEquiv_fStarOmega_along_beta_Icc01
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    {β : ℝ → RiemannSphere} (hβ_cont : Continuous β)
    (hβ_reg : ∀ s ∈ Icc (0 : ℝ) 1, β s ∈ f.regularValueSet)
    (h_per_sheet_univ :
      ∀ {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet),
        ∀ p ∈ (f.fiberFinset hv₀).attach,
          ContinuousOn
            (fun v : RiemannSphere =>
              (SmoothPath.cotangentEquiv
                (f.sheetCotPullback hnc
                  (f.mem_regularSet_of_preimage_regularValue hv₀
                    ((f.mem_fiberFinset_iff hv₀ p.val).mp p.property))
                  v om) : ℂ →L[ℝ] ℝ))
            (f.localFiberLabelingNbhd hnc hv₀)) :
    ContinuousOn
      (fun s : ℝ =>
        (SmoothPath.cotangentEquiv (f.fStarOmega hnc om (β s)) : ℂ →L[ℝ] ℝ))
      (Icc (0 : ℝ) 1) := by
  -- Pointwise: at each `s₀ ∈ Icc 0 1`, exhibit `ContinuousWithinAt`.
  intro s₀ hs₀
  -- Regularity witness at `β s₀`.
  have hβs₀_reg : β s₀ ∈ f.regularValueSet := hβ_reg s₀ hs₀
  -- Take the labelling nbhd at `β s₀`.
  set U : Set RiemannSphere := f.localFiberLabelingNbhd hnc hβs₀_reg with hU_def
  -- `U` is open and contains `β s₀`.
  have hU_open : IsOpen U := f.localFiberLabelingNbhd_isOpen hnc hβs₀_reg
  have hβs₀_in_U : β s₀ ∈ U := f.mem_localFiberLabelingNbhd_self hnc hβs₀_reg
  -- β-preimage of `U` is open in ℝ and contains `s₀`.
  set T : Set ℝ := β ⁻¹' U with hT_def
  have hT_open : IsOpen T := hU_open.preimage hβ_cont
  have hs₀_in_T : s₀ ∈ T := hβs₀_in_U
  -- Per-sheet input at `v₀ = β s₀` from the universal hypothesis.
  have h_per_sheet := h_per_sheet_univ hβs₀_reg
  -- Apply the pullback chip on `T` (trivially `T ⊆ β ⁻¹ U` = `T`).
  have h_cont_on_T :
      ContinuousOn
        (fun s : ℝ =>
          (SmoothPath.cotangentEquiv (f.fStarOmega hnc om (β s)) : ℂ →L[ℝ] ℝ))
        T :=
    f.continuousOn_cotangentEquiv_fStarOmega_along_beta_on_preimage
      hnc om hβ_cont hβs₀_reg h_per_sheet (subset_refl _)
  -- `T` is an open nhd of `s₀`; convert `ContinuousOn T` to
  -- `ContinuousAt s₀` and then to `ContinuousWithinAt (Icc 0 1) s₀`.
  have h_at_s₀ : ContinuousAt
      (fun s : ℝ =>
        (SmoothPath.cotangentEquiv (f.fStarOmega hnc om (β s)) : ℂ →L[ℝ] ℝ))
      s₀ :=
    (h_cont_on_T.continuousAt (hT_open.mem_nhds hs₀_in_T))
  exact h_at_s₀.continuousWithinAt

end MeromorphicNonzero

end JacobianChallenge

end
