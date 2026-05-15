/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CotangentPullbackSheetIdentification
import JacobianChallenge.Manifold.SourceFiberPathAmbientSurjOnAt

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Source-side cotangent pullback sum equals `traceAt` at the lifted value

For `t ∈ Icc 0 1` and the standard regular-path setup, the
**source-indexed** chain-rule sum
`∑_{p ∈ sourceFiber} cotangentPullbackAt sheet_p.g (β(σ t)) ω`
equals the **target-indexed** trace
`traceAt f hnc hβσt_reg ω
  = ∑_{q ∈ fiberFinset(β(σ t))} cotangentPullbackAt sheet_q.g (β(σ t)) ω`,
provided the **sub-interval condition** holds: for every `p ∈ sourceFiber`,
`β(σ t) ∈ sheet_p.V`.

Two-stage proof:

1. **Per-fiber** (`cotangentPullbackAt_localSheet_eq_at_target_sheet`):
   for each `p`, source-sheet pullback = target-sheet pullback at the
   lifted point.

2. **Re-indexing** (`sourceFiberPath_toPath_extend_image_eq_fiberFinset_at`):
   bijection `sourceFiber → fiberFinset(v)` re-indexes the sum.

To dodge a parser issue with `cotangentPullbackAt (I := …)` named-args
inside the conclusion at the file's top-level term mode, the per-fiber
sheet-cotangent-pullback function is wrapped in a local `noncomputable
def` `sheetCotPullback` that fixes both model arguments.

## What ships

* `MeromorphicNonzero.sheetCotPullback` — wrapper for
  `cotangentPullbackAt` at the source-sheet inverse with both model
  arguments fixed at `𝓘(ℝ, ℂ)`.
* `MeromorphicNonzero.source_sheet_sum_eq_traceAt` — the headline
  per-`t` identification.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Wrapper for source-side cotangent pullback at a sheet inverse.**
Fixes both model arguments at `𝓘(ℝ, ℂ)`. -/
noncomputable def sheetCotPullback
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {x₀ : X} (hx_reg : x₀ ∈ f.regularSet)
    (v : RiemannSphere) (om : SmoothOneForm 𝓘(ℝ, ℂ) X) :
    CotangentSpace 𝓘(ℝ, ℂ) v :=
  cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
    (f.localSheetData_at_regular hnc hx_reg).g v om

/-- **`traceAt` rewritten via `sheetCotPullback`.** Definitional
unfolding: the trace at a regular value is the source-fibre sum of
`sheetCotPullback` over local sheets at fibre points. -/
lemma traceAt_eq_sum_sheetCotPullback
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X) :
    f.traceAt hnc hv om
      = ∑ p ∈ (f.fiberFinset hv).attach,
          f.sheetCotPullback hnc
            (f.mem_regularSet_of_preimage_regularValue hv
              ((f.mem_fiberFinset_iff hv p.val).mp p.property))
            v om := by
  unfold traceAt sheetCotPullback
  rfl

/-- **Per-`t` identification: source-side cotangent pullback sum = `traceAt`.** -/
theorem source_sheet_sum_eq_traceAt
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hβσt_reg : β (Real.smoothTransition t) ∈ f.regularValueSet)
    (hβ0_reg : β 0 ∈ f.regularValueSet)
    (h_sub_interval :
      ∀ p : { x : X // x ∈ f.sourceFiber hβ0_reg },
        β (Real.smoothTransition t) ∈
          (f.localSheetData_at_regular hnc
            (f.mem_regularSet_of_preimage_regularValue hβ0_reg
              ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property))).V)
    (h_lift_eq :
      ∀ p : { x : X // x ∈ f.sourceFiber hβ0_reg },
        (f.sourceFiberPath hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).toPath.extend t
          = (f.localSheetData_at_regular hnc
              (f.mem_regularSet_of_preimage_regularValue hβ0_reg
                ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property))).g
              (β (Real.smoothTransition t))) :
    ∑ p ∈ (f.sourceFiber hβ0_reg).attach,
        f.sheetCotPullback hnc
          (f.mem_regularSet_of_preimage_regularValue hβ0_reg
            ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property))
          (β (Real.smoothTransition t)) om
      = f.traceAt hnc hβσt_reg om := by
  classical
  -- Stage 1: per-p, source-sheet pullback = target-sheet pullback at q_p := sheet_p.g v.
  have h_per_p :
      ∀ p ∈ (f.sourceFiber hβ0_reg).attach,
        f.sheetCotPullback hnc
          (f.mem_regularSet_of_preimage_regularValue hβ0_reg
            ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property))
          (β (Real.smoothTransition t)) om
        = f.sheetCotPullback hnc
          (f.mem_regularSet_of_preimage_regularValue hβσt_reg
            ((f.localSheetData_at_regular hnc
              (f.mem_regularSet_of_preimage_regularValue hβ0_reg
                ((f.mem_sourceFiber_iff hβ0_reg p.val).mp
                  p.property))).rightInvOn
              (h_sub_interval p)))
          (β (Real.smoothTransition t)) om := by
    intro p _
    -- Both sides unfold to cotangentPullbackAt; apply the cross-sheet identification.
    unfold sheetCotPullback
    exact f.cotangentPullbackAt_localSheet_eq_at_target_sheet hnc
      (f.mem_regularSet_of_preimage_regularValue hβ0_reg
        ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property))
      hβσt_reg (h_sub_interval p) om
  rw [Finset.sum_congr rfl h_per_p]
  -- Stage 2: re-index via the bijection.
  rw [traceAt_eq_sum_sheetCotPullback]
  refine Finset.sum_bij
    (fun p _ =>
      ⟨(f.localSheetData_at_regular hnc
        (f.mem_regularSet_of_preimage_regularValue hβ0_reg
          ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property))).g
        (β (Real.smoothTransition t)),
      by
        rw [f.mem_fiberFinset_iff hβσt_reg]
        exact (f.localSheetData_at_regular hnc
          (f.mem_regularSet_of_preimage_regularValue hβ0_reg
            ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property))).rightInvOn
          (h_sub_interval p)⟩) ?_ ?_ ?_ ?_
  · -- maps into target Finset.attach
    intro p _; exact Finset.mem_attach _ _
  · -- injectivity
    intro p₁ _ p₂ _ h_eq
    apply Subtype.ext
    have h_sheet_eq :
        (f.localSheetData_at_regular hnc
          (f.mem_regularSet_of_preimage_regularValue hβ0_reg
            ((f.mem_sourceFiber_iff hβ0_reg p₁.val).mp p₁.property))).g
            (β (Real.smoothTransition t))
        = (f.localSheetData_at_regular hnc
          (f.mem_regularSet_of_preimage_regularValue hβ0_reg
            ((f.mem_sourceFiber_iff hβ0_reg p₂.val).mp p₂.property))).g
            (β (Real.smoothTransition t)) :=
      Subtype.ext_iff.mp h_eq
    have h_lift_p₁ := h_lift_eq p₁
    have h_lift_p₂ := h_lift_eq p₂
    have h_extend_eq :
        (f.sourceFiberPath hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff hβ0_reg p₁.val).mp p₁.property)).toPath.extend t
          = (f.sourceFiberPath hnc hβ_smooth hβ_reg
            ((f.mem_sourceFiber_iff hβ0_reg p₂.val).mp p₂.property)).toPath.extend t := by
      rw [h_lift_p₁, h_lift_p₂]; exact h_sheet_eq
    exact f.sourceFiberPath_toPath_extend_injOn_at hnc hβ_smooth hβ_reg
      ((f.mem_sourceFiber_iff hβ0_reg p₁.val).mp p₁.property)
      ((f.mem_sourceFiber_iff hβ0_reg p₂.val).mp p₂.property)
      ht h_extend_eq
  · -- surjectivity
    intro q _
    have hq_finset : q.val ∈ f.fiberFinset hβσt_reg := q.property
    have h_image_eq :=
      f.sourceFiberPath_toPath_extend_image_eq_fiberFinset_at hnc hβ_smooth hβ_reg
        ht hβσt_reg
    have hq_in_image : q.val ∈ (f.sourceFiber hβ0_reg).attach.image
        (fun p => (f.sourceFiberPath hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).toPath.extend t) := by
      rw [h_image_eq]; exact hq_finset
    rw [Finset.mem_image] at hq_in_image
    obtain ⟨p, hp_attach, h_extend_eq⟩ := hq_in_image
    refine ⟨p, hp_attach, ?_⟩
    apply Subtype.ext
    change (f.localSheetData_at_regular hnc
      (f.mem_regularSet_of_preimage_regularValue hβ0_reg
        ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property))).g
        (β (Real.smoothTransition t)) = q.val
    rw [← h_lift_eq p]
    exact h_extend_eq
  · -- summand congruence
    intro p _
    rfl

end MeromorphicNonzero

end JacobianChallenge

end
