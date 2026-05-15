/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroFStarOmegaDef
import JacobianChallenge.Manifold.MeromorphicNonzeroFiberLocallyConst
import JacobianChallenge.Manifold.SourceSheetSumEqTraceAt

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `fStarOmega` as a fixed Finset sum on a labelling neighbourhood

For `v₀ ∈ f.regularValueSet` and `v` in the open nbhd
`localFiberLabelingNbhd hnc hv₀`, the trace `fStarOmega hnc om v`
equals a fixed `Finset` sum indexed by `f.fiberFinset hv₀`:

```
fStarOmega f hnc om v
  = ∑ p ∈ (f.fiberFinset hv₀).attach,
      cotangentPullbackAt (fiberSheetAt p).g v om
```

The argument composes two pieces already in tree:

1. **Re-indexing (f-2).** On the labelling nbhd, the fibre at `v` is
   bijectively labelled by the fibre at `v₀` via `p ↦ (fiberSheetAt p).g v`
   (`fiberSheetAt_g_image_eq_fiberFinset`).
2. **Cross-sheet identification (already in tree).** For each `p`, the
   cotangent pullback through `(fiberSheetAt p).g` at `v` equals the
   cotangent pullback through the sheet at the target point
   `q := (fiberSheetAt p).g v`
   (`cotangentPullbackAt_localSheet_eq_at_target_sheet`).

Combining: `traceAt f hv'` (= sum over fiber at v) re-indexes by the
bijection to a sum over fiber at v₀, with each summand transported
to the source-sheet form by the cross-sheet identification.

This is the **fixed Finset rewrite** that decouples the trace from
the v-varying fiber, enabling smoothness packaging
(`f-4` → `f-5`).

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

/-- **Fixed-Finset rewrite of `fStarOmega` on the labelling nbhd.**

For `v ∈ localFiberLabelingNbhd hnc hv₀` (which is open and ⊆
regularValueSet), `fStarOmega f hnc om v` equals the source-sheet sum
indexed by `f.fiberFinset hv₀.attach`. -/
theorem fStarOmega_eq_sum_sheetCotPullback_at_v0
    [DecidableEq X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet)
    {v : RiemannSphere} (hv : v ∈ f.localFiberLabelingNbhd hnc hv₀) :
    f.fStarOmega hnc om v
      = ∑ p ∈ (f.fiberFinset hv₀).attach,
          f.sheetCotPullback hnc
            (f.mem_regularSet_of_preimage_regularValue hv₀
              ((f.mem_fiberFinset_iff hv₀ p.val).mp p.property))
            v om := by
  classical
  have hv' : v ∈ f.regularValueSet :=
    f.localFiberLabelingNbhd_subset_regularValueSet hnc hv₀ hv
  -- Step 1: fStarOmega = traceAt at the regular value v.
  rw [f.fStarOmega_apply_of_regular hnc om hv']
  -- Step 2: traceAt = ∑_{q ∈ fiberFinset hv'} sheetCotPullback at q.
  rw [f.traceAt_eq_sum_sheetCotPullback hnc hv' om]
  -- Step 3: re-index via the labelling bijection (p ↦ (fiberSheetAt p).g v).
  -- The bijection: image of attach equals fiberFinset f hv', via
  -- fiberSheetAt_g_image_eq_fiberFinset (f-2).
  -- Apply Finset.sum_bij with the explicit bijection.
  refine (Finset.sum_bij
      (fun p _ =>
        ⟨(f.fiberSheetAt hnc hv₀ p).g v,
          f.fiberSheetAt_g_mem_fiberFinset hnc hv₀ p hv hv'⟩)
      ?_ ?_ ?_ ?_).symm
  · -- maps into target Finset.attach
    intro p _; exact Finset.mem_attach _ _
  · -- injectivity
    intro p₁ _ p₂ _ h_eq
    -- Both sides give Subtype elements; project to value.
    have h_val_eq :
        (f.fiberSheetAt hnc hv₀ p₁).g v = (f.fiberSheetAt hnc hv₀ p₂).g v :=
      Subtype.ext_iff.mp h_eq
    -- Apply InjOn from f-2.
    exact f.fiberSheetAt_g_injOn hnc hv₀ hv (Finset.mem_attach _ _)
      (Finset.mem_attach _ _) h_val_eq
  · -- surjectivity
    intro q _
    -- q : f.fiberFinset hv'.attach, q.val ∈ fiberFinset hv'.
    -- By image=fiberFinset, q.val is in the image of attach under our map.
    have h_image_eq :=
      f.fiberSheetAt_g_image_eq_fiberFinset hnc hv₀ hv hv'
    have hq_in_image : q.val ∈ (f.fiberFinset hv₀).attach.image
        (fun p => (f.fiberSheetAt hnc hv₀ p).g v) := by
      rw [h_image_eq]; exact q.property
    rw [Finset.mem_image] at hq_in_image
    obtain ⟨p, hp_attach, hp_eq⟩ := hq_in_image
    refine ⟨p, hp_attach, ?_⟩
    -- Goal: ⟨(fiberSheetAt p).g v, _⟩ = q
    apply Subtype.ext
    exact hp_eq
  · -- per-summand equality: cross-sheet identification
    intro p _
    -- Goal: target sheet pullback at q := (fiberSheetAt p).g v = source sheet pullback at p.
    -- Apply cotangentPullbackAt_localSheet_eq_at_target_sheet.
    unfold sheetCotPullback
    -- The target sheet's regular witness is built via mem_regularSet_of_preimage at the
    -- new fiber point ⟨(fiberSheetAt p).g v, ...⟩.
    -- The cross-sheet identification gives sheet_p.g pullback = sheet_q.g pullback.
    have hp_reg : p.val ∈ f.regularSet :=
      f.mem_regularSet_of_preimage_regularValue hv₀
        ((f.mem_fiberFinset_iff hv₀ p.val).mp p.property)
    have hv_in_Vp : v ∈ (f.fiberSheetAt hnc hv₀ p).V :=
      f.mem_V_of_mem_localFiberLabelingNbhd hnc hv₀ p hv
    -- Cross-sheet identification:
    have h_cross := f.cotangentPullbackAt_localSheet_eq_at_target_sheet hnc
      hp_reg hv' hv_in_Vp om
    -- h_cross : cotangentPullbackAt (localSheetData_at_regular hnc hp_reg).g v om
    --   = cotangentPullbackAt (localSheetData_at_regular hnc (regular at sheet_p.g v)).g v om
    -- The two regularity witnesses (target side: from rightInvOn vs from
    -- mem_fiberFinset_iff lookup) are propositionally equal. Both target
    -- sheets are `localSheetData_at_regular hnc <proof>`; since the
    -- regularity-set membership is a Prop, the two sheets are equal by
    -- proof irrelevance applied at the witness level.
    rw [h_cross]
    rfl

end MeromorphicNonzero

end JacobianChallenge

end
