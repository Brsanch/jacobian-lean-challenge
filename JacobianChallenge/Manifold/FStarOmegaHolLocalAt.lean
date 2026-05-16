/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroFStarOmegaHolDef
import JacobianChallenge.Manifold.MeromorphicNonzeroFiberLocallyConst

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `fStarOmegaHol` as a fixed Finset sum on a labelling neighbourhood

Holomorphic-side analogue of
`FStarOmegaLocalAt.fStarOmega_eq_sum_sheetCotPullback_at_v0`. For
`v₀ ∈ f.regularValueSet` and `v` in the open nbhd
`localFiberLabelingNbhd hnc hv₀`, the holomorphic trace
`fStarOmegaHol hnc α v` equals a fixed `Finset` sum indexed by
`f.fiberFinset hv₀`:

```
fStarOmegaHol f hnc α v
  = ∑ p ∈ (f.fiberFinset hv₀).attach,
      holSheetCotPullback hnc (regular at p) v α
```

The argument is the exact mirror of the realified case:

1. **Re-indexing.** On the labelling nbhd, the fibre at `v` is
   bijectively labelled by the fibre at `v₀` via
   `p ↦ (fiberSheetAt p).g v`.
2. **Cross-sheet identification.** For each `p`, the holomorphic
   cotangent pullback through `(fiberSheetAt p).g` at `v` equals the
   holomorphic cotangent pullback through the sheet at the target
   point `q := (fiberSheetAt p).g v`
   (`holCotangentPullbackAt_localSheet_eq_at_target_sheet`).

These two pieces are bundle-independent (re-indexing depends only on
the set-level fibre bijection; cross-sheet identification is the
holomorphic analogue shipped in `MeromorphicNonzeroHolTraceAt.lean`).

This is the **fixed Finset rewrite** decoupling the trace from the
v-varying fibre, enabling smoothness packaging (subsequent chip:
`f.fStarOmegaHol_contMDiffAt`).

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

/-- **Fixed-Finset rewrite of `fStarOmegaHol` on the labelling nbhd.**

Holomorphic-side parallel to
`fStarOmega_eq_sum_sheetCotPullback_at_v0`. For
`v ∈ localFiberLabelingNbhd hnc hv₀` (which is open and ⊆
regularValueSet), `fStarOmegaHol f hnc α v` equals the source-sheet
sum indexed by `f.fiberFinset hv₀.attach`. -/
theorem fStarOmegaHol_eq_sum_holSheetCotPullback_at_v0
    [DecidableEq X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (α : HolomorphicOneForm X)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet)
    {v : RiemannSphere} (hv : v ∈ f.localFiberLabelingNbhd hnc hv₀) :
    f.fStarOmegaHol hnc α v
      = ∑ p ∈ (f.fiberFinset hv₀).attach,
          f.holSheetCotPullback hnc
            (f.mem_regularSet_of_preimage_regularValue hv₀
              ((f.mem_fiberFinset_iff hv₀ p.val).mp p.property))
            v α := by
  classical
  have hv' : v ∈ f.regularValueSet :=
    f.localFiberLabelingNbhd_subset_regularValueSet hnc hv₀ hv
  -- Step 1: fStarOmegaHol = holTraceAt at the regular value v.
  rw [f.fStarOmegaHol_apply_of_regular hnc α hv']
  -- Step 2: holTraceAt = ∑_{q ∈ fiberFinset hv'} holSheetCotPullback at q.
  rw [f.holTraceAt_eq_sum_holSheetCotPullback hnc hv' α]
  -- Step 3: re-index via the labelling bijection (p ↦ (fiberSheetAt p).g v).
  refine (Finset.sum_bij
      (fun p _ =>
        ⟨(f.fiberSheetAt hnc hv₀ p).g v,
          f.fiberSheetAt_g_mem_fiberFinset hnc hv₀ p hv hv'⟩)
      ?_ ?_ ?_ ?_).symm
  · intro p _; exact Finset.mem_attach _ _
  · intro p₁ _ p₂ _ h_eq
    have h_val_eq :
        (f.fiberSheetAt hnc hv₀ p₁).g v = (f.fiberSheetAt hnc hv₀ p₂).g v :=
      Subtype.ext_iff.mp h_eq
    exact f.fiberSheetAt_g_injOn hnc hv₀ hv (Finset.mem_attach _ _)
      (Finset.mem_attach _ _) h_val_eq
  · intro q _
    have h_image_eq :=
      f.fiberSheetAt_g_image_eq_fiberFinset hnc hv₀ hv hv'
    have hq_in_image : q.val ∈ (f.fiberFinset hv₀).attach.image
        (fun p => (f.fiberSheetAt hnc hv₀ p).g v) := by
      rw [h_image_eq]; exact q.property
    rw [Finset.mem_image] at hq_in_image
    obtain ⟨p, hp_attach, hp_eq⟩ := hq_in_image
    refine ⟨p, hp_attach, ?_⟩
    apply Subtype.ext
    exact hp_eq
  · -- per-summand equality: cross-sheet identification (holomorphic).
    intro p _
    unfold holSheetCotPullback
    have hp_reg : p.val ∈ f.regularSet :=
      f.mem_regularSet_of_preimage_regularValue hv₀
        ((f.mem_fiberFinset_iff hv₀ p.val).mp p.property)
    have hv_in_Vp : v ∈ (f.fiberSheetAt hnc hv₀ p).V :=
      f.mem_V_of_mem_localFiberLabelingNbhd hnc hv₀ p hv
    have h_cross := f.holCotangentPullbackAt_localSheet_eq_at_target_sheet hnc
      hp_reg hv' hv_in_Vp α
    rw [h_cross]
    rfl

end MeromorphicNonzero

end JacobianChallenge

end
