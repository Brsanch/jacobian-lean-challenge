/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.TraceFactorContinuousOnFromSheets

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Trace-factor `ContinuousOn` along `β` on the β-preimage of a labelling nbhd

Pulls back `continuousOn_cotangentEquiv_fStarOmega_of_per_sheet`
along a continuous `β : ℝ → RiemannSphere`. The result is
`ContinuousOn` of the trace-factor `cotangentEquiv (fStarOmega om (β s))`
on `S ⊆ β ⁻¹' (localFiberLabelingNbhd hv₀)`.

Composition pattern:

```
ContinuousOn cotangentEquiv∘fStarOmega∘β on β⁻¹(labelling nbhd)
    = (ContinuousOn cotangentEquiv∘fStarOmega on labelling nbhd).comp
        (Continuous β).continuousOn
        (mapsTo of preimage)
```

For Icc 0 1 (or any sub-set), one extracts the result by intersecting
with the preimage `S := Icc 0 1 ∩ β ⁻¹' (localFiberLabelingNbhd hv₀)`
and (in a downstream chip) gluing across finitely many labelling-nbhd
covers of `β '' Icc 0 1` (which is compact).

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

/-- **Trace-factor `ContinuousOn` along `β` on the β-preimage of a labelling nbhd.**

If the per-sheet cotangent-pullback continuities on the labelling nbhd
hold, then their pullback along a continuous `β : ℝ → RiemannSphere`
yields trace-factor `ContinuousOn` on any subset of
`β ⁻¹' (localFiberLabelingNbhd hv₀)`. -/
theorem continuousOn_cotangentEquiv_fStarOmega_along_beta_on_preimage
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    {β : ℝ → RiemannSphere} (hβ_cont : Continuous β)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet)
    (h_per_sheet : ∀ p ∈ (f.fiberFinset hv₀).attach,
      ContinuousOn
        (fun v : RiemannSphere =>
          (SmoothPath.cotangentEquiv
            (f.sheetCotPullback hnc
              (f.mem_regularSet_of_preimage_regularValue hv₀
                ((f.mem_fiberFinset_iff hv₀ p.val).mp p.property))
              v om) : ℂ →L[ℝ] ℝ))
        (f.localFiberLabelingNbhd hnc hv₀))
    {S : Set ℝ}
    (hS : S ⊆ β ⁻¹' (f.localFiberLabelingNbhd hnc hv₀)) :
    ContinuousOn
      (fun s : ℝ =>
        (SmoothPath.cotangentEquiv (f.fStarOmega hnc om (β s)) : ℂ →L[ℝ] ℝ))
      S := by
  -- Trace-factor `ContinuousOn` on the labelling nbhd from per-sheet inputs.
  have h_target :
      ContinuousOn
        (fun v : RiemannSphere =>
          (SmoothPath.cotangentEquiv (f.fStarOmega hnc om v) : ℂ →L[ℝ] ℝ))
        (f.localFiberLabelingNbhd hnc hv₀) :=
    f.continuousOn_cotangentEquiv_fStarOmega_of_per_sheet hnc om hv₀ h_per_sheet
  -- `β` is continuous, hence `ContinuousOn` everywhere; restrict to `S`.
  have h_beta : ContinuousOn β S := hβ_cont.continuousOn
  -- Composition with `MapsTo β S (labelling nbhd)`.
  have h_maps : MapsTo β S (f.localFiberLabelingNbhd hnc hv₀) := by
    intro s hs; exact hS hs
  exact h_target.comp h_beta h_maps

end MeromorphicNonzero

end JacobianChallenge

end
