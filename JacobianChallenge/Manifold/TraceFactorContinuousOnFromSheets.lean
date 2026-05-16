/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CotangentEquivFStarOmegaSum

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Trace-factor `ContinuousOn` on the labelling nbhd from per-sheet continuities

On `localFiberLabelingNbhd hv₀`, the rewrite

```
(cotangentEquiv (fStarOmega om v) : ℂ →L[ℝ] ℝ)
  = ∑ p ∈ (fiberFinset hv₀).attach,
      (cotangentEquiv (sheetCotPullback hnc reg_p v om) : ℂ →L[ℝ] ℝ)
```

(`cotangentEquiv_fStarOmega_eq_sum_cotangentEquiv_sheetCotPullback`) lets
us transfer `ContinuousOn` from the finite sum of per-sheet pullbacks
to the `fStarOmega` form via `Finset.continuousOn_sum` and
`ContinuousOn.congr`.

This is the **sum-aggregation step** on the way to discharging the
`trace-factor` half of
`integrandContinuousAlongBeta_of_factor_continuousOn`. The remaining
analytic content (per-sheet `cotangentPullbackAt` continuity in the
base point, viewed through `cotangentEquiv`) is exactly the
`f-4` infrastructure being built incrementally.

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

/-- **Trace-factor `ContinuousOn` from per-sheet `ContinuousOn`.**

If for every fibre point `p ∈ fiberFinset hv₀`, the per-sheet
cotangent pullback (viewed through `cotangentEquiv` as a concrete
`ℂ →L[ℝ] ℝ`) is `ContinuousOn` the labelling nbhd, then so is
`cotangentEquiv ∘ fStarOmega`. -/
theorem continuousOn_cotangentEquiv_fStarOmega_of_per_sheet
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet)
    (h_per_sheet : ∀ p ∈ (f.fiberFinset hv₀).attach,
      ContinuousOn
        (fun v : RiemannSphere =>
          (SmoothPath.cotangentEquiv
            (f.sheetCotPullback hnc
              (f.mem_regularSet_of_preimage_regularValue hv₀
                ((f.mem_fiberFinset_iff hv₀ p.val).mp p.property))
              v om) : ℂ →L[ℝ] ℝ))
        (f.localFiberLabelingNbhd hnc hv₀)) :
    ContinuousOn
      (fun v : RiemannSphere =>
        (SmoothPath.cotangentEquiv (f.fStarOmega hnc om v) : ℂ →L[ℝ] ℝ))
      (f.localFiberLabelingNbhd hnc hv₀) := by
  classical
  -- Sum is continuous-on a set when each summand is.
  have h_sum : ContinuousOn
      (fun v : RiemannSphere =>
        ∑ p ∈ (f.fiberFinset hv₀).attach,
          (SmoothPath.cotangentEquiv
            (f.sheetCotPullback hnc
              (f.mem_regularSet_of_preimage_regularValue hv₀
                ((f.mem_fiberFinset_iff hv₀ p.val).mp p.property))
              v om) : ℂ →L[ℝ] ℝ))
      (f.localFiberLabelingNbhd hnc hv₀) := by
    apply continuousOn_finset_sum
    intro p hp
    exact h_per_sheet p hp
  -- Transfer to the `fStarOmega` form via the CLM-level sum identity.
  refine h_sum.congr ?_
  intro v hv
  -- `ContinuousOn.congr` needs `g v = f v` (goal-side equals source-side).
  exact f.cotangentEquiv_fStarOmega_eq_sum_cotangentEquiv_sheetCotPullback
    hnc om hv₀ hv

end MeromorphicNonzero

end JacobianChallenge

end
