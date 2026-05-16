/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.FStarOmegaLocalAt
import JacobianChallenge.Manifold.ApplyCotangentContinuity

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `cotangentEquiv ∘ fStarOmega` as a `Finset` sum on the labelling nbhd

`SmoothPath.cotangentEquiv : CotangentSpace I x ≃ₗ[ℝ] (E →L[ℝ] ℝ)` is
a linear equivalence (identity on data); in particular it commutes
with finite sums. Composing with the `f-3` rewrite
`fStarOmega_eq_sum_sheetCotPullback_at_v0` yields:

```
(cotangentEquiv (fStarOmega f hnc om v) : ℂ →L[ℝ] ℝ)
  = ∑ p ∈ (fiberFinset hv₀).attach,
      (cotangentEquiv (sheetCotPullback hnc reg_p v om) : ℂ →L[ℝ] ℝ)
```

for `v` in `localFiberLabelingNbhd hnc hv₀`.

This is the CLM-level rewrite needed to express
**trace-factor continuity** along a smooth path as a finite sum of
per-sheet-pullback continuities. Downstream chips can then discharge
the sum-continuity from per-summand continuity via
`continuousOn_finset_sum`.

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

/-- **`cotangentEquiv` of `fStarOmega` on the labelling nbhd as a CLM-level
`Finset` sum.** Combines `cotangentEquiv`'s ℝ-linearity (hence commutation
with `Finset.sum`) with the `f-3` source-sheet sum rewrite. -/
theorem cotangentEquiv_fStarOmega_eq_sum_cotangentEquiv_sheetCotPullback
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet)
    {v : RiemannSphere} (hv : v ∈ f.localFiberLabelingNbhd hnc hv₀) :
    (SmoothPath.cotangentEquiv (f.fStarOmega hnc om v) : ℂ →L[ℝ] ℝ)
      = ∑ p ∈ (f.fiberFinset hv₀).attach,
          (SmoothPath.cotangentEquiv
            (f.sheetCotPullback hnc
              (f.mem_regularSet_of_preimage_regularValue hv₀
                ((f.mem_fiberFinset_iff hv₀ p.val).mp p.property))
              v om) : ℂ →L[ℝ] ℝ) := by
  classical
  -- `f-3`: rewrite `fStarOmega` as a fixed-Finset sum on the labelling nbhd.
  rw [f.fStarOmega_eq_sum_sheetCotPullback_at_v0 hnc om hv₀ hv]
  -- `cotangentEquiv` is ℝ-linear, hence commutes with `Finset.sum`.
  exact map_sum SmoothPath.cotangentEquiv.toLinearMap _ _

end MeromorphicNonzero

end JacobianChallenge

end
