/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RamificationSumEqualsDegree
import JacobianChallenge.Divisor.FiberPullbackWeighted

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Bridge: ramification-sum identity → `hN_total` packaging (ZZ179e)

Composer chip. Given `ramificationSumEqualsDegree_statement` as a
hypothesis (the named obligation from
`Manifold/RamificationSumEqualsDegree.lean`), produces the `hN_total`
shape that `Pic0.pullbackWeighted` consumes:

```
∀ y, (∑ x ∈ (hf y).toFinset, manifoldRamificationIndex f x) = N
```

with `N := degreeFiber f hf`.

This chip is purely structural — it just renames the conclusion of the
named obligation into the slot expected by the weighted-pullback
descent. No analytic content.

When the proof of `ramificationSumEqualsDegree_statement` lands
(follow-up chip with the Riemann-Hurwitz argument), this composer
becomes one rewrite away from producing an honest, unconditionally
discharged `Pic0.pullbackWeighted` for any non-constant ContMDiff `f`.

No `sorry`, no `axiom`. -/

@[expose] public section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

namespace ContMDiff

namespace Owed.degree

universe u v

/-- **Bridge: ramification-sum identity → constant-total-weight slot.**

The named identity `∀ y, ∑ x ∈ fibre y, manifoldRamificationIndex f x =
degreeFiber f hf` is exactly the slot that
`Div.fiberSumWeighted_mem_Div0_of_const_total_weight` requires, with
`N := degreeFiber f hf` and `e := manifoldRamificationIndex f`. -/
lemma hN_total_of_ramificationSumEqualsDegree
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_rsum : ramificationSumEqualsDegree_statement X Y)
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) :
    ∀ y : Y,
      (∑ x ∈ (fibres_finite_statement_holds_unconditional f hf hnc y).toFinset,
        JacobianChallenge.Manifold.manifoldRamificationIndex f x : ℕ)
        = JacobianChallenge.ContMDiff.degreeFiber f hf := by
  intro y
  exact h_rsum f hf hnc y

end Owed.degree

end ContMDiff

end JacobianChallenge
