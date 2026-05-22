/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.HolomorphicOneFormGlobalSesquilinearPositive
import JacobianChallenge.Analysis.HolomorphicOneFormChartLocalL2SqWeightedFinite

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Chip S.8 — strict positivity of the Hermitian diagonal (UNCONDITIONAL)

Composes:

* `globalPettersonHermitian_diagonal_re_pos_of_ne_zero_of_finite` (the
  conditional headline from
  `Topology/HolomorphicOneFormGlobalSesquilinearPositive.lean`).
* `chartLocalL2SqWeighted_lt_top_of_subordinate` (the finiteness atom
  shipped in
  `Topology/HolomorphicOneFormChartLocalL2SqWeightedFinite.lean`).

The result is the **unconditional** strict positivity at the diagonal
of the global Petersson Hermitian form: for every nonzero holomorphic
1-form `om` on a compact connected complex 1-manifold `X` and every
smooth partition of unity subordinate to the chart-source cover,

```
0 < (globalPettersonHermitian om om f).re
```

This is the L²-positivity-side analytic ingredient of
`RiemannSecondRelationPositivity` (`HodgeRiemannBridgeHypothesis`
chain) on C3's path to closing items 5/11/12/13.

Combined with S.3 (`.im = 0`) and S.6 (`.re ≥ 0`), the global
Petersson Hermitian form is **positive-definite at the diagonal**
without any remaining named hypothesis.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory ENNReal NNReal Complex

namespace HolomorphicOneForm

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Chip S.8: strict positivity at the diagonal of the global
Petersson Hermitian form for nonzero forms (UNCONDITIONAL).** -/
theorem globalPettersonHermitian_diagonal_re_pos_of_ne_zero
    (om : HolomorphicOneForm X) (h_ne : om ≠ 0)
    (f : SmoothPartitionOfUnity X 𝓘(ℝ, ℂ) X (Set.univ : Set X))
    (hf_subord : f.IsSubordinate (fun y : X => (chartAt ℂ y).source)) :
    0 < (globalPettersonHermitian om om f).re :=
  globalPettersonHermitian_diagonal_re_pos_of_ne_zero_of_finite om h_ne f hf_subord
    (fun y => chartLocalL2SqWeighted_lt_top_of_subordinate om y f hf_subord)

end HolomorphicOneForm

end
