/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import JacobianChallenge.Analysis.RealModelManifoldFromComplex

/-! # Smooth partition of unity subordinate to chart-source cover, for `ChartedSpace ℂ X`

Mathlib ships
`SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source` at
`Mathlib/Geometry/Manifold/PartitionOfUnity.lean:583`. That lemma takes
a `σ`-compact T2 manifold and produces a smooth partition of unity
indexed by the underlying type, subordinate to the family of
chart-source sets `(chartAt H y).source`.

This file specializes the lemma to **our setting** of a compact T2
`ChartedSpace ℂ X` carrying `IsManifold (𝓘(ℂ, ℂ)) ω X` (the holomorphic
manifold structure). The required `ℝ`-model instance
`IsManifold (𝓘(ℝ, ℂ)) ∞ X` is provided **unconditionally** by
`Analysis/RealModelManifoldFromComplex.lean` (closes the ℂ→ℝ ContDiff
diamond via the `set_option backward.isDefEq.respectTransparency
false` workaround).

## Headline

```
theorem exists_smoothPartitionOfUnity_subordinate_chartAt_source_complex
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] :
    ∃ f : SmoothPartitionOfUnity X 𝓘(ℝ, ℂ) X Set.univ,
      f.IsSubordinate (fun y : X => (chartAt ℂ y).source)
```

**Unconditional** — no extra hypothesis on the ℝ-model.

No `sorry`, no `axiom`. -/

open scoped Manifold ContDiff Topology

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Smooth partition of unity subordinate to the chart-source cover.**

Unconditional on any compact T2 `ChartedSpace ℂ X` carrying the
holomorphic manifold structure. The required ℝ-model `IsManifold`
instance is derived from the complex one via the diamond-aware bridge
in `Analysis/RealModelManifoldFromComplex.lean`. -/
theorem exists_smoothPartitionOfUnity_subordinate_chartAt_source_complex :
    ∃ f : SmoothPartitionOfUnity X 𝓘(ℝ, ℂ) X (Set.univ : Set X),
      f.IsSubordinate (fun y : X => (chartAt ℂ y).source) :=
  SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source (I := 𝓘(ℝ, ℂ)) X

end JacobianChallenge
