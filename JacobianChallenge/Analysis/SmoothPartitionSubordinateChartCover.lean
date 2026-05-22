/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! # Smooth partition of unity subordinate to chart-source cover, for `ChartedSpace ℂ X`

Mathlib ships
`SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source` at
`Mathlib/Geometry/Manifold/PartitionOfUnity.lean:583`. That lemma takes
a `σ`-compact T2 manifold and produces a smooth partition of unity
indexed by the underlying type, subordinate to the family of
chart-source sets `(chartAt H y).source`.

This file specializes the lemma to **our setting** of a compact T2
`ChartedSpace ℂ X` (typically a compact connected complex 1-manifold).

## Model-field caveat

`SmoothPartitionOfUnity` is defined in mathlib only for `ℝ`-models
(`ModelWithCorners ℝ E H`), because the partition functions are
`ℝ`-valued and require `ℝ`-affine combinations. Our manifold instance
in tree is `IsManifold (𝓘(ℂ, ℂ)) ω X` (the holomorphic / `ℂ`-model
form). The `ℝ`-model form `IsManifold (𝓘(ℝ, ℂ)) ∞ X` is **not** an
automatic consequence at this mathlib pin: it requires a ℂ→ℝ smoothness
restriction that hits the known `IsScalarTower ℝ ℂ ℂ` diamond
(documented in `memory/feedback_jacobian_complex_real_diamond.md`).

This file therefore takes `[IsManifold (𝓘(ℝ, ℂ)) ∞ X]` as an
**additional hypothesis** rather than attempting the diamond
workaround. Downstream callers who can produce that instance — via
either an explicit bridge from `IsManifold 𝓘(ℂ) ω X` or a direct
ℝ-model construction on the specific `X` they care about (`RiemannSphere`,
`ℂ⧸L`, etc.) — get the partition of unity.

## Headline

```
theorem exists_smoothPartitionOfUnity_subordinate_chartAt_source_complex
    [IsManifold (𝓘(ℝ, ℂ)) ∞ X] :
    ∃ f : SmoothPartitionOfUnity X 𝓘(ℝ, ℂ) X Set.univ,
      f.IsSubordinate (fun y : X => (chartAt ℂ y).source)
```

No `sorry`, no `axiom`. -/

open scoped Manifold ContDiff Topology

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℝ, ℂ)) ∞ X]

/-- **Smooth partition of unity subordinate to the chart-source cover.**

Direct specialization of mathlib's
`SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source` to
`ChartedSpace ℂ X` with the `ℝ`-model `𝓘(ℝ, ℂ)`. The compactness
hypothesis gives σ-compactness via mathlib's instance graph; T2 is
explicit.

Conditional on the `ℝ`-model `IsManifold` instance — see the
file-level docstring for why this isn't derived from
`IsManifold 𝓘(ℂ) ω X` here. -/
theorem exists_smoothPartitionOfUnity_subordinate_chartAt_source_complex :
    ∃ f : SmoothPartitionOfUnity X 𝓘(ℝ, ℂ) X (Set.univ : Set X),
      f.IsSubordinate (fun y : X => (chartAt ℂ y).source) :=
  SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source (I := 𝓘(ℝ, ℂ)) X

end JacobianChallenge
