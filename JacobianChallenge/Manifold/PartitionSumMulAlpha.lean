/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PartitionOfUnitySubordinateToCover

/-! # Partition-of-unity sum times `α`

Lifts Sub-chip 5.2's `sum_rhoC_eq_one` (`∑ᶠ i, P.rhoC i y = 1`) to
the pointwise identity

```
∑ i : {x // x ∈ cover.basePoints}, ((P.rhoC i) * α) y = α y
```

via `Finset.sum_mul` (right-distributivity of `*` over `Finset.sum`).
The finite-sum form is what Sub-chip 5.6's eventual manifold identity
sum needs to match.

The trivial computation goes:

```
∑ i, ((P.rhoC i) * α) y = ∑ i, (P.rhoC i)(y) * α y
                       = (∑ i, (P.rhoC i)(y)) * α y
                       = 1 * α y
                       = α y.
```

## Main result

* `sum_rhoC_mul_α_eq_α` — pointwise identity.

No `sorry`, no `axiom`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold Topology

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℝ, ℂ) ⊤ X]

/-- **Pointwise partition-of-unity identity** for `(P.rhoC i) * α`:
`∑ i, (P.rhoC i)(y) * α(y) = α(y)`. Reduces to Sub-chip 5.2's
`sum_rhoC_eq_one` via `Finset.sum_mul` (right-distributivity). -/
theorem sum_rhoC_mul_α_eq_α
    {cover : FiniteChartCover X}
    (P : FiniteChartCoverPartition cover) (α : X → ℂ) (y : X) :
    ∑ i : {x : X // x ∈ cover.basePoints}, ((P.rhoC i) * α) y = α y := by
  classical
  -- Rewrite (P.rhoC i * α) y = P.rhoC i y * α y pointwise (Pi.mul_apply).
  have h_pointwise :
      ∀ i : {x : X // x ∈ cover.basePoints},
        ((P.rhoC i) * α) y = P.rhoC i y * α y := fun _ => rfl
  -- Apply pointwise rewriting + Finset.sum_mul.
  calc ∑ i : {x : X // x ∈ cover.basePoints}, ((P.rhoC i) * α) y
      = ∑ i : {x : X // x ∈ cover.basePoints}, P.rhoC i y * α y :=
        Finset.sum_congr rfl (fun i _ => h_pointwise i)
    _ = (∑ i : {x : X // x ∈ cover.basePoints}, P.rhoC i y) * α y :=
        (Finset.sum_mul _ _ _).symm
    _ = (∑ᶠ i, P.rhoC i y) * α y := by
        rw [finsum_eq_sum_of_fintype]
    _ = (1 : ℂ) * α y := by rw [P.sum_rhoC_eq_one y]
    _ = α y := one_mul _

end JacobianChallenge

end
