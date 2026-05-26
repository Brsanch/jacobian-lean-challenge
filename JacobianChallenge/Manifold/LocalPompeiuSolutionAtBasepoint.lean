/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalPompeiuSolutionManifoldIdentity

/-! # `v_i` at the construction basepoint `i.val`

The chart-transition factor in the per-i recovery identity
(`partialZBarManifold_localPompeiuSolutionGlobal_eq_α_mul_transition_on_support_rhoC`)
collapses to `1` at the construction basepoint `y = i.val`: the
"chart transition" `(chartAt ℂ i.val) ∘ (chartAt ℂ i.val).symm`
is the identity on `(chartAt ℂ i.val).target`, so its derivative
at `(chartAt ℂ i.val) i.val` is `1`, and `conj 1 = 1`.

This gives the clean basepoint identity

```
partialZBarManifold (localPompeiuSolutionGlobal P i α χ) i.val
  = (P.rhoC i * α) i.val
```

whenever `i.val ∈ Function.support (P.rhoC i)`. Useful for sanity
checks and as the "easy case" the eventual global identity reduces
to. The `i.val ∈ support (P.rhoC i)` hypothesis is innocuous: by
construction the partition is centered at the cover's base points,
and typically `P.rhoC i (i.val) > 0` for the partition functions
mathlib produces — but this isn't automatic from the abstract
`SmoothPartitionOfUnity.exists_isSubordinate` interface, so we
take it as a hypothesis.

## Main result

* `partialZBarManifold_localPompeiuSolutionGlobal_at_basepoint` — the
  basepoint identity.

No `sorry`, no `axiom`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff
open Set Function

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℝ, ℂ) ⊤ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  {cover : FiniteChartCover X}

/-- The chart "self-transition" `chart_i ∘ chart_i.symm` is the identity on
`chart_i.target`. Hence eventually equal to `id` at any point of
`chart_i.target`, including the chart image of `i.val`. -/
theorem chart_self_transition_eventuallyEq_id
    (i : {x : X // x ∈ cover.basePoints}) :
    ((chartAt ℂ i.val) ∘ (chartAt ℂ i.val).symm)
      =ᶠ[𝓝 ((chartAt ℂ i.val) i.val)] id := by
  -- chart_i.target is open, contains chart_i(i.val).
  have h_target_open : IsOpen (chartAt ℂ i.val).target :=
    (chartAt ℂ i.val).open_target
  have h_ival_in_target : (chartAt ℂ i.val) i.val ∈ (chartAt ℂ i.val).target :=
    (chartAt ℂ i.val).map_source (mem_chart_source ℂ i.val)
  filter_upwards [h_target_open.mem_nhds h_ival_in_target] with ζ hζ
  -- On chart.target, chart ∘ chart.symm = id.
  show (chartAt ℂ i.val) ((chartAt ℂ i.val).symm ζ) = ζ
  exact (chartAt ℂ i.val).right_inv hζ

/-- The "chart-self-transition factor" at the basepoint `i.val` equals
`1`: derivative of identity is `1`, and `conj 1 = 1`. -/
theorem chart_self_transition_factor_at_basepoint
    (i : {x : X // x ∈ cover.basePoints}) :
    (starRingEnd ℂ)
      (deriv ((chartAt ℂ i.val) ∘ (chartAt ℂ i.val).symm)
        ((chartAt ℂ i.val) i.val))
      = 1 := by
  rw [Filter.EventuallyEq.deriv_eq (chart_self_transition_eventuallyEq_id i)]
  rw [deriv_id]
  exact map_one (starRingEnd ℂ)

/-- **Basepoint recovery identity** for `v_i` at `y = i.val`: the chart-
transition factor collapses to `1`, giving the clean form

```
partialZBarManifold v_i (i.val) = (P.rhoC i * α) (i.val).
```

Composition of the combined per-i identity with the basepoint
collapse of the chart-transition factor. -/
theorem partialZBarManifold_localPompeiuSolutionGlobal_at_basepoint
    [CompactSpace X] (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints}) (α : X → ℂ)
    (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α)
    (χ : PartitionChartSourceCutoff P i)
    (hi : i.val ∈ Function.support (P.rhoC i)) :
    JacobianChallenge.partialZBarManifold
        (localPompeiuSolutionGlobal P i α χ) i.val
      = (P.rhoC i * α) i.val := by
  -- Combined per-i identity at y := i.val.
  have h_combined :=
    partialZBarManifold_localPompeiuSolutionGlobal_eq_α_mul_transition_on_support_rhoC
      P i α h_α χ hi
  -- Apply the basepoint collapse to the transition factor.
  rw [chart_self_transition_factor_at_basepoint i] at h_combined
  -- The identity becomes `partialZBarManifold v_i (i.val) * 1 = (P.rhoC i * α) i.val`.
  simpa using h_combined

end JacobianChallenge

end
