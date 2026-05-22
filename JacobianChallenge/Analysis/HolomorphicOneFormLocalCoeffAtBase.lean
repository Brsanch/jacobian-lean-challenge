/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormChartCoeff
import JacobianChallenge.Manifold.HolomorphicOneFormRealification
import JacobianChallenge.Topology.SubsingletonFromPrimitiveExistence

/-! # `localCoeff om y` at the chart image of `y` equals `(om.eval y) 1`

For `om : HolomorphicOneForm X` and `y : X`, the chart-`y` local
coefficient evaluated at the **chart image of `y` itself**
(`z₀ := (chartAt ℂ y) y`) simplifies dramatically: the `coordChange`
in the `cotangentBundleCore` is the identity for chart-to-itself
(`VectorBundleCore.coordChange_self`), so

```
localCoeff om y ((chartAt ℂ y) y) = (om.eval y) 1.
```

This is chip E.1 of the L²-positivity arc. It connects the chart-local
function `localCoeff om y : ℂ → ℂ` to the chart-free cotangent value
`om.eval y : ℂ →L[ℂ] ℂ`, evaluated at the standard tangent vector
`1 : ℂ`. Combined with the elementary fact that a nonzero continuous
ℂ-linear map `ℂ →L[ℂ] ℂ` is determined by its value at `1` and that
value is nonzero, this gives the existence half:

```
om ≠ 0 ⇒ ∃ y : X, localCoeff om y ((chartAt ℂ y) y) ≠ 0.
```

Combined with analyticity (chip from `HolomorphicOneFormChartCoeffOnTarget`),
the identity theorem then gives `localCoeff om y` nonzero on a
non-empty open subset of the chart target, and L² positivity follows.

This chip ships:
* `localCoeff_at_chartAt_self` — the explicit identity.
* `exists_localCoeff_at_chartAt_self_ne_zero_of_ne_zero` — the
  existence half, via `HolomorphicOneForm.eq_zero_iff_eval` (in tree).

No `sorry`, no `axiom`. -/

set_option linter.unusedSectionVars false

noncomputable section

open scoped Manifold ContDiff
open Bundle

namespace HolomorphicOneForm

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **At the chart image of the base point**, the local coefficient of
`om` in chart `y` reduces to `(om.eval y) 1`. -/
theorem localCoeff_at_chartAt_self (om : HolomorphicOneForm X) (y : X) :
    localCoeff om y ((chartAt ℂ y) y) = (om.eval y) 1 := by
  -- Unfold localCoeff.
  show ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
      (achart ℂ ((chartAt ℂ y).symm ((chartAt ℂ y) y)))
      (achart ℂ y) ((chartAt ℂ y).symm ((chartAt ℂ y) y))
      (om.toFun ((chartAt ℂ y).symm ((chartAt ℂ y) y)))) 1
    = (om.eval y) 1
  -- (chartAt ℂ y).symm ((chartAt ℂ y) y) = y by chart inverse-on-source.
  have h_symm : (chartAt ℂ y).symm ((chartAt ℂ y) y) = y := by
    exact (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
  rw [h_symm]
  -- coordChange (achart ℂ y) (achart ℂ y) y v = v by coordChange_self.
  have h_self_chart : y ∈ (cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ y) :=
    mem_chart_source ℂ y
  rw [(cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange_self
        (achart ℂ y) y h_self_chart (om.toFun y)]
  -- om.toFun y = om.eval y (definitional).
  rfl

/-- **Existence of a chart in which `localCoeff` is nonzero at the
chart image of the base point**, whenever `om ≠ 0`.

Uses `JacobianChallenge.HolomorphicOneForm.eq_zero_iff_eval_at_one`
(Topology/SubsingletonFromPrimitiveExistence) to extract a point `y`
where `om.eval y 1 ≠ 0`, then converts via `localCoeff_at_chartAt_self`
above. -/
theorem exists_localCoeff_at_chartAt_self_ne_zero_of_ne_zero
    (om : HolomorphicOneForm X) (h : om ≠ 0) :
    ∃ y : X, localCoeff om y ((chartAt ℂ y) y) ≠ 0 := by
  -- Use eq_zero_iff_eval_at_one to extract a point y with om.eval y 1 ≠ 0.
  have h_eval : ¬ (∀ x : X, om.eval x 1 = 0) := by
    intro h_all
    exact h ((JacobianChallenge.HolomorphicOneForm.eq_zero_iff_eval_at_one om).mpr h_all)
  obtain ⟨y, hy⟩ : ∃ x : X, om.eval x 1 ≠ 0 := by
    by_contra h_no
    apply h_eval
    intro x
    by_contra h_x
    exact h_no ⟨x, h_x⟩
  refine ⟨y, ?_⟩
  rw [localCoeff_at_chartAt_self]
  exact hy

end HolomorphicOneForm

end
