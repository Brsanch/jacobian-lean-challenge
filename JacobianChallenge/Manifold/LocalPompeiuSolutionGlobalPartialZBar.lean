/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalPompeiuSolutionGlobal
import JacobianChallenge.Manifold.PartialZBarManifold

/-! # Chip 5.4c — `∂̄_man v_i` agrees with the cutoff-free version on `supp(P.rhoC i)`

The chart-source cutoff `χ_i` from Sub-chip 5.4a equals `1` on
`tsupport (P.rhoC i)`. In particular it equals `1` on the open subset
`support (P.rhoC i)` (which is open whenever `P.rhoC i` is continuous,
as it is here). On a neighborhood of any `y ∈ support (P.rhoC i)`,
the global Pompeiu solution `v_i` coincides with the cutoff-free
version

```
PKchart i α y := pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))
                               ((chartAt ℂ i.val) y),
```

and `partialZBarManifold` is local (depends only on values in a
neighborhood, via `Filter.EventuallyEq.fderiv_eq`). Hence

```
partialZBarManifold v_i y = partialZBarManifold (PKchart i α) y
```

for `y ∈ support (P.rhoC i)`. This is the "easy" first reduction in
Sub-chip 5.4c's Leibniz argument; the remaining step (computing the
chart-pullback `partialZBarManifold (PKchart i α) y` in terms of α via
Chip 4's chart-transition factor) lands in a follow-up sub-chip.

## Main results

* `partialZBarManifold_eventuallyEq_congr` — `partialZBarManifold` only
  depends on values in a neighborhood (`Filter.EventuallyEq` ⇒ equal).
* `localPompeiuSolutionGlobal_eventuallyEq_PKchart_on_support_rhoC` —
  on a neighborhood of any `y ∈ support (P.rhoC i)`, `v_i` equals
  the cutoff-free Pompeiu solution.
* `partialZBarManifold_localPompeiuSolutionGlobal_eq_PKchart_on_support_rhoC` —
  the headline: ∂̄_man v_i = ∂̄_man (PKchart) on supp(P.rhoC i).

No `sorry`, no `axiom`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff
open Set Function Filter
open JacobianChallenge.PompeiuKernel

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℝ, ℂ) ⊤ X]

/-! ## ∂̄_man depends only on the germ -/

/-- **`partialZBarManifold` respects eventual equality.** If `f =ᶠ[𝓝 y] g`,
then their manifold-side antiholomorphic derivatives at `y` are equal.
This is a direct consequence of the analogous fact for `partialZBar`
(via `Filter.EventuallyEq.fderiv_eq`), applied to the chart-pullbacks
`f ∘ extChartAt.symm` and `g ∘ extChartAt.symm`, whose eventual
equality at `extChartAt y` follows from continuity of `extChartAt.symm`. -/
theorem partialZBarManifold_eventuallyEq_congr
    {f g : X → ℂ} {y : X} (h : f =ᶠ[𝓝 y] g) :
    partialZBarManifold f y = partialZBarManifold g y := by
  unfold partialZBarManifold
  -- extChartAt.symm is continuous at extChartAt y (mathlib lemma).
  have h_cts : ContinuousAt (extChartAt 𝓘(ℂ, ℂ) y).symm
      ((extChartAt 𝓘(ℂ, ℂ) y) y) :=
    continuousAt_extChartAt_symm (I := (𝓘(ℂ, ℂ))) y
  -- chart_y maps chart_y(y) back to y by left_inv.
  have h_symm_apply :
      (extChartAt 𝓘(ℂ, ℂ) y).symm ((extChartAt 𝓘(ℂ, ℂ) y) y) = y :=
    extChartAt_to_inv y
  -- Tendsto extChartAt.symm at chart_y(y) goes to nhds y.
  have h_tendsto :
      Filter.Tendsto (extChartAt 𝓘(ℂ, ℂ) y).symm
        (𝓝 ((extChartAt 𝓘(ℂ, ℂ) y) y)) (𝓝 y) := by
    have := h_cts
    rwa [ContinuousAt, h_symm_apply] at this
  -- Compose with the original eventual equality.
  have h_comp : (f ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm)
      =ᶠ[𝓝 ((extChartAt 𝓘(ℂ, ℂ) y) y)]
      (g ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm) :=
    h.comp_tendsto h_tendsto
  -- partialZBar depends only on the germ via fderiv_eq.
  unfold partialZBar
  rw [Filter.EventuallyEq.fderiv_eq h_comp]

/-! ## Local coincidence of v_i with the cutoff-free version on `supp(P.rhoC i)` -/

variable {cover : FiniteChartCover X}

/-- The **cutoff-free Pompeiu solution** (no χ_i factor). -/
def chartPompeiuSolution
    (i : {x : X // x ∈ cover.basePoints})
    (P : FiniteChartCoverPartition cover) (α : X → ℂ) : X → ℂ :=
  fun y => pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))
                         ((chartAt ℂ i.val) y)

/-- On the open set `support (P.rhoC i)` (open because `P.rhoC i` is
continuous), the cutoff `χ_i` equals 1. Hence `v_i` (which is
`χ_i · chartPompeiuSolution`) coincides with `chartPompeiuSolution`
on a neighborhood of any `y ∈ support (P.rhoC i)`. -/
theorem localPompeiuSolutionGlobal_eventuallyEq_chartPompeiuSolution_on_support_rhoC
    (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints})
    (α : X → ℂ)
    (χ : PartitionChartSourceCutoff P i)
    {y : X} (hy : y ∈ Function.support (P.rhoC i)) :
    (localPompeiuSolutionGlobal P i α χ)
      =ᶠ[𝓝 y] (chartPompeiuSolution i P α) := by
  -- support (P.rhoC i) is open: support of a continuous function is open
  -- (support = preimage of {0}ᶜ, which is open under continuity).
  have h_rhoC_cont : Continuous (P.rhoC i) := P.rhoC_continuous i
  have h_support_eq : Function.support (P.rhoC i) = (P.rhoC i) ⁻¹' {0}ᶜ := by
    ext z; simp [Function.mem_support]
  have h_support_open : IsOpen (Function.support (P.rhoC i)) := by
    rw [h_support_eq]
    exact (isClosed_singleton.preimage h_rhoC_cont).isOpen_compl
  -- On this open neighborhood of y, χ_i = 1 (by 5.4a + subset_tsupport).
  have h_chi_eqOne_on : Set.EqOn χ.toFun 1 (Function.support (P.rhoC i)) :=
    χ.eqOne_on_support_rhoC
  -- filter_upwards on this open neighborhood.
  filter_upwards [h_support_open.mem_nhds hy] with z hz
  -- z ∈ support (P.rhoC i) ⇒ χ z = 1 ⇒ v_i z = chartPompeiuSolution.
  unfold localPompeiuSolutionGlobal chartPompeiuSolution
  have h_chi_z : χ.toFun z = 1 := h_chi_eqOne_on hz
  rw [h_chi_z]
  simp

/-- **Headline `5.4c-prep`.** On `support (P.rhoC i)`, the manifold-side
∂̄ of `v_i` equals the manifold-side ∂̄ of the cutoff-free
`chartPompeiuSolution`. Combines the local coincidence above with
`partialZBarManifold_eventuallyEq_congr`. -/
theorem partialZBarManifold_localPompeiuSolutionGlobal_eq_chartPompeiuSolution_on_support_rhoC
    (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints})
    (α : X → ℂ)
    (χ : PartitionChartSourceCutoff P i)
    {y : X} (hy : y ∈ Function.support (P.rhoC i)) :
    partialZBarManifold (localPompeiuSolutionGlobal P i α χ) y
      = partialZBarManifold (chartPompeiuSolution i P α) y := by
  exact partialZBarManifold_eventuallyEq_congr
    (localPompeiuSolutionGlobal_eventuallyEq_chartPompeiuSolution_on_support_rhoC
      P i α χ hy)

end JacobianChallenge

end
