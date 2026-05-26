/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalPompeiuSolutionGlobalPartialZBar

/-! # `∂̄_man v_i = 0` off `tsupport χ_i`

Trivial vanishing case for the manifold-side `∂̄` of the local
Pompeiu solution: outside `tsupport χ_i` (an open neighborhood of
`(tsupport χ_i)ᶜ`), the cutoff `χ_i` is identically zero, hence
`v_i` is identically zero on that neighborhood, hence its
manifold-side `∂̄` vanishes.

Complements Sub-chip 5.4c-prep / 5.4c-final's per-i recovery identity
(which gives `∂̄_man v_i y · conj(transition factor) = (P.rhoC i * α)(y)`
on `support (P.rhoC i)`).

Combined picture: the sum `∑ i, partialZBarManifold v_i y` decomposes
into three regimes of `y`:

* `y ∈ support (P.rhoC i)`: recovery identity (modulo transition
  factor).
* `y ∈ tsupport χ_i \ support (P.rhoC i)`: cutoff-annulus error term
  (handled by Sub-chip 5.5 Behnke-Stein spreading).
* `y ∉ tsupport χ_i`: vanishes (this file).

## Main result

* `partialZBarManifold_localPompeiuSolutionGlobal_eq_zero_off_tsupport_chi`

No `sorry`, no `axiom`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold Topology
open Set Function Filter

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℝ, ℂ) ⊤ X] {cover : FiniteChartCover X}

/-- On a neighborhood of any `y ∉ tsupport χ.toFun`, the local
Pompeiu solution `v_i` is identically zero. -/
theorem localPompeiuSolutionGlobal_eventuallyEq_zero_off_tsupport_chi
    (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints}) (α : X → ℂ)
    (χ : PartitionChartSourceCutoff P i)
    {y : X} (hy : y ∉ tsupport χ.toFun) :
    (localPompeiuSolutionGlobal P i α χ) =ᶠ[𝓝 y] (fun _ : X => (0 : ℂ)) := by
  have h_tsupport_closed : IsClosed (tsupport χ.toFun) := isClosed_tsupport _
  have h_compl_open : IsOpen (tsupport χ.toFun)ᶜ :=
    h_tsupport_closed.isOpen_compl
  have h_nhd : (tsupport χ.toFun)ᶜ ∈ 𝓝 y := h_compl_open.mem_nhds hy
  filter_upwards [h_nhd] with z hz_compl
  -- z ∉ tsupport χ ⇒ z ∉ support χ ⇒ χ z = 0 ⇒ v_i z = 0.
  have h_chi_z_zero : χ.toFun z = 0 := by
    have h_z_not_supp : z ∉ Function.support χ.toFun :=
      fun h => hz_compl (subset_tsupport _ h)
    exact Function.notMem_support.mp h_z_not_supp
  unfold localPompeiuSolutionGlobal
  simp [h_chi_z_zero]

/-- **Trivial vanishing case.** For `y ∉ tsupport χ.toFun`, the
manifold-side `∂̄` of `v_i` vanishes: `v_i` is identically zero on
an open neighborhood of `y`, so by germ-dependence
(`partialZBarManifold_eventuallyEq_congr`, Sub-chip 5.4c-prep) the
manifold `∂̄` equals `partialZBarManifold 0 = 0`. -/
theorem partialZBarManifold_localPompeiuSolutionGlobal_eq_zero_off_tsupport_chi
    (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints}) (α : X → ℂ)
    (χ : PartitionChartSourceCutoff P i)
    {y : X} (hy : y ∉ tsupport χ.toFun) :
    JacobianChallenge.partialZBarManifold
        (localPompeiuSolutionGlobal P i α χ) y = 0 := by
  have h_evEq :
      (localPompeiuSolutionGlobal P i α χ)
        =ᶠ[𝓝 y] (fun _ : X => (0 : ℂ)) :=
    localPompeiuSolutionGlobal_eventuallyEq_zero_off_tsupport_chi P i α χ hy
  rw [partialZBarManifold_eventuallyEq_congr h_evEq]
  exact partialZBarManifold_const 0 y

end JacobianChallenge

end
