/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.HolomorphicOneFormGlobalSesquilinear
import JacobianChallenge.Analysis.HolomorphicOneFormChartLocalSesquilinearLinearity

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Linearity in the left argument of `globalPettersonHermitian`

Lifts the chart-local linearity (from
`HolomorphicOneFormChartLocalSesquilinearLinearity.lean`) to the
global partition-of-unity Petersson Hermitian form.

## What ships

* `globalPettersonHermitian_smul_left` — unconditional ℂ-linearity in
  the left argument.
* `globalPettersonHermitian_add_left_of_subordinate` — additivity in
  the left argument, conditional on PoU subordinacy to chart-sources
  (which discharges the chart-local integrability hypotheses
  automatically).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory ENNReal NNReal Complex Set

namespace HolomorphicOneForm

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- The support of `y ↦ chartLocalSesquilinear (... y ...)` is finite
on a compact `X` with a subordinate smooth PoU `f`. -/
private lemma chartLocalSesquilinear_finsupp_term
    (om eta : HolomorphicOneForm X)
    (f : SmoothPartitionOfUnity X 𝓘(ℝ, ℂ) X (Set.univ : Set X)) :
    Set.Finite (Function.support
      (fun y : X => chartLocalSesquilinear om eta y (fun x => f.toFun y x))) := by
  have h_lf : LocallyFinite (fun y : X => Function.support (fun x => (f y) x)) :=
    f.locallyFinite
  have h_finite_active :
      {y : X | (Function.support (fun x => (f y) x)).Nonempty}.Finite :=
    h_lf.finite_nonempty_of_compact
  refine h_finite_active.subset ?_
  intro y hy
  by_contra h_empty
  apply hy
  have h_not_nonempty : ¬ (Function.support (fun x => (f y) x)).Nonempty := h_empty
  have h_support_empty : Function.support (fun x => (f y) x) = ∅ := by
    rw [Set.not_nonempty_iff_eq_empty] at h_not_nonempty
    exact h_not_nonempty
  have h_fy_zero : (fun x => (f y) x) = fun _ => 0 := by
    rw [Function.support_eq_empty_iff] at h_support_empty
    exact h_support_empty
  show chartLocalSesquilinear om eta y (fun x => (f y) x) = 0
  unfold chartLocalSesquilinear
  have h_zero : ∀ z : ℂ,
      ((fun x => (f y) x) ((chartAt ℂ y).symm z) : ℂ)
        * localCoeff om y z * (starRingEnd ℂ) (localCoeff eta y z) = 0 := by
    intro z
    rw [h_fy_zero]
    simp
  simp [h_zero]

/-- **ℂ-linearity in the left argument** of the global Petersson
Hermitian form. Unconditional. -/
theorem globalPettersonHermitian_smul_left
    (c : ℂ) (om eta : HolomorphicOneForm X)
    (f : SmoothPartitionOfUnity X 𝓘(ℝ, ℂ) X (Set.univ : Set X)) :
    globalPettersonHermitian (c • om) eta f
      = c * globalPettersonHermitian om eta f := by
  unfold globalPettersonHermitian
  -- ∑ᶠ y, chartLocalSesquilinear (c • om) eta y (f y) = c * ∑ᶠ y, chartLocalSesquilinear om eta y (f y).
  have h_pt : ∀ y : X,
      chartLocalSesquilinear (c • om) eta y (fun x => f.toFun y x)
      = c * chartLocalSesquilinear om eta y (fun x => f.toFun y x) := by
    intro y
    exact chartLocalSesquilinear_smul_left c om eta y _
  rw [show (fun y : X => chartLocalSesquilinear (c • om) eta y (fun x => f.toFun y x))
      = (fun y : X => c * chartLocalSesquilinear om eta y (fun x => f.toFun y x))
      from funext h_pt]
  -- Pull c out of the finsum via mul_finsum.
  exact (mul_finsum
    (fun y : X => chartLocalSesquilinear om eta y (fun x => f.toFun y x)) c).symm

/-- **Additivity in the left argument** of the global Petersson
Hermitian form, conditional on PoU subordinacy to chart-sources. -/
theorem globalPettersonHermitian_add_left_of_subordinate
    (om₁ om₂ eta : HolomorphicOneForm X)
    (f : SmoothPartitionOfUnity X 𝓘(ℝ, ℂ) X (Set.univ : Set X))
    (hf_subord : f.IsSubordinate (fun y : X => (chartAt ℂ y).source)) :
    globalPettersonHermitian (om₁ + om₂) eta f
      = globalPettersonHermitian om₁ eta f + globalPettersonHermitian om₂ eta f := by
  unfold globalPettersonHermitian
  -- Pointwise per-chart linearity, using integrability from subordinacy.
  have h_pt : ∀ y : X,
      chartLocalSesquilinear (om₁ + om₂) eta y (fun x => f.toFun y x)
      = chartLocalSesquilinear om₁ eta y (fun x => f.toFun y x)
        + chartLocalSesquilinear om₂ eta y (fun x => f.toFun y x) := by
    intro y
    have h_tsupp_sub : tsupport (fun x => f.toFun y x) ⊆ (chartAt ℂ y).source :=
      hf_subord y
    have h_cont : Continuous (fun x => f.toFun y x) :=
      (f.toFun y).contMDiff.continuous
    have h_int₁ := chartLocalSesquilinearIntegrand_integrableOn_target_of_subordinate
      om₁ eta y h_cont h_tsupp_sub
    have h_int₂ := chartLocalSesquilinearIntegrand_integrableOn_target_of_subordinate
      om₂ eta y h_cont h_tsupp_sub
    exact chartLocalSesquilinear_add_left_of_integrableOn om₁ om₂ eta y _ h_int₁ h_int₂
  rw [show (fun y : X => chartLocalSesquilinear (om₁ + om₂) eta y (fun x => f.toFun y x))
      = (fun y : X =>
          chartLocalSesquilinear om₁ eta y (fun x => f.toFun y x)
            + chartLocalSesquilinear om₂ eta y (fun x => f.toFun y x))
      from funext h_pt]
  -- ∑ᶠ y, (a y + b y) = ∑ᶠ y, a y + ∑ᶠ y, b y, when both supports finite.
  exact finsum_add_distrib
    (chartLocalSesquilinear_finsupp_term om₁ eta f)
    (chartLocalSesquilinear_finsupp_term om₂ eta f)

end HolomorphicOneForm

end
