/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.HolomorphicOneFormGlobalSesquilinearLinearity
import JacobianChallenge.Analysis.HolomorphicOneFormGlobalSesquilinearPositiveUnconditional
import JacobianChallenge.Analysis.SmoothPartitionSubordinateChartCover
import JacobianChallenge.Manifold.HodgeInnerProductHypothesis

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # `HodgeInnerProductHypothesis X` UNCONDITIONAL via the global Petersson form

The headline chip closing item #2 of the outstanding-content list:
package `globalPettersonHermitian` (for a subordinate PoU chosen
via `Classical.choose`) as a `HermitianOnHolomorphicOneForm X`
structure, prove it is `IsPositiveDefinite`, and discharge
`HodgeInnerProductHypothesis X` unconditionally on every compact
connected complex 1-manifold.

## Composition

Composes the arc-S chain shipped this session:
* S.2: zero-on-zero + Hermitian symmetry.
* S.3: diagonal imaginary part is zero.
* S.6: diagonal real part is nonneg.
* S.8 (just landed): diagonal real part is strictly positive for nonzero forms.
* Linearity (this session): `globalPettersonHermitian_smul_left`
  (unconditional ℂ-linearity) + `globalPettersonHermitian_add_left_of_subordinate`
  (additivity under subordinacy).

Plus the unconditional existence of a smooth PoU subordinate to the
chart-source cover (`exists_smoothPartitionOfUnity_subordinate_chartAt_source_complex`,
in tree, uses the ℂ→ℝ ContDiff diamond closure).

## What ships

* `globalPettersonHermitianForm` — packaged `HermitianOnHolomorphicOneForm X`.
* `globalPettersonHermitianForm_isPositiveDefinite` — positivity.
* `hodgeInnerProductHypothesis_holds` — **unconditional** discharge of
  the open named hypothesis.

This is the **L²-positivity-side analytic content** of
`RiemannSecondRelationPositivity` on C3's path to closing items
5/11/12/13. The bridge to the period-matrix Hermitian form
(`HodgeRiemannBridgeHypothesis`) remains open content (item #3 of
the outstanding list), but the Hodge-side input to that bridge is
now unconditional.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory ENNReal NNReal Complex Set
open HolomorphicOneForm

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **A canonical subordinate PoU on `X`** (via classical choice from
`exists_smoothPartitionOfUnity_subordinate_chartAt_source_complex`). -/
noncomputable def chartSourceSubordinatePoU :
    SmoothPartitionOfUnity X 𝓘(ℝ, ℂ) X (Set.univ : Set X) :=
  Classical.choose (exists_smoothPartitionOfUnity_subordinate_chartAt_source_complex X)

lemma chartSourceSubordinatePoU_isSubordinate :
    (chartSourceSubordinatePoU X).IsSubordinate
      (fun y : X => (chartAt ℂ y).source) :=
  Classical.choose_spec (exists_smoothPartitionOfUnity_subordinate_chartAt_source_complex X)

/-- **The packaged global Petersson Hermitian form on `HolomorphicOneForm X`.**

`toFun om eta := globalPettersonHermitian om eta (chartSourceSubordinatePoU X)`. -/
noncomputable def globalPettersonHermitianForm : HermitianOnHolomorphicOneForm X where
  toFun := fun om eta =>
    HolomorphicOneForm.globalPettersonHermitian om eta (chartSourceSubordinatePoU X)
  map_zero_left := fun eta =>
    HolomorphicOneForm.globalPettersonHermitian_zero_left eta (chartSourceSubordinatePoU X)
  map_add_left := fun om₁ om₂ eta =>
    HolomorphicOneForm.globalPettersonHermitian_add_left_of_subordinate om₁ om₂ eta
      (chartSourceSubordinatePoU X)
      (chartSourceSubordinatePoU_isSubordinate X)
  map_smul_left := fun c om eta =>
    HolomorphicOneForm.globalPettersonHermitian_smul_left c om eta (chartSourceSubordinatePoU X)
  conjSymm := fun om eta =>
    HolomorphicOneForm.globalPettersonHermitian_hermitian om eta (chartSourceSubordinatePoU X)

/-- **`globalPettersonHermitianForm` is `IsPositiveDefinite`.**

* Diagonal real and nonneg: from arc S's S.3 + S.6.
* Non-degeneracy: from S.8 (strict positivity for nonzero forms). -/
theorem globalPettersonHermitianForm_isPositiveDefinite :
    (globalPettersonHermitianForm X).IsPositiveDefinite := by
  refine ⟨?_, ?_⟩
  · -- ∀ om, (toFun om om).im = 0 ∧ 0 ≤ (toFun om om).re.
    intro om
    refine ⟨?_, ?_⟩
    · -- .im = 0 by S.3.
      exact HolomorphicOneForm.globalPettersonHermitian_diagonal_im om (chartSourceSubordinatePoU X)
    · -- .re ≥ 0 by S.6.
      exact HolomorphicOneForm.globalPettersonHermitian_diagonal_re_nonneg om
        (chartSourceSubordinatePoU X)
  · -- ∀ om, toFun om om = 0 → om = 0.
    -- Contrapositive: om ≠ 0 → toFun om om ≠ 0.
    intro om h_zero
    by_contra h_ne
    -- Apply S.8 to get .re > 0.
    have h_re_pos :
        0 < (HolomorphicOneForm.globalPettersonHermitian om om
              (chartSourceSubordinatePoU X)).re :=
      HolomorphicOneForm.globalPettersonHermitian_diagonal_re_pos_of_ne_zero
        om h_ne (chartSourceSubordinatePoU X) (chartSourceSubordinatePoU_isSubordinate X)
    -- But h_zero says the form is 0, so .re = 0, contradiction.
    have h_re_zero :
        (HolomorphicOneForm.globalPettersonHermitian om om
          (chartSourceSubordinatePoU X)).re = 0 := by
      rw [show HolomorphicOneForm.globalPettersonHermitian om om
            (chartSourceSubordinatePoU X)
          = (globalPettersonHermitianForm X).toFun om om from rfl, h_zero]
      simp
    rw [h_re_zero] at h_re_pos
    exact lt_irrefl _ h_re_pos

/-- **`HodgeInnerProductHypothesis X` is UNCONDITIONAL** on every
compact connected complex 1-manifold. -/
theorem hodgeInnerProductHypothesis_holds : HodgeInnerProductHypothesis X :=
  ⟨globalPettersonHermitianForm X, globalPettersonHermitianForm_isPositiveDefinite X⟩

end JacobianChallenge

end
