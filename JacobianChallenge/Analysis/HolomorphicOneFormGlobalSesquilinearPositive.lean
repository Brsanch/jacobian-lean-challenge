/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.HolomorphicOneFormGlobalL2SqPositive
import JacobianChallenge.Analysis.HolomorphicOneFormGlobalSesquilinear
import JacobianChallenge.Analysis.HolomorphicOneFormChartLocalSesquilinearL2SqBridge

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Strict positivity at the diagonal of the global Petersson Hermitian form

**Chip S.8** of arc S. Composes:

* `globalPettersonL2Sq_pos_of_ne_zero` (in tree, arc E.4) — for nonzero
  `om : HolomorphicOneForm X` on a compact connected complex 1-manifold,
  the global L²-square seminorm is strictly positive.
* `chartLocalSesquilinear_diagonal_re_eq_chartLocalL2SqWeighted_toReal`
  (in tree, the bridge chip just shipped) — chart-local Hermitian
  diagonal `.re` equals the chart-local L²-square weighted `.toReal`.
* `globalPettersonHermitian_diagonal_re_eq_finsum` (in tree, S.7') —
  global Hermitian diagonal `.re` distributes as a finsum.
* `globalPettersonHermitian_diagonal_re_nonneg` (in tree, S.6) — every
  chart-local term is `.re`-nonneg.

The argument: from `globalPettersonL2Sq > 0` extract a witness
`y₀ : X` with the chart-local L²-square `> 0`. Given a finiteness
hypothesis at `y₀`, the chart-local L²-square's `.toReal > 0`. Via the
bridge, the chart-local Hermitian diagonal `.re > 0` at `y₀`. By S.7' +
S.6 + `single_le_finsum`, the global `.re > 0`.

## Conditional on finiteness

This chip takes finiteness as a hypothesis:
`∀ y, chartLocalL2SqWeighted om y (f y) < ⊤`. The finiteness atom is
classical content (compact-support PoU + bounded chart-local form ⇒
bounded integrand on compact ⇒ finite L²-square) and is itself a
named-hypothesis target for a follow-up chip.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory ENNReal NNReal Complex

namespace HolomorphicOneForm

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Headline (conditional): strict positivity at the diagonal of the
global Petersson Hermitian form for nonzero forms.**

Conditional on chart-local L²-square finiteness, the real part of the
global Petersson Hermitian form's diagonal is strictly positive for
every nonzero holomorphic 1-form. -/
theorem globalPettersonHermitian_diagonal_re_pos_of_ne_zero_of_finite
    (om : HolomorphicOneForm X) (h_ne : om ≠ 0)
    (f : SmoothPartitionOfUnity X 𝓘(ℝ, ℂ) X (Set.univ : Set X))
    (hf_subord : f.IsSubordinate (fun y : X => (chartAt ℂ y).source))
    (h_finite : ∀ y : X,
        chartLocalL2SqWeighted om y (fun x => f.toFun y x) < ⊤) :
    0 < (globalPettersonHermitian om om f).re := by
  -- Step 1: by arc E.4, global L²-square is strictly positive.
  have h_globL2_pos : 0 < globalPettersonL2Sq om f :=
    globalPettersonL2Sq_pos_of_ne_zero om h_ne f hf_subord
  -- Step 2: hence the finsum representation is positive,
  -- so SOME chart-local L²-square term is positive.
  -- globalPettersonL2Sq om f = ∑ᶠ y, chartLocalL2SqWeighted om y (f y).
  have h_finsum_pos : 0 < ∑ᶠ y : X, chartLocalL2SqWeighted om y (fun x => f.toFun y x) := by
    unfold globalPettersonL2Sq at h_globL2_pos
    exact h_globL2_pos
  -- A nonneg finsum > 0 must have a strictly positive term (otherwise it's 0).
  have h_exists_pos : ∃ y₀ : X,
      0 < chartLocalL2SqWeighted om y₀ (fun x => f.toFun y₀ x) := by
    by_contra h_no
    push_neg at h_no
    -- h_no : ∀ y, chartLocalL2SqWeighted om y (f y) ≤ 0, hence = 0 in ENNReal.
    have h_all_zero : ∀ y : X,
        chartLocalL2SqWeighted om y (fun x => f.toFun y x) = 0 := by
      intro y
      exact le_antisymm (h_no y) (zero_le _)
    -- Hence the finsum is 0.
    have h_finsum_zero :
        ∑ᶠ y : X, chartLocalL2SqWeighted om y (fun x => f.toFun y x) = 0 := by
      apply finsum_eq_zero_of_forall_eq_zero
      exact h_all_zero
    rw [h_finsum_zero] at h_finsum_pos
    exact lt_irrefl _ h_finsum_pos
  obtain ⟨y₀, hy₀_pos⟩ := h_exists_pos
  -- Step 3: combine with finiteness ⇒ .toReal > 0.
  have hy₀_finite : chartLocalL2SqWeighted om y₀ (fun x => f.toFun y₀ x) < ⊤ :=
    h_finite y₀
  have hy₀_toReal_pos :
      0 < (chartLocalL2SqWeighted om y₀ (fun x => f.toFun y₀ x)).toReal := by
    rw [ENNReal.toReal_pos_iff]
    exact ⟨hy₀_pos, hy₀_finite⟩
  -- Step 4: via the bridge, the chart-local Hermitian .re at y₀ is positive.
  have hy₀_re_pos :
      0 < (chartLocalSesquilinear om om y₀ (fun x => f.toFun y₀ x)).re := by
    rw [chartLocalSesquilinear_diagonal_re_eq_chartLocalL2SqWeighted_toReal
        om y₀ (χ := fun x => f.toFun y₀ x) (f.nonneg y₀)
        (f.toFun y₀).contMDiff.continuous]
    exact hy₀_toReal_pos
  -- Step 5: lift to global via S.7' + S.6 + single_le_finsum.
  rw [globalPettersonHermitian_diagonal_re_eq_finsum]
  -- Finsum support is finite (same argument as in S.6 / globalPettersonL2Sq_pos).
  have h_finsupp_re :
      Set.Finite (Function.support
        (fun y : X =>
          (chartLocalSesquilinear om om y (fun x => f.toFun y x)).re)) := by
    -- Support of (chart-local .re) ⊆ support of partition.
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
    -- f y ≡ 0 ⇒ chartLocalSesquilinear is 0 ⇒ .re is 0.
    show (chartLocalSesquilinear om om y (fun x => (f y) x)).re = 0
    unfold chartLocalSesquilinear
    have h_zero : ∀ z : ℂ,
        ((fun x => (f y) x) ((chartAt ℂ y).symm z) : ℂ)
          * localCoeff om y z * (starRingEnd ℂ) (localCoeff om y z) = 0 := by
      intro z; rw [h_fy_zero]; simp
    simp [h_zero]
  -- Combine: finsum ≥ single term > 0.
  have h_nonneg :
      ∀ y : X,
        0 ≤ (chartLocalSesquilinear om om y (fun x => f.toFun y x)).re := by
    intro y
    exact chartLocalSesquilinear_diagonal_re_nonneg om y (f.nonneg y)
  have h_single_le :
      (chartLocalSesquilinear om om y₀ (fun x => f.toFun y₀ x)).re
        ≤ ∑ᶠ y : X, (chartLocalSesquilinear om om y (fun x => f.toFun y x)).re :=
    single_le_finsum y₀ h_finsupp_re h_nonneg
  exact hy₀_re_pos.trans_le h_single_le

end HolomorphicOneForm

end
