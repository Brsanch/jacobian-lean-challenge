/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.OmegaForm
import JacobianChallenge.Manifold.ChartPullbackExtendZero
import JacobianChallenge.Manifold.ChartPullbackExtendZeroSmooth
import JacobianChallenge.Manifold.PartialZBarChainRule

/-! # Sub-chip 5.5c-I-b — chart-local lift to `OmegaForm` (definition + cocycle)

Given a chart anchor `x : X` and a smooth function `β : X → ℂ` whose
`tsupport β` is contained in `(chartAt ℂ x).source`, this file builds
the chart-coefficient family for "β-as-form-anchored-at-x" and proves
the structural lemmas: zero-off-tsupport, agreement with
`chartPullbackZero` at the anchor, and the `(0,1)`-form transition
cocycle.

Smoothness on `(chartAt ℂ y).target` for arbitrary `y` is a heavier
follow-up (Sub-chip 5.5c-I-b-smoothness, in its own file), as is the
final assembly into an `OmegaForm` constructor.

This file ships **definition + structural lemmas only** so the
smoothness proof, which is the technically heaviest piece, can be
done separately without depending on the rest of Chip 5 stalling.

## What this file ships

* `localFormCoeff x β y z` — the chart-`y` view of "β-as-form-
  anchored-at-x" as a function `ℂ → ℂ`.
* Structural lemmas: `localFormCoeff_of_mem`,
  `localFormCoeff_of_not_mem`,
  `localFormCoeff_eq_zero_of_not_mem_tsupport`.
* `localFormCoeff_at_anchor_eqOn_target` — at `y = x`, the coeff
  agrees with `chartPullbackZero x β` on `chart_x.target`.
* `localFormCoeff_transition` — the `(0,1)`-form transition cocycle
  on chart overlaps.

The OmegaForm constructor and the smoothness theorem ship in the
follow-up sub-chip(s).

No `sorry`, no `axiom`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff Classical
open Complex Set Function

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## The chart-y view formula -/

/-- The cocycle-extended chart-`y` view of "β-as-form-anchored-at-`x`".
Defined as the formula

```
β(chart_y.symm z) / conj(deriv (chart_y ∘ chart_x.symm)
                                (chart_x (chart_y.symm z)))
```

when `chart_y.symm z ∈ chart_x.source` (where the cocycle is well-
defined), and `0` otherwise. The `if`/`else` discontinuity at the
chart-source boundary is harmless under `tsupport β ⊆ chart_x.source`,
because `β` vanishes near the boundary (numerator → 0). -/
def localFormCoeff (x : X) (β : X → ℂ) (y : X) : ℂ → ℂ :=
  fun z =>
    if (chartAt ℂ y).symm z ∈ (chartAt ℂ x).source then
      β ((chartAt ℂ y).symm z) /
        (starRingEnd ℂ)
          (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)
                 ((chartAt ℂ x) ((chartAt ℂ y).symm z)))
    else 0

/-! ## Structural lemmas -/

/-- The cocycle-formula branch: when `chart_y.symm z ∈ chart_x.source`. -/
lemma localFormCoeff_of_mem (x : X) (β : X → ℂ) (y : X) {z : ℂ}
    (h : (chartAt ℂ y).symm z ∈ (chartAt ℂ x).source) :
    localFormCoeff x β y z
      = β ((chartAt ℂ y).symm z) /
          (starRingEnd ℂ)
            (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)
                   ((chartAt ℂ x) ((chartAt ℂ y).symm z))) := by
  unfold localFormCoeff
  rw [if_pos h]

/-- The zero branch: when `chart_y.symm z ∉ chart_x.source`. -/
lemma localFormCoeff_of_not_mem (x : X) (β : X → ℂ) (y : X) {z : ℂ}
    (h : (chartAt ℂ y).symm z ∉ (chartAt ℂ x).source) :
    localFormCoeff x β y z = 0 := by
  unfold localFormCoeff
  rw [if_neg h]

/-- For `p ∉ tsupport β`, the chart-`y` view at `chart_y p` is `0`,
regardless of which branch of the `if` applies. Used both for
smoothness on the "zero-off-image-of-tsupport" cover piece and for
the partition-sum identity in the next sub-chip. -/
lemma localFormCoeff_eq_zero_of_not_mem_tsupport
    (x : X) (β : X → ℂ) (y : X) {p : X}
    (h_p_y : p ∈ (chartAt ℂ y).source)
    (hp : p ∉ tsupport β) :
    localFormCoeff x β y ((chartAt ℂ y) p) = 0 := by
  have h_symm : (chartAt ℂ y).symm ((chartAt ℂ y) p) = p :=
    (chartAt ℂ y).left_inv h_p_y
  by_cases hpx : p ∈ (chartAt ℂ x).source
  · -- formula branch: numerator β(p) = 0.
    have hp_supp : p ∉ Function.support β := fun hsupp => hp (subset_tsupport _ hsupp)
    have h_β_zero : β p = 0 := Function.notMem_support.mp hp_supp
    rw [localFormCoeff_of_mem (h := by rw [h_symm]; exact hpx)]
    rw [h_symm, h_β_zero]
    simp
  · -- zero branch.
    exact localFormCoeff_of_not_mem x β y (by rw [h_symm]; exact hpx)

/-! ## Agreement with `chartPullbackZero` at the anchor -/

/-- At `y = x`, the chart-`x` view of "β-as-form-anchored-at-x" is
just `chartPullbackZero x β` — the chart pullback of `β` extended by
zero. The cocycle factor degenerates: `chart_x ∘ chart_x.symm` agrees
with `id` on a neighborhood of any point of `chart_x.target`, so
`deriv = 1`, `conj 1 = 1`. -/
theorem localFormCoeff_at_anchor_eqOn_target (x : X) (β : X → ℂ) :
    EqOn (localFormCoeff x β x) (chartPullbackZero x β) (chartAt ℂ x).target := by
  intro z hz
  -- chart_x.symm z ∈ chart_x.source (since z ∈ chart_x.target).
  have h_symm_mem : (chartAt ℂ x).symm z ∈ (chartAt ℂ x).source :=
    (chartAt ℂ x).map_target hz
  rw [localFormCoeff_of_mem (h := h_symm_mem)]
  -- chart_x (chart_x.symm z) = z by right_inv.
  have h_right_inv : (chartAt ℂ x) ((chartAt ℂ x).symm z) = z :=
    (chartAt ℂ x).right_inv hz
  -- chart_x ∘ chart_x.symm = id on chart_x.target.
  have h_target_open : IsOpen (chartAt ℂ x).target :=
    (chartAt ℂ x).open_target
  have h_eventuallyEq :
      ((chartAt ℂ x) ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 z] id := by
    filter_upwards [h_target_open.mem_nhds hz] with w hw
    show (chartAt ℂ x) ((chartAt ℂ x).symm w) = w
    exact (chartAt ℂ x).right_inv hw
  -- deriv((chart_x ∘ chart_x.symm))(z) = deriv id z = 1.
  have h_deriv_eq :
      deriv ((chartAt ℂ x) ∘ (chartAt ℂ x).symm) z = 1 := by
    rw [Filter.EventuallyEq.deriv_eq h_eventuallyEq, deriv_id]
  rw [h_right_inv, h_deriv_eq]
  -- conj 1 = 1.
  rw [show (starRingEnd ℂ) 1 = 1 from map_one _, div_one]
  -- LHS: β(chart_x.symm z). RHS: chartPullbackZero x β z = β(chart_x.symm z) on chart_x.target.
  rw [chartPullbackZero_eq_α_chartSymm_on_target _ _ hz]

/-! ## The `(0,1)`-form transition cocycle -/

/-- **Local scalar-tower workaround.** Mirrors the wrapper in
`PartialZBarChainRule.lean` to dodge the `IsScalarTower ℝ ℂ ℂ` diamond
when restricting ℂ-differentiability to ℝ-differentiability on ℂ →
ℂ. -/
@[reducible] private def isScalarTower_R_C_C_local : IsScalarTower ℝ ℂ ℂ :=
  ⟨fun (r : ℝ) (c c' : ℂ) => by
    show (r • c) • c' = r • c • c'
    rw [smul_assoc]⟩

/-- For `p ∈ (chartAt ℂ x).source ∩ (chartAt ℂ y).source`, the
chart-transition derivative `deriv(chart_y ∘ chart_x.symm)(chart_x p)`
is nonzero. (Chart transitions on a holomorphic atlas are
biholomorphisms, so their derivatives don't vanish.) Used to invert
`conj(deriv)` in the cocycle. -/
lemma deriv_chart_transition_ne_zero
    {x y : X} {p : X}
    (hpx : p ∈ (chartAt ℂ x).source) (hpy : p ∈ (chartAt ℂ y).source) :
    deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p) ≠ 0 := by
  -- Compose chart_x ∘ chart_y.symm with chart_y ∘ chart_x.symm
  -- to get the identity locally; chain rule gives product = 1, so
  -- neither factor is 0.
  have h_x_atlas : chartAt ℂ x ∈ atlas ℂ X := chart_mem_atlas ℂ x
  have h_y_atlas : chartAt ℂ y ∈ atlas ℂ X := chart_mem_atlas ℂ y
  -- chart_y ∘ chart_x.symm is ℂ-analytic at chart_x p.
  have h_an_yx : AnalyticAt ℂ ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) p) :=
    JacobianChallenge.analyticAt_chart_transition_of_isManifold
      h_x_atlas h_y_atlas hpx hpy
  -- chart_x ∘ chart_y.symm is ℂ-analytic at chart_y p.
  have h_an_xy : AnalyticAt ℂ ((chartAt ℂ x) ∘ (chartAt ℂ y).symm)
      ((chartAt ℂ y) p) :=
    JacobianChallenge.analyticAt_chart_transition_of_isManifold
      h_y_atlas h_x_atlas hpy hpx
  -- chart_x ∘ chart_y.symm at (chart_y p) = chart_x p.
  have h_xy_apply :
      ((chartAt ℂ x) ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) p) = (chartAt ℂ x) p := by
    show (chartAt ℂ x) ((chartAt ℂ y).symm ((chartAt ℂ y) p)) = (chartAt ℂ x) p
    rw [(chartAt ℂ y).left_inv hpy]
  -- chart_y ∘ chart_x.symm at (chart_x p) = chart_y p.
  have h_yx_apply :
      ((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p) = (chartAt ℂ y) p := by
    show (chartAt ℂ y) ((chartAt ℂ x).symm ((chartAt ℂ x) p)) = (chartAt ℂ y) p
    rw [(chartAt ℂ x).left_inv hpx]
  -- The composition (chart_x ∘ chart_y.symm) ∘ (chart_y ∘ chart_x.symm) agrees
  -- with id on a neighborhood of (chart_x p) (specifically on
  -- chart_x.target ∩ chart_x.symm⁻¹(chart_y.source)).
  have h_pre_open : IsOpen ((chartAt ℂ x).target ∩
      (chartAt ℂ x).symm ⁻¹' (chartAt ℂ y).source) :=
    (chartAt ℂ x).isOpen_inter_preimage_symm (chartAt ℂ y).open_source
  have h_x_p_target : (chartAt ℂ x) p ∈ (chartAt ℂ x).target :=
    (chartAt ℂ x).map_source hpx
  have h_x_p_mem : (chartAt ℂ x) p ∈ (chartAt ℂ x).target ∩
      (chartAt ℂ x).symm ⁻¹' (chartAt ℂ y).source := by
    refine ⟨h_x_p_target, ?_⟩
    show (chartAt ℂ x).symm ((chartAt ℂ x) p) ∈ (chartAt ℂ y).source
    rw [(chartAt ℂ x).left_inv hpx]; exact hpy
  -- Express id-on-nbhd: (chart_x ∘ chart_y.symm) ∘ (chart_y ∘ chart_x.symm) =ᶠ id.
  have h_evEq : ((chartAt ℂ x) ∘ (chartAt ℂ y).symm) ∘
      ((chartAt ℂ y) ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 ((chartAt ℂ x) p)] id := by
    filter_upwards [h_pre_open.mem_nhds h_x_p_mem] with w hw
    obtain ⟨hw_tgt, hw_pre⟩ := hw
    show (chartAt ℂ x) ((chartAt ℂ y).symm ((chartAt ℂ y) ((chartAt ℂ x).symm w))) = w
    rw [(chartAt ℂ y).left_inv hw_pre, (chartAt ℂ x).right_inv hw_tgt]
  -- Apply chain rule for ℂ-deriv on this composition.
  have h_yx_diff : DifferentiableAt ℂ ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) p) := h_an_yx.differentiableAt
  have h_xy_diff : DifferentiableAt ℂ ((chartAt ℂ x) ∘ (chartAt ℂ y).symm)
      ((chartAt ℂ y) p) := h_an_xy.differentiableAt
  have h_xy_diff_at_yx_apply :
      DifferentiableAt ℂ ((chartAt ℂ x) ∘ (chartAt ℂ y).symm)
        (((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p)) := by
    rw [h_yx_apply]; exact h_xy_diff
  have h_chain :
      deriv (((chartAt ℂ x) ∘ (chartAt ℂ y).symm) ∘
              ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)) ((chartAt ℂ x) p)
      = deriv ((chartAt ℂ x) ∘ (chartAt ℂ y).symm)
              (((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p)) *
        deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p) :=
    deriv_comp ((chartAt ℂ x) p) h_xy_diff_at_yx_apply h_yx_diff
  -- The composition's deriv equals deriv id = 1 via the eventual eq.
  have h_comp_deriv :
      deriv (((chartAt ℂ x) ∘ (chartAt ℂ y).symm) ∘
              ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)) ((chartAt ℂ x) p) = 1 := by
    rw [Filter.EventuallyEq.deriv_eq h_evEq, deriv_id]
  -- So the product on RHS of h_chain is 1, and neither factor is 0.
  rw [h_comp_deriv, h_yx_apply] at h_chain
  -- h_chain : 1 = deriv((chart_x ∘ chart_y.symm))(chart_y p) * deriv((chart_y ∘ chart_x.symm))(chart_x p)
  intro h_zero
  rw [h_zero, mul_zero] at h_chain
  exact one_ne_zero h_chain

/-- **Cocycle.** For `p` in both `chart_x.source` and `chart_y.source`,

```
localFormCoeff x β y ((chart_y) p) *
  conj(deriv(chart_y ∘ chart_x.symm)((chart_x) p))
  = localFormCoeff x β x ((chart_x) p).
```

Direct computation: LHS unfolds to
`β(p) / conj(τ) · conj(τ) = β(p)`, and RHS unfolds to `β(p) · 1 = β(p)`
(via `localFormCoeff_at_anchor` and `chartPullbackZero` on
chart_x.target). -/
theorem localFormCoeff_transition
    (x : X) (β : X → ℂ) {y : X} {p : X}
    (hpx : p ∈ (chartAt ℂ x).source) (hpy : p ∈ (chartAt ℂ y).source) :
    localFormCoeff x β y ((chartAt ℂ y) p) *
      (starRingEnd ℂ)
        (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p))
      = localFormCoeff x β x ((chartAt ℂ x) p) := by
  -- LHS evaluation: chart_y.symm (chart_y p) = p ∈ chart_x.source.
  have h_y_left_inv : (chartAt ℂ y).symm ((chartAt ℂ y) p) = p :=
    (chartAt ℂ y).left_inv hpy
  have h_x_left_inv : (chartAt ℂ x).symm ((chartAt ℂ x) p) = p :=
    (chartAt ℂ x).left_inv hpx
  have h_chart_y_p_chart_x : (chartAt ℂ y).symm ((chartAt ℂ y) p) ∈ (chartAt ℂ x).source := by
    rw [h_y_left_inv]; exact hpx
  rw [localFormCoeff_of_mem (h := h_chart_y_p_chart_x)]
  -- RHS evaluation: chart_x.symm (chart_x p) = p ∈ chart_x.source.
  have h_chart_x_p_chart_x : (chartAt ℂ x).symm ((chartAt ℂ x) p) ∈ (chartAt ℂ x).source := by
    rw [h_x_left_inv]; exact hpx
  rw [localFormCoeff_of_mem (h := h_chart_x_p_chart_x)]
  -- chart_x ∘ chart_x.symm = id locally at chart_x p; deriv = 1; conj 1 = 1.
  have h_target_open : IsOpen (chartAt ℂ x).target :=
    (chartAt ℂ x).open_target
  have h_x_p_target : (chartAt ℂ x) p ∈ (chartAt ℂ x).target :=
    (chartAt ℂ x).map_source hpx
  have h_eventuallyEq :
      ((chartAt ℂ x) ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 ((chartAt ℂ x) p)] id := by
    filter_upwards [h_target_open.mem_nhds h_x_p_target] with w hw
    show (chartAt ℂ x) ((chartAt ℂ x).symm w) = w
    exact (chartAt ℂ x).right_inv hw
  have h_deriv_self : deriv ((chartAt ℂ x) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p) = 1 := by
    rw [Filter.EventuallyEq.deriv_eq h_eventuallyEq, deriv_id]
  rw [h_y_left_inv, h_x_left_inv, h_deriv_self,
      show (starRingEnd ℂ) 1 = 1 from map_one _, div_one]
  -- LHS now: β(p) / conj(τ_{x→y}(chart_x p)) * conj(τ_{x→y}(chart_x p)) = β(p).
  -- RHS now: β(p).
  have h_τ_ne_zero :
      deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p) ≠ 0 :=
    deriv_chart_transition_ne_zero hpx hpy
  have h_conj_τ_ne_zero :
      (starRingEnd ℂ)
        (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p)) ≠ 0 := by
    intro h
    apply h_τ_ne_zero
    have := congrArg (starRingEnd ℂ) h
    simp at this
    exact this
  field_simp

end JacobianChallenge

end
