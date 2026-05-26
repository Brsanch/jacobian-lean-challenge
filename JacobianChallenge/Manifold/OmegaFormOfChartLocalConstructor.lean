/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.OmegaFormOfChartLocalSmoothness

/-! # Sub-chip 5.5c-I-b-final — `OmegaForm.ofChartLocalFunction` constructor

Assembles the `OmegaForm X` constructor from the chart-local function
`β : X → ℂ` with `tsupport β ⊆ (chartAt ℂ x).source`, using:

* `localFormCoeff x β` (Sub-chip 5.5c-I-b def+cocycle) for the
  chart-coefficient family;
* `localFormCoeff_contDiffOn` (Sub-chip 5.5c-I-b-smoothness) for the
  `coeff_contDiffOn` field;
* `localFormCoeff_transition` (Sub-chip 5.5c-I-b def+cocycle) for the
  `transition` field.

This is the lift of "ρ_i α" (or any chart-local function) to a
`(0,1)`-form on X — the primitive Sub-chip 5.5c-I-c consumes when
building the partition sum at the form level.

## What this file ships

* `OmegaForm.ofChartLocalFunction x β h_β_smooth h_β_supp` — the
  `(0,1)`-form whose chart-`x` view is `β ∘ chart_x.symm` extended
  by zero (= `chartPullbackZero x β` on `chart_x.target`).
* `OmegaForm.ofChartLocalFunction_coeff` — definitional unfolding of
  the `coeff` field.
* `OmegaForm.ofChartLocalFunction_coeff_anchor_eqOn_target` — at the
  anchor `y = x`, the coeff agrees with `chartPullbackZero x β` on
  `chart_x.target`.
* `OmegaForm.ofChartLocalFunction_coeff_eq_zero_of_not_mem_tsupport`
  — vanishing off `tsupport β` (re-exported via the constructor).

No `sorry`, no `axiom`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff Classical
open Set Function

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℝ, ℂ) ⊤ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## General cocycle (arbitrary chart pair, not just anchor-relative)

The OmegaForm `transition` field requires the cocycle for ANY pair of
charts `(x_lambda, y_lambda)`. The anchor-relative cocycle
(`localFormCoeff_transition`) only handles `(anchor, y_lambda)`. We
upgrade via case-split on whether `p ∈ chart_anchor.source`:

* If yes: apply anchor-relative cocycle to both `y_lambda` and
  `x_lambda`, divide, and use the chain rule for chart-transition
  composition `τ_{x → y1} = τ_{x1 → y1} · τ_{x → x1}`.
* If no: `β(p) = 0`, so both sides of the cocycle vanish (zero branch
  of `localFormCoeff` at both `x1` and `y1`), and the cocycle is
  trivial.
-/

/-- **General cocycle for `localFormCoeff`.** Holds for arbitrary
chart pair `(x1, y1)`, derived from the anchor-relative cocycle via
case-split + chain rule. -/
theorem localFormCoeff_transition_general
    (x : X) (β : X → ℂ)
    (h_β_supp : tsupport β ⊆ (chartAt ℂ x).source)
    {x1 y1 : X} {p : X}
    (hpx1 : p ∈ (chartAt ℂ x1).source)
    (hpy1 : p ∈ (chartAt ℂ y1).source) :
    localFormCoeff x β y1 ((chartAt ℂ y1) p) *
      (starRingEnd ℂ)
        (deriv ((chartAt ℂ y1) ∘ (chartAt ℂ x1).symm) ((chartAt ℂ x1) p))
      = localFormCoeff x β x1 ((chartAt ℂ x1) p) := by
  by_cases hpx : p ∈ (chartAt ℂ x).source
  · -- Case 1: p ∈ chart_anchor.source. Apply anchor-relative cocycle
    -- twice + chain rule for transition composition.
    have h_y1 :
        localFormCoeff x β y1 ((chartAt ℂ y1) p) *
          (starRingEnd ℂ)
            (deriv ((chartAt ℂ y1) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p))
        = localFormCoeff x β x ((chartAt ℂ x) p) :=
      localFormCoeff_transition x β hpx hpy1
    have h_x1 :
        localFormCoeff x β x1 ((chartAt ℂ x1) p) *
          (starRingEnd ℂ)
            (deriv ((chartAt ℂ x1) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p))
        = localFormCoeff x β x ((chartAt ℂ x) p) :=
      localFormCoeff_transition x β hpx hpx1
    -- Chain rule: τ_{x → y1} = τ_{x1 → y1} · τ_{x → x1}.
    -- Locally on a nbhd of chart_x p:
    --   chart_y1 ∘ chart_x.symm = (chart_y1 ∘ chart_x1.symm) ∘ (chart_x1 ∘ chart_x.symm).
    have h_pre_open : IsOpen ((chartAt ℂ x).target ∩
        (chartAt ℂ x).symm ⁻¹' ((chartAt ℂ x1).source ∩ (chartAt ℂ y1).source)) :=
      (chartAt ℂ x).isOpen_inter_preimage_symm
        ((chartAt ℂ x1).open_source.inter (chartAt ℂ y1).open_source)
    have h_chart_x_p_target : (chartAt ℂ x) p ∈ (chartAt ℂ x).target :=
      (chartAt ℂ x).map_source hpx
    have h_chart_x_p_mem : (chartAt ℂ x) p ∈ (chartAt ℂ x).target ∩
        (chartAt ℂ x).symm ⁻¹' ((chartAt ℂ x1).source ∩ (chartAt ℂ y1).source) := by
      refine ⟨h_chart_x_p_target, ?_⟩
      show (chartAt ℂ x).symm ((chartAt ℂ x) p) ∈ (chartAt ℂ x1).source ∩ (chartAt ℂ y1).source
      rw [(chartAt ℂ x).left_inv hpx]
      exact ⟨hpx1, hpy1⟩
    have h_evEq : ((chartAt ℂ y1) ∘ (chartAt ℂ x).symm)
        =ᶠ[𝓝 ((chartAt ℂ x) p)]
        ((chartAt ℂ y1) ∘ (chartAt ℂ x1).symm) ∘
        ((chartAt ℂ x1) ∘ (chartAt ℂ x).symm) := by
      filter_upwards [h_pre_open.mem_nhds h_chart_x_p_mem] with w hw
      obtain ⟨_hw_tgt, hw_pre⟩ := hw
      obtain ⟨hw_x1_src, _hw_y1_src⟩ := hw_pre
      show (chartAt ℂ y1) ((chartAt ℂ x).symm w)
          = (chartAt ℂ y1) ((chartAt ℂ x1).symm ((chartAt ℂ x1) ((chartAt ℂ x).symm w)))
      rw [(chartAt ℂ x1).left_inv hw_x1_src]
    -- Both maps ℂ-differentiable at the right points.
    have h_x1_atlas : chartAt ℂ x1 ∈ atlas ℂ X := chart_mem_atlas ℂ x1
    have h_y1_atlas : chartAt ℂ y1 ∈ atlas ℂ X := chart_mem_atlas ℂ y1
    have h_x_atlas : chartAt ℂ x ∈ atlas ℂ X := chart_mem_atlas ℂ x
    have h_x1_diff : DifferentiableAt ℂ ((chartAt ℂ x1) ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) p) :=
      (JacobianChallenge.analyticAt_chart_transition_of_isManifold
        h_x_atlas h_x1_atlas hpx hpx1).differentiableAt
    -- chart_y1 ∘ chart_x1.symm at ((chart_x1 ∘ chart_x.symm) (chart_x p)) = chart_y1 ∘ chart_x1.symm at chart_x1 p
    -- (since chart_x1 ∘ chart_x.symm at chart_x p = chart_x1 p via chart_x.left_inv).
    have h_apply_x1 : ((chartAt ℂ x1) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p)
        = (chartAt ℂ x1) p := by
      show (chartAt ℂ x1) ((chartAt ℂ x).symm ((chartAt ℂ x) p)) = (chartAt ℂ x1) p
      rw [(chartAt ℂ x).left_inv hpx]
    have h_y1_x1_diff : DifferentiableAt ℂ ((chartAt ℂ y1) ∘ (chartAt ℂ x1).symm)
        (((chartAt ℂ x1) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p)) := by
      rw [h_apply_x1]
      exact (JacobianChallenge.analyticAt_chart_transition_of_isManifold
        h_x1_atlas h_y1_atlas hpx1 hpy1).differentiableAt
    -- Chain-rule the composition's deriv.
    have h_chain :
        deriv (((chartAt ℂ y1) ∘ (chartAt ℂ x1).symm) ∘
                ((chartAt ℂ x1) ∘ (chartAt ℂ x).symm)) ((chartAt ℂ x) p)
        = deriv ((chartAt ℂ y1) ∘ (chartAt ℂ x1).symm)
                (((chartAt ℂ x1) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p)) *
          deriv ((chartAt ℂ x1) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p) :=
      deriv_comp ((chartAt ℂ x) p) h_y1_x1_diff h_x1_diff
    rw [h_apply_x1] at h_chain
    -- The original τ_{x → y1} is equal to the composition's deriv via h_evEq.
    have h_τ_eq :
        deriv ((chartAt ℂ y1) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p)
        = deriv ((chartAt ℂ y1) ∘ (chartAt ℂ x1).symm) ((chartAt ℂ x1) p) *
          deriv ((chartAt ℂ x1) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p) :=
      (Filter.EventuallyEq.deriv_eq h_evEq).trans h_chain
    -- Algebra: combine h_y1, h_x1, h_τ_eq to derive the goal.
    rw [h_τ_eq] at h_y1
    -- h_y1 : coeff_y1 ... · conj(τ_{x1→y1} · τ_{x→x1}) = coeff_x ...
    -- Want:  coeff_y1 ... · conj(τ_{x1→y1}) = coeff_x1 ...
    -- h_x1 :  coeff_x1 ... · conj(τ_{x→x1}) = coeff_x ...
    -- So coeff_y1 ... · conj(τ_{x1→y1}) · conj(τ_{x→x1}) = coeff_x = coeff_x1 ... · conj(τ_{x→x1}).
    -- Cancel conj(τ_{x→x1}) (nonzero by `deriv_chart_transition_ne_zero`).
    have h_τx_x1_ne_zero :
        deriv ((chartAt ℂ x1) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p) ≠ 0 :=
      deriv_chart_transition_ne_zero hpx hpx1
    have h_conj_τx_x1_ne_zero :
        (starRingEnd ℂ)
          (deriv ((chartAt ℂ x1) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p)) ≠ 0 := by
      intro h
      apply h_τx_x1_ne_zero
      have := congrArg (starRingEnd ℂ) h
      simpa using this
    rw [map_mul (starRingEnd ℂ), ← mul_assoc] at h_y1
    -- h_y1 : (coeff_y1 ... · conj(τ_{x1→y1})) · conj(τ_{x→x1}) = coeff_x ...
    rw [← h_x1] at h_y1
    -- h_y1 : (coeff_y1 ... · conj(τ_{x1→y1})) · conj(τ_{x→x1}) = coeff_x1 ... · conj(τ_{x→x1})
    exact mul_right_cancel₀ h_conj_τx_x1_ne_zero h_y1
  · -- Case 2: p ∉ chart_anchor.source. Both sides 0.
    have hp_not_supp : p ∉ tsupport β := fun h => hpx (h_β_supp h)
    have h_y1 : localFormCoeff x β y1 ((chartAt ℂ y1) p) = 0 :=
      localFormCoeff_eq_zero_of_not_mem_tsupport x β y1 hpy1 hp_not_supp
    have h_x1 : localFormCoeff x β x1 ((chartAt ℂ x1) p) = 0 :=
      localFormCoeff_eq_zero_of_not_mem_tsupport x β x1 hpx1 hp_not_supp
    rw [h_y1, h_x1]; ring

namespace OmegaForm

/-- **The chart-local-function lift to `(0,1)`-forms.** Given an
anchor `x : X` and a manifold-smooth `β : X → ℂ` whose `tsupport`
sits in `(chartAt ℂ x).source`, this is the `OmegaForm X` whose
chart-`x` view is `β ∘ chart_x.symm` extended by zero off
`chart_x.target` (i.e., `chartPullbackZero x β` on `chart_x.target`),
and whose other chart views are determined by the `(0,1)`-form
chart-change cocycle. -/
def ofChartLocalFunction
    (x : X) (β : X → ℂ)
    (h_β_smooth : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ β)
    (h_β_supp : tsupport β ⊆ (chartAt ℂ x).source) :
    OmegaForm X :=
  { coeff := localFormCoeff x β
    coeff_contDiffOn := fun y => localFormCoeff_contDiffOn x h_β_smooth h_β_supp y
    transition := fun hpx1 hpy1 =>
      localFormCoeff_transition_general x β h_β_supp hpx1 hpy1 }

@[simp] lemma ofChartLocalFunction_coeff
    (x : X) (β : X → ℂ)
    (h_β_smooth : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ β)
    (h_β_supp : tsupport β ⊆ (chartAt ℂ x).source) (y : X) (z : ℂ) :
    (ofChartLocalFunction x β h_β_smooth h_β_supp).coeff y z = localFormCoeff x β y z :=
  rfl

/-- At the anchor `y = x`, the coeff agrees with `chartPullbackZero
x β` on `chart_x.target`. Direct re-export of
`localFormCoeff_at_anchor_eqOn_target`. -/
lemma ofChartLocalFunction_coeff_anchor_eqOn_target
    (x : X) (β : X → ℂ)
    (h_β_smooth : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ β)
    (h_β_supp : tsupport β ⊆ (chartAt ℂ x).source) :
    EqOn ((ofChartLocalFunction x β h_β_smooth h_β_supp).coeff x)
      (chartPullbackZero x β) ((chartAt ℂ x).target) := by
  intro z hz
  rw [ofChartLocalFunction_coeff]
  exact localFormCoeff_at_anchor_eqOn_target x β hz

/-- For `p ∉ tsupport β` with `p ∈ chart_y.source`, the chart-`y`
view of `ofChartLocalFunction` vanishes at `chart_y p`. Direct
re-export of `localFormCoeff_eq_zero_of_not_mem_tsupport`. -/
lemma ofChartLocalFunction_coeff_eq_zero_of_not_mem_tsupport
    (x : X) (β : X → ℂ)
    (h_β_smooth : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ β)
    (h_β_supp : tsupport β ⊆ (chartAt ℂ x).source)
    {y p : X} (h_p_y : p ∈ (chartAt ℂ y).source) (hp : p ∉ tsupport β) :
    (ofChartLocalFunction x β h_β_smooth h_β_supp).coeff y ((chartAt ℂ y) p) = 0 := by
  rw [ofChartLocalFunction_coeff]
  exact localFormCoeff_eq_zero_of_not_mem_tsupport x β y h_p_y hp

end OmegaForm

end JacobianChallenge

end

