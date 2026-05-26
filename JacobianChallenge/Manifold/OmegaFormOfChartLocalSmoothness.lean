/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.OmegaFormOfChartLocal
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Sub-chip 5.5c-I-b-smoothness — smoothness of `localFormCoeff`

For `β : X → ℂ` smooth with `tsupport β ⊆ (chartAt ℂ x).source` on a
compact complex 1-manifold X, we show
`ContDiffOn ℝ ∞ (localFormCoeff x β y) ((chartAt ℂ y).target)`
for every `y : X`. This is the smoothness obligation needed by
`OmegaForm`'s `coeff_contDiffOn` field; combined with Sub-chip
5.5c-I-b's cocycle (`localFormCoeff_transition`), the OmegaForm
constructor `OmegaForm.ofChartLocalFunction` ships in a follow-up.

## Proof strategy

Cover `(chartAt ℂ y).target` by two open sets:

* **Set A** = `chart_y.target ∩ chart_y.symm⁻¹(chart_x.source)`: on
  this set, `chart_y.symm z ∈ chart_x.source`, so the formula branch
  of `localFormCoeff` applies. The formula
  ```
  β(chart_y.symm z) / conj(deriv(chart_y ∘ chart_x.symm)
                                 (chart_x(chart_y.symm z)))
  ```
  is smooth as a composition: β is `ContMDiff` on X, chart_y.symm is
  smooth on chart_y.target, chart_x ∘ chart_y.symm is smooth on Set A
  (composition restricted to the overlap), `deriv(chart_y ∘
  chart_x.symm)` is smooth via `AnalyticAt.deriv` (chart transitions
  are ℂ-analytic, derivatives of analytic functions are analytic,
  hence ℝ-smooth), `conj` is ℝ-linear continuous (smooth), and
  division is smooth where the denominator is nonzero
  (`deriv_chart_transition_ne_zero` from 5.5c-I-b).
* **Set B** = `chart_y.target \ chart_y '' (tsupport β ∩
  chart_y.source)`: on this set, `localFormCoeff x β y z = 0` (by
  `localFormCoeff_eq_zero_of_not_mem_tsupport` from 5.5c-I-b), so
  smoothness is the constant-zero smoothness.

These cover `chart_y.target`: for `z ∈ chart_y.target`, let `p :=
chart_y.symm z`. Either `p ∈ chart_x.source` (`z ∈ Set A`), or
`p ∉ chart_x.source` ⇒ `p ∉ tsupport β` (since `tsupport β ⊆
chart_x.source`) ⇒ `z = chart_y p ∉ chart_y '' (tsupport β ∩
chart_y.source)` ⇒ `z ∈ Set B`.

`ContDiffOn` is local under open covers, so smoothness on both pieces
glues to smoothness on `chart_y.target`.

## What this file ships

* `localFormCoeff_contDiffOn` — `ContDiffOn ℝ ∞ (localFormCoeff x β y)
  ((chartAt ℂ y).target)` under the standing hypotheses.

No `sorry`, no `axiom`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open scoped Manifold Topology ContDiff Classical
open Complex Set Function

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℝ, ℂ) ⊤ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Scalar-tower workaround (mirror of `PartialZBarChainRule.lean`). -/

@[reducible] private def isScalarTower_R_C_C_local : IsScalarTower ℝ ℂ ℂ :=
  ⟨fun (r : ℝ) (c c' : ℂ) => by
    show (r • c) • c' = r • c • c'
    rw [smul_assoc]⟩

/-- ℂ-`ContDiffAt` ⇒ ℝ-`ContDiffAt` with explicit `IsScalarTower ℝ ℂ ℂ`
instance, dodging the synthesis diamond. -/
private theorem contDiffAt_restrictScalars_R_C_C_local
    {n : WithTop ℕ∞} {f : ℂ → ℂ} {z : ℂ} (h : ContDiffAt ℂ n f z) :
    ContDiffAt ℝ n f z :=
  @ContDiffAt.restrict_scalars ℝ _ ℂ _ _ ℂ _ _ _ _ _ ℂ _ _ _
    isScalarTower_R_C_C_local _ isScalarTower_R_C_C_local h

/-! ## Smoothness on Set A (the formula branch) -/

/-- The chart-transition derivative `z ↦ deriv(chart_y ∘ chart_x.symm)
z` is ℂ-analytic at any point `(chartAt ℂ x) p` for `p ∈
chart_x.source ∩ chart_y.source`. Combines
`analyticAt_chart_transition_of_isManifold` with `AnalyticAt.deriv`.
-/
lemma analyticAt_deriv_chart_transition
    {x y : X} {p : X}
    (hpx : p ∈ (chartAt ℂ x).source) (hpy : p ∈ (chartAt ℂ y).source) :
    AnalyticAt ℂ (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm))
      ((chartAt ℂ x) p) := by
  have h_x_atlas : chartAt ℂ x ∈ atlas ℂ X := chart_mem_atlas ℂ x
  have h_y_atlas : chartAt ℂ y ∈ atlas ℂ X := chart_mem_atlas ℂ y
  have h_an : AnalyticAt ℂ ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) p) :=
    JacobianChallenge.analyticAt_chart_transition_of_isManifold
      h_x_atlas h_y_atlas hpx hpy
  exact h_an.deriv

/-- `chart_x ∘ chart_y.symm` is ℝ-smooth on the open set `chart_y.target
∩ chart_y.symm⁻¹(chart_x.source)`. Composition: `chart_y.symm` smooth
on `chart_y.target`, `chart_x` smooth on `chart_x.source`. -/
lemma contDiffOn_chart_x_comp_chart_y_symm (x y : X) :
    ContDiffOn ℝ ∞
      ((chartAt ℂ x) ∘ (chartAt ℂ y).symm)
      ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source) := by
  -- chart_y.symm is ContMDiffOn on chart_y.target (with values in X).
  have h_symm : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (chartAt ℂ y).symm (chartAt ℂ y).target :=
    contMDiffOn_chart_symm
  -- chart_x is ContMDiffOn on chart_x.source.
  have h_chart_x : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (chartAt ℂ x) (chartAt ℂ x).source :=
    contMDiffOn_chart
  -- Restrict h_symm to s and compose.
  set s : Set ℂ :=
    (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source with hs_def
  have h_symm_s : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (chartAt ℂ y).symm s :=
    h_symm.mono Set.inter_subset_left
  have h_st : s ⊆ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source :=
    Set.inter_subset_right
  have h_comp : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      ((chartAt ℂ x) ∘ (chartAt ℂ y).symm) s :=
    h_chart_x.comp h_symm_s h_st
  exact contMDiffOn_iff_contDiffOn.mp h_comp

/-- `β ∘ chart_y.symm` is ℝ-smooth on `chart_y.target` (for `β`
manifold-smooth). -/
lemma contDiffOn_β_comp_chart_y_symm
    {β : X → ℂ} (h_β : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ β) (y : X) :
    ContDiffOn ℝ ∞ (β ∘ (chartAt ℂ y).symm) ((chartAt ℂ y).target) := by
  have h_symm : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (chartAt ℂ y).symm (chartAt ℂ y).target :=
    contMDiffOn_chart_symm
  have h_comp : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (β ∘ (chartAt ℂ y).symm) ((chartAt ℂ y).target) :=
    h_β.comp_contMDiffOn h_symm
  exact contMDiffOn_iff_contDiffOn.mp h_comp

/-- On Set A, `localFormCoeff x β y` agrees with the formula.
EqOn version for ContDiffOn.congr applications. -/
lemma localFormCoeff_eqOn_setA (x : X) (β : X → ℂ) (y : X) :
    EqOn (localFormCoeff x β y)
      (fun z => β ((chartAt ℂ y).symm z) /
        (starRingEnd ℂ)
          (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)
                 ((chartAt ℂ x) ((chartAt ℂ y).symm z))))
      ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source) := by
  intro z hz
  exact localFormCoeff_of_mem x β y hz.2

/-- The formula on Set A is smooth: composition of smooth pieces,
denominator nonvanishing via `deriv_chart_transition_ne_zero`. -/
lemma contDiffOn_formula_setA
    (x : X) {β : X → ℂ} (h_β : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ β) (y : X) :
    ContDiffOn ℝ ∞
      (fun z => β ((chartAt ℂ y).symm z) /
        (starRingEnd ℂ)
          (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)
                 ((chartAt ℂ x) ((chartAt ℂ y).symm z))))
      ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source) := by
  set A : Set ℂ :=
    (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source with hA_def
  -- Numerator: β ∘ chart_y.symm smooth on chart_y.target ⊇ A.
  have h_num : ContDiffOn ℝ ∞ (β ∘ (chartAt ℂ y).symm) A :=
    (contDiffOn_β_comp_chart_y_symm h_β y).mono Set.inter_subset_left
  -- Inner composition: chart_x ∘ chart_y.symm smooth on A.
  have h_inner : ContDiffOn ℝ ∞ ((chartAt ℂ x) ∘ (chartAt ℂ y).symm) A :=
    contDiffOn_chart_x_comp_chart_y_symm x y
  -- Derivative of chart transition: analytic on the chart_x.target side,
  -- pulled back to A via the inner composition. We show pointwise
  -- `ContDiffAt`, then assemble to ContDiffOn.
  have h_deriv_smooth_at :
      ∀ z ∈ A, ContDiffAt ℝ ∞
        (fun z => deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)
                        ((chartAt ℂ x) ((chartAt ℂ y).symm z))) z := by
    intro z hz
    have hp_in_y_src : (chartAt ℂ y).symm z ∈ (chartAt ℂ y).source :=
      (chartAt ℂ y).map_target hz.1
    have hp_in_x_src : (chartAt ℂ y).symm z ∈ (chartAt ℂ x).source := hz.2
    -- deriv of chart-transition is analytic at chart_x p, hence smooth-ℝ.
    have h_an : AnalyticAt ℂ
        (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm))
        ((chartAt ℂ x) ((chartAt ℂ y).symm z)) :=
      analyticAt_deriv_chart_transition hp_in_x_src hp_in_y_src
    have h_an_R : ContDiffAt ℝ ∞
        (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm))
        ((chartAt ℂ x) ((chartAt ℂ y).symm z)) := by
      have h_C : ContDiffAt ℂ ∞ (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm))
          ((chartAt ℂ x) ((chartAt ℂ y).symm z)) :=
        h_an.contDiffAt
      exact contDiffAt_restrictScalars_R_C_C_local h_C
    -- chart_x ∘ chart_y.symm is ContDiffAt ℝ ∞ at z (open set ⇒ contDiffAt).
    have h_open_A : IsOpen A := by
      refine (chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ x).open_source
    have h_inner_at : ContDiffAt ℝ ∞ ((chartAt ℂ x) ∘ (chartAt ℂ y).symm) z :=
      (h_inner z hz).contDiffAt (h_open_A.mem_nhds hz)
    -- Compose.
    exact h_an_R.comp z h_inner_at
  -- Lift the pointwise ContDiffAt to ContDiffOn on A.
  have h_open_A : IsOpen A :=
    (chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ x).open_source
  have h_deriv_smooth : ContDiffOn ℝ ∞
      (fun z => deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)
                      ((chartAt ℂ x) ((chartAt ℂ y).symm z))) A := by
    intro z hz
    exact (h_deriv_smooth_at z hz).contDiffWithinAt
  -- conj is ContDiff ℝ ∞.
  have h_conj : ContDiff ℝ ∞ ((starRingEnd ℂ) : ℂ → ℂ) :=
    Complex.conjCLE.contDiff
  -- conj ∘ (deriv ∘ inner) is smooth on A.
  have h_conj_deriv : ContDiffOn ℝ ∞
      (fun z => (starRingEnd ℂ)
        (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)
               ((chartAt ℂ x) ((chartAt ℂ y).symm z)))) A :=
    h_conj.comp_contDiffOn h_deriv_smooth
  -- Denominator nonvanishing on A.
  have h_denom_ne_zero : ∀ z ∈ A,
      (starRingEnd ℂ)
        (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)
               ((chartAt ℂ x) ((chartAt ℂ y).symm z))) ≠ 0 := by
    intro z hz
    have hp_in_y_src : (chartAt ℂ y).symm z ∈ (chartAt ℂ y).source :=
      (chartAt ℂ y).map_target hz.1
    have hp_in_x_src : (chartAt ℂ y).symm z ∈ (chartAt ℂ x).source := hz.2
    have h_ne :
        deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)
              ((chartAt ℂ x) ((chartAt ℂ y).symm z)) ≠ 0 :=
      deriv_chart_transition_ne_zero hp_in_x_src hp_in_y_src
    intro h_conj_eq
    apply h_ne
    have := congrArg (starRingEnd ℂ) h_conj_eq
    simpa using this
  -- Division via inv + mul (over ℝ, codomain ℂ — `ContDiffOn.div` needs
  -- field = codomain so we route through inverse).
  have h_inv : ContDiffOn ℝ ∞
      (fun z => ((starRingEnd ℂ)
        (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)
               ((chartAt ℂ x) ((chartAt ℂ y).symm z))))⁻¹) A :=
    h_conj_deriv.inv h_denom_ne_zero
  have h_mul : ContDiffOn ℝ ∞
      (fun z => β ((chartAt ℂ y).symm z) *
        ((starRingEnd ℂ)
          (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)
                 ((chartAt ℂ x) ((chartAt ℂ y).symm z))))⁻¹) A :=
    h_num.mul h_inv
  -- The goal is `f z / g z`; rewrite as `f z * (g z)⁻¹`.
  refine h_mul.congr ?_
  intro z _
  show β ((chartAt ℂ y).symm z) *
      ((starRingEnd ℂ)
        (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)
               ((chartAt ℂ x) ((chartAt ℂ y).symm z))))⁻¹
    = β ((chartAt ℂ y).symm z) /
        (starRingEnd ℂ)
          (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)
                 ((chartAt ℂ x) ((chartAt ℂ y).symm z)))
  rw [div_eq_mul_inv]

/-! ## Smoothness on Set B (the zero branch) -/

/-- On Set B (`chart_y.target ∩ chart_y.symm⁻¹((tsupport β)ᶜ)`,
manifestly open as the intersection of two open sets),
`localFormCoeff x β y` is identically zero. ContDiffOn ∞ for free. -/
lemma contDiffOn_setB
    (x : X) (β : X → ℂ) (y : X) :
    ContDiffOn ℝ ∞ (localFormCoeff x β y)
      ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (tsupport β)ᶜ) := by
  set B : Set ℂ :=
    (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (tsupport β)ᶜ with hB_def
  -- localFormCoeff x β y = 0 on B.
  have h_eq_zero : EqOn (localFormCoeff x β y) (fun _ => (0 : ℂ)) B := by
    intro z hz
    obtain ⟨hz_tgt, hz_not_supp⟩ := hz
    have hp_in_src : (chartAt ℂ y).symm z ∈ (chartAt ℂ y).source :=
      (chartAt ℂ y).map_target hz_tgt
    have hp_not_supp : (chartAt ℂ y).symm z ∉ tsupport β := hz_not_supp
    have h_eq : localFormCoeff x β y ((chartAt ℂ y) ((chartAt ℂ y).symm z)) = 0 :=
      localFormCoeff_eq_zero_of_not_mem_tsupport x β y hp_in_src hp_not_supp
    rwa [(chartAt ℂ y).right_inv hz_tgt] at h_eq
  -- Constantly zero is C^∞.
  apply ContDiffOn.congr (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℂ => (0 : ℂ)) B)
  intro z hz
  exact h_eq_zero hz

/-! ## Assembly: smoothness on `chart_y.target` -/

/-- **Headline.** `localFormCoeff x β y` is `ContDiffOn ℝ ∞` on
`(chartAt ℂ y).target`, under the hypotheses that `β` is manifold-
smooth and `tsupport β ⊆ (chartAt ℂ x).source`. Glues the
formula-branch smoothness on Set A with the zero-branch smoothness
on Set B via `ContDiffOn.union_of_isOpen`. The cover A ∪ B =
`chart_y.target` uses the precondition `h_supp` to argue that any
`p ∈ chart_y.source` with `p ∉ chart_x.source` has `p ∉ tsupport β`.

This is the smoothness obligation for `OmegaForm.ofChartLocalFunction`. -/
theorem localFormCoeff_contDiffOn
    (x : X) {β : X → ℂ} (h_β : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ β)
    (h_supp : tsupport β ⊆ (chartAt ℂ x).source) (y : X) :
    ContDiffOn ℝ ∞ (localFormCoeff x β y) ((chartAt ℂ y).target) := by
  -- The two-open-set cover.
  set A : Set ℂ :=
    (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source with hA_def
  set B : Set ℂ :=
    (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (tsupport β)ᶜ with hB_def
  -- Both sets are open.
  have h_A_open : IsOpen A :=
    (chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ x).open_source
  have h_B_open : IsOpen B :=
    (chartAt ℂ y).isOpen_inter_preimage_symm (isClosed_tsupport β).isOpen_compl
  -- A ∪ B = chart_y.target.
  have h_cover : A ∪ B = (chartAt ℂ y).target := by
    apply Set.eq_of_subset_of_subset
    · rintro z (⟨hz_tgt, _⟩ | ⟨hz_tgt, _⟩) <;> exact hz_tgt
    · intro z hz
      have hp_y : (chartAt ℂ y).symm z ∈ (chartAt ℂ y).source :=
        (chartAt ℂ y).map_target hz
      by_cases hpx : (chartAt ℂ y).symm z ∈ (chartAt ℂ x).source
      · exact Or.inl ⟨hz, hpx⟩
      · -- p ∉ chart_x.source ⇒ p ∉ tsupport β.
        have hp_not_supp : (chartAt ℂ y).symm z ∉ tsupport β := fun h_supp_mem =>
          hpx (h_supp h_supp_mem)
        exact Or.inr ⟨hz, hp_not_supp⟩
  -- Smoothness on A (formula branch).
  have h_A_smooth_formula : ContDiffOn ℝ ∞
      (fun z => β ((chartAt ℂ y).symm z) /
        (starRingEnd ℂ)
          (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)
                 ((chartAt ℂ x) ((chartAt ℂ y).symm z)))) A :=
    contDiffOn_formula_setA x h_β y
  have h_A_smooth : ContDiffOn ℝ ∞ (localFormCoeff x β y) A := by
    apply h_A_smooth_formula.congr
    intro z hz
    exact (localFormCoeff_eqOn_setA x β y hz)
  -- Smoothness on B (zero branch).
  have h_B_smooth : ContDiffOn ℝ ∞ (localFormCoeff x β y) B :=
    contDiffOn_setB x β y
  -- Glue via union_of_isOpen.
  have h_AB_smooth : ContDiffOn ℝ ∞ (localFormCoeff x β y) (A ∪ B) :=
    ContDiffOn.union_of_isOpen h_A_smooth h_B_smooth h_A_open h_B_open
  rwa [h_cover] at h_AB_smooth

end JacobianChallenge

end

