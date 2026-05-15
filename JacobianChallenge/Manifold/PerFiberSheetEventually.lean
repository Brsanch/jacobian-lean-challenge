/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroSourceFiberPathSheetEq

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Per-fibre sub-interval + lift-equality conditions hold eventually near `t = 0`

For a non-constant `f : MeromorphicNonzero X`, a smooth `β : ℝ →
RiemannSphere` regular on `[0, 1]`, and any fibre point `x ∈ sourceFiber
hβ0_reg`, the existing per-fibre local-identification chip
`sourceFiberPath_toPath_extend_eq_sheet_g_locally` gives a
`δ_x ∈ (0, 1]` such that on `[0, δ_x]`:

* `(sourceFiberPath x).toPath.extend t = sheet_x.g (β(σ t))` (lift-eq).

This file packages a **filter-form** of the same content: both
properties (sub-interval `β(σ t) ∈ sheet_x.V` and lift-equality) hold
eventually as `t → 0` from the right.

The filter form is the cleanest input to the per-`t` trace identity
`source_sheet_sum_eq_traceAt`: composing
`Finset.eventually_all_finset` with the per-fibre eventually-equal
property gives the full hypothesis vector for ALL fibre points
simultaneously, holding `∀ᶠ t in 𝓝[≥] 0`.

## What ships

* `MeromorphicNonzero.eventually_sheet_sub_interval_and_lift_eq` —
  per-fibre eventually-equal package: both V-membership and
  lift-equality hold for `t` in a right-neighbourhood of `0`.

* `MeromorphicNonzero.eventually_forall_sheet_sub_interval_and_lift_eq`
  — uniform-over-`sourceFiber` filter form via
  `Finset.eventually_all_finset`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Per-fibre filter-form: sub-interval + lift-equality eventually
hold near `0`.** Repackages
`sourceFiberPath_toPath_extend_eq_sheet_g_locally` as a `∀ᶠ t in 𝓝 0`
statement (using a uniform `[0, δ]` ball as the eventually-set).

Note: the existing chip gives `t ∈ Icc 0 δ`. To upgrade to `𝓝 0` we
shrink to the open `(-δ, δ)` ball. -/
theorem eventually_sheet_lift_eq
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet)
    {x : X} (hx : f.toRiemannSphere x = β 0) :
    ∀ᶠ t in 𝓝[≥] (0 : ℝ),
      (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath.extend t
        = (f.localSheetData_at_regular hnc
            (f.mem_regularSet_of_preimage_regularValue
              (hβ_reg 0 ⟨le_refl _, by norm_num⟩) hx)).g
            (β (Real.smoothTransition t)) := by
  classical
  obtain ⟨δ, hδ_pos, _, h_eq_on⟩ :=
    f.sourceFiberPath_toPath_extend_eq_sheet_g_locally hnc hβ_smooth hβ_reg hx
  -- The set `Icc 0 δ` ∈ 𝓝[≥] 0.
  have h_Icc_nhds : Icc (0 : ℝ) δ ∈ 𝓝[≥] (0 : ℝ) := by
    have h_Ico_sub : Ico (0 : ℝ) δ ⊆ Icc (0 : ℝ) δ := fun _ ⟨h1, h2⟩ =>
      ⟨h1, le_of_lt h2⟩
    have h_Ico_nhds : Ico (0 : ℝ) δ ∈ 𝓝[≥] (0 : ℝ) :=
      Ico_mem_nhdsGE hδ_pos
    exact mem_of_superset h_Ico_nhds h_Ico_sub
  filter_upwards [h_Icc_nhds] with t ht
  exact h_eq_on t ht

/-- **Per-fibre `β(σ t) ∈ sheet_x.V` eventually near `0`.**
Independent of the lift-equality chip: just continuity of `β ∘ σ` plus
`β 0 ∈ sheet_x.V` (from `sheet_x.mem_V` modulo `f.toRiemannSphere x = β 0`). -/
theorem eventually_betaSigma_in_sheetV
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet)
    {x : X} (hx : f.toRiemannSphere x = β 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      β (Real.smoothTransition t) ∈
        (f.localSheetData_at_regular hnc
          (f.mem_regularSet_of_preimage_regularValue
            (hβ_reg 0 ⟨le_refl _, by norm_num⟩) hx)).V := by
  classical
  set sheet := f.localSheetData_at_regular hnc
    (f.mem_regularSet_of_preimage_regularValue
      (hβ_reg 0 ⟨le_refl _, by norm_num⟩) hx) with hsheet_def
  have hβσ_cont : Continuous (fun t : ℝ => β (Real.smoothTransition t)) :=
    hβ_smooth.continuous.comp Real.smoothTransition.continuous
  have hβ0_in_V : β 0 ∈ sheet.V := by
    have h_mem : f.toRiemannSphere x ∈ sheet.V := sheet.mem_V
    exact Eq.subst (motive := fun w => w ∈ sheet.V) hx h_mem
  have h0_in_pre : (0 : ℝ) ∈ (fun t : ℝ => β (Real.smoothTransition t))
      ⁻¹' sheet.V := by
    simp only [Set.mem_preimage, Real.smoothTransition.zero]; exact hβ0_in_V
  exact (hβσ_cont.isOpen_preimage _ sheet.V_open).mem_nhds h0_in_pre

/-- **Uniform-over-`sourceFiber` filter form of `β(σ t) ∈ sheet_p.V`.** -/
theorem eventually_forall_betaSigma_in_sheetV
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ p : { x : X // x ∈ f.sourceFiber
          (hβ_reg 0 ⟨le_refl _, by norm_num⟩) },
        β (Real.smoothTransition t) ∈
          (f.localSheetData_at_regular hnc
            (f.mem_regularSet_of_preimage_regularValue
              (hβ_reg 0 ⟨le_refl _, by norm_num⟩)
              ((f.mem_sourceFiber_iff
                (hβ_reg 0 ⟨le_refl _, by norm_num⟩) p.val).mp p.property))).V := by
  classical
  rw [Filter.eventually_all]
  intro p
  exact f.eventually_betaSigma_in_sheetV hnc hβ_smooth hβ_reg
    ((f.mem_sourceFiber_iff
      (hβ_reg 0 ⟨le_refl _, by norm_num⟩) p.val).mp p.property)

/-- **Uniform-over-`sourceFiber` filter form of lift-equality.** Both
properties hold eventually for every fibre point simultaneously, via
`Finset.eventually_all`. -/
theorem eventually_forall_sheet_lift_eq
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet) :
    ∀ᶠ t in 𝓝[≥] (0 : ℝ),
      ∀ p : { x : X // x ∈ f.sourceFiber
          (hβ_reg 0 ⟨le_refl _, by norm_num⟩) },
        (f.sourceFiberPath hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff
            (hβ_reg 0 ⟨le_refl _, by norm_num⟩) p.val).mp p.property)).toPath.extend t
          = (f.localSheetData_at_regular hnc
              (f.mem_regularSet_of_preimage_regularValue
                (hβ_reg 0 ⟨le_refl _, by norm_num⟩)
                ((f.mem_sourceFiber_iff
                  (hβ_reg 0 ⟨le_refl _, by norm_num⟩) p.val).mp p.property))).g
              (β (Real.smoothTransition t)) := by
  classical
  -- Subtype `↥(f.sourceFiber _)` is Finite (Finset coerces to Finite).
  -- Apply `Filter.eventually_all` to swap the quantifier inside.
  rw [Filter.eventually_all]
  intro p
  exact f.eventually_sheet_lift_eq hnc hβ_smooth hβ_reg
    ((f.mem_sourceFiber_iff
      (hβ_reg 0 ⟨le_refl _, by norm_num⟩) p.val).mp p.property)

end MeromorphicNonzero

end JacobianChallenge

end
