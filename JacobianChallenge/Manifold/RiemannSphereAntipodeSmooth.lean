/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphereMobius
import JacobianChallenge.Manifold.HolomorphicEquivConstructor

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! # Smoothness of the antipodal Möbius map on the Riemann sphere

This file discharges the `contMDiff_antipode_TODO` follow-up flagged in
`RiemannSphereMobius.lean`: the antipode `z ↦ -1/z` on the Riemann sphere
is `ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω` (analytic as a self-map of the complex
1-manifold `RiemannSphere`).

## Strategy

We use `contMDiffAt_iff_of_mem_source` to reduce smoothness at each
`x : RiemannSphere` to:

* `ContinuousAt antipode x` (already in `RiemannSphereMobius.lean`), and
* `ContDiffAt ℂ ω` of the chart-coordinate composition
  `chartAt(antipode x) ∘ antipode ∘ chartAt(x).symm`
  at `chartAt x x`, on `range 𝓘(ℂ) = univ`.

The `OnePoint.rec` case split on `x` aligns with the canonical chart
selection (`chartN` for finite points, `chartS` for `∞`):

| `x`                  | source chart | target chart | local map  | smooth at  |
|----------------------|--------------|--------------|------------|------------|
| `∞`                  | `chartS`     | `chartN`     | `z ↦ -z`   | `0`        |
| `(0 : ℂ : RS)`       | `chartN`     | `chartS`     | `z ↦ -z`   | `0`        |
| `(w : ℂ : RS)`, `w≠0`| `chartN`     | `chartN`     | `z ↦ -z⁻¹` | `w`        |

The first two cases land on the entire map `z ↦ -z`. The third lands on
`z ↦ -z⁻¹`, checked at `w ≠ 0` where the inverse is analytic.

## What ships

* `RiemannSphere.contMDiff_antipode : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω antipode`

No `sorry`, no `axiom`. -/

open OnePoint Set Topology Filter
open scoped Manifold ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-! ### Local `chartAt` reductions on the Riemann sphere

Two small wrappers around `chartAt'_coe` / `chartAt'_infty` that present
the canonical chart choice as an equation on `chartAt ℂ _`. Duplicated
locally to avoid importing `MeromorphicExtension.lean`. -/

@[simp] private lemma chartAt_coe (z : ℂ) :
    (chartAt ℂ ((z : RiemannSphere))) = chartN := by
  show chartAt' ((z : RiemannSphere)) = chartN
  exact chartAt'_coe z

@[simp] private lemma chartAt_infty :
    (chartAt ℂ (∞ : RiemannSphere)) = chartS := by
  show chartAt' (∞ : RiemannSphere) = chartS
  exact chartAt'_infty

/-! ### Chart-pullback formulas for `antipode`

Three pointwise equations express the local form of `antipode` in the
three chart pairings relevant to the canonical chart selection. The
first two equations hold on all of `ℂ` (the chart-flip point glues
continuously). The third holds on `{z ≠ 0}`. -/

/-- `chartN ∘ antipode ∘ chartS.symm` agrees with `(-·) : ℂ → ℂ`. -/
lemma chartN_antipode_chartS_symm (z : ℂ) :
    chartN (antipode (chartS.symm z)) = -z := by
  by_cases hz : z = 0
  · subst hz
    rw [chartS_symm_apply_zero, antipode_infty, chartN_apply_coe]
    simp
  · rw [chartS_symm_apply_of_ne hz]
    have hzinv : z⁻¹ ≠ 0 := inv_ne_zero hz
    rw [antipode_coe_of_ne hzinv, chartN_apply_coe, inv_inv]

/-- `chartS ∘ antipode ∘ chartN.symm` agrees with `(-·) : ℂ → ℂ`. -/
lemma chartS_antipode_chartN_symm (z : ℂ) :
    chartS (antipode (chartN.symm z)) = -z := by
  rw [chartN_symm_apply]
  by_cases hz : z = 0
  · subst hz
    rw [antipode_coe_zero, chartS_apply_infty]
    simp
  · rw [antipode_coe_of_ne hz, chartS_apply_coe, inv_neg, inv_inv]

/-- `chartN ∘ antipode ∘ chartN.symm` agrees with `z ↦ -z⁻¹` on `{z ≠ 0}`. -/
lemma chartN_antipode_chartN_symm {z : ℂ} (hz : z ≠ 0) :
    chartN (antipode (chartN.symm z)) = -z⁻¹ := by
  rw [chartN_symm_apply, antipode_coe_of_ne hz, chartN_apply_coe]

/-! ### Smoothness of `antipode` -/

/-- The antipodal Möbius map `z ↦ -1/z` is analytic (`C^ω`) as a self-map
of the Riemann sphere. -/
theorem contMDiff_antipode :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω antipode := by
  intro x
  -- Reduce ContMDiffAt to (continuity ∧ chart-coord ContDiffWithinAt).
  have hx_source : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hax_source : antipode x ∈ (chartAt ℂ (antipode x)).source :=
    mem_chart_source ℂ (antipode x)
  rw [contMDiffAt_iff_of_mem_source hx_source hax_source]
  -- `range 𝓘(ℂ) = univ` collapses `ContDiffWithinAt` to `ContDiffAt`.
  have h_range : Set.range (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ) = Set.univ :=
    ModelWithCorners.range_eq_univ _
  rw [h_range, contDiffWithinAt_univ]
  refine ⟨continuous_antipode.continuousAt, ?_⟩
  -- Three cases on `x`.
  induction x using OnePoint.rec with
  | infty =>
    -- antipode ∞ = (0 : RS); chartAt ∞ = chartS, chartAt (0 : RS) = chartN.
    -- Local form is `z ↦ -z`; (chartAt ℂ ∞) ∞ = chartS ∞ = 0.
    have h_chart_x : chartAt ℂ (∞ : RiemannSphere) = chartS := chartAt_infty
    have h_chart_ax : chartAt ℂ (antipode (∞ : RiemannSphere)) = chartN := by
      rw [antipode_infty]; exact chartAt_coe (0 : ℂ)
    have h_pt : (extChartAt 𝓘(ℂ, ℂ) (∞ : RiemannSphere)) (∞ : RiemannSphere)
        = (0 : ℂ) := by
      simp [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_coe,
            h_chart_x, chartS_apply_infty]
    rw [h_pt]
    have h_cd : ContDiffAt ℂ (ω : WithTop ℕ∞) (fun z : ℂ => -z) (0 : ℂ) :=
      contDiffAt_id.neg
    refine h_cd.congr_of_eventuallyEq ?_
    refine Filter.Eventually.of_forall (fun z => ?_)
    show (extChartAt 𝓘(ℂ, ℂ) (antipode (∞ : RiemannSphere)))
            (antipode ((extChartAt 𝓘(ℂ, ℂ) (∞ : RiemannSphere)).symm z))
        = -z
    have h_symm : (extChartAt 𝓘(ℂ, ℂ) (∞ : RiemannSphere)).symm z
        = chartS.symm z := by
      simp [extChartAt, OpenPartialHomeomorph.extend,
            modelWithCornersSelf_coe_symm, h_chart_x]
    have h_apply : (extChartAt 𝓘(ℂ, ℂ) (antipode (∞ : RiemannSphere)))
            (antipode (chartS.symm z))
        = chartN (antipode (chartS.symm z)) := by
      simp [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_coe,
            h_chart_ax]
    rw [h_symm, h_apply, chartN_antipode_chartS_symm]
  | coe w =>
    by_cases hw : w = 0
    · subst hw
      -- antipode (0 : RS) = ∞; chartAt (0 : RS) = chartN, chartAt ∞ = chartS.
      -- Local form: `chartS ∘ antipode ∘ chartN.symm = -·`. Smooth at `0`.
      have h_chart_x : chartAt ℂ (((0 : ℂ) : RiemannSphere)) = chartN :=
        chartAt_coe (0 : ℂ)
      have h_chart_ax :
          chartAt ℂ (antipode (((0 : ℂ) : RiemannSphere))) = chartS := by
        rw [antipode_coe_zero]; exact chartAt_infty
      have h_pt : (extChartAt 𝓘(ℂ, ℂ) (((0 : ℂ) : RiemannSphere)))
              (((0 : ℂ) : RiemannSphere)) = (0 : ℂ) := by
        simp [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_coe,
              h_chart_x, chartN_apply_coe]
      rw [h_pt]
      have h_cd : ContDiffAt ℂ (ω : WithTop ℕ∞) (fun z : ℂ => -z) (0 : ℂ) :=
        contDiffAt_id.neg
      refine h_cd.congr_of_eventuallyEq ?_
      refine Filter.Eventually.of_forall (fun z => ?_)
      show (extChartAt 𝓘(ℂ, ℂ) (antipode (((0 : ℂ) : RiemannSphere))))
              (antipode ((extChartAt 𝓘(ℂ, ℂ) (((0 : ℂ) : RiemannSphere))).symm z))
          = -z
      have h_symm : (extChartAt 𝓘(ℂ, ℂ) (((0 : ℂ) : RiemannSphere))).symm z
          = chartN.symm z := by
        simp [extChartAt, OpenPartialHomeomorph.extend,
              modelWithCornersSelf_coe_symm, h_chart_x]
      have h_apply :
          (extChartAt 𝓘(ℂ, ℂ) (antipode (((0 : ℂ) : RiemannSphere))))
              (antipode (chartN.symm z))
          = chartS (antipode (chartN.symm z)) := by
        simp [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_coe,
              h_chart_ax]
      rw [h_symm, h_apply, chartS_antipode_chartN_symm]
    · -- antipode (coe w) = coe (-w⁻¹), finite for w ≠ 0.
      -- chartAt (coe w) = chartN, chartAt (coe (-w⁻¹)) = chartN.
      -- Local form: `z ↦ -z⁻¹` on `{z ≠ 0}`. Smooth at `w ≠ 0`.
      have h_chart_x : chartAt ℂ ((w : RiemannSphere)) = chartN :=
        chartAt_coe w
      have h_chart_ax :
          chartAt ℂ (antipode ((w : RiemannSphere))) = chartN := by
        rw [antipode_coe_of_ne hw]; exact chartAt_coe _
      have h_pt : (extChartAt 𝓘(ℂ, ℂ) ((w : RiemannSphere))) ((w : RiemannSphere))
          = w := by
        simp [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_coe,
              h_chart_x, chartN_apply_coe]
      rw [h_pt]
      have h_inv : AnalyticAt ℂ (fun z : ℂ => z⁻¹) w :=
        analyticOnNhd_inv w hw
      have h_an : AnalyticAt ℂ (fun z : ℂ => -z⁻¹) w := h_inv.neg
      have h_cd : ContDiffAt ℂ (ω : WithTop ℕ∞) (fun z : ℂ => -z⁻¹) w :=
        h_an.contDiffAt
      refine h_cd.congr_of_eventuallyEq ?_
      have h_open : IsOpen {z : ℂ | z ≠ 0} := isOpen_compl_singleton
      have h_mem : w ∈ {z : ℂ | z ≠ 0} := hw
      refine Filter.eventually_of_mem (h_open.mem_nhds h_mem) (fun z hz => ?_)
      show (extChartAt 𝓘(ℂ, ℂ) (antipode ((w : RiemannSphere))))
              (antipode ((extChartAt 𝓘(ℂ, ℂ) ((w : RiemannSphere))).symm z))
          = -z⁻¹
      have h_symm : (extChartAt 𝓘(ℂ, ℂ) ((w : RiemannSphere))).symm z
          = chartN.symm z := by
        simp [extChartAt, OpenPartialHomeomorph.extend,
              modelWithCornersSelf_coe_symm, h_chart_x]
      have h_apply : (extChartAt 𝓘(ℂ, ℂ) (antipode ((w : RiemannSphere))))
              (antipode (chartN.symm z))
          = chartN (antipode (chartN.symm z)) := by
        simp [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_coe,
              h_chart_ax]
      rw [h_symm, h_apply]
      exact chartN_antipode_chartN_symm hz

/-! ### Packaging as a `HolomorphicEquiv`

`antipode` is its own inverse (`antipode_antipode`), so the involution
gives both an `Equiv` and the inverse-smoothness witness for free. -/

/-- The set-level involution `antipode : RiemannSphere ≃ RiemannSphere`. -/
noncomputable def antipodeEquiv' : RiemannSphere ≃ RiemannSphere where
  toFun := antipode
  invFun := antipode
  left_inv := antipode_antipode
  right_inv := antipode_antipode

@[simp] lemma antipodeEquiv'_apply (x : RiemannSphere) :
    antipodeEquiv' x = antipode x := rfl

@[simp] lemma antipodeEquiv'_symm_apply (x : RiemannSphere) :
    antipodeEquiv'.symm x = antipode x := rfl

/-- The antipodal Möbius transformation as a biholomorphism of the
Riemann sphere. -/
noncomputable def antipodeEquiv :
    JacobianChallenge.HolomorphicEquiv RiemannSphere RiemannSphere :=
  JacobianChallenge.HolomorphicEquiv.ofEquiv antipodeEquiv'
    contMDiff_antipode
    (by
      -- `antipodeEquiv'.symm = antipode` definitionally; reuse `contMDiff_antipode`.
      change ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω antipode
      exact contMDiff_antipode)

@[simp] lemma antipodeEquiv_apply (x : RiemannSphere) :
    (antipodeEquiv : RiemannSphere → RiemannSphere) x = antipode x := rfl

end RiemannSphere

end JacobianChallenge
