/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PathPrimitiveGlobalSmoothFTC
import JacobianChallenge.Manifold.SmoothPathConnectedRiemannSphere
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option linter.unusedSectionVars false

/-! # Unconditional `PathPrimitiveAdmissibleChartCover` on `RiemannSphere`

On `RiemannSphere`, every holomorphic 1-form is zero (by the `Subsingleton
(HolomorphicOneForm RiemannSphere)` instance from
`Manifold/RiemannSphereChartSCoeffOverlap.lean`). So `chartLocalPrimitive`
of any `om` is the zero function on any chart's source, and both
`ChartLocalPrimitiveSmoothExt` and `ChartLocalPrimitiveFTC` hold trivially.

The chart cover is supplied by the standard two-chart atlas `{chartN, chartS}`:

* `chartN.target = univ : Set ℂ` (convex);
* `chartN.source = {x ≠ ∞}` (covers all finite points);
* `chartS.target = univ : Set ℂ` (convex);
* `chartS.source = {x ≠ 0}` (covers `∞`, hence the missing point of `chartN`).

This file discharges the admissibility predicate
`PathPrimitiveAdmissibleChartCover om` unconditionally on
`RiemannSphere` for every `om`.

## What this file ships

* `chartLocalPrimitiveExtend_zero_eq_zero` — the chartLocalPrimitive
  extension of the zero form is the zero function (independent of base
  manifold).
* `chartLocalPrimitive_smoothExt_RS` — `ChartLocalPrimitiveSmoothExt`
  holds unconditionally on RS for either standard chart (trivially via
  the zero-form reduction).
* `chartLocalPrimitive_FTC_RS` — `ChartLocalPrimitiveFTC` holds
  unconditionally on RS for either standard chart.
* `pathPrimitiveAdmissibleChartCover_RS` — the bundled admissibility
  predicate holds unconditionally on RS for every `om`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Set OnePoint

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **`chartLocalPrimitiveExtend (zero form) = zero function`.** -/
lemma chartLocalPrimitiveExtend_zero_eq_zero
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source) :
    chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy
        (0 : HolomorphicOneForm X)
      = fun _ : X => 0 := by
  funext x
  unfold chartLocalPrimitiveExtend
  by_cases hx : x ∈ φ.source
  · rw [dif_pos hx]
    unfold chartLocalPrimitive
    rw [complexChainPeriod_zero_right]
  · rw [dif_neg hx]

end JacobianChallenge

namespace JacobianChallenge

namespace RiemannSphere

/-- **`ChartLocalPrimitiveSmoothExt` holds for any chart at the zero
form on RS.** Reduces to ContMDiffOn of the constant-zero function. -/
lemma chartLocalPrimitive_smoothExt_zero
    (φ : OpenPartialHomeomorph RiemannSphere ℂ) (h_atlas : φ ∈ atlas ℂ RiemannSphere)
    (h_target_convex : Convex ℝ φ.target)
    (y : RiemannSphere) (hy : y ∈ φ.source) :
    ChartLocalPrimitiveSmoothExt φ h_atlas h_target_convex y hy
        (0 : HolomorphicOneForm RiemannSphere) := by
  rw [show ChartLocalPrimitiveSmoothExt φ h_atlas h_target_convex y hy
        (0 : HolomorphicOneForm RiemannSphere)
      = ContMDiffOn (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
          (chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy
            (0 : HolomorphicOneForm RiemannSphere))
          φ.source from rfl]
  rw [chartLocalPrimitiveExtend_zero_eq_zero φ h_atlas h_target_convex y hy]
  exact contMDiffOn_const

/-- **`ChartLocalPrimitiveFTC` holds for any chart at the zero form on
RS.** Both sides are zero: `(0).eval x = 0` and
`mfderiv (fun _ => 0) x = 0`. -/
lemma chartLocalPrimitive_FTC_zero
    (φ : OpenPartialHomeomorph RiemannSphere ℂ) (h_atlas : φ ∈ atlas ℂ RiemannSphere)
    (h_target_convex : Convex ℝ φ.target)
    (y : RiemannSphere) (hy : y ∈ φ.source) :
    ChartLocalPrimitiveFTC φ h_atlas h_target_convex y hy
        (0 : HolomorphicOneForm RiemannSphere) := by
  intro x _hx
  -- `(0 : HolomorphicOneForm).eval x = 0`.
  rw [HolomorphicOneForm.eval_zero]
  -- chartLocalPrimitiveExtend (zero form) = fun _ => 0.
  rw [chartLocalPrimitiveExtend_zero_eq_zero φ h_atlas h_target_convex y hy]
  -- mfderiv of constant 0 is 0.
  exact mfderiv_const.symm

/-! ## Atlas membership lemmas (helpers) -/

-- chartN_mem_atlas / chartS_mem_atlas already in
-- `SmoothPathConnectedRiemannSphere.lean`.

/-- **Convex chart targets on RS:** both `chartN` and `chartS` have
target `univ`, which is convex. -/
lemma chartN_target_convex : Convex ℝ chartN.target := by
  rw [chartN_target]
  exact convex_univ

lemma chartS_target_convex : Convex ℝ chartS.target := by
  rw [chartS_target]
  exact convex_univ

/-- **Unconditional discharge of `PathPrimitiveAdmissibleChartCover` on
`RiemannSphere`.** Uses the standard two-chart cover (chartN at finite
points, chartS at `∞`), and the zero-form simplification of the named
smoothness + FTC hypotheses. -/
theorem pathPrimitiveAdmissibleChartCover_RS
    (om : HolomorphicOneForm RiemannSphere) :
    PathPrimitiveAdmissibleChartCover om := by
  intro x
  -- Reduce om to 0 via Subsingleton.
  have hom : om = 0 := Subsingleton.elim om 0
  subst hom
  -- Pick chart and basepoint based on whether x = ∞.
  by_cases hx : x = (∞ : RiemannSphere)
  · -- x = ∞ : use chartS (covers ∞ since chartS.source = {z ≠ 0}).
    have hx_S : x ∈ chartS.source := by
      rw [chartS_source]
      -- x = ∞ ≠ (0 : ℂ : RiemannSphere).
      subst hx
      exact OnePoint.infty_ne_coe (0 : ℂ)
    -- Basepoint y := ∞ also in chartS.source.
    refine ⟨chartS, chartS_mem_atlas, chartS_target_convex,
      x, hx_S, hx_S, ?_, ?_⟩
    · exact chartLocalPrimitive_smoothExt_zero chartS chartS_mem_atlas
        chartS_target_convex x hx_S
    · exact chartLocalPrimitive_FTC_zero chartS chartS_mem_atlas
        chartS_target_convex x hx_S
  · -- x ≠ ∞ : use chartN.
    have hx_N : x ∈ chartN.source := by
      rw [chartN_source]; exact hx
    refine ⟨chartN, chartN_mem_atlas, chartN_target_convex,
      x, hx_N, hx_N, ?_, ?_⟩
    · exact chartLocalPrimitive_smoothExt_zero chartN chartN_mem_atlas
        chartN_target_convex x hx_N
    · exact chartLocalPrimitive_FTC_zero chartN chartN_mem_atlas
        chartN_target_convex x hx_N

end RiemannSphere

end JacobianChallenge

end
