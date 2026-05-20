/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasAdmissibleChartCoverClass

set_option linter.unusedSectionVars false

/-! # `HasConvexTargetChartCover` typeclass + Subsingleton-ω discharge

Decouples the **chart-cover** content of `HasAdmissibleChartCover`
from the **smoothness/FTC** content:

* `HasConvexTargetChartCover X` — every point of `X` lies in some
  chart `φ ∈ atlas ℂ X` with convex target.
* Under `[HasConvexTargetChartCover X]` + `[Subsingleton
  (HolomorphicOneForm X)]`, `HasAdmissibleChartCover X` is automatic
  (every om = 0 ⇒ chartLocalPrimitive = 0 ⇒ smooth + FTC trivially).

This factoring lets concrete X-instances supply just the chart cover,
without re-proving the zero-form smoothness/FTC each time.

## What this file ships

* `HasConvexTargetChartCover` — the chart-cover typeclass.
* `instance : HasConvexTargetChartCover RiemannSphere` — chartN + chartS.
* `instHasAdmissibleChartCoverOfConvexCoverAndSubsingletonOmega` — the
  combined instance.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open OnePoint

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **`HasConvexTargetChartCover X`**: every point lies in some chart
of `atlas ℂ X` with convex target. -/
class HasConvexTargetChartCover : Prop where
  /-- Per-point witness. -/
  cover : ∀ x : X, ∃ (φ : OpenPartialHomeomorph X ℂ),
    φ ∈ atlas ℂ X ∧ Convex ℝ φ.target ∧ x ∈ φ.source

/-- **RS instance**: `HasConvexTargetChartCover RiemannSphere` via the
standard two-chart atlas `{chartN, chartS}`. -/
instance : HasConvexTargetChartCover RiemannSphere := by
  refine ⟨?_⟩
  intro x
  by_cases hx : x = (∞ : RiemannSphere)
  · refine ⟨RiemannSphere.chartS, RiemannSphere.chartS_mem_atlas,
      RiemannSphere.chartS_target_convex, ?_⟩
    rw [RiemannSphere.chartS_source]; subst hx
    exact OnePoint.infty_ne_coe (0 : ℂ)
  · refine ⟨RiemannSphere.chartN, RiemannSphere.chartN_mem_atlas,
      RiemannSphere.chartN_target_convex, ?_⟩
    rw [RiemannSphere.chartN_source]; exact hx

variable {X}

/-- **Combined: `HasAdmissibleChartCover X` from `[HasConvexTargetChartCover X]`
+ `[Subsingleton (HolomorphicOneForm X)]`.** Every `om = 0`, so
chartLocalPrimitive of any om is the zero function, and both named
hypotheses (`ChartLocalPrimitiveSmoothExt` + `ChartLocalPrimitiveFTC`)
hold trivially via the zero-form simplification from
`Manifold/PathPrimitiveAdmissibleRiemannSphere.lean`. -/
instance instHasAdmissibleChartCoverOfConvexCoverAndSubsingletonOmega
    [HasConvexTargetChartCover X]
    [Subsingleton (HolomorphicOneForm X)] :
    HasAdmissibleChartCover X := by
  refine ⟨fun om => ?_⟩
  intro x
  obtain ⟨φ, h_atlas, h_target_convex, hx⟩ :=
    HasConvexTargetChartCover.cover x
  -- om = 0 by Subsingleton.
  have hom : om = 0 := Subsingleton.elim om 0
  subst hom
  refine ⟨φ, h_atlas, h_target_convex, x, hx, hx, ?_, ?_⟩
  · -- ChartLocalPrimitiveSmoothExt for zero form: ContMDiffOn constant 0.
    rw [show ChartLocalPrimitiveSmoothExt φ h_atlas h_target_convex x hx
          (0 : HolomorphicOneForm X)
        = ContMDiffOn (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
            (chartLocalPrimitiveExtend φ h_atlas h_target_convex x hx
              (0 : HolomorphicOneForm X))
            φ.source from rfl]
    rw [chartLocalPrimitiveExtend_zero_eq_zero φ h_atlas h_target_convex x hx]
    exact contMDiffOn_const
  · -- ChartLocalPrimitiveFTC for zero form: both sides are 0.
    intro y _hy
    rw [HolomorphicOneForm.eval_zero,
      chartLocalPrimitiveExtend_zero_eq_zero φ h_atlas h_target_convex x hx]
    exact mfderiv_const.symm

end JacobianChallenge

end
