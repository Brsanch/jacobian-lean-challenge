/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PathPrimitiveAdmissibleRiemannSphere

set_option linter.unusedSectionVars false

/-! # `HasAdmissibleChartCover` typeclass

Wraps the `PathPrimitiveAdmissibleChartCover` predicate as a typeclass
over all `om : HolomorphicOneForm X`. Discharging the class once
discharges admissibility uniformly for every form.

## What this file ships

* `HasAdmissibleChartCover X` — the class.
* `instance : HasAdmissibleChartCover RiemannSphere` — RS instance from
  the unconditional discharge in
  `Manifold/PathPrimitiveAdmissibleRiemannSphere.lean`.
* `pathPrimitive_contMDiff_of_HasAdmissibleChartCover` — class-driven
  global `ContMDiff ω`.
* `pathPrimitive_eval_eq_mfderiv_of_HasAdmissibleChartCover` —
  class-driven global FTC.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **`HasAdmissibleChartCover X`**: typeclass capturing that
`PathPrimitiveAdmissibleChartCover om` holds uniformly for every
`om : HolomorphicOneForm X`. -/
class HasAdmissibleChartCover : Prop where
  /-- Admissibility for every holomorphic 1-form. -/
  admit : ∀ (om : HolomorphicOneForm X), PathPrimitiveAdmissibleChartCover om

/-- **RS instance**: `HasAdmissibleChartCover RiemannSphere` from the
unconditional `pathPrimitiveAdmissibleChartCover_RS`. -/
instance : HasAdmissibleChartCover RiemannSphere :=
  ⟨fun om => RiemannSphere.pathPrimitiveAdmissibleChartCover_RS om⟩

variable {X}

/-- **Class-driven global `ContMDiff ω` of `pathPrimitive`.** -/
theorem pathPrimitive_contMDiff_of_HasAdmissibleChartCover
    [HasAdmissibleChartCover X]
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀) :
    ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (pathPrimitive h_conn x₀ om) :=
  pathPrimitive_contMDiff_of_admissible h_conn x₀ om h_loop
    (HasAdmissibleChartCover.admit om)

/-- **Class-driven global FTC for `pathPrimitive`.** -/
theorem pathPrimitive_eval_eq_mfderiv_of_HasAdmissibleChartCover
    [HasAdmissibleChartCover X]
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (x : X) :
    om.eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
      (pathPrimitive h_conn x₀ om) x :=
  pathPrimitive_eval_eq_mfderiv_of_admissible h_conn x₀ om h_loop
    (HasAdmissibleChartCover.admit om) x

end JacobianChallenge

end
