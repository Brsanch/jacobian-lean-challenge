/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartContainedSmooth2SimplexFromFaces

set_option linter.unusedSectionVars false

/-! # Direct boundary-period-zero headline from raw face chart-containment

Composes `ChartContainedSmooth2Simplex.ofChartContainedFaces`
(`ChartContainedSmooth2SimplexFromFaces.lean`) with the
chart-contained 2-simplex boundary-period headline
`ChartContainedSmooth2Simplex.complexChainPeriod_boundary_eq_zero`
(`ChartContainedSmooth2Simplex.lean`) to give the **direct** statement:

```
complexChainPeriod_boundary_eq_zero_of_chartContainedFaces :
  ∀ σ basePoint ballCentre ballRadius (..),
    (per-face chart-containment on [0,1])
    → ∀ α, complexChainPeriod (Smooth2Simplex.boundary σ) α = 0
```

i.e. given a `Smooth2Simplex` with all three faces chart-contained
(source-and-ball), the boundary period against every holomorphic
1-form vanishes. No `ChartContainedSmooth2Simplex` bundling required
at the user surface — the constructor is applied internally.

This is the **trivial-subdivision case** of
`SubdivisionTelescopingTo2Simplex_named`: when no subdivision is
needed (`σ` is already chart-contained), the discharge is direct.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Direct boundary-period-zero headline.**

For a `Smooth2Simplex 𝓘(ℝ, ℂ) X` whose three faces are
chart-contained on `[0, 1]` (source-and-ball), the complex period of
its boundary against every holomorphic 1-form vanishes. -/
theorem complexChainPeriod_boundary_eq_zero_of_chartContainedFaces
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X)
    (basePoint : X) (ballCentre : ℂ) (ballRadius : ℝ)
    (radius_pos : 0 < ballRadius)
    (ball_sub_target :
      Metric.ball ballCentre ballRadius ⊆ (chartAt ℂ basePoint).target)
    (h_face0_src : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      σ.toFun (Smooth2Simplex.face0Param s) ∈ (chartAt ℂ basePoint).source)
    (h_face1_src : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      σ.toFun (Smooth2Simplex.face1Param s) ∈ (chartAt ℂ basePoint).source)
    (h_face2_src : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      σ.toFun (Smooth2Simplex.face2Param s) ∈ (chartAt ℂ basePoint).source)
    (h_face0_ball : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      (chartAt ℂ basePoint) (σ.toFun (Smooth2Simplex.face0Param s))
        ∈ Metric.ball ballCentre ballRadius)
    (h_face1_ball : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      (chartAt ℂ basePoint) (σ.toFun (Smooth2Simplex.face1Param s))
        ∈ Metric.ball ballCentre ballRadius)
    (h_face2_ball : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      (chartAt ℂ basePoint) (σ.toFun (Smooth2Simplex.face2Param s))
        ∈ Metric.ball ballCentre ballRadius)
    (α : HolomorphicOneForm X) :
    complexChainPeriod (Smooth2Simplex.boundary σ) α = 0 := by
  -- Package σ as a ChartContainedSmooth2Simplex via ofChartContainedFaces.
  set data : ChartContainedSmooth2Simplex X :=
    ChartContainedSmooth2Simplex.ofChartContainedFaces
      σ basePoint ballCentre ballRadius radius_pos ball_sub_target
      h_face0_src h_face1_src h_face2_src
      h_face0_ball h_face1_ball h_face2_ball with hdata_def
  -- The underlying σ of the package equals our σ.
  have h_σ : data.σ = σ := by
    show (ChartContainedSmooth2Simplex.ofChartContainedFaces
      σ basePoint ballCentre ballRadius radius_pos ball_sub_target
      h_face0_src h_face1_src h_face2_src
      h_face0_ball h_face1_ball h_face2_ball).σ = σ
    rfl
  -- Apply the chart-contained headline.
  have h_zero : complexChainPeriod (Smooth2Simplex.boundary data.σ) α = 0 :=
    data.complexChainPeriod_boundary_eq_zero α
  rw [h_σ] at h_zero
  exact h_zero

end JacobianChallenge
