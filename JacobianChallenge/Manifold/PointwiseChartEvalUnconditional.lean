/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PointwiseChartEvalFromFrameStability
import JacobianChallenge.Manifold.HolomorphicOneFormRealComponent
import JacobianChallenge.Manifold.ChartContainedLoopBridgeFromPointwise
import JacobianChallenge.Manifold.ComplexEvalIntegrandContinuity
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # `PointwiseChartEvalIdentity` UNCONDITIONALLY (no frame-stability)

The chart-pullback pointwise identity

```
(α.eval x : ℂ →L[ℂ] ℂ) v
  = α.localCoeff basePoint (chartPath t) * deriv chartPath t
```

at `t ∈ [0, 1]`, with `x = γ.ambient t`, `v = γ.velocity t`, holds for
**every** `ChartContainedClosedLoop` on a complex 1-manifold — no
frame-stability assumption needed.

`PointwiseChartEvalFromFrameStability.lean` proves the same identity
under the restrictive hypothesis `CotangentChartFrameStable` (every
point along the path uses the same atlas chart as `basePoint`). That
hypothesis is automatic on `RiemannSphere` for `basePoint ≠ ∞` but
fails on the complex torus and most general manifolds.

This file removes the frame-stability hypothesis by keeping the
non-trivial cotangent / tangent coordinate changes alive and showing
they cancel via the cocycle of `tangentBundleCore` together with the
`ℂ ↔ ℝ` restriction-of-scalars bridge
`tangentBundleCore_coordChange_restrictScalars_eq`
(`HolomorphicOneFormRealComponent.lean`) and the `ℂ`-linearity of
`α.toFun x : ℂ →L[ℂ] ℂ`.

As a consequence,
`ChartContainedLoopVanishingHypothesis X` becomes unconditional for
every compact connected complex 1-manifold `X`, removing the open
classical input "frame stability" from the chart-contained loop chain.

## What this file ships

* `pointwiseChartEvalIdentity_unconditional` — the headline.
* `chartContainedLoopVanishingHypothesis_holds_unconditional` —
  the composite discharge dropping frame stability.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace ChartContainedClosedLoop

/-! ## Tangent / cotangent coord-change shorthand at `x = γ.ambient t` -/

/-- The `𝓘(ℂ, ℂ)` tangent coord change from `achart y → achart x` at
`x = γ.ambient t`. -/
private noncomputable def T_yx
    (data : ChartContainedClosedLoop (X := X)) (t : ℝ) : ℂ →L[ℂ] ℂ :=
  (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
    (achart ℂ data.basePoint) (achart ℂ (data.γ.ambient t)) (data.γ.ambient t)

/-- The `𝓘(ℂ, ℂ)` tangent coord change from `achart x → achart y` at
`x = γ.ambient t`. -/
private noncomputable def T_xy
    (data : ChartContainedClosedLoop (X := X)) (t : ℝ) : ℂ →L[ℂ] ℂ :=
  (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
    (achart ℂ (data.γ.ambient t)) (achart ℂ data.basePoint) (data.γ.ambient t)

/-- **Cocycle inversion at `x`.** For any `v : ℂ`,
`T_yx (T_xy v) = v`. -/
private lemma T_yx_T_xy_apply
    (data : ChartContainedClosedLoop (X := X))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (v : ℂ) :
    T_yx data t (T_xy data t v) = v := by
  have h_src : data.γ.ambient t ∈ (chartAt ℂ data.basePoint).source :=
    data.ambient_in_source t ht
  have h_self_x : data.γ.ambient t ∈ (achart ℂ (data.γ.ambient t)).1.source := by
    show data.γ.ambient t ∈ (chartAt ℂ (data.γ.ambient t)).source
    exact mem_chart_source _ _
  have h_self_y : data.γ.ambient t ∈ (achart ℂ data.basePoint).1.source := by
    show data.γ.ambient t ∈ (chartAt ℂ data.basePoint).source
    exact h_src
  -- `coordChange_comp` with (i, j, k) = (achart x, achart y, achart x).
  have h_comp := (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange_comp
    (achart ℂ (data.γ.ambient t)) (achart ℂ data.basePoint)
    (achart ℂ (data.γ.ambient t)) (data.γ.ambient t)
    ⟨⟨h_self_x, h_self_y⟩, h_self_x⟩ v
  -- `coordChange (achart x) (achart x) x v = v` by self.
  have h_self_eq : (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
      (achart ℂ (data.γ.ambient t)) (achart ℂ (data.γ.ambient t)) (data.γ.ambient t) v = v := by
    apply (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange_self
    exact h_self_x
  show (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ data.basePoint) (achart ℂ (data.γ.ambient t)) (data.γ.ambient t)
        ((tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ (data.γ.ambient t)) (achart ℂ data.basePoint) (data.γ.ambient t) v) = v
  rw [h_comp]; exact h_self_eq

/-! ## `localCoeff` identity at `(chart y) x` -/

/-- **`localCoeff` unfolds at the chart-image of `x`** to
`α.toFun x ((T_yx) 1)`. -/
private lemma localCoeff_apply_at_chartImage
    (data : ChartContainedClosedLoop (X := X))
    (α : HolomorphicOneForm X)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    α.localCoeff data.basePoint (data.chartPath t)
      = (show ℂ →L[ℂ] ℂ from α.toFun (data.γ.ambient t)) (T_yx data t 1) := by
  have h_src : data.γ.ambient t ∈ (chartAt ℂ data.basePoint).source :=
    data.ambient_in_source t ht
  have h_symm :
      (chartAt ℂ data.basePoint).symm (data.chartPath t) = data.γ.ambient t := by
    show (chartAt ℂ data.basePoint).symm
        ((chartAt ℂ data.basePoint) (data.γ.ambient t)) = data.γ.ambient t
    exact (chartAt ℂ data.basePoint).left_inv h_src
  -- Unfold `localCoeff`.
  show ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ ((chartAt ℂ data.basePoint).symm (data.chartPath t)))
          (achart ℂ data.basePoint)
          ((chartAt ℂ data.basePoint).symm (data.chartPath t))
          (α.toFun ((chartAt ℂ data.basePoint).symm (data.chartPath t)))) 1
      = (show ℂ →L[ℂ] ℂ from α.toFun (data.γ.ambient t)) (T_yx data t 1)
  rw [h_symm]
  -- Now: cotangent.coordChange (achart x) (achart y) x (α.toFun x) 1
  --    = (α.toFun x ∘ tangent.coordChange (achart y) (achart x) x) 1
  --    = α.toFun x (T_yx data t 1).
  rw [cotangentBundleCore_coordChange_apply]
  rfl

/-! ## `deriv chartPath` identity via chain rule + bridge -/

/-- **`deriv chartPath t` is the `𝓘(ℂ, ℂ)`-tangent push-forward of
the velocity.** -/
private lemma deriv_chartPath_eq_T_xy_velocity
    (data : ChartContainedClosedLoop (X := X))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    deriv data.chartPath t = T_xy data t (data.γ.velocity t) := by
  have h_src : data.γ.ambient t ∈ (chartAt ℂ data.basePoint).source :=
    data.ambient_in_source t ht
  have h_chart_atlas : (chartAt ℂ data.basePoint : OpenPartialHomeomorph X ℂ)
      ∈ atlas ℂ X := chart_mem_atlas ℂ data.basePoint
  -- Chain rule via SmoothPath.mfderiv_chart_comp_ambient_apply_one.
  have h_chain :
      (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ))
        ((chartAt ℂ data.basePoint : X → ℂ) ∘ data.γ.ambient) t : ℝ →L[ℝ] _)
            (1 : ℝ)
        = (mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ))
            (chartAt ℂ data.basePoint : X → ℂ) (data.γ.ambient t) : ℂ →L[ℝ] _)
              (data.γ.velocity t) :=
    SmoothPath.mfderiv_chart_comp_ambient_apply_one data.γ h_chart_atlas h_src
  -- `mfderiv chartAt y x = tangentCoordChange 𝓘(ℝ, ℂ) x y x`.
  rw [mfderiv_chartAt_eq_tangentCoordChange (I := 𝓘(ℝ, ℂ)) h_src] at h_chain
  -- `tangentCoordChange` is shorthand for `tangentBundleCore.coordChange`.
  -- Bridge: 𝓘(ℝ, ℂ) tangent coord change = restrictScalars ℝ of 𝓘(ℂ, ℂ) version.
  have h_bridge :
      (tangentBundleCore 𝓘(ℝ, ℂ) X).coordChange (achart ℂ (data.γ.ambient t))
          (achart ℂ data.basePoint) (data.γ.ambient t)
        = ((tangentBundleCore 𝓘(ℂ, ℂ) X).coordChange
            (achart ℂ (data.γ.ambient t)) (achart ℂ data.basePoint)
            (data.γ.ambient t)).restrictScalars ℝ :=
    tangentBundleCore_coordChange_restrictScalars_eq
      (i := achart ℂ (data.γ.ambient t)) (j := achart ℂ data.basePoint)
      (mem_chart_source _ _) h_src
  -- Reduce h_chain to `T_xy data t (γ.velocity t)`.
  have h_chain' :
      (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ))
        ((chartAt ℂ data.basePoint : X → ℂ) ∘ data.γ.ambient) t : ℝ →L[ℝ] _)
            (1 : ℝ)
        = T_xy data t (data.γ.velocity t) := by
    rw [h_chain]
    show (tangentBundleCore 𝓘(ℝ, ℂ) X).coordChange
            (achart ℂ (data.γ.ambient t)) (achart ℂ data.basePoint)
            (data.γ.ambient t) (data.γ.velocity t)
        = T_xy data t (data.γ.velocity t)
    rw [h_bridge]
    rfl
  -- Bridge `(mfderiv ... )(1) = deriv chartPath t`.
  have h_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) data.chartPath t :=
    data.chartPath_mdifferentiableAt_of_unitInterval ht
  have h_diff : DifferentiableAt ℝ data.chartPath t := h_mdiff.differentiableAt
  have h_mfderiv_eq_fderiv :
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) data.chartPath t : ℝ →L[ℝ] ℂ)
        = fderiv ℝ data.chartPath t :=
    mfderiv_eq_fderiv (f := data.chartPath) (x := t)
  have h_deriv_eq :
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
          ((chartAt ℂ data.basePoint : X → ℂ) ∘ data.γ.ambient) t : ℝ →L[ℝ] ℂ)
            (1 : ℝ) = deriv data.chartPath t := by
    -- `chartPath` is by definition `chartAt y ∘ γ.ambient`.
    show (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) data.chartPath t : ℝ →L[ℝ] ℂ) (1 : ℝ)
        = deriv data.chartPath t
    rw [h_mfderiv_eq_fderiv]
    exact h_diff.hasFDerivAt.hasDerivAt.deriv
  -- Combine.
  rw [← h_deriv_eq, h_chain']

/-! ## Headline: `PointwiseChartEvalIdentity` UNCONDITIONAL -/

/-- **`PointwiseChartEvalIdentity` UNCONDITIONAL** — no frame stability
required. Proves
`(α.eval x : ℂ →L[ℂ] ℂ) v = α.localCoeff basePoint (chartPath t) * deriv chartPath t`
for every `t ∈ [0, 1]`, with `x = γ.ambient t`, `v = γ.velocity t`.

The proof combines:
* `localCoeff_apply_at_chartImage` — expresses `localCoeff y (chart_y x)`
  as `α.toFun x (T_yx 1)` via `cotangentBundleCore_coordChange_apply`.
* `deriv_chartPath_eq_T_xy_velocity` — expresses `deriv chartPath t`
  as `T_xy v` via the chain rule + the `ℝ ↔ ℂ` restrictScalars bridge.
* `ℂ`-linearity of `α.toFun x` to pull the scalar `T_xy v` out, and of
  `T_yx` to absorb it: `T_xy v • (T_yx 1) = T_yx (T_xy v)`.
* `T_yx_T_xy_apply` — the cocycle identity `T_yx (T_xy v) = v`. -/
theorem pointwiseChartEvalIdentity_unconditional
    (data : ChartContainedClosedLoop (X := X))
    (α : HolomorphicOneForm X) :
    PointwiseChartEvalIdentity data α := by
  intro t ht
  rw [localCoeff_apply_at_chartImage data α ht]
  rw [deriv_chartPath_eq_T_xy_velocity data ht]
  -- Goal: α.eval x v = α.toFun x (T_yx 1) * T_xy v
  -- (where x = γ.ambient t, v = γ.velocity t).
  have h_eval :
      (α.eval (data.γ.ambient t) : ℂ →L[ℂ] ℂ)
        = α.toFun (data.γ.ambient t) := rfl
  show ((α.eval (data.γ.ambient t) : ℂ →L[ℂ] ℂ) (data.γ.velocity t) : ℂ)
    = (show ℂ →L[ℂ] ℂ from α.toFun (data.γ.ambient t)) (T_yx data t 1)
        * T_xy data t (data.γ.velocity t)
  rw [h_eval]
  -- Pull the scalar `T_xy v` out of `α.toFun x : ℂ →L[ℂ] ℂ` via map_smul.
  have h_smul_pull :
      (show ℂ →L[ℂ] ℂ from α.toFun (data.γ.ambient t)) (T_yx data t 1)
        * T_xy data t (data.γ.velocity t)
        = (show ℂ →L[ℂ] ℂ from α.toFun (data.γ.ambient t))
            ((T_xy data t (data.γ.velocity t)) • (T_yx data t 1)) := by
    rw [ContinuousLinearMap.map_smul]
    show (show ℂ →L[ℂ] ℂ from α.toFun (data.γ.ambient t)) (T_yx data t 1)
            * T_xy data t (data.γ.velocity t)
        = (T_xy data t (data.γ.velocity t))
            • ((show ℂ →L[ℂ] ℂ from α.toFun (data.γ.ambient t)) (T_yx data t 1))
    rw [smul_eq_mul, mul_comm]
  rw [h_smul_pull]
  -- Absorb the scalar into T_yx (ℂ-linear): `c • (T_yx 1) = T_yx c`.
  have h_T_yx_smul :
      (T_xy data t (data.γ.velocity t)) • (T_yx data t 1)
        = T_yx data t (T_xy data t (data.γ.velocity t)) := by
    rw [← (T_yx data t).map_smul]
    show (T_yx data t) ((T_xy data t (data.γ.velocity t)) • (1 : ℂ))
        = (T_yx data t) (T_xy data t (data.γ.velocity t))
    rw [smul_eq_mul, mul_one]
  rw [h_T_yx_smul]
  -- Apply cocycle: T_yx (T_xy v) = v. The rewrite closes the goal.
  rw [T_yx_T_xy_apply data ht]

/-! ## Composite: `ChartContainedLoopVanishingHypothesis` UNCONDITIONAL -/

/-- **`ChartContainedLoopVanishingHypothesis X` UNCONDITIONAL** — drops
the frame-stability hypothesis from
`chartContainedLoopVanishingHypothesis_of_frameStable`. -/
theorem chartContainedLoopVanishingHypothesis_holds_unconditional :
    ChartContainedLoopVanishingHypothesis (X := X) :=
  chartContainedLoopVanishingHypothesis_from_pointwise_only
    (fun data α => pointwiseChartEvalIdentity_unconditional data α)

end ChartContainedClosedLoop

end JacobianChallenge

end
