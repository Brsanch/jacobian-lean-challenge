/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartContainedLoopBridgeFromPointwise
import JacobianChallenge.Manifold.ComplexEvalIntegrandContinuity
import JacobianChallenge.Manifold.SmoothPathChartCompat
import JacobianChallenge.Manifold.HolomorphicOneFormChartCoeff
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

set_option linter.unusedSectionVars false

/-! # `PointwiseChartEvalIdentity` from chart-frame stability

Under the frame-stability hypothesis
`chartAt ℂ (γ.ambient t) = chartAt ℂ basePoint` for every `t ∈ [0, 1]`,
the cotangent-bundle `coordChange` in `localCoeff` collapses to the
identity (`cotangentBundleCore_coordChange_self`) and the
`mfderiv (chart basePoint)` at `γ.ambient t` collapses to the identity
(`mfderiv_chartAt_eq_tangentCoordChange` + `tangentCoordChange_self`).
Combined with `ℂ`-linearity of `α.toFun (γ.ambient t) : ℂ →L[ℂ] ℂ` and
the existing chain rule
`SmoothPath.mfderiv_chart_comp_ambient_apply_one`, this discharges
`PointwiseChartEvalIdentity` for any chart-contained closed loop on a
manifold where the frame is stable.

Frame stability is automatic on `RiemannSphere` for paths in
`chartN.source`: `chartAt ℂ x = chartN` for every `x ≠ ∞`, so any
`ChartContainedClosedLoop` with `basePoint ≠ ∞` and image in
`chartN.source` satisfies frame stability.

## What this file ships

* `CotangentChartFrameStable` — the named frame-stability predicate.
* `pointwiseChartEvalIdentity_of_frameStable` — discharge of
  `PointwiseChartEvalIdentity` under frame stability.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex MeasureTheory

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace ChartContainedClosedLoop

/-- **Cotangent-frame stability hypothesis.** For all `t ∈ [0, 1]`,
the canonical chart at `γ.ambient t` equals `chartAt ℂ basePoint` as
`OpenPartialHomeomorph`s.

Automatic on `RiemannSphere` for paths in `chartN.source`. -/
def CotangentChartFrameStable (data : ChartContainedClosedLoop (X := X)) : Prop :=
  ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
    chartAt ℂ (data.γ.ambient t) = chartAt ℂ data.basePoint

/-- Under frame stability, `achart ℂ (γ.ambient t) = achart ℂ basePoint`
as atlas elements. -/
private lemma achart_eq_basePoint_of_frameStable
    (data : ChartContainedClosedLoop (X := X))
    (h_stable : CotangentChartFrameStable data)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    achart ℂ (data.γ.ambient t) = achart ℂ data.basePoint := by
  apply Subtype.ext
  show (achart ℂ (data.γ.ambient t)).1 = (achart ℂ data.basePoint).1
  rw [achart_val, achart_val]
  exact h_stable t ht

/-- Under frame stability, `localCoeff α basePoint (chart basePoint x) =
(α.toFun x : ℂ →L[ℂ] ℂ) 1` (the cotangent `coordChange` collapses to
identity). The ascription `α.toFun x : ℂ →L[ℂ] ℂ` is needed because
`α.toFun x : CotangentSpace ...` is a type synonym that Lean does not
auto-unfold for function application. -/
private lemma localCoeff_eq_of_frameStable
    (data : ChartContainedClosedLoop (X := X))
    (α : HolomorphicOneForm X)
    (h_stable : CotangentChartFrameStable data)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    α.localCoeff data.basePoint (data.chartPath t)
      = (show ℂ →L[ℂ] ℂ from α.toFun (data.γ.ambient t)) (1 : ℂ) := by
  have h_src : data.γ.ambient t ∈ (chartAt ℂ data.basePoint).source :=
    data.ambient_in_source t ht
  have h_symm_apply :
      (chartAt ℂ data.basePoint).symm
        ((chartAt ℂ data.basePoint) (data.γ.ambient t))
        = data.γ.ambient t :=
    (chartAt ℂ data.basePoint).left_inv h_src
  -- Unfold `localCoeff` and `chartPath`.
  show (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ ((chartAt ℂ data.basePoint).symm
            ((chartAt ℂ data.basePoint) (data.γ.ambient t))))
          (achart ℂ data.basePoint)
          ((chartAt ℂ data.basePoint).symm
            ((chartAt ℂ data.basePoint) (data.γ.ambient t)))
          (α.toFun ((chartAt ℂ data.basePoint).symm
            ((chartAt ℂ data.basePoint) (data.γ.ambient t))))) (1 : ℂ))
      = (show ℂ →L[ℂ] ℂ from α.toFun (data.γ.ambient t)) (1 : ℂ)
  rw [h_symm_apply]
  rw [achart_eq_basePoint_of_frameStable data h_stable ht]
  have h_base : data.γ.ambient t ∈
      (cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ data.basePoint) := by
    show data.γ.ambient t ∈ (achart ℂ data.basePoint).1.source
    rw [achart_val]
    exact h_src
  rw [cotangentBundleCore_coordChange_self _ h_base]

/-- Under frame stability, `mfderiv (chart basePoint) (γ.ambient t) =
ContinuousLinearMap.id ℝ ℂ` (the tangentCoordChange collapses to identity). -/
private lemma mfderiv_chart_eq_id_of_frameStable
    (data : ChartContainedClosedLoop (X := X))
    (h_stable : CotangentChartFrameStable data)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) (chartAt ℂ data.basePoint : X → ℂ)
        (data.γ.ambient t))
      = ContinuousLinearMap.id ℝ ℂ := by
  have h_src : data.γ.ambient t ∈ (chartAt ℂ data.basePoint).source :=
    data.ambient_in_source t ht
  -- mfderiv (chartAt H y) x = tangentCoordChange I x y x.
  rw [mfderiv_chartAt_eq_tangentCoordChange (I := 𝓘(ℝ, ℂ)) h_src]
  -- tangentCoordChange I x y x = tangentBundleCore.coordChange (achart x) (achart y) x.
  show (tangentBundleCore (𝓘(ℝ, ℂ)) X).coordChange
      (achart ℂ (data.γ.ambient t)) (achart ℂ data.basePoint)
      (data.γ.ambient t) = ContinuousLinearMap.id ℝ ℂ
  -- Under frame stability, achart x = achart basePoint.
  rw [achart_eq_basePoint_of_frameStable data h_stable ht]
  -- coordChange (achart basePoint) (achart basePoint) x v = v.
  ext v
  apply tangentCoordChange_self (I := (𝓘(ℝ, ℂ))) (x := data.basePoint)
    (z := data.γ.ambient t) (v := v)
  -- `data.γ.ambient t ∈ (extChartAt 𝓘(ℝ, ℂ) basePoint).source`.
  rw [extChartAt_source]
  exact h_src

/-- **Discharge of `PointwiseChartEvalIdentity` under frame stability.**

Under `CotangentChartFrameStable`, the pointwise chart-pullback identity

```
(α.eval (γ.ambient t)) (γ.velocity t)
  = α.localCoeff basePoint (chartPath t) · deriv chartPath t
```

holds for every `t ∈ [0, 1]`. The proof combines the chain rule for
`chart ∘ γ.ambient`, the collapsing of the cotangent/tangent coord
changes under frame stability, and ℂ-linearity of
`α.toFun x : ℂ →L[ℂ] ℂ`. -/
theorem pointwiseChartEvalIdentity_of_frameStable
    (data : ChartContainedClosedLoop (X := X))
    (α : HolomorphicOneForm X)
    (h_stable : CotangentChartFrameStable data) :
    PointwiseChartEvalIdentity data α := by
  intro t ht
  -- Step 1: localCoeff = α.toFun (γ.ambient t) 1.
  rw [localCoeff_eq_of_frameStable data α h_stable ht]
  -- Step 2: deriv chartPath t = γ.velocity t.
  -- chain rule: deriv chartPath t = mfderiv chartPath t (1 : ℝ).
  have h_src : data.γ.ambient t ∈ (chartAt ℂ data.basePoint).source :=
    data.ambient_in_source t ht
  have h_chart_atlas : (chartAt ℂ data.basePoint : OpenPartialHomeomorph X ℂ)
      ∈ atlas ℂ X := chart_mem_atlas ℂ data.basePoint
  -- Chain rule from `SmoothPath.mfderiv_chart_comp_ambient_apply_one`.
  -- LHS becomes ` (mfderiv chart) (γ.ambient t) (γ.velocity t)` after chain rule.
  have h_chain :
      (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ))
        ((chartAt ℂ data.basePoint : X → ℂ) ∘ data.γ.ambient) t : ℝ →L[ℝ] _)
          (1 : ℝ)
      = (mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) (chartAt ℂ data.basePoint : X → ℂ)
          (data.γ.ambient t) : ℂ →L[ℝ] _) (data.γ.velocity t) :=
    SmoothPath.mfderiv_chart_comp_ambient_apply_one data.γ h_chart_atlas h_src
  -- Under frame stability, the chart's mfderiv is identity.
  rw [mfderiv_chart_eq_id_of_frameStable data h_stable ht] at h_chain
  -- The RHS of `h_chain` is now `(ContinuousLinearMap.id ℝ ℂ) (γ.velocity t)`,
  -- which equals `γ.velocity t` definitionally.
  change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
      ((chartAt ℂ data.basePoint : X → ℂ) ∘ data.γ.ambient) t : ℝ →L[ℝ] _)
        (1 : ℝ) = data.γ.velocity t at h_chain
  -- `chartPath` equals `chart ∘ γ.ambient` definitionally.
  -- Compute `deriv chartPath t` as `mfderiv chartPath t (1 : ℝ)`, then
  -- via h_chain conclude `deriv chartPath t = γ.velocity t`.
  -- (`MDifferentiableAt → DifferentiableAt → deriv = hasDerivAt.deriv`.)
  have h_chart_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) data.chartPath t :=
    data.chartPath_mdifferentiableAt_of_unitInterval ht
  have h_chart_diff : DifferentiableAt ℝ data.chartPath t :=
    h_chart_mdiff.differentiableAt
  -- `mfderiv ... = fderiv ...` (both equal to the unique tangent map in this model).
  -- Compose via `MDifferentiableAt → HasDerivAt`.
  have h_hasDeriv : HasDerivAt data.chartPath (deriv data.chartPath t) t :=
    h_chart_diff.hasDerivAt
  -- `deriv chartPath t = mfderiv chartPath t (1 : ℝ)` via mfderiv = fderiv on (ℝ → ℂ).
  have h_velocity_eq_deriv :
      deriv data.chartPath t = data.γ.velocity t := by
    -- `deriv chartPath t = (mfderiv (chartPath)) t (1 : ℝ) = h_chain RHS`.
    have h_deriv_apply :
        (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ))
            ((chartAt ℂ data.basePoint : X → ℂ) ∘ data.γ.ambient) t : ℝ →L[ℝ] _)
              (1 : ℝ) = deriv data.chartPath t := by
      have h_mfderiv_eq_fderiv :
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) data.chartPath t : ℝ →L[ℝ] ℂ)
            = fderiv ℝ data.chartPath t :=
        mfderiv_eq_fderiv (f := data.chartPath) (x := t)
      show (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) data.chartPath t : ℝ →L[ℝ] ℂ) (1 : ℝ)
        = deriv data.chartPath t
      rw [h_mfderiv_eq_fderiv]
      exact h_chart_diff.hasFDerivAt.hasDerivAt.deriv
    -- Now: h_chain says (mfderiv chartPath t)(1) = γ.velocity t.
    -- And h_deriv_apply says (mfderiv chartPath t)(1) = deriv chartPath t.
    -- So deriv chartPath t = γ.velocity t.
    rw [← h_deriv_apply, h_chain]
  -- Step 3: combine via ℂ-linearity of α.toFun.
  -- Goal: α.eval x v = (α.toFun x 1) * deriv chartPath t.
  -- With v = γ.velocity t = deriv chartPath t and α.eval = α.toFun:
  show ((α.eval (data.γ.ambient t) : (ℂ →L[ℂ] ℂ)) (data.γ.velocity t) : ℂ)
      = (show ℂ →L[ℂ] ℂ from α.toFun (data.γ.ambient t)) 1 * deriv data.chartPath t
  -- α.eval = α.toFun (definitionally via `eval` def in HolomorphicOneFormRealification).
  have h_eval :
      (α.eval (data.γ.ambient t) : ℂ →L[ℂ] ℂ)
        = α.toFun (data.γ.ambient t) := rfl
  rw [h_eval]
  rw [h_velocity_eq_deriv]
  -- Now: α.toFun x (γ.velocity t) = (α.toFun x 1) * γ.velocity t.
  -- ℂ-linearity: `(f : ℂ →L[ℂ] ℂ) v = v * f 1`.
  show (show ℂ →L[ℂ] ℂ from α.toFun (data.γ.ambient t)) (data.γ.velocity t)
      = (show ℂ →L[ℂ] ℂ from α.toFun (data.γ.ambient t)) 1
        * data.γ.velocity t
  -- v = v • 1 in ℂ; map_smul gives the identity.
  have h_smul :
      data.γ.velocity t • (1 : ℂ) = data.γ.velocity t := by
    rw [smul_eq_mul, mul_one]
  conv_lhs => rw [← h_smul]
  rw [ContinuousLinearMap.map_smul, smul_eq_mul, mul_comm]

/-! ## Composite: `ChartContainedLoopVanishingHypothesis` from frame stability -/

/-- **Composite headline.** Under the assumption that every
`ChartContainedClosedLoop` on `X` is frame-stable, the
`ChartContainedLoopVanishingHypothesis` holds.

Combines:
* `pointwiseChartEvalIdentity_of_frameStable` (this file).
* `complexEvalIntegrand_continuousOn` (from
  `ComplexEvalIntegrandContinuity.lean`).
* `chartContainedLoopVanishingHypothesis_from_pointwise_only` (the
  composite from `ComplexEvalIntegrandContinuity.lean`).

Frame stability is the **single remaining classical input**. It is
automatic on `RiemannSphere` for loops in `chartN.source` (where the
achart is uniformly `chartN`), making this composite useful for the
genus-0 closure on `RS`. On general manifolds, frame stability holds
within "connected components of constant chart"; the global discharge
of `ChartContainedLoopVanishingHypothesis` for an arbitrary
chart-contained loop on an arbitrary manifold remains a subdivision
step (split the loop into pieces inside connected chart-constant
components). -/
theorem chartContainedLoopVanishingHypothesis_of_frameStable
    (h_stable : ∀ data : ChartContainedClosedLoop (X := X),
      CotangentChartFrameStable data) :
    ChartContainedLoopVanishingHypothesis (X := X) :=
  chartContainedLoopVanishingHypothesis_from_pointwise_only
    (fun data α => pointwiseChartEvalIdentity_of_frameStable data α (h_stable data))

end ChartContainedClosedLoop

end JacobianChallenge

end
