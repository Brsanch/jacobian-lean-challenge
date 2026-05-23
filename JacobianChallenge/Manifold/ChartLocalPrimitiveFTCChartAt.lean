/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartLocalPrimitiveMfderivChainRule
import JacobianChallenge.Manifold.PathPrimitiveLocalSmoothFTCNamed
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # D5 + chip-D headline: `ChartLocalPrimitiveFTC` at `chartAt ℂ y` UNCONDITIONAL

Completes the chip-D arc. D4 gave the closed-form chain-rule identity

  `mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartLocalPrimitiveExtend (chartAt ℂ y) … y … om) x
     = (toSpanSingleton ℂ (om.localCoeff y ((chartAt ℂ y) x))).comp
         (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ y) x)`

at every `x ∈ (chartAt ℂ y).source`. This file matches the RHS with
`om.eval x` via the **chart-cotangent pointwise identity**

  `om.eval x = (toSpanSingleton ℂ (om.localCoeff y ((chartAt ℂ y) x))).comp
                 (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ y) x)`

which is the same algebraic content as chip B2
(`pointwiseChartEval_path`) applied **pointwise** — without a smooth
path, just `x` and the chart cocycle. The proof mirrors B2: identify
`localCoeff y (φ x) = (om.toFun x) (T_yx 1)` via `cotangentBundleCore_coordChange_apply`,
identify `mfderiv (chartAt y) x = T_xy` via `mfderiv_chartAt_eq_tangentCoordChange`,
then close by ℂ-linearity of `om.toFun x` + ℂ-linearity of `T_yx` +
the cocycle `T_yx ∘ T_xy = id` at `x`.

Combined with D4, this discharges the named hypothesis
`ChartLocalPrimitiveFTC` at `chartAt ℂ y` unconditionally (modulo the
convex chart-target hypothesis already required by the definition).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Pointwise tangent / cotangent coord-change shorthand at a fixed `x` -/

/-- The `𝓘(ℂ, ℂ)` tangent coord change `achart y → achart x` at `x`. -/
private noncomputable def tangentYToX (y x : X) : ℂ →L[ℂ] ℂ :=
  (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
    (achart ℂ y) (achart ℂ x) x

/-- The `𝓘(ℂ, ℂ)` tangent coord change `achart x → achart y` at `x`. -/
private noncomputable def tangentXToY (y x : X) : ℂ →L[ℂ] ℂ :=
  (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
    (achart ℂ x) (achart ℂ y) x

/-- **Cocycle inversion at `x`.** For any `v : ℂ`,
`tangentYToX y x (tangentXToY y x v) = v`, when `x ∈ (chartAt ℂ y).source`. -/
private lemma tangentYToX_tangentXToY_apply
    {y x : X} (h_src : x ∈ (chartAt ℂ y).source) (v : ℂ) :
    tangentYToX y x (tangentXToY y x v) = v := by
  have h_self_x : x ∈ (achart ℂ x).1.source := by
    show x ∈ (chartAt ℂ x).source; exact mem_chart_source _ _
  have h_self_y : x ∈ (achart ℂ y).1.source := by
    show x ∈ (chartAt ℂ y).source; exact h_src
  have h_comp := (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange_comp
    (achart ℂ x) (achart ℂ y) (achart ℂ x) x
    ⟨⟨h_self_x, h_self_y⟩, h_self_x⟩ v
  have h_self_eq : (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
      (achart ℂ x) (achart ℂ x) x v = v := by
    apply (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange_self
    exact h_self_x
  show (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y) (achart ℂ x) x
        ((tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ x) (achart ℂ y) x v) = v
  rw [h_comp]; exact h_self_eq

/-! ## `localCoeff` unfolds at `(chart y) x` -/

/-- **`localCoeff` at the chart-image of `x`** equals
`(om.toFun x) (tangentYToX y x 1)`. -/
private lemma localCoeff_apply_at_chartImage
    (om : HolomorphicOneForm X) {y x : X}
    (h_src : x ∈ (chartAt ℂ y).source) :
    om.localCoeff y ((chartAt ℂ y) x)
      = (show ℂ →L[ℂ] ℂ from om.toFun x) (tangentYToX y x 1) := by
  have h_symm : (chartAt ℂ y).symm ((chartAt ℂ y) x) = x :=
    (chartAt ℂ y).left_inv h_src
  show ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ ((chartAt ℂ y).symm ((chartAt ℂ y) x)))
          (achart ℂ y)
          ((chartAt ℂ y).symm ((chartAt ℂ y) x))
          (om.toFun ((chartAt ℂ y).symm ((chartAt ℂ y) x)))) 1
      = (show ℂ →L[ℂ] ℂ from om.toFun x) (tangentYToX y x 1)
  rw [h_symm]
  rw [cotangentBundleCore_coordChange_apply]
  rfl

/-! ## `mfderiv (chartAt ℂ y) x = tangentXToY y x` -/

/-- **mfderiv of `chartAt ℂ y` at `x ∈ (chartAt ℂ y).source`** equals
`tangentXToY y x` (= `coordChange (achart x) (achart y) x`). Direct
specialization of `mfderiv_chartAt_eq_tangentCoordChange` at
`I := 𝓘(ℂ, ℂ)`. -/
private lemma mfderiv_chartAt_eq_tangentXToY
    {y x : X} (h_src : x ∈ (chartAt ℂ y).source) :
    mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (chartAt ℂ y : X → ℂ) x
      = tangentXToY y x :=
  mfderiv_chartAt_eq_tangentCoordChange (I := 𝓘(ℂ, ℂ)) h_src

/-! ## Headline: chart-cotangent pointwise identity (D5) -/

/-- **D5: chart-cotangent pointwise identity at `x ∈ (chartAt ℂ y).source`.**

  `om.eval x = (toSpanSingleton ℂ (om.localCoeff y ((chartAt ℂ y) x))).comp
                 (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ y) x)`

Same algebraic content as `pointwiseChartEval_path` (chip B2), but
**pointwise** — no smooth path needed, only `x` and the chart cocycle. -/
theorem om_eval_eq_chartCoord_smulRight_mfderiv_chartAt
    (om : HolomorphicOneForm X) {y x : X}
    (h_src : x ∈ (chartAt ℂ y).source) :
    (om.eval x : ℂ →L[ℂ] ℂ)
      = (ContinuousLinearMap.toSpanSingleton ℂ
            (om.localCoeff y ((chartAt ℂ y) x))).comp
          (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (chartAt ℂ y : X → ℂ) x) := by
  -- Prove the CLM equality pointwise. The LHS lives in the cotangent
  -- space at `x`, which is defeq to `ℂ →L[ℂ] ℂ` but Lean's `ext` needs
  -- the unfolded shape.
  apply ContinuousLinearMap.ext
  intro v
  show (om.eval x : ℂ →L[ℂ] ℂ) v
    = (ContinuousLinearMap.toSpanSingleton ℂ
          (om.localCoeff y ((chartAt ℂ y) x)))
        ((mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (chartAt ℂ y : X → ℂ) x) v)
  rw [ContinuousLinearMap.toSpanSingleton_apply,
      mfderiv_chartAt_eq_tangentXToY h_src,
      localCoeff_apply_at_chartImage om h_src]
  -- Goal: (om.eval x) v = (tangentXToY y x) v • (om.toFun x) (tangentYToX y x 1)
  -- Strategy: rewrite om.eval x to om.toFun x, then close by chart-cotangent
  -- algebra applied to om.toFun x.
  have h_eval : (om.eval x : ℂ →L[ℂ] ℂ) = om.toFun x := rfl
  -- The CLM `om.toFun x` is ℂ-linear; rearrange via map_smul + map_smul.
  -- `T_xy v • (T_yx 1) = T_yx (T_xy v • 1) = T_yx (T_xy v)`.
  have h_absorb :
      tangentXToY y x v • tangentYToX y x 1
        = tangentYToX y x (tangentXToY y x v) := by
    rw [← (tangentYToX y x).map_smul]
    show tangentYToX y x ((tangentXToY y x v) • (1 : ℂ))
        = tangentYToX y x (tangentXToY y x v)
    rw [smul_eq_mul, mul_one]
  calc (om.eval x) v
      = (show ℂ →L[ℂ] ℂ from om.toFun x) v := by rw [h_eval]
    _ = (show ℂ →L[ℂ] ℂ from om.toFun x)
          (tangentYToX y x (tangentXToY y x v)) := by
        rw [tangentYToX_tangentXToY_apply h_src]
    _ = (show ℂ →L[ℂ] ℂ from om.toFun x)
          (tangentXToY y x v • tangentYToX y x 1) := by rw [h_absorb]
    _ = tangentXToY y x v •
          (show ℂ →L[ℂ] ℂ from om.toFun x) (tangentYToX y x 1) := by
        rw [ContinuousLinearMap.map_smul]

/-! ## Chip-D headline: `ChartLocalPrimitiveFTC` at `chartAt ℂ y` UNCONDITIONAL -/

/-- **`ChartLocalPrimitiveFTC` at `chartAt ℂ y` UNCONDITIONALLY**
(modulo the convex chart-target hypothesis already required by the
definition). Composes D4 (chain-rule closed form for
`mfderiv chartLocalPrimitiveExtend`) with D5 (chart-cotangent
pointwise identity). -/
theorem chartLocalPrimitiveFTC_chartAt
    (y : X) (h_target_convex : Convex ℝ (chartAt ℂ y).target)
    (om : HolomorphicOneForm X) :
    ChartLocalPrimitiveFTC (chartAt ℂ y) (chart_mem_atlas ℂ y)
      h_target_convex y (mem_chart_source ℂ y) om := by
  intro x hx
  -- D4: closed-form mfderiv of chartLocalPrimitiveExtend.
  have h_d4 := mfderiv_chartLocalPrimitiveExtend_chartAt y h_target_convex om x hx
  -- D5: chart-cotangent identity for om.eval x.
  have h_d5 := om_eval_eq_chartCoord_smulRight_mfderiv_chartAt om hx
  rw [h_d4, ← h_d5]

end JacobianChallenge

end
