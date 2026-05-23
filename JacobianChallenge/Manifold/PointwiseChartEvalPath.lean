/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PointwiseChartEvalUnconditional

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Pointwise chart-pullback identity for an arbitrary smooth path

`ChartContainedClosedLoop.pointwiseChartEvalIdentity_unconditional` in
`PointwiseChartEvalUnconditional.lean` ships the identity

```
(α.eval x : ℂ →L[ℂ] ℂ) v
  = α.localCoeff basePoint (chartPath t) * deriv chartPath t
```

for `x = γ.ambient t`, `v = γ.velocity t` and `t ∈ [0, 1]`, but is
scoped to a `ChartContainedClosedLoop` data bundle (requires
`is_loop : γ.src = γ.tgt`, ball-containment, etc.). The proof of the
identity itself uses NONE of those — just:

* `γ.ambient t ∈ (chartAt y).source` (so `chartAt y` makes sense on
  `γ.ambient t`),
* the cocycle of `tangentBundleCore (𝓘(ℂ, ℂ)) X` at that point.

This file ships the **path-only generalization**: for any smooth path
`γ : SmoothPath 𝓘(ℝ, ℂ) X`, any base point `y : X` with
`γ.ambient t ∈ (chartAt ℂ y).source`, and any
`α : HolomorphicOneForm X`, the identity holds at `t`.

This is the substantive half of the chip-B chart-pulled identity for
`chartLocalPrimitive`: applied to `γ := linearInChartSegment φ y x`
(which is NOT a loop in general), with chip B1's structural bridge it
gives the explicit ℂ-integral form.

The proof mirrors `pointwiseChartEvalIdentity_unconditional` — same
helper trio (`T_yx`, `T_xy` cocycle + `localCoeff` chart-image unfold
+ `deriv chartPath = T_xy v` chain-rule identity), but with the
`ChartContainedClosedLoop` data field accesses replaced by direct
hypotheses on `(γ, y, t)`. The trio is restated locally (the originals
in `PointwiseChartEvalUnconditional.lean` are `private`).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace SmoothPath

/-! ## Tangent / cotangent coord-change shorthand at `x = γ.ambient t`

These mirror `T_yx`/`T_xy` from
`ChartContainedClosedLoop.PointwiseChartEvalUnconditional.lean` but
take the base point `y` and time `t` as loose parameters. -/

/-- The `𝓘(ℂ, ℂ)` tangent coord change from `achart y → achart (γ.ambient t)`
at `γ.ambient t`. -/
private noncomputable def tangentYToAmbient
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) (y : X) (t : ℝ) : ℂ →L[ℂ] ℂ :=
  (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
    (achart ℂ y) (achart ℂ (γ.ambient t)) (γ.ambient t)

/-- The `𝓘(ℂ, ℂ)` tangent coord change from `achart (γ.ambient t) → achart y`
at `γ.ambient t`. -/
private noncomputable def tangentAmbientToY
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) (y : X) (t : ℝ) : ℂ →L[ℂ] ℂ :=
  (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
    (achart ℂ (γ.ambient t)) (achart ℂ y) (γ.ambient t)

/-- **Cocycle inversion at `γ.ambient t`.** -/
private lemma tangentYToAmbient_tangentAmbientToY_apply
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) (y : X)
    {t : ℝ} (h_src : γ.ambient t ∈ (chartAt ℂ y).source)
    (v : ℂ) :
    tangentYToAmbient γ y t (tangentAmbientToY γ y t v) = v := by
  have h_self_x : γ.ambient t ∈ (achart ℂ (γ.ambient t)).1.source := by
    show γ.ambient t ∈ (chartAt ℂ (γ.ambient t)).source
    exact mem_chart_source _ _
  have h_self_y : γ.ambient t ∈ (achart ℂ y).1.source := by
    show γ.ambient t ∈ (chartAt ℂ y).source
    exact h_src
  have h_comp := (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange_comp
    (achart ℂ (γ.ambient t)) (achart ℂ y)
    (achart ℂ (γ.ambient t)) (γ.ambient t)
    ⟨⟨h_self_x, h_self_y⟩, h_self_x⟩ v
  have h_self_eq : (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
      (achart ℂ (γ.ambient t)) (achart ℂ (γ.ambient t)) (γ.ambient t) v = v := by
    apply (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange_self
    exact h_self_x
  show (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y) (achart ℂ (γ.ambient t)) (γ.ambient t)
        ((tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ (γ.ambient t)) (achart ℂ y) (γ.ambient t) v) = v
  rw [h_comp]; exact h_self_eq

/-! ## `localCoeff` unfolds at `(chart y) (γ.ambient t)` -/

/-- **`localCoeff` at the chart-image of `γ.ambient t`** equals
`α.toFun (γ.ambient t) (tangentYToAmbient 1)`. -/
private lemma localCoeff_apply_at_chartImage_path
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) (y : X)
    (α : HolomorphicOneForm X)
    {t : ℝ} (h_src : γ.ambient t ∈ (chartAt ℂ y).source) :
    α.localCoeff y ((chartAt ℂ y) (γ.ambient t))
      = (show ℂ →L[ℂ] ℂ from α.toFun (γ.ambient t))
          (tangentYToAmbient γ y t 1) := by
  have h_symm :
      (chartAt ℂ y).symm ((chartAt ℂ y) (γ.ambient t)) = γ.ambient t :=
    (chartAt ℂ y).left_inv h_src
  show ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ ((chartAt ℂ y).symm ((chartAt ℂ y) (γ.ambient t))))
          (achart ℂ y)
          ((chartAt ℂ y).symm ((chartAt ℂ y) (γ.ambient t)))
          (α.toFun ((chartAt ℂ y).symm ((chartAt ℂ y) (γ.ambient t))))) 1
      = (show ℂ →L[ℂ] ℂ from α.toFun (γ.ambient t))
          (tangentYToAmbient γ y t 1)
  rw [h_symm]
  rw [cotangentBundleCore_coordChange_apply]
  rfl

/-! ## `deriv (chartAt y ∘ γ.ambient) t = tangentAmbientToY (γ.velocity t)` -/

/-- **`deriv (chartAt y ∘ γ.ambient) t`** equals
`tangentAmbientToY γ y t (γ.velocity t)`. -/
private lemma deriv_chartPath_eq_tangentAmbientToY_velocity_path
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) (y : X)
    {t : ℝ} (h_src : γ.ambient t ∈ (chartAt ℂ y).source) :
    deriv ((chartAt ℂ y : X → ℂ) ∘ γ.ambient) t
      = tangentAmbientToY γ y t (γ.velocity t) := by
  have h_chart_atlas : (chartAt ℂ y : OpenPartialHomeomorph X ℂ)
      ∈ atlas ℂ X := chart_mem_atlas ℂ y
  -- Chain rule.
  have h_chain :
      (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ))
        ((chartAt ℂ y : X → ℂ) ∘ γ.ambient) t : ℝ →L[ℝ] _) (1 : ℝ)
        = (mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ))
            (chartAt ℂ y : X → ℂ) (γ.ambient t) : ℂ →L[ℝ] _)
              (γ.velocity t) :=
    SmoothPath.mfderiv_chart_comp_ambient_apply_one γ h_chart_atlas h_src
  rw [mfderiv_chartAt_eq_tangentCoordChange (I := 𝓘(ℝ, ℂ)) h_src] at h_chain
  -- Bridge ℝ-tangent-coord-change with restrictScalars of ℂ-tangent-coord-change.
  have h_bridge :
      (tangentBundleCore 𝓘(ℝ, ℂ) X).coordChange (achart ℂ (γ.ambient t))
          (achart ℂ y) (γ.ambient t)
        = ((tangentBundleCore 𝓘(ℂ, ℂ) X).coordChange
            (achart ℂ (γ.ambient t)) (achart ℂ y)
            (γ.ambient t)).restrictScalars ℝ :=
    tangentBundleCore_coordChange_restrictScalars_eq
      (i := achart ℂ (γ.ambient t)) (j := achart ℂ y)
      (mem_chart_source _ _) h_src
  -- Reduce h_chain to `tangentAmbientToY γ y t (γ.velocity t)`.
  have h_chain' :
      (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ))
        ((chartAt ℂ y : X → ℂ) ∘ γ.ambient) t : ℝ →L[ℝ] _) (1 : ℝ)
        = tangentAmbientToY γ y t (γ.velocity t) := by
    rw [h_chain]
    show (tangentBundleCore 𝓘(ℝ, ℂ) X).coordChange
            (achart ℂ (γ.ambient t)) (achart ℂ y)
            (γ.ambient t) (γ.velocity t)
        = tangentAmbientToY γ y t (γ.velocity t)
    rw [h_bridge]
    rfl
  -- Bridge `(mfderiv … )(1) = deriv (…) t`.
  have h_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
      ((chartAt ℂ y : X → ℂ) ∘ γ.ambient) t :=
    SmoothPath.mdifferentiableAt_chart_comp_ambient γ h_chart_atlas h_src
  have h_diff : DifferentiableAt ℝ
      ((chartAt ℂ y : X → ℂ) ∘ γ.ambient) t :=
    h_mdiff.differentiableAt
  have h_mfderiv_eq_fderiv :
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
          ((chartAt ℂ y : X → ℂ) ∘ γ.ambient) t : ℝ →L[ℝ] ℂ)
        = fderiv ℝ ((chartAt ℂ y : X → ℂ) ∘ γ.ambient) t :=
    mfderiv_eq_fderiv (f := (chartAt ℂ y : X → ℂ) ∘ γ.ambient) (x := t)
  have h_deriv_eq :
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
          ((chartAt ℂ y : X → ℂ) ∘ γ.ambient) t : ℝ →L[ℝ] ℂ) (1 : ℝ)
        = deriv ((chartAt ℂ y : X → ℂ) ∘ γ.ambient) t := by
    rw [h_mfderiv_eq_fderiv]
    exact h_diff.hasFDerivAt.hasDerivAt.deriv
  rw [← h_deriv_eq, h_chain']

/-! ## Headline: pointwise chart-pullback identity for arbitrary smooth path -/

/-- **Pointwise chart-pullback identity for a smooth path.**

For any smooth path `γ : SmoothPath 𝓘(ℝ, ℂ) X`, base point `y : X`
with `γ.ambient t ∈ (chartAt ℂ y).source`, and holomorphic 1-form
`α : HolomorphicOneForm X`,

  `(α.eval (γ.ambient t)) (γ.velocity t)
     = α.localCoeff y ((chartAt ℂ y) (γ.ambient t))
         * deriv ((chartAt ℂ y) ∘ γ.ambient) t`.

Mirrors `pointwiseChartEvalIdentity_unconditional` (which is scoped
to `ChartContainedClosedLoop`) — the loop hypothesis and ball-
containment fields are not used by the underlying algebra. -/
theorem pointwiseChartEval_path
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) (y : X)
    (α : HolomorphicOneForm X)
    {t : ℝ} (h_src : γ.ambient t ∈ (chartAt ℂ y).source) :
    (α.eval (γ.ambient t)) (γ.velocity t)
      = α.localCoeff y ((chartAt ℂ y) (γ.ambient t)) *
          deriv ((chartAt ℂ y : X → ℂ) ∘ γ.ambient) t := by
  rw [localCoeff_apply_at_chartImage_path γ y α h_src]
  rw [deriv_chartPath_eq_tangentAmbientToY_velocity_path γ y h_src]
  -- Goal: α.eval x v = α.toFun x (T_yx 1) * T_xy v
  have h_eval :
      (α.eval (γ.ambient t) : ℂ →L[ℂ] ℂ) = α.toFun (γ.ambient t) := rfl
  show ((α.eval (γ.ambient t) : ℂ →L[ℂ] ℂ) (γ.velocity t) : ℂ)
    = (show ℂ →L[ℂ] ℂ from α.toFun (γ.ambient t))
        (tangentYToAmbient γ y t 1)
        * tangentAmbientToY γ y t (γ.velocity t)
  rw [h_eval]
  -- Pull the scalar `T_xy v` out of `α.toFun x : ℂ →L[ℂ] ℂ` via map_smul.
  have h_smul_pull :
      (show ℂ →L[ℂ] ℂ from α.toFun (γ.ambient t))
          (tangentYToAmbient γ y t 1)
        * tangentAmbientToY γ y t (γ.velocity t)
        = (show ℂ →L[ℂ] ℂ from α.toFun (γ.ambient t))
            ((tangentAmbientToY γ y t (γ.velocity t)) •
              (tangentYToAmbient γ y t 1)) := by
    rw [ContinuousLinearMap.map_smul]
    show (show ℂ →L[ℂ] ℂ from α.toFun (γ.ambient t))
            (tangentYToAmbient γ y t 1)
            * tangentAmbientToY γ y t (γ.velocity t)
        = (tangentAmbientToY γ y t (γ.velocity t))
            • ((show ℂ →L[ℂ] ℂ from α.toFun (γ.ambient t))
                (tangentYToAmbient γ y t 1))
    rw [smul_eq_mul, mul_comm]
  rw [h_smul_pull]
  -- Absorb the scalar into T_yx (ℂ-linear): `c • (T_yx 1) = T_yx c`.
  have h_T_yx_smul :
      (tangentAmbientToY γ y t (γ.velocity t)) •
          (tangentYToAmbient γ y t 1)
        = tangentYToAmbient γ y t
            (tangentAmbientToY γ y t (γ.velocity t)) := by
    rw [← (tangentYToAmbient γ y t).map_smul]
    show (tangentYToAmbient γ y t)
        ((tangentAmbientToY γ y t (γ.velocity t)) • (1 : ℂ))
        = (tangentYToAmbient γ y t)
            (tangentAmbientToY γ y t (γ.velocity t))
    rw [smul_eq_mul, mul_one]
  rw [h_T_yx_smul]
  -- Apply cocycle: T_yx (T_xy v) = v.
  rw [tangentYToAmbient_tangentAmbientToY_apply γ y h_src]

end SmoothPath

end JacobianChallenge

end
