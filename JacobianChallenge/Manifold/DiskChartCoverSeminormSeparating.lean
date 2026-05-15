/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverSeminormAggregate

set_option diagnostics.threshold 100

/-! # Separating property of `seminormVal cover`

The disk-cover seminorm `seminormVal cover` on `HolomorphicOneForm X` is
*separating*:

```
seminormVal cover om = 0 ↔ om = 0
```

The forward direction reduces, via the per-base-point `sup'` bound, to:

* `localCoeffMax cover x om = 0 → om` vanishes on the chart-`x` preimage
  of the outer closed disk, in particular on the chart-`x` preimage of
  the open inner disk.
* The open inner disks cover `X` (by `cover.covers`), so `om` vanishes
  everywhere, hence `om = 0` by `ContMDiffSection` extensionality.

The "inner" pointwise step

```
localCoeff om y ((chartAt ℂ y) y') = 0 → om.toFun y' = 0
```

for `y' ∈ (chartAt ℂ y).source` decomposes as:

1. **CLM eval-at-`1` separation.** For a CLM `T : ℂ →L[ℂ] ℂ`, `T 1 = 0`
   implies `T = 0`. Mathlib's `ContinuousLinearMap.ext_ring`.
2. **Cotangent `coordChange` fibre injectivity.** At
   `y' ∈ (chartAt ℂ y).source ∩ (chartAt ℂ y').source`, the cotangent
   coord-change `coordChange (achart ℂ y') (achart ℂ y) y'` is
   injective on the fibre `ℂ →L[ℂ] ℂ`. Proof: applying
   `coordChange (achart ℂ y) (achart ℂ y') y'` on the left composes via
   `coordChange_comp` + `coordChange_self` to the identity on the
   fibre; and applying it to `0` yields `0` via
   `cotangentBundleCore_coordChange_apply` + `ContinuousLinearMap.zero_comp`.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff
open Set Metric HolomorphicOneForm

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-! ## CLM eval-at-`1` separation -/

/-- A CLM `T : ℂ →L[ℂ] ℂ` is zero iff `T 1 = 0`. -/
private lemma clm_eq_zero_of_apply_one (T : ℂ →L[ℂ] ℂ) (h : T 1 = 0) :
    T = 0 :=
  ContinuousLinearMap.ext_ring
    (h.trans (ContinuousLinearMap.zero_apply 1).symm)

/-! ## Cotangent `coordChange` fibre invertibility -/

/-- The cotangent `coordChange` sends `0` to `0`. Proof: by
`cotangentBundleCore_coordChange_apply` the LHS equals
`(0 : ℂ →L[ℂ] ℂ).comp T`, which is `0` by `ContinuousLinearMap.zero_comp`. -/
private lemma cotangentBundleCore_coordChange_apply_zero
    (i j : atlas ℂ X) (x : X) :
    (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange i j x 0 = 0 := by
  rw [cotangentBundleCore_coordChange_apply]
  exact ContinuousLinearMap.zero_comp _

/-- At a point `y' ∈ (chartAt ℂ y).source`, the cotangent coord-change
`coordChange (achart ℂ y') (achart ℂ y) y'` is injective on the fibre. -/
private lemma cotangent_coordChange_injective {y y' : X}
    (hy' : y' ∈ (chartAt ℂ y).source) {v : ℂ →L[ℂ] ℂ}
    (hv : (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
            (achart ℂ y') (achart ℂ y) y' v = 0) :
    v = 0 := by
  have hy'_in_y : y' ∈ (cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ y) := hy'
  have hy'_in_y' : y' ∈ (cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ y') :=
    mem_chart_source _ y'
  -- Start from the cocycle equation
  --   `coordChange (achart y) (achart y') y' (coordChange (achart y') (achart y) y' v)
  --      = coordChange (achart y') (achart y') y' v`,
  -- then rewrite the inner coordChange via `hv`, the resulting `coordChange ... 0`
  -- via `cotangentBundleCore_coordChange_apply_zero`, and the RHS via `coordChange_self`.
  have h_comp := (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange_comp
    (achart ℂ y') (achart ℂ y) (achart ℂ y') y'
    ⟨⟨hy'_in_y', hy'_in_y⟩, hy'_in_y'⟩ v
  rw [hv, cotangentBundleCore_coordChange_apply_zero,
      (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange_self
        (achart ℂ y') y' hy'_in_y' v] at h_comp
  exact h_comp.symm

/-! ## Bridge: `localCoeff = 0` at chart image implies `om.toFun = 0` -/

/-- For `y' ∈ (chartAt ℂ y).source`, vanishing of `localCoeff om y` at the
chart image `(chartAt ℂ y) y'` implies `om.toFun y' = 0`. -/
private lemma toFun_eq_zero_of_localCoeff_eq_zero_at_chart_image
    (om : HolomorphicOneForm X) {y y' : X}
    (hy' : y' ∈ (chartAt ℂ y).source)
    (h : localCoeff om y ((chartAt ℂ y) y') = 0) :
    om.toFun y' = 0 := by
  have h_chart : (chartAt ℂ y).symm ((chartAt ℂ y) y') = y' :=
    (chartAt ℂ y).left_inv hy'
  -- Unfold `localCoeff om y ((chartAt ℂ y) y')` using `h_chart` to
  -- normalize the chart-symm side.
  have h_unfold :
      ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ y') (achart ℂ y) y' (om.toFun y')) 1 = 0 := by
    have h_eq : localCoeff om y ((chartAt ℂ y) y') =
        ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ y') (achart ℂ y) y' (om.toFun y')) 1 := by
      show ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
              (achart ℂ ((chartAt ℂ y).symm ((chartAt ℂ y) y')))
              (achart ℂ y)
              ((chartAt ℂ y).symm ((chartAt ℂ y) y'))
              (om.toFun ((chartAt ℂ y).symm ((chartAt ℂ y) y')))) 1 = _
      rw [h_chart]
    rw [h_eq] at h
    exact h
  -- By CLM eval-at-`1` separation: the inner CLM is zero.
  have h_clm := clm_eq_zero_of_apply_one _ h_unfold
  -- By cotangent coordChange injectivity: `om.toFun y' = 0`.
  exact cotangent_coordChange_injective hy' h_clm

/-! ## Headline: separating norm property -/

/-- **Separating property** of the disk-cover seminorm:
`seminormVal cover om = 0` iff `om = 0`. -/
theorem seminormVal_eq_zero_iff_zero (cover : DiskChartCover X) [Nonempty X]
    (om : HolomorphicOneForm X) :
    seminormVal cover om = 0 ↔ om = 0 := by
  refine ⟨fun h => ?_, fun h => by subst h; exact seminormVal_zero cover⟩
  -- Reduce to: `∀ y, om.toFun y = 0`.
  apply ContMDiffSection.ext
  intro y
  -- Pick a base point `x` whose chart contains `y` in the inner open ball.
  obtain ⟨x, hx_base, hy_source, hy_ball⟩ := cover.covers y
  -- The per-chart sup `localCoeffMax x om` is sandwiched between `0` and
  -- `seminormVal cover om = 0`, so it is `0`.
  have h_max_nonneg := localCoeffMax_nonneg cover om hx_base
  have h_max_le : localCoeffMax cover x om ≤ seminormVal cover om := by
    unfold seminormVal
    exact Finset.le_sup' (fun y => localCoeffMax cover y om) hx_base
  rw [h] at h_max_le
  have h_max_zero : localCoeffMax cover x om = 0 :=
    le_antisymm h_max_le h_max_nonneg
  -- `(chartAt ℂ x) y` is in the inner open ball, hence in the outer closed disk.
  have h_inner_le_outer : cover.innerRadius x ≤ cover.outerRadius x :=
    (cover.innerRadius_lt_outerRadius x hx_base).le
  have h_chart_y_in_outer :
      (chartAt ℂ x) y ∈ closedBall ((chartAt ℂ x) x) (cover.outerRadius x) := by
    have h_inner_ball_sub_outer :
        ball ((chartAt ℂ x) x) (cover.innerRadius x) ⊆
          closedBall ((chartAt ℂ x) x) (cover.outerRadius x) :=
      (ball_subset_closedBall).trans
        (closedBall_subset_closedBall h_inner_le_outer)
    exact h_inner_ball_sub_outer hy_ball
  -- `‖localCoeff om x ((chartAt ℂ x) y)‖ ≤ localCoeffMax x om = 0`,
  -- so it vanishes; hence `localCoeff om x ((chartAt ℂ x) y) = 0`.
  have h_norm_le :=
    norm_localCoeff_le_localCoeffMax cover om hx_base h_chart_y_in_outer
  rw [h_max_zero] at h_norm_le
  have h_norm_zero : ‖localCoeff om x ((chartAt ℂ x) y)‖ = 0 :=
    le_antisymm h_norm_le (norm_nonneg _)
  have h_lc_zero : localCoeff om x ((chartAt ℂ x) y) = 0 :=
    norm_eq_zero.mp h_norm_zero
  -- Conclude via the bridge. `ContMDiffSection.toFun 0 y` is definitionally
  -- the zero CLM, so the `show` collapses the RHS.
  have h_om_y : om.toFun y = 0 :=
    toFun_eq_zero_of_localCoeff_eq_zero_at_chart_image om hy_source h_lc_zero
  change om.toFun y = 0
  exact h_om_y

end DiskChartCover

end JacobianChallenge

end
