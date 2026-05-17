/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverDensityTransition
import JacobianChallenge.Manifold.Cotangent

set_option linter.unusedSectionVars false

/-! # Per-point localCoeff transition identity

For any base points `x y : X`, any `q ∈ (chartAt ℂ x).source ∩ (chartAt ℂ y).source`,
any holomorphic 1-form `om`:

```
localCoeff om x ((chartAt ℂ x) q) = transitionFactor x y q · localCoeff om y ((chartAt ℂ y) q)
```

Algebraic core of the multi-chart density bound that bridges
per-inner-disk uniform convergence to outer-disk seminorm convergence.

## Proof sketch

Unfold `localCoeff` and apply `cotangentBundleCore_coordChange_apply`
on both sides to reduce to compositions with tangent coordChanges. The
tangent cocycle `T(x,q) q v = T(y,q) q (T(x,y) q v)` at `v = 1`, combined
with ℂ-linearity of `T(y,q) q`, yields the identity.

No `sorry`, no `axiom`.
-/

open Set Metric

open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- For a continuous `ℂ`-linear `f : ℂ →L[ℂ] ℂ`, `f c = c * f 1`. -/
private lemma clm_apply_eq_smul_apply_one (f : ℂ →L[ℂ] ℂ) (c : ℂ) :
    f c = c * f 1 := by
  have h1 : (c : ℂ) = c • (1 : ℂ) := by rw [smul_eq_mul, mul_one]
  conv_lhs => rw [h1]
  rw [map_smul, smul_eq_mul]

/-- **Per-point localCoeff transition identity.** -/
theorem localCoeff_transition
    (om : HolomorphicOneForm X) {x y q : X}
    (hq_x : q ∈ (chartAt ℂ x).source)
    (hq_y : q ∈ (chartAt ℂ y).source) :
    HolomorphicOneForm.localCoeff om x ((chartAt ℂ x) q)
      = transitionFactor x y q
        * HolomorphicOneForm.localCoeff om y ((chartAt ℂ y) q) := by
  -- Unfold both `localCoeff`s.
  unfold HolomorphicOneForm.localCoeff
  -- Reduce `(chartAt _ z).symm ((chartAt _ z) q)` to `q`.
  have h_inv_x : (chartAt ℂ x).symm ((chartAt ℂ x) q) = q :=
    (chartAt ℂ x).left_inv hq_x
  have h_inv_y : (chartAt ℂ y).symm ((chartAt ℂ y) q) = q :=
    (chartAt ℂ y).left_inv hq_y
  rw [h_inv_x, h_inv_y]
  -- Apply `cotangentBundleCore_coordChange_apply` on both sides.
  rw [cotangentBundleCore_coordChange_apply,
      cotangentBundleCore_coordChange_apply]
  -- LHS now: `(om.toFun q).comp ((tangentBundleCore).coordChange (achart x) (achart q) q) 1`
  -- RHS factor: `(om.toFun q).comp ((tangentBundleCore).coordChange (achart y) (achart q) q) 1`
  -- Set `v := om.toFun q` (as a CLM); set
  --   `Txq := (tangentBundleCore).coordChange (achart x) (achart q) q : ℂ →L[ℂ] ℂ`
  --   `Tyq := (tangentBundleCore).coordChange (achart y) (achart q) q : ℂ →L[ℂ] ℂ`
  --   `Txy := transitionFactor x y q = ((tangentBundleCore).coordChange (achart x) (achart y) q) 1`
  -- Goal: `(v.comp Txq) 1 = Txy * (v.comp Tyq) 1`.
  -- `(v.comp Txq) 1 = v (Txq 1)`.
  -- `(v.comp Tyq) 1 = v (Tyq 1)`.
  -- By ℂ-linearity of v (which is `ℂ →L[ℂ] ℂ`): `v (Txq 1) = (Txq 1) * v 1`,
  --   `v (Tyq 1) = (Tyq 1) * v 1`.
  -- So the goal reduces to: `(Txq 1) * v 1 = Txy * (Tyq 1) * v 1`.
  -- Suffices: `Txq 1 = Txy * Tyq 1`.
  -- By tangent cocycle at v = 1: `Txq 1 = Tyq (Txq_via_y 1) = Tyq (Txy)
  --   = Txy * Tyq 1` (ℂ-linearity of Tyq).
  show (((om.toFun q : ℂ →L[ℂ] ℂ).comp
        ((tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ x) (achart ℂ q) q : ℂ →L[ℂ] ℂ)) : ℂ →L[ℂ] ℂ) 1
      = transitionFactor x y q
        * (((om.toFun q : ℂ →L[ℂ] ℂ).comp
            ((tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
              (achart ℂ y) (achart ℂ q) q : ℂ →L[ℂ] ℂ)) : ℂ →L[ℂ] ℂ) 1
  -- Rewrite `(f.comp g) 1 = f (g 1)`.
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  -- Now: `(om.toFun q) (Txq 1) = Txy * (om.toFun q) (Tyq 1)`.
  -- Apply ℂ-linearity.
  set v : ℂ →L[ℂ] ℂ := om.toFun q with hv
  set Txq : ℂ := ((tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
    (achart ℂ x) (achart ℂ q) q : ℂ →L[ℂ] ℂ) 1
  set Tyq : ℂ := ((tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
    (achart ℂ y) (achart ℂ q) q : ℂ →L[ℂ] ℂ) 1
  show v Txq = transitionFactor x y q * v Tyq
  rw [clm_apply_eq_smul_apply_one v Txq,
      clm_apply_eq_smul_apply_one v Tyq]
  -- Goal: `Txq * v 1 = transitionFactor x y q * (Tyq * v 1)`.
  -- Suffices: `Txq = transitionFactor x y q * Tyq`.
  have h_cocycle :
      ((tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange (achart ℂ y) (achart ℂ q) q
        : ℂ →L[ℂ] ℂ)
        (((tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange (achart ℂ x) (achart ℂ y) q
          : ℂ →L[ℂ] ℂ) 1)
      = Txq := by
    have h := (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange_comp
      (achart ℂ x) (achart ℂ y) (achart ℂ q) q
      ⟨⟨hq_x, hq_y⟩, mem_chart_source _ q⟩ (1 : ℂ)
    exact h
  -- Use ℂ-linearity of `Tyq-CLM` to pull the scalar `transitionFactor` out.
  have h_lin :
      ((tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange (achart ℂ y) (achart ℂ q) q
        : ℂ →L[ℂ] ℂ) (transitionFactor x y q)
      = transitionFactor x y q * Tyq := by
    exact clm_apply_eq_smul_apply_one _ _
  -- Combine.
  have h_eq : Txq = transitionFactor x y q * Tyq := by
    rw [← h_cocycle]
    exact h_lin
  rw [h_eq]
  ring

end DiskChartCover

end JacobianChallenge

end
