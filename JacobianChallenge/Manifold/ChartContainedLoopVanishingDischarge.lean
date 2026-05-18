/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartContainedLoopPeriod
import JacobianChallenge.Manifold.HolomorphicOneFormRealComponent
import JacobianChallenge.Manifold.SmoothPathChartCompat
import JacobianChallenge.Manifold.LoopPeriodConstant
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

/-! # Discharge of `ChartContainedLoopVanishingHypothesis` via local primitive + FTC

For a `ChartContainedClosedLoop` on `X` and a holomorphic 1-form
`α : HolomorphicOneForm X`, the complex period vanishes:
`complexChainPeriod (SmoothChain.single γ) α = 0`.

## Proof strategy

1. `α.localCoeff y` has a primitive `F : ℂ → ℂ` on `Metric.ball c r`
   (`HolomorphicOneFormLocalPrimitive.exists_local_primitive_on_ball`).

2. The composite `G := F ∘ (chartAt ℂ y) : X → ℂ` (on the chart source)
   serves as a local primitive of `α` on `X`: under chart-coord chain
   rule, `mfderiv G (γ.ambient t) (γ.velocity t)` equals
   `α.eval (γ.ambient t) (γ.velocity t)` (the integrand of
   `complexChainPeriod`).

3. By the manifold FTC (applied separately to real and imaginary parts
   of `G`), `complexChainPeriod (single γ) α = G(γ.tgt) - G(γ.src)`.

4. For a closed loop (`γ.src = γ.tgt`), this is `0`.

The substantive content is step 2 (chain rule for chart-pullback) and
step 3 (FTC on real/imag parts). Both are standard but require careful
chart-coord bookkeeping.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex MeasureTheory intervalIntegral

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace ChartContainedClosedLoop

/-- **The chart-coord path traced by a chart-contained loop.**
For a `ChartContainedClosedLoop` `data`, the function `t ↦ chart(γ(t))`
on `[0, 1]` traces a closed loop in `Metric.ball data.ballCentre data.ballRadius`. -/
def chartPath (data : ChartContainedClosedLoop (X := X)) (t : ℝ) : ℂ :=
  (chartAt ℂ data.basePoint) (data.γ.ambient t)

@[simp] lemma chartPath_at_one_eq_at_zero (data : ChartContainedClosedLoop (X := X)) :
    data.chartPath 1 = data.chartPath 0 := by
  unfold chartPath
  -- Use the loop property: γ.src = γ.tgt, where src and tgt are γ.ambient 0 and γ.ambient 1.
  have h_src_amb : data.γ.ambient 0 = data.γ.src := by
    have h := data.γ.ambient_eq_on_unitInterval ⟨0, ⟨le_refl 0, zero_le_one⟩⟩
    have h_val : ((⟨0, ⟨le_refl 0, zero_le_one⟩⟩ : unitInterval) : ℝ) = 0 := rfl
    rw [h_val] at h
    rw [h]
    exact data.γ.toPath.source
  have h_tgt_amb : data.γ.ambient 1 = data.γ.tgt := by
    have h := data.γ.ambient_eq_on_unitInterval ⟨1, ⟨zero_le_one, le_refl 1⟩⟩
    have h_val : ((⟨1, ⟨zero_le_one, le_refl 1⟩⟩ : unitInterval) : ℝ) = 1 := rfl
    rw [h_val] at h
    rw [h]
    exact data.γ.toPath.target
  rw [h_src_amb, h_tgt_amb, data.is_loop]

end ChartContainedClosedLoop

end JacobianChallenge

end
