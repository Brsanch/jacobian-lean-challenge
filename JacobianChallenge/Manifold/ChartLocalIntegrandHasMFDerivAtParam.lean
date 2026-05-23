/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartLocalIntegrandHasDerivAtParam
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option linter.unusedSectionVars false

/-! # D3: `HasMFDerivAt` / `mfderiv` of the chart-coord parametric integral

Lifts D2's `HasDerivAt g (f z) z` for the chart-coord parametric
integral `g(z) := ∫ t in 0..1, f(B(z₀,z,t)) * V(z₀,z,t)` to the
manifold-side `HasMFDerivAt` and the closed-form

  `mfderiv 𝓘(ℂ) 𝓘(ℂ) g z = ContinuousLinearMap.toSpanSingleton ℂ (f z)`

(= `(1 : ℂ →L[ℂ] ℂ).smulRight (f z)`, the "multiply by `f z`" CLM).

This is the **D3 sub-atom** of chip D (`ChartLocalPrimitiveFTC`). D4
combines D3 with chip B3 (`chartLocalPrimitive = g ∘ chartAt y`) and
the chain rule for `mfderiv` to factor `mfderiv chartLocalPrimitive x`
through `mfderiv (chartAt y) x`. D5 then matches that factorization
with chip B2's pointwise chart-pullback identity to recover `om.eval x`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Topology MeasureTheory ContDiff Manifold
open MeasureTheory Set Filter

namespace JacobianChallenge

/-- **D3 (HasMFDerivAt form).** At every `z ∈ S` (convex, open, `z₀ ∈ S`),
the chart-coord parametric integral
`z' ↦ ∫ t in 0..1, f(B(z₀,z',t)) * V(z₀,z',t)` has manifold-derivative
`toSpanSingleton ℂ (f z) : ℂ →L[ℂ] ℂ` at `z`. -/
theorem hasMFDerivAt_chartLocalIntegrand_param
    {f : ℂ → ℂ} {S : Set ℂ}
    (hS_open : IsOpen S) (hS_conv : Convex ℝ S)
    (hf : AnalyticOn ℂ f S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) {z : ℂ} (hz : z ∈ S) :
    HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (fun z' : ℂ => ∫ t in (0 : ℝ)..1,
        f (bumpedSegment z₀ z' t) * chartCoordVelocity z₀ z' t)
      z
      (ContinuousLinearMap.toSpanSingleton ℂ (f z)) := by
  -- D2 gives HasDerivAt; convert HasDerivAt → HasFDerivAt → HasMFDerivAt.
  have h_derivAt := hasDerivAt_chartLocalIntegrand_param
    hS_open hS_conv hf hz₀ hz
  exact h_derivAt.hasFDerivAt.hasMFDerivAt

/-- **D3 (mfderiv form).** Closed form for `mfderiv` of the chart-coord
parametric integral at every `z ∈ S`. -/
theorem mfderiv_chartLocalIntegrand_param
    {f : ℂ → ℂ} {S : Set ℂ}
    (hS_open : IsOpen S) (hS_conv : Convex ℝ S)
    (hf : AnalyticOn ℂ f S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) {z : ℂ} (hz : z ∈ S) :
    mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (fun z' : ℂ => ∫ t in (0 : ℝ)..1,
          f (bumpedSegment z₀ z' t) * chartCoordVelocity z₀ z' t) z
      = ContinuousLinearMap.toSpanSingleton ℂ (f z) :=
  (hasMFDerivAt_chartLocalIntegrand_param hS_open hS_conv hf hz₀ hz).mfderiv

end JacobianChallenge

end
