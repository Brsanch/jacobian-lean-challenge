/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AnalyticOnChartLocalIntegrand
import JacobianChallenge.Manifold.ChartLocalPrimitiveChartIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # The FTC identity `∫₀¹ ∂z[f(B(z₀,z,t)) · V(z₀,z,t)] dt = f(z)`

The integrand-`z` derivative `chartLocalIntegrandDerivInZ f z₀ z t`
is exactly the time-derivative of the auxiliary function

  `aux(t) := ((σ(t):ℝ):ℂ) · f(bumpedSegment z₀ z t)`

(product + chain rule). FTC over `[0, 1]` then collapses

  `∫₀¹ chartLocalIntegrandDerivInZ f z₀ z t dt = aux(1) - aux(0)
     = 1·f(z) - 0·f(z₀) = f(z)`

since `σ(0) = 0`, `σ(1) = 1`, `B(z₀, z, 0) = z₀`, `B(z₀, z, 1) = z`.

This is the **D1 sub-atom** of chip D (`ChartLocalPrimitiveFTC`): it
identifies the chart-coord parametric integral's derivative
`g'(z) = f(z)`, which is the analytic-side input of the FTC.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Topology MeasureTheory ContDiff
open MeasureTheory Set Filter

namespace JacobianChallenge

/-! ## The auxiliary `aux(t) = σ(t) · f(B(z₀, z, t))` and its `t`-derivative -/

/-- The auxiliary function `aux(t) := ((σ(t):ℝ):ℂ) * f(bumpedSegment z₀ z t)`
whose time-derivative is `chartLocalIntegrandDerivInZ`. -/
private noncomputable def chartLocalIntegrandAuxT
    (f : ℂ → ℂ) (z₀ z : ℂ) (t : ℝ) : ℂ :=
  ((Real.smoothTransition t : ℝ) : ℂ) * f (bumpedSegment z₀ z t)

/-- `aux(0) = 0`. -/
@[simp] private lemma chartLocalIntegrandAuxT_zero (f : ℂ → ℂ) (z₀ z : ℂ) :
    chartLocalIntegrandAuxT f z₀ z 0 = 0 := by
  unfold chartLocalIntegrandAuxT
  rw [Real.smoothTransition.zero]
  simp

/-- `aux(1) = f(z)`. -/
@[simp] private lemma chartLocalIntegrandAuxT_one (f : ℂ → ℂ) (z₀ z : ℂ) :
    chartLocalIntegrandAuxT f z₀ z 1 = f z := by
  unfold chartLocalIntegrandAuxT
  rw [Real.smoothTransition.one, bumpedSegment_one]
  push_cast
  ring

/-- The ℂ-cast of `Real.smoothTransition` has time-derivative `(σ'(t):ℂ)`
at every `t : ℝ`. Direct via mathlib's `HasDerivAt.ofReal_comp`. -/
private lemma hasDerivAt_sigma_complex (t : ℝ) :
    HasDerivAt (fun s : ℝ => ((Real.smoothTransition s : ℝ) : ℂ))
      ((deriv Real.smoothTransition t : ℝ) : ℂ) t := by
  have h_cd : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have h_diff : Differentiable ℝ Real.smoothTransition :=
    h_cd.differentiable (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have h_real : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition t) t :=
    (h_diff t).hasDerivAt
  exact h_real.ofReal_comp

/-- **HasDerivAt of `aux`** at every `t : ℝ` with derivative
`chartLocalIntegrandDerivInZ f z₀ z t`, under analyticity hypotheses
on `f` (so the chain rule fires at `bumpedSegment z₀ z t`). -/
private lemma hasDerivAt_chartLocalIntegrandAuxT
    {f : ℂ → ℂ} {S : Set ℂ} (hS_open : IsOpen S) (hS_conv : Convex ℝ S)
    (hf : AnalyticOn ℂ f S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) {z : ℂ} (hz : z ∈ S) (t : ℝ) :
    HasDerivAt (fun s : ℝ => chartLocalIntegrandAuxT f z₀ z s)
      (chartLocalIntegrandDerivInZ f z₀ z t) t := by
  unfold chartLocalIntegrandAuxT
  -- HasDerivAt of σ : ℝ → ℂ.
  have h_sigma : HasDerivAt (fun s : ℝ => ((Real.smoothTransition s : ℝ) : ℂ))
      ((deriv Real.smoothTransition t : ℝ) : ℂ) t :=
    hasDerivAt_sigma_complex t
  -- HasDerivAt of B(z₀, z, ·) : ℝ → ℂ.
  have h_B : HasDerivAt (fun s : ℝ => bumpedSegment z₀ z s)
      (chartCoordVelocity z₀ z t) t :=
    hasDerivAt_bumpedSegment_in_t z₀ z t
  -- f is differentiable at B(z₀, z, t) ∈ S.
  have h_B_mem : bumpedSegment z₀ z t ∈ S :=
    bumpedSegment_mem_of_convex hS_conv hz₀ hz t
  have hf_at : HasDerivAt f (deriv f (bumpedSegment z₀ z t))
      (bumpedSegment z₀ z t) :=
    (hf.analyticAt (hS_open.mem_nhds h_B_mem)).differentiableAt.hasDerivAt
  -- Chain rule: f ∘ B has time-deriv = deriv f (B) * V.
  have h_f_B : HasDerivAt (fun s : ℝ => f (bumpedSegment z₀ z s))
      (deriv f (bumpedSegment z₀ z t) * chartCoordVelocity z₀ z t) t :=
    hf_at.comp t h_B
  -- Product rule: aux = σ * (f ∘ B) has time-deriv
  --   = σ' * (f ∘ B) + σ * (deriv f B * V).
  have h_prod := h_sigma.mul h_f_B
  -- Identify with chartLocalIntegrandDerivInZ.
  rw [chartLocalIntegrandDerivInZ_eq]
  convert h_prod using 1
  ring

/-! ## The integral identity (D1) -/

/-- **D1: `∫₀¹ chartLocalIntegrandDerivInZ f z₀ z t dt = f z`.**

The ∂z-integral of the chart-coord integrand collapses pointwise via
FTC on `aux(t) = σ(t) · f(B(z₀, z, t))`. Substantive analytic input
for chip D (`ChartLocalPrimitiveFTC`). -/
theorem integral_chartLocalIntegrandDerivInZ_eq
    {f : ℂ → ℂ} {S : Set ℂ} (hS_open : IsOpen S) (hS_conv : Convex ℝ S)
    (hf : AnalyticOn ℂ f S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) {z : ℂ} (hz : z ∈ S) :
    ∫ t in (0 : ℝ)..1, chartLocalIntegrandDerivInZ f z₀ z t = f z := by
  -- Apply FTC: ∫₀¹ aux'(t) dt = aux(1) - aux(0).
  have h_deriv_at : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt
      (fun s : ℝ => chartLocalIntegrandAuxT f z₀ z s)
      (chartLocalIntegrandDerivInZ f z₀ z t) t := by
    intro t _
    exact hasDerivAt_chartLocalIntegrandAuxT hS_open hS_conv hf hz₀ hz t
  have h_int : IntervalIntegrable
      (fun t : ℝ => chartLocalIntegrandDerivInZ f z₀ z t)
      MeasureTheory.volume 0 1 := by
    have hf_cts : ContinuousOn f S := hf.continuousOn
    have hfd_cts : ContinuousOn (deriv f) S := by
      have h_deriv_an : AnalyticOnNhd ℂ (deriv f) S := by
        intro w hw
        exact (hf.analyticAt (hS_open.mem_nhds hw)).deriv
      exact h_deriv_an.continuousOn
    exact (continuous_chartLocalIntegrandDerivInZ_slice
      hS_conv hf_cts hfd_cts hz₀ hz).intervalIntegrable 0 1
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv_at h_int
  rw [h_ftc, chartLocalIntegrandAuxT_one, chartLocalIntegrandAuxT_zero]
  ring

end JacobianChallenge

end
