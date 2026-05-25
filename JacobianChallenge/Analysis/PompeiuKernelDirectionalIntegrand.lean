/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.PompeiuKernelContinuity
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Chip 2c-prep: directional derivative of `α` as a Pompeiu input

For `α : ℂ → ℂ` of class `C^1` with compact support, the directional
derivative

  `αDeriv α v := fun ζ : ℂ => (fderiv ℝ α ζ) v`

is again continuous with compact support (`HasCompactSupport.fderiv_apply`
+ continuity of the bundled derivative for `C^1` functions). Therefore
`αDeriv α v` is itself a valid input to the Pompeiu integrand
(Chip 1c) and to `pompeiuKernel` (Chip 2b). Moreover, `‖fderiv ℝ α‖` is
uniformly bounded on `ℂ` since `fderiv ℝ α` is continuous with compact
support.

This file packages the infrastructure used by Chip 2c proper, which
applies `hasDerivAt_integral_of_dominated_loc_of_deriv_le` to
differentiate `pompeiuKernel α` in `z` along the real path
`t ↦ z₀ + t • v`. The candidate derivative is `pompeiuKernel (αDeriv α v) z₀`.

## Main contents

* `αDeriv` — the directional-derivative function `ζ ↦ (fderiv ℝ α ζ) v`.
* `αDeriv_hasCompactSupport` — compact support is preserved.
* `αDeriv_continuous` — continuity is preserved under `ContDiff ℝ 1 α`.
* `integrable_pompeiuIntegrand_αDeriv` — Chip 1c lifts to the directional
  Pompeiu integrand.
* `continuous_pompeiuKernel_αDeriv` — Chip 2b lifts to the directional
  Pompeiu kernel.
* `exists_fderiv_norm_bound` — uniform bound `‖fderiv ℝ α ζ‖ ≤ M'`
  (used as the integrable Lipschitz/derivative bound in Chip 2c proper).

No `sorry`, no `axiom`. -/

noncomputable section

open MeasureTheory Complex Filter Set Topology Metric
open scoped Real Topology ENNReal

namespace JacobianChallenge.PompeiuKernel

/-! ## The directional-derivative function -/

/-- Directional derivative of `α : ℂ → ℂ` in direction `v : ℂ`:
`αDeriv α v ζ = (fderiv ℝ α ζ) v`. -/
def αDeriv (α : ℂ → ℂ) (v : ℂ) : ℂ → ℂ := fun ζ => fderiv ℝ α ζ v

/-- `αDeriv α v` has compact support whenever `α` does. -/
lemma αDeriv_hasCompactSupport {α : ℂ → ℂ}
    (h_supp : HasCompactSupport α) (v : ℂ) :
    HasCompactSupport (αDeriv α v) :=
  HasCompactSupport.fderiv_apply ℝ h_supp v

/-- `αDeriv α v` is continuous whenever `α` is `C^1`. The bundled
derivative `fderiv ℝ α : ℂ → (ℂ →L[ℝ] ℂ)` is continuous
(`ContDiff.continuous_fderiv`), and CLM-application at a fixed point
`v` is continuous (`ContinuousLinearMap.apply` is bounded bilinear). -/
lemma αDeriv_continuous {α : ℂ → ℂ}
    (h_smooth : ContDiff ℝ 1 α) (v : ℂ) :
    Continuous (αDeriv α v) := by
  have h_fderiv_cont : Continuous (fderiv ℝ α) :=
    h_smooth.continuous_fderiv (by norm_num)
  have h_apply_cont : Continuous (fun L : ℂ →L[ℝ] ℂ => L v) :=
    (ContinuousLinearMap.apply ℝ ℂ v).continuous
  exact h_apply_cont.comp h_fderiv_cont

/-! ## Chips 1c and 2b lifted to the directional-derivative input -/

/-- Chip 1c lifted: the Pompeiu integrand built from `αDeriv α v` is
integrable. -/
theorem integrable_pompeiuIntegrand_αDeriv
    {α : ℂ → ℂ} (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
    (v z : ℂ) :
    Integrable (pompeiuIntegrand (αDeriv α v) z) (volume : Measure ℂ) :=
  integrable_pompeiuIntegrand_of_continuous_hasCompactSupport
    (αDeriv_continuous h_smooth v) (αDeriv_hasCompactSupport h_supp v) z

/-- Chip 2b lifted: the Pompeiu kernel built from `αDeriv α v` is
continuous in `z`. -/
theorem continuous_pompeiuKernel_αDeriv
    {α : ℂ → ℂ} (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
    (v : ℂ) :
    Continuous (pompeiuKernel (αDeriv α v)) :=
  continuous_pompeiuKernel_of_continuous_hasCompactSupport
    (αDeriv_continuous h_smooth v) (αDeriv_hasCompactSupport h_supp v)

/-! ## Uniform bound on `‖fderiv ℝ α‖`

For `α : ℂ → ℂ` of class `C^1` with compact support, the bundled
derivative `fderiv ℝ α : ℂ → (ℂ →L[ℝ] ℂ)` is continuous and itself has
compact support. By
`Continuous.bounded_above_of_compact_support`, there is a real `M' ≥ 0`
with `‖fderiv ℝ α ζ‖ ≤ M'` for all `ζ`. -/

/-- Uniform `‖fderiv ℝ α‖`-bound for `α ∈ C^1(ℂ → ℂ)` with compact
support. -/
theorem exists_fderiv_norm_bound
    {α : ℂ → ℂ} (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α) :
    ∃ M' : ℝ, 0 ≤ M' ∧ ∀ ζ : ℂ, ‖fderiv ℝ α ζ‖ ≤ M' := by
  have h_fderiv_cont : Continuous (fderiv ℝ α) :=
    h_smooth.continuous_fderiv (by norm_num)
  have h_fderiv_supp : HasCompactSupport (fderiv ℝ α) :=
    HasCompactSupport.fderiv ℝ h_supp
  obtain ⟨M', hM'⟩ :=
    h_fderiv_cont.bounded_above_of_compact_support h_fderiv_supp
  refine ⟨M', ?_, hM'⟩
  exact (norm_nonneg (fderiv ℝ α 0)).trans (hM' 0)

/-- Pointwise bound on the directional derivative `‖αDeriv α v ζ‖ ≤ M' · ‖v‖`. -/
theorem norm_αDeriv_le {α : ℂ → ℂ} {M' : ℝ}
    (h_bound : ∀ ζ : ℂ, ‖fderiv ℝ α ζ‖ ≤ M') (v ζ : ℂ) :
    ‖αDeriv α v ζ‖ ≤ M' * ‖v‖ := by
  unfold αDeriv
  refine ((fderiv ℝ α ζ).le_opNorm v).trans ?_
  exact mul_le_mul_of_nonneg_right (h_bound ζ) (norm_nonneg _)

end JacobianChallenge.PompeiuKernel

end
