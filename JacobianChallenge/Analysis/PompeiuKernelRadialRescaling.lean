/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.PompeiuKernelRadialIntegral
import JacobianChallenge.Analysis.PompeiuKernelRadialWirtinger
import JacobianChallenge.Analysis.PompeiuKernelSecondSummandIdentity

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Cauchy-Pompeiu kernel — Chip 3c-F-3d-2-prep: rescaling identities for the radial bump

The algebraic identities under the rescaling `η = z + ε·w`:

```
radialBump z ε (z + ε·w) = radialBump 0 1 w           = psiBump 1 ‖w‖,
radialBumpComplex z ε (z + ε·w) = unitRadialBumpC w,
radialCutoff z ε (z + ε·w) = radialCutoff 0 1 w,
radialCutoffComplex z ε (z + ε·w) = ((radialCutoff 0 1 w : ℝ) : ℂ).
```

These follow from `psiBump ε (ε·r) = psiBump 1 r` (a direct calculation
in `Real.smoothTransition`'s argument), combined with the norm identity
`‖z + ε·w - z‖ = ε · ‖w‖` for `ε ≥ 0`.

Used by Chip 3c-F-3d-2 (the substitution identity) and Chip 3c-F-3d-3
(the DCT on the substituted integral). All sorry- and axiom-free. -/

noncomputable section

open Complex Filter Set Topology Metric
open scoped Topology

namespace JacobianChallenge.PompeiuKernel

/-! ## Scalar identity: `psiBump ε (ε·r) = psiBump 1 r` -/

/-- The 1D profile `psiBump` is invariant under the rescaling
`(ε, r) ↦ (1, ε⁻¹·r)`: `psiBump ε (ε·r) = psiBump 1 r`. -/
lemma psiBump_rescale {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    psiBump ε (ε * r) = psiBump 1 r := by
  unfold psiBump
  -- psiBump ε (ε·r) = smoothTransition (2 - 2 · (ε·r) / ε)
  --                 = smoothTransition (2 - 2·r)
  --                 = smoothTransition (2 - 2·r / 1)
  --                 = psiBump 1 r.
  congr 1
  field_simp

/-! ## Norm identity for `z + ε·w - z` -/

/-- `‖(z + ε·w) - z‖ = ε · ‖w‖` for `ε ≥ 0`. -/
lemma norm_z_add_smul_sub {z w : ℂ} {ε : ℝ} (hε : 0 ≤ ε) :
    ‖(z + (ε : ℂ) * w) - z‖ = ε * ‖w‖ := by
  have h : (z + (ε : ℂ) * w) - z = (ε : ℂ) * w := by ring
  rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε]

/-! ## Rescaling of the radial bump -/

/-- `radialBump z ε (z + ε·w) = psiBump 1 ‖w‖` for `ε > 0`. -/
lemma radialBump_at_rescaled {z : ℂ} {ε : ℝ} (hε : 0 < ε) (w : ℂ) :
    radialBump z ε (z + (ε : ℂ) * w) = psiBump 1 ‖w‖ := by
  unfold radialBump
  rw [norm_z_add_smul_sub hε.le]
  exact psiBump_rescale hε ‖w‖

/-- `unitRadialBumpC w = ((psiBump 1 ‖w‖ : ℝ) : ℂ)`: the `ℂ`-valued
unit bump equals the lifted `psiBump 1 ‖w‖`. Restates
`unitRadialBumpC_eq_psi`. -/
lemma unitRadialBumpC_value (w : ℂ) :
    unitRadialBumpC w = ((psiBump 1 ‖w‖ : ℝ) : ℂ) :=
  unitRadialBumpC_eq_psi w

/-- **Rescaling identity for `radialBumpComplex`.** For `ε > 0`,
`radialBumpComplex z ε (z + ε·w) = unitRadialBumpC w`. -/
lemma radialBumpComplex_at_rescaled {z : ℂ} {ε : ℝ} (hε : 0 < ε) (w : ℂ) :
    ((radialBump z ε (z + (ε : ℂ) * w) : ℝ) : ℂ) = unitRadialBumpC w := by
  rw [radialBump_at_rescaled hε, unitRadialBumpC_value]

/-! ## Rescaling of the radial cutoff -/

/-- `radialCutoff z ε (z + ε·w) = 1 - psiBump 1 ‖w‖` for `ε > 0`. -/
lemma radialCutoff_at_rescaled {z : ℂ} {ε : ℝ} (hε : 0 < ε) (w : ℂ) :
    radialCutoff z ε (z + (ε : ℂ) * w) = 1 - psiBump 1 ‖w‖ := by
  unfold radialCutoff
  rw [radialBump_at_rescaled hε]

/-- The unit-scale radial cutoff `ℂ`-valued: `radialCutoffComplex 0 1 w`. -/
lemma radialCutoffComplex_at_rescaled {z : ℂ} {ε : ℝ} (hε : 0 < ε) (w : ℂ) :
    radialCutoffComplex z ε (z + (ε : ℂ) * w) = radialCutoffComplex 0 1 w := by
  unfold radialCutoffComplex
  rw [radialCutoff_at_rescaled hε]
  unfold radialCutoff radialBump
  congr 1
  rw [sub_zero]

/-! ## Derivative of the rescaled profile -/

/-- `HasDerivAt (psiBump ε) (deriv (psiBump ε) r) r`. The 1D profile
is differentiable everywhere (it is `C^∞`). -/
lemma hasDerivAt_psiBump {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    HasDerivAt (psiBump ε) (deriv (psiBump ε) r) r :=
  ((psiBump_contDiff hε (n := 1)).differentiable
    (by norm_num)).differentiableAt.hasDerivAt

/-- **Derivative rescaling.** For `ε > 0`,
`deriv (psiBump ε) (ε * r) = ε⁻¹ * deriv (psiBump 1) r`.

Differentiating `psiBump_rescale : psiBump ε (ε * r) = psiBump 1 r`
both sides as functions of `r`: the LHS gives `ε · deriv (psiBump ε) (ε * r)`
by chain rule; the RHS gives `deriv (psiBump 1) r`. Equating and
dividing by `ε ≠ 0` produces the claim. -/
lemma deriv_psiBump_rescale {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    deriv (psiBump ε) (ε * r) = ε⁻¹ * deriv (psiBump 1) r := by
  -- LHS function: `fun r => psiBump ε (ε * r)`. Derivative at r:
  -- (deriv (psiBump ε) (ε * r)) * ε  (by chain rule).
  have h_inner : HasDerivAt (fun r : ℝ => ε * r) ε r := by
    have := (hasDerivAt_id r).const_mul ε
    simpa using this
  have h_lhs : HasDerivAt (fun r : ℝ => psiBump ε (ε * r))
      ((deriv (psiBump ε) (ε * r)) * ε) r :=
    (hasDerivAt_psiBump hε (ε * r)).comp r h_inner
  -- RHS function: `fun r => psiBump 1 r`. Derivative is `deriv (psiBump 1) r`.
  have h_rhs : HasDerivAt (psiBump 1) (deriv (psiBump 1) r) r :=
    hasDerivAt_psiBump one_pos r
  -- The two functions agree (psiBump_rescale).
  have h_eq : (fun r : ℝ => psiBump ε (ε * r)) = psiBump 1 := by
    funext r'
    exact psiBump_rescale hε r'
  -- Transport h_lhs through h_eq to compare with h_rhs.
  rw [h_eq] at h_lhs
  -- HasDerivAt gives unique derivative, so:
  have h_unique : (deriv (psiBump ε) (ε * r)) * ε = deriv (psiBump 1) r :=
    h_lhs.unique h_rhs
  -- Solve for `deriv (psiBump ε) (ε * r)`.
  have hε_ne : (ε : ℝ) ≠ 0 := ne_of_gt hε
  field_simp at h_unique ⊢
  linarith [h_unique]

/-! ## Eventual constancy of radial bumps near their centers -/

/-- `radialBumpComplex z ε =ᶠ[𝓝 z] 1`. -/
lemma radialBumpComplex_eventuallyEq_one (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (fun η : ℂ => ((radialBump z ε η : ℝ) : ℂ)) =ᶠ[𝓝 z] (fun _ => (1 : ℂ)) := by
  have h_nhds : Metric.ball z (ε / 2) ∈ 𝓝 z :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (half_pos hε))
  filter_upwards [h_nhds] with η hη
  have h_eq_one : radialBump z ε η = 1 :=
    radialBump_eq_one_of_mem_closedBall_half z hε (Metric.ball_subset_closedBall hη)
  show ((radialBump z ε η : ℝ) : ℂ) = (1 : ℂ)
  rw [h_eq_one]; norm_num

/-- `partialZBar (radialBumpComplex z ε) z = 0` (the lifted radial bump
is locally constant at its center). -/
lemma partialZBar_radialBumpComplex_at_z (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    partialZBar (fun η : ℂ => ((radialBump z ε η : ℝ) : ℂ)) z = 0 := by
  have h_eq : (fun η : ℂ => ((radialBump z ε η : ℝ) : ℂ)) =ᶠ[𝓝 z]
      (fun _ : ℂ => (1 : ℂ)) := radialBumpComplex_eventuallyEq_one z hε
  unfold partialZBar
  have h_fderiv : fderiv ℝ (fun η : ℂ => ((radialBump z ε η : ℝ) : ℂ)) z
      = fderiv ℝ (fun _ : ℂ => (1 : ℂ)) z :=
    Filter.EventuallyEq.fderiv_eq h_eq
  rw [h_fderiv]
  simp

/-- `partialZBar (unitRadialBumpC) 0 = 0` (the unit-scale bump is
locally constant at the origin). -/
lemma partialZBar_unitRadialBumpC_at_zero :
    partialZBar unitRadialBumpC 0 = 0 := by
  have h_fun_eq : unitRadialBumpC =
      (fun η : ℂ => ((radialBump 0 1 η : ℝ) : ℂ)) := by
    funext w; rfl
  rw [h_fun_eq]
  exact partialZBar_radialBumpComplex_at_z 0 one_pos

/-! ## Explicit `partialZBar` for the radial bump and unit bump (off center) -/

/-- For `η ≠ z`, `partialZBar (radialBumpComplex z ε) η` evaluates via
`partialZBar_radial_of_ne` applied to `psiBump ε`. -/
lemma partialZBar_radialBumpComplex_of_ne
    {z η : ℂ} (hη : η ≠ z) {ε : ℝ} (hε : 0 < ε) :
    partialZBar (fun w : ℂ => ((radialBump z ε w : ℝ) : ℂ)) η
      = ((deriv (psiBump ε) ‖η - z‖ / 2 : ℝ) : ℂ) * (η - z) / ‖η - z‖ := by
  have hψ : HasDerivAt (psiBump ε) (deriv (psiBump ε) ‖η - z‖) ‖η - z‖ :=
    hasDerivAt_psiBump hε ‖η - z‖
  have h_fun_eq :
      (fun w : ℂ => ((radialBump z ε w : ℝ) : ℂ))
        = (fun w : ℂ => ((psiBump ε ‖w - z‖ : ℝ) : ℂ)) := by
    funext w; rfl
  rw [h_fun_eq]
  exact partialZBar_radial_of_ne hη hψ

/-- For `w ≠ 0`, `partialZBar (unitRadialBumpC) w` evaluates via the
radial-Wirtinger formula at `z = 0, ψ = psiBump 1`. -/
lemma partialZBar_unitRadialBumpC_of_ne {w : ℂ} (hw : w ≠ 0) :
    partialZBar unitRadialBumpC w
      = ((deriv (psiBump 1) ‖w‖ / 2 : ℝ) : ℂ) * w / ‖w‖ := by
  have h_eq := partialZBar_radialBumpComplex_of_ne (z := (0 : ℂ)) hw one_pos
  have h_fun_eq : unitRadialBumpC =
      (fun w : ℂ => ((radialBump 0 1 w : ℝ) : ℂ)) := by
    funext w; rfl
  rw [h_fun_eq, h_eq]
  simp

/-! ## The main pointwise rescaling identity for `partialZBar` -/

/-- **Chip 3c-F-3d-2b.** For `ε > 0` and any `w : ℂ`,
```
partialZBar (radialBumpComplex z ε) (z + ε·w)
  = ε⁻¹ · partialZBar (unitRadialBumpC) w.
```
At `w = 0` both sides are zero (locally constant `1` at the center).
At `w ≠ 0`, `partialZBar_radial_of_ne` evaluates each side in terms of
`deriv (psiBump ·) ‖·‖`, and `deriv_psiBump_rescale` cancels the ε. -/
theorem partialZBar_radialBumpComplex_rescaled
    {z : ℂ} {ε : ℝ} (hε : 0 < ε) (w : ℂ) :
    partialZBar (fun η : ℂ => ((radialBump z ε η : ℝ) : ℂ)) (z + (ε : ℂ) * w)
      = (ε : ℂ)⁻¹ * partialZBar unitRadialBumpC w := by
  by_cases hw : w = 0
  · -- Both sides 0: at w = 0, the substituted point is z and the unit
    -- bump is at 0.
    subst hw
    simp only [mul_zero, add_zero, partialZBar_unitRadialBumpC_at_zero]
    exact partialZBar_radialBumpComplex_at_z z hε
  · -- η = z + εw ≠ z.
    have h_η_ne : z + (ε : ℂ) * w ≠ z := by
      intro h
      have h_diff : (ε : ℂ) * w = 0 := by linear_combination h
      have hε_ne : (ε : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hε
      rcases mul_eq_zero.mp h_diff with h | h
      · exact absurd h hε_ne
      · exact hw h
    rw [partialZBar_radialBumpComplex_of_ne h_η_ne hε,
        partialZBar_unitRadialBumpC_of_ne hw]
    have h_norm : ‖(z + (ε : ℂ) * w) - z‖ = ε * ‖w‖ := norm_z_add_smul_sub hε.le
    have h_diff : (z + (ε : ℂ) * w) - z = (ε : ℂ) * w := by ring
    rw [h_norm, h_diff, deriv_psiBump_rescale hε]
    have hε_C_ne : (ε : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hε
    have hw_norm_ne : (‖w‖ : ℂ) ≠ 0 := by
      exact_mod_cast (norm_ne_zero_iff.mpr hw)
    push_cast
    field_simp

end JacobianChallenge.PompeiuKernel
