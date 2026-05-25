/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Cauchy-Pompeiu kernel — Chip 3c-F (Section A): explicit radial bump

This file builds an **explicit radially-symmetric** bump function
`radialBump z ε : ℂ → ℝ` defined directly from `Real.smoothTransition`:

```
radialBump z ε η := Real.smoothTransition (2 - (2/ε) * ‖η - z‖).
```

Properties mirror those of Chip 3c-C₁'s `pompeiuBump`/`pompeiuCutoff`:

* `radialBump z ε η = 1` on `closedBall z (ε/2)`;
* `radialBump z ε η = 0` outside `ball z ε`;
* `0 ≤ radialBump z ε η ≤ 1` everywhere;
* `ContDiff ℝ n (radialBump z ε)`.

The key NEW property — which mathlib's abstract `ContDiffBump`
(behind the `someContDiffBumpBase` typeclass mechanism) does not
directly expose — is **radial symmetry**:
```
radialBump z ε η = ψ_ε (‖η - z‖)
```
where `ψ_ε r := Real.smoothTransition (2 - 2r/ε)`. This is the
exact structure the radial-Wirtinger formula (Chip 3c-F Section B)
needs.

`radialCutoff z ε η := 1 - radialBump z ε η` plays the role of
`pompeiuCutoff` in the second-summand DCT limit; the same algebraic
chain (`regInvSub`, `partialZBar_mul`, rectangle Stokes, plane-form
balance, DCT) carries through with `radialCutoff` in place of
`pompeiuCutoff`. Chip 3c-F Section C performs the radial-bump rescaling
that extracts the universal constant `-π`.

## Main definitions

* `psiBump (ε : ℝ) (r : ℝ) : ℝ := Real.smoothTransition (2 - 2 * r / ε)`
  — the radial profile.
* `radialBump (z : ℂ) (ε : ℝ) (η : ℂ) : ℝ := psiBump ε ‖η - z‖`
  — the bump itself.
* `radialCutoff (z : ℂ) (ε : ℝ) (η : ℂ) : ℝ := 1 - radialBump z ε η`.

## Main results

* `radialBump_eq_one_of_mem_closedBall_half`
* `radialBump_eq_zero_of_not_mem_ball`
* `radialBump_nonneg`, `radialBump_le_one`
* `radialBump_contDiff` (the `ContDiff` lift)
* `radialCutoff_*` mirrors of the above.

No `sorry`, no `axiom`. -/

noncomputable section

open Complex Filter Set Topology Metric Real
open scoped Topology

namespace JacobianChallenge.PompeiuKernel

/-! ## Radial profile -/

/-- The 1D radial profile of the bump: `ψ_ε(r) := smoothTransition(2 - 2r/ε)`.
* `ψ_ε(r) = 1` for `r ≤ ε/2` (where `2 - 2r/ε ≥ 1`).
* `ψ_ε(r) = 0` for `r ≥ ε` (where `2 - 2r/ε ≤ 0`).
* Smooth everywhere. -/
def psiBump (ε : ℝ) (r : ℝ) : ℝ :=
  Real.smoothTransition (2 - 2 * r / ε)

lemma psiBump_eq_one_of_le_half {ε : ℝ} (hε : 0 < ε) {r : ℝ} (hr : r ≤ ε / 2) :
    psiBump ε r = 1 := by
  unfold psiBump
  apply Real.smoothTransition.one_of_one_le
  -- Need: 1 ≤ 2 - 2r/ε, i.e., 2r/ε ≤ 1, i.e., 2r ≤ ε.
  have h2r : 2 * r ≤ ε := by linarith
  have : 2 * r / ε ≤ 1 := by
    rw [div_le_one hε]; exact h2r
  linarith

lemma psiBump_eq_zero_of_ge {ε : ℝ} (hε : 0 < ε) {r : ℝ} (hr : ε ≤ r) :
    psiBump ε r = 0 := by
  unfold psiBump
  apply Real.smoothTransition.zero_of_nonpos
  -- Need: 2 - 2r/ε ≤ 0, i.e., 2 ≤ 2r/ε, i.e., 2ε ≤ 2r, i.e., ε ≤ r.
  have h1 : 1 ≤ r / ε := (one_le_div hε).mpr hr
  have h2 : 2 ≤ 2 * (r / ε) := by linarith
  have h3 : 2 * r / ε = 2 * (r / ε) := by ring
  linarith [h3 ▸ h2]

lemma psiBump_nonneg (ε : ℝ) (r : ℝ) : 0 ≤ psiBump ε r :=
  Real.smoothTransition.nonneg _

lemma psiBump_le_one (ε : ℝ) (r : ℝ) : psiBump ε r ≤ 1 :=
  Real.smoothTransition.le_one _

lemma psiBump_contDiff {ε : ℝ} (hε : 0 < ε) {n : ℕ∞} :
    ContDiff ℝ n (psiBump ε) := by
  unfold psiBump
  apply Real.smoothTransition.contDiff.comp
  exact (contDiff_const.sub ((contDiff_const.mul contDiff_id).div_const ε))

/-! ## The radial bump on `ℂ` -/

/-- The radially-symmetric bump function on `ℂ` centered at `z`:
```
radialBump z ε η := ψ_ε(‖η - z‖).
```
Equals `1` on `closedBall z (ε/2)`, `0` outside `ball z ε`. -/
def radialBump (z : ℂ) (ε : ℝ) (η : ℂ) : ℝ :=
  psiBump ε ‖η - z‖

lemma radialBump_eq_psi (z : ℂ) (ε : ℝ) (η : ℂ) :
    radialBump z ε η = psiBump ε ‖η - z‖ := rfl

lemma radialBump_eq_one_of_mem_closedBall_half
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) {η : ℂ} (hη : η ∈ closedBall z (ε / 2)) :
    radialBump z ε η = 1 := by
  unfold radialBump
  apply psiBump_eq_one_of_le_half hε
  rw [Metric.mem_closedBall, dist_eq_norm] at hη
  exact hη

lemma radialBump_eq_zero_of_not_mem_ball
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) {η : ℂ} (hη : η ∉ ball z ε) :
    radialBump z ε η = 0 := by
  unfold radialBump
  apply psiBump_eq_zero_of_ge hε
  rw [Metric.mem_ball, not_lt, dist_eq_norm] at hη
  exact hη

lemma radialBump_nonneg (z : ℂ) (ε : ℝ) (η : ℂ) : 0 ≤ radialBump z ε η :=
  psiBump_nonneg ε _

lemma radialBump_le_one (z : ℂ) (ε : ℝ) (η : ℂ) : radialBump z ε η ≤ 1 :=
  psiBump_le_one ε _

/-- `radialBump z ε` is `ContDiff ℝ n`. Off `z`, the norm `‖· - z‖`
is smooth (via `contDiffAt_norm`) and `psiBump ε` is smooth, so the
composition is smooth. At `η = z`, `radialBump` is locally constant
`1` on `ball z (ε/2)`, hence smooth there too. -/
lemma radialBump_contDiff (z : ℂ) {ε : ℝ} (hε : 0 < ε) {n : ℕ∞} :
    ContDiff ℝ n (radialBump z ε) := by
  rw [contDiff_iff_contDiffAt]
  intro η
  by_cases h_ne : η = z
  · -- `radialBump z ε` is constantly `1` on `ball z (ε/2)`, a nbhd of z.
    subst h_ne
    have h_nhds : Metric.ball η (ε / 2) ∈ 𝓝 η :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (half_pos hε))
    have h_eventually : radialBump η ε =ᶠ[𝓝 η] (fun _ : ℂ => (1 : ℝ)) := by
      filter_upwards [h_nhds] with w hw
      exact radialBump_eq_one_of_mem_closedBall_half η hε
        (Metric.ball_subset_closedBall hw)
    exact contDiffAt_const.congr_of_eventuallyEq h_eventually
  · -- `η ≠ z`: chain rule on `psiBump ε ∘ (‖· - z‖)`.
    have h_sub : ContDiffAt ℝ n (fun w : ℂ => w - z) η :=
      (contDiff_id.sub contDiff_const).contDiffAt
    have h_ne_zero : (fun w : ℂ => w - z) η ≠ 0 := sub_ne_zero.mpr h_ne
    have h_norm : ContDiffAt ℝ n (fun w : ℂ => ‖w - z‖) η :=
      h_sub.norm ℝ h_ne_zero
    have h_psi : ContDiffAt ℝ n (psiBump ε) (‖η - z‖) :=
      (psiBump_contDiff hε).contDiffAt
    exact h_psi.comp η h_norm

/-! ## The radial cutoff -/

/-- The cutoff `1 - radialBump`: equals `0` on `closedBall z (ε/2)` and
`1` outside `ball z ε`. -/
def radialCutoff (z : ℂ) (ε : ℝ) (η : ℂ) : ℝ :=
  1 - radialBump z ε η

lemma radialCutoff_eq_zero_of_mem_closedBall_half
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) {η : ℂ} (hη : η ∈ closedBall z (ε / 2)) :
    radialCutoff z ε η = 0 := by
  unfold radialCutoff
  rw [radialBump_eq_one_of_mem_closedBall_half z hε hη]; ring

lemma radialCutoff_eq_one_of_not_mem_ball
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) {η : ℂ} (hη : η ∉ ball z ε) :
    radialCutoff z ε η = 1 := by
  unfold radialCutoff
  rw [radialBump_eq_zero_of_not_mem_ball z hε hη]; ring

lemma radialCutoff_nonneg (z : ℂ) (ε : ℝ) (η : ℂ) : 0 ≤ radialCutoff z ε η := by
  unfold radialCutoff
  linarith [radialBump_le_one z ε η]

lemma radialCutoff_le_one (z : ℂ) (ε : ℝ) (η : ℂ) : radialCutoff z ε η ≤ 1 := by
  unfold radialCutoff
  linarith [radialBump_nonneg z ε η]

/-- `radialCutoff z ε` is `ContDiff ℝ n` (since it is `1 - radialBump`). -/
lemma radialCutoff_contDiff (z : ℂ) {ε : ℝ} (hε : 0 < ε) {n : ℕ∞} :
    ContDiff ℝ n (radialCutoff z ε) := by
  unfold radialCutoff
  exact contDiff_const.sub (radialBump_contDiff z hε)

/-- Eventually `0` on a neighborhood of `z`. -/
lemma radialCutoff_eventuallyEq_zero (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    radialCutoff z ε =ᶠ[𝓝 z] 0 := by
  have h_ball_mem : Metric.ball z (ε / 2) ∈ 𝓝 z :=
    Metric.ball_mem_nhds z (half_pos hε)
  filter_upwards [h_ball_mem] with η hη
  show radialCutoff z ε η = (0 : ℂ → ℝ) η
  apply radialCutoff_eq_zero_of_mem_closedBall_half z hε
  exact Metric.ball_subset_closedBall hη

end JacobianChallenge.PompeiuKernel

end
