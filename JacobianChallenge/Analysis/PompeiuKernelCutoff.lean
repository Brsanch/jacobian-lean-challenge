/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Cauchy-Pompeiu kernel — Chip 3c-C₁: smooth cutoff around the singularity

This file defines a `C^∞` cutoff function `pompeiuCutoff z ε` on `ℂ`
that vanishes on a neighborhood of `z` and equals `1` outside
`ball z ε`. The cutoff is the regularizer used in Chip 3c-C₂'s
rectangle-Stokes argument: while the raw Pompeiu integrand
`α(η) · (η - z)⁻¹` is unbounded at `η = z` (so mathlib's rectangle
Stokes `Hc : ContinuousOn f (rect)` fails), the regularized product
`α(η) · (η - z)⁻¹ · χ_ε(η)` is `C^∞` everywhere and admits rectangle
Stokes directly. The `ε → 0` Lebesgue-DCT limit then recovers the
original identity.

## Chip 3 arc context

* Chip 3a, 3b — small-disc limit + algebraic bridge.
* Chip 3c-A (`PompeiuKernelLeibniz.lean`) — pointwise `partialZBar` reduction.
* Chip 3c-B (`PompeiuKernelMulInvFDeriv.lean`) — `HasFDerivAt` off `z`.
* **Chip 3c-C₁ (this file)** — smooth cutoff `pompeiuCutoff z ε` and its key
  properties (vanishing near `z`, identity outside `ball z ε`, bounds,
  smoothness).
* Chip 3c-C₂ — smoothness of the regularized integrand
  `(η - z)⁻¹ · χ_ε(η)` everywhere on `ℂ` (using that `χ_ε ≡ 0` on a
  neighborhood of `z`).
* Chip 3c-C₃ onwards — rectangle-Stokes invocation + outer-boundary
  vanishing + DCT limit.

## Main results

* `pompeiuCutoff z ε hε : ℂ → ℝ` — the cutoff function.
* `pompeiuCutoff_eq_zero_of_mem_closedBall_half` — vanishes on
  `closedBall z (ε / 2)`.
* `pompeiuCutoff_eq_one_of_not_mem_ball` — equals `1` outside
  `ball z ε`.
* `pompeiuCutoff_nonneg`, `pompeiuCutoff_le_one` — pointwise bounds.
* `pompeiuCutoff_contDiff` — `C^∞` smoothness.
* `pompeiuCutoff_eventuallyEq_zero` — eventually `0` on `𝓝 z`.

No `sorry`, no `axiom`. -/

noncomputable section

open Complex Filter Set Topology Metric
open scoped Topology

namespace JacobianChallenge.PompeiuKernel

/-! ## The underlying `ContDiffBump` -/

/-- The `ContDiffBump` underlying `pompeiuCutoff z ε`: a smooth bump at
`z` of inner radius `ε/2` and outer radius `ε`. Equals `1` on
`closedBall z (ε / 2)` and `0` outside `ball z ε`. -/
def pompeiuBump (z : ℂ) {ε : ℝ} (hε : 0 < ε) : ContDiffBump z where
  rIn := ε / 2
  rOut := ε
  rIn_pos := half_pos hε
  rIn_lt_rOut := half_lt_self hε

/-! ## The cutoff function -/

/-- The cutoff function around the Pompeiu kernel singularity at `z`:
```
χ_ε(η) = 1 - bump(η),
```
where `bump : ContDiffBump z` with `rIn := ε/2`, `rOut := ε`. Then
`χ_ε ∈ C^∞`, `χ_ε(η) = 0` on `closedBall z (ε/2)`, `χ_ε(η) = 1`
outside `ball z ε`, and `0 ≤ χ_ε(η) ≤ 1` everywhere. -/
def pompeiuCutoff (z : ℂ) {ε : ℝ} (hε : 0 < ε) : ℂ → ℝ :=
  fun η => 1 - pompeiuBump z hε η

/-- `pompeiuCutoff z ε ζ = 0` for `ζ` in the closed half-ball
`closedBall z (ε / 2)`. -/
lemma pompeiuCutoff_eq_zero_of_mem_closedBall_half
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) {ζ : ℂ}
    (hζ : ζ ∈ closedBall z (ε / 2)) :
    pompeiuCutoff z hε ζ = 0 := by
  unfold pompeiuCutoff
  have h_bump_one : pompeiuBump z hε ζ = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    exact hζ
  rw [h_bump_one]; ring

/-- `pompeiuCutoff z ε ζ = 1` for `ζ` outside `ball z ε`. -/
lemma pompeiuCutoff_eq_one_of_not_mem_ball
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) {ζ : ℂ}
    (hζ : ζ ∉ ball z ε) :
    pompeiuCutoff z hε ζ = 1 := by
  unfold pompeiuCutoff
  have h_dist : ε ≤ dist ζ z := by
    rw [mem_ball, not_lt] at hζ; exact hζ
  have h_bump_zero : pompeiuBump z hε ζ = 0 :=
    ContDiffBump.zero_of_le_dist (pompeiuBump z hε) h_dist
  rw [h_bump_zero]; ring

/-- `0 ≤ pompeiuCutoff z ε ζ` for all `ζ`. -/
lemma pompeiuCutoff_nonneg (z : ℂ) {ε : ℝ} (hε : 0 < ε) (ζ : ℂ) :
    0 ≤ pompeiuCutoff z hε ζ := by
  unfold pompeiuCutoff
  have h_le_one : pompeiuBump z hε ζ ≤ 1 := ContDiffBump.le_one (pompeiuBump z hε)
  linarith

/-- `pompeiuCutoff z ε ζ ≤ 1` for all `ζ`. -/
lemma pompeiuCutoff_le_one (z : ℂ) {ε : ℝ} (hε : 0 < ε) (ζ : ℂ) :
    pompeiuCutoff z hε ζ ≤ 1 := by
  unfold pompeiuCutoff
  have h_nonneg : 0 ≤ pompeiuBump z hε ζ := ContDiffBump.nonneg (pompeiuBump z hε)
  linarith

/-- `pompeiuCutoff z ε` is `C^∞`. -/
lemma pompeiuCutoff_contDiff (z : ℂ) {ε : ℝ} (hε : 0 < ε) {n : ℕ∞} :
    ContDiff ℝ n (pompeiuCutoff z hε) := by
  unfold pompeiuCutoff
  exact contDiff_const.sub (ContDiffBump.contDiff (pompeiuBump z hε))

/-- `pompeiuCutoff z ε` is eventually `0` on a neighborhood of `z`.
Useful for showing that the regularized integrand
`(η - z)⁻¹ · pompeiuCutoff z ε η` is well-behaved at `η = z`. -/
lemma pompeiuCutoff_eventuallyEq_zero (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    pompeiuCutoff z hε =ᶠ[𝓝 z] 0 := by
  have h_bump_one : pompeiuBump z hε =ᶠ[𝓝 z] 1 :=
    ContDiffBump.eventuallyEq_one (pompeiuBump z hε)
  filter_upwards [h_bump_one] with η hη
  unfold pompeiuCutoff
  show 1 - pompeiuBump z hε η = (0 : ℂ → ℝ) η
  simp [hη]

/-! ## Compact support away from a neighborhood of `z`

`1 - pompeiuCutoff` (the "interior" part) is compactly supported,
equal to the bump. -/

/-- `1 - pompeiuCutoff z ε` is just the bump function, in particular
compactly supported in `closedBall z ε`. -/
lemma one_sub_pompeiuCutoff_eq_bump (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (1 : ℂ → ℝ) - pompeiuCutoff z hε = pompeiuBump z hε := by
  funext η
  unfold pompeiuCutoff
  simp

/-- `tsupport (1 - pompeiuCutoff z ε) ⊆ closedBall z ε`. -/
lemma tsupport_one_sub_pompeiuCutoff_subset (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    tsupport ((1 : ℂ → ℝ) - pompeiuCutoff z hε) ⊆ closedBall z ε := by
  rw [one_sub_pompeiuCutoff_eq_bump]
  exact (ContDiffBump.tsupport_eq (pompeiuBump z hε)).le

end JacobianChallenge.PompeiuKernel
