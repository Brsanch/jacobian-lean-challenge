/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Group.Measure

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Cauchy-Pompeiu kernel — Chip 1a: definitions + translation reduction

The Pompeiu kernel `u(z) := -(1/π) ∫_ℂ α(ζ) · (ζ - z)⁻¹ dA(ζ)` solves
`∂̄u = α` for smooth compactly-supported `α : ℂ → ℂ`. This file is the
foundational layer of the Pompeiu kernel arc on the way to closing
Item 14 (`Basic.lean:73`).

## Chip 1 arc

* **Chip 1a (this file)** — definitions of `pompeiuIntegrand` and
  `pompeiuKernel`; measurability; translation-invariance reduction
  (`‖ζ - z‖⁻¹` integrability reduces to the centred-at-origin case);
  trivial integrability case (`z` outside a compact `K`).
* Chip 1b (next session) — polar-coordinate proof that `‖ζ‖⁻¹` is
  integrable on `closedBall 0 R` (with explicit value `2π · R`).
* Chip 1c — assemble Chips 1a + 1b into integrability of the full
  Pompeiu integrand for continuous compactly-supported `α`.
* Chip 2+ — kernel well-definedness, smoothness, the `∂̄u = α` identity.

## What ships in Chip 1a

* `pompeiuIntegrand` — `α(ζ) · (ζ - z)⁻¹` as a `ℂ → ℂ → ℂ → ℂ` function.
* `pompeiuKernel` — the kernel `-(π⁻¹) · ∫ pompeiuIntegrand α z ζ dA`.
* `measurable_pompeiuIntegrand_snd` — measurability of the integrand
  in `ζ` for fixed `z` and measurable `α`.
* `aestronglyMeasurable_pompeiuIntegrand_snd` — `AEStronglyMeasurable`
  version for continuous `α`.
* `integrableOn_inv_norm_sub_iff_origin` — the translation-invariance
  reduction.
* `integrableOn_inv_norm_sub_of_not_mem_compact` — trivial case where
  `z` is outside the compact integration domain.

No `sorry`, no `axiom`. -/

noncomputable section

open MeasureTheory Complex Filter Set Topology Metric
open scoped Real Topology ENNReal

namespace JacobianChallenge.PompeiuKernel

/-! ## Definitions -/

/-- The Pompeiu kernel integrand at base point `z`, evaluated at `ζ`:
`α(ζ) · (ζ - z)⁻¹`. Has a `1/(ζ - z)` singularity at `ζ = z` (locally
integrable in 2D). -/
def pompeiuIntegrand (α : ℂ → ℂ) (z ζ : ℂ) : ℂ :=
  α ζ * (ζ - z)⁻¹

/-- The Pompeiu kernel `u(z) := -(1/π) ∫_ℂ α(ζ) · (ζ - z)⁻¹ dA(ζ)`.
When the integrand is integrable (Chip 1c), this gives a smooth
function with `∂̄u = α` (Chip 2+). The constant `-(1/π)` is chosen so
that this is the canonical inverse of `∂̄` on `ℂ` via the Cauchy-Pompeiu
formula. -/
def pompeiuKernel (α : ℂ → ℂ) (z : ℂ) : ℂ :=
  -((Real.pi : ℂ)⁻¹) * ∫ ζ, pompeiuIntegrand α z ζ

/-! ## Measurability -/

/-- The Pompeiu integrand is measurable in `ζ` for fixed `z`, provided
`α` is measurable. -/
lemma measurable_pompeiuIntegrand_snd
    {α : ℂ → ℂ} (h_α : Measurable α) (z : ℂ) :
    Measurable (fun ζ : ℂ => pompeiuIntegrand α z ζ) := by
  unfold pompeiuIntegrand
  exact h_α.mul ((measurable_id.sub measurable_const).inv)

/-- The Pompeiu integrand is `AEStronglyMeasurable` in `ζ` for fixed
`z`, provided `α` is continuous (hence strongly measurable). -/
lemma aestronglyMeasurable_pompeiuIntegrand_snd
    {α : ℂ → ℂ} (h_α : Continuous α) (z : ℂ) :
    AEStronglyMeasurable (fun ζ : ℂ => pompeiuIntegrand α z ζ) volume := by
  unfold pompeiuIntegrand
  refine AEStronglyMeasurable.mul h_α.aestronglyMeasurable ?_
  exact ((measurable_id.sub measurable_const).inv).aestronglyMeasurable

/-! ## Translation-invariance reduction

The kernel `‖ζ - z‖⁻¹` translates to the centred kernel `‖ζ‖⁻¹` under
`ζ ↦ ζ - z`. Lebesgue measure on `ℂ` is translation invariant (Haar
measure on the additive group `ℂ`). So integrability of `‖ζ - z‖⁻¹` on
`closedBall z R` reduces to integrability of `‖ζ‖⁻¹` on
`closedBall 0 R`.

This is the **reduction lemma** that lets Chip 1b focus on the
origin case only. -/

/-- The translation `ζ ↦ ζ - z` is a measurable embedding on `ℂ`. -/
private lemma measurableEmbedding_sub_const (z : ℂ) :
    MeasurableEmbedding (fun ζ : ℂ => ζ - z) :=
  (Homeomorph.subRight z).measurableEmbedding

/-- The translation `ζ ↦ ζ - z` is volume-preserving on `ℂ`. -/
private lemma measurePreserving_sub_const (z : ℂ) :
    MeasurePreserving (fun ζ : ℂ => ζ - z) volume volume :=
  measurePreserving_sub_right volume z

/-- The closed ball at `z` is the preimage of the closed ball at `0`
under `ζ ↦ ζ - z`. -/
private lemma closedBall_eq_preimage_sub_const (z : ℂ) (R : ℝ) :
    closedBall z R = (fun ζ : ℂ => ζ - z) ⁻¹' closedBall (0 : ℂ) R := by
  ext ζ
  simp [Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg]

/-- **Translation-invariance reduction.** Integrability of
`‖ζ - z‖⁻¹` on `closedBall z R` is equivalent to integrability of
`‖ζ‖⁻¹` on `closedBall 0 R`. -/
theorem integrableOn_inv_norm_sub_iff_origin (z : ℂ) (R : ℝ) :
    IntegrableOn (fun ζ : ℂ => ‖ζ - z‖⁻¹) (closedBall z R) volume
      ↔ IntegrableOn (fun ζ : ℂ => ‖ζ‖⁻¹) (closedBall (0 : ℂ) R) volume := by
  have h_mp := measurePreserving_sub_const z
  have h_emb := measurableEmbedding_sub_const z
  rw [closedBall_eq_preimage_sub_const z R]
  have h_comp : (fun ζ : ℂ => ‖ζ - z‖⁻¹)
      = (fun ζ : ℂ => ‖ζ‖⁻¹) ∘ (fun ζ : ℂ => ζ - z) := by
    funext ζ; rfl
  rw [h_comp]
  exact h_mp.integrableOn_comp_preimage h_emb

/-! ## A trivial integrability case: `z` not in a compact `K`

When `z` lies outside the compact set `K`, the kernel `‖ζ - z‖⁻¹` is
bounded on `K` (by `(dist(K, z))⁻¹`), so integrability on `K` is
trivial from continuity-on-compact. -/

/-- If `z ∉ K` and `K` is compact, then `‖ζ - z‖⁻¹` is integrable on `K`. -/
theorem integrableOn_inv_norm_sub_of_not_mem_compact
    (z : ℂ) {K : Set ℂ} (hK : IsCompact K) (hz : z ∉ K) :
    IntegrableOn (fun ζ : ℂ => ‖ζ - z‖⁻¹) K volume := by
  -- Continuous on `K` (since `ζ - z ≠ 0` for ζ ∈ K).
  have h_cont : ContinuousOn (fun ζ : ℂ => ‖ζ - z‖⁻¹) K := by
    intro ζ hζ
    have h_ne : ζ - z ≠ 0 := sub_ne_zero.mpr (fun h => hz (h ▸ hζ))
    have h_norm_ne : ‖ζ - z‖ ≠ 0 := norm_ne_zero_iff.mpr h_ne
    -- `(fun ζ => ‖ζ - z‖)` is continuous; its reciprocal is continuous where nonzero.
    have h_inner : ContinuousAt (fun ζ : ℂ => ‖ζ - z‖) ζ :=
      (continuous_norm.comp (continuous_id.sub continuous_const)).continuousAt
    exact (h_inner.inv₀ h_norm_ne).continuousWithinAt
  exact h_cont.integrableOn_compact hK

end JacobianChallenge.PompeiuKernel

end
