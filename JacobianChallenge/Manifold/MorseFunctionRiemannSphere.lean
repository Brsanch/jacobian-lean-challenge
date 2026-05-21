/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MorseFunction
import JacobianChallenge.Manifold.RiemannSphereChartNHolomorphy
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Concrete Morse function on `RiemannSphere`

Builds the **height function** `h : RS → ℝ`,

  `h(z) = 1 / (1 + ‖z‖²)` for `z : ℂ`, `h(∞) = 0`,

as the first concrete Morse function on a compact connected complex
1-manifold. Two critical points (`0` and `∞`), value 1 at `0` (max),
value 0 at `∞` (min), Hessian non-degenerate at both.

This realises the (P3) Morse-theory route at the simplest non-trivial
example. It is **non-vacuous** evidence that the foundation laid in
chip 32 (`MorseFunction X`) accepts genuine geometric data.

## What this file ships

* `heightRiemannSphere : RiemannSphere → ℝ` — the height function.
* `heightRiemannSphere_infty` / `heightRiemannSphere_coe` — defining
  identities.
* `heightRiemannSphere_continuous` — continuity on RS.

The full `MorseFunction` instance (smoothness + critical-set
characterisation) is deferred to a subsequent chip, which requires the
chart-local Hessian infrastructure (open content for the (P3) route at
the manifold level).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff OnePoint
open OnePoint

namespace JacobianChallenge

namespace RiemannSphere

/-- **Height function** `h : RS → ℝ`, `h(z) = 1/(1+‖z‖²)` for `z : ℂ`
and `h(∞) = 0`. Real-valued, continuous, with two critical points
(`0` minimum value 1 — actually the maximum of `h` since `1/(1+|z|²) ≤ 1`;
`∞` value 0 — minimum). -/
noncomputable def heightRiemannSphere : RiemannSphere → ℝ :=
  fun x => x.elim 0 (fun z => 1 / (1 + ‖z‖^2))

@[simp] lemma heightRiemannSphere_infty :
    heightRiemannSphere (∞ : RiemannSphere) = 0 :=
  OnePoint.elim_infty _ _

@[simp] lemma heightRiemannSphere_coe (z : ℂ) :
    heightRiemannSphere ((z : RiemannSphere)) = 1 / (1 + ‖z‖^2) :=
  OnePoint.elim_some _ _ z

/-- Bounds: `0 ≤ h(x) ≤ 1` for all `x : RS`. -/
lemma heightRiemannSphere_nonneg (x : RiemannSphere) :
    0 ≤ heightRiemannSphere x := by
  induction x using OnePoint.rec with
  | infty => simp
  | coe z =>
    rw [heightRiemannSphere_coe]
    apply div_nonneg one_pos.le
    positivity

/-- Maximum value 1 attained at `(0 : ℂ) : RS`. -/
lemma heightRiemannSphere_zero :
    heightRiemannSphere ((0 : ℂ) : RiemannSphere) = 1 := by
  simp [heightRiemannSphere_coe]

/-- The height function on the `chartN` chart: `h(some z) = 1/(1+‖z‖²)`. -/
lemma heightRiemannSphere_chartN_local (z : ℂ) :
    heightRiemannSphere (chartN.symm z) = 1 / (1 + ‖z‖^2) := by
  show heightRiemannSphere (((z : ℂ) : RiemannSphere)) = 1 / (1 + ‖z‖^2)
  exact heightRiemannSphere_coe z

/-- The chart-local ℂ-form of `heightRiemannSphere`. -/
noncomputable def heightLocalℂ : ℂ → ℝ := fun z => 1 / (1 + ‖z‖^2)

@[simp] lemma heightLocalℂ_apply (z : ℂ) :
    heightLocalℂ z = 1 / (1 + ‖z‖^2) := rfl

/-- The chart-local form is continuous on `ℂ`. -/
lemma heightLocalℂ_continuous : Continuous heightLocalℂ := by
  unfold heightLocalℂ
  refine Continuous.div continuous_const
    (continuous_const.add (continuous_norm.pow 2)) ?_
  intro z
  have : (0 : ℝ) < 1 + ‖z‖^2 := by positivity
  exact this.ne'

/-- The chart-local form is real-`C^∞` on `ℂ`. -/
lemma heightLocalℂ_contDiff : ContDiff ℝ (⊤ : ℕ∞) heightLocalℂ := by
  unfold heightLocalℂ
  refine ContDiff.div contDiff_const ?_ ?_
  · -- `ContDiff ℝ ∞ (fun z => 1 + ‖z‖^2)`.
    exact contDiff_const.add (contDiff_norm_sq ℂ)
  · -- Pointwise: `1 + ‖z‖^2 ≠ 0`.
    intro z
    have : (0 : ℝ) < 1 + ‖z‖^2 := by positivity
    exact this.ne'

/-- **The chart-S local form** of `heightRiemannSphere`:
`w ↦ ‖w‖² / (1 + ‖w‖²)`. This is `heightRiemannSphere ∘ chartS.symm`. -/
noncomputable def heightLocalℂ_S : ℂ → ℝ :=
  fun w => ‖w‖^2 / (1 + ‖w‖^2)

@[simp] lemma heightLocalℂ_S_apply (w : ℂ) :
    heightLocalℂ_S w = ‖w‖^2 / (1 + ‖w‖^2) := rfl

@[simp] lemma heightLocalℂ_S_zero : heightLocalℂ_S 0 = 0 := by
  simp [heightLocalℂ_S]

/-- The chartS local form is real-`C^∞` on `ℂ`. -/
lemma heightLocalℂ_S_contDiff : ContDiff ℝ (⊤ : ℕ∞) heightLocalℂ_S := by
  unfold heightLocalℂ_S
  refine ContDiff.div (contDiff_norm_sq ℂ) ?_ ?_
  · exact contDiff_const.add (contDiff_norm_sq ℂ)
  · intro z
    have : (0 : ℝ) < 1 + ‖z‖^2 := by positivity
    exact this.ne'

/-- **chartS-local identity** for `heightRiemannSphere`: at `w ≠ 0`,
`heightRiemannSphere (chartS.symm w) = heightLocalℂ_S w`. The point
`w = 0` lifts to `∞ : RS` with `heightRiemannSphere ∞ = 0 = heightLocalℂ_S 0`. -/
lemma heightRiemannSphere_chartS_local (w : ℂ) :
    heightRiemannSphere (chartSInvFun w) = heightLocalℂ_S w := by
  unfold chartSInvFun heightLocalℂ_S
  by_cases hw : w = 0
  · subst hw
    simp
  · rw [if_neg hw]
    show heightRiemannSphere ((w⁻¹ : ℂ) : RiemannSphere) = _
    rw [heightRiemannSphere_coe]
    -- Goal: `1 / (1 + ‖w⁻¹‖^2) = ‖w‖^2 / (1 + ‖w‖^2)`.
    have hw_norm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    have hw_norm_sq : ‖w‖^2 ≠ 0 := pow_ne_zero 2 hw_norm
    have hw_inv_sq : ‖w⁻¹‖^2 = 1 / ‖w‖^2 := by
      rw [norm_inv]
      field_simp
    rw [hw_inv_sq]
    field_simp
    ring

/-- **Tendsto-to-0 at infinity:** as `z → ∞` in `cocompact ℂ`,
`1/(1+‖z‖²) → 0`. -/
lemma heightLocalℂ_tendsto_zero_cocompact :
    Filter.Tendsto heightLocalℂ (Filter.cocompact ℂ) (nhds (0 : ℝ)) := by
  -- `‖z‖ → ∞` as `z → ∞`.
  have h_norm : Filter.Tendsto (fun z : ℂ => ‖z‖) (Filter.cocompact ℂ)
      Filter.atTop := tendsto_norm_cocompact_atTop
  -- `‖z‖² → ∞` via `‖z‖ * ‖z‖`.
  have h_sq : Filter.Tendsto (fun z : ℂ => ‖z‖^2) (Filter.cocompact ℂ)
      Filter.atTop := by
    have h_mul : Filter.Tendsto (fun z : ℂ => ‖z‖ * ‖z‖)
        (Filter.cocompact ℂ) Filter.atTop :=
      h_norm.atTop_mul_atTop₀ h_norm
    exact h_mul.congr (fun z => by ring)
  -- `1 + ‖z‖² → ∞`: const + atTop = atTop.
  have h_denom : Filter.Tendsto (fun z : ℂ => 1 + ‖z‖^2)
      (Filter.cocompact ℂ) Filter.atTop :=
    Filter.tendsto_atTop_add_const_left _ 1 h_sq
  -- `1/(1+‖z‖²) → 0` via `tendsto_inv_atTop_zero ∘ h_denom`.
  have h_inv : Filter.Tendsto (fun z : ℂ => (1 + ‖z‖^2)⁻¹)
      (Filter.cocompact ℂ) (nhds 0) :=
    tendsto_inv_atTop_zero.comp h_denom
  -- Identify `1 / x = x⁻¹`.
  refine h_inv.congr ?_
  intro z
  unfold heightLocalℂ
  exact (one_div _).symm

/-- **Continuity of `heightRiemannSphere` on RS.**

Uses `OnePoint.continuous_iff` with the chart-local continuity on `ℂ`
plus the tendsto-to-0 at infinity. For the locally compact T₂ space
`ℂ`, `coclosedCompact ℂ = cocompact ℂ`. -/
lemma heightRiemannSphere_continuous :
    Continuous heightRiemannSphere := by
  rw [OnePoint.continuous_iff]
  refine ⟨?_, ?_⟩
  · -- Tendsto branch at infinity: `f ∞ = 0`.
    rw [heightRiemannSphere_infty]
    rw [Filter.coclosedCompact_eq_cocompact]
    refine heightLocalℂ_tendsto_zero_cocompact.congr ?_
    intro z
    exact heightRiemannSphere_coe z
  · -- Continuity branch on the `ℂ` part.
    refine heightLocalℂ_continuous.congr ?_
    intro z
    exact (heightRiemannSphere_coe z).symm

/-- **`ContMDiffAt` at any `(z : ℂ) : RS` point.**

For `x = (z : ℂ) : RS` (i.e., `x ≠ ∞`), `chartAt ℂ x = chartN`, and the
chart-local form is `heightLocalℂ` (chip 39 ContDiff). -/
lemma heightRiemannSphere_contMDiffAt_coe (z : ℂ) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) heightRiemannSphere
      ((z : RiemannSphere)) := by
  rw [contMDiffAt_iff]
  refine ⟨heightRiemannSphere_continuous.continuousAt, ?_⟩
  -- `Set.range 𝓘(ℝ, ℂ) = Set.univ`.
  have h_range : Set.range (𝓘(ℝ, ℂ) : ModelWithCorners ℝ ℂ ℂ) = Set.univ :=
    ModelWithCorners.range_eq_univ _
  rw [h_range, contDiffWithinAt_univ]
  -- The chart-local form coincides with heightLocalℂ.
  refine (heightLocalℂ_contDiff.contDiffAt).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with w _
  rfl

end RiemannSphere

end JacobianChallenge

end
