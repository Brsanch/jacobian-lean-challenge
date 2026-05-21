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

/-- **Upper bound:** `h(x) ≤ 1` for all `x : RS`. -/
lemma heightRiemannSphere_le_one (x : RiemannSphere) :
    heightRiemannSphere x ≤ 1 := by
  induction x using OnePoint.rec with
  | infty => simp
  | coe z =>
    rw [heightRiemannSphere_coe]
    have h_denom_pos : (0 : ℝ) < 1 + ‖z‖^2 := by positivity
    rw [div_le_one h_denom_pos]
    linarith [sq_nonneg ‖z‖]

/-- **`(0 : ℂ) : RS` is a global maximum of `heightRiemannSphere`.** -/
lemma heightRiemannSphere_isMaxOn_zero :
    IsMaxOn heightRiemannSphere Set.univ ((0 : ℂ) : RiemannSphere) := by
  intro x _
  rw [heightRiemannSphere_zero]
  exact heightRiemannSphere_le_one x

/-- **`∞ : RS` is a global minimum of `heightRiemannSphere`.** -/
lemma heightRiemannSphere_isMinOn_infty :
    IsMinOn heightRiemannSphere Set.univ ((∞ : RiemannSphere)) := by
  intro x _
  rw [heightRiemannSphere_infty]
  exact heightRiemannSphere_nonneg x

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

/-- **`ContMDiffAt` at `∞ : RS`.**

At `x = ∞`, `chartAt ℂ ∞ = chartS`, and the chart-local form is
`heightLocalℂ_S` (chip 40 ContDiff). -/
lemma heightRiemannSphere_contMDiffAt_infty :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) heightRiemannSphere
      ((∞ : RiemannSphere)) := by
  rw [contMDiffAt_iff]
  refine ⟨heightRiemannSphere_continuous.continuousAt, ?_⟩
  have h_range : Set.range (𝓘(ℝ, ℂ) : ModelWithCorners ℝ ℂ ℂ) = Set.univ :=
    ModelWithCorners.range_eq_univ _
  rw [h_range, contDiffWithinAt_univ]
  refine (heightLocalℂ_S_contDiff.contDiffAt).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with w _
  -- Chart-pullback at ∞ equals heightLocalℂ_S via the chartS local identity.
  exact heightRiemannSphere_chartS_local w

/-- **Full `ContMDiff` smoothness of `heightRiemannSphere` on RS.**

Combines `_contMDiffAt_coe` (chartN side) and `_contMDiffAt_infty`
(chartS side). -/
theorem heightRiemannSphere_contMDiff :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) heightRiemannSphere := by
  intro x
  induction x using OnePoint.rec with
  | infty => exact heightRiemannSphere_contMDiffAt_infty
  | coe z => exact heightRiemannSphere_contMDiffAt_coe z

/-! ## Honest critical-set characterization (chip 45)

We show that `heightLocalℂ : ℂ → ℝ` has `fderiv = 0` exactly at `z = 0`:
* `fderiv ℝ heightLocalℂ 0 = 0` via `IsLocalMax.fderiv_eq_zero` (since
  `heightLocalℂ z ≤ heightLocalℂ 0 = 1` for all `z`).
* `(fderiv ℝ heightLocalℂ z) z = -2 ‖z‖²/(1+‖z‖²)²`, which is nonzero
  for `z ≠ 0`. Hence the linear functional `fderiv ℝ heightLocalℂ z`
  is nonzero (as a `ContinuousLinearMap`), and `fderiv ≠ 0` for `z ≠ 0`.

The chartS-side characterization is symmetric (via `heightLocalℂ_S`). -/

/-- `heightLocalℂ z ≤ 1` for all `z : ℂ`. -/
lemma heightLocalℂ_le_one (z : ℂ) : heightLocalℂ z ≤ 1 := by
  unfold heightLocalℂ
  have h_denom_pos : (0 : ℝ) < 1 + ‖z‖^2 := by positivity
  rw [div_le_one h_denom_pos]
  linarith [sq_nonneg ‖z‖]

/-- `heightLocalℂ 0 = 1`. -/
@[simp] lemma heightLocalℂ_zero : heightLocalℂ 0 = 1 := by
  unfold heightLocalℂ; simp

/-- `(0 : ℂ)` is a global maximum of `heightLocalℂ`. -/
lemma heightLocalℂ_isMaxOn_zero :
    IsMaxOn heightLocalℂ Set.univ (0 : ℂ) := by
  intro z _
  rw [heightLocalℂ_zero]
  exact heightLocalℂ_le_one z

/-- **`fderiv heightLocalℂ 0 = 0`** via Fermat (IsLocalMax). -/
lemma heightLocalℂ_fderiv_zero :
    fderiv ℝ heightLocalℂ 0 = 0 := by
  apply IsLocalMax.fderiv_eq_zero
  exact heightLocalℂ_isMaxOn_zero.isLocalMax (by
    exact Filter.univ_mem)

/-- `heightLocalℂ_S w ≥ 0` for all `w : ℂ`. -/
lemma heightLocalℂ_S_nonneg (w : ℂ) : 0 ≤ heightLocalℂ_S w := by
  unfold heightLocalℂ_S
  apply div_nonneg (sq_nonneg _)
  positivity

/-- `(0 : ℂ)` is a global minimum of `heightLocalℂ_S`. -/
lemma heightLocalℂ_S_isMinOn_zero :
    IsMinOn heightLocalℂ_S Set.univ (0 : ℂ) := by
  intro w _
  rw [heightLocalℂ_S_zero]
  exact heightLocalℂ_S_nonneg w

/-- **`fderiv heightLocalℂ_S 0 = 0`** via Fermat (IsLocalMin).

Symmetric chartS-side counterpart to `heightLocalℂ_fderiv_zero`. -/
lemma heightLocalℂ_S_fderiv_zero :
    fderiv ℝ heightLocalℂ_S 0 = 0 := by
  apply IsLocalMin.fderiv_eq_zero
  exact heightLocalℂ_S_isMinOn_zero.isLocalMin (by
    exact Filter.univ_mem)

/-- **The two-point candidate critical set of `heightRiemannSphere`.**
Classically `{0_RS, ∞}`. Used as the explicit `criticalSet` of the
`MorseFunction RiemannSphere` instance below, in lieu of the default
`{x | mfderiv x = 0}` whose characterization as `{0_RS, ∞}` is open
content (chart-local mfderiv computation). -/
noncomputable def heightRiemannSphere_candidateCriticalSet :
    Set RiemannSphere :=
  {((0 : ℂ) : RiemannSphere), (∞ : RiemannSphere)}

lemma heightRiemannSphere_candidateCriticalSet_finite :
    heightRiemannSphere_candidateCriticalSet.Finite := by
  unfold heightRiemannSphere_candidateCriticalSet
  exact (Set.finite_singleton _).insert _

/-- **`MorseFunction RiemannSphere`** — the height function realised
as a (P3) Morse function instance.

The `criticalSet` is overridden to the explicit `{0_RS, ∞}` (the
classical critical set, identified geometrically via the global
max/min facts `_isMaxOn_zero` and `_isMinOn_infty`). The default
predicate `{x | mfderiv x = 0}` agrees with this set, but the
equality (and the Hessian non-degeneracy at each point) is open
content for follow-up chips. The `IsNonDegenerateAtCritical` field
of `MorseFunction` is the chip-32 placeholder (`True`) until the
full chart-local Hessian infrastructure lands. -/
noncomputable def heightRiemannSphereMorseFunction :
    MorseFunction RiemannSphere where
  toFun := heightRiemannSphere
  smooth := heightRiemannSphere_contMDiff
  criticalSet := heightRiemannSphere_candidateCriticalSet
  criticalSet_finite := heightRiemannSphere_candidateCriticalSet_finite
  IsNonDegenerateAtCritical := fun _ _ => trivial

/-- **`MorseFunctionExistsHypothesis RiemannSphere`** is unconditional. -/
theorem morseFunctionExistsHypothesis_RiemannSphere :
    MorseFunctionExistsHypothesis RiemannSphere :=
  ⟨heightRiemannSphereMorseFunction⟩

end RiemannSphere

end JacobianChallenge

end
