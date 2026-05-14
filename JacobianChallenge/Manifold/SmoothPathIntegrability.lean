/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import JacobianChallenge.Manifold.SmoothPathIntegral
import JacobianChallenge.Manifold.SmoothPathChartCompat
import JacobianChallenge.Manifold.CotangentBundleSmoothness
import JacobianChallenge.Manifold.SmoothCycle

/-! # Interval-integrability of `SmoothPath.integrand` (chip PL-3e)

This file discharges the `intervalIntegrable` witness that
`SmoothPathIntegral.lean` left open.

## Main result

* `SmoothPath.intervalIntegrable_integrand` — for every smooth path
  `γ : SmoothPath I X` and every smooth 1-form `om : SmoothOneForm I X`,
  the integrand `γ.integrand om` is `IntervalIntegrable` on `[0, 1]` with
  respect to Lebesgue measure.

## Strategy

We prove `Continuous (γ.integrand om)` and then apply
`Continuous.intervalIntegrable`. Continuity is proved pointwise: for
each `t₀ : ℝ`, the integrand is `ContinuousAt t₀`.

At `t₀`, choose the canonical chart `c := chartAt H (γ.ambient t₀)`.
On the open preimage `J := γ.ambient ⁻¹ c.source`, the integrand can be
factored as a `clm_apply` of two continuous factors:

* **Velocity side.** `inTangentCoordinates 𝓘(ℝ, ℝ) I id γ.ambient
  (mfderiv …) t₀` is the *chart-coord representative of the velocity-
  valued mfderiv*. Mathlib's `ContMDiffAt.mfderiv_const` says this is
  `ContMDiff ⊤` near `t₀`; applied to the constant section `(1 : ℝ)`,
  it gives a continuous `E`-valued function of `t` near `t₀`.

* **Form side.** `om` is a `ContMDiffSection` of the cotangent bundle;
  via `cotangentSection_contMDiffAt_iff`, its `c`-chart-coord
  representative is `ContMDiff ⊤` at `γ.ambient t₀`, hence continuous.
  Pre-composing with the continuous path `γ.ambient` gives continuity
  of the chart-coord form along the path.

* **Chart invariance of the pairing.** On `J` the intrinsic pairing
  `(om(γ.ambient t))(γ.velocity t)` agrees with the chart-coord pairing
  `(chart-coord rep of om) · (chart-coord rep of velocity)`. This is
  because the cotangent and tangent chart-coord changes are mutually
  inverse (one is the transpose of the other) and cancel under the
  pairing — applied at the `γ.ambient t` chart-source overlap with the
  fixed `γ.ambient t₀` chart, the tangent cocycle
  `coordChange_comp` discharges the cancellation.

* **`clm_apply` finishes.** Applying `Continuous.clm_apply` to the
  chart-coord form and chart-coord velocity gives continuity of the
  pairing, and by chart invariance, of the integrand on `J`.

Pointwise `ContinuousAt` is enough for global `Continuous` — no
finite-cover argument needed.

## Downstream

* `SmoothPath.integrate_add_unconditional` — drops the integrability
  hypotheses from `integrate_add`.
* This in turn unblocks `complexPeriod` additivity in the form argument
  (`Manifold/ComplexPeriodPairing.lean`), the deferred PL-2 obligation.
-/

open scoped Manifold Topology Bundle ContDiff
open MeasureTheory intervalIntegral Bundle

noncomputable section

set_option diagnostics.threshold 100

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace SmoothPath

/-- The chosen ambient extension of a smooth path is continuous on `ℝ`. -/
lemma continuous_ambient (γ : SmoothPath I X) : Continuous γ.ambient :=
  γ.ambient_contMDiff.continuous

/-! ## Velocity side: chart-coord velocity is continuous near a base point -/

variable (I) in
/-- The chart-coord velocity of `γ.ambient` near base parameter `t₀`,
expressed in the chart at `γ.ambient t₀` (and the trivial chart on `ℝ`
for the source). Equals
`(tangentBundleCore I X).coordChange (achart H (γ.ambient t)) (achart H (γ.ambient t₀)) (γ.ambient t) (γ.velocity t)`
on the chart-source overlap. -/
def chartVelocity (γ : SmoothPath I X) (t₀ : ℝ) (t : ℝ) : E :=
  (inTangentCoordinates 𝓘(ℝ, ℝ) I id γ.ambient
      (fun s => mfderiv 𝓘(ℝ, ℝ) I γ.ambient s) t₀ t) (1 : ℝ)

lemma contMDiffAt_chartVelocity (γ : SmoothPath I X) (t₀ : ℝ) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (γ.chartVelocity I t₀) t₀ := by
  have h_inT :
      ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ →L[ℝ] E) ∞
        (inTangentCoordinates 𝓘(ℝ, ℝ) I id γ.ambient
          (fun s => mfderiv 𝓘(ℝ, ℝ) I γ.ambient s) t₀) t₀ := by
    have h_amb : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ.ambient t₀ := γ.ambient_contMDiff t₀
    -- `∞ + 1 = ∞` in `WithTop ℕ∞` (top is absorptive in `ℕ∞`).
    have h_top : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by simp
    exact h_amb.mfderiv_const h_top
  exact h_inT.clm_apply contMDiffAt_const

lemma continuous_chartVelocity_at (γ : SmoothPath I X) (t₀ : ℝ) :
    ContinuousAt (γ.chartVelocity I t₀) t₀ :=
  (γ.contMDiffAt_chartVelocity t₀).continuousAt

/-! ## Form side: chart-coord section is continuous near a base point -/

variable (I) in
/-- The chart-coord representative of `om` along the path, relative to
the chart anchored at `γ.ambient t₀`. -/
def chartForm (γ : SmoothPath I X) (om : SmoothOneForm I X) (t₀ : ℝ) (t : ℝ) :
    E →L[ℝ] ℝ :=
  (cotangentBundleCore I X).coordChange
    (achart H (γ.ambient t)) (achart H (γ.ambient t₀)) (γ.ambient t)
    (om (γ.ambient t))

lemma contMDiffAt_chartForm_at_x (γ : SmoothPath I X) (om : SmoothOneForm I X)
    (t₀ : ℝ) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) ⊤
      (fun x => (cotangentBundleCore I X).coordChange
        (achart H x) (achart H (γ.ambient t₀)) x (om x))
      (γ.ambient t₀) :=
  (cotangentSection_contMDiffAt_iff (I := I) (n := ⊤)
    (fun x => om x)).mp om.contMDiff_toFun.contMDiffAt

lemma continuous_chartForm_at (γ : SmoothPath I X) (om : SmoothOneForm I X)
    (t₀ : ℝ) :
    ContinuousAt (γ.chartForm I om t₀) t₀ := by
  have h_at_x : ContinuousAt
      (fun x => (cotangentBundleCore I X).coordChange
        (achart H x) (achart H (γ.ambient t₀)) x (om x))
      (γ.ambient t₀) :=
    (γ.contMDiffAt_chartForm_at_x om t₀).continuousAt
  have h_amb : ContinuousAt γ.ambient t₀ := γ.continuous_ambient.continuousAt
  exact h_at_x.comp h_amb

/-! ## Chart invariance of the pairing -/

/-- **Chart invariance of the cotangent–tangent pairing.** On the
chart-source overlap of the chart at `γ.ambient t₀` with the chart at
`γ.ambient t`, the intrinsic pairing `(om(γ.ambient t))(γ.velocity t)`
equals the chart-coord pairing `(chartForm)(chartVelocity)`. The
cancellation is the tangent-bundle cocycle:
`coordChange (achart x_t₀) (achart x_t) x_t ∘ coordChange (achart x_t) (achart x_t₀) x_t = id`. -/
lemma integrand_eq_chart_pairing (γ : SmoothPath I X) (om : SmoothOneForm I X)
    (t₀ : ℝ) {t : ℝ}
    (ht : γ.ambient t ∈ (chartAt H (γ.ambient t₀)).source) :
    γ.integrand om t = (γ.chartForm I om t₀ t) (γ.chartVelocity I t₀ t) := by
  -- Set up abbreviations.
  set x_t : X := γ.ambient t
  set x_t₀ : X := γ.ambient t₀
  set i : atlas H X := achart H x_t
  set j : atlas H X := achart H x_t₀
  -- Chart-source memberships used by the cocycle.
  have hi : x_t ∈ i.1.source := mem_chart_source H x_t
  have hj : x_t ∈ j.1.source := ht
  -- Unfold `chartVelocity` using `inTangentCoordinates_eq`.
  have h_chart_src : id t ∈ (chartAt ℝ ((id : ℝ → ℝ) t₀)).source := by
    change t ∈ (chartAt ℝ t₀).source
    simp [chartAt]
  have h_eq_inT :
      inTangentCoordinates 𝓘(ℝ, ℝ) I id γ.ambient
          (fun s => mfderiv 𝓘(ℝ, ℝ) I γ.ambient s) t₀ t
        = (tangentBundleCore I X).coordChange i j x_t ∘L
          (mfderiv 𝓘(ℝ, ℝ) I γ.ambient t) ∘L
          (tangentBundleCore 𝓘(ℝ, ℝ) ℝ).coordChange (achart ℝ t₀) (achart ℝ t) t :=
    inTangentCoordinates_eq (I := 𝓘(ℝ, ℝ)) (I' := I)
      (f := id) (g := γ.ambient)
      (ϕ := fun s => mfderiv 𝓘(ℝ, ℝ) I γ.ambient s) h_chart_src ht
  -- The source-side coordinate change is the identity (model space).
  have h_src_id :
      (tangentBundleCore 𝓘(ℝ, ℝ) ℝ).coordChange (achart ℝ t₀) (achart ℝ t) t
        = ContinuousLinearMap.id ℝ ℝ :=
    tangentBundleCore_coordChange_model_space (I := 𝓘(ℝ, ℝ)) t₀ t t
  -- Apply at `(1 : ℝ)`: chartVelocity = T_velo (γ.velocity t).
  have h_chartVel :
      γ.chartVelocity I t₀ t
        = (tangentBundleCore I X).coordChange i j x_t (γ.velocity t) := by
    unfold chartVelocity
    rw [h_eq_inT, h_src_id]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    rfl
  -- Unfold `chartForm` using `cotangentBundleCore_coordChange_apply`.
  have h_chartForm :
      γ.chartForm I om t₀ t
        = (om x_t).comp ((tangentBundleCore I X).coordChange j i x_t) := by
    unfold chartForm
    exact cotangentBundleCore_coordChange_apply (I := I) i j x_t (om x_t)
  -- Cocycle cancellation: T_form ∘ T_velo = id (applied to γ.velocity t).
  have h_cocycle :
      (tangentBundleCore I X).coordChange j i x_t
        ((tangentBundleCore I X).coordChange i j x_t (γ.velocity t))
        = γ.velocity t := by
    have h_mem : x_t ∈ (tangentBundleCore I X).baseSet i ∩
        (tangentBundleCore I X).baseSet j ∩ (tangentBundleCore I X).baseSet i :=
      ⟨⟨hi, hj⟩, hi⟩
    have := (tangentBundleCore I X).coordChange_comp i j i x_t h_mem (γ.velocity t)
    -- `coordChange j i x_t (coordChange i j x_t v) = coordChange i i x_t v = v`.
    rw [this]
    exact (tangentBundleCore I X).coordChange_self i x_t hi (γ.velocity t)
  -- Assemble: (chartForm)(chartVelocity) = (om x_t).comp(T_form) (T_velo v)
  --                                      = (om x_t) (T_form (T_velo v))
  --                                      = (om x_t) (γ.velocity t)
  --                                      = γ.integrand om t.
  rw [h_chartForm, h_chartVel, ContinuousLinearMap.comp_apply, h_cocycle]
  -- Goal: (om x_t) (γ.velocity t) = γ.integrand om t.
  unfold integrand applyCotangent
  rfl

/-! ## Continuity of the integrand at a single parameter -/

lemma continuous_integrand_at (γ : SmoothPath I X) (om : SmoothOneForm I X)
    (t₀ : ℝ) :
    ContinuousAt (γ.integrand om) t₀ := by
  have h_chart_src : γ.ambient t₀ ∈ (chartAt H (γ.ambient t₀)).source :=
    mem_chart_source H (γ.ambient t₀)
  have h_open : IsOpen (γ.ambient ⁻¹' (chartAt H (γ.ambient t₀)).source) :=
    (chartAt H (γ.ambient t₀)).open_source.preimage γ.continuous_ambient
  have h_t₀_mem : t₀ ∈ γ.ambient ⁻¹' (chartAt H (γ.ambient t₀)).source := h_chart_src
  have h_eq : (γ.ambient ⁻¹' (chartAt H (γ.ambient t₀)).source).EqOn
      (γ.integrand om)
      (fun t => (γ.chartForm I om t₀ t) (γ.chartVelocity I t₀ t)) := by
    intro t ht
    exact γ.integrand_eq_chart_pairing om t₀ ht
  have h_pair :
      ContinuousAt (fun t => (γ.chartForm I om t₀ t) (γ.chartVelocity I t₀ t)) t₀ :=
    (γ.continuous_chartForm_at om t₀).clm_apply (γ.continuous_chartVelocity_at t₀)
  -- `EqOn` on an open nhd ⇒ `=ᶠ`; `ContinuousAt.congr` consumes the
  -- right-to-left direction.
  refine h_pair.congr ?_
  refine (h_eq.eventuallyEq_of_mem (h_open.mem_nhds h_t₀_mem)).symm
  -- (Now both sides match the expected `=ᶠ`.)

/-! ## Global continuity and interval-integrability -/

/-- The integrand `γ.integrand om : ℝ → ℝ` is continuous on `ℝ`. -/
theorem continuous_integrand (γ : SmoothPath I X) (om : SmoothOneForm I X) :
    Continuous (γ.integrand om) :=
  continuous_iff_continuousAt.mpr (γ.continuous_integrand_at om)

/-- **PL-3e — interval integrability.** The integrand of a smooth-path
integral is interval-integrable on `[0, 1]` with respect to Lebesgue
measure. -/
theorem intervalIntegrable_integrand (γ : SmoothPath I X) (om : SmoothOneForm I X) :
    IntervalIntegrable (γ.integrand om) MeasureTheory.volume 0 1 :=
  (continuous_integrand γ om).intervalIntegrable 0 1

/-! ## Unconditional additivity of the path integral -/

/-- Linearity of the path integral in the 1-form: addition, without
integrability hypotheses. Specialisation of `integrate_add` using
`intervalIntegrable_integrand`. -/
theorem integrate_add_unconditional (γ : SmoothPath I X)
    (om₁ om₂ : SmoothOneForm I X) :
    γ.integrate (om₁ + om₂) = γ.integrate om₁ + γ.integrate om₂ :=
  γ.integrate_add om₁ om₂ (γ.intervalIntegrable_integrand om₁)
    (γ.intervalIntegrable_integrand om₂)

end SmoothPath

/-! ## Form-side additivity for chains and cycles -/

namespace SmoothChain

/-- **Form-side additivity for chain integrals.** `integrate c (om₁ + om₂)
= integrate c om₁ + integrate c om₂`. The proof distributes the chain's
`Finsupp` support sum and applies `SmoothPath.integrate_add_unconditional`
on each summand. -/
theorem integrate_add_form (c : SmoothChain I X) (om₁ om₂ : SmoothOneForm I X) :
    integrate c (om₁ + om₂) = integrate c om₁ + integrate c om₂ := by
  unfold integrate
  classical
  -- Pointwise: ((c γ : ℝ) * γ.integrate (om₁ + om₂))
  --          = (c γ : ℝ) * γ.integrate om₁ + (c γ : ℝ) * γ.integrate om₂.
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro γ _
  rw [γ.integrate_add_unconditional om₁ om₂, mul_add]

end SmoothChain

namespace JacobianChallenge

namespace SmoothCycle

/-- **Form-side additivity for cycle integrals.** Inherits from
`SmoothChain.integrate_add_form`. -/
theorem integrate_add_form (c : SmoothCycle I X) (om₁ om₂ : SmoothOneForm I X) :
    integrate c (om₁ + om₂) = integrate c om₁ + integrate c om₂ := by
  unfold integrate
  exact SmoothChain.integrate_add_form (c : SmoothChain I X) om₁ om₂

end SmoothCycle

end JacobianChallenge

end
