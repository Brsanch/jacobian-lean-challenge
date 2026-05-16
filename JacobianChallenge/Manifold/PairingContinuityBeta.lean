/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartBetaVelocity
import JacobianChallenge.Manifold.ChartBetaPairingInvariance
import JacobianChallenge.Manifold.CotangentBundleSmoothness
import JacobianChallenge.Manifold.SmoothOneForm
import JacobianChallenge.Manifold.SmoothPathIntegral

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Pairing continuity along `β` for a `SmoothOneForm`

For a smooth map `β : ℝ → M` and a `SmoothOneForm I M` `om`, the
function

  `s ↦ applyCotangent (om (β s)) (mfderiv β s 1)`

is `ContinuousAt s₀` for every `s₀ : ℝ`.

This is the β-analogue of `SmoothPath.continuous_integrand_at`,
assembled from:

* `applyCotangent_eq_chart_pairing_beta` (chart-coord pairing identity
  on the chart preimage of `β s₀`).
* `continuousAt_chartBetaVelocity` (velocity-side at the anchor).
* `cotangentSection_contMDiffAt_iff` + `Continuous β`
  (form-side smoothness at the anchor, factored through `β`).
* `ContinuousAt.clm_apply` (pairing continuity).

When `fStarOmega` is upgraded to a `SmoothOneForm` post-`f-5`, this
lemma directly discharges `IntegrandContinuousAlongBeta` for the
trace-pairing along `β`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]

namespace JacobianChallenge

variable {I}

/-- **Pairing continuity along `β` for a `SmoothOneForm`.**

The function `s ↦ applyCotangent (om (β s)) (mfderiv β s 1)` is
`ContinuousAt s₀`. Mirrors `SmoothPath.continuous_integrand_at`. -/
theorem continuousAt_pairing_smoothOneForm_beta
    {β : ℝ → M} (hβ : ContMDiff 𝓘(ℝ, ℝ) I ∞ β)
    (om : SmoothOneForm I M) (s₀ : ℝ) :
    ContinuousAt
      (fun s => SmoothPath.applyCotangent (om (β s))
                  ((mfderiv 𝓘(ℝ, ℝ) I β s) (1 : ℝ))) s₀ := by
  -- Chart preimage (open nbhd of `s₀`).
  have h_chart_src : β s₀ ∈ (chartAt H (β s₀)).source :=
    mem_chart_source H (β s₀)
  have h_β_cont : Continuous β := hβ.continuous
  have h_open : IsOpen (β ⁻¹' (chartAt H (β s₀)).source) :=
    (chartAt H (β s₀)).open_source.preimage h_β_cont
  have h_s₀_mem : s₀ ∈ β ⁻¹' (chartAt H (β s₀)).source := h_chart_src
  -- Form-side chart-coord smoothness at `x = β s₀` (via section iff).
  have h_form_at_x : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) ⊤
      (fun x => (cotangentBundleCore I M).coordChange
        (achart H x) (achart H (β s₀)) x (om x)) (β s₀) :=
    (cotangentSection_contMDiffAt_iff (I := I) (n := ⊤)
      (fun x => om x)).mp om.contMDiff_toFun.contMDiffAt
  -- Pull back along `β`: form-side along `β` is continuous at `s₀`.
  have h_form_cont : ContinuousAt
      (fun s => (cotangentBundleCore I M).coordChange
        (achart H (β s)) (achart H (β s₀)) (β s) (om (β s))) s₀ :=
    h_form_at_x.continuousAt.comp h_β_cont.continuousAt
  -- Velocity-side at `s₀` (chip 9).
  have h_vel_cont : ContinuousAt (chartBetaVelocity I β s₀) s₀ :=
    continuousAt_chartBetaVelocity hβ s₀
  -- Chart-coord pairing is continuous at `s₀` via `clm_apply`.
  have h_pair_cont : ContinuousAt
      (fun s => ((cotangentBundleCore I M).coordChange
        (achart H (β s)) (achart H (β s₀)) (β s) (om (β s)))
          (chartBetaVelocity I β s₀ s)) s₀ :=
    h_form_cont.clm_apply h_vel_cont
  -- `EqOn` on the chart preimage (chip 12).
  have h_eq : (β ⁻¹' (chartAt H (β s₀)).source).EqOn
      (fun s => SmoothPath.applyCotangent (om (β s))
                  ((mfderiv 𝓘(ℝ, ℝ) I β s) (1 : ℝ)))
      (fun s => ((cotangentBundleCore I M).coordChange
        (achart H (β s)) (achart H (β s₀)) (β s) (om (β s)))
          (chartBetaVelocity I β s₀ s)) := by
    intro s hs
    exact applyCotangent_eq_chart_pairing_beta (I := I) β s₀ hs (om (β s))
  -- Conclude: `EqOn` on an open nbhd ⇒ eventually equal ⇒ `congr`.
  refine h_pair_cont.congr ?_
  exact (h_eq.eventuallyEq_of_mem (h_open.mem_nhds h_s₀_mem)).symm

/-- **Continuity (global, in `s`) of the pairing along `β` for a
`SmoothOneForm`.** Corollary of `continuousAt_pairing_smoothOneForm_beta`. -/
theorem continuous_pairing_smoothOneForm_beta
    {β : ℝ → M} (hβ : ContMDiff 𝓘(ℝ, ℝ) I ∞ β)
    (om : SmoothOneForm I M) :
    Continuous
      (fun s => SmoothPath.applyCotangent (om (β s))
                  ((mfderiv 𝓘(ℝ, ℝ) I β s) (1 : ℝ))) :=
  continuous_iff_continuousAt.mpr
    (continuousAt_pairing_smoothOneForm_beta hβ om)

end JacobianChallenge

end
