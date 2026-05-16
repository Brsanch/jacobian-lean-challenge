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

/-! # Local pairing continuity along `β` for a `SmoothOneForm`

A *local* version of `continuousAt_pairing_smoothOneForm_beta`
(`PairingContinuityBeta.lean`): the hypothesis on `β` is relaxed from
global `ContMDiff 𝓘(ℝ, ℝ) I ∞ β` to a single
`ContMDiffAt 𝓘(ℝ, ℝ) I ∞ β s₀`. This is the form needed when `β` is
*not* a smooth map on all of `ℝ` (e.g. when `β` is the composition
`sheet.g ∘ β'` of a smooth path `β'` with a local sheet inverse
`sheet.g` defined only on an open subset of the target manifold).

The proof is the same chart-coord-pair construction as in
`PairingContinuityBeta.lean`, but the chart-preimage nbhd is obtained
via `ContinuousAt.preimage_mem_nhds` rather than
`IsOpen.preimage Continuous`.

## What ships

* `chartBetaVelocity_contMDiffAt_local` — chart-coord velocity smooth
  at `s₀` from `ContMDiffAt β s₀` alone (local version of chip 9).
* `chartBetaVelocity_continuousAt_local` — continuity corollary.
* `continuousAt_pairing_smoothOneForm_beta_local` — `ContinuousAt s₀`
  of the pairing along `β` for a global `SmoothOneForm I M`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]

namespace JacobianChallenge

variable {I}

/-- **Local `ContMDiffAt` of `chartBetaVelocity` from `ContMDiffAt β s₀`.**

Generalises `contMDiffAt_chartBetaVelocity` (`ChartBetaVelocity.lean`)
to take only a pointwise `ContMDiffAt β s₀` hypothesis. -/
theorem chartBetaVelocity_contMDiffAt_local
    {β : ℝ → M} {s₀ : ℝ}
    (hβ_at : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ β s₀) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (chartBetaVelocity I β s₀) s₀ := by
  have h_inT :
      ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ →L[ℝ] E) ∞
        (inTangentCoordinates 𝓘(ℝ, ℝ) I id β
          (fun s => mfderiv 𝓘(ℝ, ℝ) I β s) s₀) s₀ := by
    have h_top : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by simp
    exact hβ_at.mfderiv_const h_top
  exact h_inT.clm_apply contMDiffAt_const

/-- **Local `ContinuousAt` of `chartBetaVelocity`.** -/
theorem chartBetaVelocity_continuousAt_local
    {β : ℝ → M} {s₀ : ℝ}
    (hβ_at : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ β s₀) :
    ContinuousAt (chartBetaVelocity I β s₀) s₀ :=
  (chartBetaVelocity_contMDiffAt_local hβ_at).continuousAt

/-- **Local pairing continuity along `β` for a `SmoothOneForm`.**

For `β : ℝ → M` with `ContMDiffAt β s₀`, and `om : SmoothOneForm I M`,
the function `s ↦ applyCotangent (om (β s)) (mfderiv β s 1)` is
`ContinuousAt s₀`. Local version of
`continuousAt_pairing_smoothOneForm_beta` (`PairingContinuityBeta.lean`). -/
theorem continuousAt_pairing_smoothOneForm_beta_local
    {β : ℝ → M} {s₀ : ℝ}
    (hβ_at : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ β s₀)
    (om : SmoothOneForm I M) :
    ContinuousAt
      (fun s => SmoothPath.applyCotangent (om (β s))
                  ((mfderiv 𝓘(ℝ, ℝ) I β s) (1 : ℝ))) s₀ := by
  -- Chart-source membership at `β s₀`.
  have h_chart_src : β s₀ ∈ (chartAt H (β s₀)).source :=
    mem_chart_source H (β s₀)
  -- `β` is `ContinuousAt s₀`.
  have h_β_at : ContinuousAt β s₀ := hβ_at.continuousAt
  -- Chart preimage is a nbhd of `s₀` (via `ContinuousAt.preimage_mem_nhds`).
  have h_nhd : β ⁻¹' (chartAt H (β s₀)).source ∈ 𝓝 s₀ :=
    h_β_at.preimage_mem_nhds
      ((chartAt H (β s₀)).open_source.mem_nhds h_chart_src)
  -- Form-side chart-coord smoothness at `x = β s₀` (via section iff).
  have h_form_at_x : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) ⊤
      (fun x => (cotangentBundleCore I M).coordChange
        (achart H x) (achart H (β s₀)) x (om x)) (β s₀) :=
    (cotangentSection_contMDiffAt_iff (I := I) (n := ⊤)
      (fun x => om x)).mp om.contMDiff_toFun.contMDiffAt
  -- Form-side along `β` is continuous at `s₀`.
  have h_form_cont : ContinuousAt
      (fun s => (cotangentBundleCore I M).coordChange
        (achart H (β s)) (achart H (β s₀)) (β s) (om (β s))) s₀ :=
    h_form_at_x.continuousAt.comp h_β_at
  -- Velocity-side at `s₀`.
  have h_vel_cont : ContinuousAt (chartBetaVelocity I β s₀) s₀ :=
    chartBetaVelocity_continuousAt_local hβ_at
  -- Chart-coord pairing is `ContinuousAt s₀` via `clm_apply`.
  have h_pair_cont : ContinuousAt
      (fun s => ((cotangentBundleCore I M).coordChange
        (achart H (β s)) (achart H (β s₀)) (β s) (om (β s)))
          (chartBetaVelocity I β s₀ s)) s₀ :=
    h_form_cont.clm_apply h_vel_cont
  -- Chart-invariance on the chart preimage.
  have h_eq : (β ⁻¹' (chartAt H (β s₀)).source).EqOn
      (fun s => SmoothPath.applyCotangent (om (β s))
                  ((mfderiv 𝓘(ℝ, ℝ) I β s) (1 : ℝ)))
      (fun s => ((cotangentBundleCore I M).coordChange
        (achart H (β s)) (achart H (β s₀)) (β s) (om (β s)))
          (chartBetaVelocity I β s₀ s)) := by
    intro s hs
    exact applyCotangent_eq_chart_pairing_beta (I := I) β s₀ hs (om (β s))
  -- `EqOn` on a nbhd → eventually equal → `ContinuousAt.congr`.
  refine h_pair_cont.congr ?_
  exact (h_eq.eventuallyEq_of_mem h_nhd).symm

end JacobianChallenge

end
