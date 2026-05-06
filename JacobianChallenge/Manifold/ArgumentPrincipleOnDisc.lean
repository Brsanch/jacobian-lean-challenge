/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.MeasureTheory.Integral.CircleIntegral
import JacobianChallenge.Manifold.PlanarAnnulusCircleIntegral

/-! # Argument principle on a planar disc (ZZ59)

This file works toward the headline planar argument principle:

  *If `f : ℂ → ℂ` is holomorphic on the closed disc `closedBall c R`
  except for finitely many isolated zeros / poles inside `ball c R`,
  with `f` non-vanishing on the boundary circle `sphere c R`, then*

      `∮_{|z-c|=R} f'(z) / f(z) dz = 2πi · ∑_{x ∈ S} ord_x(f)`

  *where `ord_x(f)` is the meromorphic order at `x`.*

## What is proved here

* `argumentPrincipleOnDisc_empty_diffOnNhd` — the **`S = ∅`** instance,
  unconditionally proved at the current mathlib pin
  (`8e3c989104daaa052921bf43de9eef0e1ac9fbf5`, 15 April 2026):
  if `f` is holomorphic on an *open* neighbourhood of the closed disc
  and non-vanishing there, then `∮_{|z-c|=R} f'/f = 0`.

  The hypothesis is `DifferentiableOn ℂ f U` with `closedBall c R ⊆ U`
  and `U` open, rather than `DifferentiableOn ℂ f (closedBall c R)`.
  This strengthening is needed to extract continuity of `deriv f` on
  the closed disc, which is required by
  `DiffContOnCl.circleIntegral_eq_zero` and is **not** a consequence of
  `DifferentiableOn` on a closed set at this mathlib pin.

## What is *not* proved here

The headline multi-point theorem is **not** discharged at this pin.
The general case requires a *multi-hole* Cauchy deformation lemma:

  `circleIntegral_eq_sum_of_holomorphic_on_punctured_disc`:
  given disjoint discs `ball x_i ε_i ⊆ ball c R` and `g` holomorphic on
  `closedBall c R \ ⋃ ball x_i ε_i`, the boundary circle integral over
  `sphere c R` equals the sum of boundary circle integrals over each
  `sphere x_i ε_i`.

Mathlib at this pin provides only the *single*-hole annulus deformation
(`Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`
and the wrapper `JacobianChallenge.PlanarAnnulus.circleIntegral_eq_of_holomorphic_on_annulus`).
The multi-hole generalisation has to be proved (e.g. by induction on
`|S|` plus a planar-domain Stokes argument) before the headline
theorem can be discharged.

## Anti-cheat

* No `sorry`, no `axiom`.
* No existing definition or signature is changed.
* The only result exported -- `argumentPrincipleOnDisc_empty_diffOnNhd`
  -- is proved end-to-end against mathlib at the pin.
-/

noncomputable section

open Complex MeasureTheory Set Metric Filter Topology

namespace JacobianChallenge

namespace ArgumentPrinciple

/-- **Argument principle, empty-zero-set case (open-neighbourhood form).**

If `f : ℂ → ℂ` is holomorphic on an open set `U` containing the closed
disc `closedBall c R`, and `f` is non-vanishing on the closed disc,
then the boundary circle integral of `f'/f` is zero:

    `∮_{|z-c|=R} f'(z) / f(z) dz = 0`.

This is the `S = ∅` instance of the planar argument principle: the
right-hand sum `2πi · ∑_{x ∈ ∅} ord_x f` is the empty sum, which is
zero, so the equality with the integral becomes the vanishing
statement above. -/
theorem argumentPrincipleOnDisc_empty_diffOnNhd
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R) {f : ℂ → ℂ} {U : Set ℂ}
    (hUopen : IsOpen U) (hUsub : closedBall c R ⊆ U)
    (hf : DifferentiableOn ℂ f U)
    (hne : ∀ z ∈ closedBall c R, f z ≠ 0) :
    (∮ z in C(c, R), deriv f z / f z) = 0 := by
  -- `f` is analytic on the open neighbourhood `U`.
  have hf_an : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hUopen
  -- Hence `deriv f` is analytic on `U`, and in particular differentiable on `U`.
  have hderiv_diff : DifferentiableOn ℂ (deriv f) U :=
    (fun z hz => ((hf_an z hz).deriv).differentiableAt.differentiableWithinAt)
  -- `f` is continuous on `U`.
  have hf_cont : ContinuousOn f U := hf.continuousOn
  -- Build `V := U ∩ f⁻¹' {0}ᶜ`, an open subset of `U` containing the closed disc.
  set V : Set ℂ := U ∩ f ⁻¹' ({0}ᶜ) with hV_def
  have hVopen : IsOpen V :=
    hf_cont.isOpen_inter_preimage hUopen isOpen_compl_singleton
  have hVsubU : V ⊆ U := Set.inter_subset_left
  have hVsub : closedBall c R ⊆ V := by
    intro z hz
    refine ⟨hUsub hz, ?_⟩
    simp [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact hne z hz
  -- On `V`, `deriv f / f` is differentiable (numerator analytic, denominator non-zero).
  have hquot_diff_V : DifferentiableOn ℂ (fun z => deriv f z / f z) V := by
    intro z hz
    have hzU : z ∈ U := hz.1
    have hzfne : f z ≠ 0 := by
      have : z ∈ f ⁻¹' ({0}ᶜ) := hz.2
      simpa [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] using this
    have hd : DifferentiableWithinAt ℂ (fun w => deriv f w / f w) U z :=
      (hderiv_diff z hzU).div (hf z hzU) hzfne
    exact hd.mono hVsubU
  -- Restrict to the open ball.
  have hball_subset_closed : ball c R ⊆ closedBall c R := Metric.ball_subset_closedBall
  have hquot_diff_open : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball c R) :=
    hquot_diff_V.mono (fun z hz => hVsub (hball_subset_closed hz))
  -- Continuity on the closed ball.
  have hquot_cont_closed : ContinuousOn (fun z => deriv f z / f z) (closedBall c R) :=
    (hquot_diff_V.continuousOn).mono hVsub
  -- Continuity on `closure (ball c R)`. For `R > 0`,
  -- `closure (ball c R) = closedBall c R`. For `R = 0`,
  -- `ball c 0 = ∅`, so `closure (ball c 0) = ∅`, and the goal is
  -- vacuously true.
  have hquot_cont_clos : ContinuousOn (fun z => deriv f z / f z) (closure (ball c R)) := by
    refine hquot_cont_closed.mono ?_
    -- `closure (ball c R) ⊆ closedBall c R` always.
    exact Metric.closure_ball_subset_closedBall
  have hquot_dcoc : DiffContOnCl ℂ (fun z => deriv f z / f z) (ball c R) :=
    ⟨hquot_diff_open, hquot_cont_clos⟩
  exact hquot_dcoc.circleIntegral_eq_zero hR

end ArgumentPrinciple

end JacobianChallenge

end
