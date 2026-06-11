/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PartialZBarAnalyticConverse
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

set_option linter.unusedSectionVars false

/-! # Weyl's lemma for `∂̄` on ℂ (Arc 1, chip 1)

**Weyl regularity for the Cauchy–Riemann operator**: a continuous
function `h` on an open `U ⊆ ℂ` that is *weakly* `∂̄`-closed — i.e.

  `∫ h · ∂̄φ = 0` for every smooth compactly-supported test function
  `φ` with support in `U`

— is holomorphic on `U`.

This is the regularity engine of the L²-Hodge-lite route to
`DBarSolvabilityAtGenusZero X` (see `HANDOFF_ITEM14.md`, ACTIVE ARC
2026-06-10): the orthogonal complement of `im ∂̄` consists of weak
solutions, and this lemma upgrades them to honest holomorphic objects.

## Proof

Mollification. Fix `z₀ ∈ U` and `r` with `closedBall z₀ (2r) ⊆ U`, and
let `h̃` be `h` cut off to that closed ball (so it is integrable). For
a bump `ρ` with outer radius `≤ r` the convolution `u = ρ ⋆ h̃` is
smooth, and for `z ∈ ball z₀ r`:

  `∂̄u(z) = ∫ q(t)·h̃(z−t) dt = ∫ q(z−y)·h̃(y) dy = −∫ h(y)·∂̄φ_z(y) dy = 0`,

where `q := ∂̄ρ` and `φ_z(y) := ρ(z−y)` is an admissible test function
(its support `closedBall z ρ.rOut` stays inside `U`, and `h̃ = h`
there). Smooth + `∂̄ = 0` is honestly holomorphic by the in-tree
Cauchy–Riemann converse
(`differentiableAt_complex_of_differentiableAt_real_of_partialZBar_zero`).
Finally `u → h` uniformly on `ball z₀ r` as the bump radius shrinks
(`ContDiffBump.dist_normed_convolution_le` + uniform continuity of `h`
on the compact ball), so `h` is a locally uniform limit of holomorphic
functions, hence holomorphic (`TendstoLocallyUniformlyOn.differentiableOn`).

## What this file ships

* `WeaklyDBarZeroOn h U` — the weak `∂̄`-closedness predicate.
* `differentiableOn_of_weaklyDBarZeroOn` — **Weyl's lemma**:
  continuous + weakly `∂̄`-closed on open `U` ⟹ `DifferentiableOn ℂ h U`.
* `analyticOnNhd_of_weaklyDBarZeroOn` — the analytic form.

No `sorry`, no `axiom`. -/

noncomputable section

open MeasureTheory Metric Filter Function
open scoped Convolution Topology ContDiff

namespace JacobianChallenge

namespace WeylDBar

/-- **Weak `∂̄`-closedness on `U`**: the defining integrals against
`∂̄` of admissible test functions all vanish. -/
def WeaklyDBarZeroOn (h : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∫ z, h z * partialZBar φ z ∂volume = 0

/-- The `∂̄` of a normed bump, as an explicit ℂ-valued function:
`q(t) = ½(∂₁ρ(t) + i·∂ᵢρ(t))`. -/
def qDeriv (ρ : ContDiffBump (0 : ℂ)) (t : ℂ) : ℂ :=
  (2 : ℂ)⁻¹ * (((fderiv ℝ (ρ.normed volume) t 1 : ℝ) : ℂ)
    + Complex.I * ((fderiv ℝ (ρ.normed volume) t Complex.I : ℝ) : ℂ))

/-- `qDeriv` vanishes outside `closedBall 0 ρ.rOut`. -/
lemma qDeriv_eq_zero_of_notMem (ρ : ContDiffBump (0 : ℂ)) {t : ℂ}
    (ht : t ∉ Metric.closedBall (0 : ℂ) ρ.rOut) : qDeriv ρ t = 0 := by
  have hzero : ρ.normed volume =ᶠ[𝓝 t] 0 := by
    have hopen : IsOpen (Metric.closedBall (0 : ℂ) ρ.rOut)ᶜ :=
      Metric.isClosed_closedBall.isOpen_compl
    filter_upwards [hopen.mem_nhds ht] with s hs
    have hns : s ∉ tsupport (ρ.normed volume) := by
      rw [ρ.tsupport_normed_eq]
      exact hs
    exact image_eq_zero_of_notMem_tsupport hns
  have hfd : fderiv ℝ (ρ.normed volume) t = fderiv ℝ (0 : ℂ → ℝ) t :=
    hzero.fderiv_eq
  simp [qDeriv, hfd]

/-- `∂̄` of the shifted bump test function `y ↦ ρ(z − y)` (coerced to
ℂ) equals `−q(z − y)`. -/
lemma partialZBar_shifted_bump (ρ : ContDiffBump (0 : ℂ)) (z y : ℂ) :
    partialZBar (fun w => ((ρ.normed volume (z - w) : ℝ) : ℂ)) y
      = -(qDeriv ρ (z - y)) := by
  have hg : DifferentiableAt ℝ (ρ.normed volume) (z - y) :=
    ((ρ.contDiff_normed (n := 1)).differentiable one_ne_zero).differentiableAt
  have hinner : HasFDerivAt (fun w : ℂ => z - w)
      (-(ContinuousLinearMap.id ℝ ℂ)) y := by
    simpa using (hasFDerivAt_id y).const_sub z
  have hcomp : HasFDerivAt (fun w : ℂ => ρ.normed volume (z - w))
      ((fderiv ℝ (ρ.normed volume) (z - y)).comp
        (-(ContinuousLinearMap.id ℝ ℂ))) y :=
    hg.hasFDerivAt.comp y hinner
  have hfull : HasFDerivAt (fun w : ℂ => ((ρ.normed volume (z - w) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp
        ((fderiv ℝ (ρ.normed volume) (z - y)).comp
          (-(ContinuousLinearMap.id ℝ ℂ)))) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y hcomp
  rw [partialZBar, hfull.fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_id', id_eq,
    map_neg, Complex.ofRealCLM_apply, qDeriv]
  ring

section Convolution

variable {g : ℂ → ℂ}

/-- `∂̄` of the convolution `ρ ⋆ g` at `z` equals
`∫ q(t)·g(z − t) dt`. -/
lemma partialZBar_convolution_left (ρ : ContDiffBump (0 : ℂ))
    (hg : Integrable g volume) (z : ℂ) :
    partialZBar ((ρ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) z
      = ∫ t, qDeriv ρ t * g (z - t) ∂volume := by
  have hcf : HasCompactSupport (ρ.normed volume) := ρ.hasCompactSupport_normed
  have hf1 : ContDiff ℝ 1 (ρ.normed volume) := ρ.contDiff_normed
  have hgl : LocallyIntegrable g volume := hg.locallyIntegrable
  -- derivative of the convolution
  have hD := hcf.hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) hf1 hgl z
  -- existence of the derivative-side convolution integrand
  have hf' : Continuous (fderiv ℝ (ρ.normed volume)) := by
    have h2 : ContDiff ℝ 1 (ρ.normed volume) := ρ.contDiff_normed
    exact (contDiff_one_iff_fderiv.mp h2).2
  have hcf' : HasCompactSupport (fderiv ℝ (ρ.normed volume)) :=
    hcf.fderiv (𝕜 := ℝ)
  have hex : ConvolutionExistsAt (fderiv ℝ (ρ.normed volume)) g z
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL ℂ) volume :=
    hcf'.convolutionExists_left _ hf' hgl z
  -- evaluate the operator-valued convolution on a vector
  have happ : ∀ w : ℂ,
      ((fderiv ℝ (ρ.normed volume)
          ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL ℂ, volume] g) z) w
        = ∫ t, ((fderiv ℝ (ρ.normed volume) t w : ℝ) : ℂ) * g (z - t)
            ∂volume := by
    intro w
    rw [convolution_def, ContinuousLinearMap.integral_apply hex]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.precompL_apply,
      ContinuousLinearMap.lsmul_apply]
    exact Complex.real_smul
  -- component integrability
  have hcomp : ∀ w : ℂ,
      Integrable
        (fun t => ((fderiv ℝ (ρ.normed volume) t w : ℝ) : ℂ) * g (z - t))
        volume := by
    intro w
    have h0 := Integrable.apply_continuousLinearMap hex w
    have heqfun : (fun t => ((ContinuousLinearMap.precompL ℂ
          (ContinuousLinearMap.lsmul ℝ ℝ))
            (fderiv ℝ (ρ.normed volume) t) (g (z - t))) w)
        = fun t => ((fderiv ℝ (ρ.normed volume) t w : ℝ) : ℂ) * g (z - t) := by
      funext t
      simp only [ContinuousLinearMap.precompL_apply,
        ContinuousLinearMap.lsmul_apply]
      exact Complex.real_smul
    rwa [heqfun] at h0
  -- assemble
  rw [partialZBar, hD.fderiv, happ 1, happ Complex.I]
  have hpull : Complex.I * ∫ t,
        ((fderiv ℝ (ρ.normed volume) t Complex.I : ℝ) : ℂ) * g (z - t) ∂volume
      = ∫ t, Complex.I *
        (((fderiv ℝ (ρ.normed volume) t Complex.I : ℝ) : ℂ) * g (z - t))
          ∂volume :=
    (integral_const_mul _ _).symm
  rw [hpull]
  have hadd : (∫ t, ((fderiv ℝ (ρ.normed volume) t 1 : ℝ) : ℂ) * g (z - t)
            ∂volume)
        + ∫ t, Complex.I *
            (((fderiv ℝ (ρ.normed volume) t Complex.I : ℝ) : ℂ) * g (z - t))
              ∂volume
      = ∫ t, (((fderiv ℝ (ρ.normed volume) t 1 : ℝ) : ℂ) * g (z - t)
          + Complex.I *
            (((fderiv ℝ (ρ.normed volume) t Complex.I : ℝ) : ℂ) * g (z - t)))
              ∂volume :=
    (integral_add (hcomp 1) ((hcomp Complex.I).const_mul Complex.I)).symm
  rw [hadd]
  have hhalf : (2 : ℂ)⁻¹
        * ∫ t, (((fderiv ℝ (ρ.normed volume) t 1 : ℝ) : ℂ) * g (z - t)
          + Complex.I *
            (((fderiv ℝ (ρ.normed volume) t Complex.I : ℝ) : ℂ) * g (z - t)))
              ∂volume
      = ∫ t, (2 : ℂ)⁻¹
          * (((fderiv ℝ (ρ.normed volume) t 1 : ℝ) : ℂ) * g (z - t)
          + Complex.I *
            (((fderiv ℝ (ρ.normed volume) t Complex.I : ℝ) : ℂ) * g (z - t)))
              ∂volume :=
    (integral_const_mul _ _).symm
  rw [hhalf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [qDeriv]
  ring

/-- Change of variables: `∫ q(t)·g(z−t) dt = ∫ q(z−y)·g(y) dy`. -/
lemma integral_qDeriv_mul_shift (ρ : ContDiffBump (0 : ℂ)) (g : ℂ → ℂ)
    (z : ℂ) :
    ∫ t, qDeriv ρ t * g (z - t) ∂volume
      = ∫ y, qDeriv ρ (z - y) * g y ∂volume := by
  have h := integral_sub_left_eq_self
    (fun t => qDeriv ρ t * g (z - t)) volume z
  simpa [sub_sub_cancel] using h.symm

end Convolution

section Vanishing

variable {h htilde : ℂ → ℂ} {U : Set ℂ}

/-- **The `∂̄` of the mollification vanishes** at points whose
`ρ.rOut`-ball stays inside `U` (and where the cutoff `htilde` agrees
with `h`). -/
lemma partialZBar_convolution_eq_zero
    (hweak : WeaklyDBarZeroOn h U) (hint : Integrable htilde volume)
    (ρ : ContDiffBump (0 : ℂ)) {z : ℂ}
    (hball : Metric.closedBall z ρ.rOut ⊆ U)
    (hagree : ∀ y ∈ Metric.closedBall z ρ.rOut, htilde y = h y) :
    partialZBar
      ((ρ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] htilde) z
      = 0 := by
  rw [partialZBar_convolution_left ρ hint z, integral_qDeriv_mul_shift]
  -- where `q(z−y) ≠ 0`, `y` is in the closed ball
  have hsupp : ∀ y : ℂ, qDeriv ρ (z - y) ≠ 0 →
      y ∈ Metric.closedBall z ρ.rOut := by
    intro y hy
    by_contra hyn
    refine hy (qDeriv_eq_zero_of_notMem ρ ?_)
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hyn ⊢
    simpa [Complex.dist_eq, norm_sub_rev] using hyn
  -- swap `htilde` for `h`
  have heq : ∀ y : ℂ, qDeriv ρ (z - y) * htilde y = qDeriv ρ (z - y) * h y := by
    intro y
    by_cases hq : qDeriv ρ (z - y) = 0
    · simp [hq]
    · rw [hagree y (hsupp y hq)]
  rw [integral_congr_ae (Filter.Eventually.of_forall heq)]
  -- the shifted bump is an admissible test function
  have hφsmooth : ContDiff ℝ ∞
      (fun y : ℂ => ((ρ.normed volume (z - y) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((ρ.contDiff_normed).comp (contDiff_const.sub contDiff_id))
  have hφsuppsub : Function.support
      (fun y : ℂ => ((ρ.normed volume (z - y) : ℝ) : ℂ))
        ⊆ Metric.closedBall z ρ.rOut := by
    intro y hy
    have hne : ρ.normed volume (z - y) ≠ 0 := by
      simpa [Function.mem_support, Complex.ofReal_eq_zero] using hy
    have hmem : z - y ∈ Function.support (ρ.normed volume) := hne
    rw [ρ.support_normed_eq] at hmem
    simp only [Metric.mem_ball, dist_zero_right] at hmem
    simp only [Metric.mem_closedBall]
    calc dist y z = ‖z - y‖ := by rw [Complex.dist_eq, norm_sub_rev]
      _ ≤ ρ.rOut := le_of_lt hmem
  have hφtsupp : tsupport (fun y : ℂ => ((ρ.normed volume (z - y) : ℝ) : ℂ))
      ⊆ Metric.closedBall z ρ.rOut :=
    closure_minimal hφsuppsub Metric.isClosed_closedBall
  have hφcompact : HasCompactSupport
      (fun y : ℂ => ((ρ.normed volume (z - y) : ℝ) : ℂ)) :=
    (isCompact_closedBall z ρ.rOut).of_isClosed_subset isClosed_closure
      hφtsupp
  have h0 := hweak _ hφsmooth hφcompact (hφtsupp.trans hball)
  -- rewrite the conclusion through the test-function identity
  have hkey : ∫ y, qDeriv ρ (z - y) * h y ∂volume
      = -∫ y, h y * partialZBar
          (fun w : ℂ => ((ρ.normed volume (z - w) : ℝ) : ℂ)) y ∂volume := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show qDeriv ρ (z - y) * h y
      = -(h y * partialZBar
          (fun w : ℂ => ((ρ.normed volume (z - w) : ℝ) : ℂ)) y)
    rw [partialZBar_shifted_bump ρ z y]
    ring
  rw [hkey, h0, neg_zero]

/-- **The mollification is holomorphic on the inner ball.** -/
lemma differentiableOn_convolution_ball
    (hweak : WeaklyDBarZeroOn h U) (hint : Integrable htilde volume)
    (ρ : ContDiffBump (0 : ℂ)) {z₀ : ℂ} {r : ℝ}
    (hrOut : ρ.rOut ≤ r)
    (hUball : Metric.closedBall z₀ (2 * r) ⊆ U)
    (hagree : ∀ y ∈ Metric.closedBall z₀ (2 * r), htilde y = h y) :
    DifferentiableOn ℂ
      ((ρ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] htilde)
      (Metric.ball z₀ r) := by
  intro z hz
  have hzdist : dist z z₀ < r := hz
  have hsub : Metric.closedBall z ρ.rOut ⊆ Metric.closedBall z₀ (2 * r) := by
    intro y hy
    have h1 : dist y z ≤ ρ.rOut := hy
    simp only [Metric.mem_closedBall]
    calc dist y z₀ ≤ dist y z + dist z z₀ := dist_triangle _ _ _
      _ ≤ ρ.rOut + r := by linarith
      _ ≤ 2 * r := by linarith
  have hzero := partialZBar_convolution_eq_zero hweak hint ρ
    (hsub.trans hUball) (fun y hy => hagree y (hsub hy))
  have hsmooth : ContDiff ℝ 1
      ((ρ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] htilde) :=
    (ρ.hasCompactSupport_normed).contDiff_convolution_left _
      (ρ.contDiff_normed) hint.locallyIntegrable
  have hdiff := differentiableAt_complex_of_differentiableAt_real_of_partialZBar_zero
    ((hsmooth.differentiable one_ne_zero).differentiableAt) hzero
  exact hdiff.differentiableWithinAt

end Vanishing

section Main

variable {h : ℂ → ℂ} {U : Set ℂ}

/-- **Weyl's lemma for `∂̄` on ℂ.** A continuous function on an open
set that is weakly `∂̄`-closed is holomorphic. -/
theorem differentiableOn_of_weaklyDBarZeroOn (hU : IsOpen U)
    (hcont : ContinuousOn h U) (hweak : WeaklyDBarZeroOn h U) :
    DifferentiableOn ℂ h U := by
  intro z₀ hz₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  set r : ℝ := ε / 3 with hr
  have hrpos : 0 < r := by positivity
  have hUball : Metric.closedBall z₀ (2 * r) ⊆ U := by
    intro y hy
    apply hball
    have hyd : dist y z₀ ≤ 2 * (ε / 3) := hy
    simp only [Metric.mem_ball]
    linarith
  set K : Set ℂ := Metric.closedBall z₀ (2 * r) with hK
  have hKcompact : IsCompact K := isCompact_closedBall _ _
  set htilde : ℂ → ℂ := K.indicator h with hht
  have hcontK : ContinuousOn h K := hcont.mono hUball
  have hint : Integrable htilde volume := by
    rw [hht, integrable_indicator_iff measurableSet_closedBall]
    exact hcontK.integrableOn_compact hKcompact
  have hagree : ∀ y ∈ K, htilde y = h y := fun y hy =>
    Set.indicator_of_mem hy h
  -- the mollifier sequence
  have hrn : ∀ n : ℕ, (0 : ℝ) < r / (n + 1) := fun n => by positivity
  set ρseq : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    { rIn := r / (n + 1) / 2
      rOut := r / (n + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := half_lt_self (hrn n) } with hρseq
  have hrOut_le : ∀ n : ℕ, (ρseq n).rOut ≤ r := by
    intro n
    rw [hρseq]
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    calc r / (n + 1) ≤ r / 1 := by
          apply div_le_div_of_nonneg_left (le_of_lt hrpos) one_pos h1
      _ = r := div_one r
  set u : ℕ → ℂ → ℂ := fun n =>
    (ρseq n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] htilde
    with hu
  -- each mollification is holomorphic on the inner ball
  have hudiff : ∀ n : ℕ, DifferentiableOn ℂ (u n) (Metric.ball z₀ r) :=
    fun n => differentiableOn_convolution_ball hweak hint (ρseq n)
      (hrOut_le n) hUball hagree
  -- uniform convergence on the inner ball
  have hballK : Metric.ball z₀ r ⊆ K := by
    intro x hx
    have : dist x z₀ < r := hx
    simp only [hK, Metric.mem_closedBall]
    linarith
  have hconv : TendstoUniformlyOn u h Filter.atTop (Metric.ball z₀ r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    have huc : UniformContinuousOn h K :=
      hKcompact.uniformContinuousOn_of_continuous hcontK
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨η, hη, hmod⟩ := huc (δ / 2) (by positivity)
    obtain ⟨N, hN⟩ := exists_nat_gt (r / η)
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn x hx => ?_⟩
    have hxK : x ∈ K := hballK hx
    have hrOutn : (ρseq n).rOut < η := by
      have h1 : r / η < (n : ℝ) + 1 := by
        have h2 : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
        linarith
      have h3 : r < η * ((n : ℝ) + 1) := by
        rw [div_lt_iff₀ hη] at h1
        linarith [h1]
      rw [hρseq]
      show r / ((n : ℝ) + 1) < η
      rw [div_lt_iff₀ (by positivity)]
      linarith
    have happrox : dist (u n x) (htilde x) ≤ δ / 2 := by
      apply ContDiffBump.dist_normed_convolution_le
        hint.aestronglyMeasurable
      intro y hy
      have hyx : dist y x < (ρseq n).rOut := hy
      have hyK : y ∈ K := by
        simp only [hK, Metric.mem_closedBall]
        have hx' : dist x z₀ < r := hx
        calc dist y z₀ ≤ dist y x + dist x z₀ := dist_triangle _ _ _
          _ ≤ (ρseq n).rOut + r := by
              have := hrOut_le n
              linarith
          _ ≤ 2 * r := by
              have := hrOut_le n
              linarith
      rw [hagree y hyK, hagree x hxK]
      exact le_of_lt (hmod y hyK x hxK (lt_trans hyx hrOutn))
    rw [hagree x hxK] at happrox
    calc dist (h x) (u n x) = dist (u n x) (h x) := dist_comm _ _
      _ ≤ δ / 2 := happrox
      _ < δ := by linarith
  -- pass to the limit
  have hlocconv : TendstoLocallyUniformlyOn u h Filter.atTop
      (Metric.ball z₀ r) := hconv.tendstoLocallyUniformlyOn
  have hdiff : DifferentiableOn ℂ h (Metric.ball z₀ r) :=
    hlocconv.differentiableOn (Filter.Eventually.of_forall hudiff)
      Metric.isOpen_ball
  exact (hdiff.differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hrpos))).differentiableWithinAt

/-- **Weyl's lemma, analytic form.** -/
theorem analyticOnNhd_of_weaklyDBarZeroOn (hU : IsOpen U)
    (hcont : ContinuousOn h U) (hweak : WeaklyDBarZeroOn h U) :
    AnalyticOnNhd ℂ h U :=
  (differentiableOn_of_weaklyDBarZeroOn hU hcont hweak).analyticOnNhd hU

end Main

end WeylDBar

end JacobianChallenge

end
