/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AnalyticOnIntervalIntegralParam
import JacobianChallenge.Manifold.ChartLocalIntegrandAnalyticInZ
import JacobianChallenge.Manifold.ChartLocalPrimitiveSmoothness
import Mathlib.Analysis.Calculus.FDeriv.Analytic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

/-! # `AnalyticOn ℂ` of the chart-coord parametric integral

For `f : ℂ → ℂ` analytic on a convex open set `S ⊆ ℂ` containing `z₀`,
the parametric integral

  `g(z) := ∫ t in 0..1, f (bumpedSegment z₀ z t) * chartCoordVelocity z₀ z t`

is `AnalyticOn ℂ` on `S`. Combines the two foundation atoms (chips 10
and 11):

* per-z `HasDerivAt` of the integrand at every `z ∈ S` for every `t : ℝ`,
  built from the per-z analyticity (chip 11) via the explicit chain +
  product rule (`bumpedSegment` and `chartCoordVelocity` are both
  ℂ-affine in `z`);
* compactness of `closedBall z₁ ε × [0, 1]` ⊆ `ℂ × ℝ` → uniform bound on
  the jointly continuous explicit `∂z`-derivative on that closed ball;
* `analyticOn_intervalIntegral_param` (chip 10) discharges the result.

Specialised to `f := localCoeff om y` and `S := (chartAt ℂ y).target`,
this gives the chart-coord side of `ChartLocalPrimitiveSmoothExt`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Topology MeasureTheory ContDiff
open MeasureTheory Set Filter

namespace JacobianChallenge

/-! ## Explicit ∂z-derivative of the chart-coord integrand -/

/-- The explicit ∂z-derivative of `f(B(z,t)) * V(z,t)`:

    `f'(B(z,t)) * σ(t) * V(z,t) + f(B(z,t)) * σ'(t)`

where `B(z,t) = bumpedSegment z₀ z t`, `V(z,t) = chartCoordVelocity z₀ z t`,
`σ = Real.smoothTransition`, and `σ' = deriv σ`. The scalars `σ(t), σ'(t)`
are real, cast to ℂ here.

Marked `@[irreducible]` to prevent elaboration cascades when this def
appears in `ContinuousOn`/`Continuous` lemma signatures — typeclass
synthesis can otherwise blow past `maxHeartbeats` trying to whnf the
body during defeq checks. Access the body via the `_eq` lemma below or
`unfold chartLocalIntegrandDerivInZ`. -/
@[irreducible]
noncomputable def chartLocalIntegrandDerivInZ (f : ℂ → ℂ) (z₀ z : ℂ) (t : ℝ) : ℂ :=
  deriv f (bumpedSegment z₀ z t) *
      ((Real.smoothTransition t : ℝ) : ℂ) *
      chartCoordVelocity z₀ z t
    + f (bumpedSegment z₀ z t) *
      ((deriv Real.smoothTransition t : ℝ) : ℂ)

/-- The defining equality of `chartLocalIntegrandDerivInZ`. -/
lemma chartLocalIntegrandDerivInZ_eq (f : ℂ → ℂ) (z₀ z : ℂ) (t : ℝ) :
    chartLocalIntegrandDerivInZ f z₀ z t =
      deriv f (bumpedSegment z₀ z t) *
          ((Real.smoothTransition t : ℝ) : ℂ) *
          chartCoordVelocity z₀ z t
        + f (bumpedSegment z₀ z t) *
          ((deriv Real.smoothTransition t : ℝ) : ℂ) := by
  unfold chartLocalIntegrandDerivInZ
  rfl

/-! ## Pointwise `HasDerivAt` lemmas for the affine factors -/

/-- `bumpedSegment z₀ · t` is `ℂ-affine` in `z`; its `z`-derivative is
`σ(t) : ℂ`. -/
lemma hasDerivAt_bumpedSegment_in_z (z₀ : ℂ) (t : ℝ) (z : ℂ) :
    HasDerivAt (fun z' : ℂ => bumpedSegment z₀ z' t)
      ((Real.smoothTransition t : ℝ) : ℂ) z := by
  -- Rewrite `bumpedSegment z₀ z' t` as ℂ-affine in `z'`.
  have h_eq : (fun z' : ℂ => bumpedSegment z₀ z' t)
      = fun z' : ℂ =>
        ((1 - Real.smoothTransition t : ℝ) : ℂ) * z₀
          + ((Real.smoothTransition t : ℝ) : ℂ) * z' := by
    funext z'
    show (1 - Real.smoothTransition t) • z₀ + Real.smoothTransition t • z'
        = ((1 - Real.smoothTransition t : ℝ) : ℂ) * z₀
          + ((Real.smoothTransition t : ℝ) : ℂ) * z'
    rw [Complex.real_smul, Complex.real_smul]
  rw [h_eq]
  -- Constant term + linear term.
  have h_const : HasDerivAt
      (fun _ : ℂ => ((1 - Real.smoothTransition t : ℝ) : ℂ) * z₀) 0 z :=
    hasDerivAt_const z _
  have h_lin : HasDerivAt
      (fun z' : ℂ => ((Real.smoothTransition t : ℝ) : ℂ) * z')
      ((Real.smoothTransition t : ℝ) : ℂ) z := by
    have h_id : HasDerivAt (fun z' : ℂ => z') 1 z := hasDerivAt_id z
    have h_mul := h_id.const_mul ((Real.smoothTransition t : ℝ) : ℂ)
    -- `h_mul : HasDerivAt (fun z' => (σ:ℂ) * z') ((σ:ℂ) * 1) z`.
    rw [mul_one] at h_mul
    exact h_mul
  have h_sum := h_const.add h_lin
  -- `h_sum : HasDerivAt _ (0 + (σ:ℂ)) z` ⟹ rewrite `zero_add`.
  rw [zero_add] at h_sum
  exact h_sum

/-- `chartCoordVelocity z₀ · t` is `ℂ-affine` in `z`; its `z`-derivative
is `σ'(t) : ℂ`. -/
lemma hasDerivAt_chartCoordVelocity_in_z (z₀ : ℂ) (t : ℝ) (z : ℂ) :
    HasDerivAt (fun z' : ℂ => chartCoordVelocity z₀ z' t)
      ((deriv Real.smoothTransition t : ℝ) : ℂ) z := by
  -- `chartCoordVelocity z₀ z' t = ((σ'(t):ℝ):ℂ) * (z' - z₀)`.
  show HasDerivAt
      (fun z' : ℂ => ((deriv Real.smoothTransition t : ℝ) : ℂ) * (z' - z₀))
      ((deriv Real.smoothTransition t : ℝ) : ℂ) z
  have h_sub : HasDerivAt (fun z' : ℂ => z' - z₀) 1 z :=
    (hasDerivAt_id z).sub_const z₀
  have h_mul := h_sub.const_mul ((deriv Real.smoothTransition t : ℝ) : ℂ)
  rw [mul_one] at h_mul
  exact h_mul

/-- **`HasDerivAt` in `z` of the chart-coord integrand** at every `z ∈ S`,
for every `t : ℝ`, with the explicit derivative `chartLocalIntegrandDerivInZ`. -/
lemma hasDerivAt_chartLocalIntegrand_in_z
    {f : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S) (hS_conv : Convex ℝ S)
    (hf : AnalyticOn ℂ f S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S)
    {z : ℂ} (hz : z ∈ S) (t : ℝ) :
    HasDerivAt
        (fun z' : ℂ => f (bumpedSegment z₀ z' t) * chartCoordVelocity z₀ z' t)
        (chartLocalIntegrandDerivInZ f z₀ z t) z := by
  -- `f` is differentiable at `bumpedSegment z₀ z t ∈ S`.
  have h_im_mem : bumpedSegment z₀ z t ∈ S :=
    bumpedSegment_mem_of_convex hS_conv hz₀ hz t
  have hf_at : HasDerivAt f (deriv f (bumpedSegment z₀ z t))
      (bumpedSegment z₀ z t) := by
    have h_anal : AnalyticAt ℂ f (bumpedSegment z₀ z t) :=
      hf.analyticAt (hS.mem_nhds h_im_mem)
    exact h_anal.differentiableAt.hasDerivAt
  -- Chain rule with bumpedSegment-in-z deriv.
  have h_bs : HasDerivAt (fun z' : ℂ => bumpedSegment z₀ z' t)
      ((Real.smoothTransition t : ℝ) : ℂ) z :=
    hasDerivAt_bumpedSegment_in_z z₀ t z
  have h_comp : HasDerivAt (fun z' : ℂ => f (bumpedSegment z₀ z' t))
      (deriv f (bumpedSegment z₀ z t) *
        ((Real.smoothTransition t : ℝ) : ℂ)) z := hf_at.comp z h_bs
  -- Product rule with chartCoordVelocity-in-z deriv.
  have h_vel : HasDerivAt (fun z' : ℂ => chartCoordVelocity z₀ z' t)
      ((deriv Real.smoothTransition t : ℝ) : ℂ) z :=
    hasDerivAt_chartCoordVelocity_in_z z₀ t z
  have h_prod := h_comp.mul h_vel
  -- The product rule gives exactly the unfolded `chartLocalIntegrandDerivInZ`.
  rw [chartLocalIntegrandDerivInZ_eq]
  exact h_prod

/-! ## Joint continuity of the explicit ∂z-derivative -/

/-- The explicit ∂z-derivative `chartLocalIntegrandDerivInZ` is jointly
continuous on `S × Set.univ` whenever `f` and `deriv f` are continuous
on the (convex open) `S` containing `z₀`. -/
lemma continuousOn_chartLocalIntegrandDerivInZ
    {f : ℂ → ℂ} {S : Set ℂ} (hS_conv : Convex ℝ S)
    (hf : ContinuousOn f S) (hfd : ContinuousOn (deriv f) S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) :
    ContinuousOn
        (fun p : ℂ × ℝ => chartLocalIntegrandDerivInZ f z₀ p.1 p.2)
        (S ×ˢ Set.univ) := by
  simp only [chartLocalIntegrandDerivInZ_eq]
  have h_bs_cts : Continuous (fun p : ℂ × ℝ => bumpedSegment z₀ p.1 p.2) :=
    continuous_bumpedSegment_param z₀
  have h_vel_cts : Continuous (fun p : ℂ × ℝ => chartCoordVelocity z₀ p.1 p.2) :=
    continuous_chartCoordVelocity_param z₀
  have h_bs_to_S : ∀ p : ℂ × ℝ, p ∈ S ×ˢ Set.univ →
      bumpedSegment z₀ p.1 p.2 ∈ S := fun p hp =>
    bumpedSegment_mem_of_convex hS_conv hz₀ hp.1 p.2
  have h_f_bs : ContinuousOn (fun p : ℂ × ℝ => f (bumpedSegment z₀ p.1 p.2))
      (S ×ˢ Set.univ) := hf.comp h_bs_cts.continuousOn h_bs_to_S
  have h_df_bs : ContinuousOn (fun p : ℂ × ℝ => deriv f (bumpedSegment z₀ p.1 p.2))
      (S ×ˢ Set.univ) := hfd.comp h_bs_cts.continuousOn h_bs_to_S
  have h_sigma_cts : Continuous (fun t : ℝ => ((Real.smoothTransition t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp Real.smoothTransition.continuous
  have h_sigma'_cts : Continuous (deriv Real.smoothTransition) := by
    have h_cd : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
    exact h_cd.continuous_deriv (by show (1 : WithTop ℕ∞) ≤ ∞; decide)
  have h_sigma'_cast_cts :
      Continuous (fun t : ℝ => ((deriv Real.smoothTransition t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp h_sigma'_cts
  have h_term1 : ContinuousOn (fun p : ℂ × ℝ =>
      deriv f (bumpedSegment z₀ p.1 p.2) *
          ((Real.smoothTransition p.2 : ℝ) : ℂ) *
          chartCoordVelocity z₀ p.1 p.2) (S ×ˢ Set.univ) :=
    ((h_df_bs.mul ((h_sigma_cts.comp continuous_snd).continuousOn)).mul
      h_vel_cts.continuousOn)
  have h_term2 : ContinuousOn (fun p : ℂ × ℝ =>
      f (bumpedSegment z₀ p.1 p.2) *
          ((deriv Real.smoothTransition p.2 : ℝ) : ℂ)) (S ×ˢ Set.univ) :=
    h_f_bs.mul ((h_sigma'_cast_cts.comp continuous_snd).continuousOn)
  exact h_term1.add h_term2

/-! ## Joint continuity of the chart-coord integrand itself -/

/-- The chart-coord integrand `f(B(z,t)) * V(z,t)` is jointly continuous
on `S × Set.univ` whenever `f` is continuous on the convex open `S`
containing `z₀`. -/
lemma continuousOn_chartLocalIntegrand
    {f : ℂ → ℂ} {S : Set ℂ} (hS_conv : Convex ℝ S)
    (hf : ContinuousOn f S) {z₀ : ℂ} (hz₀ : z₀ ∈ S) :
    ContinuousOn
        (fun p : ℂ × ℝ =>
          f (bumpedSegment z₀ p.1 p.2) * chartCoordVelocity z₀ p.1 p.2)
        (S ×ˢ Set.univ) := by
  have h_bs_cts : Continuous (fun p : ℂ × ℝ => bumpedSegment z₀ p.1 p.2) :=
    continuous_bumpedSegment_param z₀
  have h_vel_cts : Continuous (fun p : ℂ × ℝ => chartCoordVelocity z₀ p.1 p.2) :=
    continuous_chartCoordVelocity_param z₀
  have h_bs_to_S : ∀ p : ℂ × ℝ, p ∈ S ×ˢ Set.univ →
      bumpedSegment z₀ p.1 p.2 ∈ S := fun p hp =>
    bumpedSegment_mem_of_convex hS_conv hz₀ hp.1 p.2
  have h_f_bs : ContinuousOn (fun p : ℂ × ℝ => f (bumpedSegment z₀ p.1 p.2))
      (S ×ˢ Set.univ) := hf.comp h_bs_cts.continuousOn h_bs_to_S
  exact h_f_bs.mul h_vel_cts.continuousOn

/-! ## Per-slice continuity at fixed `z` -/

/-- For fixed `z ∈ S`, the chart-coord integrand `t ↦ f(B(z,t)) * V(z,t)`
is continuous on `ℝ`. -/
lemma continuous_chartLocalIntegrand_slice
    {f : ℂ → ℂ} {S : Set ℂ} (hS_conv : Convex ℝ S)
    (hf : ContinuousOn f S) {z₀ : ℂ} (hz₀ : z₀ ∈ S)
    {z : ℂ} (hz : z ∈ S) :
    Continuous (fun t : ℝ =>
      f (bumpedSegment z₀ z t) * chartCoordVelocity z₀ z t) := by
  have h_pair : Continuous (fun t : ℝ => ((z, t) : ℂ × ℝ)) :=
    Continuous.prodMk continuous_const continuous_id
  have h_mem : ∀ t : ℝ, ((z, t) : ℂ × ℝ) ∈ S ×ˢ Set.univ :=
    fun _ => ⟨hz, mem_univ _⟩
  exact (continuousOn_chartLocalIntegrand hS_conv hf hz₀).comp_continuous h_pair h_mem

/-- For fixed `z ∈ S`, the explicit ∂z-derivative
`t ↦ chartLocalIntegrandDerivInZ f z₀ z t` is continuous on `ℝ`. -/
lemma continuous_chartLocalIntegrandDerivInZ_slice
    {f : ℂ → ℂ} {S : Set ℂ} (hS_conv : Convex ℝ S)
    (hf : ContinuousOn f S) (hfd : ContinuousOn (deriv f) S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) {z : ℂ} (hz : z ∈ S) :
    Continuous (fun t : ℝ => chartLocalIntegrandDerivInZ f z₀ z t) := by
  have h_pair : Continuous (fun t : ℝ => ((z, t) : ℂ × ℝ)) :=
    Continuous.prodMk continuous_const continuous_id
  have h_mem : ∀ t : ℝ, ((z, t) : ℂ × ℝ) ∈ S ×ˢ Set.univ :=
    fun _ => ⟨hz, mem_univ _⟩
  exact (continuousOn_chartLocalIntegrandDerivInZ hS_conv hf hfd hz₀).comp_continuous
    h_pair h_mem

/-! ## The headline `AnalyticOn ℂ` result -/

/-- **`AnalyticOn ℂ` of the chart-coord parametric integral** on a convex
open `S` containing `z₀`, for any analytic `f` on `S`. -/
theorem analyticOn_chartLocalIntegrand_param
    {f : ℂ → ℂ} {S : Set ℂ}
    (hS_open : IsOpen S) (hS_conv : Convex ℝ S)
    (hf : AnalyticOn ℂ f S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) :
    AnalyticOn ℂ
        (fun z : ℂ => ∫ t in (0 : ℝ)..1,
          f (bumpedSegment z₀ z t) * chartCoordVelocity z₀ z t) S := by
  have hf_cts : ContinuousOn f S := hf.continuousOn
  have hfd_cts : ContinuousOn (deriv f) S := by
    have h_deriv_an : AnalyticOnNhd ℂ (deriv f) S := by
      intro z hz
      exact (hf.analyticAt (hS_open.mem_nhds hz)).deriv
    exact h_deriv_an.continuousOn
  have h_slice_int : ∀ z ∈ S, Continuous (fun t : ℝ =>
      f (bumpedSegment z₀ z t) * chartCoordVelocity z₀ z t) :=
    fun z hz => continuous_chartLocalIntegrand_slice hS_conv hf_cts hz₀ hz
  have h_slice_deriv : ∀ z ∈ S, Continuous (fun t : ℝ =>
      chartLocalIntegrandDerivInZ f z₀ z t) :=
    fun z hz => continuous_chartLocalIntegrandDerivInZ_slice
      hS_conv hf_cts hfd_cts hz₀ hz
  have h_deriv_on_S : ContinuousOn
      (fun p : ℂ × ℝ => chartLocalIntegrandDerivInZ f z₀ p.1 p.2)
      (S ×ˢ Set.univ) :=
    continuousOn_chartLocalIntegrandDerivInZ hS_conv hf_cts hfd_cts hz₀
  have h_meas_F : ∀ᶠ z in Filter.principal S,
      AEStronglyMeasurable
        (fun t : ℝ =>
          f (bumpedSegment z₀ z t) * chartCoordVelocity z₀ z t)
        (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    rw [Filter.eventually_principal]
    intro z hz
    exact (h_slice_int z hz).aestronglyMeasurable.restrict
  have h_int_F : ∀ z ∈ S,
      IntervalIntegrable
        (fun t : ℝ =>
          f (bumpedSegment z₀ z t) * chartCoordVelocity z₀ z t)
        volume 0 1 := by
    intro z hz
    exact (h_slice_int z hz).intervalIntegrable 0 1
  have h_meas_F' : ∀ z ∈ S,
      AEStronglyMeasurable
        (fun t : ℝ => chartLocalIntegrandDerivInZ f z₀ z t)
        (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    intro z hz
    exact (h_slice_deriv z hz).aestronglyMeasurable.restrict
  have h_local_bound : ∀ z₁ ∈ S, ∃ ε > 0, Metric.ball z₁ ε ⊆ S ∧
      ∃ bound : ℝ → ℝ, IntervalIntegrable bound volume 0 1 ∧
        ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 →
          ∀ z ∈ Metric.ball z₁ ε,
            ‖chartLocalIntegrandDerivInZ f z₀ z t‖ ≤ bound t := by
    intro z₁ hz₁
    obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.isOpen_iff.mp hS_open z₁ hz₁
    refine ⟨δ / 2, by positivity, ?_, ?_⟩
    · intro w hw
      apply hδ_sub
      rw [Metric.mem_ball] at hw ⊢
      linarith
    have h_cb_sub : Metric.closedBall z₁ (δ / 2) ⊆ S := by
      intro w hw
      apply hδ_sub
      rw [Metric.mem_closedBall] at hw
      rw [Metric.mem_ball]
      linarith
    have h_compact : IsCompact
        (Metric.closedBall z₁ (δ / 2) ×ˢ Set.Icc (0 : ℝ) 1) :=
      (isCompact_closedBall z₁ (δ / 2)).prod isCompact_Icc
    have h_ne : (Metric.closedBall z₁ (δ / 2) ×ˢ Set.Icc (0 : ℝ) 1).Nonempty :=
      ⟨(z₁, 0),
        Metric.mem_closedBall_self (by positivity),
        by constructor <;> norm_num⟩
    have h_deriv_compact : ContinuousOn
        (fun p : ℂ × ℝ => chartLocalIntegrandDerivInZ f z₀ p.1 p.2)
        (Metric.closedBall z₁ (δ / 2) ×ˢ Set.Icc (0 : ℝ) 1) := by
      apply h_deriv_on_S.mono
      intro p hp
      exact ⟨h_cb_sub hp.1, mem_univ _⟩
    have h_norm_cts : ContinuousOn
        (fun p : ℂ × ℝ => ‖chartLocalIntegrandDerivInZ f z₀ p.1 p.2‖)
        (Metric.closedBall z₁ (δ / 2) ×ˢ Set.Icc (0 : ℝ) 1) :=
      h_deriv_compact.norm
    obtain ⟨p_max, _, hp_max⟩ :=
      h_compact.exists_isMaxOn h_ne h_norm_cts
    refine ⟨fun _ : ℝ =>
        ‖chartLocalIntegrandDerivInZ f z₀ p_max.1 p_max.2‖,
      intervalIntegrable_const, ?_⟩
    refine Filter.Eventually.of_forall ?_
    intro t ht z hz_ball
    have hz_cb : z ∈ Metric.closedBall z₁ (δ / 2) := by
      rw [Metric.mem_ball] at hz_ball
      rw [Metric.mem_closedBall]
      linarith
    have ht_Icc : t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact ⟨le_of_lt ht.1, ht.2⟩
    have hp_mem : (z, t) ∈ Metric.closedBall z₁ (δ / 2) ×ˢ Set.Icc (0 : ℝ) 1 :=
      Set.mk_mem_prod hz_cb ht_Icc
    exact hp_max hp_mem
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 →
      ∀ z ∈ S, HasDerivAt
        (fun z' : ℂ =>
          f (bumpedSegment z₀ z' t) * chartCoordVelocity z₀ z' t)
        (chartLocalIntegrandDerivInZ f z₀ z t) z := by
    refine Filter.Eventually.of_forall ?_
    intro t _ z hz
    exact hasDerivAt_chartLocalIntegrand_in_z hS_open hS_conv hf hz₀ hz t
  exact analyticOn_intervalIntegral_param
    (f := fun z t =>
      f (bumpedSegment z₀ z t) * chartCoordVelocity z₀ z t)
    (f' := fun z t => chartLocalIntegrandDerivInZ f z₀ z t)
    (S := S) hS_open (a := 0) (b := 1)
    h_meas_F h_int_F h_meas_F' h_local_bound h_diff

end JacobianChallenge

end
