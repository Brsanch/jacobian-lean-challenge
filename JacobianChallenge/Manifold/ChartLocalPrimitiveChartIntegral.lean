/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartLocalPrimitive
import JacobianChallenge.Manifold.ChartLocalPrimitiveSmoothness
import JacobianChallenge.Manifold.ComplexChainPeriodSinglePathIntegral
import JacobianChallenge.Manifold.PointwiseChartEvalPath
import JacobianChallenge.Manifold.ComplexEvalIntegrandContinuity

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Chart-pulled identity for `chartLocalPrimitive`

For `x, y ∈ φ.source` with `φ = chartAt ℂ y` and convex `φ.target`,
the chart-local primitive of `om : HolomorphicOneForm X` at basepoint
`y`, evaluated at `x`, equals the chart-coord parametric integral:

  `chartLocalPrimitive (chartAt y) … y … om x …
     = ∫ t in 0..1,
         om.localCoeff y (bumpedSegment ((chartAt y) y) ((chartAt y) x) t)
           * chartCoordVelocity ((chartAt y) y) ((chartAt y) x) t`.

Proof structure:
* Chip B1 (`complexChainPeriod_single_eq_complex_integral_of_path`)
  converts the chain-period `complexChainPeriod (single γ) om` (= the
  unfolded `chartLocalPrimitive`) into the ℂ-valued path integral
  `∫ t in 0..1, (om.eval γ.ambient(t)) (γ.velocity t)`. Needs continuity
  of the ℂ-valued integrand on `[0, 1]`, discharged by
  `complexEvalIntegrand_continuous`.
* Chip B2 (`pointwiseChartEval_path`) gives the per-`t` chart-pullback
  identity for `γ = linearInChartSegment` (whose ambient lands in
  `φ.source` on `Icc 0 1`).
* Two structural identifications complete the substitution:
  - `(chartAt y) (γ.ambient t) = bumpedSegment (φy)(φx) t` on `Icc 0 1`
    via `ambient_eq_on_unitInterval` + `left_inv`.
  - `deriv ((chartAt y) ∘ γ.ambient) t = chartCoordVelocity (φy)(φx) t`
    on `Ioo 0 1` via `EventuallyEq.deriv_eq` (the chart-pulled path
    locally equals `bumpedSegment` on the interior).
* `intervalIntegral.integral_congr_ae` finishes (Ioo 0 1 is co-null
  in Ioc 0 1).

This is the chip-B headline; chip C transports the analyticity from
the chart-coord side (chip A) through this identity to the manifold-
side `ContMDiffOn ω`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex MeasureTheory Set

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Time-derivative of `bumpedSegment` -/

/-- The time-`t` derivative of `bumpedSegment z₀ z` is `chartCoordVelocity z₀ z t`.

Works directly with ℝ-smul on ℂ via `HasDerivAt.smul_const`, dodging
the `Complex.ofRealCLM ∘ ·` route. -/
lemma hasDerivAt_bumpedSegment_in_t (z₀ z : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => bumpedSegment z₀ z s) (chartCoordVelocity z₀ z t) t := by
  -- σ is C^∞, so `HasDerivAt σ (σ'(t)) t`.
  have h_sigma_cd : ContDiff ℝ ∞ Real.smoothTransition :=
    Real.smoothTransition.contDiff
  have h_sigma_diff : Differentiable ℝ Real.smoothTransition :=
    h_sigma_cd.differentiable (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have h_sigma_hasDeriv : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition t) t :=
    (h_sigma_diff t).hasDerivAt
  -- `1 - σ` has deriv `-σ'(t)`.
  have h_one_sub : HasDerivAt (fun s : ℝ => 1 - Real.smoothTransition s)
      (-(deriv Real.smoothTransition t)) t := by
    have := (hasDerivAt_const t (1 : ℝ)).sub h_sigma_hasDeriv
    simpa using this
  -- `(1 - σ) • z₀` and `σ • z` via `HasDerivAt.smul_const`.
  have h_first : HasDerivAt (fun s : ℝ => (1 - Real.smoothTransition s) • z₀)
      ((-(deriv Real.smoothTransition t)) • z₀) t :=
    h_one_sub.smul_const z₀
  have h_second : HasDerivAt (fun s : ℝ => Real.smoothTransition s • z)
      ((deriv Real.smoothTransition t) • z) t :=
    h_sigma_hasDeriv.smul_const z
  have h_sum := h_first.add h_second
  -- `bumpedSegment z₀ z = (1 - σ) • z₀ + σ • z` is definitional.
  show HasDerivAt (fun s : ℝ =>
        (1 - Real.smoothTransition s) • z₀ + Real.smoothTransition s • z)
      (chartCoordVelocity z₀ z t) t
  -- Reduce the derivative: `-σ'(t) • z₀ + σ'(t) • z = σ'(t) • (z - z₀) = chartCoordVelocity`.
  have h_id :
      (-(deriv Real.smoothTransition t)) • z₀ + (deriv Real.smoothTransition t) • z
        = chartCoordVelocity z₀ z t := by
    unfold chartCoordVelocity
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  rw [← h_id]
  exact h_sum

/-- The `deriv` form of `hasDerivAt_bumpedSegment_in_t`. -/
lemma deriv_bumpedSegment_eq_chartCoordVelocity (z₀ z : ℂ) (t : ℝ) :
    deriv (fun s : ℝ => bumpedSegment z₀ z s) t = chartCoordVelocity z₀ z t :=
  (hasDerivAt_bumpedSegment_in_t z₀ z t).deriv

/-! ## Chart-image identification on `Icc 0 1` -/

/-- For the linear-in-chart segment from `y` to `x`, the chart-pulled
ambient at any `t ∈ Icc 0 1` equals `bumpedSegment (φy) (φx) t`. -/
lemma chartAt_y_comp_linearInChartSegment_ambient_eq
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (y x : X) (hy : y ∈ φ.source) (hx : x ∈ φ.source)
    (h_seg : segment ℝ (φ y) (φ x) ⊆ φ.target)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    φ ((SmoothPath.linearInChartSegment φ h_atlas y x hy hx h_seg).ambient t)
      = bumpedSegment (φ y) (φ x) t := by
  -- ambient on unitInterval equals toPath at s.val = t.
  have h_amb := (SmoothPath.linearInChartSegment φ h_atlas y x hy hx h_seg).ambient_eq_on_unitInterval
    ⟨t, ht⟩
  rw [show ((⟨t, ht⟩ : unitInterval) : ℝ) = t from rfl] at h_amb
  rw [h_amb]
  -- toPath at ⟨t, ht⟩ = φ.symm (bumpedSegment (φ y) (φ x) t).
  show φ (φ.symm (bumpedSegment (φ y) (φ x) t)) = bumpedSegment (φ y) (φ x) t
  -- bumpedSegment t ∈ segment ⊆ φ.target ⟹ φ ∘ φ.symm = id.
  have h_mem : bumpedSegment (φ y) (φ x) t ∈ φ.target :=
    h_seg (bumpedSegment_mem_segment _ _ _)
  exact φ.right_inv h_mem

/-! ## `EventuallyEq` of the chart-pulled ambient and `bumpedSegment` -/

/-- On a neighborhood of any `t ∈ Ioo 0 1`, the chart-pulled ambient
`(chartAt y) ∘ γ.ambient` equals `bumpedSegment (φy) (φx)`. -/
lemma chartAt_y_comp_linearInChartSegment_ambient_eventuallyEq
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (y x : X) (hy : y ∈ φ.source) (hx : x ∈ φ.source)
    (h_seg : segment ℝ (φ y) (φ x) ⊆ φ.target)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (fun s : ℝ => φ
      ((SmoothPath.linearInChartSegment φ h_atlas y x hy hx h_seg).ambient s))
      =ᶠ[nhds t] (fun s : ℝ => bumpedSegment (φ y) (φ x) s) := by
  refine Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Ioo ht) ?_
  intro s hs
  have hs_icc : s ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  exact chartAt_y_comp_linearInChartSegment_ambient_eq
    φ h_atlas y x hy hx h_seg hs_icc

/-! ## Headline: chip-B identity for `chartLocalPrimitive` -/

/-- **Chip-B identity: `chartLocalPrimitive` as a chart-coord parametric integral.**

For `om : HolomorphicOneForm X`, `y : X`, and `x ∈ (chartAt ℂ y).source`,
with `(chartAt ℂ y).target` convex,

  `chartLocalPrimitive (chartAt y) … y … om x …
     = ∫ t in 0..1,
         om.localCoeff y (bumpedSegment ((chartAt y) y) ((chartAt y) x) t)
           * chartCoordVelocity ((chartAt y) y) ((chartAt y) x) t`.

Proof combines chip B1 + chip B2 + the two identifications (chart-image
on `Icc 0 1`, chart-pulled-deriv on `Ioo 0 1`) + `integral_congr_ae`. -/
theorem chartLocalPrimitive_eq_chartCoordIntegral
    (y : X) (h_target_convex : Convex ℝ (chartAt ℂ y).target)
    (om : HolomorphicOneForm X)
    (x : X) (hx : x ∈ (chartAt ℂ y).source) :
    chartLocalPrimitive (chartAt ℂ y) (chart_mem_atlas ℂ y) h_target_convex
        y (mem_chart_source ℂ y) om x hx
      = ∫ t in (0 : ℝ)..1,
          om.localCoeff y
              (bumpedSegment ((chartAt ℂ y) y) ((chartAt ℂ y) x) t) *
            chartCoordVelocity ((chartAt ℂ y) y) ((chartAt ℂ y) x) t := by
  -- Notation: γ := the linear-in-chart segment.
  set φ : OpenPartialHomeomorph X ℂ := chartAt ℂ y with hφ
  have h_atlas : φ ∈ atlas ℂ X := chart_mem_atlas ℂ y
  have hy : y ∈ φ.source := mem_chart_source ℂ y
  have h_seg : segment ℝ (φ y) (φ x) ⊆ φ.target :=
    Convex.segment_subset h_target_convex (φ.map_source hy) (φ.map_source hx)
  set γ : SmoothPath 𝓘(ℝ, ℂ) X :=
    SmoothPath.linearInChartSegment φ h_atlas y x hy hx h_seg with hγ_def
  -- Step 1: chartLocalPrimitive unfolds to complexChainPeriod.
  show complexChainPeriod (SmoothChain.single γ) om = _
  -- Step 2: chip B1 — convert to the ℂ-valued path integral.
  have h_cont : ContinuousOn
      (fun t : ℝ => (om.eval (γ.ambient t)) (γ.velocity t))
      (Set.Icc (0 : ℝ) 1) :=
    (ChartContainedClosedLoop.complexEvalIntegrand_continuous γ om).continuousOn
  rw [complexChainPeriod_single_eq_complex_integral_of_path γ om h_cont]
  -- Step 3: identify the integrand via chip B2 + structural identifications.
  -- Prove equality on Ioo 0 1; lift to a.e. on Ioc 0 1 via {1} measure zero.
  refine intervalIntegral.integral_congr_ae ?_
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  -- Pointwise equality at every `t ∈ Ioo 0 1`.
  have h_eq_on_ioo : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      (om.eval (γ.ambient t)) (γ.velocity t)
        = om.localCoeff y
            (bumpedSegment ((chartAt ℂ y) y) ((chartAt ℂ y) x) t) *
          chartCoordVelocity ((chartAt ℂ y) y) ((chartAt ℂ y) x) t := by
    intro t ht
    have ht_icc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    -- γ.ambient t ∈ φ.source via the ambient = φ.symm ∘ B identity.
    have h_amb_src : γ.ambient t ∈ φ.source := by
      have h_bs_mem : bumpedSegment (φ y) (φ x) t ∈ φ.target :=
        h_seg (bumpedSegment_mem_segment _ _ _)
      have h_amb_eq := γ.ambient_eq_on_unitInterval ⟨t, ht_icc⟩
      rw [show ((⟨t, ht_icc⟩ : unitInterval) : ℝ) = t from rfl] at h_amb_eq
      rw [h_amb_eq]
      show φ.symm (bumpedSegment (φ y) (φ x) t) ∈ φ.source
      exact φ.map_target h_bs_mem
    -- chip B2 at (γ, y, om, t).
    have h_chip_b2 := SmoothPath.pointwiseChartEval_path γ y om h_amb_src
    rw [h_chip_b2]
    -- Substitute chart-image identification on Icc.
    rw [chartAt_y_comp_linearInChartSegment_ambient_eq
      φ h_atlas y x hy hx h_seg ht_icc]
    -- Substitute deriv identification (EventuallyEq → deriv equality).
    have h_eventually := chartAt_y_comp_linearInChartSegment_ambient_eventuallyEq
      φ h_atlas y x hy hx h_seg ht
    have h_deriv_eq : deriv ((φ : X → ℂ) ∘ γ.ambient) t
        = deriv (fun s : ℝ => bumpedSegment (φ y) (φ x) s) t :=
      Filter.EventuallyEq.deriv_eq h_eventually
    show om.localCoeff y (bumpedSegment (φ y) (φ x) t)
            * deriv ((φ : X → ℂ) ∘ γ.ambient) t
        = om.localCoeff y (bumpedSegment ((chartAt ℂ y) y) ((chartAt ℂ y) x) t)
            * chartCoordVelocity ((chartAt ℂ y) y) ((chartAt ℂ y) x) t
    rw [h_deriv_eq, deriv_bumpedSegment_eq_chartCoordVelocity]
  -- Lift to a.e. on Ioc 0 1: complement of Ioo in Ioc is {1}, measure zero.
  have h_subset : {a : ℝ | ¬ (a ∈ Set.Ioc (0 : ℝ) 1 →
        (om.eval (γ.ambient a)) (γ.velocity a) =
          om.localCoeff y
              (bumpedSegment ((chartAt ℂ y) y) ((chartAt ℂ y) x) a) *
            chartCoordVelocity ((chartAt ℂ y) y) ((chartAt ℂ y) x) a)}
      ⊆ ({1} : Set ℝ) := by
    intro t ht_not
    rw [Set.mem_setOf_eq, Classical.not_imp] at ht_not
    obtain ⟨ht_ioc, ht_neq⟩ := ht_not
    rw [Set.mem_singleton_iff]
    by_contra h_t_neq_one
    have ht_lt_one : t < 1 := lt_of_le_of_ne ht_ioc.2 h_t_neq_one
    have ht_ioo : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht_ioc.1, ht_lt_one⟩
    exact ht_neq (h_eq_on_ioo t ht_ioo)
  refine MeasureTheory.ae_iff.mpr ?_
  exact MeasureTheory.measure_mono_null h_subset Real.volume_singleton

end JacobianChallenge

end
