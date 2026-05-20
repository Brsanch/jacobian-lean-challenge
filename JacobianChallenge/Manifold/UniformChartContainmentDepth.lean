/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.IteratedMidpointDiameter
import JacobianChallenge.Manifold.BoundaryPeriodFromDepthN
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # `UniformChartContainmentDepth_named X` is UNCONDITIONAL

We discharge
`UniformChartContainmentDepth_named X` — every smooth 2-simplex `σ`
on a compact connected complex 1-manifold `X` admits a depth `n` at
which every sub-simplex in `iteratedMidpointList σ n` admits a
`ChartContainmentWitness` — via the classical **Lebesgue number**
argument:

1. For each `q : X`, pick a metric ball
   `Metric.ball (chartAt ℂ q q) (chartBallRadius q) ⊆ (chartAt ℂ q).target`
   inside the chart target (exists since the chart target is open and
   contains `chartAt ℂ q q`).
2. Pull this ball back through the chart to get an open set
   `chartSourceBallPreimage q ⊆ X` containing `q`.
3. The collection `{σ⁻¹ (chartSourceBallPreimage σ(p)) : p ∈ Δ²}` is
   an open cover of the compact metric set `standardSimplex2`. Apply
   Lebesgue's number lemma to get `δ > 0` such that any open ball in
   `Δ²` of radius `δ` lies inside some cover element.
4. By the **depth-`n` diameter bound** (chip C), the parameter image
   of every `T ∈ iteratedMidpointList σ n` lies inside the
   `(1/2)^n`-closed-ball around the first vertex `A` of its affine
   form. Pick `n` so `(1/2)^n < δ` (`exists_pow_lt_of_lt_one`); then
   the parameter image lies inside some `σ⁻¹ (chartSourceBallPreimage
   σ(p))`, so `T`'s `σ`-image lies inside the chart-ball at `σ(p)` —
   a `ChartContainmentWitness`.

Headline: `uniformChartContainmentDepth_named_holds`. Combined with
the chip-A-and-prior wiring this closes
`HolomorphicComponentsCanonicalClosed X` on every compact connected
complex 1-manifold unconditionally — the final atomic period-lattice
input at general genus.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex Set

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Compactness of `standardSimplex2` -/

/-- `standardSimplex2` is closed in `Fin 2 → ℝ`. -/
lemma isClosed_standardSimplex2 : IsClosed (standardSimplex2 : Set (Fin 2 → ℝ)) := by
  -- intersection of three preimages of closed half-lines
  have h0 : Continuous (fun p : Fin 2 → ℝ => p 0) := continuous_apply 0
  have h1 : Continuous (fun p : Fin 2 → ℝ => p 1) := continuous_apply 1
  have h_sum : Continuous (fun p : Fin 2 → ℝ => p 0 + p 1) := h0.add h1
  have : standardSimplex2 =
      {p : Fin 2 → ℝ | 0 ≤ p 0} ∩ {p | 0 ≤ p 1} ∩ {p | p 0 + p 1 ≤ 1} := by
    ext p; simp [standardSimplex2, and_assoc]
  rw [this]
  exact (((isClosed_Ici).preimage h0).inter ((isClosed_Ici).preimage h1)).inter
    ((isClosed_Iic).preimage h_sum)

/-- `standardSimplex2` is contained in the closed unit `Metric.closedBall 0 1`
of `Fin 2 → ℝ`. Every coordinate `p i` lies in `[0, 1]`, hence
`|p i| ≤ 1`, hence `dist p 0 = ⨆ i, |p i| ≤ 1`. -/
lemma standardSimplex2_subset_closedBall :
    (standardSimplex2 : Set (Fin 2 → ℝ)) ⊆ Metric.closedBall 0 1 := by
  intro p hp
  obtain ⟨h0, h1, h_sum⟩ := hp
  rw [Metric.mem_closedBall]
  rw [dist_pi_le_iff zero_le_one]
  intro i
  simp only [Pi.zero_apply, Real.dist_eq, sub_zero]
  fin_cases i
  · change |p 0| ≤ 1; rw [abs_of_nonneg h0]; linarith
  · change |p 1| ≤ 1; rw [abs_of_nonneg h1]; linarith

/-- `standardSimplex2` is compact: it's closed and contained in the compact
closed unit ball of `Fin 2 → ℝ` (proper space, so closed balls are compact). -/
lemma isCompact_standardSimplex2 :
    IsCompact (standardSimplex2 : Set (Fin 2 → ℝ)) :=
  (Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_standardSimplex2,
      (Metric.isBounded_closedBall.subset standardSimplex2_subset_closedBall)⟩)

/-! ## Chart-ball-radius and chart-source-ball-preimage -/

/-- For each `q : X`, an `r > 0` with `Metric.ball (chartAt ℂ q q) r ⊆ (chartAt ℂ q).target`.
Such an `r` exists because `(chartAt ℂ q).target` is open and contains
`chartAt ℂ q q`. -/
private lemma exists_chartBallRadius (q : X) :
    ∃ r > 0, Metric.ball (chartAt ℂ q q) r ⊆ (chartAt ℂ q).target :=
  Metric.isOpen_iff.mp (chartAt ℂ q).open_target _ (mem_chart_target ℂ q)

/-- A specific positive radius with `Metric.ball (chartAt ℂ q q) r ⊆ target`. -/
private noncomputable def chartBallRadius (q : X) : ℝ :=
  Classical.choose (exists_chartBallRadius q)

private lemma chartBallRadius_pos (q : X) : 0 < chartBallRadius q :=
  (Classical.choose_spec (exists_chartBallRadius q)).1

private lemma chartBallRadius_subset_target (q : X) :
    Metric.ball (chartAt ℂ q q) (chartBallRadius q) ⊆ (chartAt ℂ q).target :=
  (Classical.choose_spec (exists_chartBallRadius q)).2

/-- The open set in `X` obtained by pulling back the inner chart-ball
through `chartAt ℂ q`. -/
private noncomputable def chartSourceBallPreimage (q : X) : Set X :=
  (chartAt ℂ q).source ∩
    (chartAt ℂ q) ⁻¹' Metric.ball (chartAt ℂ q q) (chartBallRadius q)

private lemma chartSourceBallPreimage_isOpen (q : X) :
    IsOpen (chartSourceBallPreimage q) :=
  (chartAt ℂ q).isOpen_inter_preimage Metric.isOpen_ball

private lemma chartSourceBallPreimage_mem (q : X) :
    q ∈ chartSourceBallPreimage q := by
  refine ⟨mem_chart_source ℂ q, ?_⟩
  rw [Set.mem_preimage]
  exact Metric.mem_ball_self (chartBallRadius_pos q)

/-! ## Open cover of `standardSimplex2` via `σ`-pullbacks -/

variable (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X)

/-- For each `p ∈ standardSimplex2`, the open set in `Fin 2 → ℝ` obtained
by pulling back `chartSourceBallPreimage (σ.toFun p)` through `σ.toFun`. -/
private noncomputable def sigmaCover (p : Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  σ.toFun ⁻¹' chartSourceBallPreimage (σ.toFun p)

private lemma sigmaCover_isOpen (p : Fin 2 → ℝ) : IsOpen (sigmaCover σ p) :=
  (chartSourceBallPreimage_isOpen (σ.toFun p)).preimage σ.smooth.continuous

private lemma sigmaCover_mem_self (p : Fin 2 → ℝ) : p ∈ sigmaCover σ p :=
  chartSourceBallPreimage_mem (σ.toFun p)

private lemma sigmaCover_covers :
    (standardSimplex2 : Set (Fin 2 → ℝ)) ⊆ ⋃ p, sigmaCover σ p :=
  fun p _hp => Set.mem_iUnion.mpr ⟨p, sigmaCover_mem_self σ p⟩

/-! ## Lebesgue number from the cover -/

/-- Lebesgue's number lemma applied to the `σ`-pullback cover. -/
private lemma exists_lebesgue_for_sigmaCover :
    ∃ δ > 0, ∀ x ∈ (standardSimplex2 : Set (Fin 2 → ℝ)),
      ∃ p, Metric.ball x δ ⊆ sigmaCover σ p :=
  lebesgue_number_lemma_of_metric isCompact_standardSimplex2
    (sigmaCover_isOpen σ) (sigmaCover_covers σ)

/-! ## Depth `n` from `(1/2)^n < δ` -/

private lemma exists_depth_lt (δ : ℝ) (hδ : 0 < δ) :
    ∃ n : ℕ, ((1 : ℝ) / 2)^n < δ :=
  exists_pow_lt_of_lt_one hδ (by norm_num : ((1 : ℝ) / 2) < 1)

/-! ## Parameter image ⊆ closedBall A r under coordinate bound -/

/-- For any vertices `A, B, C` and coordinate-wise pairwise bound `r`,
every point `affineCombo A B C t` with `t ∈ standardSimplex2` lies in
`Metric.closedBall A r`. -/
private lemma dist_affineCombo_first_vertex_le
    {A B C : Fin 2 → ℝ} {r : ℝ}
    (h : Smooth2Simplex.ParameterTriangleBound A B C r)
    {t : Fin 2 → ℝ} (ht : t ∈ standardSimplex2) :
    dist (Smooth2Simplex.affineCombo A B C t) A ≤ r := by
  obtain ⟨hAB, hAC, _⟩ := h
  obtain ⟨ht0, ht1, ht_sum⟩ := ht
  -- Need r ≥ 0 to use dist_pi_le_iff; derive from hAB 0 (LHS is ≥ 0).
  have hr_nn : 0 ≤ r := (abs_nonneg _).trans (hAB 0)
  rw [dist_pi_le_iff hr_nn]
  intro i
  rw [Real.dist_eq]
  -- (affineCombo A B C t) i - A i = t 0 * (B i - A i) + t 1 * (C i - A i)
  have hcalc :
      Smooth2Simplex.affineCombo A B C t i - A i
        = t 0 * (B i - A i) + t 1 * (C i - A i) := by
    simp only [Smooth2Simplex.affineCombo, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  rw [hcalc]
  -- |t 0 (B i - A i) + t 1 (C i - A i)|
  --   ≤ t 0 |B i - A i| + t 1 |C i - A i|     (triangle ineq + |t i| = t i ≥ 0)
  --   ≤ t 0 r + t 1 r = (t 0 + t 1) r ≤ r.
  have habs := hAB i
  have hac := hAC i
  have h_t0r : t 0 * |B i - A i| ≤ t 0 * r :=
    mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact habs) ht0
  have h_t1r : t 1 * |C i - A i| ≤ t 1 * r :=
    mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact hac) ht1
  calc |t 0 * (B i - A i) + t 1 * (C i - A i)|
      ≤ |t 0 * (B i - A i)| + |t 1 * (C i - A i)| := abs_add_le _ _
    _ = |t 0| * |B i - A i| + |t 1| * |C i - A i| := by
        rw [abs_mul, abs_mul]
    _ = t 0 * |B i - A i| + t 1 * |C i - A i| := by
        rw [abs_of_nonneg ht0, abs_of_nonneg ht1]
    _ ≤ t 0 * r + t 1 * r := by linarith
    _ = (t 0 + t 1) * r := by ring
    _ ≤ 1 * r := mul_le_mul_of_nonneg_right ht_sum hr_nn
    _ = r := one_mul r

/-! ## Existence of a chart-containment witness for a single `T`

For any `T ∈ iteratedMidpointList σ n` at sufficient depth, build the
witness. -/

/-- **Witness existence at depth `n`** (the depth being parametric on
the Lebesgue-number `δ` and the `(1/2)^n < δ` choice). -/
private lemma chartContainmentWitness_of_param_in_cover
    {n : ℕ} {T : Smooth2Simplex 𝓘(ℝ, ℂ) X} {δ : ℝ}
    (h_lebesgue : ∀ x ∈ (standardSimplex2 : Set (Fin 2 → ℝ)),
        ∃ p, Metric.ball x δ ⊆ sigmaCover σ p)
    (h_pow_lt : ((1 : ℝ) / 2)^n < δ)
    (hT : T ∈ Smooth2Simplex.iteratedMidpointList σ n) :
    Nonempty (ChartContainmentWitness T) := by
  -- Extract affine form + diameter bound for T.
  obtain ⟨A, B, C, hA, _hB, _hC, h_bound, h_eq⟩ :=
    Smooth2Simplex.iteratedMidpointList_affine_form_with_diam_bound hT
  -- Apply Lebesgue at A.
  obtain ⟨p_anchor, h_ball_sub⟩ := h_lebesgue A hA
  -- p_anchor is a parameter point; σ(p_anchor) is the chart base point.
  refine ⟨⟨σ.toFun p_anchor,
    chartAt ℂ (σ.toFun p_anchor) (σ.toFun p_anchor),
    chartBallRadius (σ.toFun p_anchor),
    chartBallRadius_pos _,
    chartBallRadius_subset_target _,
    ?_, ?_⟩⟩
  · -- image_in_source: T.toFun p ∈ (chartAt _).source for p ∈ Δ²
    intro p hp
    -- T.toFun p = (affineReparam σ A B C).toFun p = σ.toFun (affineCombo A B C p)
    rw [show T.toFun p = σ.toFun (Smooth2Simplex.affineCombo A B C p) from
        congrFun h_eq p]
    -- Show: σ.toFun (affineCombo A B C p) ∈ chart.source.
    -- We have parameter point affineCombo A B C p; show it's in sigmaCover.
    have h_in_ball : Smooth2Simplex.affineCombo A B C p ∈ Metric.ball A δ := by
      rw [Metric.mem_ball]
      calc dist (Smooth2Simplex.affineCombo A B C p) A
          ≤ ((1 : ℝ) / 2)^n :=
            dist_affineCombo_first_vertex_le h_bound hp
        _ < δ := h_pow_lt
    have h_in_cover := h_ball_sub h_in_ball
    -- sigmaCover σ p_anchor = σ⁻¹ (chartSourceBallPreimage (σ p_anchor))
    -- so σ(affineCombo A B C p) ∈ chartSourceBallPreimage (σ p_anchor)
    exact (h_in_cover : _).1
  · -- chart_image_in_ball: (chartAt _) (T.toFun p) ∈ Metric.ball ...
    intro p hp
    rw [show T.toFun p = σ.toFun (Smooth2Simplex.affineCombo A B C p) from
        congrFun h_eq p]
    have h_in_ball : Smooth2Simplex.affineCombo A B C p ∈ Metric.ball A δ := by
      rw [Metric.mem_ball]
      calc dist (Smooth2Simplex.affineCombo A B C p) A
          ≤ ((1 : ℝ) / 2)^n :=
            dist_affineCombo_first_vertex_le h_bound hp
        _ < δ := h_pow_lt
    have h_in_cover := h_ball_sub h_in_ball
    exact (h_in_cover : _).2

/-! ## Headline: `UniformChartContainmentDepth_named X` holds unconditionally -/

/-- **`UniformChartContainmentDepth_named X` is unconditional.**

For every smooth 2-simplex `σ` on a compact connected complex 1-manifold
`X`, there exists `n` such that every sub-simplex in
`iteratedMidpointList σ n` admits a `ChartContainmentWitness`. -/
theorem uniformChartContainmentDepth_named_holds :
    UniformChartContainmentDepth_named X := by
  intro σ
  obtain ⟨δ, hδ_pos, h_lebesgue⟩ := exists_lebesgue_for_sigmaCover σ
  obtain ⟨n, h_pow_lt⟩ := exists_depth_lt δ hδ_pos
  refine ⟨n, ?_⟩
  intro T hT
  exact chartContainmentWitness_of_param_in_cover σ h_lebesgue h_pow_lt hT

/-! ## Downstream corollaries -/

/-- **`HolomorphicComplexBoundaryVanishingHypothesis X` holds unconditionally.** -/
theorem holomorphicComplexBoundaryVanishingHypothesis_holds_unconditional :
    HolomorphicComplexBoundaryVanishingHypothesis X :=
  holomorphicComplexBoundaryVanishingHypothesis_of_uniformChartContainmentDepth
    uniformChartContainmentDepth_named_holds

/-- **`HolomorphicStokesHypothesis X` holds unconditionally.** -/
theorem holomorphicStokesHypothesis_holds_unconditional :
    HolomorphicStokesHypothesis X :=
  holomorphicStokesHypothesis_of_uniformChartContainmentDepth
    uniformChartContainmentDepth_named_holds

/-- **`HolomorphicComponentsCanonicalClosed X` holds unconditionally.** -/
theorem holomorphicComponentsCanonicalClosed_holds_unconditional :
    HolomorphicComponentsCanonicalClosed X :=
  holomorphicComponentsCanonicalClosed_of_uniformChartContainmentDepth
    uniformChartContainmentDepth_named_holds

end JacobianChallenge

end
