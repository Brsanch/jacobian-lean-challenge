/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathTubularBump
import JacobianChallenge.Manifold.LoopFactorsThroughVectorSpaceFromChartN
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Discharge of `SmoothLoopChartNPullbackExistsHypothesis`

**Headline.** `SmoothLoopChartNPullbackExistsHypothesis p₀` holds
**unconditionally** for any basepoint `p₀ : RiemannSphere`: every smooth
loop `γ : SmoothPath 𝓘(ℝ, ℂ) RS` based at `p₀` whose image lies in
`chartN.source` admits a smooth chart-pullback `γ' : SmoothPath 𝓘(ℝ, ℂ) ℂ`
with `γ = SmoothPath.push chartN.symm chartN_symm_contMDiff.of_le γ'`.

## Construction

1. By openness of `chartN.source` and continuity of `γ.ambient`, the
   preimage `U := γ.ambient⁻¹(chartN.source)` is open and contains `[0, 1]`.

2. By `exists_tubular_delta`, there is `δ_outer > 0` with
   `Ioo (-δ_outer) (1 + δ_outer) ⊆ U`.

3. Set `δ := δ_outer / 2`. The closed `Icc (-δ, 1 + δ)` is then
   strictly inside the open `Ioo (-δ_outer, 1 + δ_outer)`.

4. Define `g'(t) := tubularBump δ t * chartN (γ.ambient t)`.

5. **Smoothness of `g'`** via an open cover:
   - On `A := Ioo (-δ_outer, 1 + δ_outer)`: both factors are smooth
     (bump smooth, `chartN ∘ γ.ambient` smooth because `γ.ambient`
     lands in `chartN.source` on `A`).
   - On `B := Iio (-δ) ∪ Ioi (1 + δ)`: `tubularBump δ = 0` (by the
     endpoint lemmas), so `g' = 0`, smooth.
   - `A ∪ B = ℝ` since `Icc (-δ, 1 + δ) ⊆ A`.

6. `g'` agrees with `chartN ∘ γ.toPath` on `unitInterval` because
   `tubularBump δ ≡ 1` on `[0, 1]` and `γ.ambient = γ.toPath` on
   `unitInterval`.

7. Build `γ' : SmoothPath 𝓘(ℝ, ℂ) ℂ` with `src := chartN γ.src`,
   `tgt := chartN γ.tgt`, `toPath` from `g'` restricted to `unitInterval`,
   and `smooth := ⟨g', smooth, agreement⟩`.

8. `γ'` is a loop (`γ'.src = γ'.tgt`) because `γ.src = γ.tgt` (loop
   hypothesis at p₀).

9. `γ = push chartN.symm γ'` via `SmoothPath.ext`: matching `src`,
   `tgt`, and pointwise `toPath` via `chartN.symm ∘ chartN = id` on
   `chartN.source`.

No `sorry`, no `axiom`. -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-! ## Smoothness of `chartN.toFun` on its source -/

/-- `chartN : RS → ℂ` is `ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤` on its source. -/
lemma chartN_contMDiffOn :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤
      (chartN : RiemannSphere → ℂ) chartN.source := by
  have h_chart_eq : chartAt ℂ ((0 : ℂ) : RiemannSphere) = chartN := chartAt'_coe 0
  have h_on : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤
      (chartAt ℂ ((0 : ℂ) : RiemannSphere))
      (chartAt ℂ ((0 : ℂ) : RiemannSphere)).source :=
    contMDiffOn_chart
  rw [h_chart_eq] at h_on
  exact h_on

/-! ## The chart-N pullback construction

The discharge proceeds by constructing γ' explicitly using
`tubularBump` and proving smoothness via the two-region open cover. -/

variable (p₀ : RiemannSphere)

/-- **Discharge of `SmoothLoopChartNPullbackExistsHypothesis p₀`** —
holds for every basepoint `p₀ ∈ RiemannSphere`. -/
theorem smoothLoopChartNPullbackExistsHypothesis_holds :
    SmoothLoopChartNPullbackExistsHypothesis p₀ := by
  intro γ h_src h_tgt h_in_chartN
  -- Step 1: U := γ.ambient⁻¹ chartN.source is open and contains [0, 1].
  set U : Set ℝ := γ.ambient ⁻¹' chartN.source with hU_def
  have hU_open : IsOpen U := chartN.open_source.preimage γ.ambient_contMDiff.continuous
  have hU_Icc_sub : Set.Icc (0 : ℝ) 1 ⊆ U := by
    intro t ht
    rw [hU_def, Set.mem_preimage]
    -- γ.ambient t = γ.toPath ⟨t, ht⟩ on unitInterval; image is in chartN.source.
    have ht_unit : t ∈ unitInterval := ht
    have h_amb := γ.ambient_eq_on_unitInterval ⟨t, ht_unit⟩
    rw [show (((⟨t, ht_unit⟩ : unitInterval) : ℝ)) = t from rfl] at h_amb
    rw [h_amb]
    exact h_in_chartN ⟨t, ht_unit⟩
  -- Step 2: tubular-delta existence.
  obtain ⟨δ_outer, hδ_outer_pos, hδ_outer_sub⟩ := exists_tubular_delta hU_open hU_Icc_sub
  -- Step 3: δ := δ_outer / 2.
  set δ : ℝ := δ_outer / 2 with hδ_def
  have hδ_pos : 0 < δ := by rw [hδ_def]; linarith
  have hδ_lt_outer : δ < δ_outer := by rw [hδ_def]; linarith
  -- Icc [-δ, 1+δ] ⊊ Ioo (-δ_outer, 1+δ_outer).
  have h_Icc_sub_Ioo : Set.Icc (-δ) (1 + δ) ⊆ Set.Ioo (-δ_outer) (1 + δ_outer) := by
    intro t ⟨h1, h2⟩
    constructor <;> linarith
  -- Step 4: define g' : ℝ → ℂ.
  set g' : ℝ → ℂ := fun t => (tubularBump δ t : ℂ) * chartN (γ.ambient t) with hg'_def
  -- Smoothness of g'.
  have h_bump_smooth : ContDiff ℝ ∞ (tubularBump δ) := contDiff_tubularBump hδ_pos
  -- chartN ∘ γ.ambient is ContMDiff on the open set Ioo (-δ_outer, 1+δ_outer).
  -- First, γ.ambient maps Ioo (-δ_outer, 1+δ_outer) into chartN.source (via U).
  have h_amb_in_source : ∀ t ∈ Set.Ioo (-δ_outer) (1 + δ_outer),
      γ.ambient t ∈ chartN.source :=
    fun t ht => hδ_outer_sub ht
  -- ContMDiffOn (chartN ∘ γ.ambient) (Ioo (-δ_outer, 1+δ_outer)) at regularity ∞.
  have h_chartN_inf : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (chartN : RiemannSphere → ℂ) chartN.source :=
    chartN_contMDiffOn.of_le (le_top)
  have h_amb_on : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ γ.ambient
      (Set.Ioo (-δ_outer) (1 + δ_outer)) :=
    γ.ambient_contMDiff.contMDiffOn
  have h_amb_maps : Set.MapsTo γ.ambient
      (Set.Ioo (-δ_outer) (1 + δ_outer)) chartN.source := h_amb_in_source
  have h_comp_on : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
      (fun t => (chartN : RiemannSphere → ℂ) (γ.ambient t))
      (Set.Ioo (-δ_outer) (1 + δ_outer)) :=
    h_chartN_inf.comp h_amb_on h_amb_maps
  -- Convert h_comp_on to ContDiffOn since target is ℂ (a normed space).
  have h_comp_contDiffOn : ContDiffOn ℝ ∞
      (fun t => (chartN : RiemannSphere → ℂ) (γ.ambient t))
      (Set.Ioo (-δ_outer) (1 + δ_outer)) := by
    rw [contMDiffOn_iff_contDiffOn] at h_comp_on
    exact h_comp_on
  -- g' on A = Ioo (-δ_outer, 1+δ_outer): smooth (product of smooth).
  have h_g'_A : ContDiffOn ℝ ∞ g' (Set.Ioo (-δ_outer) (1 + δ_outer)) := by
    have h_bump_on : ContDiffOn ℝ ∞ (tubularBump δ)
        (Set.Ioo (-δ_outer) (1 + δ_outer)) := h_bump_smooth.contDiffOn
    rw [hg'_def]
    -- ofReal : ℝ → ℂ is C^∞ (as a continuous linear map).
    have h_ofReal_contDiff : ContDiff ℝ ∞ (fun r : ℝ => (r : ℂ)) :=
      Complex.ofRealCLM.contDiff
    have h_bump_C : ContDiffOn ℝ ∞ (fun t : ℝ => (tubularBump δ t : ℂ))
        (Set.Ioo (-δ_outer) (1 + δ_outer)) :=
      h_ofReal_contDiff.contDiffOn.comp h_bump_on (Set.mapsTo_univ _ _)
    exact h_bump_C.mul h_comp_contDiffOn
  -- g' on B = Iio (-δ) ∪ Ioi (1+δ): zero, hence smooth.
  have h_bump_zero_iio : ∀ t ∈ Set.Iio (-δ), tubularBump δ t = 0 := by
    intro t ht
    exact tubularBump_eq_zero_of_le_neg_delta hδ_pos (le_of_lt ht)
  have h_bump_zero_ioi : ∀ t ∈ Set.Ioi (1 + δ), tubularBump δ t = 0 := by
    intro t ht
    exact tubularBump_eq_zero_of_ge_one_add_delta hδ_pos (le_of_lt ht)
  have h_g'_B : ContDiffOn ℝ ∞ g'
      (Set.Iio (-δ) ∪ Set.Ioi (1 + δ)) := by
    have h_eq_zero : Set.EqOn g' 0 (Set.Iio (-δ) ∪ Set.Ioi (1 + δ)) := by
      intro t ht
      show g' t = (0 : ℝ → ℂ) t
      rw [hg'_def]
      show (tubularBump δ t : ℂ) * chartN (γ.ambient t) = (0 : ℂ)
      rcases ht with ht | ht
      · rw [h_bump_zero_iio t ht]
        push_cast; ring
      · rw [h_bump_zero_ioi t ht]
        push_cast; ring
    have h_g'_eq_zero : ∀ t ∈ Set.Iio (-δ) ∪ Set.Ioi (1 + δ), g' t = 0 := by
      intro t ht
      exact h_eq_zero ht
    have h_zero_smooth : ContDiffOn ℝ ∞ (fun _ : ℝ => (0 : ℂ))
        (Set.Iio (-δ) ∪ Set.Ioi (1 + δ)) := contDiff_const.contDiffOn
    exact h_zero_smooth.congr (fun t ht => h_g'_eq_zero t ht)
  -- A ∪ B = ℝ.
  have h_AB_cover : Set.Ioo (-δ_outer) (1 + δ_outer) ∪
      (Set.Iio (-δ) ∪ Set.Ioi (1 + δ)) = Set.univ := by
    ext t
    simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Iio, Set.mem_Ioi, Set.mem_univ, iff_true]
    by_cases h_in_Icc : t ∈ Set.Icc (-δ) (1 + δ)
    · left
      exact h_Icc_sub_Ioo h_in_Icc
    · right
      rw [Set.mem_Icc, not_and_or] at h_in_Icc
      rcases h_in_Icc with h | h
      · left; push Not at h; exact h
      · right; push Not at h; exact h
  -- Open sets.
  have h_A_open : IsOpen (Set.Ioo (-δ_outer) (1 + δ_outer)) := isOpen_Ioo
  have h_B_open : IsOpen (Set.Iio (-δ) ∪ Set.Ioi (1 + δ)) :=
    isOpen_Iio.union isOpen_Ioi
  -- Glue.
  have h_g'_smooth : ContDiff ℝ ∞ g' := by
    have h_on_union : ContDiffOn ℝ ∞ g'
        (Set.Ioo (-δ_outer) (1 + δ_outer) ∪ (Set.Iio (-δ) ∪ Set.Ioi (1 + δ))) :=
      ContDiffOn.union_of_isOpen h_g'_A h_g'_B h_A_open h_B_open
    rw [h_AB_cover] at h_on_union
    rwa [contDiffOn_univ] at h_on_union
  -- g' matches chartN ∘ γ.toPath on unitInterval.
  have h_g'_match : ∀ t : unitInterval, g' t.val = chartN (γ.toPath t) := by
    intro t
    have ht_Icc : t.val ∈ Set.Icc (0 : ℝ) 1 := t.property
    have h_bump_one : tubularBump δ t.val = 1 :=
      tubularBump_eq_one_of_mem_Icc hδ_pos ht_Icc
    have h_amb_eq := γ.ambient_eq_on_unitInterval t
    show (tubularBump δ t.val : ℂ) * chartN (γ.ambient t.val) = chartN (γ.toPath t)
    rw [h_bump_one, h_amb_eq]
    push_cast; ring
  -- Build γ'.toPath as a continuous Path from chartN(γ.src) to chartN(γ.tgt).
  have h_chartN_src : (γ.src : RiemannSphere) ∈ chartN.source := by
    have := h_in_chartN ⟨0, ⟨le_refl 0, zero_le_one⟩⟩
    convert this using 1
    exact (γ.toPath.source').symm
  have h_chartN_tgt : (γ.tgt : RiemannSphere) ∈ chartN.source := by
    have := h_in_chartN ⟨1, ⟨zero_le_one, le_refl 1⟩⟩
    convert this using 1
    exact (γ.toPath.target').symm
  -- The pullback Path.
  let toPath_pullback : Path (chartN γ.src) (chartN γ.tgt) :=
    { toFun := fun t : unitInterval => chartN (γ.toPath t)
      continuous_toFun := by
        have h_amb_cont : Continuous γ.toPath.toFun :=
          γ.toPath.continuous_toFun
        have h_chartN_cont_on : ContinuousOn chartN chartN.source :=
          chartN.continuousOn_toFun
        have h_compose : Continuous (fun t : unitInterval =>
            chartN (γ.toPath t)) := by
          refine ContinuousOn.comp_continuous h_chartN_cont_on
            γ.toPath.continuous_toFun ?_
          intro t
          exact h_in_chartN t
        exact h_compose
      source' := by simp
      target' := by simp }
  -- Build γ' as a SmoothPath 𝓘(ℝ, ℂ) ℂ.
  let γ' : SmoothPath 𝓘(ℝ, ℂ) ℂ :=
    { src := chartN γ.src
      tgt := chartN γ.tgt
      toPath := toPath_pullback
      smooth := ⟨g', h_g'_smooth.contMDiff, fun t => (h_g'_match t).symm ▸ rfl⟩ }
  refine ⟨γ', ?_, ?_⟩
  · -- γ'.src = γ'.tgt under the loop hypothesis γ.src = γ.tgt at p₀.
    show chartN γ.src = chartN γ.tgt
    rw [h_src, h_tgt]
  · -- γ = push chartN.symm γ' via SmoothPath.ext.
    apply SmoothPath.ext
    · -- src: γ.src vs (push chartN.symm γ').src = chartN.symm (chartN γ.src).
      show γ.src = chartN.symm (chartN γ.src)
      exact (chartN.left_inv h_chartN_src).symm
    · show γ.tgt = chartN.symm (chartN γ.tgt)
      exact (chartN.left_inv h_chartN_tgt).symm
    · -- toPath pointwise.
      intro t
      have h_chartN_t : γ.toPath t ∈ chartN.source := h_in_chartN t
      show γ.toPath t = chartN.symm (chartN (γ.toPath t))
      exact (chartN.left_inv h_chartN_t).symm

end RiemannSphere

end JacobianChallenge
