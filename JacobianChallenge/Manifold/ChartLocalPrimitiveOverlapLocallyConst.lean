/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartLocalPrimitiveFTCMaxConvexBallChartAt
import JacobianChallenge.Manifold.ChartLocalPrimitiveSmoothExtMaxConvexBallChartAt
import JacobianChallenge.Manifold.ConvexBallChartAtMaximalAtlas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

set_option linter.unusedSectionVars false

/-! # Local constancy of `chartLocalPrimitiveExtendMax` difference on overlap

Second file of the étale-space arc (Alt B of `AUDIT_LOOP_PERIOD_VANISHES.md`).
Proves the chart-transition cocycle-vanishing lemma needed to upgrade
`proj : EtalePrimitives om → X` from continuous (Chip 1) to a local
homeomorphism (next chip).

## Statement

For two chart-ball centers `y, y' : X` on a compact connected complex
1-manifold X, the difference

```
D(x) := chartLocalPrimitiveExtendMax (convexBallChartAt y) … y … om x
      − chartLocalPrimitiveExtendMax (convexBallChartAt y') … y' … om x
```

is locally constant on the overlap
`(convexBallChartAt y).source ∩ (convexBallChartAt y').source` —
i.e. at each `x₀` in the overlap, there is an open neighborhood `U` of
`x₀` (contained in the overlap) on which `D` equals its value at `x₀`.

## Proof outline

1. Cascade FTC: `chartLocalPrimitiveSmoothExtMax_convexBallChartAt y om`
   gives smoothness and `chartLocalPrimitiveFTCMax_convexBallChartAt y om`
   gives `mfderiv F_y = om.eval` on the chart-ball source.
2. By `mfderiv_sub`, `D := F_y − F_y'` has `mfderiv D x = 0` on the
   overlap.
3. Pull back through the chart at `x₀`: the function
   `D ∘ (chartAt ℂ x₀).symm : ℂ → ℂ` is `DifferentiableAt` every
   `z` in `(chartAt ℂ x₀) '' (overlap ∩ source_{x₀})`, with `fderiv = 0`.
   Uses `mfderiv_comp` for the chain rule and `mfderiv_eq_fderiv`
   (vector-space coincidence on `ℂ → ℂ`).
4. Find a Euclidean ball `B := ball ((chartAt ℂ x₀) x₀) ε` contained in
   that chart-image (open). `B` is convex (hence preconnected).
5. By `IsOpen.is_const_of_fderiv_eq_zero` on `B`, `D ∘ (chartAt ℂ x₀).symm`
   is constant on `B`.
6. The desired `U := (chartAt ℂ x₀).source ∩ overlap ∩
   (chartAt ℂ x₀) ⁻¹' B` is open, contains `x₀`, lies in the overlap,
   and `D` is constant on it via the chart-symm identity.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set Metric

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Total chart-local primitive at a chart-ball center -/

/-- **Chart-local primitive of `om` at chart-ball center `y`.** Wraps the
unconditional `chartLocalPrimitiveExtendMax (convexBallChartAt y) …` so
that downstream lemmas can refer to it without re-listing the proof
terms. -/
noncomputable def localPrimitiveAtBallCenter
    (om : HolomorphicOneForm X) (y : X) : X → ℂ :=
  chartLocalPrimitiveExtendMax (convexBallChartAt y)
    (convexBallChartAt_mem_maximalAtlas_real y)
    (convexBallChartAt_target_convex y) y
    (convexBallChartAt_x_mem_source y) om

/-- **`localPrimitiveAtBallCenter` is `ContMDiffOn ω` on its chart-ball
source.** Direct restatement of the cascade headline. -/
lemma localPrimitiveAtBallCenter_contMDiffOn (om : HolomorphicOneForm X) (y : X) :
    ContMDiffOn (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (localPrimitiveAtBallCenter om y) (convexBallChartAt y).source :=
  chartLocalPrimitiveSmoothExtMax_convexBallChartAt y om

/-- **`localPrimitiveAtBallCenter` is `MDifferentiableAt` every point of
its chart-ball source.** -/
lemma localPrimitiveAtBallCenter_mdifferentiableAt
    (om : HolomorphicOneForm X) (y x : X)
    (hx : x ∈ (convexBallChartAt y).source) :
    MDifferentiableAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
      (localPrimitiveAtBallCenter om y) x := by
  have h_open : IsOpen ((convexBallChartAt y).source : Set X) :=
    (convexBallChartAt y).open_source
  have h_at : ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (localPrimitiveAtBallCenter om y) x :=
    (localPrimitiveAtBallCenter_contMDiffOn om y x hx).contMDiffAt
      (h_open.mem_nhds hx)
  exact h_at.mdifferentiableAt (by decide)

/-- **mfderiv of `localPrimitiveAtBallCenter` equals `om.eval`.** Restatement
of the cascade FTC. -/
lemma mfderiv_localPrimitiveAtBallCenter
    (om : HolomorphicOneForm X) (y x : X)
    (hx : x ∈ (convexBallChartAt y).source) :
    mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (localPrimitiveAtBallCenter om y) x
      = om.eval x :=
  (chartLocalPrimitiveFTCMax_convexBallChartAt y om x hx).symm

/-- **The difference `F_y − F_{y'}` has zero mfderiv on the overlap.** -/
lemma mfderiv_localPrimitive_diff_eq_zero
    (om : HolomorphicOneForm X) (y y' x : X)
    (hx_y : x ∈ (convexBallChartAt y).source)
    (hx_y' : x ∈ (convexBallChartAt y').source) :
    mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (localPrimitiveAtBallCenter om y - localPrimitiveAtBallCenter om y') x
      = 0 := by
  have h_y := localPrimitiveAtBallCenter_mdifferentiableAt om y x hx_y
  have h_y' := localPrimitiveAtBallCenter_mdifferentiableAt om y' x hx_y'
  rw [mfderiv_sub h_y h_y',
      mfderiv_localPrimitiveAtBallCenter om y x hx_y,
      mfderiv_localPrimitiveAtBallCenter om y' x hx_y']
  exact sub_self _

/-! ## Chart pullback differentiability and fderiv vanishing -/

/-- **The chart at `x₀` symm-side is `MDifferentiableAt` every point of
its target.** Direct from `contMDiffOn_of_mem_maximalAtlas` applied to
`(chartAt ℂ x₀).symm`. -/
private lemma chartAt_symm_mdifferentiableAt
    (x₀ : X) (z : ℂ) (hz : z ∈ (chartAt ℂ x₀).target) :
    MDifferentiableAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
      ((chartAt ℂ x₀).symm : ℂ → X) z := by
  have h_smoothOn : ContMDiffOn (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      ((chartAt ℂ x₀).symm : ℂ → X) (chartAt ℂ x₀).target :=
    contMDiffOn_chart_symm
  have h_open : IsOpen ((chartAt ℂ x₀).target : Set ℂ) :=
    (chartAt ℂ x₀).open_target
  exact ((h_smoothOn z hz).contMDiffAt
    (h_open.mem_nhds hz)).mdifferentiableAt (by decide)

/-- **Chart pullback of `D` has zero `mfderiv` (= `fderiv`) at every
chart-image of a point in `source_{x₀} ∩ overlap`.** -/
lemma fderiv_chartPullback_localPrimitive_diff_eq_zero
    (om : HolomorphicOneForm X) (y y' x₀ x : X)
    (hx_at₀ : x ∈ (chartAt ℂ x₀).source)
    (hx_y : x ∈ (convexBallChartAt y).source)
    (hx_y' : x ∈ (convexBallChartAt y').source) :
    fderiv ℂ
        ((localPrimitiveAtBallCenter om y - localPrimitiveAtBallCenter om y')
          ∘ (chartAt ℂ x₀).symm)
        ((chartAt ℂ x₀) x) = 0 := by
  set D : X → ℂ :=
    localPrimitiveAtBallCenter om y - localPrimitiveAtBallCenter om y'
    with hD_def
  -- Chart-image of x is in chart target.
  have h_chart_image_mem :
      (chartAt ℂ x₀) x ∈ (chartAt ℂ x₀).target :=
    (chartAt ℂ x₀).map_source hx_at₀
  have h_symm_chart_eq : (chartAt ℂ x₀).symm ((chartAt ℂ x₀) x) = x :=
    (chartAt ℂ x₀).left_inv hx_at₀
  have h_symm_mdiff :
      MDifferentiableAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        ((chartAt ℂ x₀).symm : ℂ → X) ((chartAt ℂ x₀) x) :=
    chartAt_symm_mdifferentiableAt x₀ ((chartAt ℂ x₀) x) h_chart_image_mem
  have h_D_mdiff_at_x :
      MDifferentiableAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) D x := by
    rw [hD_def]
    exact (localPrimitiveAtBallCenter_mdifferentiableAt om y x hx_y).sub
      (localPrimitiveAtBallCenter_mdifferentiableAt om y' x hx_y')
  have h_D_mdiff :
      MDifferentiableAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) D
        ((chartAt ℂ x₀).symm ((chartAt ℂ x₀) x)) := by
    rw [h_symm_chart_eq]; exact h_D_mdiff_at_x
  have h_mfderiv_D_zero :
      mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) D x = 0 := by
    rw [hD_def]
    exact mfderiv_localPrimitive_diff_eq_zero om y y' x hx_y hx_y'
  -- Chain rule.
  have h_chain :
      mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (D ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x)
        = (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) D
              ((chartAt ℂ x₀).symm ((chartAt ℂ x₀) x))).comp
            (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
              ((chartAt ℂ x₀).symm : ℂ → X) ((chartAt ℂ x₀) x)) :=
    mfderiv_comp ((chartAt ℂ x₀) x) h_D_mdiff h_symm_mdiff
  have h_inner_zero :
      mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) D
          ((chartAt ℂ x₀).symm ((chartAt ℂ x₀) x)) = 0 := by
    rw [h_symm_chart_eq]; exact h_mfderiv_D_zero
  have h_mfderiv_zero :
      mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (D ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x)
        = 0 := by
    rw [h_chain, h_inner_zero]
    exact ContinuousLinearMap.zero_comp _
  -- Bridge to fderiv.
  have h_fderiv_eq :
      fderiv ℂ (D ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x)
        = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (D ∘ (chartAt ℂ x₀).symm)
            ((chartAt ℂ x₀) x) :=
    (mfderiv_eq_fderiv (f := D ∘ (chartAt ℂ x₀).symm)
      (x := (chartAt ℂ x₀) x)).symm
  rw [h_fderiv_eq]
  exact h_mfderiv_zero

/-- **Chart pullback of `D` is `DifferentiableAt` every chart-image of a
point in `source_{x₀} ∩ overlap`.** -/
lemma differentiableAt_chartPullback_localPrimitive_diff
    (om : HolomorphicOneForm X) (y y' x₀ x : X)
    (hx_at₀ : x ∈ (chartAt ℂ x₀).source)
    (hx_y : x ∈ (convexBallChartAt y).source)
    (hx_y' : x ∈ (convexBallChartAt y').source) :
    DifferentiableAt ℂ
      ((localPrimitiveAtBallCenter om y - localPrimitiveAtBallCenter om y')
        ∘ (chartAt ℂ x₀).symm)
      ((chartAt ℂ x₀) x) := by
  set D : X → ℂ :=
    localPrimitiveAtBallCenter om y - localPrimitiveAtBallCenter om y'
  have h_chart_image_mem :
      (chartAt ℂ x₀) x ∈ (chartAt ℂ x₀).target :=
    (chartAt ℂ x₀).map_source hx_at₀
  have h_symm_chart_eq : (chartAt ℂ x₀).symm ((chartAt ℂ x₀) x) = x :=
    (chartAt ℂ x₀).left_inv hx_at₀
  have h_symm_mdiff :
      MDifferentiableAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        ((chartAt ℂ x₀).symm : ℂ → X) ((chartAt ℂ x₀) x) :=
    chartAt_symm_mdifferentiableAt x₀ ((chartAt ℂ x₀) x) h_chart_image_mem
  have h_D_mdiff_at_x :
      MDifferentiableAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) D x :=
    (localPrimitiveAtBallCenter_mdifferentiableAt om y x hx_y).sub
      (localPrimitiveAtBallCenter_mdifferentiableAt om y' x hx_y')
  have h_D_mdiff :
      MDifferentiableAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) D
        ((chartAt ℂ x₀).symm ((chartAt ℂ x₀) x)) := by
    rw [h_symm_chart_eq]; exact h_D_mdiff_at_x
  have h_comp_mdiff :
      MDifferentiableAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (D ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x) :=
    h_D_mdiff.comp ((chartAt ℂ x₀) x) h_symm_mdiff
  exact mdifferentiableAt_iff_differentiableAt.mp h_comp_mdiff

/-! ## Main theorem: local constancy on the overlap -/

/-- **Local constancy of `D = F_y − F_{y'}` on the overlap.** For every
`x₀` in `(convexBallChartAt y).source ∩ (convexBallChartAt y').source`,
there is an open neighborhood `U` of `x₀` (contained in the overlap) on
which `D` is constant equal to `D(x₀)`. -/
theorem chartLocalPrimitive_diff_locallyConstant_at_overlap
    (om : HolomorphicOneForm X) (y y' x₀ : X)
    (hx₀_y : x₀ ∈ (convexBallChartAt y).source)
    (hx₀_y' : x₀ ∈ (convexBallChartAt y').source) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
      U ⊆ (convexBallChartAt y).source ∧
      U ⊆ (convexBallChartAt y').source ∧
      ∀ x ∈ U,
        localPrimitiveAtBallCenter om y x - localPrimitiveAtBallCenter om y' x
        = localPrimitiveAtBallCenter om y x₀
            - localPrimitiveAtBallCenter om y' x₀ := by
  set D : X → ℂ :=
    localPrimitiveAtBallCenter om y - localPrimitiveAtBallCenter om y'
    with hD_def
  -- Open neighborhoods.
  have hOpen_y : IsOpen ((convexBallChartAt y).source : Set X) :=
    (convexBallChartAt y).open_source
  have hOpen_y' : IsOpen ((convexBallChartAt y').source : Set X) :=
    (convexBallChartAt y').open_source
  have hOpen_x₀ : IsOpen ((chartAt ℂ x₀).source : Set X) :=
    (chartAt ℂ x₀).open_source
  have hx₀_chartAt : x₀ ∈ (chartAt ℂ x₀).source := mem_chart_source ℂ x₀
  -- `s` := chart-source ∩ overlap.
  set s : Set X :=
    (chartAt ℂ x₀).source ∩ (convexBallChartAt y).source
      ∩ (convexBallChartAt y').source
    with hs_def
  have hs_open : IsOpen s := (hOpen_x₀.inter hOpen_y).inter hOpen_y'
  have hx₀_in_s : x₀ ∈ s := ⟨⟨hx₀_chartAt, hx₀_y⟩, hx₀_y'⟩
  have hs_sub_chartAt : s ⊆ (chartAt ℂ x₀).source := fun _ hx => hx.1.1
  have hs_sub_y : s ⊆ (convexBallChartAt y).source := fun _ hx => hx.1.2
  have hs_sub_y' : s ⊆ (convexBallChartAt y').source := fun _ hx => hx.2
  -- Image of s under the chart at x₀: open in ℂ.
  set s_im : Set ℂ := (chartAt ℂ x₀) '' s with hs_im_def
  have hs_im_open : IsOpen s_im :=
    (chartAt ℂ x₀).isOpen_image_of_subset_source hs_open hs_sub_chartAt
  have hp₀_in_im : (chartAt ℂ x₀) x₀ ∈ s_im := ⟨x₀, hx₀_in_s, rfl⟩
  -- Euclidean ball around (chart x₀).
  obtain ⟨ε, hε_pos, hε_sub⟩ :=
    Metric.isOpen_iff.mp hs_im_open _ hp₀_in_im
  set B : Set ℂ := Metric.ball ((chartAt ℂ x₀) x₀) ε with hB_def
  have hB_open : IsOpen B := Metric.isOpen_ball
  have hB_preconn : IsPreconnected B := (convex_ball _ _).isPreconnected
  have hp₀_in_B : (chartAt ℂ x₀) x₀ ∈ B := Metric.mem_ball_self hε_pos
  have hB_sub_im : B ⊆ s_im := hε_sub
  -- For each z ∈ B, chart.symm z is some x ∈ s.
  have h_symm_in_s : ∀ z ∈ B, (chartAt ℂ x₀).symm z ∈ s := by
    intro z hz
    obtain ⟨x, hx_s, hx_eq⟩ := hB_sub_im hz
    have h_symm : (chartAt ℂ x₀).symm z = x := by
      rw [← hx_eq]; exact (chartAt ℂ x₀).left_inv (hs_sub_chartAt hx_s)
    rw [h_symm]; exact hx_s
  -- DifferentiableOn ℂ D̃ B.
  have hDiff_D_pullback :
      DifferentiableOn ℂ (D ∘ (chartAt ℂ x₀).symm) B := by
    intro z hz
    have hz_im : z ∈ s_im := hB_sub_im hz
    obtain ⟨x, hx_s, hx_eq⟩ := hz_im
    have h_eq_chart : z = (chartAt ℂ x₀) x := hx_eq.symm
    rw [h_eq_chart]
    exact (differentiableAt_chartPullback_localPrimitive_diff om y y' x₀ x
      (hs_sub_chartAt hx_s) (hs_sub_y hx_s)
      (hs_sub_y' hx_s)).differentiableWithinAt
  -- fderiv D̃ = 0 on B.
  have hFderiv_zero : ∀ z ∈ B,
      fderiv ℂ (D ∘ (chartAt ℂ x₀).symm) z = 0 := by
    intro z hz
    have hz_im : z ∈ s_im := hB_sub_im hz
    obtain ⟨x, hx_s, hx_eq⟩ := hz_im
    have h_eq_chart : z = (chartAt ℂ x₀) x := hx_eq.symm
    rw [h_eq_chart]
    exact fderiv_chartPullback_localPrimitive_diff_eq_zero om y y' x₀ x
      (hs_sub_chartAt hx_s) (hs_sub_y hx_s) (hs_sub_y' hx_s)
  -- D̃ constant on B by IsOpen.is_const_of_fderiv_eq_zero.
  have hD_pullback_const : ∀ z ∈ B,
      (D ∘ (chartAt ℂ x₀).symm) z = (D ∘ (chartAt ℂ x₀).symm)
        ((chartAt ℂ x₀) x₀) := fun z hz =>
    hB_open.is_const_of_fderiv_eq_zero hB_preconn hDiff_D_pullback
      (fun w hw => hFderiv_zero w hw) hz hp₀_in_B
  -- Construct U.
  set U : Set X := s ∩ (chartAt ℂ x₀) ⁻¹' B with hU_def
  have hU_open : IsOpen U := by
    have h_pre :
        IsOpen ((chartAt ℂ x₀).source ∩ (chartAt ℂ x₀) ⁻¹' B) :=
      (chartAt ℂ x₀).continuousOn.isOpen_inter_preimage hOpen_x₀ hB_open
    have h_eq :
        U = s ∩ ((chartAt ℂ x₀).source ∩ (chartAt ℂ x₀) ⁻¹' B) := by
      ext w
      refine ⟨?_, ?_⟩
      · rintro ⟨hw_s, hw_pre⟩
        exact ⟨hw_s, hs_sub_chartAt hw_s, hw_pre⟩
      · rintro ⟨hw_s, _, hw_pre⟩
        exact ⟨hw_s, hw_pre⟩
    rw [h_eq]
    exact hs_open.inter h_pre
  have hx₀_in_U : x₀ ∈ U := by
    refine ⟨hx₀_in_s, ?_⟩
    show (chartAt ℂ x₀) x₀ ∈ B
    exact hp₀_in_B
  have hU_sub_y : U ⊆ (convexBallChartAt y).source := fun _ hx => hs_sub_y hx.1
  have hU_sub_y' : U ⊆ (convexBallChartAt y').source := fun _ hx => hs_sub_y' hx.1
  refine ⟨U, hU_open, hx₀_in_U, hU_sub_y, hU_sub_y', ?_⟩
  intro x hx
  -- Show D x = D x₀.
  have hx_in_s : x ∈ s := hx.1
  have hx_chart_in_B : (chartAt ℂ x₀) x ∈ B := hx.2
  have h_symm_x : (chartAt ℂ x₀).symm ((chartAt ℂ x₀) x) = x :=
    (chartAt ℂ x₀).left_inv (hs_sub_chartAt hx_in_s)
  have h_symm_x₀ : (chartAt ℂ x₀).symm ((chartAt ℂ x₀) x₀) = x₀ :=
    (chartAt ℂ x₀).left_inv hx₀_chartAt
  -- D x = D̃ (chart x), D x₀ = D̃ (chart x₀).
  have h_D_x : D x = (D ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x) := by
    show D x = D ((chartAt ℂ x₀).symm ((chartAt ℂ x₀) x))
    rw [h_symm_x]
  have h_D_x₀ : D x₀ = (D ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) := by
    show D x₀ = D ((chartAt ℂ x₀).symm ((chartAt ℂ x₀) x₀))
    rw [h_symm_x₀]
  have h_eq : (D ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x)
              = (D ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) :=
    hD_pullback_const _ hx_chart_in_B
  -- Convert D-statement to localPrimitive-difference statement.
  change localPrimitiveAtBallCenter om y x - localPrimitiveAtBallCenter om y' x
      = localPrimitiveAtBallCenter om y x₀ - localPrimitiveAtBallCenter om y' x₀
  have h_dval : D x = D x₀ := h_D_x.trans (h_eq.trans h_D_x₀.symm)
  -- D x and D x₀ unfold to the difference.
  simpa [hD_def, Pi.sub_apply] using h_dval

end JacobianChallenge

end
