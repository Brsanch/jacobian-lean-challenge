/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartContainedSmooth2Simplex
import JacobianChallenge.Manifold.SmoothPathReverse
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # `ChartContainedSmooth2Simplex` constructor from per-face chart-containment

The `ChartContainedSmooth2Simplex X` structure bundles a
`Smooth2Simplex 𝓘(ℝ, ℂ) X` with an explicit `ChartContainedClosedLoop`
on its boundary loop. This file actualises that bundle: from raw
per-face chart-containment data on `[0, 1]`, build the
`ChartContainedClosedLoop` directly, threading through the
`concatAmbient` and `reverseAmbient` bookkeeping.

**Key identity.** For `concat γ δ h`, the chosen ambient on `[0, 1]`
equals `γ.concatAmbient δ` evaluated there:

  `(γ.concat δ h).ambient t = γ.concatAmbient δ t`  for `t ∈ [0, 1]`

via `ambient_eq_on_unitInterval` + the definitional equality between
`concat.toPath` and `concatAmbient` on `unitInterval`. Similarly for
`reverse`.

## What this file ships

* `concat_ambient_apply_of_unitInterval` — the bridge identity above.
* `reverse_ambient_apply_of_unitInterval` — analogue for `reverse`.
* `boundaryLoop_ambient_in_source` — chart-source containment of the
  boundary loop's ambient on `[0, 1]` from per-face chart-containment.
* `ChartContainedSmooth2Simplex.ofChartContainedFaces` — the
  constructor.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex Real

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace ChartContainedSmooth2Simplex

/-! ## Bridge: `concat.ambient = concatAmbient` on `[0, 1]` -/

/-- For `t ∈ [0, 1]`, the concat's chosen ambient equals `concatAmbient γ δ`.

Uses `ambient_eq_on_unitInterval` (the structural property of `SmoothPath`)
+ the definitional equality `concat.toPath ⟨t, ht⟩ = γ.concatAmbient δ t`
(by the body of `SmoothPath.concat`). -/
private lemma concat_ambient_apply_of_unitInterval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ⊤ Y]
    (γ δ : SmoothPath I Y) (h_eq : γ.tgt = δ.src)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (γ.concat δ h_eq).ambient t = γ.concatAmbient δ t := by
  have h := (γ.concat δ h_eq).ambient_eq_on_unitInterval ⟨t, ht⟩
  have h_val : ((⟨t, ht⟩ : unitInterval).val : ℝ) = t := rfl
  rw [h_val] at h
  rw [h]
  rfl

/-- For `t ∈ [0, 1]`, `γ.reverse.ambient t = γ.ambient (1 - t)`. -/
private lemma reverse_ambient_apply_of_unitInterval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ⊤ Y]
    (γ : SmoothPath I Y) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    γ.reverse.ambient t = γ.ambient (1 - t) := by
  have h_one_sub : 1 - t ∈ Set.Icc (0 : ℝ) 1 := by
    obtain ⟨h0, h1⟩ := ht
    exact ⟨by linarith, by linarith⟩
  have h_eq_rev := γ.reverse.ambient_eq_on_unitInterval ⟨t, ht⟩
  have h_val_t : ((⟨t, ht⟩ : unitInterval).val : ℝ) = t := rfl
  rw [h_val_t] at h_eq_rev
  have h_eq_fwd := γ.ambient_eq_on_unitInterval ⟨1 - t, h_one_sub⟩
  have h_val_1sub : ((⟨1 - t, h_one_sub⟩ : unitInterval).val : ℝ) = 1 - t := rfl
  rw [h_val_1sub] at h_eq_fwd
  rw [h_eq_rev, h_eq_fwd]
  rfl

/-! ## Face-ambient on `[0, 1]` equals `σ ∘ face_iParam` -/

private lemma face0_ambient_apply_of_unitInterval
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (Smooth2Simplex.face0 σ).ambient s
      = σ.toFun (Smooth2Simplex.face0Param s) := by
  have h_eq := (Smooth2Simplex.face0 σ).ambient_eq_on_unitInterval ⟨s, hs⟩
  have h_val : ((⟨s, hs⟩ : unitInterval).val : ℝ) = s := rfl
  rw [h_val] at h_eq
  rw [h_eq]
  rfl

private lemma face1_ambient_apply_of_unitInterval
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (Smooth2Simplex.face1 σ).ambient s
      = σ.toFun (Smooth2Simplex.face1Param s) := by
  have h_eq := (Smooth2Simplex.face1 σ).ambient_eq_on_unitInterval ⟨s, hs⟩
  have h_val : ((⟨s, hs⟩ : unitInterval).val : ℝ) = s := rfl
  rw [h_val] at h_eq
  rw [h_eq]
  rfl

private lemma face2_ambient_apply_of_unitInterval
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (Smooth2Simplex.face2 σ).ambient s
      = σ.toFun (Smooth2Simplex.face2Param s) := by
  have h_eq := (Smooth2Simplex.face2 σ).ambient_eq_on_unitInterval ⟨s, hs⟩
  have h_val : ((⟨s, hs⟩ : unitInterval).val : ℝ) = s := rfl
  rw [h_val] at h_eq
  rw [h_eq]
  rfl

/-! ## Smooth-transition reparameterisations land in `[0, 1]` -/

private lemma concatRepLeft_mem_Icc (t : ℝ) :
    SmoothPath.concatRepLeft t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold SmoothPath.concatRepLeft
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private lemma concatRepRight_mem_Icc (t : ℝ) :
    SmoothPath.concatRepRight t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold SmoothPath.concatRepRight
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-! ## Inner concat: `face2 ⋆ face0` chart-source containment -/

private lemma concat_face2_face0_ambient_in_source
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X)
    (basePoint : X)
    (h_face2 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      σ.toFun (Smooth2Simplex.face2Param s) ∈ (chartAt ℂ basePoint).source)
    (h_face0 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      σ.toFun (Smooth2Simplex.face0Param s) ∈ (chartAt ℂ basePoint).source) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ((Smooth2Simplex.face2 σ).concat (Smooth2Simplex.face0 σ)
          (Smooth2Simplex.face2_tgt_eq_face0_src σ)).ambient t
        ∈ (chartAt ℂ basePoint).source := by
  intro t ht
  rw [concat_ambient_apply_of_unitInterval _ _ _ ht]
  -- `concatAmbient γ δ t = if t ≤ 1/2 then γ.ambient (concatRepLeft t)
  --                                    else δ.ambient (concatRepRight t)`.
  unfold SmoothPath.concatAmbient
  by_cases h_half : t ≤ 1/2
  · rw [if_pos h_half]
    -- face2.ambient (concatRepLeft t) ∈ chart-source.
    rw [face2_ambient_apply_of_unitInterval σ (concatRepLeft_mem_Icc t)]
    exact h_face2 (SmoothPath.concatRepLeft t) (concatRepLeft_mem_Icc t)
  · rw [if_neg h_half]
    rw [face0_ambient_apply_of_unitInterval σ (concatRepRight_mem_Icc t)]
    exact h_face0 (SmoothPath.concatRepRight t) (concatRepRight_mem_Icc t)

/-! ## Outer concat: boundary loop chart-source containment -/

/-- **Boundary-loop chart-source containment.** From per-face
chart-containment data on `[0, 1]`, derive the chart-source
containment of `(boundaryLoop σ).ambient` on `[0, 1]`. -/
theorem boundaryLoop_ambient_in_source
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X)
    (basePoint : X)
    (h_face0 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      σ.toFun (Smooth2Simplex.face0Param s) ∈ (chartAt ℂ basePoint).source)
    (h_face1 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      σ.toFun (Smooth2Simplex.face1Param s) ∈ (chartAt ℂ basePoint).source)
    (h_face2 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      σ.toFun (Smooth2Simplex.face2Param s) ∈ (chartAt ℂ basePoint).source) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      (Smooth2Simplex.boundaryLoop σ).ambient t ∈ (chartAt ℂ basePoint).source := by
  intro t ht
  -- `boundaryLoop σ = ((face2 σ).concat (face0 σ) _).concat (face1 σ).reverse _`.
  unfold Smooth2Simplex.boundaryLoop
  rw [concat_ambient_apply_of_unitInterval _ _ _ ht]
  unfold SmoothPath.concatAmbient
  by_cases h_half : t ≤ 1/2
  · -- Inner concat on `concatRepLeft t ∈ [0, 1]`.
    rw [if_pos h_half]
    -- inner_concat.ambient (concatRepLeft t) — use the inner-concat lemma.
    exact concat_face2_face0_ambient_in_source σ basePoint h_face2 h_face0
      (SmoothPath.concatRepLeft t) (concatRepLeft_mem_Icc t)
  · -- `face1.reverse.ambient (concatRepRight t)`.
    rw [if_neg h_half]
    rw [reverse_ambient_apply_of_unitInterval _ (concatRepRight_mem_Icc t)]
    -- `face1.ambient (1 - concatRepRight t)`.
    -- `1 - concatRepRight t ∈ [0, 1]`.
    have h_one_sub_mem : 1 - SmoothPath.concatRepRight t ∈ Set.Icc (0 : ℝ) 1 := by
      obtain ⟨h0, h1⟩ := concatRepRight_mem_Icc t
      exact ⟨by linarith, by linarith⟩
    rw [face1_ambient_apply_of_unitInterval σ h_one_sub_mem]
    exact h_face1 (1 - SmoothPath.concatRepRight t) h_one_sub_mem

/-! ## Boundary-loop chart-image-in-ball containment -/

theorem boundaryLoop_chart_image_in_ball
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X)
    (basePoint : X)
    (ballCentre : ℂ) (ballRadius : ℝ)
    (h_face0 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      (chartAt ℂ basePoint) (σ.toFun (Smooth2Simplex.face0Param s))
        ∈ Metric.ball ballCentre ballRadius)
    (h_face1 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      (chartAt ℂ basePoint) (σ.toFun (Smooth2Simplex.face1Param s))
        ∈ Metric.ball ballCentre ballRadius)
    (h_face2 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      (chartAt ℂ basePoint) (σ.toFun (Smooth2Simplex.face2Param s))
        ∈ Metric.ball ballCentre ballRadius) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      (chartAt ℂ basePoint) ((Smooth2Simplex.boundaryLoop σ).ambient t)
        ∈ Metric.ball ballCentre ballRadius := by
  intro t ht
  unfold Smooth2Simplex.boundaryLoop
  rw [concat_ambient_apply_of_unitInterval _ _ _ ht]
  unfold SmoothPath.concatAmbient
  by_cases h_half : t ≤ 1/2
  · rw [if_pos h_half]
    -- Inner concat: same case-split.
    have h_concat_left := concatRepLeft_mem_Icc t
    rw [concat_ambient_apply_of_unitInterval _ _ _ h_concat_left]
    unfold SmoothPath.concatAmbient
    by_cases h_inner_half : SmoothPath.concatRepLeft t ≤ 1/2
    · rw [if_pos h_inner_half]
      rw [face2_ambient_apply_of_unitInterval σ
        (concatRepLeft_mem_Icc (SmoothPath.concatRepLeft t))]
      exact h_face2 _ (concatRepLeft_mem_Icc _)
    · rw [if_neg h_inner_half]
      rw [face0_ambient_apply_of_unitInterval σ
        (concatRepRight_mem_Icc (SmoothPath.concatRepLeft t))]
      exact h_face0 _ (concatRepRight_mem_Icc _)
  · rw [if_neg h_half]
    rw [reverse_ambient_apply_of_unitInterval _ (concatRepRight_mem_Icc t)]
    have h_one_sub_mem : 1 - SmoothPath.concatRepRight t ∈ Set.Icc (0 : ℝ) 1 := by
      obtain ⟨h0, h1⟩ := concatRepRight_mem_Icc t
      exact ⟨by linarith, by linarith⟩
    rw [face1_ambient_apply_of_unitInterval σ h_one_sub_mem]
    exact h_face1 _ h_one_sub_mem

/-! ## The constructor -/

/-- **Constructor from per-face chart-containment.**

Build a `ChartContainedSmooth2Simplex X` from:

* `σ : Smooth2Simplex 𝓘(ℝ, ℂ) X`,
* a chart base point `basePoint` and ball data
  `(ballCentre, ballRadius, radius_pos, ball_sub_target)`,
* per-face source-containment:
  `∀ s ∈ [0, 1], σ.toFun (face_iParam s) ∈ chart-source` for `i ∈ {0, 1, 2}`,
* per-face ball-containment:
  `∀ s ∈ [0, 1], chart (σ.toFun (face_iParam s)) ∈ ball`.

The boundary-loop chart-containment is derived via
`boundaryLoop_ambient_in_source` and `boundaryLoop_chart_image_in_ball`. -/
noncomputable def ofChartContainedFaces
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X)
    (basePoint : X) (ballCentre : ℂ) (ballRadius : ℝ)
    (radius_pos : 0 < ballRadius)
    (ball_sub_target :
      Metric.ball ballCentre ballRadius ⊆ (chartAt ℂ basePoint).target)
    (h_face0_src : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      σ.toFun (Smooth2Simplex.face0Param s) ∈ (chartAt ℂ basePoint).source)
    (h_face1_src : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      σ.toFun (Smooth2Simplex.face1Param s) ∈ (chartAt ℂ basePoint).source)
    (h_face2_src : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      σ.toFun (Smooth2Simplex.face2Param s) ∈ (chartAt ℂ basePoint).source)
    (h_face0_ball : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      (chartAt ℂ basePoint) (σ.toFun (Smooth2Simplex.face0Param s))
        ∈ Metric.ball ballCentre ballRadius)
    (h_face1_ball : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      (chartAt ℂ basePoint) (σ.toFun (Smooth2Simplex.face1Param s))
        ∈ Metric.ball ballCentre ballRadius)
    (h_face2_ball : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      (chartAt ℂ basePoint) (σ.toFun (Smooth2Simplex.face2Param s))
        ∈ Metric.ball ballCentre ballRadius) :
    ChartContainedSmooth2Simplex X where
  σ := σ
  boundaryData :=
    { γ := Smooth2Simplex.boundaryLoop σ
      basePoint := basePoint
      ballCentre := ballCentre
      ballRadius := ballRadius
      radius_pos := radius_pos
      ball_sub_target := ball_sub_target
      ambient_in_source :=
        boundaryLoop_ambient_in_source σ basePoint
          h_face0_src h_face1_src h_face2_src
      chart_image_in_ball :=
        boundaryLoop_chart_image_in_ball σ basePoint ballCentre ballRadius
          h_face0_ball h_face1_ball h_face2_ball
      is_loop := by
        -- `boundaryLoop_src σ = σ.toFun v0 = boundaryLoop_tgt σ`.
        rw [Smooth2Simplex.boundaryLoop_src, Smooth2Simplex.boundaryLoop_tgt] }
  boundaryData_γ := rfl

end ChartContainedSmooth2Simplex

end JacobianChallenge

end
