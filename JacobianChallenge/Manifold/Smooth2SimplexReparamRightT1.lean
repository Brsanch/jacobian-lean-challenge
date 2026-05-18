/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexConst
import JacobianChallenge.Manifold.SmoothPathBumpedHalf
import JacobianChallenge.Manifold.SmoothPathExt

set_option linter.unusedSectionVars false

/-! # First simplex T₁ of the bumpedHalfRight reparameterisation homotopy

Symmetric to `Smooth2SimplexReparamLeftT1.lean` but uses
`reparamRightF s t := (1 - s) * t + s * concatRepRight ((1 + t) / 2)`.

Face identifications:

* `face0 T₁ = const δ.tgt` (because `F (s, 1) = 1` for all `s`).
* `face1 T₁` = the **diagonal path** (matches `face2 T₂`).
* `face2 T₁ = δ`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-! ## Auxiliary parameter function -/

/-- `reparamRightF s t := (1 - s) * t + s * concatRepRight ((1 + t) / 2)`. -/
def reparamRightF (s t : ℝ) : ℝ :=
  (1 - s) * t + s * SmoothPath.concatRepRight ((1 + t) / 2)

/-- `reparamRightF` is C^∞ on `ℝ²`. -/
lemma contDiff_reparamRightF :
    ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun p : ℝ × ℝ => reparamRightF p.1 p.2) := by
  unfold reparamRightF
  have h_fst : ContDiff ℝ (∞ : WithTop ℕ∞) (fun p : ℝ × ℝ => p.1) :=
    contDiff_fst
  have h_snd : ContDiff ℝ (∞ : WithTop ℕ∞) (fun p : ℝ × ℝ => p.2) :=
    contDiff_snd
  have h_one : ContDiff ℝ (∞ : WithTop ℕ∞) (fun _ : ℝ × ℝ => (1 : ℝ)) :=
    contDiff_const
  have h_oneSub : ContDiff ℝ (∞ : WithTop ℕ∞) (fun p : ℝ × ℝ => 1 - p.1) :=
    h_one.sub h_fst
  have h_term1 : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (1 - p.1) * p.2) :=
    h_oneSub.mul h_snd
  have h_oneAdd : ContDiff ℝ (∞ : WithTop ℕ∞) (fun p : ℝ × ℝ => 1 + p.2) :=
    h_one.add h_snd
  have h_half : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (1 + p.2) / 2) := by
    have h_two : ContDiff ℝ (∞ : WithTop ℕ∞) (fun _ : ℝ × ℝ => (2 : ℝ)) :=
      contDiff_const
    exact h_oneAdd.div h_two (fun _ => by norm_num)
  have h_crr : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun p : ℝ × ℝ => SmoothPath.concatRepRight ((1 + p.2) / 2)) :=
    SmoothPath.contDiff_concatRepRight.comp h_half
  have h_term2 : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun p : ℝ × ℝ => p.1 * SmoothPath.concatRepRight ((1 + p.2) / 2)) :=
    h_fst.mul h_crr
  exact h_term1.add h_term2

@[simp] lemma reparamRightF_zero_left (t : ℝ) :
    reparamRightF 0 t = t := by
  unfold reparamRightF; ring

@[simp] lemma reparamRightF_one_left (t : ℝ) :
    reparamRightF 1 t = SmoothPath.concatRepRight ((1 + t) / 2) := by
  unfold reparamRightF; ring

@[simp] lemma reparamRightF_zero_right (s : ℝ) :
    reparamRightF s 0 = 0 := by
  unfold reparamRightF
  have h_eq : SmoothPath.concatRepRight ((1 + (0 : ℝ)) / 2) = 0 := by
    have h_arg : (1 + (0 : ℝ)) / 2 = 1/2 := by norm_num
    rw [h_arg]
    exact SmoothPath.concatRepRight_eq_zero_of_le (1/2) (by norm_num)
  rw [h_eq]
  ring

@[simp] lemma reparamRightF_one_right (s : ℝ) :
    reparamRightF s 1 = 1 := by
  unfold reparamRightF
  have h_eq : SmoothPath.concatRepRight ((1 + (1 : ℝ)) / 2) = 1 := by
    have h_arg : (1 + (1 : ℝ)) / 2 = 1 := by norm_num
    rw [h_arg]
    exact SmoothPath.concatRepRight_one
  rw [h_eq]
  ring

/-! ## The first triangle T₁ (right variant) -/

/-- **First 2-simplex of the bumpedHalfRight reparam homotopy.** -/
noncomputable def Smooth2Simplex.ofReparamRightT1 (δ : SmoothPath I X) :
    Smooth2Simplex I X where
  toFun := fun x : Fin 2 → ℝ => δ.ambient (reparamRightF (x 1) (x 0 + x 1))
  smooth := by
    have h_proj0 :
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : Fin 2 → ℝ => x 0) :=
      (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff
    have h_proj1 :
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : Fin 2 → ℝ => x 1) :=
      (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff
    have h_sum : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : Fin 2 → ℝ => x 0 + x 1) := h_proj0.add h_proj1
    have h_pair : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : Fin 2 → ℝ => (x 1, x 0 + x 1)) :=
      h_proj1.prodMk h_sum
    have h_F : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : Fin 2 → ℝ => reparamRightF (x 1) (x 0 + x 1)) :=
      contDiff_reparamRightF.comp h_pair
    exact δ.ambient_contMDiff.comp h_F.contMDiff

variable (δ : SmoothPath I X)

@[simp] lemma Smooth2Simplex.ofReparamRightT1_toFun
    (x : Fin 2 → ℝ) :
    (Smooth2Simplex.ofReparamRightT1 δ).toFun x
      = δ.ambient (reparamRightF (x 1) (x 0 + x 1)) := rfl

/-! ## Face identifications for T₁ -/

lemma face0_ofReparamRightT1_eq_const_tgt :
    Smooth2Simplex.face0 (Smooth2Simplex.ofReparamRightT1 δ)
      = SmoothPath.const I X δ.tgt := by
  apply SmoothPath.ext
  · show δ.ambient (reparamRightF
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v1 : Fin 2 → ℝ) 1))
      = (SmoothPath.const I X δ.tgt).src
    have h_v1_0 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 = 1 := rfl
    have h_v1_1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h_v1_0, h_v1_1, SmoothPath.const_src]
    show δ.ambient (reparamRightF 0 (1 + 0)) = δ.tgt
    have h_arg : (1 : ℝ) + 0 = 1 := by norm_num
    rw [h_arg, reparamRightF_one_right]
    exact δ.ambient_one_eq_tgt
  · show δ.ambient (reparamRightF
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v2 : Fin 2 → ℝ) 1))
      = (SmoothPath.const I X δ.tgt).tgt
    have h_v2_0 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v2_1 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 1 = 1 := rfl
    rw [h_v2_0, h_v2_1, SmoothPath.const_tgt]
    show δ.ambient (reparamRightF 1 (0 + 1)) = δ.tgt
    have h_arg : (0 : ℝ) + 1 = 1 := by norm_num
    rw [h_arg, reparamRightF_one_right]
    exact δ.ambient_one_eq_tgt
  · intro t
    show δ.ambient (reparamRightF
        ((Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0
          + (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1))
      = (SmoothPath.const I X δ.tgt).toPath t
    have h_p0 : (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0
        = 1 - t.val := rfl
    have h_p1 : (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1
        = t.val := rfl
    rw [h_p0, h_p1]
    show δ.ambient (reparamRightF t.val ((1 - t.val) + t.val))
      = (SmoothPath.const I X δ.tgt).toPath t
    have h_arg : (1 - t.val) + t.val = 1 := by ring
    rw [h_arg, reparamRightF_one_right]
    rw [δ.ambient_one_eq_tgt]
    rfl

lemma face2_ofReparamRightT1_eq :
    Smooth2Simplex.face2 (Smooth2Simplex.ofReparamRightT1 δ) = δ := by
  apply SmoothPath.ext
  · show δ.ambient (reparamRightF
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v0 : Fin 2 → ℝ) 1))
      = δ.src
    have h_v0_0 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v0_1 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h_v0_0, h_v0_1]
    show δ.ambient (reparamRightF 0 (0 + 0)) = δ.src
    have h_arg : (0 : ℝ) + 0 = 0 := by norm_num
    rw [h_arg, reparamRightF_zero_right]
    exact δ.ambient_zero_eq_src
  · show δ.ambient (reparamRightF
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v1 : Fin 2 → ℝ) 1))
      = δ.tgt
    have h_v1_0 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 = 1 := rfl
    have h_v1_1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h_v1_0, h_v1_1]
    show δ.ambient (reparamRightF 0 (1 + 0)) = δ.tgt
    have h_arg : (1 : ℝ) + 0 = 1 := by norm_num
    rw [h_arg, reparamRightF_one_right]
    exact δ.ambient_one_eq_tgt
  · intro t
    show δ.ambient (reparamRightF
        ((Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 0
          + (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 1))
      = δ.toPath t
    have h_p0 : (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 0
        = t.val := rfl
    have h_p1 : (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 1
        = 0 := rfl
    rw [h_p0, h_p1]
    show δ.ambient (reparamRightF 0 (t.val + 0)) = δ.toPath t
    have h_arg : t.val + 0 = t.val := by ring
    rw [h_arg, reparamRightF_zero_left]
    exact δ.ambient_eq_on_unitInterval t

end JacobianChallenge

end
