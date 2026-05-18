/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexReparamRightT1
import JacobianChallenge.Manifold.SmoothPathReverse

set_option linter.unusedSectionVars false

/-! # Second simplex T₂ of the bumpedHalfRight reparameterisation homotopy

Symmetric to `Smooth2SimplexReparamLeftT2.lean` but for the right
variant.

Face identifications:

* `face0 T₂ = δ.bumpedHalfRight.reverse`.
* `face1 T₂ = const δ.src`.
* `face2 T₂` = the **diagonal path**, equal to `face1 T₁` (the
  cancellation lemma).

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-! ## The second triangle T₂ (right variant) -/

/-- **Second 2-simplex of the bumpedHalfRight reparam homotopy.** -/
noncomputable def Smooth2Simplex.ofReparamRightT2 (δ : SmoothPath I X) :
    Smooth2Simplex I X where
  toFun := fun x : Fin 2 → ℝ => δ.ambient (reparamRightF (x 0 + x 1) (x 0))
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
        (fun x : Fin 2 → ℝ => (x 0 + x 1, x 0)) :=
      h_sum.prodMk h_proj0
    have h_F : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : Fin 2 → ℝ => reparamRightF (x 0 + x 1) (x 0)) :=
      contDiff_reparamRightF.comp h_pair
    exact δ.ambient_contMDiff.comp h_F.contMDiff

variable (δ : SmoothPath I X)

@[simp] lemma Smooth2Simplex.ofReparamRightT2_toFun
    (x : Fin 2 → ℝ) :
    (Smooth2Simplex.ofReparamRightT2 δ).toFun x
      = δ.ambient (reparamRightF (x 0 + x 1) (x 0)) := rfl

/-! ## Face identifications -/

lemma face0_ofReparamRightT2_eq_bumpedHalfRightReverse :
    Smooth2Simplex.face0 (Smooth2Simplex.ofReparamRightT2 δ)
      = δ.bumpedHalfRight.reverse := by
  apply SmoothPath.ext
  · show δ.ambient (reparamRightF
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v1 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 0))
      = δ.bumpedHalfRight.reverse.src
    have h_v1_0 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 = 1 := rfl
    have h_v1_1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h_v1_0, h_v1_1, SmoothPath.reverse_src, SmoothPath.bumpedHalfRight_tgt]
    show δ.ambient (reparamRightF (1 + 0) 1) = δ.tgt
    have h_arg : (1 : ℝ) + 0 = 1 := by norm_num
    rw [h_arg, reparamRightF_one_right]
    exact δ.ambient_one_eq_tgt
  · show δ.ambient (reparamRightF
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v2 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 0))
      = δ.bumpedHalfRight.reverse.tgt
    have h_v2_0 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v2_1 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 1 = 1 := rfl
    rw [h_v2_0, h_v2_1, SmoothPath.reverse_tgt, SmoothPath.bumpedHalfRight_src]
    show δ.ambient (reparamRightF (0 + 1) 0) = δ.src
    have h_arg : (0 : ℝ) + 1 = 1 := by norm_num
    rw [h_arg, reparamRightF_zero_right]
    exact δ.ambient_zero_eq_src
  · intro t
    show δ.ambient (reparamRightF
        ((Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0
          + (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0))
      = δ.bumpedHalfRight.reverse.toPath t
    have h_p0 : (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0
        = 1 - t.val := rfl
    have h_p1 : (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1
        = t.val := rfl
    rw [h_p0, h_p1]
    show δ.ambient (reparamRightF ((1 - t.val) + t.val) (1 - t.val))
      = δ.bumpedHalfRight.reverse.toPath t
    have h_arg : (1 - t.val) + t.val = 1 := by ring
    rw [h_arg, reparamRightF_one_left]
    show δ.ambient (SmoothPath.concatRepRight ((1 + (1 - t.val)) / 2))
      = δ.bumpedHalfRight.toPath.symm t
    -- bumpedHalfRight.toPath.symm t = bumpedHalfRight.toPath (unitInterval.symm t)
    --                              = δ.ambient(concatRepRight((1 + (1-t.val))/2))
    have h_symm_val : (unitInterval.symm t).val = 1 - t.val := rfl
    have h_bumped := SmoothPath.bumpedHalfRight_toPath_apply δ (unitInterval.symm t)
    rw [h_symm_val] at h_bumped
    have h_symm_apply :
        δ.bumpedHalfRight.toPath.symm t
          = δ.bumpedHalfRight.toPath (unitInterval.symm t) := rfl
    rw [h_symm_apply, h_bumped]

lemma face1_ofReparamRightT2_eq_const_src :
    Smooth2Simplex.face1 (Smooth2Simplex.ofReparamRightT2 δ)
      = SmoothPath.const I X δ.src := by
  apply SmoothPath.ext
  · show δ.ambient (reparamRightF
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v0 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 0))
      = (SmoothPath.const I X δ.src).src
    have h_v0_0 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v0_1 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h_v0_0, h_v0_1, SmoothPath.const_src]
    show δ.ambient (reparamRightF (0 + 0) 0) = δ.src
    have h_arg : (0 : ℝ) + 0 = 0 := by norm_num
    rw [h_arg, reparamRightF_zero_right]
    exact δ.ambient_zero_eq_src
  · show δ.ambient (reparamRightF
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v2 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 0))
      = (SmoothPath.const I X δ.src).tgt
    have h_v2_0 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v2_1 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 1 = 1 := rfl
    rw [h_v2_0, h_v2_1, SmoothPath.const_tgt]
    show δ.ambient (reparamRightF (0 + 1) 0) = δ.src
    have h_arg : (0 : ℝ) + 1 = 1 := by norm_num
    rw [h_arg, reparamRightF_zero_right]
    exact δ.ambient_zero_eq_src
  · intro t
    show δ.ambient (reparamRightF
        ((Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 0
          + (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 0))
      = (SmoothPath.const I X δ.src).toPath t
    have h_p0 : (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 0 = 0 := rfl
    have h_p1 : (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 1
        = t.val := rfl
    rw [h_p0, h_p1]
    show δ.ambient (reparamRightF (0 + t.val) 0)
      = (SmoothPath.const I X δ.src).toPath t
    rw [reparamRightF_zero_right]
    rw [δ.ambient_zero_eq_src]
    rfl

lemma face2_ofReparamRightT2_eq_face1_ofReparamRightT1 :
    Smooth2Simplex.face2 (Smooth2Simplex.ofReparamRightT2 δ)
      = Smooth2Simplex.face1 (Smooth2Simplex.ofReparamRightT1 δ) := by
  apply SmoothPath.ext
  · show δ.ambient (reparamRightF
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v0 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 0))
      = δ.ambient (reparamRightF
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v0 : Fin 2 → ℝ) 1))
    have h_v0_0 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v0_1 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h_v0_0, h_v0_1]
    have h_arg : (0 : ℝ) + 0 = 0 := by norm_num
    rw [h_arg]
  · show δ.ambient (reparamRightF
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v1 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 0))
      = δ.ambient (reparamRightF
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v2 : Fin 2 → ℝ) 1))
    have h_v1_0 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 = 1 := rfl
    have h_v1_1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 1 = 0 := rfl
    have h_v2_0 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v2_1 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 1 = 1 := rfl
    rw [h_v1_0, h_v1_1, h_v2_0, h_v2_1]
    have h_arg1 : (1 : ℝ) + 0 = 1 := by norm_num
    have h_arg2 : (0 : ℝ) + 1 = 1 := by norm_num
    rw [h_arg1, h_arg2]
  · intro t
    show δ.ambient (reparamRightF
        ((Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 0
          + (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 0))
      = δ.ambient (reparamRightF
        ((Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 0
          + (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 1))
    have h_p2_0 : (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 0
        = t.val := rfl
    have h_p2_1 : (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 1 = 0 := rfl
    have h_p1_0 : (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 0 = 0 := rfl
    have h_p1_1 : (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 1
        = t.val := rfl
    rw [h_p2_0, h_p2_1, h_p1_0, h_p1_1]
    have h_arg_t2 : t.val + 0 = t.val := by ring
    have h_arg_t1 : (0 : ℝ) + t.val = t.val := by ring
    rw [h_arg_t2, h_arg_t1]

end JacobianChallenge

end
