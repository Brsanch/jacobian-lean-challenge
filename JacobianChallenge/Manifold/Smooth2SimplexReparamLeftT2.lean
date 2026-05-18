/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexReparamLeftT1
import JacobianChallenge.Manifold.SmoothPathReverse

set_option linter.unusedSectionVars false

/-! # Second simplex T₂ of the bumpedHalfLeft reparameterisation homotopy

Companion file to `Smooth2SimplexReparamLeftT1.lean`. This file
constructs the SECOND triangle T₂ in the diagonal split of the square
`[0, 1]²`, with vertices `((0, 0), (1, 1), (1, 0))` in the (s, t)-square,
mapped via affine `(x₀, x₁) ↦ (x₀ + x₁, x₀)`.

So `T₂(x₀, x₁) := γ.ambient (reparamLeftF (x₀ + x₁) x₀)`.

Face identifications:

* `face0 T₂ = γ.bumpedHalfLeft.reverse` — at parameter `t`,
  `face0(T₂)(t) = γ.ambient(reparamLeftF 1 (1 - t.val))
                = γ.ambient(concatRepLeft((1 - t.val) / 2))`,
  which is `bumpedHalfLeft.reverse.toPath(t)`.
* `face1 T₂ = const γ.src` — at parameter `t`,
  `face1(T₂)(t) = γ.ambient(reparamLeftF t.val 0) = γ.ambient(0) = γ.src`.
* `face2 T₂` — the **diagonal path**, equal to `face1 T₁` (the
  cancelling face).

## What this file ships

* `Smooth2Simplex.ofReparamLeftT2 γ : Smooth2Simplex I X`.
* `face0_ofReparamLeftT2_eq_bumpedHalfLeftReverse`.
* `face1_ofReparamLeftT2_eq_const_src`.
* `face2_ofReparamLeftT2_eq_face1_ofReparamLeftT1` — the diagonal
  cancellation lemma.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-! ## The second triangle T₂ -/

/-- **The second 2-simplex of the bumpedHalfLeft reparam homotopy.**

Maps `(x₀, x₁) ↦ γ.ambient (reparamLeftF (x₀ + x₁) x₀)`, the
composition of the smooth homotopy with the affine map
`(x₀, x₁) ↦ (x₀ + x₁, x₀)` sending standard `Δ²` to the triangle
`((0, 0), (1, 1), (1, 0))` in the (s, t)-square. -/
noncomputable def Smooth2Simplex.ofReparamLeftT2 (γ : SmoothPath I X) :
    Smooth2Simplex I X where
  toFun := fun x : Fin 2 → ℝ => γ.ambient (reparamLeftF (x 0 + x 1) (x 0))
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
        (fun x : Fin 2 → ℝ => reparamLeftF (x 0 + x 1) (x 0)) :=
      contDiff_reparamLeftF.comp h_pair
    exact γ.ambient_contMDiff.comp h_F.contMDiff

variable (γ : SmoothPath I X)

@[simp] lemma Smooth2Simplex.ofReparamLeftT2_toFun
    (x : Fin 2 → ℝ) :
    (Smooth2Simplex.ofReparamLeftT2 γ).toFun x
      = γ.ambient (reparamLeftF (x 0 + x 1) (x 0)) := rfl

/-! ## Face identifications -/

/-- **face0 T₂ = γ.bumpedHalfLeft.reverse.**

face0(T₂)(t) = T₂.toFun(1 - t.val, t.val) = γ.ambient(reparamLeftF ((1-t.val)+t.val) (1-t.val))
            = γ.ambient(reparamLeftF 1 (1 - t.val))
            = γ.ambient(concatRepLeft((1 - t.val) / 2)).

`bumpedHalfLeft.reverse.toPath(t)` via `Path.symm`:
`= γ.ambient (concatRepLeft ((1 - t.val) / 2))` (= bumpedHalfLeft.toPath at `1 - t.val`).

Match. -/
lemma face0_ofReparamLeftT2_eq_bumpedHalfLeftReverse :
    Smooth2Simplex.face0 (Smooth2Simplex.ofReparamLeftT2 γ)
      = γ.bumpedHalfLeft.reverse := by
  apply SmoothPath.ext
  · -- src: face0.src = T₂.toFun v1 = γ.ambient(reparamLeftF 1 1) = γ.tgt.
    -- bumpedHalfLeft.reverse.src = bumpedHalfLeft.tgt = γ.tgt.
    show γ.ambient (reparamLeftF
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v1 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 0))
      = γ.bumpedHalfLeft.reverse.src
    have h_v1_0 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 = 1 := rfl
    have h_v1_1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h_v1_0, h_v1_1, SmoothPath.reverse_src, SmoothPath.bumpedHalfLeft_tgt]
    show γ.ambient (reparamLeftF (1 + 0) 1) = γ.tgt
    have h_arg : (1 : ℝ) + 0 = 1 := by norm_num
    rw [h_arg, reparamLeftF_one_right]
    exact γ.ambient_one_eq_tgt
  · -- tgt: face0.tgt = T₂.toFun v2 = γ.ambient(reparamLeftF (0+1) 0) = γ.ambient 0 = γ.src.
    -- bumpedHalfLeft.reverse.tgt = bumpedHalfLeft.src = γ.src.
    show γ.ambient (reparamLeftF
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v2 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 0))
      = γ.bumpedHalfLeft.reverse.tgt
    have h_v2_0 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v2_1 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 1 = 1 := rfl
    rw [h_v2_0, h_v2_1, SmoothPath.reverse_tgt, SmoothPath.bumpedHalfLeft_src]
    show γ.ambient (reparamLeftF (0 + 1) 0) = γ.src
    have h_arg : (0 : ℝ) + 1 = 1 := by norm_num
    rw [h_arg, reparamLeftF_zero_right]
    exact γ.ambient_zero_eq_src
  · -- toPath: face0(T₂)(t) = γ.ambient(reparamLeftF 1 (1-t.val))
    --                    = γ.ambient(concatRepLeft((1-t.val)/2))
    -- bumpedHalfLeft.reverse.toPath(t) = bumpedHalfLeft.toPath.symm(t)
    --     = bumpedHalfLeft.toPath ⟨1 - t.val, _⟩
    --     = γ.ambient(concatRepLeft((1 - t.val)/2))  (by bumpedHalfLeft_toPath_apply)
    intro t
    show γ.ambient (reparamLeftF
        ((Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0
          + (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0))
      = γ.bumpedHalfLeft.reverse.toPath t
    have h_p0 : (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0
        = 1 - t.val := rfl
    have h_p1 : (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1
        = t.val := rfl
    rw [h_p0, h_p1]
    show γ.ambient (reparamLeftF ((1 - t.val) + t.val) (1 - t.val))
      = γ.bumpedHalfLeft.reverse.toPath t
    have h_arg : (1 - t.val) + t.val = 1 := by ring
    rw [h_arg, reparamLeftF_one_left]
    -- Now goal: γ.ambient (concatRepLeft ((1 - t.val) / 2))
    --         = γ.bumpedHalfLeft.reverse.toPath t.
    -- Unfold reverse: toPath.symm t = γ.bumpedHalfLeft.toPath (unitInterval.symm t).
    show γ.ambient (SmoothPath.concatRepLeft ((1 - t.val) / 2))
      = γ.bumpedHalfLeft.toPath.symm t
    have h_symm_val : (unitInterval.symm t).val = 1 - t.val := rfl
    have h_bumped := SmoothPath.bumpedHalfLeft_toPath_apply γ (unitInterval.symm t)
    rw [h_symm_val] at h_bumped
    -- h_bumped : γ.bumpedHalfLeft.toPath (unitInterval.symm t)
    --             = γ.ambient (concatRepLeft ((1 - t.val) / 2))
    -- γ.bumpedHalfLeft.toPath.symm t = γ.bumpedHalfLeft.toPath (unitInterval.symm t).
    have h_symm_apply :
        γ.bumpedHalfLeft.toPath.symm t
          = γ.bumpedHalfLeft.toPath (unitInterval.symm t) := rfl
    rw [h_symm_apply, h_bumped]

/-- **face1 T₂ = const γ.src.**

face1(T₂)(t) = T₂.toFun(0, t.val) = γ.ambient(reparamLeftF (0+t.val) 0)
            = γ.ambient(reparamLeftF t.val 0) = γ.ambient(0) = γ.src.

`(const γ.src).toPath(t) = γ.src` for all `t`. -/
lemma face1_ofReparamLeftT2_eq_const_src :
    Smooth2Simplex.face1 (Smooth2Simplex.ofReparamLeftT2 γ)
      = SmoothPath.const I X γ.src := by
  apply SmoothPath.ext
  · -- src: face1.src = T₂.toFun v0 = γ.ambient(reparamLeftF 0 0) = γ.src.
    show γ.ambient (reparamLeftF
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v0 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 0))
      = (SmoothPath.const I X γ.src).src
    have h_v0_0 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v0_1 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h_v0_0, h_v0_1, SmoothPath.const_src]
    show γ.ambient (reparamLeftF (0 + 0) 0) = γ.src
    have h_arg : (0 : ℝ) + 0 = 0 := by norm_num
    rw [h_arg, reparamLeftF_zero_right]
    exact γ.ambient_zero_eq_src
  · -- tgt: face1.tgt = T₂.toFun v2 = γ.ambient(reparamLeftF (0+1) 0) = γ.src.
    show γ.ambient (reparamLeftF
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v2 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 0))
      = (SmoothPath.const I X γ.src).tgt
    have h_v2_0 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v2_1 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 1 = 1 := rfl
    rw [h_v2_0, h_v2_1, SmoothPath.const_tgt]
    show γ.ambient (reparamLeftF (0 + 1) 0) = γ.src
    have h_arg : (0 : ℝ) + 1 = 1 := by norm_num
    rw [h_arg, reparamLeftF_zero_right]
    exact γ.ambient_zero_eq_src
  · -- toPath: face1(T₂)(t) = γ.ambient(reparamLeftF t.val 0) = γ.ambient(0) = γ.src
    --       = (const γ.src).toPath t.
    intro t
    show γ.ambient (reparamLeftF
        ((Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 0
          + (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 0))
      = (SmoothPath.const I X γ.src).toPath t
    have h_p0 : (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 0 = 0 := rfl
    have h_p1 : (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 1
        = t.val := rfl
    rw [h_p0, h_p1]
    show γ.ambient (reparamLeftF (0 + t.val) 0)
      = (SmoothPath.const I X γ.src).toPath t
    rw [reparamLeftF_zero_right]
    rw [γ.ambient_zero_eq_src]
    rfl

/-! ## Diagonal cancellation -/

/-- **The diagonal face: `face2 T₂ = face1 T₁`.**

Both faces are the path `t ↦ γ.ambient(reparamLeftF t.val t.val)` from
`γ.src` to `γ.tgt`. This is the load-bearing identity for the cancellation
in `∂(T₁ + T₂)`. -/
lemma face2_ofReparamLeftT2_eq_face1_ofReparamLeftT1 :
    Smooth2Simplex.face2 (Smooth2Simplex.ofReparamLeftT2 γ)
      = Smooth2Simplex.face1 (Smooth2Simplex.ofReparamLeftT1 γ) := by
  apply SmoothPath.ext
  · -- src: face2(T₂).src = T₂.toFun v0 = γ.ambient(reparamLeftF 0 0) = γ.src.
    -- face1(T₁).src = T₁.toFun v0 = γ.ambient(reparamLeftF 0 0) = γ.src.
    show γ.ambient (reparamLeftF
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v0 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 0))
      = γ.ambient (reparamLeftF
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v0 : Fin 2 → ℝ) 1))
    have h_v0_0 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v0_1 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h_v0_0, h_v0_1]
    have h_arg : (0 : ℝ) + 0 = 0 := by norm_num
    rw [h_arg]
  · -- tgt: face2(T₂).tgt = T₂.toFun v1 = γ.ambient(reparamLeftF (1+0) 1)
    --                                  = γ.ambient(reparamLeftF 1 1).
    -- face1(T₁).tgt = T₁.toFun v2 = γ.ambient(reparamLeftF 1 (0+1))
    --                            = γ.ambient(reparamLeftF 1 1).
    show γ.ambient (reparamLeftF
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v1 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 0))
      = γ.ambient (reparamLeftF
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
  · -- toPath: face2(T₂)(t) = γ.ambient(reparamLeftF (t.val+0) t.val).
    -- face1(T₁)(t) = γ.ambient(reparamLeftF t.val (0+t.val))
    --             = γ.ambient(reparamLeftF t.val t.val).
    -- Both reduce to γ.ambient(reparamLeftF t.val t.val).
    intro t
    show γ.ambient (reparamLeftF
        ((Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 0
          + (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 0))
      = γ.ambient (reparamLeftF
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
