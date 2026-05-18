/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexLoopBoundsVectorSpaceT1

set_option linter.unusedSectionVars false

/-! # Second simplex T₂ for the loop-bounds-2-chain in a vector space V

Companion to `Smooth2SimplexLoopBoundsVectorSpaceT1.lean`. The square
`[0, 1]²` is split into two triangles along the diagonal `(0, 0) ↔ (1, 1)`;
T₂ is the lower-right triangle, with affine map
`(x₀, x₁) ↦ (x₀ + x₁, x₀)` taking standard Δ² to vertices
`((0, 0), (1, 1), (1, 0))` in `(s, t)`-coordinates.

So `T₂(x₀, x₁) := H(x₀ + x₁, x₀)`.

Face identifications:

* `face0 T₂ = const γ.src` — right edge of the homotopy square,
  `H(1, t) = γ.src` for all `t`.
* `face1 T₂ = const γ.src` — bottom-left of the homotopy square,
  `H(t, 0) = γ.src` for all `t` (using `γ.ambient 0 = γ.src`).
* `face2 T₂` — the **diagonal**, same as `face1 T₁`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace JacobianChallenge

/-! ## The second triangle T₂ -/

/-- **Second 2-simplex of the loop-bounds 2-chain.**

`T₂(x₀, x₁) := loopBoundH γ (x 0 + x 1) (x 0)`. -/
noncomputable def Smooth2Simplex.ofLoopBoundT2 (γ : SmoothPath 𝓘(ℝ, V) V) :
    Smooth2Simplex 𝓘(ℝ, V) V where
  toFun := fun x : Fin 2 → ℝ => loopBoundH γ (x 0 + x 1) (x 0)
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
    have h_H : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : Fin 2 → ℝ => loopBoundH γ (x 0 + x 1) (x 0)) :=
      (contDiff_loopBoundH γ).comp h_pair
    exact h_H.contMDiff

variable (γ : SmoothPath 𝓘(ℝ, V) V)

@[simp] lemma Smooth2Simplex.ofLoopBoundT2_toFun
    (x : Fin 2 → ℝ) :
    (Smooth2Simplex.ofLoopBoundT2 γ).toFun x
      = loopBoundH γ (x 0 + x 1) (x 0) := rfl

/-! ## Face identifications -/

/-- **face0 T₂ = const γ.src.**

face0(T₂)(t) = T₂(1-t, t) = H((1-t)+t, 1-t) = H(1, 1-t) = γ.src. -/
lemma face0_ofLoopBoundT2_eq_const_src :
    Smooth2Simplex.face0 (Smooth2Simplex.ofLoopBoundT2 γ)
      = SmoothPath.const 𝓘(ℝ, V) V γ.src := by
  apply SmoothPath.ext
  · show loopBoundH γ
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v1 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 0)
      = (SmoothPath.const 𝓘(ℝ, V) V γ.src).src
    have h_v1_0 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 = 1 := rfl
    have h_v1_1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h_v1_0, h_v1_1, SmoothPath.const_src]
    show loopBoundH γ (1 + 0) 1 = γ.src
    have h_arg : (1 : ℝ) + 0 = 1 := by norm_num
    rw [h_arg]
    rw [loopBoundH_s_one]
  · show loopBoundH γ
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v2 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 0)
      = (SmoothPath.const 𝓘(ℝ, V) V γ.src).tgt
    have h_v2_0 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v2_1 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 1 = 1 := rfl
    rw [h_v2_0, h_v2_1, SmoothPath.const_tgt]
    show loopBoundH γ (0 + 1) 0 = γ.src
    have h_arg : (0 : ℝ) + 1 = 1 := by norm_num
    rw [h_arg]
    rw [loopBoundH_s_one]
  · intro t
    show loopBoundH γ
        ((Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0
          + (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0)
      = (SmoothPath.const 𝓘(ℝ, V) V γ.src).toPath t
    have h_p0 : (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0
        = 1 - t.val := rfl
    have h_p1 : (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1
        = t.val := rfl
    rw [h_p0, h_p1]
    show loopBoundH γ ((1 - t.val) + t.val) (1 - t.val)
      = (SmoothPath.const 𝓘(ℝ, V) V γ.src).toPath t
    have h_arg : (1 - t.val) + t.val = 1 := by ring
    rw [h_arg, loopBoundH_s_one]
    rfl

/-- **face1 T₂ = const γ.src.**

face1(T₂)(t) = T₂(0, t) = H(0+t, 0) = H(t, 0) = γ.src (using
`γ.ambient 0 = γ.src` and `(1-t) • γ.src + t • γ.src = γ.src`). -/
lemma face1_ofLoopBoundT2_eq_const_src :
    Smooth2Simplex.face1 (Smooth2Simplex.ofLoopBoundT2 γ)
      = SmoothPath.const 𝓘(ℝ, V) V γ.src := by
  apply SmoothPath.ext
  · show loopBoundH γ
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v0 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 0)
      = (SmoothPath.const 𝓘(ℝ, V) V γ.src).src
    have h_v0_0 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v0_1 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h_v0_0, h_v0_1, SmoothPath.const_src]
    show loopBoundH γ (0 + 0) 0 = γ.src
    have h_arg : (0 : ℝ) + 0 = 0 := by norm_num
    rw [h_arg, loopBoundH_t_zero]
  · show loopBoundH γ
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v2 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 0)
      = (SmoothPath.const 𝓘(ℝ, V) V γ.src).tgt
    have h_v2_0 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v2_1 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 1 = 1 := rfl
    rw [h_v2_0, h_v2_1, SmoothPath.const_tgt]
    show loopBoundH γ (0 + 1) 0 = γ.src
    have h_arg : (0 : ℝ) + 1 = 1 := by norm_num
    rw [h_arg, loopBoundH_t_zero]
  · intro t
    show loopBoundH γ
        ((Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 0
          + (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 0)
      = (SmoothPath.const 𝓘(ℝ, V) V γ.src).toPath t
    have h_p0 : (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 0
        = 0 := rfl
    have h_p1 : (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 1
        = t.val := rfl
    rw [h_p0, h_p1]
    show loopBoundH γ (0 + t.val) 0
      = (SmoothPath.const 𝓘(ℝ, V) V γ.src).toPath t
    rw [loopBoundH_t_zero]
    rfl

/-! ## Diagonal cancellation -/

/-- **The diagonal face: face2 T₂ = face1 T₁.**

Both faces are `t ↦ loopBoundH γ t.val t.val` from `γ.src` to `γ.src`.
This is the load-bearing identity for the cancellation in
`∂(T₁ + T₂)`. -/
lemma face2_ofLoopBoundT2_eq_face1_ofLoopBoundT1 :
    Smooth2Simplex.face2 (Smooth2Simplex.ofLoopBoundT2 γ)
      = Smooth2Simplex.face1 (Smooth2Simplex.ofLoopBoundT1 γ) := by
  apply SmoothPath.ext
  · -- src: face2(T₂).src = T₂(v0) = H(0+0, 0) = H(0, 0) = γ.ambient 0 = γ.src.
    -- face1(T₁).src = T₁(v0) = H(0, 0+0) = H(0, 0) = γ.src.
    show loopBoundH γ
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v0 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 0)
      = loopBoundH γ
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v0 : Fin 2 → ℝ) 1)
    have h_v0_0 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v0_1 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h_v0_0, h_v0_1]
    have h_arg : (0 : ℝ) + 0 = 0 := by norm_num
    rw [h_arg]
  · -- tgt: face2(T₂).tgt = T₂(v1) = H(1+0, 1) = H(1, 1) = γ.src.
    -- face1(T₁).tgt = T₁(v2) = H(1, 0+1) = H(1, 1) = γ.src.
    show loopBoundH γ
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v1 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 0)
      = loopBoundH γ
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v2 : Fin 2 → ℝ) 1)
    have h_v1_0 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 = 1 := rfl
    have h_v1_1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 1 = 0 := rfl
    have h_v2_0 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v2_1 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 1 = 1 := rfl
    rw [h_v1_0, h_v1_1, h_v2_0, h_v2_1]
    have h_arg1 : (1 : ℝ) + 0 = 1 := by norm_num
    have h_arg2 : (0 : ℝ) + 1 = 1 := by norm_num
    rw [h_arg1, h_arg2]
  · intro t
    -- face2(T₂)(t) = T₂(t, 0) = H(t+0, t) = H(t, t).
    -- face1(T₁)(t) = T₁(0, t) = H(t, 0+t) = H(t, t).
    show loopBoundH γ
        ((Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 0
          + (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 0)
      = loopBoundH γ
        ((Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 0
          + (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 1)
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
