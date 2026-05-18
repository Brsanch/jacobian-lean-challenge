/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexConst
import JacobianChallenge.Manifold.SmoothPathConst
import JacobianChallenge.Manifold.SmoothPathIntegral
import JacobianChallenge.Manifold.SmoothPathExt
import JacobianChallenge.Manifold.SmoothPathBumpedHalf

set_option linter.unusedSectionVars false

/-! # First simplex T₁ for the loop-bounds-2-chain in a vector space V

For `V : Type*` a normed ℝ-vector space and `γ : SmoothPath 𝓘(ℝ, V) V`
a smooth loop in `V` (i.e., `γ.src = γ.tgt`), we build a smooth
2-simplex T₁ : Δ² → V whose three faces are:

* `face0 T₁ = const γ.src` — top edge of the homotopy square,
  constant at `γ.src = γ.tgt`.
* `face1 T₁` — diagonal of the homotopy square.
* `face2 T₁ = γ` — bottom edge.

Construction: the smooth homotopy
`H(s, t) := (1 - s) • γ.ambient t + s • γ.src`
contracts `γ` to the constant path at `γ.src` (using the loop
hypothesis to keep endpoints fixed at `γ.src`). Split the square
`[0, 1]²` into two triangles along the diagonal `(0, 0) ↔ (1, 1)`;
T₁ is the upper-left triangle, with affine map
`(x₀, x₁) ↦ (x₁, x₀ + x₁)` taking standard Δ² to the target.

So `T₁(x₀, x₁) := H(x₁, x₀ + x₁)`.

## What this file ships

* `loopBoundH γ : ℝ → ℝ → V` — the smooth homotopy.
* `contDiff_loopBoundH` — C^∞ proof.
* Endpoint specialisations.
* `Smooth2Simplex.ofLoopBoundT1 γ h_loop : Smooth2Simplex 𝓘(ℝ, V) V`.
* `face0_ofLoopBoundT1_eq_const_src` — face0 identification.
* `face2_ofLoopBoundT1_eq` — face2 = γ.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace JacobianChallenge

/-! ## The auxiliary homotopy `H` -/

/-- The smooth homotopy `H(s, t) := (1 - s) • γ.ambient t + s • γ.src`
from a smooth loop `γ` (at `s = 0`) to the constant path at `γ.src`
(at `s = 1`). For `t = 0` or `t = 1`, `H(s, t) = γ.src` (using the
loop hypothesis `γ.src = γ.tgt`). -/
def loopBoundH (γ : SmoothPath 𝓘(ℝ, V) V) (s t : ℝ) : V :=
  (1 - s) • γ.ambient t + s • γ.src

/-- `loopBoundH γ` is `C^∞` on `ℝ²` (as a function from `ℝ × ℝ` to `V`). -/
lemma contDiff_loopBoundH (γ : SmoothPath 𝓘(ℝ, V) V) :
    ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun p : ℝ × ℝ => loopBoundH γ p.1 p.2) := by
  unfold loopBoundH
  have h_fst : ContDiff ℝ (∞ : WithTop ℕ∞) (fun p : ℝ × ℝ => p.1) :=
    contDiff_fst
  have h_snd : ContDiff ℝ (∞ : WithTop ℕ∞) (fun p : ℝ × ℝ => p.2) :=
    contDiff_snd
  have h_one : ContDiff ℝ (∞ : WithTop ℕ∞) (fun _ : ℝ × ℝ => (1 : ℝ)) :=
    contDiff_const
  have h_oneSub : ContDiff ℝ (∞ : WithTop ℕ∞) (fun p : ℝ × ℝ => 1 - p.1) :=
    h_one.sub h_fst
  -- γ.ambient : ℝ → V is C^∞ (as a manifold map, which on V is
  -- equivalent to the analyst's C^∞).
  have h_amb : ContDiff ℝ (∞ : WithTop ℕ∞) γ.ambient := by
    have h_mdiff := γ.ambient_contMDiff
    rwa [contMDiff_iff_contDiff] at h_mdiff
  have h_amb_comp : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun p : ℝ × ℝ => γ.ambient p.2) := h_amb.comp h_snd
  have h_term1 : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (1 - p.1) • γ.ambient p.2) :=
    h_oneSub.smul h_amb_comp
  have h_src_const : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun _ : ℝ × ℝ => γ.src) := contDiff_const
  have h_term2 : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun p : ℝ × ℝ => p.1 • γ.src) := h_fst.smul h_src_const
  exact h_term1.add h_term2

/-! ## Endpoint specialisations of `loopBoundH` -/

@[simp] lemma loopBoundH_s_zero (γ : SmoothPath 𝓘(ℝ, V) V) (t : ℝ) :
    loopBoundH γ 0 t = γ.ambient t := by
  unfold loopBoundH
  simp

@[simp] lemma loopBoundH_s_one (γ : SmoothPath 𝓘(ℝ, V) V) (t : ℝ) :
    loopBoundH γ 1 t = γ.src := by
  unfold loopBoundH
  simp

/-- At `t = 0`, `loopBoundH γ s 0 = γ.src` (using `γ.ambient 0 = γ.src`). -/
@[simp] lemma loopBoundH_t_zero (γ : SmoothPath 𝓘(ℝ, V) V) (s : ℝ) :
    loopBoundH γ s 0 = γ.src := by
  unfold loopBoundH
  rw [SmoothPath.ambient_zero_eq_src γ]
  module

/-- At `t = 1`, `loopBoundH γ s 1 = γ.src` (using the loop hypothesis
`γ.src = γ.tgt` and `γ.ambient 1 = γ.tgt`). -/
@[simp] lemma loopBoundH_t_one (γ : SmoothPath 𝓘(ℝ, V) V)
    (h_loop : γ.src = γ.tgt) (s : ℝ) :
    loopBoundH γ s 1 = γ.src := by
  unfold loopBoundH
  rw [SmoothPath.ambient_one_eq_tgt γ, ← h_loop]
  module

/-! ## The first triangle T₁ -/

/-- **First 2-simplex of the loop-bounds 2-chain.**

`T₁(x₀, x₁) := loopBoundH γ (x 1) (x 0 + x 1)`. The affine reindex
`(x₀, x₁) ↦ (x₁, x₀ + x₁)` sends standard `Δ²` to the upper-left
triangle in `[0, 1]²` with vertices `((0, 0), (0, 1), (1, 1))` in
`(s, t)`-coordinates. -/
noncomputable def Smooth2Simplex.ofLoopBoundT1 (γ : SmoothPath 𝓘(ℝ, V) V) :
    Smooth2Simplex 𝓘(ℝ, V) V where
  toFun := fun x : Fin 2 → ℝ => loopBoundH γ (x 1) (x 0 + x 1)
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
    have h_H : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : Fin 2 → ℝ => loopBoundH γ (x 1) (x 0 + x 1)) :=
      (contDiff_loopBoundH γ).comp h_pair
    exact h_H.contMDiff

variable (γ : SmoothPath 𝓘(ℝ, V) V)

@[simp] lemma Smooth2Simplex.ofLoopBoundT1_toFun
    (x : Fin 2 → ℝ) :
    (Smooth2Simplex.ofLoopBoundT1 γ).toFun x
      = loopBoundH γ (x 1) (x 0 + x 1) := rfl

/-! ## Face identifications -/

/-- **face0 T₁ = const γ.src.**

face0(T₁)(t) = T₁(1-t, t) = H(t, (1-t)+t) = H(t, 1) = γ.src
(using the loop hypothesis). -/
lemma face0_ofLoopBoundT1_eq_const_src (h_loop : γ.src = γ.tgt) :
    Smooth2Simplex.face0 (Smooth2Simplex.ofLoopBoundT1 γ)
      = SmoothPath.const 𝓘(ℝ, V) V γ.src := by
  apply SmoothPath.ext
  · show loopBoundH γ
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v1 : Fin 2 → ℝ) 1)
      = (SmoothPath.const 𝓘(ℝ, V) V γ.src).src
    have h_v1_0 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 = 1 := rfl
    have h_v1_1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h_v1_0, h_v1_1, SmoothPath.const_src]
    show loopBoundH γ 0 (1 + 0) = γ.src
    have h_arg : (1 : ℝ) + 0 = 1 := by norm_num
    rw [h_arg, loopBoundH_t_one γ h_loop]
  · show loopBoundH γ
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v2 : Fin 2 → ℝ) 1)
      = (SmoothPath.const 𝓘(ℝ, V) V γ.src).tgt
    have h_v2_0 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v2_1 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 1 = 1 := rfl
    rw [h_v2_0, h_v2_1, SmoothPath.const_tgt]
    show loopBoundH γ 1 (0 + 1) = γ.src
    have h_arg : (0 : ℝ) + 1 = 1 := by norm_num
    rw [h_arg, loopBoundH_t_one γ h_loop]
  · intro t
    show loopBoundH γ
        ((Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0
          + (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1)
      = (SmoothPath.const 𝓘(ℝ, V) V γ.src).toPath t
    have h_p0 : (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0
        = 1 - t.val := rfl
    have h_p1 : (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1
        = t.val := rfl
    rw [h_p0, h_p1]
    show loopBoundH γ t.val ((1 - t.val) + t.val)
      = (SmoothPath.const 𝓘(ℝ, V) V γ.src).toPath t
    have h_arg : (1 - t.val) + t.val = 1 := by ring
    rw [h_arg, loopBoundH_t_one γ h_loop]
    rfl

/-- **face2 T₁ = γ.**

face2(T₁)(t) = T₁(t, 0) = H(0, t+0) = H(0, t) = γ.ambient t = γ. -/
lemma face2_ofLoopBoundT1_eq :
    Smooth2Simplex.face2 (Smooth2Simplex.ofLoopBoundT1 γ) = γ := by
  apply SmoothPath.ext
  · show loopBoundH γ
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v0 : Fin 2 → ℝ) 1)
      = γ.src
    have h_v0_0 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v0_1 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h_v0_0, h_v0_1]
    show loopBoundH γ 0 (0 + 0) = γ.src
    have h_arg : (0 : ℝ) + 0 = 0 := by norm_num
    rw [h_arg, loopBoundH_t_zero]
  · show loopBoundH γ
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v1 : Fin 2 → ℝ) 1)
      = γ.tgt
    have h_v1_0 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 = 1 := rfl
    have h_v1_1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h_v1_0, h_v1_1]
    show loopBoundH γ 0 (1 + 0) = γ.tgt
    have h_arg : (1 : ℝ) + 0 = 1 := by norm_num
    rw [h_arg, loopBoundH_s_zero]
    exact γ.ambient_one_eq_tgt
  · intro t
    show loopBoundH γ
        ((Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 0
          + (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 1)
      = γ.toPath t
    have h_p0 : (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 0
        = t.val := rfl
    have h_p1 : (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 1
        = 0 := rfl
    rw [h_p0, h_p1]
    show loopBoundH γ 0 (t.val + 0) = γ.toPath t
    have h_arg : t.val + 0 = t.val := by ring
    rw [h_arg, loopBoundH_s_zero]
    exact γ.ambient_eq_on_unitInterval t

end JacobianChallenge

end
