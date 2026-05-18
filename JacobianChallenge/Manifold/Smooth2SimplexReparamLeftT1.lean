/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexConst
import JacobianChallenge.Manifold.SmoothPathBumpedHalf
import JacobianChallenge.Manifold.SmoothPathExt

set_option linter.unusedSectionVars false

/-! # First simplex T₁ of the bumpedHalfLeft reparameterisation homotopy

This is the first of two 2-simplices whose sum forms a smooth 2-chain
bounding `single γ - single γ.bumpedHalfLeft` (modulo
constant-path-stokes-boundaries and reverse-cancellation).

## Geometric idea

Consider the square `[0, 1]² → X` given by
`(s, t) ↦ γ.ambient ((1 - s) * t + s * concatRepLeft (t / 2))`. This is
a smooth homotopy from `γ` (at `s = 0`) to `γ.bumpedHalfLeft` (at
`s = 1`), constant at `γ.src` on the bottom edge (`t = 0`) and constant
at `γ.tgt` on the top edge (`t = 1`).

We split the square into two triangles by the diagonal from `(0, 0)`
to `(1, 1)`. The first triangle T₁ has vertices `((0, 0), (0, 1),
(1, 1))` in `(s, t)`-coordinates (or after the affine
re-parameterisation, `((0, 0), (0, 1), (1, 1))` in the target
`(x₀, x₁)` coordinates). The affine map sending standard `Δ²` to T₁'s
target triangle is

```
(x₀, x₁) ↦ (x₁, x₀ + x₁).
```

So T₁(x₀, x₁) := `γ.ambient` of the formula with `(s := x₁, t := x₀ + x₁)`.

The three faces work out (after simplification):

* `face0 T₁` is constant at `γ.tgt` (because `F (s, 1) = 1` for all `s ∈ [0, 1]`).
* `face1 T₁` is the **diagonal path** (will be matched with `face2 T₂` for cancellation).
* `face2 T₁ = γ`.

## What this file ships

* `reparamLeftF (s t : ℝ) : ℝ` — the auxiliary parameter function
  `(1 - s) * t + s * concatRepLeft (t / 2)`. C^∞ on `ℝ²`.
* `Smooth2Simplex.ofReparamLeftT1 γ : Smooth2Simplex I X` — the first
  triangle.
* `face0_ofReparamLeftT1_eq_const_tgt`,
* `face2_ofReparamLeftT1_eq`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-! ## Auxiliary parameter function -/

/-- The auxiliary parameter function for the bumpedHalfLeft homotopy:
`reparamLeftF s t := (1 - s) * t + s * concatRepLeft (t / 2)`.

At `s = 0`: returns `t` (identity, traces `γ`).
At `s = 1`: returns `concatRepLeft (t / 2)` (traces `γ.bumpedHalfLeft`).
At `t = 0`: returns `0` regardless of `s` (constant at `γ.src` on bottom edge).
At `t = 1`: returns `(1 - s) + s = 1` regardless of `s` (constant at `γ.tgt` on top edge).
-/
def reparamLeftF (s t : ℝ) : ℝ :=
  (1 - s) * t + s * SmoothPath.concatRepLeft (t / 2)

/-- `reparamLeftF` is `C^∞` on `ℝ²`. -/
lemma contDiff_reparamLeftF :
    ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun p : ℝ × ℝ => reparamLeftF p.1 p.2) := by
  unfold reparamLeftF
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
  have h_half : ContDiff ℝ (∞ : WithTop ℕ∞) (fun p : ℝ × ℝ => p.2 / 2) := by
    have h_two : ContDiff ℝ (∞ : WithTop ℕ∞) (fun _ : ℝ × ℝ => (2 : ℝ)) :=
      contDiff_const
    exact h_snd.div h_two (fun _ => by norm_num)
  have h_crl : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun p : ℝ × ℝ => SmoothPath.concatRepLeft (p.2 / 2)) :=
    SmoothPath.contDiff_concatRepLeft.comp h_half
  have h_term2 : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun p : ℝ × ℝ => p.1 * SmoothPath.concatRepLeft (p.2 / 2)) :=
    h_fst.mul h_crl
  exact h_term1.add h_term2

/-- Specialisation: `reparamLeftF` at fixed `s = 0` is the identity. -/
@[simp] lemma reparamLeftF_zero_left (t : ℝ) :
    reparamLeftF 0 t = t := by
  unfold reparamLeftF; ring

/-- Specialisation: `reparamLeftF` at fixed `s = 1` is `concatRepLeft (· / 2)`. -/
@[simp] lemma reparamLeftF_one_left (t : ℝ) :
    reparamLeftF 1 t = SmoothPath.concatRepLeft (t / 2) := by
  unfold reparamLeftF; ring

/-- Specialisation: `reparamLeftF` at fixed `t = 0` is identically `0`. -/
@[simp] lemma reparamLeftF_zero_right (s : ℝ) :
    reparamLeftF s 0 = 0 := by
  unfold reparamLeftF
  rw [show (0 : ℝ) / 2 = 0 from by norm_num, SmoothPath.concatRepLeft_zero]
  ring

/-- Specialisation: `reparamLeftF` at fixed `t = 1` is identically `1`. -/
@[simp] lemma reparamLeftF_one_right (s : ℝ) :
    reparamLeftF s 1 = 1 := by
  unfold reparamLeftF
  rw [SmoothPath.concatRepLeft_eq_one_of_ge (1/2) (by norm_num : (3:ℝ)/8 ≤ 1/2)]
  ring

/-! ## The first triangle T₁ -/

/-- **The first 2-simplex of the bumpedHalfLeft reparam homotopy.**

Maps `(x₀, x₁) ↦ γ.ambient (reparamLeftF x₁ (x₀ + x₁))`, which is the
composition of the smooth homotopy with the affine map
`(x₀, x₁) ↦ (x₁, x₀ + x₁)` sending standard `Δ²` to the triangle
`((0, 0), (0, 1), (1, 1))` in the (s, t)-square. -/
noncomputable def Smooth2Simplex.ofReparamLeftT1 (γ : SmoothPath I X) :
    Smooth2Simplex I X where
  toFun := fun x : Fin 2 → ℝ => γ.ambient (reparamLeftF (x 1) (x 0 + x 1))
  smooth := by
    -- Smoothness chain:
    --   γ.ambient : ℝ → X is C^∞,
    --   the linear map `x ↦ x 1` is C^∞,
    --   the linear map `x ↦ x 0 + x 1` is C^∞,
    --   their product through `reparamLeftF` is C^∞.
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
        (fun x : Fin 2 → ℝ => reparamLeftF (x 1) (x 0 + x 1)) :=
      contDiff_reparamLeftF.comp h_pair
    exact γ.ambient_contMDiff.comp h_F.contMDiff

variable (γ : SmoothPath I X)

@[simp] lemma Smooth2Simplex.ofReparamLeftT1_toFun
    (x : Fin 2 → ℝ) :
    (Smooth2Simplex.ofReparamLeftT1 γ).toFun x
      = γ.ambient (reparamLeftF (x 1) (x 0 + x 1)) := rfl

/-! ## Face identifications -/

/-- **face0 T₁ = const γ.tgt.**

face0 maps `t ↦ T₁.toFun (1 - t, t) = γ.ambient (reparamLeftF t (1 - t + t))
= γ.ambient (reparamLeftF t 1) = γ.ambient 1 = γ.tgt` for all `t`. -/
lemma face0_ofReparamLeftT1_eq_const_tgt :
    Smooth2Simplex.face0 (Smooth2Simplex.ofReparamLeftT1 γ)
      = SmoothPath.const I X γ.tgt := by
  apply SmoothPath.ext
  · -- src: face0.src = T₁.toFun v1 = γ.ambient (reparamLeftF 0 1) = γ.ambient 1 = γ.tgt.
    show γ.ambient (reparamLeftF
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v1 : Fin 2 → ℝ) 1))
      = (SmoothPath.const I X γ.tgt).src
    have h_v1_0 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 = 1 := rfl
    have h_v1_1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h_v1_0, h_v1_1, SmoothPath.const_src]
    show γ.ambient (reparamLeftF 0 (1 + 0)) = γ.tgt
    have h_arg : (1 : ℝ) + 0 = 1 := by norm_num
    rw [h_arg, reparamLeftF_one_right]
    exact γ.ambient_one_eq_tgt
  · -- tgt: face0.tgt = T₁.toFun v2 = γ.ambient (reparamLeftF 1 1) = γ.tgt.
    show γ.ambient (reparamLeftF
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v2 : Fin 2 → ℝ) 1))
      = (SmoothPath.const I X γ.tgt).tgt
    have h_v2_0 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v2_1 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 1 = 1 := rfl
    rw [h_v2_0, h_v2_1, SmoothPath.const_tgt]
    show γ.ambient (reparamLeftF 1 (0 + 1)) = γ.tgt
    have h_arg : (0 : ℝ) + 1 = 1 := by norm_num
    rw [h_arg, reparamLeftF_one_right]
    exact γ.ambient_one_eq_tgt
  · -- toPath: face0(T₁)(t) = γ.ambient(reparamLeftF t.val 1) = γ.tgt = const γ.tgt(t).
    intro t
    show γ.ambient (reparamLeftF
        ((Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0
          + (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1))
      = (SmoothPath.const I X γ.tgt).toPath t
    have h_p0 : (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0
        = 1 - t.val := rfl
    have h_p1 : (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1
        = t.val := rfl
    rw [h_p0, h_p1]
    show γ.ambient (reparamLeftF t.val ((1 - t.val) + t.val))
      = (SmoothPath.const I X γ.tgt).toPath t
    have h_arg : (1 - t.val) + t.val = 1 := by ring
    rw [h_arg, reparamLeftF_one_right]
    rw [γ.ambient_one_eq_tgt]
    -- const γ.tgt at any t is γ.tgt.
    rfl

/-- **face2 T₁ = γ.**

face2 maps `t ↦ T₁.toFun (t, 0) = γ.ambient (reparamLeftF 0 (t + 0))
= γ.ambient (reparamLeftF 0 t) = γ.ambient t`. So face2's toPath at `t`
equals `γ.ambient t.val`, which is `γ.toPath t` via
`ambient_eq_on_unitInterval`. -/
lemma face2_ofReparamLeftT1_eq :
    Smooth2Simplex.face2 (Smooth2Simplex.ofReparamLeftT1 γ) = γ := by
  apply SmoothPath.ext
  · -- src: face2.src = T₁.toFun v0 = γ.ambient (reparamLeftF 0 0) = γ.ambient 0 = γ.src.
    show γ.ambient (reparamLeftF
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v0 : Fin 2 → ℝ) 1))
      = γ.src
    have h_v0_0 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v0_1 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h_v0_0, h_v0_1]
    show γ.ambient (reparamLeftF 0 (0 + 0)) = γ.src
    have h_arg : (0 : ℝ) + 0 = 0 := by norm_num
    rw [h_arg, reparamLeftF_zero_right]
    exact γ.ambient_zero_eq_src
  · -- tgt: face2.tgt = T₁.toFun v1 = γ.ambient (reparamLeftF 0 1) = γ.ambient 1 = γ.tgt.
    show γ.ambient (reparamLeftF
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 0
          + (Smooth2Simplex.v1 : Fin 2 → ℝ) 1))
      = γ.tgt
    have h_v1_0 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 = 1 := rfl
    have h_v1_1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h_v1_0, h_v1_1]
    show γ.ambient (reparamLeftF 0 (1 + 0)) = γ.tgt
    have h_arg : (1 : ℝ) + 0 = 1 := by norm_num
    rw [h_arg, reparamLeftF_one_right]
    exact γ.ambient_one_eq_tgt
  · -- toPath: face2(T₁)(t) = γ.ambient(reparamLeftF 0 (t.val+0))
    --                     = γ.ambient(reparamLeftF 0 t.val) = γ.ambient(t.val) = γ.toPath t.
    intro t
    show γ.ambient (reparamLeftF
        ((Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 1)
        ((Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 0
          + (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 1))
      = γ.toPath t
    have h_p0 : (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 0
        = t.val := rfl
    have h_p1 : (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 1
        = 0 := rfl
    rw [h_p0, h_p1]
    show γ.ambient (reparamLeftF 0 (t.val + 0)) = γ.toPath t
    have h_arg : t.val + 0 = t.val := by ring
    rw [h_arg, reparamLeftF_zero_left]
    exact γ.ambient_eq_on_unitInterval t

end JacobianChallenge

end
