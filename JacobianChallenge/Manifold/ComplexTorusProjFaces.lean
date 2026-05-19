/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusProjSimplices
import JacobianChallenge.Manifold.SmoothPathExt
import JacobianChallenge.Manifold.SmoothPathConst

set_option linter.unusedSectionVars false

/-! # Face identifications of the projected straight-line 2-simplices on `ℂ ⧸ L`

For the lower-right and upper-left triangle 2-simplices

* `σ_LR := projLowerRight L lift λ h_lift`,
* `σ_UL := projUpperLeft  L lift λ h_lift`,

with `lift 0 = 0` and `lift 1 = λ ∈ L`, the six boundary faces
identify as:

* `face0 σ_LR = torusBasisLoop λ` (right edge of `[0,1]²`),
* `face2 σ_LR = SmoothPath.const _ _ 0` (bottom edge),
* `face1 σ_LR` = the **diagonal** path `t ↦ mkQ ((1-t)·lift t + t²·λ)`,
* `face0 σ_UL = SmoothPath.const _ _ 0` (top edge),
* `face1 σ_UL` = the **projected lift path** `t ↦ mkQ (lift t)`,
* `face2 σ_UL = face1 σ_LR` (same diagonal path),

so summing `∂σ_LR + ∂σ_UL` cancels the diagonal and leaves
`single (torusBasisLoop λ) - single (projected-lift-path) + 2 · single const`.

This file ships:

* `face0_projLowerRight_eq_torusBasisLoop` — `face0 σ_LR = torusBasisLoop λ`.
* `face2_projLowerRight_eq_const` — `face2 σ_LR = SmoothPath.const _ _ 0`.
* `face0_projUpperLeft_eq_const` — `face0 σ_UL = SmoothPath.const _ _ 0`.
* `face2_projUpperLeft_eq_face1_projLowerRight` — diagonal cancellation.

The remaining identification — `face1 σ_UL = γ` (the original loop) — is
deferred to a successor chip (it requires the lift-identity hypothesis
`mkQ ∘ lift = γ.ambient on [0, 1]`).

No `sorry`, no `axiom`. -/

open Set
open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

variable {L}

/-! ## `face0 σ_LR = torusBasisLoop λ` (right edge of `[0,1]²`) -/

/-- **The face opposite `v₀` of `projLowerRight` equals `torusBasisLoop λ`.**

`face0 σ_LR` is the path `t ↦ σ_LR(face0Param t) = σ_LR(1-t, t)
= H((1-t)+t, t) = H(1, t)`, which equals `mkQ(t • λ)` by the right-edge
identity of `projStraightLineMap`. -/
theorem face0_projLowerRight_eq_torusBasisLoop
    (lift : ℝ → ℂ) (lam : ℂ)
    (h_lift : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ lift)
    (h_lift_zero : lift 0 = 0) (h_lift_one : lift 1 = lam) (h_lam : lam ∈ L) :
    Smooth2Simplex.face0 (projLowerRight L lift lam h_lift)
      = torusBasisLoop lam h_lam := by
  apply SmoothPath.ext
  · -- src: σ_LR.toFun v1 = projStraightLineMap L lift lam ![1+0, 0]
    --                    = projStraightLineMap L lift lam ![1, 0] = 0 (bottom_edge).
    show (projLowerRight L lift lam h_lift).toFun Smooth2Simplex.v1
      = (torusBasisLoop lam h_lam).src
    show projStraightLineMap L lift lam
        ![(Smooth2Simplex.v1 : Fin 2 → ℝ) 0 + (Smooth2Simplex.v1 : Fin 2 → ℝ) 1,
          (Smooth2Simplex.v1 : Fin 2 → ℝ) 1] = (0 : ℂ ⧸ L)
    have h0 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 = 1 := rfl
    have h1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h0, h1]
    have h_eq : (1 : ℝ) + 0 = 1 := by norm_num
    rw [h_eq]
    exact projStraightLineMap_bottom_edge lift lam h_lift_zero 1
  · -- tgt: σ_LR.toFun v2 = projStraightLineMap L lift lam ![0+1, 1]
    --                    = projStraightLineMap L lift lam ![1, 1] = 0 (top_edge).
    show (projLowerRight L lift lam h_lift).toFun Smooth2Simplex.v2
      = (torusBasisLoop lam h_lam).tgt
    show projStraightLineMap L lift lam
        ![(Smooth2Simplex.v2 : Fin 2 → ℝ) 0 + (Smooth2Simplex.v2 : Fin 2 → ℝ) 1,
          (Smooth2Simplex.v2 : Fin 2 → ℝ) 1] = (0 : ℂ ⧸ L)
    have h0 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 = 0 := rfl
    have h1 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 1 = 1 := rfl
    rw [h0, h1]
    have h_eq : (0 : ℝ) + 1 = 1 := by norm_num
    rw [h_eq]
    exact projStraightLineMap_top_edge lift lam h_lift_one h_lam 1
  · intro t
    -- Both LHS and RHS evaluate at t.val ∈ [0, 1].
    -- LHS: σ_LR(face0Param t.val) = σ_LR(1-t.val, t.val) = H(1, t.val) = mkQ(t.val • lam).
    -- RHS: mkQ((t.val : ℂ) * lam).
    show (projLowerRight L lift lam h_lift).toFun
        (Smooth2Simplex.face0Param t.val) = (torusBasisLoop lam h_lam).toPath t
    show projStraightLineMap L lift lam
        ![(Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0
            + (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1,
          (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1]
      = L.mkQ (((t.val : ℝ) : ℂ) * lam)
    have h0 : (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0 = 1 - t.val := rfl
    have h1 : (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1 = t.val := rfl
    rw [h0, h1]
    have h_eq : (1 - t.val) + t.val = (1 : ℝ) := by ring
    rw [h_eq]
    -- Now we have projStraightLineMap L lift lam ![1, t.val] = mkQ ((t.val : ℂ) * lam).
    -- mkQ (t.val • lam) = mkQ ((t.val : ℂ) * lam) by `Complex.real_smul`, which `congr 1`
    -- + defeq closes.
    rw [projStraightLineMap_right_edge lift lam t.val]
    congr 1

/-! ## `face2 σ_LR = SmoothPath.const _ _ 0` (bottom edge of `[0,1]²`) -/

/-- **The face opposite `v₂` of `projLowerRight` is the constant loop at `0`.**

`face2 σ_LR` is the path `t ↦ σ_LR(face2Param t) = σ_LR(t, 0)
= H(t+0, 0) = H(t, 0)`, which equals `0` by the bottom-edge identity. -/
theorem face2_projLowerRight_eq_const
    (lift : ℝ → ℂ) (lam : ℂ)
    (h_lift : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ lift)
    (h_lift_zero : lift 0 = 0) :
    Smooth2Simplex.face2 (projLowerRight L lift lam h_lift)
      = SmoothPath.const 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L) := by
  apply SmoothPath.ext
  · show (projLowerRight L lift lam h_lift).toFun Smooth2Simplex.v0
      = (SmoothPath.const 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L)).src
    show projStraightLineMap L lift lam
        ![(Smooth2Simplex.v0 : Fin 2 → ℝ) 0 + (Smooth2Simplex.v0 : Fin 2 → ℝ) 1,
          (Smooth2Simplex.v0 : Fin 2 → ℝ) 1] = (0 : ℂ ⧸ L)
    have h0 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 0 = 0 := rfl
    have h1 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h0, h1]
    have h_eq : (0 : ℝ) + 0 = 0 := by norm_num
    rw [h_eq]
    exact projStraightLineMap_bottom_edge lift lam h_lift_zero 0
  · show (projLowerRight L lift lam h_lift).toFun Smooth2Simplex.v1
      = (SmoothPath.const 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L)).tgt
    show projStraightLineMap L lift lam
        ![(Smooth2Simplex.v1 : Fin 2 → ℝ) 0 + (Smooth2Simplex.v1 : Fin 2 → ℝ) 1,
          (Smooth2Simplex.v1 : Fin 2 → ℝ) 1] = (0 : ℂ ⧸ L)
    have h0 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 = 1 := rfl
    have h1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h0, h1]
    have h_eq : (1 : ℝ) + 0 = 1 := by norm_num
    rw [h_eq]
    exact projStraightLineMap_bottom_edge lift lam h_lift_zero 1
  · intro t
    show (projLowerRight L lift lam h_lift).toFun
        (Smooth2Simplex.face2Param t.val)
      = (SmoothPath.const 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L)).toPath t
    show projStraightLineMap L lift lam
        ![(Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 0
            + (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 1,
          (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 1] = (0 : ℂ ⧸ L)
    have h0 : (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 0 = t.val := rfl
    have h1 : (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h0, h1]
    have h_eq : (t.val : ℝ) + 0 = t.val := by ring
    rw [h_eq]
    exact projStraightLineMap_bottom_edge lift lam h_lift_zero t.val

/-! ## `face0 σ_UL = SmoothPath.const _ _ 0` (top edge of `[0,1]²`) -/

/-- **The face opposite `v₀` of `projUpperLeft` is the constant loop at `0`.**

`face0 σ_UL` is the path `t ↦ σ_UL(face0Param t) = σ_UL(1-t, t)
= H(1-t, (1-t)+t) = H(1-t, 1)`, which equals `0` by the top-edge
identity (using `lam ∈ L`). -/
theorem face0_projUpperLeft_eq_const
    (lift : ℝ → ℂ) (lam : ℂ)
    (h_lift : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ lift)
    (h_lift_one : lift 1 = lam) (h_lam : lam ∈ L) :
    Smooth2Simplex.face0 (projUpperLeft L lift lam h_lift)
      = SmoothPath.const 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L) := by
  apply SmoothPath.ext
  · show (projUpperLeft L lift lam h_lift).toFun Smooth2Simplex.v1
      = (SmoothPath.const 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L)).src
    show projStraightLineMap L lift lam
        ![(Smooth2Simplex.v1 : Fin 2 → ℝ) 0,
          (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 + (Smooth2Simplex.v1 : Fin 2 → ℝ) 1]
      = (0 : ℂ ⧸ L)
    have h0 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 = 1 := rfl
    have h1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h0, h1]
    have h_eq : (1 : ℝ) + 0 = 1 := by norm_num
    rw [h_eq]
    exact projStraightLineMap_top_edge lift lam h_lift_one h_lam 1
  · show (projUpperLeft L lift lam h_lift).toFun Smooth2Simplex.v2
      = (SmoothPath.const 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L)).tgt
    show projStraightLineMap L lift lam
        ![(Smooth2Simplex.v2 : Fin 2 → ℝ) 0,
          (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 + (Smooth2Simplex.v2 : Fin 2 → ℝ) 1]
      = (0 : ℂ ⧸ L)
    have h0 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 = 0 := rfl
    have h1 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 1 = 1 := rfl
    rw [h0, h1]
    have h_eq : (0 : ℝ) + 1 = 1 := by norm_num
    rw [h_eq]
    exact projStraightLineMap_top_edge lift lam h_lift_one h_lam 0
  · intro t
    show (projUpperLeft L lift lam h_lift).toFun
        (Smooth2Simplex.face0Param t.val)
      = (SmoothPath.const 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L)).toPath t
    show projStraightLineMap L lift lam
        ![(Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0,
          (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0
            + (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1] = (0 : ℂ ⧸ L)
    have h0 : (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0 = 1 - t.val := rfl
    have h1 : (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1 = t.val := rfl
    rw [h0, h1]
    have h_eq : (1 - t.val) + t.val = (1 : ℝ) := by ring
    rw [h_eq]
    exact projStraightLineMap_top_edge lift lam h_lift_one h_lam (1 - t.val)

/-! ## Diagonal cancellation: `face2 σ_UL = face1 σ_LR` -/

/-- **The diagonal faces of `σ_LR` and `σ_UL` agree as smooth paths.**

`face1 σ_LR(t) = σ_LR(0, t) = H(0+t, t) = H(t, t)`,
`face2 σ_UL(t) = σ_UL(t, 0) = H(t, t+0) = H(t, t)`. -/
theorem face2_projUpperLeft_eq_face1_projLowerRight
    (lift : ℝ → ℂ) (lam : ℂ)
    (h_lift : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ lift) :
    Smooth2Simplex.face2 (projUpperLeft L lift lam h_lift)
      = Smooth2Simplex.face1 (projLowerRight L lift lam h_lift) := by
  apply SmoothPath.ext
  · show (projUpperLeft L lift lam h_lift).toFun Smooth2Simplex.v0
      = (projLowerRight L lift lam h_lift).toFun Smooth2Simplex.v0
    show projStraightLineMap L lift lam
        ![(Smooth2Simplex.v0 : Fin 2 → ℝ) 0,
          (Smooth2Simplex.v0 : Fin 2 → ℝ) 0 + (Smooth2Simplex.v0 : Fin 2 → ℝ) 1]
      = projStraightLineMap L lift lam
        ![(Smooth2Simplex.v0 : Fin 2 → ℝ) 0 + (Smooth2Simplex.v0 : Fin 2 → ℝ) 1,
          (Smooth2Simplex.v0 : Fin 2 → ℝ) 1]
    -- v0 = ![0, 0]. Both reduce to projStraightLineMap L lift lam ![0, 0].
    have h0 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 0 = 0 := rfl
    have h1 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h0, h1]
    have h_eq : (0 : ℝ) + 0 = 0 := by norm_num
    rw [h_eq]
  · show (projUpperLeft L lift lam h_lift).toFun Smooth2Simplex.v1
      = (projLowerRight L lift lam h_lift).toFun Smooth2Simplex.v2
    show projStraightLineMap L lift lam
        ![(Smooth2Simplex.v1 : Fin 2 → ℝ) 0,
          (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 + (Smooth2Simplex.v1 : Fin 2 → ℝ) 1]
      = projStraightLineMap L lift lam
        ![(Smooth2Simplex.v2 : Fin 2 → ℝ) 0 + (Smooth2Simplex.v2 : Fin 2 → ℝ) 1,
          (Smooth2Simplex.v2 : Fin 2 → ℝ) 1]
    -- v1 = ![1, 0], v2 = ![0, 1]. Both reduce to projStraightLineMap L lift lam ![1, 1].
    have h0_v1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 = 1 := rfl
    have h1_v1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 1 = 0 := rfl
    have h0_v2 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 = 0 := rfl
    have h1_v2 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 1 = 1 := rfl
    rw [h0_v1, h1_v1, h0_v2, h1_v2]
    have h_eq1 : (1 : ℝ) + 0 = 1 := by norm_num
    have h_eq2 : (0 : ℝ) + 1 = 1 := by norm_num
    rw [h_eq1, h_eq2]
  · intro t
    show (projUpperLeft L lift lam h_lift).toFun
        (Smooth2Simplex.face2Param t.val)
      = (projLowerRight L lift lam h_lift).toFun
        (Smooth2Simplex.face1Param t.val)
    show projStraightLineMap L lift lam
        ![(Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 0,
          (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 0
            + (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 1]
      = projStraightLineMap L lift lam
        ![(Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 0
            + (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 1,
          (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 1]
    have h0_f2 : (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 0 = t.val := rfl
    have h1_f2 : (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 1 = 0 := rfl
    have h0_f1 : (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 0 = 0 := rfl
    have h1_f1 : (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 1 = t.val := rfl
    rw [h0_f2, h1_f2, h0_f1, h1_f1]
    have h_eq1 : (t.val : ℝ) + 0 = t.val := by ring
    have h_eq2 : (0 : ℝ) + t.val = t.val := by ring
    rw [h_eq1, h_eq2]

end ComplexTorus

end JacobianChallenge

end
