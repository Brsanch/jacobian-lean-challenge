/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusProjFaces
import JacobianChallenge.Manifold.SmoothPathIntegral

set_option linter.unusedSectionVars false

/-! # `face1 σ_UL = γ` for the upper-left projected straight-line simplex

The face opposite `v₁` of the upper-left triangle simplex `σ_UL :=
projUpperLeft L lift λ h_lift` is the smooth path
`t ↦ σ_UL.toFun ![0, t] = H(0, t) = mkQ (lift t)`.

If `lift` is a smooth ambient lift of a given smooth based loop `γ`
on `ℂ ⧸ L` at `0` — i.e., `mkQ (lift t) = γ.ambient t` for `t ∈ [0, 1]`
— then this face IS `γ` (as a SmoothPath, via the path-extensionality
lemma `SmoothPath.ext`).

This is the substantive face identification that closes the bordism
arc: combined with the four face identifications from
`ComplexTorusProjFaces.lean` (γ_λ on `face0 σ_LR`, const on
`face2 σ_LR` + `face0 σ_UL`, diagonal cancellation between `face1 σ_LR`
and `face2 σ_UL`), summing `∂σ_LR + ∂σ_UL` produces

```
single (torusBasisLoop λ) - single γ + 2 · single (const 0)
   ∈ image of `Smooth2Chain.boundary₂Cycle`
```

i.e., `(γ_λ - γ).singleCycle ∈ stokesBoundaries` after subtracting the
two const-singles (each of which is itself in `stokesBoundaries`).

## What this file ships

* `face1_projUpperLeft_eq` — face1 σ_UL = γ as a SmoothPath, under
  the lift-agreement hypothesis.

No `sorry`, no `axiom`. -/

open Set
open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

variable {L}

/-- **`face1 σ_UL` equals the smooth based loop `γ` it was built from**,
provided the ambient `lift` agrees with `γ.ambient` on `[0, 1]`. -/
theorem face1_projUpperLeft_eq
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L))
    (lift : ℝ → ℂ) (lam : ℂ)
    (h_lift : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ lift)
    (h_lift_zero : lift 0 = 0) (h_lift_one : lift 1 = lam) (h_lam : lam ∈ L)
    (h_γ_src : γ.src = (0 : ℂ ⧸ L)) (h_γ_tgt : γ.tgt = (0 : ℂ ⧸ L))
    (h_lift_agrees : ∀ t ∈ Set.Icc (0 : ℝ) 1, L.mkQ (lift t) = γ.ambient t) :
    Smooth2Simplex.face1 (projUpperLeft L lift lam h_lift) = γ := by
  apply SmoothPath.ext
  · -- src: σ_UL.toFun v0 = H(0, 0) = mkQ (lift 0) = mkQ 0 = 0 = γ.src.
    show (projUpperLeft L lift lam h_lift).toFun Smooth2Simplex.v0 = γ.src
    show projStraightLineMap L lift lam
        ![(Smooth2Simplex.v0 : Fin 2 → ℝ) 0,
          (Smooth2Simplex.v0 : Fin 2 → ℝ) 0 + (Smooth2Simplex.v0 : Fin 2 → ℝ) 1]
      = γ.src
    have h0 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 0 = 0 := rfl
    have h1 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h0, h1]
    have h_eq : (0 : ℝ) + 0 = 0 := by norm_num
    rw [h_eq]
    -- projStraightLineMap L lift lam ![0, 0] = mkQ (lift 0) (left_edge with t=0).
    rw [projStraightLineMap_left_edge lift lam 0, h_lift_zero, map_zero, h_γ_src]
  · -- tgt: σ_UL.toFun v2 = H(0, 1) = mkQ (lift 1) = mkQ λ = 0 = γ.tgt.
    show (projUpperLeft L lift lam h_lift).toFun Smooth2Simplex.v2 = γ.tgt
    show projStraightLineMap L lift lam
        ![(Smooth2Simplex.v2 : Fin 2 → ℝ) 0,
          (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 + (Smooth2Simplex.v2 : Fin 2 → ℝ) 1]
      = γ.tgt
    have h0 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 = 0 := rfl
    have h1 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 1 = 1 := rfl
    rw [h0, h1]
    have h_eq : (0 : ℝ) + 1 = 1 := by norm_num
    rw [h_eq]
    -- projStraightLineMap L lift lam ![0, 1] = mkQ (lift 1) (left_edge with t=1).
    rw [projStraightLineMap_left_edge lift lam 1, h_lift_one]
    rw [h_γ_tgt]
    exact (Submodule.Quotient.mk_eq_zero L).mpr h_lam
  · intro t
    -- (face1 σ_UL).toPath t = σ_UL.toFun (face1Param t.val)
    --                       = σ_UL.toFun ![0, t.val]
    --                       = projStraightLineMap L lift lam ![0, 0 + t.val]
    --                       = mkQ (lift t.val)
    --                       = γ.ambient t.val (by h_lift_agrees, t.val ∈ [0,1])
    --                       = γ.toPath t (by ambient_eq_on_unitInterval).
    show (projUpperLeft L lift lam h_lift).toFun
        (Smooth2Simplex.face1Param t.val) = γ.toPath t
    show projStraightLineMap L lift lam
        ![(Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 0,
          (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 0
            + (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 1]
      = γ.toPath t
    have h0 : (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 0 = 0 := rfl
    have h1 : (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 1 = t.val := rfl
    rw [h0, h1]
    have h_eq : (0 : ℝ) + t.val = t.val := by ring
    rw [h_eq]
    rw [projStraightLineMap_left_edge lift lam t.val]
    rw [h_lift_agrees t.val t.property]
    rw [γ.ambient_eq_on_unitInterval t]

end ComplexTorus

end JacobianChallenge

end
