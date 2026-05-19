/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusProjStraightLineMap
import JacobianChallenge.Manifold.Smooth2Simplex

set_option linter.unusedSectionVars false

/-! # Two smooth 2-simplices covering `[0, 1]²` via the projected
straight-line map on `ℂ ⧸ L`

For a smooth ambient `lift : ℝ → ℂ` and lattice element `λ ∈ L`,
`projStraightLineMap L lift λ : (Fin 2 → ℝ) → ℂ ⧸ L` is the smooth
homotopy `[0,1]² → T²` between

* `t ↦ mkQ (lift t)` (left edge, the projected ambient lift), and
* `t ↦ mkQ (t · λ)` (right edge, the torus basis loop at `λ`),

with `0` on both top and bottom edges (provided `lift 0 = 0` and
`lift 1 = λ`).

We decompose the unit square `[0, 1]²` into two triangles via the
diagonal `(0,0) → (1,1)`:

* **Lower-right** with vertices `(0,0), (1,0), (1,1)` —
  parameterised `Δ² ∋ (u, v) ↦ (u + v, v) ∈ [0,1]²`.
* **Upper-left** with vertices `(0,0), (1,1), (0,1)` —
  parameterised `Δ² ∋ (u, v) ↦ (u, u + v) ∈ [0,1]²`.

Composing each with `projStraightLineMap` gives two
`Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)`.

## What this file ships

* `ComplexTorus.projLowerRight L lift lam h_lift` — the lower-right
  triangle 2-simplex.
* `ComplexTorus.projUpperLeft L lift lam h_lift` — the upper-left
  triangle 2-simplex.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Smoothness of the two triangle reparams -/

/-- `(x : Fin 2 → ℝ) ↦ x i` is `C^∞`. -/
private lemma contMDiff_proj_fin2_local (i : Fin 2) :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞ (fun x : Fin 2 → ℝ => x i) := by
  have h_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Fin 2 → ℝ => x i) :=
    (ContinuousLinearMap.proj i : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff
  exact h_cd.contMDiff

/-- The lower-right reparam `Δ² ∋ (u, v) ↦ (u + v, v)`, as a smooth
map `(Fin 2 → ℝ) → (Fin 2 → ℝ)`. -/
private lemma contMDiff_reparamLR :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞
      (fun x : Fin 2 → ℝ => ![x 0 + x 1, x 1]) := by
  rw [contMDiff_pi_space]
  intro i
  fin_cases i
  · have h_eq : (fun x : Fin 2 → ℝ => (![x 0 + x 1, x 1] : Fin 2 → ℝ) 0)
              = fun x : Fin 2 → ℝ => x 0 + x 1 := by
      funext; rfl
    show ContMDiff _ _ ∞ (fun x : Fin 2 → ℝ => (![x 0 + x 1, x 1] : Fin 2 → ℝ) 0)
    rw [h_eq]
    exact (contMDiff_proj_fin2_local 0).add (contMDiff_proj_fin2_local 1)
  · have h_eq : (fun x : Fin 2 → ℝ => (![x 0 + x 1, x 1] : Fin 2 → ℝ) 1)
              = fun x : Fin 2 → ℝ => x 1 := by
      funext; rfl
    show ContMDiff _ _ ∞ (fun x : Fin 2 → ℝ => (![x 0 + x 1, x 1] : Fin 2 → ℝ) 1)
    rw [h_eq]
    exact contMDiff_proj_fin2_local 1

/-- The upper-left reparam `Δ² ∋ (u, v) ↦ (u, u + v)`, as a smooth
map `(Fin 2 → ℝ) → (Fin 2 → ℝ)`. -/
private lemma contMDiff_reparamUL :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞
      (fun x : Fin 2 → ℝ => ![x 0, x 0 + x 1]) := by
  rw [contMDiff_pi_space]
  intro i
  fin_cases i
  · have h_eq : (fun x : Fin 2 → ℝ => (![x 0, x 0 + x 1] : Fin 2 → ℝ) 0)
              = fun x : Fin 2 → ℝ => x 0 := by
      funext; rfl
    show ContMDiff _ _ ∞ (fun x : Fin 2 → ℝ => (![x 0, x 0 + x 1] : Fin 2 → ℝ) 0)
    rw [h_eq]
    exact contMDiff_proj_fin2_local 0
  · have h_eq : (fun x : Fin 2 → ℝ => (![x 0, x 0 + x 1] : Fin 2 → ℝ) 1)
              = fun x : Fin 2 → ℝ => x 0 + x 1 := by
      funext; rfl
    show ContMDiff _ _ ∞ (fun x : Fin 2 → ℝ => (![x 0, x 0 + x 1] : Fin 2 → ℝ) 1)
    rw [h_eq]
    exact (contMDiff_proj_fin2_local 0).add (contMDiff_proj_fin2_local 1)

/-! ## The two simplices -/

/-- **Lower-right triangle 2-simplex** over `projStraightLineMap`.
Composes `H := projStraightLineMap L lift λ` with the
parameterisation `Δ² ∋ (u, v) ↦ (u + v, v) ∈ [0, 1]²`. -/
noncomputable def projLowerRight
    (lift : ℝ → ℂ) (lam : ℂ)
    (h_lift : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ lift) :
    Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L) where
  toFun := fun x : Fin 2 → ℝ =>
    projStraightLineMap L lift lam ![x 0 + x 1, x 1]
  smooth := (projStraightLineMap_contMDiff L lift lam h_lift).comp contMDiff_reparamLR

/-- **Upper-left triangle 2-simplex** over `projStraightLineMap`.
Composes `H := projStraightLineMap L lift λ` with the
parameterisation `Δ² ∋ (u, v) ↦ (u, u + v) ∈ [0, 1]²`. -/
noncomputable def projUpperLeft
    (lift : ℝ → ℂ) (lam : ℂ)
    (h_lift : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ lift) :
    Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L) where
  toFun := fun x : Fin 2 → ℝ =>
    projStraightLineMap L lift lam ![x 0, x 0 + x 1]
  smooth := (projStraightLineMap_contMDiff L lift lam h_lift).comp contMDiff_reparamUL

end ComplexTorus

end JacobianChallenge

end
