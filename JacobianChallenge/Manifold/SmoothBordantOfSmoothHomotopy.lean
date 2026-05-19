/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothBordismAndWordRepresentative
import JacobianChallenge.Manifold.Smooth2SimplexFromPath
import JacobianChallenge.Manifold.SmoothPathConstFromFace0

set_option linter.unusedSectionVars false

/-! # Smooth bordism from a smooth homotopy of based loops

For two smooth based loops `γ₀, γ₁ : BasedLoopAt 𝓘(ℝ, ℂ) X p₀`, a
**smooth homotopy** is a smooth map `H : ℝ² → X` (via the `Fin 2 → ℝ`
pi-manifold model) with:

* `H(0, t) = γ₀(t)` for `t ∈ [0, 1]`  (left edge = γ₀);
* `H(1, t) = γ₁(t)` for `t ∈ [0, 1]`  (right edge = γ₁);
* `H(s, 0) = p₀`                       (bottom edge constant at `p₀`);
* `H(s, 1) = p₀`                       (top edge constant at `p₀`).

This file shows that **the existence of a smooth homotopy implies
`SmoothBordant γ₀ γ₁`** — concrete geometric content discharging the
"bordism" sub-hypothesis of the smooth-Hurewicz arc.

## Construction

Divide the unit square `[0,1]²` into two standard 2-simplices via the
diagonal `(0,0) → (1,1)`:

* **Lower-right triangle** with vertices `(0,0), (1,0), (1,1)`,
  parameterised by `Δ² ∋ (s, t) ↦ (s + t, t) ∈ [0,1]²`.
* **Upper-left triangle** with vertices `(0,0), (1,1), (0,1)`,
  parameterised by `Δ² ∋ (s, t) ↦ (s, s + t) ∈ [0,1]²`.

Composing each with `H` gives `Smooth2Simplex 𝓘(ℝ, ℂ) X` instances
`σ_LR` and `σ_UL`. Their boundary, as a `Smooth2Chain`, computes to:

```
∂(σ_LR + σ_UL)
  = (γ₁ - D + const p₀) + (const p₀ - γ₀ + D)
  = single γ₁ - single γ₀ + 2 · single (const p₀)
```

where `D : t ↦ H(t, t)` is the diagonal (which cancels). Since
`single (const p₀) ∈ stokesBoundaries`, the `2 · single (const p₀)`
term lies in `stokesBoundaries`. Subtracting gives
`single γ₁ - single γ₀ ∈ stokesBoundaries`, i.e., `SmoothBordant γ₀ γ₁`
(by `SmoothBordant.symm`).

## What this file ships

* `SmoothHomotopyBasedLoop p₀ γ₀ γ₁` — structure bundling the smooth
  map `H : (Fin 2 → ℝ) → X` with the four edge conditions.
* `smoothBordant_of_smoothHomotopy` — the geometric content discharge:
  existence of a smooth homotopy gives `SmoothBordant γ₀ γ₁`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-! ## Smoothness of `Fin 2 → ℝ` coordinate projections and reparams -/

/-- `(x : Fin 2 → ℝ) ↦ x i` is `C^∞` for each `i`. -/
private lemma contMDiff_proj_fin2 (i : Fin 2) :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞ (fun x : Fin 2 → ℝ => x i) := by
  have h_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Fin 2 → ℝ => x i) :=
    (ContinuousLinearMap.proj i : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff
  exact h_cd.contMDiff

/-- The reparam `(x 0, x 1) ↦ (x 0 + x 1, x 1)` is `C^∞`
on `Fin 2 → ℝ`. -/
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
    exact (contMDiff_proj_fin2 0).add (contMDiff_proj_fin2 1)
  · have h_eq : (fun x : Fin 2 → ℝ => (![x 0 + x 1, x 1] : Fin 2 → ℝ) 1)
              = fun x : Fin 2 → ℝ => x 1 := by
      funext; rfl
    show ContMDiff _ _ ∞ (fun x : Fin 2 → ℝ => (![x 0 + x 1, x 1] : Fin 2 → ℝ) 1)
    rw [h_eq]
    exact contMDiff_proj_fin2 1

/-- The reparam `(x 0, x 1) ↦ (x 0, x 0 + x 1)` is `C^∞`
on `Fin 2 → ℝ`. -/
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
    exact contMDiff_proj_fin2 0
  · have h_eq : (fun x : Fin 2 → ℝ => (![x 0, x 0 + x 1] : Fin 2 → ℝ) 1)
              = fun x : Fin 2 → ℝ => x 0 + x 1 := by
      funext; rfl
    show ContMDiff _ _ ∞ (fun x : Fin 2 → ℝ => (![x 0, x 0 + x 1] : Fin 2 → ℝ) 1)
    rw [h_eq]
    exact (contMDiff_proj_fin2 0).add (contMDiff_proj_fin2 1)

/-! ## `SmoothHomotopyBasedLoop` structure -/

/-- **A smooth homotopy between two based loops at `p₀`.** -/
structure SmoothHomotopyBasedLoop {p₀ : X}
    (γ₀ γ₁ : BasedLoopAt 𝓘(ℝ, ℂ) X p₀) where
  /-- Ambient smooth extension to `Fin 2 → ℝ`. -/
  toFun : (Fin 2 → ℝ) → X
  /-- Smoothness witness. -/
  smooth : ContMDiff (𝓘(ℝ, Fin 2 → ℝ)) (𝓘(ℝ, ℂ)) ∞ toFun
  /-- Left edge (`s = 0`) equals `γ₀.toPath.ambient`. -/
  left_edge : ∀ t : ℝ, toFun ![0, t] = γ₀.toPath.ambient t
  /-- Right edge (`s = 1`) equals `γ₁.toPath.ambient`. -/
  right_edge : ∀ t : ℝ, toFun ![1, t] = γ₁.toPath.ambient t
  /-- Bottom edge (`t = 0`) constant at `p₀`. -/
  bottom_edge : ∀ s : ℝ, toFun ![s, 0] = p₀
  /-- Top edge (`t = 1`) constant at `p₀`. -/
  top_edge : ∀ s : ℝ, toFun ![s, 1] = p₀

namespace SmoothHomotopyBasedLoop

variable {p₀ : X} {γ₀ γ₁ : BasedLoopAt 𝓘(ℝ, ℂ) X p₀}

/-! ## The two triangle 2-simplexes covering the unit square -/

/-- **Lower-right triangle 2-simplex.** Parameterised
`Δ² ∋ (s, t) ↦ (s + t, t) ∈ [0,1]²`. Vertices map to:
`v₀ = (0,0) ↦ (0,0) ↦ H(0,0) = p₀`,
`v₁ = (1,0) ↦ (1,0) ↦ H(1,0) = p₀`,
`v₂ = (0,1) ↦ (1,1) ↦ H(1,1) = p₀`. -/
noncomputable def lowerRightSimplex (H : SmoothHomotopyBasedLoop γ₀ γ₁) :
    Smooth2Simplex 𝓘(ℝ, ℂ) X where
  toFun := fun x : Fin 2 → ℝ => H.toFun ![x 0 + x 1, x 1]
  smooth := H.smooth.comp contMDiff_reparamLR

/-- **Upper-left triangle 2-simplex.** Parameterised
`Δ² ∋ (s, t) ↦ (s, s + t) ∈ [0,1]²`. Vertices map to:
`v₀ = (0,0) ↦ (0,0) ↦ H(0,0) = p₀`,
`v₁ = (1,0) ↦ (1,1) ↦ H(1,1) = p₀`,
`v₂ = (0,1) ↦ (0,1) ↦ H(0,1) = p₀`. -/
noncomputable def upperLeftSimplex (H : SmoothHomotopyBasedLoop γ₀ γ₁) :
    Smooth2Simplex 𝓘(ℝ, ℂ) X where
  toFun := fun x : Fin 2 → ℝ => H.toFun ![x 0, x 0 + x 1]
  smooth := H.smooth.comp contMDiff_reparamUL

/-! ## Vertex-of-simplex evaluations (all four corners of [0,1]² hit p₀) -/

@[simp] lemma lowerRightSimplex_v0 (H : SmoothHomotopyBasedLoop γ₀ γ₁) :
    (H.lowerRightSimplex).toFun (Smooth2Simplex.v0 : Fin 2 → ℝ) = p₀ := by
  show H.toFun ![Smooth2Simplex.v0 0 + Smooth2Simplex.v0 1, Smooth2Simplex.v0 1] = p₀
  have h0 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 0 = 0 := rfl
  have h1 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 1 = 0 := rfl
  rw [h0, h1]
  change H.toFun ![0 + 0, 0] = p₀
  have : (0 : ℝ) + 0 = 0 := by norm_num
  rw [this]
  exact H.bottom_edge 0

@[simp] lemma lowerRightSimplex_v1 (H : SmoothHomotopyBasedLoop γ₀ γ₁) :
    (H.lowerRightSimplex).toFun (Smooth2Simplex.v1 : Fin 2 → ℝ) = p₀ := by
  show H.toFun ![Smooth2Simplex.v1 0 + Smooth2Simplex.v1 1, Smooth2Simplex.v1 1] = p₀
  have h0 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 = 1 := rfl
  have h1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 1 = 0 := rfl
  rw [h0, h1]
  change H.toFun ![1 + 0, 0] = p₀
  have : (1 : ℝ) + 0 = 1 := by norm_num
  rw [this]
  exact H.bottom_edge 1

@[simp] lemma lowerRightSimplex_v2 (H : SmoothHomotopyBasedLoop γ₀ γ₁) :
    (H.lowerRightSimplex).toFun (Smooth2Simplex.v2 : Fin 2 → ℝ) = p₀ := by
  show H.toFun ![Smooth2Simplex.v2 0 + Smooth2Simplex.v2 1, Smooth2Simplex.v2 1] = p₀
  have h0 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 = 0 := rfl
  have h1 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 1 = 1 := rfl
  rw [h0, h1]
  change H.toFun ![0 + 1, 1] = p₀
  have : (0 : ℝ) + 1 = 1 := by norm_num
  rw [this]
  exact H.top_edge 1

@[simp] lemma upperLeftSimplex_v0 (H : SmoothHomotopyBasedLoop γ₀ γ₁) :
    (H.upperLeftSimplex).toFun (Smooth2Simplex.v0 : Fin 2 → ℝ) = p₀ := by
  show H.toFun ![Smooth2Simplex.v0 0, Smooth2Simplex.v0 0 + Smooth2Simplex.v0 1] = p₀
  have h0 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 0 = 0 := rfl
  have h1 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 1 = 0 := rfl
  rw [h0, h1]
  change H.toFun ![0, 0 + 0] = p₀
  have : (0 : ℝ) + 0 = 0 := by norm_num
  rw [this]
  exact H.bottom_edge 0

@[simp] lemma upperLeftSimplex_v1 (H : SmoothHomotopyBasedLoop γ₀ γ₁) :
    (H.upperLeftSimplex).toFun (Smooth2Simplex.v1 : Fin 2 → ℝ) = p₀ := by
  show H.toFun ![Smooth2Simplex.v1 0, Smooth2Simplex.v1 0 + Smooth2Simplex.v1 1] = p₀
  have h0 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 = 1 := rfl
  have h1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 1 = 0 := rfl
  rw [h0, h1]
  change H.toFun ![1, 1 + 0] = p₀
  have : (1 : ℝ) + 0 = 1 := by norm_num
  rw [this]
  exact H.top_edge 1

@[simp] lemma upperLeftSimplex_v2 (H : SmoothHomotopyBasedLoop γ₀ γ₁) :
    (H.upperLeftSimplex).toFun (Smooth2Simplex.v2 : Fin 2 → ℝ) = p₀ := by
  show H.toFun ![Smooth2Simplex.v2 0, Smooth2Simplex.v2 0 + Smooth2Simplex.v2 1] = p₀
  have h0 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 = 0 := rfl
  have h1 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 1 = 1 := rfl
  rw [h0, h1]
  change H.toFun ![0, 0 + 1] = p₀
  have : (0 : ℝ) + 1 = 1 := by norm_num
  rw [this]
  exact H.top_edge 0

/-! ## Face identifications

Each of the 6 faces (3 per triangle) identifies with one of:
- γ₀ (the left edge),
- γ₁ (the right edge),
- the constant loop at p₀ (the top/bottom edges),
- the "diagonal" path `t ↦ H(t, t)` (appears twice with opposite signs,
  so cancels in the boundary sum).

We prove the six identifications. -/

/-- Auxiliary: the diagonal-path 1-simplex `t ↦ H(t, t)`, as a smooth
path from `p₀` to `p₀`. -/
noncomputable def diagonalPath (H : SmoothHomotopyBasedLoop γ₀ γ₁) :
    SmoothPath 𝓘(ℝ, ℂ) X where
  src := p₀
  tgt := p₀
  toPath := {
    toFun := fun t : unitInterval => H.toFun ![t.val, t.val]
    continuous_toFun := by
      have h_cont : Continuous fun t : ℝ => H.toFun ![t, t] := by
        have h_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
            (fun t : ℝ => H.toFun ![t, t]) := by
          have h_diag : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞
              (fun t : ℝ => (![t, t] : Fin 2 → ℝ)) := by
            rw [contMDiff_pi_space]
            intro i
            fin_cases i
            · have h_eq : (fun t : ℝ => (![t, t] : Fin 2 → ℝ) 0)
                        = fun t : ℝ => t := by funext; rfl
              show ContMDiff _ _ ∞ (fun t : ℝ => (![t, t] : Fin 2 → ℝ) 0)
              rw [h_eq]; exact contMDiff_id
            · have h_eq : (fun t : ℝ => (![t, t] : Fin 2 → ℝ) 1)
                        = fun t : ℝ => t := by funext; rfl
              show ContMDiff _ _ ∞ (fun t : ℝ => (![t, t] : Fin 2 → ℝ) 1)
              rw [h_eq]; exact contMDiff_id
          exact H.smooth.comp h_diag
        exact h_smooth.continuous
      exact h_cont.comp continuous_subtype_val
    source' := by
      show H.toFun ![(0 : unitInterval).val, (0 : unitInterval).val] = p₀
      change H.toFun ![(0 : ℝ), 0] = p₀
      exact H.bottom_edge 0
    target' := by
      show H.toFun ![(1 : unitInterval).val, (1 : unitInterval).val] = p₀
      change H.toFun ![(1 : ℝ), 1] = p₀
      exact H.top_edge 1
  }
  smooth := by
    refine ⟨fun t : ℝ => H.toFun ![t, t], ?_, ?_⟩
    · have h_diag : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞
          (fun t : ℝ => (![t, t] : Fin 2 → ℝ)) := by
        rw [contMDiff_pi_space]
        intro i
        fin_cases i
        · have h_eq : (fun t : ℝ => (![t, t] : Fin 2 → ℝ) 0)
                    = fun t : ℝ => t := by funext; rfl
          show ContMDiff _ _ ∞ (fun t : ℝ => (![t, t] : Fin 2 → ℝ) 0)
          rw [h_eq]; exact contMDiff_id
        · have h_eq : (fun t : ℝ => (![t, t] : Fin 2 → ℝ) 1)
                    = fun t : ℝ => t := by funext; rfl
          show ContMDiff _ _ ∞ (fun t : ℝ => (![t, t] : Fin 2 → ℝ) 1)
          rw [h_eq]; exact contMDiff_id
      exact H.smooth.comp h_diag
    · intro t; rfl

/-! ## Face identifications -/

/-- **face0 of `lowerRightSimplex H` equals `γ₁.toPath`** as a
SmoothPath. Both go p₀ → p₀ via t ↦ H(1, t) = γ₁.toPath.ambient t. -/
lemma face0_lowerRightSimplex_eq (H : SmoothHomotopyBasedLoop γ₀ γ₁) :
    Smooth2Simplex.face0 H.lowerRightSimplex = γ₁.toPath := by
  apply SmoothPath.ext
  · show H.lowerRightSimplex.toFun (Smooth2Simplex.v1 : Fin 2 → ℝ) = γ₁.toPath.src
    rw [lowerRightSimplex_v1]
    exact (γ₁.toPath_src).symm
  · show H.lowerRightSimplex.toFun (Smooth2Simplex.v2 : Fin 2 → ℝ) = γ₁.toPath.tgt
    rw [lowerRightSimplex_v2]
    exact (γ₁.toPath_tgt).symm
  · intro t
    show H.toFun ![(Smooth2Simplex.face0Param t.val) 0
                    + (Smooth2Simplex.face0Param t.val) 1,
                   (Smooth2Simplex.face0Param t.val) 1] = γ₁.toPath.toPath t
    have h0 : (Smooth2Simplex.face0Param t.val) 0 = 1 - t.val := rfl
    have h1 : (Smooth2Simplex.face0Param t.val) 1 = t.val := rfl
    rw [h0, h1]
    have h_sum : (1 - t.val) + t.val = 1 := by ring
    rw [h_sum]
    rw [H.right_edge t.val]
    exact γ₁.toPath.ambient_eq_on_unitInterval t

/-- **face2 of `lowerRightSimplex H` equals `const p₀`.** Both are
constant at `p₀`: t ↦ H(t, 0) = p₀ by the bottom edge. -/
lemma face2_lowerRightSimplex_eq (H : SmoothHomotopyBasedLoop γ₀ γ₁) :
    Smooth2Simplex.face2 H.lowerRightSimplex = SmoothPath.const 𝓘(ℝ, ℂ) X p₀ := by
  apply SmoothPath.ext
  · show H.lowerRightSimplex.toFun (Smooth2Simplex.v0 : Fin 2 → ℝ)
        = (SmoothPath.const 𝓘(ℝ, ℂ) X p₀).src
    rw [lowerRightSimplex_v0, SmoothPath.const_src]
  · show H.lowerRightSimplex.toFun (Smooth2Simplex.v1 : Fin 2 → ℝ)
        = (SmoothPath.const 𝓘(ℝ, ℂ) X p₀).tgt
    rw [lowerRightSimplex_v1, SmoothPath.const_tgt]
  · intro t
    show H.toFun ![(Smooth2Simplex.face2Param t.val) 0
                    + (Smooth2Simplex.face2Param t.val) 1,
                   (Smooth2Simplex.face2Param t.val) 1]
        = (SmoothPath.const 𝓘(ℝ, ℂ) X p₀).toPath t
    have h0 : (Smooth2Simplex.face2Param t.val) 0 = t.val := rfl
    have h1 : (Smooth2Simplex.face2Param t.val) 1 = 0 := rfl
    rw [h0, h1]
    have h_sum : t.val + (0 : ℝ) = t.val := by ring
    rw [h_sum]
    rw [H.bottom_edge t.val]
    -- (SmoothPath.const _ _ p₀).toPath = Path.refl p₀, so applied to t gives p₀.
    rfl

/-- **face1 of `lowerRightSimplex H` equals `diagonalPath H`.** Both
parameterise t ↦ H(t, t). -/
lemma face1_lowerRightSimplex_eq (H : SmoothHomotopyBasedLoop γ₀ γ₁) :
    Smooth2Simplex.face1 H.lowerRightSimplex = H.diagonalPath := by
  apply SmoothPath.ext
  · show H.lowerRightSimplex.toFun (Smooth2Simplex.v0 : Fin 2 → ℝ)
        = H.diagonalPath.src
    rw [lowerRightSimplex_v0]
    rfl
  · show H.lowerRightSimplex.toFun (Smooth2Simplex.v2 : Fin 2 → ℝ)
        = H.diagonalPath.tgt
    rw [lowerRightSimplex_v2]
    rfl
  · intro t
    show H.toFun ![(Smooth2Simplex.face1Param t.val) 0
                    + (Smooth2Simplex.face1Param t.val) 1,
                   (Smooth2Simplex.face1Param t.val) 1]
        = H.diagonalPath.toPath t
    have h0 : (Smooth2Simplex.face1Param t.val) 0 = 0 := rfl
    have h1 : (Smooth2Simplex.face1Param t.val) 1 = t.val := rfl
    rw [h0, h1]
    have h_sum : (0 : ℝ) + t.val = t.val := by ring
    rw [h_sum]
    -- H.diagonalPath.toPath t = H.toFun ![t.val, t.val] by construction.
    rfl

/-- **face0 of `upperLeftSimplex H` equals `const p₀`.** Both constant:
t ↦ H(1-t, 1) = p₀ by top edge. -/
lemma face0_upperLeftSimplex_eq (H : SmoothHomotopyBasedLoop γ₀ γ₁) :
    Smooth2Simplex.face0 H.upperLeftSimplex = SmoothPath.const 𝓘(ℝ, ℂ) X p₀ := by
  apply SmoothPath.ext
  · show H.upperLeftSimplex.toFun (Smooth2Simplex.v1 : Fin 2 → ℝ)
        = (SmoothPath.const 𝓘(ℝ, ℂ) X p₀).src
    rw [upperLeftSimplex_v1, SmoothPath.const_src]
  · show H.upperLeftSimplex.toFun (Smooth2Simplex.v2 : Fin 2 → ℝ)
        = (SmoothPath.const 𝓘(ℝ, ℂ) X p₀).tgt
    rw [upperLeftSimplex_v2, SmoothPath.const_tgt]
  · intro t
    show H.toFun ![(Smooth2Simplex.face0Param t.val) 0,
                   (Smooth2Simplex.face0Param t.val) 0
                    + (Smooth2Simplex.face0Param t.val) 1]
        = (SmoothPath.const 𝓘(ℝ, ℂ) X p₀).toPath t
    have h0 : (Smooth2Simplex.face0Param t.val) 0 = 1 - t.val := rfl
    have h1 : (Smooth2Simplex.face0Param t.val) 1 = t.val := rfl
    rw [h0, h1]
    have h_sum : (1 - t.val) + t.val = 1 := by ring
    rw [h_sum]
    rw [H.top_edge (1 - t.val)]
    rfl

/-- **face1 of `upperLeftSimplex H` equals `γ₀.toPath`.** Both go
p₀ → p₀ via t ↦ H(0, t) = γ₀.toPath.ambient t. -/
lemma face1_upperLeftSimplex_eq (H : SmoothHomotopyBasedLoop γ₀ γ₁) :
    Smooth2Simplex.face1 H.upperLeftSimplex = γ₀.toPath := by
  apply SmoothPath.ext
  · show H.upperLeftSimplex.toFun (Smooth2Simplex.v0 : Fin 2 → ℝ) = γ₀.toPath.src
    rw [upperLeftSimplex_v0]
    exact (γ₀.toPath_src).symm
  · show H.upperLeftSimplex.toFun (Smooth2Simplex.v2 : Fin 2 → ℝ) = γ₀.toPath.tgt
    rw [upperLeftSimplex_v2]
    exact (γ₀.toPath_tgt).symm
  · intro t
    show H.toFun ![(Smooth2Simplex.face1Param t.val) 0,
                   (Smooth2Simplex.face1Param t.val) 0
                    + (Smooth2Simplex.face1Param t.val) 1]
        = γ₀.toPath.toPath t
    have h0 : (Smooth2Simplex.face1Param t.val) 0 = 0 := rfl
    have h1 : (Smooth2Simplex.face1Param t.val) 1 = t.val := rfl
    rw [h0, h1]
    have h_sum : (0 : ℝ) + t.val = t.val := by ring
    rw [h_sum]
    rw [H.left_edge t.val]
    exact γ₀.toPath.ambient_eq_on_unitInterval t

/-- **face2 of `upperLeftSimplex H` equals `diagonalPath H`.** Both
parameterise t ↦ H(t, t). -/
lemma face2_upperLeftSimplex_eq (H : SmoothHomotopyBasedLoop γ₀ γ₁) :
    Smooth2Simplex.face2 H.upperLeftSimplex = H.diagonalPath := by
  apply SmoothPath.ext
  · show H.upperLeftSimplex.toFun (Smooth2Simplex.v0 : Fin 2 → ℝ)
        = H.diagonalPath.src
    rw [upperLeftSimplex_v0]
    rfl
  · show H.upperLeftSimplex.toFun (Smooth2Simplex.v1 : Fin 2 → ℝ)
        = H.diagonalPath.tgt
    rw [upperLeftSimplex_v1]
    rfl
  · intro t
    show H.toFun ![(Smooth2Simplex.face2Param t.val) 0,
                   (Smooth2Simplex.face2Param t.val) 0
                    + (Smooth2Simplex.face2Param t.val) 1]
        = H.diagonalPath.toPath t
    have h0 : (Smooth2Simplex.face2Param t.val) 0 = t.val := rfl
    have h1 : (Smooth2Simplex.face2Param t.val) 1 = 0 := rfl
    rw [h0, h1]
    have h_sum : t.val + (0 : ℝ) = t.val := by ring
    rw [h_sum]
    rfl

/-! ## Boundary chain identity and the bordism conclusion -/

/-- **Boundary of the homotopy 2-chain at the SmoothChain level.**

`∂(σ_LR) + ∂(σ_UL) = single γ₁ - single γ₀
                       + single (const p₀) + single (const p₀)`

(after diagonal-path cancellation). -/
lemma boundary_lowerRight_plus_upperLeft (H : SmoothHomotopyBasedLoop γ₀ γ₁) :
    Smooth2Simplex.boundary H.lowerRightSimplex
        + Smooth2Simplex.boundary H.upperLeftSimplex
      = SmoothChain.single γ₁.toPath - SmoothChain.single γ₀.toPath
        + SmoothChain.single (SmoothPath.const 𝓘(ℝ, ℂ) X p₀)
        + SmoothChain.single (SmoothPath.const 𝓘(ℝ, ℂ) X p₀) := by
  -- Unfold both boundaries via face0 - face1 + face2.
  unfold Smooth2Simplex.boundary
  rw [face0_lowerRightSimplex_eq, face1_lowerRightSimplex_eq,
      face2_lowerRightSimplex_eq,
      face0_upperLeftSimplex_eq, face1_upperLeftSimplex_eq,
      face2_upperLeftSimplex_eq]
  -- Now: (single γ₁ - single D + single (const p₀))
  --    + (single (const p₀) - single γ₀ + single D)
  --  = single γ₁ - single γ₀ + 2 * single (const p₀)  (diagonals cancel)
  abel

/-- **Smooth-bordism from a smooth homotopy.** -/
theorem smoothBordant_of_smoothHomotopy
    (H : SmoothHomotopyBasedLoop γ₀ γ₁) :
    SmoothBordant γ₀ γ₁ := by
  -- Apply SmoothBordant.symm to reduce to SmoothBordant γ₁ γ₀, since the chain
  -- difference computed by the homotopy is γ₁ - γ₀ + 2 · const, hence
  -- single γ₁ - single γ₀ ∈ stokesBoundaries.
  apply SmoothBordant.symm
  unfold SmoothBordant
  -- The bordism 2-chain.
  let chain : Smooth2Chain 𝓘(ℝ, ℂ) X :=
    Smooth2Chain.single H.lowerRightSimplex + Smooth2Chain.single H.upperLeftSimplex
  -- Its boundary (via `boundary₂Cycle` packaged as SmoothCycle) lies in
  -- `stokesBoundaries`.
  have h_chain_in : Smooth2Chain.boundary₂Cycle chain ∈ stokesBoundaries 𝓘(ℝ, ℂ) X := by
    rw [mem_stokesBoundaries_iff]
    exact ⟨chain, rfl⟩
  -- Compute boundary₂Cycle chain at the SmoothChain level.
  have h_chain_eq :
      (Smooth2Chain.boundary₂Cycle chain : SmoothChain 𝓘(ℝ, ℂ) X)
        = SmoothChain.single γ₁.toPath - SmoothChain.single γ₀.toPath
          + SmoothChain.single (SmoothPath.const 𝓘(ℝ, ℂ) X p₀)
          + SmoothChain.single (SmoothPath.const 𝓘(ℝ, ℂ) X p₀) := by
    show (Smooth2Chain.boundary₂Cycle (Smooth2Chain.single H.lowerRightSimplex
            + Smooth2Chain.single H.upperLeftSimplex)
          : SmoothChain 𝓘(ℝ, ℂ) X)
        = SmoothChain.single γ₁.toPath - SmoothChain.single γ₀.toPath
          + SmoothChain.single (SmoothPath.const 𝓘(ℝ, ℂ) X p₀)
          + SmoothChain.single (SmoothPath.const 𝓘(ℝ, ℂ) X p₀)
    rw [LinearMap.map_add, SmoothCycle.coe_add,
        Smooth2Chain.boundary₂Cycle_coe, Smooth2Chain.boundary₂Cycle_coe,
        Smooth2Chain.boundary₂_single, Smooth2Chain.boundary₂_single]
    exact boundary_lowerRight_plus_upperLeft H
  -- Now show: γ₁.singleCycle - γ₀.singleCycle ∈ stokesBoundaries.
  -- The chain-level equality `h_chain_eq` lifts to a SmoothCycle equality.
  have h_const_in : single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := X) p₀
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) X :=
    single_smoothPath_const_smoothCycle_mem_stokesBoundaries p₀
  have h_two_const_in :
      single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := X) p₀
        + single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := X) p₀
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) X :=
    AddSubgroup.add_mem _ h_const_in h_const_in
  -- The SmoothCycle `boundary₂Cycle chain` equals (as SmoothCycle):
  --   γ₁.singleCycle - γ₀.singleCycle + 2 · const_p₀.singleCycle
  have h_chain_smoothCycle_eq :
      Smooth2Chain.boundary₂Cycle chain
        = γ₁.singleCycle - γ₀.singleCycle
          + single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := X) p₀
          + single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := X) p₀ := by
    apply Subtype.ext
    simp only [SmoothCycle.coe_add, SmoothCycle.coe_sub,
               BasedLoopAt.singleCycle_coe,
               single_smoothPath_const_smoothCycle_coe]
    exact h_chain_eq
  -- Substitute in h_chain_in.
  rw [h_chain_smoothCycle_eq] at h_chain_in
  -- Now h_chain_in : γ₁.singleCycle - γ₀.singleCycle + const_cycle + const_cycle ∈ stokes.
  -- Subtract the two const_cycles (which are in stokes) to get γ₁ - γ₀ ∈ stokes.
  have h_diff : γ₁.singleCycle - γ₀.singleCycle
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) X := by
    have h_sub :
        (γ₁.singleCycle - γ₀.singleCycle
            + single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := X) p₀
            + single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := X) p₀)
          - (single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := X) p₀
              + single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := X) p₀)
        ∈ stokesBoundaries 𝓘(ℝ, ℂ) X :=
      AddSubgroup.sub_mem _ h_chain_in h_two_const_in
    have h_eq :
        (γ₁.singleCycle - γ₀.singleCycle
            + single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := X) p₀
            + single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := X) p₀)
          - (single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := X) p₀
              + single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := X) p₀)
          = γ₁.singleCycle - γ₀.singleCycle := by abel
    rw [h_eq] at h_sub
    exact h_sub
  exact h_diff

end SmoothHomotopyBasedLoop

end JacobianChallenge

end
