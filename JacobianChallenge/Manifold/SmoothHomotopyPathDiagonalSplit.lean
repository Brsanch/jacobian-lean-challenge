/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothHomotopyPath
import JacobianChallenge.Manifold.SmoothBordantOfSmoothHomotopy
import JacobianChallenge.Manifold.SmoothPathExt
import JacobianChallenge.Manifold.SmoothPathConst

set_option linter.unusedSectionVars false

/-! # Diagonal-split of `SmoothHomotopyPath` into two `Smooth2Simplex`es

Sister construction to `SmoothBordantOfSmoothHomotopy.lean`'s
`lowerRightSimplex` / `upperLeftSimplex` for `SmoothHomotopyBasedLoop`,
adapted to `SmoothHomotopyPath γ₀ γ₁` (paths with the same `src` and
`tgt`, not loops at a common basepoint).

Given a homotopy `H : SmoothHomotopyPath γ₀ γ₁ h_src h_tgt`, the unit
square `[0,1]²` is covered by two triangles:

* **Lower-right**: `Δ² ∋ (s, t) ↦ (s + t, t)`, with vertices
    `v₀ = (0,0) ↦ (0,0) ↦ γ₀.src`,
    `v₁ = (1,0) ↦ (1,0) ↦ γ₁.src = γ₀.src`,
    `v₂ = (0,1) ↦ (1,1) ↦ γ₁.tgt = γ₀.tgt`.
* **Upper-left**: `Δ² ∋ (s, t) ↦ (s, s + t)`, with vertices
    `v₀ = (0,0) ↦ (0,0) ↦ γ₀.src`,
    `v₁ = (1,0) ↦ (1,1) ↦ γ₁.tgt = γ₀.tgt`,
    `v₂ = (0,1) ↦ (0,1) ↦ γ₀.tgt`.

The sum of their boundaries gives `single γ₁ - single γ₀` modulo
constant-path residues (the "bottom" and "top" constant-loop
contributions cancel in the loop case but here become constant
paths at `γ₀.src` and `γ₀.tgt`). The diagonal contribution appears
in both boundaries with opposite signs and cancels.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-- ℝ-component projection `(Fin 2 → ℝ) → ℝ` is `C^∞`. -/
private lemma contMDiff_proj_fin2 (i : Fin 2) :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞ (fun x : Fin 2 → ℝ => x i) :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).contDiff).contMDiff

/-- The reparam `(x 0, x 1) ↦ (x 0 + x 1, x 1)` is `C^∞`. -/
private lemma contMDiff_reparamLR_path :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞
      (fun x : Fin 2 → ℝ => ![x 0 + x 1, x 1]) := by
  rw [contMDiff_pi_space]
  intro i
  fin_cases i
  · have h_eq : (fun x : Fin 2 → ℝ => (![x 0 + x 1, x 1] : Fin 2 → ℝ) 0)
              = fun x : Fin 2 → ℝ => x 0 + x 1 := by funext; rfl
    show ContMDiff _ _ ∞ (fun x : Fin 2 → ℝ => (![x 0 + x 1, x 1] : Fin 2 → ℝ) 0)
    rw [h_eq]
    exact (contMDiff_proj_fin2 0).add (contMDiff_proj_fin2 1)
  · have h_eq : (fun x : Fin 2 → ℝ => (![x 0 + x 1, x 1] : Fin 2 → ℝ) 1)
              = fun x : Fin 2 → ℝ => x 1 := by funext; rfl
    show ContMDiff _ _ ∞ (fun x : Fin 2 → ℝ => (![x 0 + x 1, x 1] : Fin 2 → ℝ) 1)
    rw [h_eq]
    exact contMDiff_proj_fin2 1

/-- The reparam `(x 0, x 1) ↦ (x 0, x 0 + x 1)` is `C^∞`. -/
private lemma contMDiff_reparamUL_path :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞
      (fun x : Fin 2 → ℝ => ![x 0, x 0 + x 1]) := by
  rw [contMDiff_pi_space]
  intro i
  fin_cases i
  · have h_eq : (fun x : Fin 2 → ℝ => (![x 0, x 0 + x 1] : Fin 2 → ℝ) 0)
              = fun x : Fin 2 → ℝ => x 0 := by funext; rfl
    show ContMDiff _ _ ∞ (fun x : Fin 2 → ℝ => (![x 0, x 0 + x 1] : Fin 2 → ℝ) 0)
    rw [h_eq]
    exact contMDiff_proj_fin2 0
  · have h_eq : (fun x : Fin 2 → ℝ => (![x 0, x 0 + x 1] : Fin 2 → ℝ) 1)
              = fun x : Fin 2 → ℝ => x 0 + x 1 := by funext; rfl
    show ContMDiff _ _ ∞ (fun x : Fin 2 → ℝ => (![x 0, x 0 + x 1] : Fin 2 → ℝ) 1)
    rw [h_eq]
    exact (contMDiff_proj_fin2 0).add (contMDiff_proj_fin2 1)

namespace SmoothHomotopyPath

variable {γ₀ γ₁ : SmoothPath (𝓘(ℝ, ℂ)) Y}
  {h_src : γ₀.src = γ₁.src} {h_tgt : γ₀.tgt = γ₁.tgt}

/-- **Lower-right triangle 2-simplex** of a `SmoothHomotopyPath`. -/
noncomputable def lowerRightSimplex (H : SmoothHomotopyPath γ₀ γ₁ h_src h_tgt) :
    Smooth2Simplex (𝓘(ℝ, ℂ)) Y where
  toFun := fun x : Fin 2 → ℝ => H.toFun ![x 0 + x 1, x 1]
  smooth := H.smooth.comp contMDiff_reparamLR_path

/-- **Upper-left triangle 2-simplex** of a `SmoothHomotopyPath`. -/
noncomputable def upperLeftSimplex (H : SmoothHomotopyPath γ₀ γ₁ h_src h_tgt) :
    Smooth2Simplex (𝓘(ℝ, ℂ)) Y where
  toFun := fun x : Fin 2 → ℝ => H.toFun ![x 0, x 0 + x 1]
  smooth := H.smooth.comp contMDiff_reparamUL_path

/-! ## Vertex evaluations -/

@[simp] lemma lowerRightSimplex_v0 (H : SmoothHomotopyPath γ₀ γ₁ h_src h_tgt) :
    (H.lowerRightSimplex).toFun (Smooth2Simplex.v0 : Fin 2 → ℝ) = γ₀.src := by
  show H.toFun ![Smooth2Simplex.v0 0 + Smooth2Simplex.v0 1,
                  Smooth2Simplex.v0 1] = γ₀.src
  have h0 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 0 = 0 := rfl
  have h1 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 1 = 0 := rfl
  rw [h0, h1]
  change H.toFun ![0 + 0, 0] = γ₀.src
  have : (0 : ℝ) + 0 = 0 := by norm_num
  rw [this]
  exact H.bottom_edge 0

@[simp] lemma lowerRightSimplex_v1 (H : SmoothHomotopyPath γ₀ γ₁ h_src h_tgt) :
    (H.lowerRightSimplex).toFun (Smooth2Simplex.v1 : Fin 2 → ℝ) = γ₀.src := by
  show H.toFun ![Smooth2Simplex.v1 0 + Smooth2Simplex.v1 1,
                  Smooth2Simplex.v1 1] = γ₀.src
  have h0 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 = 1 := rfl
  have h1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 1 = 0 := rfl
  rw [h0, h1]
  change H.toFun ![1 + 0, 0] = γ₀.src
  have : (1 : ℝ) + 0 = 1 := by norm_num
  rw [this]
  exact H.bottom_edge 1

@[simp] lemma lowerRightSimplex_v2 (H : SmoothHomotopyPath γ₀ γ₁ h_src h_tgt) :
    (H.lowerRightSimplex).toFun (Smooth2Simplex.v2 : Fin 2 → ℝ) = γ₀.tgt := by
  show H.toFun ![Smooth2Simplex.v2 0 + Smooth2Simplex.v2 1,
                  Smooth2Simplex.v2 1] = γ₀.tgt
  have h0 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 = 0 := rfl
  have h1 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 1 = 1 := rfl
  rw [h0, h1]
  change H.toFun ![0 + 1, 1] = γ₀.tgt
  have : (0 : ℝ) + 1 = 1 := by norm_num
  rw [this]
  exact H.top_edge 1

@[simp] lemma upperLeftSimplex_v0 (H : SmoothHomotopyPath γ₀ γ₁ h_src h_tgt) :
    (H.upperLeftSimplex).toFun (Smooth2Simplex.v0 : Fin 2 → ℝ) = γ₀.src := by
  show H.toFun ![Smooth2Simplex.v0 0,
                  Smooth2Simplex.v0 0 + Smooth2Simplex.v0 1] = γ₀.src
  have h0 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 0 = 0 := rfl
  have h1 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 1 = 0 := rfl
  rw [h0, h1]
  change H.toFun ![0, 0 + 0] = γ₀.src
  have : (0 : ℝ) + 0 = 0 := by norm_num
  rw [this]
  exact H.bottom_edge 0

@[simp] lemma upperLeftSimplex_v1 (H : SmoothHomotopyPath γ₀ γ₁ h_src h_tgt) :
    (H.upperLeftSimplex).toFun (Smooth2Simplex.v1 : Fin 2 → ℝ) = γ₀.tgt := by
  show H.toFun ![Smooth2Simplex.v1 0,
                  Smooth2Simplex.v1 0 + Smooth2Simplex.v1 1] = γ₀.tgt
  have h0 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 = 1 := rfl
  have h1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 1 = 0 := rfl
  rw [h0, h1]
  change H.toFun ![1, 1 + 0] = γ₀.tgt
  have : (1 : ℝ) + 0 = 1 := by norm_num
  rw [this]
  exact H.top_edge 1

@[simp] lemma upperLeftSimplex_v2 (H : SmoothHomotopyPath γ₀ γ₁ h_src h_tgt) :
    (H.upperLeftSimplex).toFun (Smooth2Simplex.v2 : Fin 2 → ℝ) = γ₀.tgt := by
  show H.toFun ![Smooth2Simplex.v2 0,
                  Smooth2Simplex.v2 0 + Smooth2Simplex.v2 1] = γ₀.tgt
  have h0 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 = 0 := rfl
  have h1 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 1 = 1 := rfl
  rw [h0, h1]
  change H.toFun ![0, 0 + 1] = γ₀.tgt
  have : (0 : ℝ) + 1 = 1 := by norm_num
  rw [this]
  exact H.top_edge 0

/-! ## Diagonal path -/

/-- The diagonal-path 1-simplex `t ↦ H(t, t)`, as a smooth path from
`γ₀.src` to `γ₀.tgt`. -/
noncomputable def diagonalPath (H : SmoothHomotopyPath γ₀ γ₁ h_src h_tgt) :
    SmoothPath (𝓘(ℝ, ℂ)) Y where
  src := γ₀.src
  tgt := γ₀.tgt
  toPath := {
    toContinuousMap :=
      { toFun := fun t : unitInterval => H.toFun ![t.val, t.val]
        continuous_toFun := by
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
          exact h_smooth.continuous.comp continuous_subtype_val }
    source' := by
      show H.toFun ![(0 : unitInterval).val, (0 : unitInterval).val] = γ₀.src
      change H.toFun ![(0 : ℝ), 0] = γ₀.src
      exact H.bottom_edge 0
    target' := by
      show H.toFun ![(1 : unitInterval).val, (1 : unitInterval).val] = γ₀.tgt
      change H.toFun ![(1 : ℝ), 1] = γ₀.tgt
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

/-- **face0 of `lowerRightSimplex H` equals `γ₁`.** -/
lemma face0_lowerRightSimplex_eq (H : SmoothHomotopyPath γ₀ γ₁ h_src h_tgt) :
    Smooth2Simplex.face0 H.lowerRightSimplex = γ₁ := by
  apply SmoothPath.ext
  · show H.lowerRightSimplex.toFun (Smooth2Simplex.v1 : Fin 2 → ℝ) = γ₁.src
    rw [lowerRightSimplex_v1]
    exact h_src
  · show H.lowerRightSimplex.toFun (Smooth2Simplex.v2 : Fin 2 → ℝ) = γ₁.tgt
    rw [lowerRightSimplex_v2]
    exact h_tgt
  · intro t
    show H.toFun ![(Smooth2Simplex.face0Param t.val) 0
                    + (Smooth2Simplex.face0Param t.val) 1,
                   (Smooth2Simplex.face0Param t.val) 1] = γ₁.toPath t
    have h0 : (Smooth2Simplex.face0Param t.val) 0 = 1 - t.val := rfl
    have h1 : (Smooth2Simplex.face0Param t.val) 1 = t.val := rfl
    rw [h0, h1]
    have h_sum : (1 - t.val) + t.val = 1 := by ring
    rw [h_sum]
    rw [H.right_edge t.val]
    exact γ₁.ambient_eq_on_unitInterval t

/-- **face2 of `lowerRightSimplex H` equals `const γ₀.src`.** -/
lemma face2_lowerRightSimplex_eq (H : SmoothHomotopyPath γ₀ γ₁ h_src h_tgt) :
    Smooth2Simplex.face2 H.lowerRightSimplex
      = SmoothPath.const (𝓘(ℝ, ℂ)) Y γ₀.src := by
  apply SmoothPath.ext
  · show H.lowerRightSimplex.toFun (Smooth2Simplex.v0 : Fin 2 → ℝ)
        = (SmoothPath.const (𝓘(ℝ, ℂ)) Y γ₀.src).src
    rw [lowerRightSimplex_v0, SmoothPath.const_src]
  · show H.lowerRightSimplex.toFun (Smooth2Simplex.v1 : Fin 2 → ℝ)
        = (SmoothPath.const (𝓘(ℝ, ℂ)) Y γ₀.src).tgt
    rw [lowerRightSimplex_v1, SmoothPath.const_tgt]
  · intro t
    show H.toFun ![(Smooth2Simplex.face2Param t.val) 0
                    + (Smooth2Simplex.face2Param t.val) 1,
                   (Smooth2Simplex.face2Param t.val) 1]
        = (SmoothPath.const (𝓘(ℝ, ℂ)) Y γ₀.src).toPath t
    have h0 : (Smooth2Simplex.face2Param t.val) 0 = t.val := rfl
    have h1 : (Smooth2Simplex.face2Param t.val) 1 = 0 := rfl
    rw [h0, h1]
    have h_sum : t.val + (0 : ℝ) = t.val := by ring
    rw [h_sum]
    rw [H.bottom_edge t.val]
    rfl

/-- **face1 of `lowerRightSimplex H` equals `diagonalPath H`.** -/
lemma face1_lowerRightSimplex_eq (H : SmoothHomotopyPath γ₀ γ₁ h_src h_tgt) :
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
    rfl

/-- **face0 of `upperLeftSimplex H` equals `const γ₀.tgt`.** -/
lemma face0_upperLeftSimplex_eq (H : SmoothHomotopyPath γ₀ γ₁ h_src h_tgt) :
    Smooth2Simplex.face0 H.upperLeftSimplex
      = SmoothPath.const (𝓘(ℝ, ℂ)) Y γ₀.tgt := by
  apply SmoothPath.ext
  · show H.upperLeftSimplex.toFun (Smooth2Simplex.v1 : Fin 2 → ℝ)
        = (SmoothPath.const (𝓘(ℝ, ℂ)) Y γ₀.tgt).src
    rw [upperLeftSimplex_v1, SmoothPath.const_src]
  · show H.upperLeftSimplex.toFun (Smooth2Simplex.v2 : Fin 2 → ℝ)
        = (SmoothPath.const (𝓘(ℝ, ℂ)) Y γ₀.tgt).tgt
    rw [upperLeftSimplex_v2, SmoothPath.const_tgt]
  · intro t
    show H.toFun ![(Smooth2Simplex.face0Param t.val) 0,
                   (Smooth2Simplex.face0Param t.val) 0
                    + (Smooth2Simplex.face0Param t.val) 1]
        = (SmoothPath.const (𝓘(ℝ, ℂ)) Y γ₀.tgt).toPath t
    have h0 : (Smooth2Simplex.face0Param t.val) 0 = 1 - t.val := rfl
    have h1 : (Smooth2Simplex.face0Param t.val) 1 = t.val := rfl
    rw [h0, h1]
    have h_sum : (1 - t.val) + t.val = 1 := by ring
    rw [h_sum]
    rw [H.top_edge (1 - t.val)]
    rfl

/-- **face1 of `upperLeftSimplex H` equals `γ₀`.** -/
lemma face1_upperLeftSimplex_eq (H : SmoothHomotopyPath γ₀ γ₁ h_src h_tgt) :
    Smooth2Simplex.face1 H.upperLeftSimplex = γ₀ := by
  apply SmoothPath.ext
  · show H.upperLeftSimplex.toFun (Smooth2Simplex.v0 : Fin 2 → ℝ) = γ₀.src
    rw [upperLeftSimplex_v0]
  · show H.upperLeftSimplex.toFun (Smooth2Simplex.v2 : Fin 2 → ℝ) = γ₀.tgt
    rw [upperLeftSimplex_v2]
  · intro t
    show H.toFun ![(Smooth2Simplex.face1Param t.val) 0,
                   (Smooth2Simplex.face1Param t.val) 0
                    + (Smooth2Simplex.face1Param t.val) 1]
        = γ₀.toPath t
    have h0 : (Smooth2Simplex.face1Param t.val) 0 = 0 := rfl
    have h1 : (Smooth2Simplex.face1Param t.val) 1 = t.val := rfl
    rw [h0, h1]
    have h_sum : (0 : ℝ) + t.val = t.val := by ring
    rw [h_sum]
    rw [H.left_edge t.val]
    exact γ₀.ambient_eq_on_unitInterval t

/-- **face2 of `upperLeftSimplex H` equals `diagonalPath H`.** -/
lemma face2_upperLeftSimplex_eq (H : SmoothHomotopyPath γ₀ γ₁ h_src h_tgt) :
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

/-! ## Boundary sum identity -/

/-- **`∂(σ_LR) + ∂(σ_UL) = single γ₁ - single γ₀
  + single (const γ₀.src) + single (const γ₀.tgt)`.**
Diagonal-path contributions cancel. -/
theorem boundary_lowerRight_plus_upperLeft
    (H : SmoothHomotopyPath γ₀ γ₁ h_src h_tgt) :
    Smooth2Simplex.boundary H.lowerRightSimplex
        + Smooth2Simplex.boundary H.upperLeftSimplex
      = SmoothChain.single γ₁ - SmoothChain.single γ₀
        + SmoothChain.single (SmoothPath.const (𝓘(ℝ, ℂ)) Y γ₀.src)
        + SmoothChain.single (SmoothPath.const (𝓘(ℝ, ℂ)) Y γ₀.tgt) := by
  unfold Smooth2Simplex.boundary
  rw [face0_lowerRightSimplex_eq, face1_lowerRightSimplex_eq,
      face2_lowerRightSimplex_eq,
      face0_upperLeftSimplex_eq, face1_upperLeftSimplex_eq,
      face2_upperLeftSimplex_eq]
  abel

/-! ## Bordism conclusion: `single γ₁ - single γ₀` is a stokesBoundary -/

/-- `single γ₁ - single γ₀` is a `SmoothCycle`. Its `X →₀ ℤ` boundary
vanishes because γ₀.src = γ₁.src and γ₀.tgt = γ₁.tgt. -/
lemma single_sub_single_mem_smoothCycle
    (h_src : γ₀.src = γ₁.src) (h_tgt : γ₀.tgt = γ₁.tgt) :
    SmoothChain.single γ₁ - SmoothChain.single γ₀
      ∈ SmoothCycle (𝓘(ℝ, ℂ)) Y := by
  rw [SmoothCycle.mem_iff]
  simp [SmoothChain.boundary_single, SmoothChain.boundarySingle, h_src, h_tgt]

/-- **The bordism conclusion at the SmoothCycle level.** Given a
`SmoothHomotopyPath γ₀ γ₁`, the SmoothCycle `single γ₁ - single γ₀`
lies in `stokesBoundaries`. -/
theorem singleSub_smoothCycle_mem_stokesBoundaries
    (H : SmoothHomotopyPath γ₀ γ₁ h_src h_tgt) :
    (⟨SmoothChain.single γ₁ - SmoothChain.single γ₀,
        single_sub_single_mem_smoothCycle h_src h_tgt⟩
          : SmoothCycle (𝓘(ℝ, ℂ)) Y)
      ∈ stokesBoundaries (𝓘(ℝ, ℂ)) Y := by
  -- The 2-chain witness: σ_LR + σ_UL produces single γ₁ - single γ₀
  -- modulo the two constant residues; both constants are themselves
  -- stokesBoundaries.
  set chain : Smooth2Chain (𝓘(ℝ, ℂ)) Y :=
    Smooth2Chain.single H.lowerRightSimplex
      + Smooth2Chain.single H.upperLeftSimplex with h_chain_def
  -- ∂₂Cycle chain ∈ stokesBoundaries (trivially).
  have h_chain_in : Smooth2Chain.boundary₂Cycle chain
      ∈ stokesBoundaries (𝓘(ℝ, ℂ)) Y :=
    (mem_stokesBoundaries_iff (I := 𝓘(ℝ, ℂ)) (X := Y)).mpr ⟨chain, rfl⟩
  -- Const-cycles at γ₀.src and γ₀.tgt are stokesBoundaries.
  have h_const_src_in :
      single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := Y) γ₀.src
        ∈ stokesBoundaries (𝓘(ℝ, ℂ)) Y :=
    single_smoothPath_const_smoothCycle_mem_stokesBoundaries γ₀.src
  have h_const_tgt_in :
      single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := Y) γ₀.tgt
        ∈ stokesBoundaries (𝓘(ℝ, ℂ)) Y :=
    single_smoothPath_const_smoothCycle_mem_stokesBoundaries γ₀.tgt
  -- Chain equality at the SmoothChain level.
  have h_chain_eq :
      (Smooth2Chain.boundary₂Cycle chain : SmoothChain (𝓘(ℝ, ℂ)) Y)
        = SmoothChain.single γ₁ - SmoothChain.single γ₀
          + SmoothChain.single (SmoothPath.const (𝓘(ℝ, ℂ)) Y γ₀.src)
          + SmoothChain.single (SmoothPath.const (𝓘(ℝ, ℂ)) Y γ₀.tgt) := by
    rw [h_chain_def]
    simp [Smooth2Chain.boundary₂Cycle_coe, Smooth2Chain.boundary₂_single]
    exact boundary_lowerRight_plus_upperLeft H
  -- Lift chain equality to SmoothCycle level.
  have h_cycle_eq : Smooth2Chain.boundary₂Cycle chain
      = ⟨SmoothChain.single γ₁ - SmoothChain.single γ₀,
            single_sub_single_mem_smoothCycle h_src h_tgt⟩
        + single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := Y) γ₀.src
        + single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := Y) γ₀.tgt := by
    apply Subtype.ext
    simp only [SmoothCycle.coe_add, single_smoothPath_const_smoothCycle_coe]
    show (Smooth2Chain.boundary₂Cycle chain : SmoothChain (𝓘(ℝ, ℂ)) Y)
        = SmoothChain.single γ₁ - SmoothChain.single γ₀
          + SmoothChain.single (SmoothPath.const (𝓘(ℝ, ℂ)) Y γ₀.src)
          + SmoothChain.single (SmoothPath.const (𝓘(ℝ, ℂ)) Y γ₀.tgt)
    exact h_chain_eq
  -- Solve for the target cycle: it equals `boundary₂Cycle chain - const_src - const_tgt`.
  have h_target_eq :
      (⟨SmoothChain.single γ₁ - SmoothChain.single γ₀,
          single_sub_single_mem_smoothCycle h_src h_tgt⟩ : SmoothCycle (𝓘(ℝ, ℂ)) Y)
        = Smooth2Chain.boundary₂Cycle chain
          - single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := Y) γ₀.src
          - single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := Y) γ₀.tgt := by
    rw [h_cycle_eq]
    abel
  rw [h_target_eq]
  -- Closed under subtraction: stokesBoundaries is an AddSubgroup.
  exact (stokesBoundaries (𝓘(ℝ, ℂ)) Y).sub_mem
    ((stokesBoundaries (𝓘(ℝ, ℂ)) Y).sub_mem h_chain_in h_const_src_in)
    h_const_tgt_in

end SmoothHomotopyPath

end JacobianChallenge

end
