/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothHomotopyPath
import JacobianChallenge.Manifold.SmoothBordantOfSmoothHomotopy

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

end SmoothHomotopyPath

end JacobianChallenge

end
