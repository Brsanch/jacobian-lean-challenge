/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorus
import JacobianChallenge.Manifold.ComplexTorusBasisLoop

set_option linter.unusedSectionVars false

/-! # Projected straight-line homotopy `[0,1]² → ℂ ⧸ L`

Given a lattice element `λ ∈ L` and a smooth ambient map `lift : ℝ → ℂ`
with `lift 0 = 0` and `lift 1 = λ`, the **projected straight-line
homotopy** is the smooth map

```
projStraightLineMap L lift λ : (Fin 2 → ℝ) → ℂ ⧸ L
                     x ↦ mkQ ((1 - x 0) · lift (x 1) + x 0 · (x 1 · λ))
```

interpolating in `ℂ` between `t ↦ lift t` (at `x 0 = 0`) and the linear
path `t ↦ t · λ` (at `x 0 = 1`), then projecting via `mkQ`.

This is the building block for the bordism between an arbitrary smooth
based loop `γ` on `ℂ ⧸ L` and the corresponding torus basis loop
`γ_λ = torusBasisLoop λ` — given the smooth lift `Γ` of `γ` from the
unconditional `SmoothPathLiftHypothesisTorus L`, the four edges of the
unit square map to:

* **left edge** (`x 0 = 0`): `mkQ ∘ lift` (which equals `γ.ambient` on
  `[0, 1]`);
* **right edge** (`x 0 = 1`): `mkQ ((x 1) · λ)` (which equals
  `γ_λ.ambient`);
* **bottom edge** (`x 1 = 0`): constant at `mkQ 0 = 0`;
* **top edge** (`x 1 = 1`): constant at `mkQ ((1 - s) · λ + s · λ)
  = mkQ λ = 0` (since `λ ∈ L`).

In Chip B we compose this `H` with the two triangle reparams covering
the unit square via `Δ²` to produce two `Smooth2Simplex`es whose boundary
realises the bordism `single γ - single γ_λ ∈ stokesBoundaries`.

## What this file ships

* `ComplexTorus.projStraightLineMap L lift λ` — the map.
* `ComplexTorus.projStraightLineMap_contMDiff` — smoothness in
  `𝓘(ℝ, Fin 2 → ℝ) → 𝓘(ℝ, ℂ)`.
* Edge identities at the four corner curves.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Smoothness primitives on `Fin 2 → ℝ` -/

/-- `(x : Fin 2 → ℝ) ↦ x i` is `C^∞` for each `i`. -/
private lemma contMDiff_proj_fin2 (i : Fin 2) :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞ (fun x : Fin 2 → ℝ => x i) := by
  have h_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Fin 2 → ℝ => x i) :=
    (ContinuousLinearMap.proj i : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff
  exact h_cd.contMDiff

/-! ## The map -/

/-- **Projected straight-line homotopy** from `lift` to `t ↦ t · λ`,
projected via `mkQ : ℂ → ℂ ⧸ L`. -/
noncomputable def projStraightLineMap (lift : ℝ → ℂ) (lam : ℂ) :
    (Fin 2 → ℝ) → ℂ ⧸ L :=
  fun x : Fin 2 → ℝ =>
    L.mkQ ((1 - x 0) • lift (x 1) + (x 0 : ℝ) • ((x 1 : ℝ) • lam))

/-! ## Smoothness -/

/-- Helper: for any smooth `lift : ℝ → ℂ`, the composition
`(x : Fin 2 → ℝ) ↦ lift (x 1)` is smooth. -/
private lemma contMDiff_lift_comp_proj1 {lift : ℝ → ℂ}
    (h_lift : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ lift) :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => lift (x 1)) :=
  h_lift.comp (contMDiff_proj_fin2 1)

/-- The inner `ℂ`-valued part of `projStraightLineMap` is smooth. -/
private lemma contMDiff_proj_inner
    (lift : ℝ → ℂ) (lam : ℂ)
    (h_lift : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ lift) :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ =>
        (1 - x 0) • lift (x 1) + (x 0 : ℝ) • ((x 1 : ℝ) • lam)) := by
  have h_one_sub : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun x : Fin 2 → ℝ => 1 - x 0) :=
    contMDiff_const.sub (contMDiff_proj_fin2 0)
  have h_s : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun x : Fin 2 → ℝ => (x 0 : ℝ)) := contMDiff_proj_fin2 0
  have h_t : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun x : Fin 2 → ℝ => (x 1 : ℝ)) := contMDiff_proj_fin2 1
  have h_lift_p : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => lift (x 1)) :=
    contMDiff_lift_comp_proj1 h_lift
  -- (x 1) • λ
  have h_t_lam : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => (x 1 : ℝ) • lam) :=
    h_t.smul contMDiff_const
  -- x 0 • (x 1 • λ)
  have h_s_t_lam : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => (x 0 : ℝ) • ((x 1 : ℝ) • lam)) :=
    h_s.smul h_t_lam
  -- (1 - x 0) • lift (x 1)
  have h_lhs : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => (1 - x 0) • lift (x 1)) :=
    h_one_sub.smul h_lift_p
  exact h_lhs.add h_s_t_lam

/-- **`projStraightLineMap` is smooth `(Fin 2 → ℝ) → ℂ ⧸ L`.** -/
theorem projStraightLineMap_contMDiff
    (lift : ℝ → ℂ) (lam : ℂ)
    (h_lift : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ lift) :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞ (projStraightLineMap L lift lam) := by
  unfold projStraightLineMap
  exact (mkQ_contMDiff_real L ∞).comp (contMDiff_proj_inner lift lam h_lift)

/-! ## Edge identities -/

variable {L}

/-- **Left edge identity (`x 0 = 0`).** `H(0, t) = mkQ (lift t)`. -/
lemma projStraightLineMap_left_edge
    (lift : ℝ → ℂ) (lam : ℂ) (t : ℝ) :
    projStraightLineMap L lift lam ![0, t] = L.mkQ (lift t) := by
  show L.mkQ ((1 - (0 : ℝ)) • lift ((![0, t] : Fin 2 → ℝ) 1)
      + ((0 : ℝ) : ℝ) • (((![0, t] : Fin 2 → ℝ) 1 : ℝ) • lam))
    = L.mkQ (lift t)
  have h1 : ((![0, t] : Fin 2 → ℝ) 1) = t := rfl
  rw [h1]
  congr 1
  -- (1 - 0) • lift t + 0 • (t • λ) = lift t
  simp

/-- **Right edge identity (`x 0 = 1`).** `H(1, t) = mkQ (t · λ)`. -/
lemma projStraightLineMap_right_edge
    (lift : ℝ → ℂ) (lam : ℂ) (t : ℝ) :
    projStraightLineMap L lift lam ![1, t] = L.mkQ ((t : ℝ) • lam) := by
  show L.mkQ ((1 - (1 : ℝ)) • lift ((![1, t] : Fin 2 → ℝ) 1)
      + ((1 : ℝ) : ℝ) • (((![1, t] : Fin 2 → ℝ) 1 : ℝ) • lam))
    = L.mkQ ((t : ℝ) • lam)
  have h1 : ((![1, t] : Fin 2 → ℝ) 1) = t := rfl
  rw [h1]
  congr 1
  simp

/-- **Bottom edge identity (`x 1 = 0`).** If `lift 0 = 0` then
`H(s, 0) = 0`. -/
lemma projStraightLineMap_bottom_edge
    (lift : ℝ → ℂ) (lam : ℂ) (h_lift_zero : lift 0 = 0) (s : ℝ) :
    projStraightLineMap L lift lam ![s, 0] = (0 : ℂ ⧸ L) := by
  show L.mkQ ((1 - s) • lift ((![s, (0 : ℝ)] : Fin 2 → ℝ) 1)
      + (s : ℝ) • (((![s, (0 : ℝ)] : Fin 2 → ℝ) 1 : ℝ) • lam))
    = (0 : ℂ ⧸ L)
  have h1 : ((![s, (0 : ℝ)] : Fin 2 → ℝ) 1) = 0 := rfl
  rw [h1, h_lift_zero]
  -- (1 - s) • 0 + s • (0 • λ) = 0
  have h_inner : (1 - s) • (0 : ℂ) + (s : ℝ) • ((0 : ℝ) • lam) = 0 := by
    simp
  rw [h_inner]
  exact map_zero L.mkQ

/-- **Top edge identity (`x 1 = 1`).** If `lift 1 = λ` and `λ ∈ L`,
then `H(s, 1) = 0`. -/
lemma projStraightLineMap_top_edge
    (lift : ℝ → ℂ) (lam : ℂ)
    (h_lift_one : lift 1 = lam) (h_lam : lam ∈ L) (s : ℝ) :
    projStraightLineMap L lift lam ![s, 1] = (0 : ℂ ⧸ L) := by
  change L.mkQ ((1 - s) • lift ((![s, (1 : ℝ)] : Fin 2 → ℝ) 1)
      + (s : ℝ) • (((![s, (1 : ℝ)] : Fin 2 → ℝ) 1 : ℝ) • lam))
    = (0 : ℂ ⧸ L)
  have h1 : ((![s, (1 : ℝ)] : Fin 2 → ℝ) 1) = 1 := rfl
  rw [h1, h_lift_one]
  -- (1 - s) • λ + s • (1 • λ) = (1 - s) • λ + s • λ = ((1 - s) + s) • λ = 1 • λ = λ
  have h_inner : (1 - s) • lam + (s : ℝ) • ((1 : ℝ) • lam) = lam := by
    have : (1 - s) • lam + (s : ℝ) • ((1 : ℝ) • lam) = lam := by
      module
    exact this
  rw [h_inner]
  exact (Submodule.Quotient.mk_eq_zero L).mpr h_lam

end ComplexTorus

end JacobianChallenge

end
