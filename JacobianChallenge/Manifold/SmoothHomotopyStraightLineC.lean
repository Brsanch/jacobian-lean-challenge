/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothBordantOfSmoothHomotopy

set_option linter.unusedSectionVars false

/-! # Straight-line smooth homotopy of based loops in `ℂ`

For two smooth based loops `γ₀, γ₁ : BasedLoopAt 𝓘(ℝ, ℂ) ℂ p₀` at a
common basepoint `p₀ ∈ ℂ`, the **straight-line homotopy**

```
H(s, t) := (1 - s) • γ₀.toPath.ambient(t) + s • γ₁.toPath.ambient(t)
```

is a smooth map `ℝ² → ℂ` with the four edge conditions of
`SmoothHomotopyBasedLoop`:

* `H(0, t) = γ₀.toPath.ambient(t)`;
* `H(1, t) = γ₁.toPath.ambient(t)`;
* `H(s, 0) = (1-s) • p₀ + s • p₀ = p₀`  (since both loops start at `p₀`);
* `H(s, 1) = p₀` (likewise).

Composed with `smoothBordant_of_smoothHomotopy`, this discharges
`SmoothBordant γ₀ γ₁` unconditionally for **any** two based loops in
`ℂ` at `p₀` — confirming the smooth-singular fact that `ℂ` is
homologically trivial.

This is a real geometric construction (not a structural split): a
concrete smooth homotopy is built and its smoothness + edge conditions
discharged. It is a building block for chart-local smooth homotopies
on Riemann surfaces (where each chart maps to a convex subset of `ℂ`).

## What this file ships

* `SmoothHomotopyBasedLoop.straightLineC` — the straight-line
  homotopy constructor.
* `smoothBordant_straightLineC` — corollary: any two based loops in
  `ℂ` at `p₀` are smoothly bordant.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

/-! ## Smoothness of the linear-combination map -/

/-- Helper: for any smooth function `f : ℝ → ℂ`, the composition
`(x : Fin 2 → ℝ) ↦ f (x 1)` is smooth. -/
private lemma contMDiff_comp_proj1 {f : ℝ → ℂ}
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ f) :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => f (x 1)) := by
  have h_proj : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun x : Fin 2 → ℝ => x 1) := by
    have h_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : Fin 2 → ℝ => x 1) :=
      (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff
    exact h_cd.contMDiff
  exact hf.comp h_proj

/-- Helper: `(x : Fin 2 → ℝ) ↦ x 0` (the s-coordinate) is smooth `→ ℝ`. -/
private lemma contMDiff_proj0_R :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞ (fun x : Fin 2 → ℝ => x 0) := by
  have h_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Fin 2 → ℝ => x 0) :=
    (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff
  exact h_cd.contMDiff

/-- **Smoothness of the straight-line homotopy map.**

For smooth ambient functions `f, g : ℝ → ℂ`, the map
`(s, t) ↦ (1 - s) • f(t) + s • g(t) : (Fin 2 → ℝ) → ℂ` is `C^∞`. -/
private lemma contMDiff_straightLine
    (f g : ℝ → ℂ)
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ g) :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => (1 - (x 0 : ℝ)) • f (x 1) + (x 0 : ℝ) • g (x 1)) := by
  -- f ∘ proj1, g ∘ proj1 are smooth.
  have hfp : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => f (x 1)) := contMDiff_comp_proj1 hf
  have hgp : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => g (x 1)) := contMDiff_comp_proj1 hg
  -- The scalar `1 - x 0` and `x 0` are smooth ℝ-valued.
  have h_one_sub : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun x : Fin 2 → ℝ => 1 - (x 0 : ℝ)) :=
    contMDiff_const.sub contMDiff_proj0_R
  have h_s : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun x : Fin 2 → ℝ => (x 0 : ℝ)) := contMDiff_proj0_R
  -- Smul: ℝ smul ℂ.
  have h_lhs : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => (1 - (x 0 : ℝ)) • f (x 1)) := h_one_sub.smul hfp
  have h_rhs : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => (x 0 : ℝ) • g (x 1)) := h_s.smul hgp
  exact h_lhs.add h_rhs

/-! ## The straight-line homotopy constructor on `X = ℂ` -/

/-- **Straight-line smooth homotopy in `ℂ`.** For any two smooth based
loops `γ₀, γ₁` at `p₀ ∈ ℂ`, the map `H(s, t) := (1 - s) • γ₀.ambient(t)
+ s • γ₁.ambient(t)` defines a `SmoothHomotopyBasedLoop γ₀ γ₁`. -/
noncomputable def SmoothHomotopyBasedLoop.straightLineC
    {p₀ : ℂ} (γ₀ γ₁ : BasedLoopAt 𝓘(ℝ, ℂ) ℂ p₀) :
    SmoothHomotopyBasedLoop γ₀ γ₁ where
  toFun := fun x : Fin 2 → ℝ =>
    (1 - x 0) • γ₀.toPath.ambient (x 1) + (x 0) • γ₁.toPath.ambient (x 1)
  smooth :=
    contMDiff_straightLine γ₀.toPath.ambient γ₁.toPath.ambient
      γ₀.toPath.ambient_contMDiff γ₁.toPath.ambient_contMDiff
  left_edge := by
    intro t
    show (1 - (0 : ℝ)) • γ₀.toPath.ambient ((![0, t] : Fin 2 → ℝ) 1)
          + (0 : ℝ) • γ₁.toPath.ambient ((![0, t] : Fin 2 → ℝ) 1)
        = γ₀.toPath.ambient t
    have h1 : (![0, t] : Fin 2 → ℝ) 1 = t := rfl
    rw [h1]
    simp
  right_edge := by
    intro t
    show (1 - (1 : ℝ)) • γ₀.toPath.ambient ((![1, t] : Fin 2 → ℝ) 1)
          + (1 : ℝ) • γ₁.toPath.ambient ((![1, t] : Fin 2 → ℝ) 1)
        = γ₁.toPath.ambient t
    have h1 : (![1, t] : Fin 2 → ℝ) 1 = t := rfl
    rw [h1]
    simp
  bottom_edge := by
    intro s
    show (1 - s) • γ₀.toPath.ambient ((![s, 0] : Fin 2 → ℝ) 1)
          + s • γ₁.toPath.ambient ((![s, 0] : Fin 2 → ℝ) 1)
        = p₀
    have h1 : (![s, (0 : ℝ)] : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h1]
    -- γᵢ.toPath.ambient 0 = γᵢ.toPath.toPath 0 = γᵢ.toPath.src = p₀.
    have h_γ₀_amb_0 : γ₀.toPath.ambient 0 = p₀ := by
      have h := γ₀.toPath.ambient_eq_on_unitInterval
        (⟨0, by constructor <;> norm_num⟩ : unitInterval)
      have hval : ((⟨0, by constructor <;> norm_num⟩ : unitInterval).val : ℝ) = 0
        := rfl
      rw [hval] at h
      rw [h]
      exact (γ₀.toPath.toPath.source).trans γ₀.toPath_src
    have h_γ₁_amb_0 : γ₁.toPath.ambient 0 = p₀ := by
      have h := γ₁.toPath.ambient_eq_on_unitInterval
        (⟨0, by constructor <;> norm_num⟩ : unitInterval)
      have hval : ((⟨0, by constructor <;> norm_num⟩ : unitInterval).val : ℝ) = 0
        := rfl
      rw [hval] at h
      rw [h]
      exact (γ₁.toPath.toPath.source).trans γ₁.toPath_src
    rw [h_γ₀_amb_0, h_γ₁_amb_0]
    -- (1 - s) • p₀ + s • p₀ = ((1 - s) + s) • p₀ = 1 • p₀ = p₀
    module
  top_edge := by
    intro s
    show (1 - s) • γ₀.toPath.ambient ((![s, 1] : Fin 2 → ℝ) 1)
          + s • γ₁.toPath.ambient ((![s, 1] : Fin 2 → ℝ) 1)
        = p₀
    have h1 : (![s, (1 : ℝ)] : Fin 2 → ℝ) 1 = 1 := rfl
    rw [h1]
    have h_γ₀_amb_1 : γ₀.toPath.ambient 1 = p₀ := by
      have h := γ₀.toPath.ambient_eq_on_unitInterval
        (⟨1, by constructor <;> norm_num⟩ : unitInterval)
      have hval : ((⟨1, by constructor <;> norm_num⟩ : unitInterval).val : ℝ) = 1
        := rfl
      rw [hval] at h
      rw [h]
      exact (γ₀.toPath.toPath.target).trans γ₀.toPath_tgt
    have h_γ₁_amb_1 : γ₁.toPath.ambient 1 = p₀ := by
      have h := γ₁.toPath.ambient_eq_on_unitInterval
        (⟨1, by constructor <;> norm_num⟩ : unitInterval)
      have hval : ((⟨1, by constructor <;> norm_num⟩ : unitInterval).val : ℝ) = 1
        := rfl
      rw [hval] at h
      rw [h]
      exact (γ₁.toPath.toPath.target).trans γ₁.toPath_tgt
    rw [h_γ₀_amb_1, h_γ₁_amb_1]
    module

/-- **Corollary: any two based loops in `ℂ` at `p₀` are smoothly bordant.**

Direct application of `smoothBordant_of_smoothHomotopy` to the
straight-line homotopy. -/
theorem smoothBordant_straightLineC
    {p₀ : ℂ} (γ₀ γ₁ : BasedLoopAt 𝓘(ℝ, ℂ) ℂ p₀) :
    SmoothBordant γ₀ γ₁ :=
  SmoothHomotopyBasedLoop.smoothBordant_of_smoothHomotopy
    (SmoothHomotopyBasedLoop.straightLineC γ₀ γ₁)

end JacobianChallenge

end
