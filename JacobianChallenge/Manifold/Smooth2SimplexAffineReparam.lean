/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2Simplex
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Affine reparameterisation of a `Smooth2Simplex`

Given a `Smooth2Simplex I X` and three target vertices
`v0' v1' v2' : Fin 2 → ℝ`, produces a new `Smooth2Simplex I X` whose
vertices are `σ.toFun v0'`, `σ.toFun v1'`, `σ.toFun v2'`, with
parameterisation by the affine combination
`(t : Fin 2 → ℝ) ↦ (1 - t 0 - t 1) • v0' + t 0 • v1' + t 1 • v2'`
on `Δ²` (extended affinely to all of `(Fin 2 → ℝ)`).

This is the **building block** for barycentric Δ²-subdivision: each
sub-2-simplex of a subdivision is an affine reparameterisation of the
original.

## What this file ships

* `Smooth2Simplex.affineCombo` — the affine combination
  `(Fin 2 → ℝ) → (Fin 2 → ℝ)` sending `vᵢ` to `vᵢ'`.
* `Smooth2Simplex.affineCombo_v0` / `_v1` / `_v2` — endpoint identities.
* `Smooth2Simplex.affineCombo_contMDiff` — smoothness as a map between
  `(Fin 2 → ℝ)` normed spaces (manifold-modelled).
* `Smooth2Simplex.affineReparam σ v0' v1' v2'` — the reparameterised
  smooth 2-simplex.
* `Smooth2Simplex.affineReparam_apply` / `_v0` / `_v1` / `_v2` —
  computational equalities.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

namespace Smooth2Simplex

/-- **Affine combination** sending the standard simplex vertices
`v0`, `v1`, `v2` to chosen targets `v0'`, `v1'`, `v2'`:
`affineCombo v0' v1' v2' t = (1 - t 0 - t 1) • v0' + t 0 • v1' + t 1 • v2'`.
Defined for all `t : Fin 2 → ℝ`. -/
def affineCombo (v0' v1' v2' : Fin 2 → ℝ) : (Fin 2 → ℝ) → (Fin 2 → ℝ) :=
  fun t => (1 - t 0 - t 1) • v0' + t 0 • v1' + t 1 • v2'

@[simp] lemma affineCombo_v0 (v0' v1' v2' : Fin 2 → ℝ) :
    affineCombo v0' v1' v2' Smooth2Simplex.v0 = v0' := by
  unfold affineCombo Smooth2Simplex.v0
  funext i
  fin_cases i <;> simp

@[simp] lemma affineCombo_v1 (v0' v1' v2' : Fin 2 → ℝ) :
    affineCombo v0' v1' v2' Smooth2Simplex.v1 = v1' := by
  unfold affineCombo Smooth2Simplex.v1
  funext i
  fin_cases i <;> simp

@[simp] lemma affineCombo_v2 (v0' v1' v2' : Fin 2 → ℝ) :
    affineCombo v0' v1' v2' Smooth2Simplex.v2 = v2' := by
  unfold affineCombo Smooth2Simplex.v2
  funext i
  fin_cases i <;> simp

/-- The affine combination is `C^∞` as a map `(Fin 2 → ℝ) → (Fin 2 → ℝ)`
in the trivial-model manifold sense. -/
lemma affineCombo_contMDiff (v0' v1' v2' : Fin 2 → ℝ) :
    ContMDiff (𝓘(ℝ, Fin 2 → ℝ)) (𝓘(ℝ, Fin 2 → ℝ)) ∞
      (affineCombo v0' v1' v2') := by
  -- ContMDiff against trivial models = ContDiff ℝ ∞ in the smooth-norm sense.
  rw [contMDiff_iff_contDiff]
  unfold affineCombo
  -- Coordinate projections are ContDiff via `contDiff_pi.1 contDiff_id`.
  have h_proj0 : ContDiff ℝ ∞ (fun t : Fin 2 → ℝ => t 0) :=
    contDiff_pi.1 contDiff_id 0
  have h_proj1 : ContDiff ℝ ∞ (fun t : Fin 2 → ℝ => t 1) :=
    contDiff_pi.1 contDiff_id 1
  have h1 : ContDiff ℝ ∞ (fun t : Fin 2 → ℝ => (1 - t 0 - t 1) • v0') := by
    have h_coeff : ContDiff ℝ ∞ (fun t : Fin 2 → ℝ => 1 - t 0 - t 1) :=
      (contDiff_const.sub h_proj0).sub h_proj1
    exact h_coeff.smul contDiff_const
  have h2 : ContDiff ℝ ∞ (fun t : Fin 2 → ℝ => t 0 • v1') :=
    h_proj0.smul contDiff_const
  have h3 : ContDiff ℝ ∞ (fun t : Fin 2 → ℝ => t 1 • v2') :=
    h_proj1.smul contDiff_const
  exact (h1.add h2).add h3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ω X]

/-- **Affine reparameterisation of a smooth 2-simplex.**

For `σ : Smooth2Simplex I X` and target vertices `v0' v1' v2' : Fin 2 → ℝ`,
produces the smooth 2-simplex `σ ∘ (affineCombo v0' v1' v2')`. The new
vertices are `σ.toFun v0'`, `σ.toFun v1'`, `σ.toFun v2'`. -/
noncomputable def affineReparam (σ : Smooth2Simplex I X)
    (v0' v1' v2' : Fin 2 → ℝ) : Smooth2Simplex I X :=
  ⟨σ.toFun ∘ affineCombo v0' v1' v2',
    ContMDiff.comp σ.smooth (affineCombo_contMDiff v0' v1' v2')⟩

@[simp] lemma affineReparam_apply (σ : Smooth2Simplex I X)
    (v0' v1' v2' : Fin 2 → ℝ) (t : Fin 2 → ℝ) :
    (Smooth2Simplex.affineReparam σ v0' v1' v2').toFun t
      = σ.toFun (affineCombo v0' v1' v2' t) := rfl

@[simp] lemma affineReparam_at_v0 (σ : Smooth2Simplex I X)
    (v0' v1' v2' : Fin 2 → ℝ) :
    (Smooth2Simplex.affineReparam σ v0' v1' v2').toFun Smooth2Simplex.v0 = σ.toFun v0' := by
  rw [affineReparam_apply, affineCombo_v0]

@[simp] lemma affineReparam_at_v1 (σ : Smooth2Simplex I X)
    (v0' v1' v2' : Fin 2 → ℝ) :
    (Smooth2Simplex.affineReparam σ v0' v1' v2').toFun Smooth2Simplex.v1 = σ.toFun v1' := by
  rw [affineReparam_apply, affineCombo_v1]

@[simp] lemma affineReparam_at_v2 (σ : Smooth2Simplex I X)
    (v0' v1' v2' : Fin 2 → ℝ) :
    (Smooth2Simplex.affineReparam σ v0' v1' v2').toFun Smooth2Simplex.v2 = σ.toFun v2' := by
  rw [affineReparam_apply, affineCombo_v2]

end Smooth2Simplex

end JacobianChallenge

end
