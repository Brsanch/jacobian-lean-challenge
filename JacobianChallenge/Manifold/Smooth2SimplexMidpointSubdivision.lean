/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexAffineReparam

set_option linter.unusedSectionVars false

/-! # Midpoint subdivision of a `Smooth2Simplex`

Standard 4-way midpoint subdivision of `Δ²`:

```
       v₂
       /\
      /T2\
   m₀₂---m₁₂
    /\T3 /\
   /T0\ /T1\
  v₀--m₀₁--v₁
```

The four sub-triangles, with their vertex tuples:
* `T0` (near `v₀`): vertices `v₀, m₀₁, m₀₂`.
* `T1` (near `v₁`): vertices `m₀₁, v₁, m₁₂`.
* `T2` (near `v₂`): vertices `m₀₂, m₁₂, v₂`.
* `T3` (central, **reversed orientation**): vertices `m₁₂, m₀₂, m₀₁`.

The central triangle `T3` uses the *opposite* orientation so that
when we sum boundaries `∂T0 + ∂T1 + ∂T2 + ∂T3`, interior edges cancel
pairwise and the result equals `∂σ`.

Each sub-triangle is built via `Smooth2Simplex.affineReparam` applied
to the appropriate vertex triple in `Δ²`.

## What this file ships

* `Smooth2Simplex.midpoint01 / 12 / 02` — midpoints in `Δ²`.
* `Smooth2Simplex.midpointSubdivision σ` — a `Fin 4 → Smooth2Simplex I X`
  giving the 4 sub-2-simplices.
* `Smooth2Simplex.midpointSubdivision_T0 / T1 / T2 / T3` — definitional
  equalities exposing each sub-2-simplex as an `affineReparam`.
* Corner-vertex evaluations
  `midpointSubdivision_T0_at_v0` etc.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

namespace Smooth2Simplex

/-! ## Midpoints in `Δ²` -/

/-- Midpoint of `v₀-v₁` in `Δ²`: `(1/2, 0)`. -/
def midpoint01 : Fin 2 → ℝ := ![1/2, 0]

/-- Midpoint of `v₁-v₂` in `Δ²`: `(1/2, 1/2)`. -/
def midpoint12 : Fin 2 → ℝ := ![1/2, 1/2]

/-- Midpoint of `v₀-v₂` in `Δ²`: `(0, 1/2)`. -/
def midpoint02 : Fin 2 → ℝ := ![0, 1/2]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ω X]

/-- **The four sub-2-simplices of the midpoint subdivision of `σ`.**

The reversed orientation of `T3` is essential for the
orientation-cancellation telescoping `∂T0 + ∂T1 + ∂T2 + ∂T3 = ∂σ`. -/
noncomputable def midpointSubdivision (σ : Smooth2Simplex I X) :
    Fin 4 → Smooth2Simplex I X
  | ⟨0, _⟩ => affineReparam σ Smooth2Simplex.v0 midpoint01 midpoint02
  | ⟨1, _⟩ => affineReparam σ midpoint01 Smooth2Simplex.v1 midpoint12
  | ⟨2, _⟩ => affineReparam σ midpoint02 midpoint12 Smooth2Simplex.v2
  | ⟨3, _⟩ => affineReparam σ midpoint12 midpoint02 midpoint01

/-! ## Definitional expansions of each sub-triangle -/

@[simp] lemma midpointSubdivision_T0 (σ : Smooth2Simplex I X) :
    midpointSubdivision σ 0
      = affineReparam σ Smooth2Simplex.v0 midpoint01 midpoint02 := rfl

@[simp] lemma midpointSubdivision_T1 (σ : Smooth2Simplex I X) :
    midpointSubdivision σ 1
      = affineReparam σ midpoint01 Smooth2Simplex.v1 midpoint12 := rfl

@[simp] lemma midpointSubdivision_T2 (σ : Smooth2Simplex I X) :
    midpointSubdivision σ 2
      = affineReparam σ midpoint02 midpoint12 Smooth2Simplex.v2 := rfl

@[simp] lemma midpointSubdivision_T3 (σ : Smooth2Simplex I X) :
    midpointSubdivision σ 3
      = affineReparam σ midpoint12 midpoint02 midpoint01 := rfl

/-! ## Corner-vertex evaluations -/

lemma midpointSubdivision_T0_at_v0 (σ : Smooth2Simplex I X) :
    (midpointSubdivision σ 0).toFun Smooth2Simplex.v0 = σ.toFun Smooth2Simplex.v0 :=
  affineReparam_at_v0 σ Smooth2Simplex.v0 midpoint01 midpoint02

lemma midpointSubdivision_T0_at_v1 (σ : Smooth2Simplex I X) :
    (midpointSubdivision σ 0).toFun Smooth2Simplex.v1 = σ.toFun midpoint01 :=
  affineReparam_at_v1 σ Smooth2Simplex.v0 midpoint01 midpoint02

lemma midpointSubdivision_T0_at_v2 (σ : Smooth2Simplex I X) :
    (midpointSubdivision σ 0).toFun Smooth2Simplex.v2 = σ.toFun midpoint02 :=
  affineReparam_at_v2 σ Smooth2Simplex.v0 midpoint01 midpoint02

lemma midpointSubdivision_T1_at_v0 (σ : Smooth2Simplex I X) :
    (midpointSubdivision σ 1).toFun Smooth2Simplex.v0 = σ.toFun midpoint01 :=
  affineReparam_at_v0 σ midpoint01 Smooth2Simplex.v1 midpoint12

lemma midpointSubdivision_T1_at_v1 (σ : Smooth2Simplex I X) :
    (midpointSubdivision σ 1).toFun Smooth2Simplex.v1 = σ.toFun Smooth2Simplex.v1 :=
  affineReparam_at_v1 σ midpoint01 Smooth2Simplex.v1 midpoint12

lemma midpointSubdivision_T1_at_v2 (σ : Smooth2Simplex I X) :
    (midpointSubdivision σ 1).toFun Smooth2Simplex.v2 = σ.toFun midpoint12 :=
  affineReparam_at_v2 σ midpoint01 Smooth2Simplex.v1 midpoint12

lemma midpointSubdivision_T2_at_v0 (σ : Smooth2Simplex I X) :
    (midpointSubdivision σ 2).toFun Smooth2Simplex.v0 = σ.toFun midpoint02 :=
  affineReparam_at_v0 σ midpoint02 midpoint12 Smooth2Simplex.v2

lemma midpointSubdivision_T2_at_v1 (σ : Smooth2Simplex I X) :
    (midpointSubdivision σ 2).toFun Smooth2Simplex.v1 = σ.toFun midpoint12 :=
  affineReparam_at_v1 σ midpoint02 midpoint12 Smooth2Simplex.v2

lemma midpointSubdivision_T2_at_v2 (σ : Smooth2Simplex I X) :
    (midpointSubdivision σ 2).toFun Smooth2Simplex.v2 = σ.toFun Smooth2Simplex.v2 :=
  affineReparam_at_v2 σ midpoint02 midpoint12 Smooth2Simplex.v2

lemma midpointSubdivision_T3_at_v0 (σ : Smooth2Simplex I X) :
    (midpointSubdivision σ 3).toFun Smooth2Simplex.v0 = σ.toFun midpoint12 :=
  affineReparam_at_v0 σ midpoint12 midpoint02 midpoint01

lemma midpointSubdivision_T3_at_v1 (σ : Smooth2Simplex I X) :
    (midpointSubdivision σ 3).toFun Smooth2Simplex.v1 = σ.toFun midpoint02 :=
  affineReparam_at_v1 σ midpoint12 midpoint02 midpoint01

lemma midpointSubdivision_T3_at_v2 (σ : Smooth2Simplex I X) :
    (midpointSubdivision σ 3).toFun Smooth2Simplex.v2 = σ.toFun midpoint01 :=
  affineReparam_at_v2 σ midpoint12 midpoint02 midpoint01

end Smooth2Simplex

end JacobianChallenge

end
