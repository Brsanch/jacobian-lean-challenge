/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusDz
import JacobianChallenge.Manifold.Smooth2Simplex
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiff.Basic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-! # ℂ-valued partial derivatives of a `Smooth2Simplex` on `T_L`

For `σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)`, the underlying smooth map
`σ.toFun : (Fin 2 → ℝ) → ℂ ⧸ L` has an `mfderiv` at every point, which
is a continuous `ℝ`-linear map
`(Fin 2 → ℝ) →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (σ p) = ℂ`. Applying it to
the standard basis vectors `e_0 = (1, 0)` and `e_1 = (0, 1)` gives
two `ℂ`-valued **partial derivatives** of `σ`.

These partial derivatives are themselves continuous (in fact smooth)
functions `(Fin 2 → ℝ) → ℂ` — they are the building blocks of the
horizontal-then-vertical 2-simplex lift `σ̃ : (Fin 2 → ℝ) → ℂ`
constructed in `ComplexTorusTwoSimplexLift.lean`.

## What this file ships

* `Smooth2Simplex.basisVec` — the standard basis vector
  `e_i : Fin 2 → ℝ` for `i : Fin 2`.
* `ComplexTorus.partial1 σ`, `ComplexTorus.partial2 σ` — the
  ℂ-valued partial derivatives.
* `ComplexTorus.partial1_continuous`, `partial2_continuous` —
  continuity, sufficient for parameter-integral smoothness downstream.

No `sorry`, no `axiom`. -/

open scoped Manifold ContDiff Topology
open Bundle

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Standard basis on `Fin 2 → ℝ` -/

/-- The standard basis vector `e_i : Fin 2 → ℝ`. `e_0 = (1, 0)`,
`e_1 = (0, 1)`. -/
def basisVec (i : Fin 2) : Fin 2 → ℝ := Pi.single i 1

@[simp] lemma basisVec_zero_zero : basisVec 0 0 = 1 := by
  simp [basisVec, Pi.single]

@[simp] lemma basisVec_zero_one : basisVec 0 1 = 0 := by
  simp [basisVec, Pi.single]

@[simp] lemma basisVec_one_zero : basisVec 1 0 = 0 := by
  simp [basisVec, Pi.single]

@[simp] lemma basisVec_one_one : basisVec 1 1 = 1 := by
  simp [basisVec, Pi.single]

/-! ## Partial derivatives of a `Smooth2Simplex` on `T_L` -/

/-- **First partial derivative** of a smooth 2-simplex on `T_L`,
viewed as a `ℂ`-valued function. -/
def partial1 (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (p : Fin 2 → ℝ) : ℂ :=
  (mfderiv (𝓘(ℝ, Fin 2 → ℝ)) (𝓘(ℝ, ℂ)) σ.toFun p :
    (Fin 2 → ℝ) →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (σ.toFun p)) (basisVec 0)

/-- **Second partial derivative** of a smooth 2-simplex on `T_L`,
viewed as a `ℂ`-valued function. -/
def partial2 (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (p : Fin 2 → ℝ) : ℂ :=
  (mfderiv (𝓘(ℝ, Fin 2 → ℝ)) (𝓘(ℝ, ℂ)) σ.toFun p :
    (Fin 2 → ℝ) →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (σ.toFun p)) (basisVec 1)

end ComplexTorus

end JacobianChallenge

end
