/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CotangentWedgeVanishing
import Mathlib.LinearAlgebra.Alternating.Basic

set_option linter.unusedSectionVars false

/-! # Cotangent wedge as `AlternatingMap`

For two continuous ℂ-linear functionals `α, β : ℂ →L[ℂ] ℂ`, the
formal "wedge product" `α ∧ β` is the alternating bilinear map

  `(v 0, v 1) ↦ α(v 0) · β(v 1) - α(v 1) · β(v 0)`.

On a 1-complex-dim base — which is exactly the cotangent fibre type
`ℂ →L[ℂ] ℂ` of a complex 1-manifold — this expression is identically
zero by chip 5 (`cotangent_wedge_pointwise_zero`).

This file packages the wedge directly as `0 : AlternatingMap ℂ ℂ ℂ
(Fin 2)`, with the formula identity proven via chip 5. The
"definition-by-fiat" pattern reflects the mathematical content: on a
1-complex-dim base, the second exterior power of the cotangent fibre
is the zero space, so the wedge is *unconditionally* the zero
AlternatingMap.

Bridge for the chip 9 (`RiemannFirstBilinearRelation`) discharge:
future chips that lift this pointwise wedge to a smooth section of
the 2-form bundle, then integrate against a smooth 2-chain, will use
this trivial-vanishing fact to discharge the integration identity
underlying `Q J cycleGens ω₀ ω₁ = 0`.

## What this file ships

* `cotangentWedge` — the wedge as an `AlternatingMap`, defined as
  `0` since the second exterior power of `ℂ →L[ℂ] ℂ` is zero.
* `cotangentWedge_apply` — pointwise zero.
* `cotangentWedge_formula` — the formula identity:
  `cotangentWedge α β v = α(v 0) · β(v 1) - α(v 1) · β(v 0)`.
  Direction `0 = pointwise alternating pair` is exactly chip 5.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

/-- **The cotangent wedge as an `AlternatingMap`.**

On a 1-complex-dim base (here `ℂ →L[ℂ] ℂ`), the second exterior power
is the zero space. The wedge `α ∧ β` is identically zero as an
alternating multilinear map. -/
noncomputable def cotangentWedge (_α _β : ℂ →L[ℂ] ℂ) :
    AlternatingMap ℂ ℂ ℂ (Fin 2) := 0

/-- **`cotangentWedge α β v = 0` pointwise.** -/
@[simp]
theorem cotangentWedge_apply (α β : ℂ →L[ℂ] ℂ) (v : Fin 2 → ℂ) :
    cotangentWedge α β v = 0 := AlternatingMap.zero_apply v

/-- **Wedge formula: `α ∧ β` evaluates to the alternating pair on `(v 0, v 1)`.**

The wedge is mathematically the alternating bilinear map
`α(v 0) · β(v 1) - α(v 1) · β(v 0)`. Since this expression is
identically zero on a 1-complex-dim base (chip 5
`cotangent_wedge_pointwise_zero`), the formula identity holds. -/
theorem cotangentWedge_formula (α β : ℂ →L[ℂ] ℂ) (v : Fin 2 → ℂ) :
    cotangentWedge α β v = α (v 0) * β (v 1) - α (v 1) * β (v 0) := by
  rw [cotangentWedge_apply]
  exact (cotangent_wedge_pointwise_zero α β (v 0) (v 1)).symm

end JacobianChallenge

end
