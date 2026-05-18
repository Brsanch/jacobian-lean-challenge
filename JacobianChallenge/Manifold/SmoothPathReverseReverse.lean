/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathExt
import JacobianChallenge.Manifold.SmoothPathReverse

set_option linter.unusedSectionVars false

/-! # `(γ.reverse).reverse = γ` for smooth paths

Direct application of `SmoothPath.ext` (chip 16) and
`Path.symm_symm` from mathlib: reversing a smooth path twice yields
the original path. The src/tgt fields swap then swap back; the
`toPath` field reverses via `Path.symm` twice and the underlying
`toFun` evaluations cancel.

## What this file ships

* `SmoothPath.reverse_reverse` —
  `(γ.reverse).reverse = γ`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-- **Reversing a smooth path twice gives the original path.** -/
@[simp] lemma SmoothPath.reverse_reverse (γ : SmoothPath I X) :
    γ.reverse.reverse = γ := by
  apply SmoothPath.ext
  · -- src: reverse.reverse.src = reverse.tgt = γ.src.
    show γ.src = γ.src
    rfl
  · -- tgt: reverse.reverse.tgt = reverse.src = γ.tgt.
    show γ.tgt = γ.tgt
    rfl
  · -- toPath pointwise: reverse.reverse.toPath t = γ.toPath t.
    intro t
    -- reverse.toPath = γ.toPath.symm, so reverse.reverse.toPath
    -- = γ.toPath.symm.symm. mathlib's Path.symm_symm closes this.
    show γ.toPath.symm.symm t = γ.toPath t
    rw [Path.symm_symm]

end JacobianChallenge

end
