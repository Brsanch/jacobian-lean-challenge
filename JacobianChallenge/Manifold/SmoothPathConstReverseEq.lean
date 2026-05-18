/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathExt
import JacobianChallenge.Manifold.SmoothPathReverse

set_option linter.unusedSectionVars false

/-! # The reverse of a constant smooth path equals itself

`SmoothPath.const I X P` is a constant smooth path at `P`. Its
reverse is also a constant path at `P` (since reversing doesn't
change the underlying constant-valued function). Via `SmoothPath.ext`
(chip 16), the two are equal as `SmoothPath` terms.

## What this file ships

* `SmoothPath.const_reverse` — `(SmoothPath.const I X P).reverse =
  SmoothPath.const I X P`.

This simplifies arguments involving constant paths under reversal,
e.g. when applying chip 18 (`single γ + single γ.reverse ∈
stokesBoundaries`) to a constant path.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-- **`(SmoothPath.const I X P).reverse = SmoothPath.const I X P`**.
The reverse of a constant path at `P` is the constant path at `P`. -/
@[simp] lemma SmoothPath.const_reverse (P : X) :
    (SmoothPath.const I X P).reverse = SmoothPath.const I X P := by
  apply SmoothPath.ext
  · -- src: reverse.src = const.tgt = P; const.src = P.
    show (SmoothPath.const I X P).tgt = (SmoothPath.const I X P).src
    rw [SmoothPath.const_src, SmoothPath.const_tgt]
  · -- tgt: reverse.tgt = const.src = P; const.tgt = P.
    show (SmoothPath.const I X P).src = (SmoothPath.const I X P).tgt
    rw [SmoothPath.const_src, SmoothPath.const_tgt]
  · -- toPath pointwise: reverse.toPath t = const.toPath (1-t) = P;
    -- const.toPath t = P.
    intro t
    -- `(SmoothPath.const I X P).reverse.toPath t
    --     = (SmoothPath.const I X P).toPath.symm t
    --     = (SmoothPath.const I X P).toPath (unitInterval.symm t)`.
    -- All of these evaluate to `P` (the constant path).
    show (SmoothPath.const I X P).toPath.symm t = (SmoothPath.const I X P).toPath t
    -- (Path.refl P).symm = Path.refl P essentially; both evaluate to P.
    rfl

end JacobianChallenge

end
