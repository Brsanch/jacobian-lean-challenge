/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LinearSystemConstants
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option diagnostics.threshold 100

/-! # `dim_ℂ (constants ⊆ X → ℂ) = 1` on Nonempty X

For `X` nonempty, the ℂ-span of the constant function `(1 : X → ℂ)`
is one-dimensional. This is the formal target for "the constants
form a 1-dim subspace of `L(δp)`", which together with zz354's
strict-containment iff statement turns
`ExistsNonConstantBoundedByDeltaP_GenusZero` into a concrete
`finrank ≥ 2` statement.

This file ships:

* `one_ne_zero_in_pi` — `(1 : X → ℂ) ≠ 0` under `[Nonempty X]`.

* `finrank_span_one_eq_one` — `Module.finrank ℂ (Submodule.span ℂ
  {(1 : X → ℂ)}) = 1`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold

namespace JacobianChallenge

universe u

variable {X : Type u}

/-- **`1 ≠ 0` as a function `X → ℂ` when `X` is nonempty.** -/
lemma one_ne_zero_in_pi [Nonempty X] :
    (1 : X → ℂ) ≠ (0 : X → ℂ) := by
  intro h
  have hf := congr_fun h (Classical.arbitrary X)
  -- hf : (1 : X → ℂ) (Classical.arbitrary X) = (0 : X → ℂ) (Classical.arbitrary X)
  -- The two sides definitionally reduce to (1 : ℂ) and (0 : ℂ).
  exact one_ne_zero hf

/-- **The constants subspace of `X → ℂ` is one-dimensional.** -/
theorem finrank_span_one_eq_one [Nonempty X] :
    Module.finrank ℂ (Submodule.span ℂ ({(1 : X → ℂ)} : Set (X → ℂ))) = 1 := by
  rw [finrank_span_singleton (one_ne_zero_in_pi (X := X))]

end JacobianChallenge

end
