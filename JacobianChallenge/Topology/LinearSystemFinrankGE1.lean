/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LinearSystemConstants
import JacobianChallenge.Topology.ConstantsFinrank

set_option diagnostics.threshold 100

/-! # `linearSystemDeltaP p` is nontrivial: `finrank ≥ 1`

Since `linearSystemDeltaP p` contains the constants subspace
(zz354) and that subspace has `finrank = 1` over `ℂ` on Nonempty X
(zz356), the ambient linear system has `finrank ≥ 1`. This trivial
bound matters because the Riemann-Roch dimension hypothesis says
`finrank ≥ 2`, which is exactly "one more than the constants
dimension."

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff

set_option linter.unusedSectionVars false

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **`linearSystemDeltaP p` contains the constant function `1`**,
so it is non-trivial. -/
theorem linearSystemDeltaP_nontrivial [Nonempty X] (p : X) :
    Nontrivial (linearSystemDeltaP p) := by
  use ⟨0, (linearSystemDeltaP p).zero_mem⟩
  use ⟨(1 : X → ℂ), one_mem_linearSystemDeltaP p⟩
  intro h
  have h_val : (0 : X → ℂ) = (1 : X → ℂ) := Subtype.ext_iff.mp h
  exact one_ne_zero_in_pi h_val.symm

end JacobianChallenge

end
