/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianAnalyticStructure
import JacobianChallenge.Manifold.HJASFromHasPic0AnalyticEquiv

set_option linter.unusedSectionVars false

/-! # Smoke test: HJAS on `ℂ ⧸ L` via inferInstance

Validates that `HasJacobianAnalyticStructure (ℂ ⧸ L)` fires via
`inferInstance`. The instance is provided unconditionally in tree
via `instHasJacobianAnalyticStructure_complexTorus`. The new
[HJAE → HJAS] bridge instance provides an alternative route via
[HasPic0AnalyticEquiv (ℂ ⧸ L)] (which itself requires the two T_L
hypotheses TLDivSumHypothesis + TLAbelConverseHypothesis), but the
direct instance is unconditional.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Submodule

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- **HJAS T_L via inferInstance.** -/
example : HasJacobianAnalyticStructure (ℂ ⧸ L) := inferInstance

end ComplexTorus

end JacobianChallenge

end
