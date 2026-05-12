/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ResidueTheorem
import JacobianChallenge.Manifold.R4FibreSumBalance

/-! # Unconditional discharge of `R5_principal_degree_zero_statement`

`R5_principal_degree_zero_statement X` (in `Manifold/ResidueTheorem.lean`)
is, by definition,

  `∀ (f : MeromorphicNonzero X), (principalDivisorMap f).degree = 0`.

That is precisely the conclusion of
`R4FibreSumBalance.residue_theorem_unconditional` (which is already proven
in-tree, with no `sorry` / `axiom`, by composing the in-tree R4 chip
`R4_fibreSum_balance_statement_holds` with
`ResidueTheoremFromRsum.residue_theorem_of_R4`).

This file packages that composition as the single named theorem
`R5_principal_degree_zero_statement_holds`, which the headline
`residue_theorem` in `Manifold/ResidueTheorem.lean` consumes to close
its previous `sorry`.

No `sorry`, no `axiom`, no new mathematical content — purely a
defeq-level repackaging from `(principalDivisorMap f).degree = 0`
(quantified over `f`) to the named `Prop` `R5_principal_degree_zero_statement X`.
-/

@[expose] public section

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set OnePoint

namespace JacobianChallenge

namespace ResidueTheorem

universe u

variable (X : Type u)
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Unconditional discharge of `R5_principal_degree_zero_statement X`.**

The statement `R5_principal_degree_zero_statement X` unfolds to

  `∀ (f : MeromorphicNonzero X), (principalDivisorMap f).degree = 0`,

which is the conclusion of `R4FibreSumBalance.residue_theorem_unconditional`
quantified over `f`. -/
theorem R5_principal_degree_zero_statement_holds :
    R5_principal_degree_zero_statement X :=
  fun f => JacobianChallenge.R4FibreSumBalance.residue_theorem_unconditional X f

end ResidueTheorem

end JacobianChallenge

end

end
