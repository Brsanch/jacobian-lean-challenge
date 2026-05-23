/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.PrincipalDivisorRange
import JacobianChallenge.Manifold.ResidueTheoremUnconditional

set_option diagnostics.threshold 100

/-! # Unconditional discharge of `ResidueTheorem X` and consequences

The `def Prop` `JacobianChallenge.ResidueTheorem X` in
`Divisor/PrincipalDivisorRange.lean` is stated as a named-hypothesis
classical input:

  `∀ f : MeromorphicNonzero X, (principalDivisorMap f).degree = 0`.

The headline theorem `JacobianChallenge.residue_theorem` in
`Manifold/ResidueTheoremUnconditional.lean` is precisely this statement,
discharged unconditionally via the topological-degree / Hurwitz chain:

  `nearbyRegularWitnessHypothesis_holds_unconditional`
  → `ramificationSumEqualsDegree_holds_unconditional`
  → `R4FibreSumBalance.residue_theorem_unconditional`
  → `ResidueTheorem.R5_principal_degree_zero_statement_holds`
  → `JacobianChallenge.residue_theorem`.

This file closes the wiring gap between the `def Prop` and the proven
headline, then derives the consequence
`PrincDivHonestCandidate X ≤ Div0 X` via the existing biconditional
`residueTheorem_iff_range_le_Div0`. After this file, the
`PrincDiv = Div0` story underlying `Pic0 X` is honest unconditionally —
every principal divisor of a non-zero global meromorphic function lies
in the degree-zero subgroup, with no remaining classical-input hypothesis.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

variable (X : Type u)
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **The named hypothesis `ResidueTheorem X` is discharged unconditionally.**

Wires `JacobianChallenge.residue_theorem` (proved via the topological-degree
chain in `Manifold/ResidueTheoremUnconditional.lean`) into the `def Prop`
in `Divisor/PrincipalDivisorRange.lean`. Pure repackaging, no new content. -/
theorem residueTheorem_holds : ResidueTheorem X :=
  fun f => residue_theorem f

/-- **Consequence: `PrincDivHonestCandidate X ≤ Div0 X` unconditionally.**

Combines `residueTheorem_holds` with the existing biconditional
`residueTheorem_iff_range_le_Div0`. After this lemma every divisor in
`PrincDivHonestCandidate X` lies in `Div0 X`, so the Picard-group
quotient `Pic0 X = Div0 X / PrincDivHonestCandidate.addSubgroupOf Div0`
is a quotient of honest subgroups rather than resting on a named
classical input. -/
theorem princDivHonestCandidate_le_Div0 :
    PrincDivHonestCandidate X ≤ Div0 X :=
  (residueTheorem_iff_range_le_Div0 (X := X)).mp (residueTheorem_holds X)

end JacobianChallenge

end
