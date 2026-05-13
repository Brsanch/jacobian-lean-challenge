/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.R5Unconditional

/-! # Unconditional discharge of the headline `residue_theorem`

The headline `JacobianChallenge.residue_theorem` formerly lived in
`Manifold/ResidueTheorem.lean` as a skeleton with one `sorry` against the
named owed input `R5_principal_degree_zero_statement X`. Once
`R5_principal_degree_zero_statement_holds` landed (in
`Manifold/R5Unconditional.lean`, composing the in-tree R1+R2+R3+R4 chain),
that sorry became dischargeable in one line. The skeleton in
`Manifold/ResidueTheorem.lean` has been removed; this file is now the
canonical site of the headline.

No `sorry`, no `axiom`, no new mathematical content — purely a defeq-level
repackaging of `R5_principal_degree_zero_statement_holds`.
-/

@[expose] public section

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

/-- The **residue theorem** on a compact connected Riemann surface: for every
non-zero global meromorphic function `f`, the principal divisor `(f)` has
degree zero, i.e. `∑_x ord_x f = 0`.

Unconditional discharge composing the in-tree R1+R2+R3+R4 chain via
`ResidueTheorem.R5_principal_degree_zero_statement_holds`. -/
theorem residue_theorem
    {X : Type u}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (f : MeromorphicNonzero X) :
    (principalDivisorMap f).degree = 0 :=
  ResidueTheorem.R5_principal_degree_zero_statement_holds X f

end JacobianChallenge

end

end
