/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodLatticeOfRankTwoG_ComplexWiring
import JacobianChallenge.Manifold.PeriodLatticeLieGroupAdd

/-! # Wiring: discharge `LieAddGroupHypothesis` on `PeriodLatticeOfRankTwoG`

Final companion to `PeriodLatticeOfRankTwoG_Wiring.lean` (discharged
`CompactSpaceHypothesis`) and `PeriodLatticeOfRankTwoG_ComplexWiring.lean`
(discharged `ChartedSpaceHypothesis`).

This file consumes the **complex-`ω` Lie-group** instance landed by
`PeriodLatticeLieGroupAdd.lean` (this session) and discharges, on the
named-hypothesis bundle `PeriodLatticeOfRankTwoG`, the bundled hypothesis

* `LieAddGroupHypothesis data charts` — item 13 of `OPEN.md`.

The discharge takes `[DiscreteTopology data.lattice.toIntSubmodule]` and
`[IsZLattice ℝ data.lattice.toIntSubmodule]` as instance arguments, and
the canonical `charts := chartedSpaceHypothesis_holds data` produced by
the sister wiring file. Combined with the prior two wiring discharges,
all three named hypotheses on `PeriodLatticeOfRankTwoG` are now
unconditional once the lattice is registered as a `ℤ`-lattice.

## Anti-hack

Same `DiscreteTopology` + `IsZLattice ℝ` instance arguments reject the
trivial-bundle hack `data.lattice = ⊥` (for `g ≥ 1`): the
`IsZLattice ℝ ⊥` instance would force the trivial submodule to be a
real basis, false in real dimension `≥ 1`.
-/

open scoped ContDiff Manifold

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- **Wiring discharge of OPEN.md item 13.** The `LieAddGroupHypothesis`
of `PeriodLatticeOfRankTwoG` is automatic once the lattice is registered
as a `ℤ`-lattice. -/
theorem PeriodLatticeOfRankTwoG.lieAddGroupHypothesis_holds
    (data : PeriodLatticeOfRankTwoG X)
    [DiscreteTopology data.lattice.toIntSubmodule]
    [IsZLattice ℝ data.lattice.toIntSubmodule] :
    JacobianOfLattice.LieAddGroupHypothesis data
      (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds data) := by
  -- Unfold to the bare `LieAddGroup` instance on `JacobianOfLattice X data`
  -- with the canonical chart bundle. Both the type and the `ChartedSpace`
  -- instance are `rfl`-defeq to the corresponding `Submodule ℤ`-quotient
  -- versions.
  show
    @LieAddGroup ℂ _ (Fin (JacobianChallenge.genus X) → ℂ) _
      (Fin (JacobianChallenge.genus X) → ℂ) _ _
      (modelWithCornersSelf ℂ (Fin (JacobianChallenge.genus X) → ℂ)) ω
      (JacobianOfLattice X data) _ _
      (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds data).toChartedSpace
  -- The default-instance from `lieAddGroup_quotient_of_zlattice` fires
  -- on `(Fin g → ℂ) ⧸ data.lattice.toIntSubmodule` with its default
  -- `chartedSpace_quotient_of_zlattice` instance. The `JacobianOfLattice
  -- X data` type and the `chartedSpaceHypothesis_holds` chart bundle
  -- coincide with these by `rfl` (`JacobianOfLattice.eq_intSubmodule_quotient`
  -- is `rfl`-level on the underlying type, and the chart bundle's
  -- `toChartedSpace` is built from `chartedSpace_quotient_of_zlattice` of
  -- the same lattice).
  exact lieAddGroup_quotient_of_zlattice data.lattice.toIntSubmodule ω

end JacobianChallenge

end
