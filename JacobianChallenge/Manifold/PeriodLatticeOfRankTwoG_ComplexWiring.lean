/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodLatticeRankTwoG
import JacobianChallenge.Manifold.PeriodLatticeComplexQuotient

/-! # Wiring: discharge `ChartedSpaceHypothesis` on `PeriodLatticeOfRankTwoG`

Companion to `PeriodLatticeOfRankTwoG_Wiring.lean` (which discharged
`CompactSpaceHypothesis`).

This file consumes the **complex-model** charted-space + `IsManifold`
instances landed by `PeriodLatticeComplexQuotient.lean` (ZZ140) and
discharges, on the named-hypothesis bundle `PeriodLatticeOfRankTwoG`,
the bundled hypothesis

* `ChartedSpaceHypothesis data` — items 5 + 12 of `OPEN.md` together.

The discharge is unconditional once the lattice's underlying
`Submodule ℤ` is registered as a `ℤ`-lattice
(`IsZLattice ℝ` + `DiscreteTopology`). The two underlying quotients
(bundle's `AddSubgroup`-quotient vs mathlib's `Submodule ℤ`-quotient)
are definitionally the same type, so the discharge is by transport
along `rfl`-level identifications.

## Hypothesis *not* discharged here

* `LieAddGroupHypothesis` (item 13). At the current pin no mathlib-keyed
  `LieAddGroup` instance is landed for `(Fin g → ℂ) ⧸ Λ` — the companion
  `PeriodLatticeLieGroup.lean` produces only `IsManifold` for the real
  model, and `PeriodLatticeComplexQuotient.lean` upgrades that to the
  complex model but does not export `LieAddGroup`. Closing item 13 is a
  separate chip that needs `ContMDiff`-of-add/neg through the local
  charts.
-/

open scoped ContDiff Manifold

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Wiring discharge of OPEN.md items 5 + 12.** The
`ChartedSpaceHypothesis` of `PeriodLatticeOfRankTwoG` is automatic once
the lattice is registered as a `ℤ`-lattice. Both components
(`ChartedSpace` and complex-model `IsManifold ω`) are pulled directly
from `PeriodLatticeChartedSpace` / `PeriodLatticeComplexQuotient`. -/
noncomputable def PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds
    (data : PeriodLatticeOfRankTwoG X)
    [DiscreteTopology data.lattice.toIntSubmodule]
    [IsZLattice ℝ data.lattice.toIntSubmodule] :
    JacobianOfLattice.ChartedSpaceHypothesis data :=
  { toChartedSpace :=
      (chartedSpace_quotient_of_zlattice
        (L := data.lattice.toIntSubmodule) :
          ChartedSpace (Fin (JacobianChallenge.genus X) → ℂ)
            (JacobianOfLattice X data))
    toIsManifold :=
      (complex_isManifold_quotient_of_zlattice
        (L := data.lattice.toIntSubmodule) ω :
          @IsManifold ℂ _ (Fin (JacobianChallenge.genus X) → ℂ) _ _
            (Fin (JacobianChallenge.genus X) → ℂ) _
            (modelWithCornersSelf ℂ (Fin (JacobianChallenge.genus X) → ℂ)) ω
            (JacobianOfLattice X data) _
            (chartedSpace_quotient_of_zlattice
              (L := data.lattice.toIntSubmodule))) }

end JacobianChallenge

end
