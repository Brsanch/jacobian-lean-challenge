/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodLatticeRankTwoG
import JacobianChallenge.Manifold.PeriodLatticeCompactQuotient

/-! # Wiring: discharge `CompactSpaceHypothesis` on `PeriodLatticeOfRankTwoG`

This file wires the unconditional discharge
`compactSpace_quotient_of_zlattice` (`PeriodLatticeCompactQuotient.lean`)
into the `PeriodLatticeOfRankTwoG` named-hypothesis bundle introduced in
`PeriodLatticeRankTwoG.lean`.

## What is collapsed

The bundle exposes three named hypotheses; this file discharges
`CompactSpaceHypothesis data` (item 11 of `OPEN.md`) unconditionally
once the lattice's underlying `Submodule ℤ` is registered as a
`ℤ`-lattice (`IsZLattice ℝ` + `DiscreteTopology`).

## Hypotheses *not* discharged here, with the concrete obstructions

* `ChartedSpaceHypothesis` (items 5 + 12). The `ChartedSpace`
  *component* is provided by `chartedSpace_quotient_of_zlattice` in
  `PeriodLatticeChartedSpace.lean`, but the `IsManifold` *component*
  the bundle field expects uses the **complex** model with corners
  `modelWithCornersSelf ℂ (Fin g → ℂ)`. The mathlib-keyed file
  `PeriodLatticeLieGroup.lean` produces an `IsManifold 𝓘(ℝ, E) n`
  instance for the **real** model. The two models are *not* defeq;
  upgrading from real-`C^n` chart-changes to complex-`ω` chart-changes
  would require a parallel proof that the transition maps `x ↦ x - λ`
  are `ContDiff ℂ ω` (true, since translations are complex-affine), but
  the real-model file does not export the `ContDiff ℂ`-flavoured
  `contDiffOn_chart_transition`. Closing this is a separate chip.

* `LieAddGroupHypothesis` (item 13). No mathlib-keyed
  `lieAddGroup_quotient_of_zlattice` lemma is landed in this repository
  at the pin (`PeriodLatticeLieGroup.lean` proves `IsManifold` only,
  not `LieAddGroup`).

## Anti-hack

The discharge takes `[DiscreteTopology data.lattice.toIntSubmodule]`
and `[IsZLattice ℝ data.lattice.toIntSubmodule]` as instance arguments.
For `g ≥ 1` and the trivial bundle hack `data.lattice = ⊥`, the
`IsZLattice ℝ ⊥` instance would require
`Submodule.span ℝ ((⊥ : Submodule ℤ _) : Set _) = ⊤`, which forces
`(⊥ : Submodule ℝ _) = ⊤`, false in real dimension `≥ 1`. So the
trivial-lattice hack is rejected at instance-class level — the same
way the bundle's `lattice_rank_eq` field rejects it at the
rank-certificate level.

## Why the discharge goes through `toIntSubmodule`

`compactSpace_quotient_of_zlattice` is stated for `L : Submodule ℤ E`.
The bundle stores `data.lattice : AddSubgroup E`. The two quotients are
the *same* underlying `Quotient`: by `Submodule.hasQuotient`, the
`Submodule ℤ`-quotient unfolds to a `QuotientAddGroup` quotient by
`toAddSubgroup`, and `AddSubgroup.toIntSubmodule_toAddSubgroup`
identifies that `AddSubgroup` with `data.lattice`.
-/

open scoped ContDiff Manifold

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The bundle quotient and the `Submodule ℤ` quotient have the same
underlying type. -/
private theorem JacobianOfLattice.eq_intSubmodule_quotient
    (data : PeriodLatticeOfRankTwoG X) :
    JacobianOfLattice X data =
      ((Fin (JacobianChallenge.genus X) → ℂ) ⧸ data.lattice.toIntSubmodule) := by
  -- `JacobianOfLattice X data := (Fin g → ℂ) ⧸ data.lattice`.
  -- The `Submodule.hasQuotient` instance unfolds to a `QuotientAddGroup`
  -- quotient by the underlying `AddSubgroup`, which is `data.lattice`
  -- itself by `AddSubgroup.toIntSubmodule_toAddSubgroup`.
  -- Both quotients have the same underlying `Quotient` type because
  -- `Submodule.hasQuotient` unfolds via `toAddSubgroup`, and
  -- `AddSubgroup.toIntSubmodule_toAddSubgroup` is the `rfl` round-trip.
  rfl

/-- Same as `eq_intSubmodule_quotient` but in the form needed by
`CompactSpace`-style transport: as a `HEq` on the topology. -/
private theorem JacobianOfLattice.compactSpace_iff
    (data : PeriodLatticeOfRankTwoG X) :
    CompactSpace (JacobianOfLattice X data) ↔
      CompactSpace
        ((Fin (JacobianChallenge.genus X) → ℂ) ⧸ data.lattice.toIntSubmodule) := by
  -- The two underlying types are definitionally the same `QuotientAddGroup`,
  -- because `Submodule.hasQuotient` unfolds via `toAddSubgroup` and
  -- `AddSubgroup.toIntSubmodule_toAddSubgroup` is `rfl` in the
  -- `Quotient.mk`-eq direction (`Submodule.toAddSubgroup_toIntSubmodule`
  -- of `AddSubgroup.toIntSubmodule`).
  -- Both topologies are the corresponding `instTopologicalSpaceQuotient`
  -- on the *same* underlying `Quotient`, so `CompactSpace` agrees.
  exact Iff.rfl

/-- **Wiring discharge of OPEN.md item 11.** The `CompactSpaceHypothesis`
of `PeriodLatticeOfRankTwoG` is automatic once the lattice is
registered as a `ℤ`-lattice. -/
theorem PeriodLatticeOfRankTwoG.compactSpaceHypothesis_holds
    (data : PeriodLatticeOfRankTwoG X)
    [DiscreteTopology data.lattice.toIntSubmodule]
    [IsZLattice ℝ data.lattice.toIntSubmodule] :
    JacobianOfLattice.CompactSpaceHypothesis data := by
  -- Goal unfolds to `CompactSpace (JacobianOfLattice X data)`.
  show CompactSpace (JacobianOfLattice X data)
  -- The mathlib lemma fires on the `Submodule ℤ`-quotient.
  have h :
      CompactSpace
        ((Fin (JacobianChallenge.genus X) → ℂ) ⧸ data.lattice.toIntSubmodule) :=
    compactSpace_quotient_of_zlattice data.lattice.toIntSubmodule
  -- Transport along the iff identification of the two quotients (defeq).
  exact (JacobianOfLattice.compactSpace_iff data).mpr h

end JacobianChallenge

end
