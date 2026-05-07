/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-! # Compactness of `E ⧸ L` for a `ℤ`-lattice `L` in finite-dimensional `E`

This file discharges the named hypothesis `compactSpace_of_lattice` of
`PeriodLatticeRankTwoG.lean` for the general case where the ambient space is a
finite-dimensional real normed space and the candidate lattice is registered as
an `IsZLattice ℝ` with `DiscreteTopology`.

The classical fact is: `ℝ^n / Λ` is compact whenever `Λ` is a full-rank discrete
`ℤ`-submodule of `ℝ^n` (the quotient is the `n`-torus). The mathlib ingredient is
`IsZLattice.isCompact_range_of_periodic`, which says that any continuous
`Λ`-periodic function out of `E` has compact range. Applied to the natural
quotient map `E → E ⧸ Λ`, this gives `IsCompact (Set.range mkQ)`. Surjectivity of
the quotient map then upgrades this to `CompactSpace`.

The result is stated for `Submodule ℤ E`. The `AddSubgroup` flavour used by
`PeriodLatticeOfRankTwoG` can be obtained by routing through
`AddSubgroup.toIntSubmodule`.
-/

open Submodule

namespace JacobianChallenge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- For a finite-dimensional real normed space `E` and a discrete full-rank
`ℤ`-lattice `L` in `E`, the quotient `E ⧸ L` is a compact topological space. -/
theorem compactSpace_quotient_of_zlattice
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    CompactSpace (E ⧸ L) := by
  -- The quotient map `E → E ⧸ L` is continuous, surjective, and `L`-periodic.
  -- `IsZLattice.isCompact_range_of_periodic` gives compactness of its range,
  -- which equals the whole quotient by surjectivity.
  refine ⟨?_⟩
  have hsurj : Set.range (L.mkQ) = Set.univ := L.mkQ_surjective.range_eq
  rw [← hsurj]
  refine IsZLattice.isCompact_range_of_periodic (E := E) (F := E ⧸ L) L
    (f := fun x => L.mkQ x) ?_ ?_
  · exact continuous_quot_mk
  · intro z w hw
    show L.mkQ (z + w) = L.mkQ z
    have hw0 : L.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero L).mpr hw
    rw [map_add, hw0, add_zero]

end JacobianChallenge
