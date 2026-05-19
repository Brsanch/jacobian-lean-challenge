/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorus
import JacobianChallenge.Manifold.ComplexTorusBasicInstances
import Mathlib.Topology.Covering.Quotient

set_option linter.unusedSectionVars false

/-! # `L.mkQ : ℂ → ℂ ⧸ L` is a covering map

Mathlib has `AddSubgroup.isQuotientCoveringMap_of_comm` for any
commutative additive topological group with a discrete additive
subgroup. We apply this with `G := ℂ` and `S := L.toAddSubgroup` to
obtain `IsCoveringMap (L.mkQ : ℂ → ℂ ⧸ L)`.

The Lean types `ℂ ⧸ L` (Submodule notation) and `ℂ ⧸ L.toAddSubgroup`
(QuotientAddGroup notation) coincide via
`Submodule.Quotient.quotientAddGroupMk_eq_mk`.

## What this file ships

* `ComplexTorus.mkQ_isCoveringMap` — `IsCoveringMap (L.mkQ : ℂ → ℂ ⧸ L)`.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Discreteness of `L.toAddSubgroup` -/

private lemma toAddSubgroup_isDiscrete :
    IsDiscrete (L.toAddSubgroup : Set ℂ) := by
  -- L.toAddSubgroup has the same underlying set as L. DiscreteTopology
  -- transfers via the SetLike-iff.
  rw [SetLike.isDiscrete_iff_discreteTopology]
  -- Show DiscreteTopology of L.toAddSubgroup.
  -- The two subtypes (L : Submodule) and L.toAddSubgroup have the same
  -- underlying type and topology.
  show DiscreteTopology { x : ℂ // x ∈ L.toAddSubgroup }
  -- L.toAddSubgroup.mem coincides with L.mem (both are "in L's underlying set").
  infer_instance

/-! ## `mkQ` as a covering map -/

/-- **`L.mkQ : ℂ → ℂ ⧸ L` is a covering map.** Applies
`AddSubgroup.isQuotientCoveringMap_of_comm` with `G := ℂ`
(commutative additive topological group) and `S := L.toAddSubgroup`
(discrete). The Submodule quotient `ℂ ⧸ L` and the AddGroup quotient
`ℂ ⧸ L.toAddSubgroup` are the same Lean type (with appropriate
notational coercions handled by mathlib's quotient infrastructure). -/
theorem mkQ_isCoveringMap :
    IsCoveringMap (L.mkQ : ℂ → ℂ ⧸ L) := by
  -- mkQ is essentially QuotientAddGroup.mk for L.toAddSubgroup.
  -- AddSubgroup.isQuotientCoveringMap_of_comm gives IsQuotientCoveringMap;
  -- IsCoveringMap follows via `IsQuotientCoveringMap.isCoveringMap`.
  have h_disc : IsDiscrete (L.toAddSubgroup : Set ℂ) :=
    toAddSubgroup_isDiscrete L
  have h_quotient := AddSubgroup.isAddQuotientCoveringMap_of_comm
    L.toAddSubgroup h_disc
  -- h_quotient : IsAddQuotientCoveringMap (QuotientAddGroup.mk : ℂ → ℂ ⧸ L.toAddSubgroup) L.toAddSubgroup.
  have h_cov := h_quotient.isCoveringMap
  -- `L.mkQ x = QuotientAddGroup.mk x` definitionally (via Submodule.Quotient.quotientAddGroupMk_eq_mk).
  have h_eq : (L.mkQ : ℂ → ℂ ⧸ L) = (QuotientAddGroup.mk : ℂ → ℂ ⧸ L.toAddSubgroup) := by
    funext x
    exact (Submodule.Quotient.quotientAddGroupMk_eq_mk x).symm
  rw [h_eq]
  exact h_cov

end ComplexTorus

end JacobianChallenge

end
