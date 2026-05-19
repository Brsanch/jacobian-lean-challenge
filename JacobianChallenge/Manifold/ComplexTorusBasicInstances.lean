/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorus
import JacobianChallenge.Manifold.PeriodLatticeCompactQuotient
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

set_option linter.unusedSectionVars false

/-! # Basic instances on the complex torus `ℂ ⧸ L`

Registers as Lean `instance`s the basic topological facts about the
complex torus needed to feed into the Forster-Riesz finite-dimensionality
arc (`holomorphicOneFormFiniteDim_holds`):

* `Nonempty (ℂ ⧸ L)` — via the zero class.
* `CompactSpace (ℂ ⧸ L)` — wraps `compactSpace_quotient_of_zlattice`
  (theorem) as an instance.
* `T2Space (ℂ ⧸ L)` — derives from the in-mathlib
  `Submodule.Quotient.normedAddCommGroup` (which requires `IsClosed
  (L : Set ℂ)`, supplied by `AddSubgroup.isClosed_of_discrete` on
  `L.toAddSubgroup`).

All three are necessary preconditions for invoking
`DiskChartCover.holomorphicOneFormFiniteDim_holds` on `ℂ ⧸ L`.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Nonempty -/

instance instNonempty : Nonempty (ℂ ⧸ L) := ⟨0⟩

/-! ## CompactSpace -/

instance instCompactSpace : CompactSpace (ℂ ⧸ L) :=
  compactSpace_quotient_of_zlattice L

/-! ## T2Space -/

/-- The underlying set of `L : Submodule ℤ ℂ` is closed in `ℂ`, since
`L` carries the discrete topology and `ℂ` is `T2Space`. -/
lemma isClosed_lattice : IsClosed (L : Set ℂ) := by
  -- DiscreteTopology on the Submodule transfers to the underlying AddSubgroup.
  haveI : DiscreteTopology (L.toAddSubgroup : AddSubgroup ℂ) := by
    -- The two subtypes have the same underlying topological space.
    -- DiscreteTopology depends only on the topological structure on the subtype.
    -- Since L and L.toAddSubgroup have the same underlying set (and the same
    -- subspace topology), the DiscreteTopology instance transfers.
    show DiscreteTopology { x : ℂ // x ∈ L }
    infer_instance
  -- AddSubgroup.isClosed_of_discrete needs T2 ambient.
  exact (L.toAddSubgroup.isClosed_of_discrete)

/-- **`T2Space (ℂ ⧸ L)`** via the `NormedAddCommGroup` instance on the
quotient by a closed subgroup, which provides a `MetricSpace` structure
(hence T2). -/
instance instT2Space : T2Space (ℂ ⧸ L) := by
  haveI hL : IsClosed (L : Set ℂ) := isClosed_lattice L
  -- `Submodule.Quotient.normedAddCommGroup [IsClosed (L : Set ℂ)] :
  --   NormedAddCommGroup (ℂ ⧸ L)`. NormedAddCommGroup → MetricSpace → T2Space.
  haveI : NormedAddCommGroup (ℂ ⧸ L) :=
    Submodule.Quotient.normedAddCommGroup L
  infer_instance

end ComplexTorus

end JacobianChallenge

end
