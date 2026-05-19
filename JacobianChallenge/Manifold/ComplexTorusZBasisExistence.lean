/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import JacobianChallenge.Manifold.ComplexTorusSmoothHurewiczFromBasis

set_option linter.unusedSectionVars false

/-! # ZLattice basis existence on `L ≤ ℂ` and unconditional
discharge of the basis hypothesis

For a discrete full-rank `ℤ`-lattice `L ≤ ℂ`, mathlib provides
`Module.Free ℤ L` (via `ZLattice.module_free`) with rank
`finrank ℤ L = finrank ℝ ℂ = 2`. Reindexing the chosen basis gives a
`Basis (Fin 2) ℤ L`.

Using this basis, we discharge `IsZBasisOfL L lam₁ lam₂` for the
specific pair `(lam₁, lam₂) := ((b 0 : ℂ), (b 1 : ℂ))`. Combined with
`smoothHurewiczHypothesisTorus_holds_of_basis` from
`ComplexTorusSmoothHurewiczFromBasis.lean`, this gives an
**unconditional existence** of a pair of lattice elements for which
`SmoothHurewiczHypothesisTorus` holds.

## What this file ships

* `ComplexTorus.basisFin2OfL` — explicit `Basis (Fin 2) ℤ L` via
  reindexing `Module.Free.chooseBasis`.
* `ComplexTorus.basisFin2OfL_isZBasisOfL` — `IsZBasisOfL L _ _` for
  the two basis elements.
* `ComplexTorus.exists_smoothHurewiczHypothesisTorus` — existence of
  `(lam₁, lam₂)` for which `SmoothHurewiczHypothesisTorus L lam₁ lam₂
  hlam₁ hlam₂` is unconditional.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## A `Fin 2`-indexed basis of `L` -/

/-- `finrank ℤ L = 2` for any discrete full-rank `ℤ`-lattice in `ℂ`. -/
theorem finrank_int_L_eq_two : Module.finrank ℤ L = 2 := by
  rw [ZLattice.rank ℝ L]
  exact Complex.finrank_real_complex

/-- The `Free.ChooseBasisIndex ℤ L` has cardinality `2`. -/
theorem chooseBasisIndex_card_eq_two :
    Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = 2 := by
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  rw [← Module.finrank_eq_card_chooseBasisIndex]
  exact finrank_int_L_eq_two L

/-- **An explicit `Basis (Fin 2) ℤ L`** for any discrete full-rank
`ℤ`-lattice in `ℂ`. -/
noncomputable def basisFin2OfL : Module.Basis (Fin 2) ℤ L := by
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  exact (Module.Free.chooseBasis ℤ L).reindex
    (Fintype.equivOfCardEq
      (by rw [chooseBasisIndex_card_eq_two]; rfl)).symm

/-! ## Decomposition: every `z ∈ L` is `m₁ • (b 0) + m₂ • (b 1)` -/

variable {L}

/-- **The basis-decomposition formula** for elements of `L`. -/
theorem basisFin2OfL_isZBasisOfL :
    IsZBasisOfL L ((basisFin2OfL L 0 : L) : ℂ) ((basisFin2OfL L 1 : L) : ℂ) := by
  intro z hz
  -- Set b := basisFin2OfL L.
  let b := basisFin2OfL L
  -- z lifted to L.
  set z' : L := ⟨z, hz⟩ with hz'_def
  -- Use b.repr z' to get integer coefficients.
  let c : Fin 2 →₀ ℤ := b.repr z'
  -- z = c 0 • b 0 + c 1 • b 1 in L (via Basis.sum_equivFun or repr_self_apply).
  -- In ℂ: (z' : ℂ) = c 0 • (b 0 : ℂ) + c 1 • (b 1 : ℂ).
  refine ⟨c 0, c 1, ?_⟩
  -- Derive the equality from `b.repr_total_apply` style results.
  -- z' = ∑ i, c i • b i (basis representation theorem).
  have h_sum : z' = ∑ i, c i • b i := (Module.Basis.sum_repr b z').symm
  -- Bring to ℂ via L.subtype.
  have h_sum_C : (z : ℂ) = ∑ i, c i • ((b i : L) : ℂ) := by
    have h_cast : ((z' : L) : ℂ) = z := rfl
    rw [← h_cast]
    rw [h_sum]
    push_cast
    rfl
  -- Unfold ∑ i over Fin 2.
  rw [Fin.sum_univ_two] at h_sum_C
  exact h_sum_C

/-! ## Headline existence -/

/-- **Unconditional existence** of a pair `(lam₁, lam₂) ∈ L²` for which
the smooth-Hurewicz hypothesis holds on `T_L = ℂ ⧸ L`. -/
theorem exists_smoothHurewiczHypothesisTorus :
    ∃ (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L),
      SmoothHurewiczHypothesisTorus L lam₁ lam₂ hlam₁ hlam₂ := by
  let b := basisFin2OfL L
  refine ⟨(b 0 : L), (b 1 : L), (b 0).property, (b 1).property, ?_⟩
  exact smoothHurewiczHypothesisTorus_holds_of_basis _ _ _ _
    (basisFin2OfL_isZBasisOfL)

end ComplexTorus

end JacobianChallenge

end
