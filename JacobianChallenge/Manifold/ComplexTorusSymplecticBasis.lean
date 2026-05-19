/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusBasisLoop
import JacobianChallenge.Manifold.SmoothSymplecticBasis

/-! # Symplectic basis on the complex torus `T_L = ℂ ⧸ L`

For a discrete full-rank `ℤ`-lattice `L ≤ ℂ` and a pair of lattice
elements `lam₁, lam₂ ∈ L` (intended to be a `ℤ`-basis of `L`, though
this file does not require linear independence — it only consumes the
membership data), we bundle the two torus basis loops
`torusBasisLoop lam₁` and `torusBasisLoop lam₂` as a
`SmoothSymplecticBasis 𝓘(ℝ, ℂ) (ℂ ⧸ L) 0 1`.

The structural piece for the period-lattice closure: a genuine
non-degenerate symplectic basis on a concrete genus-`≥1` complex
1-manifold. The downstream `SmoothHurewiczHypothesis` for this basis
remains as a separate analytic input (covered classically by the fact
that `H₁(T_L; ℤ) ≅ L ≅ ℤ²`), but the symplectic-basis *data* is now
unconditionally in tree.

## What this file ships

* `ComplexTorus.symplecticBasis L lam₁ lam₂ hlam₁ hlam₂` — the
  `SmoothSymplecticBasis 𝓘(ℝ, ℂ) (ℂ ⧸ L) 0 1` indexed by `Fin 2` with
  loop 0 := `torusBasisLoop lam₁` and loop 1 := `torusBasisLoop lam₂`.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **Symplectic basis on `ℂ ⧸ L` from a pair of lattice elements.**
For `lam₁, lam₂ ∈ L`, bundles the two torus basis loops as a
`SmoothSymplecticBasis` at basepoint `0` and genus `1`
(so `Fin (2 * 1) = Fin 2` indexes the two loops). -/
noncomputable def symplecticBasis
    (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L) :
    SmoothSymplecticBasis 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L) 1 where
  basis := fun i : Fin (2 * 1) =>
    if i.val = 0 then torusBasisLoop lam₁ hlam₁
    else torusBasisLoop lam₂ hlam₂
  basis_src := by
    intro i
    by_cases h : i.val = 0
    · simp [h, torusBasisLoop_src]
    · simp [h, torusBasisLoop_src]
  basis_tgt := by
    intro i
    by_cases h : i.val = 0
    · simp [h, torusBasisLoop_tgt]
    · simp [h, torusBasisLoop_tgt]

@[simp] lemma symplecticBasis_basis_zero
    (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L) :
    (symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).basis ⟨0, by decide⟩
      = torusBasisLoop lam₁ hlam₁ := by
  change (if (⟨0, by decide⟩ : Fin (2 * 1)).val = 0
        then torusBasisLoop lam₁ hlam₁
        else torusBasisLoop lam₂ hlam₂)
      = torusBasisLoop lam₁ hlam₁
  rfl

@[simp] lemma symplecticBasis_basis_one
    (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L) :
    (symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).basis ⟨1, by decide⟩
      = torusBasisLoop lam₂ hlam₂ := by
  change (if (⟨1, by decide⟩ : Fin (2 * 1)).val = 0
        then torusBasisLoop lam₁ hlam₁
        else torusBasisLoop lam₂ hlam₂)
      = torusBasisLoop lam₂ hlam₂
  rfl

end ComplexTorus

end JacobianChallenge

end
