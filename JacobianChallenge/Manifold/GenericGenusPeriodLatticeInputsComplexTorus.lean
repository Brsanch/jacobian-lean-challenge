/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodLatticeSymplecticBundleComplexTorus
import JacobianChallenge.Manifold.GenericGenusPeriodLatticeInputsFromSmoothHurewicz

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Explicit `GenericGenusPeriodLatticeInputs` on `T_L = ℂ ⧸ L`

`nonempty_periodLatticeSymplecticBundle_complexTorus` constructs the
PLSB Nonempty witness but discards the underlying term. Here we ship
the explicit terms — keyed off a chosen `IsZBasisOfL` pair from
`basisFin2OfL L`:

* `cycleGens_complexTorus L : Fin (2 * genus (ℂ ⧸ L)) → (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)).H1`
  — the explicit symplectic-basis cycles
  `(symplecticBasis L lam₁ lam₂ _ _).reindex (genus_eq_one L) .cycleGens`.

* `genericGenusPeriodLatticeInputs_complexTorus L :
    GenericGenusPeriodLatticeInputs (basis_g_dz L)`
  — the explicit four-atom record.

* Downstream chips access this term's `.toBundle` (an explicit
  `C3PeriodLatticeStokesSpanTopInputs (basis_g_dz L)`) to invoke
  `homologyGeneration_of_spans_top` for per-cycle decomposition.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## The chosen `lam₁ / lam₂` pair from `basisFin2OfL L` -/

/-- The first chosen lattice generator on `T_L`: `basisFin2OfL L 0`
coerced to `ℂ`. -/
noncomputable def lam₁_complexTorus : ℂ := ((basisFin2OfL L 0 : L) : ℂ)

/-- The second chosen lattice generator on `T_L`. -/
noncomputable def lam₂_complexTorus : ℂ := ((basisFin2OfL L 1 : L) : ℂ)

lemma lam₁_complexTorus_mem : lam₁_complexTorus L ∈ L :=
  (basisFin2OfL L 0).property

lemma lam₂_complexTorus_mem : lam₂_complexTorus L ∈ L :=
  (basisFin2OfL L 1).property

/-! ## The explicit symplectic basis and `cycleGens` -/

/-- **The dim-1 symplectic basis on T_L** at the chosen
`lam₁ / lam₂`. -/
noncomputable def symplecticBasisOne :
    SmoothSymplecticBasis 𝓘(ℝ, ℂ) (ℂ ⧸ L) 0 1 :=
  symplecticBasis L (lam₁_complexTorus L) (lam₂_complexTorus L)
    (lam₁_complexTorus_mem L) (lam₂_complexTorus_mem L)

/-- **The dim-`genus T_L` symplectic basis on T_L**, reindexed from
the dim-1 version. -/
noncomputable def symplecticBasisG :
    SmoothSymplecticBasis 𝓘(ℝ, ℂ) (ℂ ⧸ L) 0
      (JacobianChallenge.genus (ℂ ⧸ L)) :=
  (symplecticBasisOne L).reindex (genus_eq_one L)

/-- **The explicit `cycleGens` tuple on T_L.** -/
noncomputable def cycleGens_complexTorus :
    Fin (2 * JacobianChallenge.genus (ℂ ⧸ L))
      → (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)).H1 :=
  (symplecticBasisG L).cycleGens

/-! ## The explicit `GenericGenusPeriodLatticeInputs` -/

/-- **The explicit four-atom `GenericGenusPeriodLatticeInputs` record
on T_L.** -/
noncomputable def genericGenusPeriodLatticeInputs_complexTorus :
    GenericGenusPeriodLatticeInputs (basis_g_dz L) := by
  have hSH_torus :
      SmoothHurewiczHypothesisTorus L (lam₁_complexTorus L) (lam₂_complexTorus L)
        (lam₁_complexTorus_mem L) (lam₂_complexTorus_mem L) :=
    smoothHurewiczHypothesisTorus_holds_of_basis _ _ _ _ basisFin2OfL_isZBasisOfL
  have hSH_g : SmoothHurewiczHypothesis (symplecticBasisG L) :=
    SmoothHurewiczHypothesis.reindex (symplecticBasisOne L) (genus_eq_one L) hSH_torus
  exact GenericGenusPeriodLatticeInputs.ofSmoothHurewicz
    (basis := basis_g_dz L)
    (p₀ := (0 : ℂ ⧸ L))
    (sb := symplecticBasisG L)
    (riemannBilinear :=
      riemannBilinear_transport L (lam₁_complexTorus L) (lam₂_complexTorus L)
        (lam₁_complexTorus_mem L) (lam₂_complexTorus_mem L)
        (basisFin2OfL_realLinearIndependent L))
    (holomorphicCanonicalClosed := holomorphicComponentsCanonicalClosed_holds L)
    (α := α L) (h_α_src := α_src L) (h_α_tgt := α_tgt L)
    (smoothHurewicz := hSH_g)

@[simp] lemma genericGenusPeriodLatticeInputs_complexTorus_cycleGens :
    (genericGenusPeriodLatticeInputs_complexTorus L).cycleGens
      = cycleGens_complexTorus L := rfl

/-! ## Promote to `C3PeriodLatticeStokesSpanTopInputs` and PLSB -/

/-- **The explicit `C3PeriodLatticeStokesSpanTopInputs` on T_L.** -/
noncomputable def c3StokesSpanTopInputs_complexTorus :
    C3PeriodLatticeStokesSpanTopInputs (basis_g_dz L) :=
  (genericGenusPeriodLatticeInputs_complexTorus L).toBundle

/-- **The explicit PLSB on T_L.** -/
noncomputable def periodLatticeSymplecticBundle_complexTorus :
    PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L) :=
  (c3StokesSpanTopInputs_complexTorus L).toBundle

@[simp] lemma c3StokesSpanTopInputs_complexTorus_cycleGens :
    (c3StokesSpanTopInputs_complexTorus L).cycleGens
      = cycleGens_complexTorus L := rfl

@[simp] lemma c3StokesSpanTopInputs_complexTorus_stokes :
    (c3StokesSpanTopInputs_complexTorus L).stokes
      = StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) (ℂ ⧸ L) := rfl

end ComplexTorus

end JacobianChallenge

end
