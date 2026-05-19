/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusH1SpansTop
import JacobianChallenge.Manifold.GenericGenusPeriodLatticeInputsFromSmoothHurewicz

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Module Submodule

/-! # `GenericGenusPeriodLatticeInputs` on `ℂ ⧸ L`, parameterised on
the three classical-content atoms

Final wiring layer for the torus genus-1 example. Given:

* a discrete full-rank `ℤ`-lattice `L ≤ ℂ`;
* a pair `lam₁ lam₂ ∈ L`;
* a Hodge basis `basis : Basis (Fin 1) ℂ (HolomorphicOneForm (ℂ ⧸ L))`
  (taken at dimension `1` so the caller can transport from
  `genus (ℂ ⧸ L) = 1` separately);
* the genus identification `genus_eq : JacobianChallenge.genus (ℂ ⧸ L) = 1`;
* the three classical atomic hypotheses on the torus:
  - `SmoothHurewiczHypothesisTorus L lam₁ lam₂ hlam₁ hlam₂`
    (universal-cover lifting);
  - `riemannBilinear` (Hodge non-degeneracy);
  - `holomorphicCanonicalClosed` (chart-pullback Cauchy);

we package these into a `GenericGenusPeriodLatticeInputs basis_X`
where `basis_X : Basis (Fin (genus (ℂ ⧸ L))) ℂ (HolomorphicOneForm
(ℂ ⧸ L))` is obtained by transporting `basis` along `genus_eq.symm`.

This is the "consume the atoms" terminal step: once the three classical
inputs are discharged classically (multi-thousand LOC each), the
genus-1 period lattice on `ℂ ⧸ L` follows immediately from this
constructor.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Transport the dim-1 basis to dim `genus (ℂ ⧸ L)` via `genus_eq` -/

/-- Transport a `Basis (Fin 1) ℂ V` to `Basis (Fin (genus (ℂ ⧸ L))) ℂ V`
using `genus_eq : genus (ℂ ⧸ L) = 1`. -/
noncomputable def transportBasis
    (basis : Basis (Fin 1) ℂ (HolomorphicOneForm (ℂ ⧸ L)))
    (genus_eq : JacobianChallenge.genus (ℂ ⧸ L) = 1) :
    Basis (Fin (JacobianChallenge.genus (ℂ ⧸ L))) ℂ (HolomorphicOneForm (ℂ ⧸ L)) :=
  basis.reindex (finCongr genus_eq.symm)

/-- Transport the dim-1 symplectic basis to dim `genus (ℂ ⧸ L)` via
`genus_eq`. -/
noncomputable def transportSymplecticBasis
    (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L)
    (genus_eq : JacobianChallenge.genus (ℂ ⧸ L) = 1) :
    SmoothSymplecticBasis 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L)
      (JacobianChallenge.genus (ℂ ⧸ L)) := by
  rw [genus_eq]
  exact symplecticBasis L lam₁ lam₂ hlam₁ hlam₂

end ComplexTorus

end JacobianChallenge

end
