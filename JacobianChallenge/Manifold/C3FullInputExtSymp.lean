/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3FullInputSymp
import JacobianChallenge.Manifold.JacobianAnalyticOfCurveContMDiff
import JacobianChallenge.Manifold.JacobianAnalyticOfCurveInjective
import JacobianChallenge.Manifold.C3FullInputExt

set_option linter.unusedSectionVars false

/-! # `C3FullInputExtSymp X` — extended C3 input over the symplectic bundle

Mirrors `C3FullInputExt` against the corrected
`PeriodLatticeSymplecticBundle`. Carries the two additional predicates
needed for items 16, 17 on the analytic Jacobian:

* `AbelJacobiSmoothnessSymp` — `ContMDiff` of `B.abelJacobiPoint` into
  `AnalyticJacobianSymp`.
* `AbelJacobiInjectiveSymp` — injectivity (under `0 < genus X`).

The legacy versions in `JacobianAnalyticOfCurveContMDiff.lean` /
`JacobianAnalyticOfCurveInjective.lean` are stated against
`AnalyticJacobian` parametrised by a legacy bundle. The symplectic
versions are stated against `AnalyticJacobianSymp` parametrised by a
symplectic bundle. The two `AnalyticJacobian` types are definitionally
equal (both reduce to `(Fin g → ℂ) ⧸ (periodLatticeImage data α).toIntSubmodule`),
so the conversion of the predicates along `toSymp` is term-level
straightforward.

## What this file ships

* `AbelJacobiSmoothnessSymp` — `ContMDiff` predicate (symplectic).
* `AbelJacobiInjectiveSymp` — injectivity predicate (symplectic).
* `AbelJacobiInjectiveSymp.relAbelJacobi_injective` — corollary at the
  relative-AJ level.
* `C3FullInputExtSymp` — 3-field structure (base + smoothness + injective).
* `C3FullInputExt.toSymp` — legacy → symplectic conversion.

No `sorry`, no `axiom`. -/

open scoped ContDiff Manifold
open Submodule Module

noncomputable section

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ⊤ X]

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) α}

/-! ## Symplectic predicates -/

/-- **Item 17 predicate (symplectic).** `ContMDiff` of
`B.abelJacobiPoint : X → AnalyticJacobianSymp …`. -/
def AbelJacobiSmoothnessSymp
    (B : AbelJacobiInputSymp α h)
    [DiscreteTopology
      (PeriodLatticeOfRankTwoG.ofSymplectic
        (PeriodPairingData.ofSmoothCycle X) α h).lattice.toIntSubmodule]
    [IsZLattice ℝ
      (PeriodLatticeOfRankTwoG.ofSymplectic
        (PeriodPairingData.ofSmoothCycle X) α h).lattice.toIntSubmodule] : Prop :=
  haveI := (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds
    (PeriodLatticeOfRankTwoG.ofSymplectic
      (PeriodPairingData.ofSmoothCycle X) α h)).toChartedSpace
  ContMDiff (𝓘(ℂ, ℂ))
    (𝓘(ℂ, Fin (JacobianChallenge.genus X) → ℂ)) ω
    (B.abelJacobiPoint :
      X → AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle X) α h)

/-- **Item 16 predicate (symplectic).** Injectivity of `B.abelJacobiPoint`
under `0 < genus X`. -/
def AbelJacobiInjectiveSymp (B : AbelJacobiInputSymp α h) : Prop :=
  0 < JacobianChallenge.genus X →
    Function.Injective
      (B.abelJacobiPoint :
        X → AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle X) α h)

/-- Corollary: under `AbelJacobiInjectiveSymp`, the relative AJ map is
also injective. Mirrors `AbelJacobiInjective.relAbelJacobi_injective`. -/
theorem AbelJacobiInjectiveSymp.relAbelJacobi_injective
    (B : AbelJacobiInputSymp α h) (hinj : AbelJacobiInjectiveSymp B)
    (hpos : 0 < JacobianChallenge.genus X) (P : X) :
    Function.Injective
      (fun Q : X => B.relAbelJacobi P Q :
        X → AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle X) α h) := by
  intro Q₁ Q₂ hQ
  have h_eq : B.abelJacobiPoint Q₁ = B.abelJacobiPoint Q₂ := by
    have hQ' : B.abelJacobiPoint Q₁ - B.abelJacobiPoint P =
        B.abelJacobiPoint Q₂ - B.abelJacobiPoint P := hQ
    have := congrArg (· + B.abelJacobiPoint P) hQ'
    simp only [sub_add_cancel] at this
    exact this
  exact hinj hpos h_eq

end JacobianChallenge

/-! ## `C3FullInputExtSymp` bundle -/

namespace JacobianChallenge

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Extended C3 input (symplectic)**: `C3FullInputSymp X` plus the two
extra predicates for items 16, 17. -/
structure C3FullInputExtSymp where
  /-- The base `C3FullInputSymp`. -/
  base : C3FullInputSymp X
  /-- Abel-Jacobi smoothness (item 17, symplectic). -/
  smoothness :
    haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle
      base.discreteness
    haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle
      base.discreteness
    haveI : DiscreteTopology
        (PeriodLatticeOfRankTwoG.ofSymplectic (PeriodPairingData.ofSmoothCycle X)
          base.basis base.discreteness).lattice.toIntSubmodule :=
      PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle
        base.discreteness
    haveI : IsZLattice ℝ
        (PeriodLatticeOfRankTwoG.ofSymplectic (PeriodPairingData.ofSmoothCycle X)
          base.basis base.discreteness).lattice.toIntSubmodule :=
      PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle
        base.discreteness
    AbelJacobiSmoothnessSymp base.ajInput
  /-- Abel-Jacobi point-injectivity (item 16, symplectic). -/
  injective : AbelJacobiInjectiveSymp base.ajInput

end JacobianChallenge

/-! ## Legacy → symplectic conversion for `C3FullInputExt`

`C3FullInputExt.smoothness` is a `ContMDiff` statement about
`B.base.ajInput.abelJacobiPoint` into `AnalyticJacobian`. Its symplectic
counterpart is the same statement into `AnalyticJacobianSymp`. Since
the two target types are definitionally equal (both reduce to
`(Fin g → ℂ) ⧸ periodLatticeImage`), the statements transport. The
`ChartedSpace` instances also match because they're derived from the
same `chartedSpaceHypothesis_holds` lemma on
`PeriodLatticeOfRankTwoG X` (where the underlying lattice is the same). -/

namespace JacobianChallenge

namespace C3FullInputExt

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Smoothness transports along `toSymp`.** -/
lemma smoothness_of_toSymp
    (B : C3FullInputExt X) :
    haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle
      (B.base.discreteness.toSymplectic)
    haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle
      (B.base.discreteness.toSymplectic)
    haveI : DiscreteTopology
        (PeriodLatticeOfRankTwoG.ofSymplectic (PeriodPairingData.ofSmoothCycle X)
          B.base.basis B.base.discreteness.toSymplectic).lattice.toIntSubmodule :=
      PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle
        B.base.discreteness.toSymplectic
    haveI : IsZLattice ℝ
        (PeriodLatticeOfRankTwoG.ofSymplectic (PeriodPairingData.ofSmoothCycle X)
          B.base.basis B.base.discreteness.toSymplectic).lattice.toIntSubmodule :=
      PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle
        B.base.discreteness.toSymplectic
    AbelJacobiSmoothnessSymp (B.base.ajInput.toSymp) := by
  -- Provide both the abstract `periodLatticeImage` form (used by the
  -- bundle's discreteness/zlattice instances) AND the explicit
  -- `(ofSymplectic ...).lattice` / `(ofBundle ...).lattice` forms (which
  -- the predicate types literally mention). Both are `rfl`-defeq under
  -- `ofSymplectic_lattice` / `ofBundle_lattice`, but Lean's typeclass
  -- elaboration doesn't search through that defeq automatically.
  haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle
    (B.base.discreteness.toSymplectic)
  haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle
    (B.base.discreteness.toSymplectic)
  haveI dis_sym : DiscreteTopology
      (PeriodLatticeOfRankTwoG.ofSymplectic (PeriodPairingData.ofSmoothCycle X)
        B.base.basis B.base.discreteness.toSymplectic).lattice.toIntSubmodule :=
    PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle
      B.base.discreteness.toSymplectic
  haveI zlat_sym : IsZLattice ℝ
      (PeriodLatticeOfRankTwoG.ofSymplectic (PeriodPairingData.ofSmoothCycle X)
        B.base.basis B.base.discreteness.toSymplectic).lattice.toIntSubmodule :=
    PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle
      B.base.discreteness.toSymplectic
  haveI dis_leg : DiscreteTopology
      (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle X)
        B.base.basis B.base.discreteness).lattice.toIntSubmodule :=
    periodLatticeImage_discreteTopology_of_bundle B.base.discreteness
  haveI zlat_leg : IsZLattice ℝ
      (PeriodLatticeOfRankTwoG.ofBundle (PeriodPairingData.ofSmoothCycle X)
        B.base.basis B.base.discreteness).lattice.toIntSubmodule :=
    periodLatticeImage_isZLattice_of_bundle B.base.discreteness
  -- The legacy smoothness statement is definitionally equal to the
  -- symplectic one — same underlying function, same target type, same
  -- `ChartedSpace` derivation (both go through `chartedSpaceHypothesis_holds`
  -- on the underlying `PeriodLatticeOfRankTwoG X`).
  exact B.smoothness

/-- **Injectivity transports along `toSymp`.** -/
lemma injective_of_toSymp (B : C3FullInputExt X) :
    AbelJacobiInjectiveSymp (B.base.ajInput.toSymp) := by
  intro hpos Q₁ Q₂ hQ
  -- hQ : symp.abelJacobiPoint Q₁ = symp.abelJacobiPoint Q₂ in AnalyticJacobianSymp.
  -- Both sides equal the legacy abelJacobiPoint by `toSymp_abelJacobiPoint_eq` (`rfl`).
  have h_legacy : B.base.ajInput.abelJacobiPoint Q₁
      = B.base.ajInput.abelJacobiPoint Q₂ := by
    have h₁ := B.base.ajInput.toSymp_abelJacobiPoint_eq Q₁
    have h₂ := B.base.ajInput.toSymp_abelJacobiPoint_eq Q₂
    -- h₁ : symp.abelJacobiPoint Q₁ = legacy.abelJacobiPoint Q₁
    -- h₂ : symp.abelJacobiPoint Q₂ = legacy.abelJacobiPoint Q₂
    -- hQ : symp.abelJacobiPoint Q₁ = symp.abelJacobiPoint Q₂
    rw [← h₁, ← h₂]; exact hQ
  exact B.injective hpos h_legacy

/-- **Legacy → symplectic for `C3FullInputExt`.** -/
noncomputable def toSymp (B : C3FullInputExt X) :
    C3FullInputExtSymp X where
  base := B.base.toSymp
  smoothness := B.smoothness_of_toSymp
  injective := B.injective_of_toSymp

end C3FullInputExt

end JacobianChallenge

end
