/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusSymplecticBasis
import JacobianChallenge.Manifold.GenericGenusPeriodLatticeInputsFromSmoothHurewicz
import JacobianChallenge.Manifold.SmoothHomotopyHurewiczHypothesis

set_option linter.unusedSectionVars false

open Module Submodule

/-! # Atomic period-lattice inputs for the complex torus `T_L = ℂ ⧸ L`

The generic genus-`g` period-lattice closure factors through four
atomic classical inputs (`GenericGenusPeriodLatticeInputs`). This file
makes those four atoms **concrete and named** for the complex torus
`X := ℂ ⧸ L` with the symplectic basis from `ComplexTorusSymplecticBasis`.

## Naming convention

We surface the Hurewicz hypotheses at the **fixed dimension `g = 1`**
(the geometric / topological genus of the torus). The Hodge-side
identification `genus (ℂ ⧸ L) = 1` (i.e., that the *analytic* genus —
the ℂ-dimension of `HolomorphicOneForm (ℂ ⧸ L)`, defined via the
generic `genus` function from `Basic.lean` — equals the topological
`1`) is a separate classical input (Hodge theory). The
`GenericGenusInputs_at_dim1` constructor below works at the `g = 1`
level and leaves the genus_eq identification to whoever wants to flip
items 4/5/10 in `Basic.lean`.

## What this file ships

* `SmoothHurewiczHypothesisTorus L lam₁ lam₂ hlam₁ hlam₂` — named
  Hurewicz hypothesis on the torus (algebraic-bordism version).

* `SmoothHomotopyHurewiczHypothesisTorus L lam₁ lam₂ hlam₁ hlam₂` —
  the strictly stronger smooth-homotopy version (existential of a
  concrete smooth homotopy to a `basisProductLoop`).

* `smoothHurewiczHypothesisTorus_of_smoothHomotopy` — the
  bordism downgrade.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Named Hurewicz hypotheses on the torus -/

/-- **`SmoothHurewiczHypothesis` on `ℂ ⧸ L` with the symplectic basis
`symplecticBasis L lam₁ lam₂`.** Surfaces the classical genus-1
Hurewicz content (universal-cover lifting `ℂ → ℂ ⧸ L` of every
smooth based loop, with the lift's endpoint in `L`, classifying the
loop's class in `H₁ ≅ L ≅ ℤ²`) as a single named Prop. -/
def SmoothHurewiczHypothesisTorus
    (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L) : Prop :=
  SmoothHurewiczHypothesis (symplecticBasis L lam₁ lam₂ hlam₁ hlam₂)

/-- **Stronger smooth-homotopy version on the torus.** Every smooth
based loop on the torus admits a *concrete smooth homotopy* (not just
algebraic bordism) to a `basisProductLoop` over the symplectic basis. -/
def SmoothHomotopyHurewiczHypothesisTorus
    (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L) : Prop :=
  SmoothHomotopyHurewiczHypothesis (symplecticBasis L lam₁ lam₂ hlam₁ hlam₂)

/-- **Smooth-homotopy ⟹ algebraic-bordism Hurewicz, on the torus.** -/
theorem smoothHurewiczHypothesisTorus_of_smoothHomotopy
    (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L)
    (h : SmoothHomotopyHurewiczHypothesisTorus L lam₁ lam₂ hlam₁ hlam₂) :
    SmoothHurewiczHypothesisTorus L lam₁ lam₂ hlam₁ hlam₂ :=
  smoothHurewiczHypothesis_of_smoothHomotopyHurewicz h

/-- **`BasedLoopHomologyDecompositionHypothesis` on the torus's
symplectic-basis cycles** — the canonical-Stokes-quotient form of the
Hurewicz hypothesis, suitable for direct ingestion by the
`H1_spans_top_canonical_of_basedLoopHomology` reduction. -/
theorem basedLoopHomology_of_smoothHurewiczTorus
    (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L)
    (h : SmoothHurewiczHypothesisTorus L lam₁ lam₂ hlam₁ hlam₂) :
    BasedLoopHomologyDecompositionHypothesis
      (symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens
      (0 : ℂ ⧸ L) :=
  SmoothHurewiczHypothesis.basedLoopHomology_of_smoothHurewicz h

end ComplexTorus

end JacobianChallenge

end
