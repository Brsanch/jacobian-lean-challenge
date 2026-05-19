/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusPathConnected
import JacobianChallenge.Manifold.ComplexTorusPeriodLatticeInputs
import JacobianChallenge.Manifold.GenericGenusH1SpansTopFromLoopHomology

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Module Submodule

/-! # `H1_spans_top_canonical` on the complex torus from
`SmoothHurewiczHypothesisTorus`

For the symplectic basis on `ℂ ⧸ L`, the canonical-Stokes-quotient
generation field `H1_spans_top_canonical` reduces (via the per-loop
decomposition + smooth-path-connectedness chain in
`GenericGenusH1SpansTopFromLoopHomology.lean`) to:

  (a) `BasedLoopHomologyDecompositionHypothesis (symplecticBasis…).cycleGens 0`
      — discharged by `SmoothHurewiczHypothesisTorus L lam₁ lam₂ hlam₁ hlam₂`
      via `basedLoopHomology_of_smoothHurewiczTorus`.

  (b) Smooth-path-connectedness data `(α, h_α_src, h_α_tgt)` at base
      point `0 ∈ ℂ ⧸ L` — discharged **unconditionally** by
      `ComplexTorus.α` from `ComplexTorusPathConnected.lean`.

So this file gives the unconditional reduction from the single named
Hurewicz hypothesis on the torus to the canonical-quotient generation
on its symplectic-basis cycles.

## What this file ships

* `ComplexTorus.h1_spans_top_canonical_of_smoothHurewicz` —
  `SmoothHurewiczHypothesisTorus L lam₁ lam₂ hlam₁ hlam₂` ⟹
  `H1_spans_top_canonical` on `(symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens`
  in the canonical Stokes quotient.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **`H1_spans_top_canonical` on the torus from
`SmoothHurewiczHypothesisTorus`** (unconditional in the
smooth-path-connectedness data via `ComplexTorus.α`).

The canonical-quotient `S.H1 := SmoothCycle / stokesBoundaries` on
`ℂ ⧸ L` is ℤ-spanned by the projections of the two torus basis-loop
cycles. -/
theorem h1_spans_top_canonical_of_smoothHurewicz
    (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L)
    (h_hurewicz : SmoothHurewiczHypothesisTorus L lam₁ lam₂ hlam₁ hlam₂) :
    (Submodule.span ℤ
      (Set.range (fun i : Fin (2 * 1) =>
        ((StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) (ℂ ⧸ L)).proj
          ((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens i) :
            (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) (ℂ ⧸ L)).H1)))) = ⊤ :=
  H1_spans_top_canonical_of_basedLoopHomology
    (symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens
    (0 : ℂ ⧸ L) (α L) (α_src L) (α_tgt L)
    (basedLoopHomology_of_smoothHurewiczTorus L lam₁ lam₂ hlam₁ hlam₂ h_hurewicz)

end ComplexTorus

end JacobianChallenge

end
