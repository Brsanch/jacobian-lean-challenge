/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSecondRelationPositivityNamed
import JacobianChallenge.Manifold.HodgeRiemannBridgeComposition
import JacobianChallenge.Analysis.HodgeInnerProductDischarge

set_option linter.unusedSectionVars false

/-! # `RiemannSecondRelationPositivity` from the Hodge–Riemann bridge

The named atom `RiemannSecondRelationPositivity data basis_ω cycleGens`
(positivity of `i · pmᵀ · standardSymplectic g · pm.map star` on
non-zero `x : Fin g → ℂ`) is exactly the positivity half of
`RiemannBilinearSecondRelation` specialised to `J = standardSymplectic g`.

The in-tree `RiemannBilinearSecondRelation_of_HodgeBridge` discharges
the full second relation (Hermitian half + positivity half) from
`H.IsPositiveDefinite` + `HodgeRiemannBridgeHypothesis`. Project the
positivity half onto `RiemannSecondRelationPositivity`.

Combined with `hodgeInnerProductHypothesis_holds` (this file's session
unconditional discharge), the only remaining open input to RSRP at
*any* genus is the **bridge identity** for the canonical Petersson
Hermitian form `globalPettersonHermitianForm X` and
`J := standardSymplectic g`. That identity is the deep classical
content (wedge product + Stokes + cup product), and the open atom #3
in OPEN.md's outstanding list.

## What this file ships

* `riemannSecondRelationPositivity_of_bridge_and_PD` — RSRP from
  `HodgeRiemannBridgeHypothesis` at `J = standardSymplectic g` plus
  `H.IsPositiveDefinite`. Takes any Hermitian form witness.

* `riemannSecondRelationPositivity_of_bridge_pettersonForm` — the
  specialisation to the canonical Petersson Hermitian form
  `globalPettersonHermitianForm X` (whose positive-definiteness is
  unconditional this session). Only the bridge identity remains an
  input.

## Significance

Reduces the open content for items 5/11/12/13 (modulo SCD + RBFR) to a
**single open identity**: the bridge identity for the Petersson form
and `standardSymplectic g`. Specifically at genus 1 this is a single
scalar identity; at general genus it is a `g × g` matrix identity
that classically follows from Stokes on a fundamental polygon.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`RiemannSecondRelationPositivity` from the bridge + Hodge positivity.**

Given any positive-definite Hermitian form `H` on `HolomorphicOneForm X`
and a bridge identity `i · pmᵀ · standardSymplectic g · pm.map star
= H.toMatrix basis_ω`, the named atom
`RiemannSecondRelationPositivity` is satisfied. -/
theorem riemannSecondRelationPositivity_of_bridge_and_PD
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    {H : HermitianOnHolomorphicOneForm X}
    (hPD : H.IsPositiveDefinite)
    (hBridge :
      HodgeRiemannBridgeHypothesis data basis_ω cycleGens
        (standardSymplectic (JacobianChallenge.genus X)) H) :
    RiemannSecondRelationPositivity data basis_ω cycleGens := by
  intro x hx
  -- The full RBSR follows from the bridge composition; project its
  -- positivity half (and note the matrix expansion equals
  -- `i • periodMatrixForm pm (standardSymplectic g)`).
  have hRBSR :
      RiemannBilinearSecondRelation data basis_ω cycleGens
        (standardSymplectic (JacobianChallenge.genus X)) :=
    RiemannBilinearSecondRelation_of_HodgeBridge hPD hBridge
  -- RBSR.2 gives the per-x positivity for the matrix expansion.
  have h_pos := hRBSR.2 x hx
  -- Identify the matrix in RBSR with `i • periodMatrixForm pm J`.
  -- They are definitionally equal: RBSR's `M` literal vs `periodMatrixForm`.
  exact h_pos

/-- **`RiemannSecondRelationPositivity` from the bridge for the
canonical Petersson Hermitian form.**

The positive-definiteness of `globalPettersonHermitianForm X` is
unconditional this session (`globalPettersonHermitianForm_isPositiveDefinite`).
Combined with the bridge identity for the Petersson form and
`standardSymplectic g`, the named atom RSRP follows.

This isolates the **single remaining open input** for RSRP at any
genus to a matrix identity bridging the period matrix with the global
Petersson Hermitian form. -/
theorem riemannSecondRelationPositivity_of_bridge_pettersonForm
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (hBridge :
      HodgeRiemannBridgeHypothesis data basis_ω cycleGens
        (standardSymplectic (JacobianChallenge.genus X))
        (globalPettersonHermitianForm X)) :
    RiemannSecondRelationPositivity data basis_ω cycleGens :=
  riemannSecondRelationPositivity_of_bridge_and_PD data basis_ω cycleGens
    (globalPettersonHermitianForm_isPositiveDefinite X) hBridge

end JacobianChallenge

end
