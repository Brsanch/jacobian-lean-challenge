/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannFirstBilinearRelationFromStrictUpperQ

set_option linter.unusedSectionVars false

/-! # Per-pair Riemann period identity

`RiemannFirstBilinearRelation` (chip 9) factors via chip 16 into a
collection of `g(g-1)/2` scalar identities

  `Q J cycleGens (α₀ i) (α₀ j) = 0`, for `i < j`.

This file names each such scalar identity as
`RiemannPeriodIdentity α₀ cycleGens J i j` and shows the biconditional:

  `(∀ i < j, RiemannPeriodIdentity α₀ cycleGens J i j) ∧ Jᵀ = -J`
    ↔ `RiemannFirstBilinearRelation cycleGens J`

The per-pair Prop is the finest-grained open-content factoring of the
first Riemann bilinear relation. Each scalar identity corresponds
classically to a "period integral over a 2-chain whose boundary is
the symplectic combination [α_i, α_j]" — a single Riemann period
relation `∫_{αᵢ} ωⱼ - ∫_{αⱼ} ωᵢ = (period of a wedge in a 2-chain)`.

## What this file ships

* `RiemannPeriodIdentity α₀ cycleGens J i j` — the per-pair scalar
  identity.
* `riemannFirstBilinearRelation_of_perPairIdentities` — RFBR from the
  per-pair identities + `Jᵀ = -J`.
* `perPairIdentities_of_riemannFirstBilinearRelation` — converse:
  RFBR + `J antisym` implies every per-pair identity (in fact,
  for any pair, not just `i < j`).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Per-pair Riemann period identity.** The single scalar identity
`Q J cycleGens (α₀ i) (α₀ j) = 0` for a fixed pair `(i, j)`. -/
def RiemannPeriodIdentity
    (α₀ : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    {data : PeriodPairingData X}
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ)
    (i j : Fin (JacobianChallenge.genus X)) : Prop :=
  riemannBilinearPeriodForm cycleGens J (α₀ i) (α₀ j) = 0

/-- **`RiemannFirstBilinearRelation` from per-pair identities + `J` antisym.**

The strict-upper-triangular per-pair identities, combined with the
antisymmetry of `J` (which gives the strict-lower triangle via chip 6
and the diagonal via chip 7), yield RFBR. Direct corollary of chip 16. -/
theorem riemannFirstBilinearRelation_of_perPairIdentities
    (α₀ : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    {data : PeriodPairingData X}
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    (hJ : Jᵀ = -J)
    (h_pair :
      ∀ i j : Fin (JacobianChallenge.genus X), i < j →
        RiemannPeriodIdentity α₀ cycleGens J i j) :
    RiemannFirstBilinearRelation cycleGens J :=
  riemannFirstBilinearRelation_of_strictUpperTriangular_Q_zero
    α₀ cycleGens hJ h_pair

/-- **Converse: every per-pair identity follows from RFBR.**

If RFBR holds, then for every pair `(i, j)`, the per-pair identity
holds (in fact unconditionally on `i ⋚ j`). -/
theorem perPairIdentities_of_riemannFirstBilinearRelation
    (α₀ : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    {data : PeriodPairingData X}
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ)
    (h_rfbr : RiemannFirstBilinearRelation cycleGens J)
    (i j : Fin (JacobianChallenge.genus X)) :
    RiemannPeriodIdentity α₀ cycleGens J i j :=
  h_rfbr (α₀ i) (α₀ j)

end JacobianChallenge

end
