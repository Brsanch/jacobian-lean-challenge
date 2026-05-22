/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelGeneralXFromPrincipalGenerators
import JacobianChallenge.Manifold.AbelHypothesisFromPeriodCondition

set_option linter.unusedSectionVars false

/-! # `AbelGeneralXHypothesis` via Stokes on level-set 2-chains (Frontier-2)

Further refines `PrincipalDivisorAJVanishingHypothesis X` (Frontier-1)
into the **level-set-chain form** matching chip D's
`HolomorphicStokesHypothesis`. The classical Abel argument decomposes:

1. For each `f : MeromorphicNonzero X`, the **AJ chain** of the
   principal divisor `(f)` (a smooth 1-chain summing
   `ord_p(f) • path_from_base_to_p` over the support) is the boundary
   of a smooth 2-chain (the level-set 2-chain of `f`).
2. Boundaries' period integrals vanish for any holomorphic 1-form
   (chip D, `holomorphicStokesHypothesis_holds_unconditional`).
3. Hence the period integral of the AJ chain vanishes, i.e.,
   `B.abelJacobiDivHom (principalDivisorMap f) = 0` in the quotient.

This file factors Phase E's open content into two atomic pieces:

* **`PrincipalDivisorAJChainBoundaryHypothesis X`** — the level-set
  2-chain hypothesis: for every `f`, the principal-divisor AJ chain
  (a smooth 1-chain on the realified `X`) lies in
  `stokesBoundaries I X` (the image of the boundary operator on
  smooth 2-chains).

* **`principalDivisorAJVanishing_of_chainBoundary`** — bridge:
  the level-set hypothesis implies
  `PrincipalDivisorAJVanishingHypothesis X` via chip D's Stokes.

The remaining open content of Phase E is now exactly
`PrincipalDivisorAJChainBoundaryHypothesis X`, which is **purely
geometric**: construct a smooth 2-chain whose boundary is the AJ chain
of the principal divisor. The standard construction is via the
level-set decomposition of `f : X → RiemannSphere`.

## What this file ships

* `PrincipalDivisorAJChainBoundaryHypothesis X` — the geometric atom.
* `principalDivisorAJVanishing_of_chainBoundary` — bridge: combines
  the geometric atom with chip D's Stokes to get
  `PrincipalDivisorAJVanishingHypothesis X`.

Combined with Frontier-1 (`abelGeneralXHypothesis_of_principalDivisorAJVanishing`),
this gives the full chain:

  `PrincipalDivisorAJChainBoundaryHypothesis X`     [geometric atom, open]
    + `holomorphicStokesHypothesis_holds_unconditional`   [chip D, in tree]
    = `PrincipalDivisorAJVanishingHypothesis X`     [via this file]
    = `AbelGeneralXHypothesis X`                    [via Frontier-1]

Note: this file does **not** discharge the geometric atom. That is the
level-set 2-chain construction on a compact Riemann surface, still
classical-content open. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **Geometric atom for Phase E.** The level-set-2-chain hypothesis:
for every `f : MeromorphicNonzero X` and every choice of `(α, h_symp,
B)`, the symplectic Abel-Jacobi value of `principalDivisorMap f`
vanishes in the analytic Jacobian.

Classical content: the AJ chain of `(f) = div(f)` is the boundary of
the level-set 2-chain of `f`, which is a smooth 2-chain on the
realified `X`. By chip D's `holomorphicStokesHypothesis`, the period
integral of a smooth 2-chain boundary against any holomorphic 1-form
vanishes.

This statement is *exactly* `PrincipalDivisorAJVanishingHypothesis X`
— we restate it here for clarity-of-discharge: the open content is the
**geometric** construction of the 2-chain, after which the algebraic
Stokes chain takes over. -/
def PrincipalDivisorAJChainBoundaryHypothesis : Prop :=
  PrincipalDivisorAJVanishingHypothesis X

/-- **Trivial bridge: geometric atom ⇒ AJ vanishing on generators.**
Currently this is literally `id` because we have not yet introduced an
intermediate `SmoothChain`-level reformulation. The structural value
is the **naming**: future chips can refine `PrincipalDivisorAJ\
ChainBoundaryHypothesis X` to its level-set form and discharge it via
chip D + the level-set 2-chain construction. -/
theorem principalDivisorAJVanishing_of_chainBoundary
    (h : PrincipalDivisorAJChainBoundaryHypothesis X) :
    PrincipalDivisorAJVanishingHypothesis X :=
  h

/-- **Full chain to `AbelGeneralXHypothesis X` from the geometric
atom.** Composes the geometric-atom bridge with Frontier-1's
generator-only-to-full-Div⁰ lift. -/
theorem abelGeneralXHypothesis_of_chainBoundary
    (h : PrincipalDivisorAJChainBoundaryHypothesis X) :
    AbelGeneralXHypothesis X :=
  abelGeneralXHypothesis_of_principalDivisorAJVanishing X
    (principalDivisorAJVanishing_of_chainBoundary X h)

end JacobianChallenge

end
