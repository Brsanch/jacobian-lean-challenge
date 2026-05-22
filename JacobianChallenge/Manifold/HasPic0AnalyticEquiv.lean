/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CanonicalAnalyticJacobianFromClass
import JacobianChallenge.Divisor.PrincipalDivisorRange

set_option linter.unusedSectionVars false

/-! # `HasPic0AnalyticEquiv X` — the Pic⁰ ↔ analytic-Jacobian bridge (Phase A)

A Prop typeclass on a compact connected complex 1-manifold `X` asserting
the **classical Abel–Jacobi isomorphism**:

  `Pic⁰ X ≃+ CanonicalAnalyticJacobian basis_ω`

for some choice of holomorphic-1-form basis `basis_ω` and a witness of
`HasSmoothHomologyDataPackage basis_ω`. Bundles all three pieces into a
single typeclass so downstream consumers (the Basic.lean instances for
items 5/11/12/13/17/18/21) can request the joint blocker as a single
named hypothesis.

## Why a single class

Item 5 of `JacobianChallenge/Basic.lean` —
`instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` — is the
keystone open sorry, gating 6 of the 8 OPEN items. The
`CanonicalAnalyticJacobian basis_ω` already carries
`ChartedSpace`/`IsManifold`/`LieAddGroup`/`CompactSpace` instances
(`Manifold/CanonicalAnalyticJacobianFromClass.lean` lines 153–188)
**unconditionally** under `[HasSmoothHomologyDataPackage X basis_ω]`.
The only remaining bridge is the AddEquiv `Pic⁰ X ≃+
CanonicalAnalyticJacobian basis_ω`, which is the Abel–Jacobi theorem
(Abel direction = vanishing on principal divisors;
converse direction = Jacobi inversion / theta-function surjectivity).

At pin:
* `RiemannSphere` discharges the class trivially (both sides
  subsingleton at genus 0).
* `T_L = ℂ ⧸ L` discharges the class conditionally on the two T_L
  classical hypotheses (`TLDivSumHypothesis` + `TLAbelConverseHypothesis`).
* General X is the multi-phase open frontier (Phases D–F of the plan).

## What this file ships

* `Pic0AnalyticEquivBundle X` — the data structure bundling `basis_ω`,
  the smooth-homology-data-package witness, and the AddEquiv.
* `HasPic0AnalyticEquiv X` — Prop class wrapping
  `Nonempty (Pic0AnalyticEquivBundle X)`.
* `canonicalPic0AnalyticEquivBundle` / `canonicalPic0AnalyticEquiv` —
  extraction lemmas via `Classical.choice`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`Pic0AnalyticEquivBundle X`** — the data of the Pic⁰ ↔
analytic-Jacobian bridge at `X`. -/
structure Pic0AnalyticEquivBundle where
  /-- The chosen holomorphic-1-form basis. -/
  basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)
  /-- The accompanying `HasSmoothHomologyDataPackage` witness needed to
  build `CanonicalAnalyticJacobian basis_ω`. -/
  shdp : HasSmoothHomologyDataPackage (X := X) basis_ω
  /-- The classical Abel–Jacobi isomorphism. -/
  equiv : letI := shdp
          Pic0 X ≃+ CanonicalAnalyticJacobian (X := X) basis_ω

/-- **`HasPic0AnalyticEquiv X`** — Prop class wrapping
`Nonempty (Pic0AnalyticEquivBundle X)`. The single joint blocker for
items 5/11/12/13/17/18/21 of `Basic.lean`. -/
class HasPic0AnalyticEquiv : Prop where
  /-- Nonempty witness of `Pic0AnalyticEquivBundle X`. -/
  out : Nonempty (Pic0AnalyticEquivBundle X)

namespace Pic0AnalyticEquivBundle

variable {X}

/-- Restate the bundle's `shdp` as a local typeclass instance. Used to
discharge `[HasSmoothHomologyDataPackage X B.basis_ω]` obligations
inside theorems that consume a `B : Pic0AnalyticEquivBundle X`. -/
instance instHasSmoothHomologyDataPackage (B : Pic0AnalyticEquivBundle X) :
    HasSmoothHomologyDataPackage (X := X) B.basis_ω :=
  B.shdp

end Pic0AnalyticEquivBundle

/-! ### Canonical extraction via `Classical.choice` -/

/-- **Canonical bundle** under `[HasPic0AnalyticEquiv X]`. Picked once
per type via `Classical.choice`. -/
noncomputable def canonicalPic0AnalyticEquivBundle [HasPic0AnalyticEquiv X] :
    Pic0AnalyticEquivBundle X :=
  Classical.choice HasPic0AnalyticEquiv.out

/-- **Canonical basis** extracted from the canonical bundle. -/
noncomputable def canonicalBasisOmega [HasPic0AnalyticEquiv X] :
    Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X) :=
  (canonicalPic0AnalyticEquivBundle X).basis_ω

/-- The canonical `HasSmoothHomologyDataPackage` witness is available
under `[HasPic0AnalyticEquiv X]`. -/
instance hasSmoothHomologyDataPackage_of_HasPic0AnalyticEquiv
    [HasPic0AnalyticEquiv X] :
    HasSmoothHomologyDataPackage (X := X) (canonicalBasisOmega X) :=
  (canonicalPic0AnalyticEquivBundle X).shdp

/-- **Canonical Abel–Jacobi isomorphism** under `[HasPic0AnalyticEquiv
X]`. The keystone bridge for items 5/11/12/13/17/18/21. -/
noncomputable def canonicalPic0AnalyticEquiv [HasPic0AnalyticEquiv X] :
    Pic0 X ≃+ CanonicalAnalyticJacobian (X := X) (canonicalBasisOmega X) :=
  (canonicalPic0AnalyticEquivBundle X).equiv

end JacobianChallenge

end
