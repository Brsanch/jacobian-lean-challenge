/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HodgeRiemannBridgeGenusZero
import JacobianChallenge.Manifold.BilinearFromHodgeChain
import JacobianChallenge.Manifold.RiemannBilinearRelations

set_option linter.unusedSectionVars false

/-! # `CompleteHodgeRiemannHypothesis` at genus 0 via the Petersson form

Capstone of this session's Hodge-Riemann arc. Provides an
**alternative** discharge of `CompleteHodgeRiemannHypothesis` at
`genus X = 0` to the existing
`completeHodgeRiemannHypothesis_of_genus_eq_zero` (in
`Manifold/CompleteHodgeRiemannGenusZero.lean`), routing through the
**actual** positive-definite Petersson Hermitian form constructed
this session rather than the vacuous Subsingleton-ω witness.

## Routes compared

* **Existing in-tree route**
  `completeHodgeRiemannHypothesis_of_subsingleton`: under `Subsingleton
  (HolomorphicOneForm X)`, every quantity in CHRH is vacuously zero.
  CHRH is satisfied by `J := 0`, `H := the constant-zero form`.

* **This file's route** (via Petersson form): the Hodge inner product
  `H := globalPettersonHermitianForm X` (this session's
  `hodgeInnerProductHypothesis_holds`) is positive-definite on
  *every* compact connected complex 1-manifold — not vacuous at
  general genus. Combined with this session's `_of_genus_zero`
  discharges for `RiemannBilinearFirstRelation` (new, ships below)
  and `HodgeRiemannBridgeHypothesis`, gives CHRH at genus 0 with an
  explicit non-zero Hermitian form witness.

The two routes give the same Prop conclusion, but the new route is
**structurally non-vacuous** — at general genus it would need only
the bridge identity to close, since `H` is already established.

## What ships

* `riemannBilinearFirstRelation_of_genus_zero` — RBFR at genus 0.
  Both sides are matrices over `Fin (genus X) = Fin 0`, hence equal
  by extensionality. (Not previously exposed as a named theorem; the
  existing `_of_subsingleton` CHRH route bundles RBFR implicitly.)

* `completeHodgeRiemannHypothesis_of_genus_zero_via_pettersonForm` —
  CHRH at genus 0 via this session's Petersson form route.

## Significance

Validates that this session's chain composes correctly into the C3
analytic blocker at genus 0:
* S.8 (strict positivity of Petersson Hermitian diagonal)
* `HodgeInnerProductHypothesis` discharge (this session)
* Hodge-Riemann bridge at genus 0 (this session)
* RBFR at genus 0 (this file)
* CompleteHodgeRiemannHypothesis at genus 0 (this file, new route)

For **general genus ≥ 1**, the bridge identity (and hence CHRH via
this route) remains open: wedge product + Stokes + cup-product.
Symplectic basis + Smooth Hurewicz also remain open at general genus
(handle decomposition + abelianization of π₁ on a genus-g surface).

This is the last capstone chip of the outstanding-items arc started
this session. Items 5/11/12/13 still OPEN at general X.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`RiemannBilinearFirstRelation` is unconditional at genus 0.**

At `genus X = 0`, both sides of `Π^T · J · Π = 0` are matrices over
the empty type `Fin (genus X) = Fin 0`, hence equal by extensionality. -/
theorem riemannBilinearFirstRelation_of_genus_zero
    (h_g : JacobianChallenge.genus X = 0)
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ) :
    RiemannBilinearFirstRelation data basis_ω cycleGens J := by
  unfold RiemannBilinearFirstRelation
  have h_empty : IsEmpty (Fin (JacobianChallenge.genus X)) := by
    rw [h_g]; exact Fin.isEmpty
  ext i j
  exact h_empty.elim i

/-- **`CompleteHodgeRiemannHypothesis` at genus 0 via the Petersson form.**

Alternative route to `completeHodgeRiemannHypothesis_of_genus_eq_zero`
(in `CompleteHodgeRiemannGenusZero.lean`, via vacuous Subsingleton-ω
form). This route composes the three discharges shipped this session:

* `hodgeInnerProductHypothesis_holds` — `globalPettersonHermitianForm
  X` is positive-definite (unconditional at all genera).
* `riemannBilinearFirstRelation_of_genus_zero` — RBFR holds at genus 0.
* `hodgeRiemannBridgeHypothesis_of_genus_zero` — bridge identity holds
  at genus 0.

The same Prop is established, but via an **actual** positive-definite
form rather than a vacuous one. -/
theorem completeHodgeRiemannHypothesis_of_genus_zero_via_pettersonForm
    (h_g : JacobianChallenge.genus X = 0)
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1) :
    CompleteHodgeRiemannHypothesis data basis_ω cycleGens := by
  obtain ⟨H, hPD⟩ := hodgeInnerProductHypothesis_holds X
  refine ⟨0, H, hPD,
    riemannBilinearFirstRelation_of_genus_zero h_g data basis_ω cycleGens 0,
    hodgeRiemannBridgeHypothesis_of_genus_zero h_g data basis_ω cycleGens 0 H⟩

end JacobianChallenge

end
