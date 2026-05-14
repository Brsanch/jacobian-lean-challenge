/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiPic0

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Genus-zero discharge of `AbelHypothesis`

For a compact connected complex 1-manifold `X` with
`JacobianChallenge.genus X = 0`, the analytic Jacobian

    `AnalyticJacobian (PeriodPairingData.ofSmoothCycle X) α h
      = (Fin (genus X) → ℂ) ⧸ lattice`

reduces to a **subsingleton**, because `Fin 0` is empty and the
function space `Empty → ℂ` is a one-point type. Quotients of
subsingleton groups are subsingleton.

Consequently, the named-hypothesis `AbelHypothesis B` — the assertion
that `B.abelJacobiDiv0Hom` vanishes on every principal divisor — is
**trivially satisfied** at genus zero: every element of the codomain
is `0`.

This file ships:

* `Subsingleton.analyticJacobian_of_genus_zero` —
  `Subsingleton (AnalyticJacobian data α h)` whenever
  `genus X = 0`.
* `AbelJacobiInput.abelHypothesis_of_genus_zero` —
  `AbelHypothesis B` unconditionally, from `genus X = 0`.

This corresponds to a genuine corner of C3 (Abel's theorem) — the
classical statement is non-trivial in general but **vacuous** at
genus 0, where there are no holomorphic 1-forms to integrate against
and `Pic⁰ X` is trivial anyway. The general-genus case is the
deeper classical content of C3 (per `CLOSURE_MAP.md` §F.3,
~1,200–2,800 LOC of Stokes-on-2-chains machinery), unaffected by
this discharge.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff
open Submodule Module

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-! ## Subsingleton of the analytic Jacobian at genus zero -/

/-- **`Fin (genus X) → ℂ` is a subsingleton at genus 0.**
`Fin 0` is empty, so functions from it are unique. -/
lemma subsingleton_pi_fin_genus_zero
    (hgenus : JacobianChallenge.genus X = 0) :
    Subsingleton (Fin (JacobianChallenge.genus X) → ℂ) := by
  rw [hgenus]
  -- `Fin 0 → ℂ` is `Pi (·) (fun _ : Fin 0 => ℂ)`. Since `Fin 0` is empty,
  -- this is `Unique` (hence `Subsingleton`) via `Pi.uniqueOfIsEmpty`.
  haveI : Unique (Fin 0 → ℂ) := Pi.uniqueOfIsEmpty (fun _ : Fin 0 => ℂ)
  infer_instance

/-- **The analytic Jacobian is a subsingleton at genus 0.** Quotient
of the one-point group `Fin 0 → ℂ` by any subgroup is one-point. -/
theorem Subsingleton.analyticJacobian_of_genus_zero
    {data : PeriodPairingData X}
    {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
    {h : PeriodLatticeDiscretenessBundle data α}
    (hgenus : JacobianChallenge.genus X = 0) :
    Subsingleton (AnalyticJacobian data α h) := by
  -- `AnalyticJacobian = JacobianOfLattice X (... .ofBundle data α h)`
  -- `JacobianOfLattice X data' = (Fin (genus X) → ℂ) ⧸ data'.lattice`
  -- Quotient of a subsingleton is a subsingleton.
  unfold AnalyticJacobian JacobianOfLattice
  haveI : Subsingleton (Fin (JacobianChallenge.genus X) → ℂ) :=
    subsingleton_pi_fin_genus_zero hgenus
  -- The quotient `G ⧸ N` of a subsingleton `G` by any normal subgroup `N`
  -- is a subsingleton (all classes are the same).
  refine ⟨fun x y => ?_⟩
  induction x using QuotientAddGroup.induction_on with
  | H xRep =>
    induction y using QuotientAddGroup.induction_on with
    | H yRep =>
      -- Two representatives, but the underlying group is subsingleton,
      -- so `xRep = yRep`; the quotient classes agree.
      have heq : xRep = yRep := Subsingleton.elim xRep yRep
      rw [heq]

/-! ## Genus-zero `AbelHypothesis` discharge -/

namespace AbelJacobiInput

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α}

/-- **Genus-zero discharge of `AbelHypothesis`.** When `genus X = 0`
the analytic Jacobian is subsingleton (single point), so every value
of `B.abelJacobiDiv0Hom` is `0`. This trivially satisfies the named
hypothesis `AbelHypothesis B`.

The general-genus content of `AbelHypothesis` (the classical Abel
forward direction via Stokes on a 2-chain whose boundary represents
the principal divisor) is unaffected; this lemma only closes the
genus-0 corner. -/
theorem abelHypothesis_of_genus_zero
    (B : AbelJacobiInput α h)
    (hgenus : JacobianChallenge.genus X = 0) :
    AbelHypothesis B := by
  intro D _hPrinc
  haveI := Subsingleton.analyticJacobian_of_genus_zero
    (data := PeriodPairingData.ofSmoothCycle X) (α := α) (h := h) hgenus
  exact Subsingleton.elim _ _

end AbelJacobiInput

end JacobianChallenge

end
