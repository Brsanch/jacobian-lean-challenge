/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiIso
import JacobianChallenge.Manifold.AbelHypothesisGenusZero

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Genus-zero discharge of `JacobiInversion`

`JacobiInversion B hAbel` (`Manifold/AbelJacobiIso.lean`) is the
bijectivity statement for the descended Abel-Jacobi map `B.abelJacobi
hAbel : Pic0 X →+ AnalyticJacobian`. Two parts: injectivity (Abel
converse) and surjectivity (Jacobi inversion).

At `genus X = 0`, the analytic Jacobian collapses to a single point
(see `Manifold/AbelHypothesisGenusZero.lean`), so:

* **Surjectivity is automatic**: `B.abelJacobi hAbel 0 = 0` reaches
  the unique element of `AnalyticJacobian`.
* **Injectivity reduces to** `Subsingleton (Pic0 X)`: when the
  codomain is subsingleton, `f a = f b` is automatic, so injectivity
  ⟺ source is subsingleton. At genus 0 the classical statement
  `Pic⁰(ℙ¹) = 0` realizes this; we take it as a named hypothesis at
  the named-hypothesis level (downstream-discharged via Abel
  converse or Riemann-Roch on `RiemannSphere`).

## What ships

* `JacobiInversion.of_genus_zero_and_subsingleton_pic0` — builds the
  full bijectivity from `genus X = 0` plus
  `Subsingleton (Pic0 X)`. Surjectivity uses
  `Subsingleton.analyticJacobian_of_genus_zero`; injectivity uses the
  source-side subsingleton hypothesis.

The remaining classical content at genus 0 is exactly `Subsingleton
(Pic0 X)` — equivalently, "every degree-0 divisor on a genus-0
compact connected complex 1-manifold is principal", aka the
zero-genus case of Abel's converse / Riemann-Roch on `ℙ¹`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff
open Submodule Module

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

namespace AbelJacobiInput

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α}

/-- **Genus-zero discharge of `JacobiInversion`.** Combines:

* `Subsingleton (AnalyticJacobian _ α h)` — automatic from
  `genus X = 0` (`Manifold/AbelHypothesisGenusZero.lean`,
  `Subsingleton.analyticJacobian_of_genus_zero`).
* `Subsingleton (Pic0 X)` — taken as a named hypothesis. The
  classical statement is `Pic⁰(ℙ¹) = 0` (every degree-0 divisor on
  a genus-0 compact Riemann surface is principal), which downstream
  is the genus-0 case of Abel's converse.

Surjectivity: any element of `AnalyticJacobian` equals `0` by
subsingleton; `B.abelJacobi hAbel 0 = 0` reaches it.

Injectivity: when the source is subsingleton, every two elements
are equal — `f a = f b` is vacuous information, but the conclusion
`a = b` is automatic.
-/
theorem jacobiInversion_of_genus_zero_and_subsingleton_pic0
    (B : AbelJacobiInput α h)
    (hAbel : AbelHypothesis B)
    (hgenus : JacobianChallenge.genus X = 0)
    (hPic0 : Subsingleton (Pic0 X)) :
    JacobiInversion B hAbel := by
  haveI : Subsingleton (AnalyticJacobian (PeriodPairingData.ofSmoothCycle X) α h) :=
    Subsingleton.analyticJacobian_of_genus_zero (data := _) (α := α) (h := h) hgenus
  refine ⟨?_, ?_⟩
  · -- Injective: source is subsingleton.
    intro a b _
    exact hPic0.elim a b
  · -- Surjective: codomain is subsingleton.
    intro v
    refine ⟨0, ?_⟩
    exact Subsingleton.elim _ _

/-- **Genus-zero composite (full chain) — closed `abelJacobiEquiv`.**
With `AbelHypothesis B` discharged trivially via
`abelHypothesis_of_genus_zero`, and `JacobiInversion` discharged via
the above plus `Subsingleton (Pic0 X)`, the full Abel-Jacobi
isomorphism `Pic0 X ≃+ AnalyticJacobian` is available at genus 0.
This composite packages it. -/
noncomputable def abelJacobiEquiv_of_genus_zero
    (B : AbelJacobiInput α h)
    (hgenus : JacobianChallenge.genus X = 0)
    (hPic0 : Subsingleton (Pic0 X)) :
    Pic0 X ≃+ AnalyticJacobian (PeriodPairingData.ofSmoothCycle X) α h :=
  B.abelJacobiEquiv
    (B.abelHypothesis_of_genus_zero hgenus)
    (jacobiInversion_of_genus_zero_and_subsingleton_pic0 B
      (B.abelHypothesis_of_genus_zero hgenus) hgenus hPic0)

end AbelJacobiInput

end JacobianChallenge

end
