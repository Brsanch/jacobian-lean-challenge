/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiPoint

/-! # Named-hypothesis predicate for injectivity of `abelJacobiPoint` (item 16)

OPEN.md item 16 (`ofCurve_inj`) is the anti-hack lemma against the
trivialization `Jacobian := PUnit`: when `genus X > 0`, the Abel-Jacobi
map `ofCurve P : X → Jacobian X` is injective.

On the analytic Jacobian this is **Abel's theorem** for compact Riemann
surfaces: the pointwise Abel-Jacobi map
`abelJacobiPoint B : X → AnalyticJacobian X α h`
is injective when `genus X > 0`. The corresponding `Q ↦ relAbelJacobi B P Q`
is then also injective.

Classical content: if `abelJacobiPoint B Q₁ = abelJacobiPoint B Q₂` then
the divisor `δQ₁ - δQ₂` is principal, i.e., equals `(g) = div f` for
some meromorphic `f : X → ℙ¹`. For `g ≥ 1` this forces `Q₁ = Q₂`
because a non-constant meromorphic function on `X` of degree 1 would
exhibit `X ≃ ℙ¹` (hence genus 0).

Reduction in mathlib at the pin: Abel's theorem is genuine C4-content
(`CLOSURE_MAP.md` §F.5 step 3), not at the mathlib pin. We surface it
as a **named-hypothesis predicate** here and leave the discharge as
C4 work.

## Net contribution

* `AbelJacobiInjective B` — predicate carrying `Function.Injective` of
  `abelJacobiPoint B` (under `0 < genus X`).
-/

open scoped ContDiff Manifold
open Submodule Module

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ⊤ X]

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α}

/-- **Named-hypothesis predicate** for OPEN.md item 16 at the analytic-
Jacobian level: `abelJacobiPoint B : X → AnalyticJacobian _ α h` is
injective. The hypothesis is conditioned on `0 < genus X` (otherwise the
statement is vacuous — at genus 0 the AnalyticJacobian is trivial). -/
def AbelJacobiInjective (B : AbelJacobiInput α h) : Prop :=
  0 < JacobianChallenge.genus X →
    Function.Injective
      (B.abelJacobiPoint :
        X → AnalyticJacobian (PeriodPairingData.ofSmoothCycle X) α h)

/-- Corollary at the relative-Abel-Jacobi level: under `AbelJacobiInjective`,
the relative map `Q ↦ relAbelJacobi B P Q` is also injective.

(Both maps differ by a constant, and a translation-by-a-constant
preserves injectivity.) -/
theorem AbelJacobiInjective.relAbelJacobi_injective
    (B : AbelJacobiInput α h) (hinj : AbelJacobiInjective B)
    (hpos : 0 < JacobianChallenge.genus X) (P : X) :
    Function.Injective
      (fun Q : X => B.relAbelJacobi P Q :
        X → AnalyticJacobian (PeriodPairingData.ofSmoothCycle X) α h) := by
  intro Q₁ Q₂ hQ
  -- `relAbelJacobi P Q := abelJacobiPoint Q - abelJacobiPoint P`.
  -- `hQ : abelJacobiPoint Q₁ - abelJacobiPoint P = abelJacobiPoint Q₂ - abelJacobiPoint P`.
  -- Cancel `abelJacobiPoint P` to get `abelJacobiPoint Q₁ = abelJacobiPoint Q₂`.
  have h_eq : B.abelJacobiPoint Q₁ = B.abelJacobiPoint Q₂ := by
    have hQ' : B.abelJacobiPoint Q₁ - B.abelJacobiPoint P =
        B.abelJacobiPoint Q₂ - B.abelJacobiPoint P := hQ
    -- Add `abelJacobiPoint P` to both sides.
    have := congrArg (· + B.abelJacobiPoint P) hQ'
    simp only [sub_add_cancel] at this
    exact this
  exact hinj hpos h_eq

end JacobianChallenge

end
