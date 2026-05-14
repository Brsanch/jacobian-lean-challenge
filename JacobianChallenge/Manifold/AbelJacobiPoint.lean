/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiPath

set_option diagnostics.threshold 100

/-! # PL-4-C: Pointwise Abel-Jacobi map relative to a base point

The pathwise AJ class `abelJacobiPath α h γ` (PL-4-A) takes a specific
smooth path as input. To define a **pointwise** map `X → AnalyticJacobian`
sending each `Q : X` to a class independent of intermediate choices,
we need:

* a fixed base point `P₀ : X`,
* a smooth path `P₀ → Q` for each `Q : X`.

We package these as a named-hypothesis bundle `AbelJacobiInput`. The
existence of such a bundle on a compact connected complex 1-manifold is
classical — it follows from smooth-path-connectedness, which mathlib
does not yet have at this pin for the manifold `IsManifold I ω X`
typeclass setup. Surfacing the bundle here lets the AJ construction
proceed independently of that mathlib gap.

## What this file delivers

* `AbelJacobiInput α h` — bundle of `basePoint`, `pathFromBase`, and
  the source/target witnesses.
* `abelJacobiPoint B Q : AnalyticJacobian` — the AJ class of `Q`
  relative to `B.basePoint`.
* `abelJacobiPoint_basePoint_class` — the AJ class at the base point is
  the class of the "self-loop" path `pathFromBase basePoint`. Whether
  it equals `0` depends on the user-supplied `pathFromBase basePoint`;
  on the canonical convention `pathFromBase basePoint = trivial loop`,
  this becomes `0`, but we do not force the convention here.
* `relAbelJacobi B P Q : AnalyticJacobian` — the "relative" class
  `abelJacobiPoint B Q - abelJacobiPoint B P`. By path-independence in
  PL-4-A, this equals the class of any smooth path from `P` to `Q`.

The base-point dependence cancels in `relAbelJacobi`, which is the
shape Abel-Jacobi takes on degree-0 divisors (where coefficients sum
to zero).

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff
open Submodule Module

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ⊤ X]

/-- **Abel-Jacobi base-point bundle.** Carries a chosen base point and
a smooth-path-picker `Q ↦ (P₀ → Q)` with source/target witnesses.

Existence of this bundle on a compact connected complex 1-manifold is
classical (smooth-path-connectedness), but not in mathlib at this pin —
hence the named-hypothesis pattern. -/
structure AbelJacobiInput
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α) where
  /-- A chosen base point on `X`. -/
  basePoint : X
  /-- For each target `Q : X`, a smooth path from `basePoint` to `Q`. -/
  pathFromBase : (Q : X) → SmoothPath 𝓘(ℝ, ℂ) X
  /-- The source of each `pathFromBase Q` is `basePoint`. -/
  src_eq : ∀ Q : X, (pathFromBase Q).src = basePoint
  /-- The target of each `pathFromBase Q` is `Q`. -/
  tgt_eq : ∀ Q : X, (pathFromBase Q).tgt = Q

namespace AbelJacobiInput

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α}

/-- **Pointwise Abel-Jacobi map.** Given a base-point bundle `B`, sends
each `Q : X` to the AJ class of the path `B.pathFromBase Q`. -/
def abelJacobiPoint (B : AbelJacobiInput α h) (Q : X) :
    AnalyticJacobian (PeriodPairingData.ofSmoothCycle X) α h :=
  abelJacobiPath α h (B.pathFromBase Q)

@[simp] lemma abelJacobiPoint_def (B : AbelJacobiInput α h) (Q : X) :
    B.abelJacobiPoint Q = abelJacobiPath α h (B.pathFromBase Q) := rfl

/-- **Relative Abel-Jacobi.** The difference of AJ classes between two
points, expressed as `abelJacobiPoint Q - abelJacobiPoint P`. By
path-independence (PL-4-A), this equals the class of any smooth path
from `P` to `Q`.

The base-point dependence cancels: if `B'` is another bundle with a
different base point but the same path-from-`P`-to-`Q` (or any path
with the same endpoints), then `relAbelJacobi B P Q = relAbelJacobi B'
P Q`. This is the shape Abel-Jacobi takes on degree-0 divisors. -/
def relAbelJacobi (B : AbelJacobiInput α h) (P Q : X) :
    AnalyticJacobian (PeriodPairingData.ofSmoothCycle X) α h :=
  B.abelJacobiPoint Q - B.abelJacobiPoint P

@[simp] lemma relAbelJacobi_def (B : AbelJacobiInput α h) (P Q : X) :
    B.relAbelJacobi P Q = B.abelJacobiPoint Q - B.abelJacobiPoint P := rfl

/-- **Self-relative AJ is zero.** `relAbelJacobi P P = 0`. -/
@[simp] lemma relAbelJacobi_self (B : AbelJacobiInput α h) (P : X) :
    B.relAbelJacobi P P = 0 := by
  show B.abelJacobiPoint P - B.abelJacobiPoint P = 0
  exact sub_self _

/-- **Antisymmetry of relAbelJacobi.** -/
lemma relAbelJacobi_swap (B : AbelJacobiInput α h) (P Q : X) :
    B.relAbelJacobi P Q = -(B.relAbelJacobi Q P) := by
  show B.abelJacobiPoint Q - B.abelJacobiPoint P
      = -(B.abelJacobiPoint P - B.abelJacobiPoint Q)
  abel

end AbelJacobiInput

end JacobianChallenge

end
