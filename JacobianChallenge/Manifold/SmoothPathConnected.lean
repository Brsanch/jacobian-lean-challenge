/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiPoint
import JacobianChallenge.Manifold.SmoothPathConst

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Smooth-path-connectedness and `AbelJacobiInput` discharge

This file introduces `SmoothPathConnected I X`, the classical predicate
"every two points of `X` are joined by a smooth path", and uses it to
discharge the existence of an `AbelJacobiInput α h` bundle once a base
point on `X` is chosen.

## What `AbelJacobiInput` actually bundles

`AbelJacobiInput α h` (`Manifold/AbelJacobiPoint.lean`) carries:

* a chosen base point `P₀ : X`, and
* a per-target picker `Q ↦ pathFromBase Q : SmoothPath 𝓘(ℝ, ℂ) X`,
  with source `= P₀` and target `= Q`.

Two textbook facts are bundled together here. Splitting them apart
helps downstream chips: discharging the existence of an
`AbelJacobiInput` then factors through the strictly weaker classical
predicate

    `SmoothPathConnected 𝓘(ℝ, ℂ) X` (every two points joined by a
                                     smooth path)

plus a nonempty `X`. The path-picker is then recovered by
`Classical.choose` from the existence statement, and the source/target
witnesses by `Classical.choose_spec`.

## What this file delivers

* `SmoothPathConnected I X : Prop` — the classical predicate: every two
  points of `X` are joined by a `SmoothPath I X`.
* `SmoothPathConnected.exists_smoothPath` — projection to existence
  (definitionally equal, exposed by name).
* `SmoothPathConnected.diagonal` — the `p = q` case is uniform: a
  `SmoothPath I X` from `p` to `p` always exists, via
  `SmoothPath.const`.
* `AbelJacobiInput.ofSmoothPathConnected` — constructor producing an
  `AbelJacobiInput α h` from `SmoothPathConnected 𝓘(ℝ, ℂ) X` and a
  chosen base point `P₀ : X`.
* `AbelJacobiInput.ofSmoothPathConnected_basePoint` /
  `ofSmoothPathConnected_pathFromBase_src` /
  `ofSmoothPathConnected_pathFromBase_tgt` — defining identities for
  the discharge.
* `AbelJacobiInput.nonempty_of_smoothPathConnected` — packaging:
  `Nonempty X + SmoothPathConnected 𝓘(ℝ, ℂ) X ⇒ Nonempty
  (AbelJacobiInput α h)`.
* `AbelJacobiInput.exists_smoothPath_from_basePoint` — the converse
  one-sided projection from a bundle to the existence of paths *from
  its base point*. (The full predicate is strictly stronger; an
  `AbelJacobiInput` does not bound paths between arbitrary source
  points.)

## Scope

This file does the named-hypothesis reduction only. Discharging
`SmoothPathConnected 𝓘(ℝ, ℂ) X` itself on a compact connected complex
1-manifold is the "linear-in-chart + chart-cover" arc tracked by
`CLOSURE_MAP.md` §F.5 step 2; it is left for subsequent chips.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Submodule Module

namespace JacobianChallenge

/-- **Smooth-path-connectedness of a manifold.** A smooth manifold `X`
modelled on `H` via `I` is *smooth-path-connected* iff every ordered
pair of points of `X` is joined by a smooth path. This is the smooth
analogue of mathlib's `PathConnectedSpace`. -/
def SmoothPathConnected {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (X : Type*) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X] :
    Prop :=
  ∀ p q : X, ∃ γ : SmoothPath I X, γ.src = p ∧ γ.tgt = q

namespace SmoothPathConnected

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

/-- **Projection to existence.** The statement of
`SmoothPathConnected I X` is the existence of a smooth path between
any two points. Exposed as a named lemma for downstream use. -/
lemma exists_smoothPath (h : SmoothPathConnected I X) (p q : X) :
    ∃ γ : SmoothPath I X, γ.src = p ∧ γ.tgt = q :=
  h p q

/-- **Diagonal case.** A smooth path from `p` to itself always exists,
witnessed by the constant self-loop `SmoothPath.const I X p`. This
fact does not depend on a global `SmoothPathConnected` hypothesis. -/
lemma diagonal (p : X) :
    ∃ γ : SmoothPath I X, γ.src = p ∧ γ.tgt = p :=
  ⟨SmoothPath.const I X p,
    SmoothPath.const_src (I := I) (X := X) p,
    SmoothPath.const_tgt (I := I) (X := X) p⟩

end SmoothPathConnected

namespace AbelJacobiInput

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α}

/-- **Discharge from smooth-path-connectedness.** Given
smooth-path-connectedness of `X` in the real model `𝓘(ℝ, ℂ)` and a
chosen base point `P₀`, build an `AbelJacobiInput α h` whose
path-picker is the `Classical.choose` witness of each existence
statement. Source/target are extracted by `Classical.choose_spec`. -/
noncomputable def ofSmoothPathConnected
    (hSPC : SmoothPathConnected 𝓘(ℝ, ℂ) X) (P₀ : X) :
    AbelJacobiInput α h where
  basePoint := P₀
  pathFromBase := fun Q => Classical.choose (hSPC P₀ Q)
  src_eq := fun Q => (Classical.choose_spec (hSPC P₀ Q)).1
  tgt_eq := fun Q => (Classical.choose_spec (hSPC P₀ Q)).2

/-- **`basePoint` of the discharge is the chosen base.** -/
@[simp] lemma ofSmoothPathConnected_basePoint
    (hSPC : SmoothPathConnected 𝓘(ℝ, ℂ) X) (P₀ : X) :
    (ofSmoothPathConnected (α := α) (h := h) hSPC P₀).basePoint = P₀ :=
  rfl

/-- **The discharge's `pathFromBase Q` has source `P₀`.** -/
lemma ofSmoothPathConnected_pathFromBase_src
    (hSPC : SmoothPathConnected 𝓘(ℝ, ℂ) X) (P₀ Q : X) :
    ((ofSmoothPathConnected (α := α) (h := h) hSPC P₀).pathFromBase Q).src
      = P₀ :=
  (ofSmoothPathConnected (α := α) (h := h) hSPC P₀).src_eq Q

/-- **The discharge's `pathFromBase Q` has target `Q`.** -/
lemma ofSmoothPathConnected_pathFromBase_tgt
    (hSPC : SmoothPathConnected 𝓘(ℝ, ℂ) X) (P₀ Q : X) :
    ((ofSmoothPathConnected (α := α) (h := h) hSPC P₀).pathFromBase Q).tgt
      = Q :=
  (ofSmoothPathConnected (α := α) (h := h) hSPC P₀).tgt_eq Q

/-- **Nonempty packaging.** A nonempty smooth-path-connected `X`
yields a nonempty `AbelJacobiInput α h`. The base point is any element
of `X` (chosen via `Classical.arbitrary`); a different choice gives a
different bundle but the existence statement is the same. -/
theorem nonempty_of_smoothPathConnected
    [Nonempty X] (hSPC : SmoothPathConnected 𝓘(ℝ, ℂ) X) :
    Nonempty (AbelJacobiInput α h) :=
  ⟨ofSmoothPathConnected hSPC (Classical.arbitrary X)⟩

/-- **One-sided projection.** Every `AbelJacobiInput α h` witnesses
the existence of a smooth path *from its base point* to every target.
The full `SmoothPathConnected 𝓘(ℝ, ℂ) X` predicate is strictly stronger:
it bounds paths between arbitrary source points, while an
`AbelJacobiInput` only fixes one. -/
lemma exists_smoothPath_from_basePoint (B : AbelJacobiInput α h) (Q : X) :
    ∃ γ : SmoothPath 𝓘(ℝ, ℂ) X, γ.src = B.basePoint ∧ γ.tgt = Q :=
  ⟨B.pathFromBase Q, B.src_eq Q, B.tgt_eq Q⟩

end AbelJacobiInput

end JacobianChallenge

end
