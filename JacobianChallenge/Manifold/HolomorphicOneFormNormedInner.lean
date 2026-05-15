/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverSeminormInner
import JacobianChallenge.Manifold.HolomorphicOneFormNormedCovered

set_option diagnostics.threshold 100

/-! # Inner-disk cover-indexed normed structure on `HolomorphicOneForm X`

Sibling to `HolomorphicOneFormNormedCovered.lean` but using the
*inner*-disk seminorm `seminormValInner cover` (from
`DiskChartCoverSeminormInner.lean`) instead of the outer-disk one.

The wrapper type `HolomorphicOneFormCoveredInner X cover` is
definitionally `HolomorphicOneForm X`; the difference from
`HolomorphicOneFormCovered` is the choice of norm. Both are
`NormedAddCommGroup`s and `NormedSpace ℂ`s, but the inner-norm version
is the one in which the per-chart `BoundedContinuousFunction` convergence
from `extract_diagonal_subseq` directly implies norm convergence — the
key technical move for the Bolzano-Weierstrass / Riesz finale.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff
open HolomorphicOneForm

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- The inner-disk-normed cover-indexed view of `HolomorphicOneForm X`.
Definitionally `HolomorphicOneForm X`; the wrapper carries the norm
`seminormValInner cover`. -/
def HolomorphicOneFormCoveredInner (X : Type*) [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (_cover : DiskChartCover X) : Type _ :=
  HolomorphicOneForm X

namespace HolomorphicOneFormCoveredInner

variable (cover : DiskChartCover X)

instance : AddCommGroup (HolomorphicOneFormCoveredInner X cover) :=
  inferInstanceAs (AddCommGroup (HolomorphicOneForm X))

instance : Module ℂ (HolomorphicOneFormCoveredInner X cover) :=
  inferInstanceAs (Module ℂ (HolomorphicOneForm X))

/-- Transport `om : HolomorphicOneForm X` into its inner-normed view. -/
def ofForm (om : HolomorphicOneForm X) : HolomorphicOneFormCoveredInner X cover := om

/-- Transport back. -/
def toForm (om : HolomorphicOneFormCoveredInner X cover) : HolomorphicOneForm X := om

@[simp]
theorem toForm_ofForm (om : HolomorphicOneForm X) :
    toForm cover (ofForm cover om) = om := rfl

@[simp]
theorem ofForm_toForm (om : HolomorphicOneFormCoveredInner X cover) :
    ofForm cover (toForm cover om) = om := rfl

@[simp]
theorem ofForm_zero : ofForm cover (0 : HolomorphicOneForm X) = 0 := rfl

@[simp]
theorem ofForm_add (om₁ om₂ : HolomorphicOneForm X) :
    ofForm cover (om₁ + om₂) = ofForm cover om₁ + ofForm cover om₂ := rfl

@[simp]
theorem ofForm_neg (om : HolomorphicOneForm X) :
    ofForm cover (-om) = -ofForm cover om := rfl

@[simp]
theorem ofForm_smul (c : ℂ) (om : HolomorphicOneForm X) :
    ofForm cover (c • om) = c • ofForm cover om := rfl

variable [Nonempty X]

/-- The inner-disk seminorm packaged as an `AddGroupNorm`. -/
noncomputable def seminormValInnerAddGroupNorm :
    AddGroupNorm (HolomorphicOneFormCoveredInner X cover) where
  toFun om := DiskChartCover.seminormValInner cover (toForm cover om)
  map_zero' := by
    show DiskChartCover.seminormValInner cover (0 : HolomorphicOneForm X) = 0
    exact DiskChartCover.seminormValInner_zero cover
  add_le' om₁ om₂ := by
    show DiskChartCover.seminormValInner cover
        (toForm cover om₁ + toForm cover om₂) ≤
      DiskChartCover.seminormValInner cover (toForm cover om₁) +
        DiskChartCover.seminormValInner cover (toForm cover om₂)
    exact DiskChartCover.seminormValInner_add_le cover _ _
  neg' om := by
    show DiskChartCover.seminormValInner cover (-toForm cover om) =
      DiskChartCover.seminormValInner cover (toForm cover om)
    exact DiskChartCover.seminormValInner_neg cover _
  eq_zero_of_map_eq_zero' om h := by
    have h_zero : toForm cover om = 0 :=
      (DiskChartCover.seminormValInner_eq_zero_iff_zero cover _).mp h
    show om = (0 : HolomorphicOneFormCoveredInner X cover)
    exact h_zero

noncomputable instance instNormedAddCommGroup :
    NormedAddCommGroup (HolomorphicOneFormCoveredInner X cover) :=
  (seminormValInnerAddGroupNorm cover).toNormedAddCommGroup

theorem norm_eq (om : HolomorphicOneFormCoveredInner X cover) :
    ‖om‖ = DiskChartCover.seminormValInner cover (toForm cover om) := rfl

theorem norm_ofForm (om : HolomorphicOneForm X) :
    ‖ofForm cover om‖ = DiskChartCover.seminormValInner cover om := rfl

noncomputable instance instNormedSpace :
    NormedSpace ℂ (HolomorphicOneFormCoveredInner X cover) where
  norm_smul_le c om := by
    rw [norm_eq, norm_eq]
    show DiskChartCover.seminormValInner cover (toForm cover (c • om)) ≤
      ‖c‖ * DiskChartCover.seminormValInner cover (toForm cover om)
    have h_smul : toForm cover (c • om) = c • toForm cover om := rfl
    rw [h_smul, DiskChartCover.seminormValInner_smul cover c (toForm cover om)]

/-- The inner norm is bounded above by the outer norm on the
corresponding `HolomorphicOneFormCovered` view. -/
theorem norm_inner_le_norm_outer (om : HolomorphicOneForm X) :
    ‖ofForm cover om‖ ≤
      ‖HolomorphicOneFormCovered.ofForm cover om‖ := by
  show DiskChartCover.seminormValInner cover om ≤
    DiskChartCover.seminormVal cover om
  exact DiskChartCover.seminormValInner_le_seminormVal cover om

end HolomorphicOneFormCoveredInner

end JacobianChallenge

end
