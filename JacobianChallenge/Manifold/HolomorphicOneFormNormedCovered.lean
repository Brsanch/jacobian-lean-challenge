/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverSeminormSeparating
import Mathlib.Analysis.Normed.Group.Seminorm

set_option diagnostics.threshold 100

/-! # Cover-indexed normed structure on `HolomorphicOneForm X`

This file packages the disk-cover seminorm `seminormVal cover` as an
honest `NormedAddCommGroup` instance on a cover-indexed type alias
`HolomorphicOneFormCovered X cover := HolomorphicOneForm X`. The norm
is `seminormVal cover`, the separating property is
`seminormVal_eq_zero_iff_zero`, and the ℂ-module structure is inherited
from `HolomorphicOneForm X` (and shown compatible with the norm via
`seminormVal_smul`).

Downstream chips assemble:

* The `NormedSpace ℂ (HolomorphicOneFormCovered X cover)` instance for
  Riesz `FiniteDimensional.of_isCompact_closedBall₀`.

Different choices of `cover` give *different* norms, but for a fixed
compact `X` they are equivalent (norms on a finite-dim space are
equivalent). The eventual `HolomorphicOneFormFiniteDim X` headline is
phrased on `HolomorphicOneForm X` itself; the cover-indexed wrapper is
the technical vehicle.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff
open HolomorphicOneForm

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- The type of holomorphic 1-forms on `X` together with the choice of a
disk chart cover used to measure them. Definitionally equal to
`HolomorphicOneForm X`; the wrapper exists only to carry a
cover-dependent norm. -/
def HolomorphicOneFormCovered (X : Type*) [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (_cover : DiskChartCover X) : Type _ :=
  HolomorphicOneForm X

namespace HolomorphicOneFormCovered

variable (cover : DiskChartCover X)

/-! ## Inherited algebraic structure -/

instance : AddCommGroup (HolomorphicOneFormCovered X cover) :=
  inferInstanceAs (AddCommGroup (HolomorphicOneForm X))

instance : Module ℂ (HolomorphicOneFormCovered X cover) :=
  inferInstanceAs (Module ℂ (HolomorphicOneForm X))

/-- Transport `om : HolomorphicOneForm X` into its `Covered` view. -/
def ofForm (om : HolomorphicOneForm X) : HolomorphicOneFormCovered X cover := om

/-- Transport back. -/
def toForm (om : HolomorphicOneFormCovered X cover) : HolomorphicOneForm X := om

@[simp]
theorem toForm_ofForm (om : HolomorphicOneForm X) :
    toForm cover (ofForm cover om) = om := rfl

@[simp]
theorem ofForm_toForm (om : HolomorphicOneFormCovered X cover) :
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

/-! ## `AddGroupNorm` packaging of `seminormVal` -/

variable [Nonempty X]

/-- The disk-cover seminorm packaged as an `AddGroupNorm`. The four
seminorm axioms come from `DiskChartCoverSeminormAggregate.lean`; the
separating axiom from `DiskChartCoverSeminormSeparating.lean`. -/
noncomputable def seminormValAddGroupNorm :
    AddGroupNorm (HolomorphicOneFormCovered X cover) where
  toFun om := DiskChartCover.seminormVal cover (toForm cover om)
  map_zero' := by
    show DiskChartCover.seminormVal cover (0 : HolomorphicOneForm X) = 0
    exact DiskChartCover.seminormVal_zero cover
  add_le' om₁ om₂ := by
    show DiskChartCover.seminormVal cover
        (toForm cover om₁ + toForm cover om₂) ≤
      DiskChartCover.seminormVal cover (toForm cover om₁) +
        DiskChartCover.seminormVal cover (toForm cover om₂)
    exact DiskChartCover.seminormVal_add_le cover _ _
  neg' om := by
    show DiskChartCover.seminormVal cover (-toForm cover om) =
      DiskChartCover.seminormVal cover (toForm cover om)
    exact DiskChartCover.seminormVal_neg cover _
  eq_zero_of_map_eq_zero' om h := by
    -- `h : DiskChartCover.seminormVal cover (toForm cover om) = 0`.
    have h_zero : toForm cover om = 0 :=
      (DiskChartCover.seminormVal_eq_zero_iff_zero cover _).mp h
    -- `toForm cover om = (om : HolomorphicOneForm X)`, so this gives
    -- `om = 0` after transport.
    show om = (0 : HolomorphicOneFormCovered X cover)
    exact h_zero

/-! ## `NormedAddCommGroup` instance -/

noncomputable instance instNormedAddCommGroup :
    NormedAddCommGroup (HolomorphicOneFormCovered X cover) :=
  (seminormValAddGroupNorm cover).toNormedAddCommGroup

/-- The norm on `HolomorphicOneFormCovered X cover` is `seminormVal cover`
on the underlying form. -/
theorem norm_eq (om : HolomorphicOneFormCovered X cover) :
    ‖om‖ = DiskChartCover.seminormVal cover (toForm cover om) := rfl

theorem norm_ofForm (om : HolomorphicOneForm X) :
    ‖ofForm cover om‖ = DiskChartCover.seminormVal cover om := rfl

/-! ## `NormedSpace ℂ` instance -/

noncomputable instance instNormedSpace :
    NormedSpace ℂ (HolomorphicOneFormCovered X cover) where
  norm_smul_le c om := by
    rw [norm_eq, norm_eq]
    show DiskChartCover.seminormVal cover (toForm cover (c • om)) ≤
      ‖c‖ * DiskChartCover.seminormVal cover (toForm cover om)
    -- `toForm` is the identity on the underlying type, so `c • om`
    -- in `Covered` is `c • (toForm om)` in `HolomorphicOneForm X`.
    have h_smul : toForm cover (c • om) = c • toForm cover om := rfl
    rw [h_smul, DiskChartCover.seminormVal_smul cover c (toForm cover om)]

end HolomorphicOneFormCovered

end JacobianChallenge

end
