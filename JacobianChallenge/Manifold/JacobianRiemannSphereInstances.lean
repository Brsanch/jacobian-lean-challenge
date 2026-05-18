/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3FullInputExtSympGenusZero
import JacobianChallenge.Manifold.Pic0RiemannSphereSubsingleton
import JacobianChallenge.Manifold.PeriodLatticeRiemannSphere
import JacobianChallenge.Jacobian
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.Basic

set_option linter.unusedSectionVars false

/-! # Manifold instances on `JacobianChallenge.Jacobian RiemannSphere`

`JacobianChallenge.Jacobian X = Pic0 X` with discrete topology
(placeholder). For `X = RiemannSphere`, `Pic0 RiemannSphere` is a
subsingleton in tree (`subsingleton_pic0_RiemannSphere`), so all the
structural manifold instances Basic.lean asks about (`CompactSpace`,
`ChartedSpace`, `IsManifold`, `LieAddGroup`, `ofCurve_contMDiff`)
reduce to subsingleton trivialities.

This file builds the full manifold-instance chain on `Jacobian
RiemannSphere` from the ground up using mathlib's
`OpenPartialHomeomorph.singletonChartedSpace` +
`singleton_hasGroupoid` machinery (single-chart atlas with universal
source, automatically compatible with any
`ClosedUnderRestriction` groupoid — including `contDiffGroupoid ω I`).

## What ships

* `Subsingleton (Pic0 RiemannSphere)` typeclass re-export.
* `Subsingleton (Jacobian RiemannSphere)` typeclass.
* `CompactSpace (Jacobian RiemannSphere)` — via `Subsingleton.compactSpace`.
* `OpenPartialHomeomorph (Jacobian RS) (Fin (genus RS) → ℂ)` —
  the trivial chart between two subsingleton spaces.
* `ChartedSpace (Fin (genus RS) → ℂ) (Jacobian RS)` — via
  `singletonChartedSpace` (single-chart atlas).
* `IsManifold (𝓘(ℂ, Fin (genus RS) → ℂ)) ω (Jacobian RS)` — via
  `singleton_hasGroupoid` + `ClosedUnderRestriction (contDiffGroupoid ω I)`.
* `LieAddGroup (𝓘(ℂ, Fin (genus RS) → ℂ)) ω (Jacobian RS)` — via
  `contMDiff_of_subsingleton` for both `add` and `neg`.
* `ofCurve_contMDiff_RiemannSphere` — via `contMDiff_of_subsingleton`.

## Scope note

Basic.lean's instances are stated for **general** `X` with manifold
typeclasses; they cannot be specialised to `X = RiemannSphere`
without changing Buzzard's verbatim signatures. The instances here
fire on the specific `Jacobian RiemannSphere` instantiation,
demonstrating that the RS closure path is fully derivable in tree.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

/-! ## Subsingleton + compactness -/

instance : Subsingleton (Pic0 RiemannSphere) :=
  subsingleton_pic0_RiemannSphere

instance instSubsingleton_Jacobian_RiemannSphere :
    Subsingleton (JacobianChallenge.Jacobian RiemannSphere) :=
  inferInstanceAs (Subsingleton (Pic0 RiemannSphere))

/-- **Item 11 on `Jacobian RiemannSphere`** — `Subsingleton ⇒ CompactSpace`. -/
instance : CompactSpace (JacobianChallenge.Jacobian RiemannSphere) :=
  Subsingleton.compactSpace

instance instSubsingleton_Fin_genus_RS :
    Subsingleton (Fin (JacobianChallenge.genus RiemannSphere) → ℂ) := by
  rw [JacobianChallenge.RiemannSphere.genus_RiemannSphere_eq_zero]
  haveI : Unique (Fin 0 → ℂ) := Pi.uniqueOfIsEmpty (fun _ : Fin 0 => ℂ)
  infer_instance

/-! ## Trivial chart between two subsingleton spaces -/

/-- The trivial `OpenPartialHomeomorph` between `Jacobian RiemannSphere`
and `Fin (genus RS) → ℂ`. Both spaces are subsingleton at genus 0, so
the chart is uniquely determined: any pair of maps between them must
be constant, and any two constant maps between subsingletons compose
to the identity. -/
noncomputable def trivialChart_RiemannSphere :
    OpenPartialHomeomorph (JacobianChallenge.Jacobian RiemannSphere)
      (Fin (JacobianChallenge.genus RiemannSphere) → ℂ) where
  toFun := fun _ => (0 : Fin (JacobianChallenge.genus RiemannSphere) → ℂ)
  invFun := fun _ => (0 : JacobianChallenge.Jacobian RiemannSphere)
  source := Set.univ
  target := Set.univ
  map_source' := fun _ _ => Set.mem_univ _
  map_target' := fun _ _ => Set.mem_univ _
  left_inv' := fun _ _ => Subsingleton.elim _ _
  right_inv' := fun _ _ => Subsingleton.elim _ _
  open_source := isOpen_univ
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_const
  continuousOn_invFun := continuousOn_const

private lemma trivialChart_RiemannSphere_source :
    trivialChart_RiemannSphere.source = Set.univ := rfl

/-! ## ChartedSpace via the trivial chart -/

/-- **Items 5 + 12 on `Jacobian RiemannSphere`**: `ChartedSpace`
structure via `singletonChartedSpace`. -/
noncomputable instance instChartedSpace_Jacobian_RiemannSphere :
    ChartedSpace (Fin (JacobianChallenge.genus RiemannSphere) → ℂ)
      (JacobianChallenge.Jacobian RiemannSphere) :=
  trivialChart_RiemannSphere.singletonChartedSpace
    trivialChart_RiemannSphere_source

/-! ## IsManifold via singleton + closed-under-restriction groupoid -/

/-- **Item 12 on `Jacobian RiemannSphere`**: `IsManifold` (analytic),
via `IsManifold.mk'` from the singleton-charted-space's
`HasGroupoid (contDiffGroupoid ω I)`. -/
noncomputable instance instIsManifold_Jacobian_RiemannSphere :
    IsManifold (modelWithCornersSelf ℂ
      (Fin (JacobianChallenge.genus RiemannSphere) → ℂ)) ω
      (JacobianChallenge.Jacobian RiemannSphere) := by
  haveI := trivialChart_RiemannSphere.singleton_hasGroupoid
    trivialChart_RiemannSphere_source
      (contDiffGroupoid ω (modelWithCornersSelf ℂ
        (Fin (JacobianChallenge.genus RiemannSphere) → ℂ)))
  exact IsManifold.mk' _ ω _

/-! ## LieAddGroup via subsingleton-derived smoothness -/

/-- **Item 13 on `Jacobian RiemannSphere`**: `ContMDiffAdd` — `add` is
smooth because the codomain is subsingleton. -/
noncomputable instance instContMDiffAdd_Jacobian_RiemannSphere :
    ContMDiffAdd (modelWithCornersSelf ℂ
      (Fin (JacobianChallenge.genus RiemannSphere) → ℂ)) ω
      (JacobianChallenge.Jacobian RiemannSphere) where
  contMDiff_add := contMDiff_of_subsingleton

/-- **Item 13 on `Jacobian RiemannSphere`**: `LieAddGroup` — `neg` is
smooth because the codomain is subsingleton. -/
noncomputable instance instLieAddGroup_Jacobian_RiemannSphere :
    LieAddGroup (modelWithCornersSelf ℂ
      (Fin (JacobianChallenge.genus RiemannSphere) → ℂ)) ω
      (JacobianChallenge.Jacobian RiemannSphere) where
  contMDiff_neg := contMDiff_of_subsingleton

/-! ## `ofCurve_contMDiff` on `RiemannSphere` -/

/-- **Item 17 on `Jacobian RiemannSphere`**: `ContMDiff` of
`ofCurve P` — codomain is subsingleton. -/
theorem ofCurve_contMDiff_RiemannSphere (P : RiemannSphere) :
    ContMDiff (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ
        (Fin (JacobianChallenge.genus RiemannSphere) → ℂ)) ω
      (JacobianChallenge.Jacobian.ofCurve P :
        RiemannSphere → JacobianChallenge.Jacobian RiemannSphere) :=
  contMDiff_of_subsingleton

end JacobianChallenge

end
