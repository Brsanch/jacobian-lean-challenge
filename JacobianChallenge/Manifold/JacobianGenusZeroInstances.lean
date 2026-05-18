/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.JacobianSubsingletonInstances
import JacobianChallenge.Jacobian
import Mathlib.Geometry.Manifold.IsManifold.Basic

set_option linter.unusedSectionVars false

/-! # Manifold instances on `Jacobian X` for any genus-0 X with subsingleton Pic0

Generalises `Manifold/JacobianRiemannSphereInstances.lean`'s charted-
space + manifold construction from `X = RiemannSphere` to **any**
compact connected complex 1-manifold `X` satisfying:

* `genus X = 0` — the geometric genus is zero.
* `Subsingleton (Pic0 X)` — the genus-0 case of Abel's converse
  (`Pic⁰ X = 0`).

Under those two named hypotheses we construct (as named-hypothesis
"_holds" theorems, not as global instances, since the hypotheses are
explicit values rather than typeclass instances):

* `subsingleton_fin_genus_to_complex_holds` — `Subsingleton (Fin (genus
  X) → ℂ)` from `genus X = 0`.
* `compactSpace_Jacobian_holds` — `CompactSpace (Jacobian X)` from
  `Subsingleton (Pic0 X)`.
* `chartedSpace_Jacobian_holds` — `ChartedSpace (Fin (genus X) → ℂ)
  (Jacobian X)` from both hypotheses, via a singleton-chart atlas.
* `isManifold_Jacobian_holds` — `IsManifold … ω (Jacobian X)` via
  `singleton_hasGroupoid` + `ClosedUnderRestriction (contDiffGroupoid ω I)`.

For `X = RiemannSphere`, both hypotheses fire unconditionally
(`genus_RiemannSphere_eq_zero` + `subsingleton_pic0_RiemannSphere`),
recovering `JacobianRiemannSphereInstances.lean`'s instances. For any
future genus-0 `X` (e.g., via uniformization), supplying the two
hypotheses inherits the full manifold structure.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]

/-! ## Subsingleton ambient -/

/-- `Fin (genus X) → ℂ` is `Subsingleton` whenever `genus X = 0`. -/
theorem subsingleton_fin_genus_to_complex_holds (hgenus : JacobianChallenge.genus X = 0) :
    Subsingleton (Fin (JacobianChallenge.genus X) → ℂ) := by
  rw [hgenus]
  haveI : Unique (Fin 0 → ℂ) := Pi.uniqueOfIsEmpty (fun _ : Fin 0 => ℂ)
  infer_instance

/-! ## CompactSpace via subsingleton -/

/-- `CompactSpace (Jacobian X)` whenever `Pic⁰ X` is a subsingleton. -/
theorem compactSpace_Jacobian_holds [Subsingleton (Pic0 X)] :
    CompactSpace (JacobianChallenge.Jacobian X) := by
  haveI : Subsingleton (JacobianChallenge.Jacobian X) :=
    inferInstanceAs (Subsingleton (Pic0 X))
  exact Subsingleton.compactSpace

/-! ## Trivial chart between two subsingleton spaces -/

/-- The trivial `OpenPartialHomeomorph` between `Jacobian X` and
`Fin (genus X) → ℂ`, valid whenever both spaces are subsingleton —
i.e., under `genus X = 0` and `Subsingleton (Pic0 X)`. -/
noncomputable def trivialChart_Jacobian
    (hgenus : JacobianChallenge.genus X = 0)
    [Subsingleton (Pic0 X)] :
    OpenPartialHomeomorph (JacobianChallenge.Jacobian X)
      (Fin (JacobianChallenge.genus X) → ℂ) :=
  haveI : Subsingleton (Fin (JacobianChallenge.genus X) → ℂ) :=
    subsingleton_fin_genus_to_complex_holds hgenus
  haveI : Subsingleton (JacobianChallenge.Jacobian X) :=
    inferInstanceAs (Subsingleton (Pic0 X))
  { toFun := fun _ => (0 : Fin (JacobianChallenge.genus X) → ℂ)
    invFun := fun _ => (0 : JacobianChallenge.Jacobian X)
    source := Set.univ
    target := Set.univ
    map_source' := fun _ _ => Set.mem_univ _
    map_target' := fun _ _ => Set.mem_univ _
    left_inv' := fun _ _ => Subsingleton.elim _ _
    right_inv' := fun _ _ => Subsingleton.elim _ _
    open_source := isOpen_univ
    open_target := isOpen_univ
    continuousOn_toFun := continuousOn_const
    continuousOn_invFun := continuousOn_const }

private lemma trivialChart_Jacobian_source
    (hgenus : JacobianChallenge.genus X = 0)
    [Subsingleton (Pic0 X)] :
    (trivialChart_Jacobian hgenus (X := X)).source = Set.univ := rfl

/-- `ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` from
`genus X = 0` + `Subsingleton (Pic0 X)`. -/
@[implicit_reducible]
noncomputable def chartedSpace_Jacobian_holds
    (hgenus : JacobianChallenge.genus X = 0)
    [Subsingleton (Pic0 X)] :
    ChartedSpace (Fin (JacobianChallenge.genus X) → ℂ)
      (JacobianChallenge.Jacobian X) :=
  (trivialChart_Jacobian hgenus).singletonChartedSpace
    (trivialChart_Jacobian_source hgenus)

/-- `IsManifold (𝓘(ℂ, Fin (genus X) → ℂ)) ω (Jacobian X)` from
`genus X = 0` + `Subsingleton (Pic0 X)`. -/
@[implicit_reducible]
noncomputable def isManifold_Jacobian_holds
    (hgenus : JacobianChallenge.genus X = 0)
    [Subsingleton (Pic0 X)] :
    @IsManifold ℂ _
      (Fin (JacobianChallenge.genus X) → ℂ) _ _
      (Fin (JacobianChallenge.genus X) → ℂ) _
      (modelWithCornersSelf ℂ
        (Fin (JacobianChallenge.genus X) → ℂ)) ω
      (JacobianChallenge.Jacobian X) _
      (chartedSpace_Jacobian_holds hgenus) := by
  letI chs := chartedSpace_Jacobian_holds hgenus (X := X)
  -- Build the underlying HasGroupoid from the singleton chart.
  letI hg : @HasGroupoid _ _ (JacobianChallenge.Jacobian X) _ chs
      (contDiffGroupoid ω (modelWithCornersSelf ℂ
        (Fin (JacobianChallenge.genus X) → ℂ))) :=
    (trivialChart_Jacobian hgenus (X := X)).singleton_hasGroupoid
      (trivialChart_Jacobian_source hgenus)
      (contDiffGroupoid ω (modelWithCornersSelf ℂ
        (Fin (JacobianChallenge.genus X) → ℂ)))
  -- `IsManifold I n M` extends `HasGroupoid M (contDiffGroupoid n I)`;
  -- use the parent-class promotion.
  exact { __ := hg }

end JacobianChallenge

end
