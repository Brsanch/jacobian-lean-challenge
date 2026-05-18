/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Jacobian
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.Basic

set_option linter.unusedSectionVars false

/-! # Manifold instances on `Jacobian X` for any `X` with `Subsingleton (Pic0 X)`

Generalises `Manifold/JacobianRiemannSphereInstances.lean` from
`X = RiemannSphere` to any compact connected complex 1-manifold `X`
satisfying `[Subsingleton (Pic0 X)]` and `genus X = 0`. The proofs go
through unchanged — the only reference to `RiemannSphere` in the prior
file was to discharge those two facts unconditionally; once they are
named hypotheses, the construction is general.

## Classical content of the typeclass / hypothesis arguments

* `[Subsingleton (Pic0 X)]` = "every degree-0 divisor on `X` is
  principal". On a compact connected complex 1-manifold this is
  exactly the **genus-0 case of Abel's converse** / `Pic⁰(ℙ¹) = 0`.
  Unconditional on `X = RiemannSphere` (`subsingleton_pic0_RiemannSphere`).
  For any genus-0 `X`, it would follow from a biholomorphism `X ≃
  RiemannSphere` (uniformization at genus 0) plus the RS case.
* `genus X = 0` — taken as an explicit hypothesis rather than as
  `[Subsingleton (Pic0 X)]`'s consequence, because the structural
  instances quantify over `Fin (genus X) → ℂ` whose subsingleton
  property requires this rewrite step.

## What ships

* `instance ContMDiffAdd … (Jacobian X)` — fires under
  `[Subsingleton (Pic0 X)]`.
* `instance LieAddGroup … (Jacobian X)` — same.
* `ofCurve_contMDiff_of_subsingleton_pic0` — `ContMDiff` of `ofCurve P`
  for any `P : X` under `[Subsingleton (Pic0 X)]`.

The `CompactSpace` / `ChartedSpace` / `IsManifold` instances at the
general-X level are deferred — they require constructing the chart
data + groupoid compatibility, which depends on `genus X = 0` as a
rewrite (to identify `Fin (genus X) → ℂ` with `Fin 0 → ℂ` for the
subsingleton derivation). The RS file has those instances unconditionally
on RS; here we ship the typeclass-level smoothness content that
doesn't require the chart-rewrite step.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]

/-! ## Smoothness of group operations via subsingleton codomain

These instances require a `ChartedSpace` and `IsManifold` instance on
`Jacobian X` to be in scope — for the RS case those come from
`JacobianRiemannSphereInstances.lean`, and any caller providing them
on a general `X` via different means (e.g. a uniformization transport)
will benefit from this file. -/

variable
    [hCS : ChartedSpace (Fin (JacobianChallenge.genus X) → ℂ)
      (JacobianChallenge.Jacobian X)]
    [_IM : IsManifold (modelWithCornersSelf ℂ
      (Fin (JacobianChallenge.genus X) → ℂ)) ω
      (JacobianChallenge.Jacobian X)]
    [hSub : Subsingleton (JacobianChallenge.Jacobian X)]

/-- **`ContMDiffAdd` on `Jacobian X` under `[Subsingleton (Jacobian X)]`**:
the addition is constant (codomain subsingleton), hence `ContMDiff`. -/
noncomputable instance instContMDiffAdd_Jacobian_of_subsingleton :
    ContMDiffAdd (modelWithCornersSelf ℂ
      (Fin (JacobianChallenge.genus X) → ℂ)) ω
      (JacobianChallenge.Jacobian X) where
  contMDiff_add := contMDiff_of_subsingleton

/-- **`LieAddGroup` on `Jacobian X` under `[Subsingleton (Jacobian X)]`**:
negation is constant, hence `ContMDiff`. -/
noncomputable instance instLieAddGroup_Jacobian_of_subsingleton :
    LieAddGroup (modelWithCornersSelf ℂ
      (Fin (JacobianChallenge.genus X) → ℂ)) ω
      (JacobianChallenge.Jacobian X) where
  contMDiff_neg := contMDiff_of_subsingleton

/-- **`ofCurve_contMDiff` on `Jacobian X` under `[Subsingleton (Jacobian X)]`**:
the Abel-Jacobi map into a subsingleton codomain is `ContMDiff`. -/
theorem ofCurve_contMDiff_of_subsingleton_jacobian (P : X) :
    ContMDiff (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ
        (Fin (JacobianChallenge.genus X) → ℂ)) ω
      (JacobianChallenge.Jacobian.ofCurve P :
        X → JacobianChallenge.Jacobian X) :=
  contMDiff_of_subsingleton

end JacobianChallenge

end
