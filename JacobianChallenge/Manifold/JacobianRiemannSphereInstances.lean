/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3FullInputExtSympGenusZero
import JacobianChallenge.Manifold.Pic0RiemannSphereSubsingleton
import JacobianChallenge.Manifold.PeriodLatticeRiemannSphere
import JacobianChallenge.Jacobian

set_option linter.unusedSectionVars false

/-! # Subsingleton + compactness instances on `Jacobian RiemannSphere`

`JacobianChallenge.Jacobian X = Pic0 X` with discrete topology
(placeholder). For `X = RiemannSphere`, `Pic0 RiemannSphere` is a
subsingleton in tree (`subsingleton_pic0_RiemannSphere`), so the
subsingleton-derived instances fire.

This file ships **trivially-derived** instances on
`JacobianChallenge.Jacobian RiemannSphere`:

* `Subsingleton (Jacobian RiemannSphere)` (typeclass-registered).
* `CompactSpace (Jacobian RiemannSphere)` — via mathlib's
  `Subsingleton.compactSpace`.

The headline bridge `picZeroEquivSymp_RiemannSphere : Pic⁰ RS ≃+
JacobianAnalyticChoiceSymp RS` is in tree separately (built by the
`JacobianAnalyticChoiceSymp.lean` chip).

## Scope note

Basic.lean's instances are stated for **general** `X` with manifold
typeclasses; they cannot be specialised to `X = RiemannSphere` without
changing Buzzard's verbatim signatures. The instances here fire on the
specific `Jacobian RiemannSphere` instantiation. To flip Basic.lean
items 11, 5, 12, 13, 17 from `sorry` to STRICT-CLOSED at general `X`,
the placeholder discrete topology on `Pic0 X` would have to be
replaced by the analytic-quotient topology globally — a structural
change requiring a redefinition of `JacobianChallenge.Jacobian X`.

The `ChartedSpace` / `IsManifold` / `LieAddGroup` instances are NOT
provided here because they require constructing a `PartialHomeomorph`
between two subsingleton-but-non-defeq types (`Pic0 RiemannSphere` and
`Fin 0 → ℂ`), plus matching mathlib's specific `IsManifold` /
`LieAddGroup` API surfaces. Those would be follow-on chips.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

/-- **`Subsingleton` of `Pic⁰ RiemannSphere`** (typeclass-registered
re-export of `subsingleton_pic0_RiemannSphere`). -/
instance : Subsingleton (Pic0 RiemannSphere) :=
  subsingleton_pic0_RiemannSphere

/-- **`Subsingleton` of `Jacobian RiemannSphere`**. Definitionally
`Pic0 RiemannSphere`. -/
instance : Subsingleton (JacobianChallenge.Jacobian RiemannSphere) :=
  inferInstanceAs (Subsingleton (Pic0 RiemannSphere))

/-- **Item 11 on `Jacobian RiemannSphere`** — compactness via
mathlib's `Subsingleton.compactSpace`. -/
instance : CompactSpace (JacobianChallenge.Jacobian RiemannSphere) :=
  Subsingleton.compactSpace

end JacobianChallenge

end
