/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianAnalyticStructureFromHolomorphicEquivRS
import JacobianChallenge.Manifold.CanonicalAnalyticJacobianRiemannSphereSmokeTest

set_option linter.unusedSectionVars false

/-! # Smoke test for `HasJacobianAnalyticStructure` via biholomorphism to RS

Validates that `HasJacobianAnalyticStructure.of_holomorphicEquiv_RiemannSphere`
fires on the canonical example `X = RiemannSphere` (with the identity
biholomorphism) and produces the expected `CanonicalAnalyticJacobianAnonymous`
structure instances.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

/-- **RS smoke: HJAS via `HolomorphicEquiv.refl`.** -/
example : HasJacobianAnalyticStructure RiemannSphere :=
  HasJacobianAnalyticStructure.of_holomorphicEquiv_RiemannSphere
    (HolomorphicEquiv.refl : HolomorphicEquiv RiemannSphere RiemannSphere)

/-- **RS smoke: HJCC via `HolomorphicEquiv.refl`.** -/
example : HasJacobianClassicalContent RiemannSphere :=
  HasJacobianClassicalContent.of_holomorphicEquiv_RiemannSphere
    (HolomorphicEquiv.refl : HolomorphicEquiv RiemannSphere RiemannSphere)

end JacobianChallenge

end
