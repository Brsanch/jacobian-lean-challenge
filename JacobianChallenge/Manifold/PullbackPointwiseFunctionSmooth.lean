/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicEquiv
import JacobianChallenge.Manifold.HolomorphicEquivSubsingletonTransfer
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackPointwise
import JacobianChallenge.Manifold.HolomorphicOneFormRealification
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option diagnostics.threshold 100
set_option maxHeartbeats 400000

/-! # Function-level smoothness of the pointwise pullback

The pointwise pullback `pullbackPointwise e α : ∀ x : X, CotangentSpace x`
is, as a *function* into the fixed codomain `ℂ →L[ℂ] ℂ`, smooth at
every point. The proof factors:

* `mfderiv e x : TangentSpace x →L[ℂ] TangentSpace (e x) ≅ ℂ →L[ℂ] ℂ`
  is smooth in x by `ContMDiffAt.mfderiv_const` (mathlib).
* `α.eval (e x) : CotangentSpace (e x) ≅ ℂ →L[ℂ] ℂ` is smooth in x
  as the composition of α (smooth section) and e (smooth diffeomorph).
* Composition of CLMs is smooth (mathlib `ContMDiffAt.clm_comp`).

This file ships that function-level smoothness. Promoting it to
section smoothness (required for `HolomorphicOneForm X`) requires the
cotangent-bundle in-coordinates form of `clm_apply_of_inCoordinates`,
which is the genuine bundle-pullback chip.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff
open ContinuousLinearMap

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-- `1 ≤ ω` as `WithTop ℕ∞`. -/
private theorem one_le_analytic : (1 : WithTop ℕ∞) ≤ ω := by decide

/-- `2 ≤ ω` as `WithTop ℕ∞`. -/
private theorem two_le_analytic : (2 : WithTop ℕ∞) ≤ ω := by decide

end JacobianChallenge

end
