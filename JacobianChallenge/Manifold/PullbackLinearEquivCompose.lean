/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PullbackLinearEquivNormalization
import JacobianChallenge.Manifold.PullbackLinearEquivTrans

set_option diagnostics.threshold 100

/-! # Composition sanity-check corollaries for `pullbackLinearEquiv`

This file ships two immediate corollaries of zz311's
`pullbackLinearEquiv_symm_eq`, zz312's `pullbackLinearEquiv_refl`, and
zz313's `pullbackLinearEquiv_trans`:

* `pullbackLinearEquiv_self_trans_symm` — for any biholomorphism
  `e : HolomorphicEquiv X Y`,
  `(e.trans e.symm).pullbackLinearEquiv = LinearEquiv.refl ℂ _`.
  (Because `e.trans e.symm = HolomorphicEquiv.refl` as a `Diffeomorph`.)

* `pullbackLinearEquiv_symm_trans_self` — likewise for
  `(e.symm.trans e).pullbackLinearEquiv`.

These exercise the full refl/symm/trans trio and give downstream code
a one-line rewrite for the round-trip pullback identity.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-- **`pullbackLinearEquiv` on `e.trans e.symm` is the identity.**
Reduces via zz313's `pullbackForm_trans` and zz308's
`pullbackForm_pullbackForm_symm`. -/
theorem HolomorphicEquiv.pullbackLinearEquiv_self_trans_symm
    (e : HolomorphicEquiv X Y) :
    (e.trans e.symm).pullbackLinearEquiv
      = LinearEquiv.refl ℂ (HolomorphicOneForm X) := by
  refine LinearEquiv.ext fun α => ?_
  show (e.trans e.symm).pullbackForm α = α
  rw [HolomorphicEquiv.pullbackForm_trans]
  exact HolomorphicEquiv.pullbackForm_pullbackForm_symm e α

/-- **`pullbackLinearEquiv` on `e.symm.trans e` is the identity.**
Reduces via zz313's `pullbackForm_trans` and zz308's
`pullbackForm_symm_pullbackForm`. -/
theorem HolomorphicEquiv.pullbackLinearEquiv_symm_trans_self
    (e : HolomorphicEquiv X Y) :
    (e.symm.trans e).pullbackLinearEquiv
      = LinearEquiv.refl ℂ (HolomorphicOneForm Y) := by
  refine LinearEquiv.ext fun α => ?_
  show (e.symm.trans e).pullbackForm α = α
  rw [HolomorphicEquiv.pullbackForm_trans]
  exact HolomorphicEquiv.pullbackForm_symm_pullbackForm e α

end JacobianChallenge

end
