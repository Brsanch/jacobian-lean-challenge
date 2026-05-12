/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PullbackLinearEquiv

set_option diagnostics.threshold 100

/-! # Normalization lemmas for `HolomorphicEquiv.pullbackLinearEquiv`

This file ships clean `simp`-suitable normalization lemmas for the
`ℂ`-linear equivalence `HolomorphicEquiv.pullbackLinearEquiv` from
zz308. The two key identities:

* `e.symm.pullbackLinearEquiv = e.pullbackLinearEquiv.symm` — taking
  the symmetric biholomorphism is the same as inverting the linear
  equivalence.

These reflect the functoriality of pullback under `symm`, and let
downstream code interchange `e.symm.pullbackLinearEquiv` with
`e.pullbackLinearEquiv.symm` definitionally via `rw` / `simp`.

No `sorry`, no `axiom`. Both lemmas reduce to extensionality on
`pullbackForm`, which is rfl after the definitional unfolding of
`pullbackLinearEquiv` from zz308.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-- **`pullbackLinearEquiv` commutes with `symm`.** For any
biholomorphism `e : HolomorphicEquiv X Y`, the LinearEquiv induced by
the inverse biholomorphism `e.symm` equals the symmetric of the
LinearEquiv induced by `e`.

Proof: by `LinearEquiv.ext`, both sides equal `e.symm.pullbackForm α`
on every input `α`. The LHS is unfolded via
`pullbackLinearEquiv_apply`; the RHS via `pullbackLinearEquiv_symm_apply`. -/
@[simp]
theorem HolomorphicEquiv.pullbackLinearEquiv_symm_eq
    (e : HolomorphicEquiv X Y) :
    e.symm.pullbackLinearEquiv = e.pullbackLinearEquiv.symm := by
  refine LinearEquiv.ext fun α => ?_
  -- LHS: e.symm.pullbackLinearEquiv α = e.symm.pullbackForm α
  --   (by pullbackLinearEquiv_apply)
  -- RHS: e.pullbackLinearEquiv.symm α = e.symm.pullbackForm α
  --   (by pullbackLinearEquiv_symm_apply, in the definition of
  --    pullbackLinearEquiv from zz308)
  rfl

/-- **`pullbackLinearEquiv` is involutive on `symm`.** Applying `symm`
twice returns the original LinearEquiv. Combines
`pullbackLinearEquiv_symm_eq` with `LinearEquiv.symm_symm`. -/
theorem HolomorphicEquiv.pullbackLinearEquiv_symm_symm
    (e : HolomorphicEquiv X Y) :
    (e.pullbackLinearEquiv.symm).symm = e.pullbackLinearEquiv :=
  LinearEquiv.symm_symm _

end JacobianChallenge

end
