/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicEquivDegreeFiber

set_option diagnostics.threshold 100

/-! # Sanity-check: `degreeFiber (id : X → X) = 1` for non-subsingleton X

Specialisation of zz323 to `e = HolomorphicEquiv.refl`. The identity
map is a biholomorphism, and zz323 says its degree is 1 on any
non-subsingleton compact connected Riemann surface.

Useful as a sanity-check on the degree machinery and as a base case
for downstream induction on biholomorphic chains.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`degreeFiber id = 1` on any non-subsingleton compact connected
Riemann surface.** -/
theorem degreeFiber_id_eq_one
    [Nonempty X] (hX : ¬ Subsingleton X) :
    ContMDiff.degreeFiber (id : X → X)
        (HolomorphicEquiv.refl : HolomorphicEquiv X X).contMDiff_forward = 1 :=
  HolomorphicEquiv.degreeFiber_eq_one hX HolomorphicEquiv.refl

end JacobianChallenge

end
