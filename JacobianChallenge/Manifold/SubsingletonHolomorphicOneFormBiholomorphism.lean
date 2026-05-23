/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PullbackLinearEquiv

set_option linter.unusedSectionVars false

/-! # `Subsingleton (HolomorphicOneForm X) ↔ Subsingleton (HolomorphicOneForm Y)`

Both directions transport along a biholomorphism `X ≃ω Y` via
`HolomorphicEquiv.pullbackLinearEquiv` (the ℂ-linear isomorphism of
holomorphic 1-form spaces). Direct corollary of `Equiv.subsingleton_congr`.

Generalises the existing `subsingleton_holomorphicOneForm_of_holomorphicEquiv_RS`
to any biholomorphic pair.

## What ships

* `subsingleton_holomorphicOneForm_iff_of_holomorphicEquiv` — biconditional.
* `subsingleton_holomorphicOneForm_of_holomorphicEquiv` — forward direction.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u v

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-- **Subsingleton (HolomorphicOneForm) is a biholomorphism invariant.** -/
theorem subsingleton_holomorphicOneForm_iff_of_holomorphicEquiv
    (e : HolomorphicEquiv X Y) :
    Subsingleton (HolomorphicOneForm X) ↔ Subsingleton (HolomorphicOneForm Y) :=
  Equiv.subsingleton_congr e.pullbackLinearEquiv.symm.toEquiv

/-- **Forward direction**: Subsingleton transports from Y to X via a
biholomorphism `X ≃ω Y`. -/
theorem subsingleton_holomorphicOneForm_of_holomorphicEquiv
    (e : HolomorphicEquiv X Y) [Subsingleton (HolomorphicOneForm Y)] :
    Subsingleton (HolomorphicOneForm X) :=
  (subsingleton_holomorphicOneForm_iff_of_holomorphicEquiv e).mpr inferInstance

end JacobianChallenge

end
