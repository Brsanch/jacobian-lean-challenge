/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicEquiv

set_option diagnostics.threshold 100

/-! # Transport of basic topological properties through `HolomorphicEquiv`

A `HolomorphicEquiv` is in particular a homeomorphism (via
`HolomorphicEquiv.toHomeomorph`), so all topological properties that
mathlib lifts through `Homeomorph` lift through a biholomorphism. This
file ships those as named one-liners so downstream code can avoid the
`toHomeomorph` detour at each callsite.

* `CompactSpace`
* `T2Space`

Each is a single-line `Homeomorph`-transport closure. (`ConnectedSpace`
and `LocallyCompactSpace` don't have direct `Homeomorph.*` projections
in mathlib at the pin; future chips may add bridge lemmas.)

No `sorry`, no `axiom`. Pure API.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- **`CompactSpace` transports through a biholomorphism.** -/
theorem HolomorphicEquiv.compactSpace
    (e : HolomorphicEquiv X Y) [CompactSpace X] : CompactSpace Y :=
  e.toHomeomorph.compactSpace

/-- **`T2Space` transports through a biholomorphism.** -/
theorem HolomorphicEquiv.t2Space
    (e : HolomorphicEquiv X Y) [T2Space X] : T2Space Y :=
  e.toHomeomorph.t2Space

end JacobianChallenge

end
