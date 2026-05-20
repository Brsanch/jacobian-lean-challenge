/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CanonicalOfCurve
import JacobianChallenge.Manifold.CanonicalAnalyticJacobianSubsingleton

set_option linter.unusedSectionVars false

/-! # `canonicalOfCurve_contMDiff` at genus 0

When `[Subsingleton (HolomorphicOneForm X)]` (i.e., `genus X = 0`), the
canonical analytic Jacobian `CanonicalAnalyticJacobianAnonymous X` is
itself subsingleton (proved in `CanonicalAnalyticJacobianSubsingleton`).
Hence ANY function into it is `ContMDiff`, by mathlib's
`contMDiff_of_subsingleton`.

This closes item-17 analog (`canonicalOfCurve` smoothness) for the
genus-0 case, conditional on `[HasJacobianAnalyticStructure X]`.

## What this file ships

* `canonicalOfCurve_contMDiff_of_subsingleton_omega` — `ContMDiff` of
  `canonicalOfCurve P` under both class instances + subsingleton ω.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`canonicalOfCurve P` is `ContMDiff` at genus 0.** Under
`[HasJacobianAnalyticStructure X]` and `[Subsingleton (HolomorphicOneForm
X)]`, the canonical analytic Jacobian is itself subsingleton, so any map
into it is automatically smooth.

Closes the genus-0 case of `canonicalOfCurve`'s smoothness — the
analytic-Jacobian-target analogue of `Jacobian.ofCurve_contMDiff` (item
17 of `Basic.lean`). -/
theorem canonicalOfCurve_contMDiff_of_subsingleton_omega
    [HasJacobianAnalyticStructure X]
    [Subsingleton (HolomorphicOneForm X)]
    (P : X) :
    ContMDiff (𝓘(ℂ, ℂ))
      (modelWithCornersSelf ℂ (Fin (JacobianChallenge.genus X) → ℂ)) ω
      (canonicalOfCurve P :
        X → CanonicalAnalyticJacobianAnonymous X) :=
  contMDiff_of_subsingleton

end JacobianChallenge

end
