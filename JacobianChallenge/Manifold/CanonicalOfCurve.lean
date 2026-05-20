/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianAnalyticStructure
import JacobianChallenge.Manifold.AbelJacobiPointSymp
import JacobianChallenge.Manifold.SmoothPathLocalConvex

set_option linter.unusedSectionVars false

/-! # Canonical Abel-Jacobi map on `CanonicalAnalyticJacobianAnonymous X`

For any `X` with `[HasJacobianAnalyticStructure X]`, this file builds
the canonical Abel-Jacobi point map

  `canonicalOfCurve : (P : X) → X → CanonicalAnalyticJacobianAnonymous X`

via integration against the canonical period-lattice symplectic bundle,
with paths supplied by `smoothPathConnected_of_preconnected` (which is
unconditional on any preconnected complex 1-manifold).

The headline identities:

* `canonicalOfCurve_self` — `canonicalOfCurve P P = 0`.

This is the analytic-Jacobian-target analogue of `Jacobian.ofCurve` /
`ofCurve_self` in `Basic.lean`, prepared for the eventual C3 rewire of
`JacobianChallenge.Jacobian X` to the analytic Jacobian.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ### Canonical Abel-Jacobi input (basis-anonymous, class-keyed) -/

/-- **Canonical Abel-Jacobi input from `[HasJacobianAnalyticStructure
X]` + a chosen base point.** Paths supplied by
`smoothPathConnected_of_preconnected`. -/
noncomputable def canonicalAbelJacobiInput
    [HasJacobianAnalyticStructure X] (p₀ : X) :
    AbelJacobiInputSymp (canonicalBasisFromAnalyticStructure X)
      (canonicalPeriodLatticeSymplecticBundle
        (canonicalBasisFromAnalyticStructure X)) := by
  -- ConnectedSpace ⇒ PreconnectedSpace.
  haveI : PreconnectedSpace X := ConnectedSpace.toPreconnectedSpace
  let sp : SmoothPathConnected (𝓘(ℝ, ℂ)) X :=
    smoothPathConnected_of_preconnected
  refine
    { basePoint := p₀
      pathFromBase := fun Q => Classical.choose (sp p₀ Q)
      src_eq := fun Q => (Classical.choose_spec (sp p₀ Q)).1
      tgt_eq := fun Q => (Classical.choose_spec (sp p₀ Q)).2 }

/-! ### Canonical Abel-Jacobi point map -/

/-- **Canonical Abel-Jacobi point map.** `canonicalOfCurve P Q` is the
relative Abel-Jacobi class `[∫_P^Q ω] mod periodLatticeImage` in
`CanonicalAnalyticJacobianAnonymous X`.

Mirrors `JacobianChallenge.Jacobian.ofCurve` in `Jacobian.lean`, but
targets the analytic Jacobian. -/
noncomputable def canonicalOfCurve
    [HasJacobianAnalyticStructure X] (P : X) :
    X → CanonicalAnalyticJacobianAnonymous X :=
  fun Q => (canonicalAbelJacobiInput P).relAbelJacobi P Q

/-- **Canonical Abel-Jacobi at the basepoint vanishes.**
`canonicalOfCurve P P = 0`. Mirrors `JacobianChallenge.Jacobian.ofCurve_self`. -/
@[simp] theorem canonicalOfCurve_self
    [HasJacobianAnalyticStructure X] (P : X) :
    canonicalOfCurve P P = 0 := by
  change (canonicalAbelJacobiInput P).relAbelJacobi P P = 0
  exact AbelJacobiInputSymp.relAbelJacobi_self _ P

end JacobianChallenge

end
