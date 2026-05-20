/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexAffineSegmentPath
import JacobianChallenge.Manifold.SmoothPathIntegrateReverse
import JacobianChallenge.Manifold.AbelJacobiPath

set_option linter.unusedSectionVars false

/-! # Reverse-orientation integrate identity for `affineSegmentPath`

Combining the SmoothPath-level reverse identity
`(affineSegmentPath σ p q).reverse = affineSegmentPath σ q p`
with the mathlib `SmoothPath.integrate_reverse`, the affine segment
path picks up a sign under endpoint swap:

```
(affineSegmentPath σ q p).integrate ω = -(affineSegmentPath σ p q).integrate ω
```

At the complex period level:

```
complexChainPeriod (single (affineSegmentPath σ q p)) α
  = - complexChainPeriod (single (affineSegmentPath σ p q)) α
```

These are the **interior-edge cancellation primitives** in the
midpoint-subdivision orientation telescoping.

## What this file ships

* `Smooth2Simplex.affineSegmentPath_integrate_reverse` — real-form
  reverse-integrate identity.
* `Smooth2Simplex.affineSegmentPath_complexChainPeriod_reverse` —
  complex-period reverse identity.
* `Smooth2Simplex.affineSegmentPath_pair_complexChainPeriod_zero` —
  the chain `single (affineSegmentPath σ p q) + single (affineSegmentPath σ q p)`
  has zero complex period against any holomorphic 1-form.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex

namespace JacobianChallenge

namespace Smooth2Simplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

/-- **Affine segment paths integrate additively-inverse under endpoint
swap.** Via the SmoothPath-level reverse identity composed with
`SmoothPath.integrate_reverse`. -/
theorem affineSegmentPath_integrate_reverse
    (σ : Smooth2Simplex I X) (p q : Fin 2 → ℝ) (om : SmoothOneForm I X) :
    (affineSegmentPath σ q p).integrate om
      = -(affineSegmentPath σ p q).integrate om := by
  rw [← affineSegmentPath_reverse σ p q]
  exact SmoothPath.integrate_reverse _ om

end Smooth2Simplex

/-! ## Complex-period version on a Riemann-surface-like manifold -/

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **Complex period of `single (affineSegmentPath σ q p)` is the
negative of `single (affineSegmentPath σ p q)`** against any
holomorphic 1-form. -/
theorem Smooth2Simplex.affineSegmentPath_complexChainPeriod_reverse
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X) (p q : Fin 2 → ℝ)
    (α : HolomorphicOneForm X) :
    complexChainPeriod (SmoothChain.single (Smooth2Simplex.affineSegmentPath σ q p)) α
      = - complexChainPeriod
            (SmoothChain.single (Smooth2Simplex.affineSegmentPath σ p q)) α := by
  unfold complexChainPeriod
  rw [SmoothChain.integrate_single, SmoothChain.integrate_single,
      SmoothChain.integrate_single, SmoothChain.integrate_single]
  rw [Smooth2Simplex.affineSegmentPath_integrate_reverse σ p q (realComponent α),
      Smooth2Simplex.affineSegmentPath_integrate_reverse σ p q (imagComponent α)]
  push_cast
  ring

/-- **Sum-of-pair vanishes: `single (affineSegmentPath σ p q) + single
(affineSegmentPath σ q p)` has zero complex period.** Direct corollary
of the reverse identity. -/
theorem Smooth2Simplex.affineSegmentPath_pair_complexChainPeriod_zero
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X) (p q : Fin 2 → ℝ)
    (α : HolomorphicOneForm X) :
    complexChainPeriod
        (SmoothChain.single (Smooth2Simplex.affineSegmentPath σ p q)
          + SmoothChain.single (Smooth2Simplex.affineSegmentPath σ q p)) α = 0 := by
  rw [complexChainPeriod_add_left,
      Smooth2Simplex.affineSegmentPath_complexChainPeriod_reverse]
  ring

end JacobianChallenge

end
