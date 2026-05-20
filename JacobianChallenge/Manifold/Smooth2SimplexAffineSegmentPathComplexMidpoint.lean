/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexAffineSegmentPathMidpoint
import JacobianChallenge.Manifold.AbelJacobiPath

set_option linter.unusedSectionVars false

/-! # Midpoint splitting at the complex-period level

The integrate-level midpoint splitting
`affineSegmentPath_integrate_midpoint_split` lifts to the complex
chain period level:

```
complexChainPeriod (single (affineSegmentPath σ a c)) α
  = complexChainPeriod (single (affineSegmentPath σ a (midpoint2 a c))) α
    + complexChainPeriod (single (affineSegmentPath σ (midpoint2 a c) c)) α
```

This is the consolidation primitive for boundary edges in the
4-way midpoint subdivision telescoping.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **Midpoint splitting at the complex-period level.**

For any `σ : Smooth2Simplex 𝓘(ℝ, ℂ) X`, any `a c : Fin 2 → ℝ`, and any
`α : HolomorphicOneForm X`:

```
complexChainPeriod (single (affineSegmentPath σ a c)) α
  = complexChainPeriod (single (affineSegmentPath σ a (midpoint2 a c))) α
    + complexChainPeriod (single (affineSegmentPath σ (midpoint2 a c) c)) α
```

Proof: lift the integrate-level midpoint-split identity along the
real/imag decomposition of the complex period. -/
theorem Smooth2Simplex.affineSegmentPath_complexChainPeriod_midpoint_split
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X) (a c : Fin 2 → ℝ)
    (α : HolomorphicOneForm X) :
    complexChainPeriod (SmoothChain.single (Smooth2Simplex.affineSegmentPath σ a c)) α
      = complexChainPeriod
          (SmoothChain.single
            (Smooth2Simplex.affineSegmentPath σ a (Smooth2Simplex.midpoint2 a c))) α
        + complexChainPeriod
          (SmoothChain.single
            (Smooth2Simplex.affineSegmentPath σ (Smooth2Simplex.midpoint2 a c) c)) α := by
  unfold complexChainPeriod
  rw [SmoothChain.integrate_single, SmoothChain.integrate_single,
      SmoothChain.integrate_single, SmoothChain.integrate_single,
      SmoothChain.integrate_single, SmoothChain.integrate_single]
  rw [Smooth2Simplex.affineSegmentPath_integrate_midpoint_split σ a c (realComponent α),
      Smooth2Simplex.affineSegmentPath_integrate_midpoint_split σ a c (imagComponent α)]
  push_cast
  ring

end JacobianChallenge

end
