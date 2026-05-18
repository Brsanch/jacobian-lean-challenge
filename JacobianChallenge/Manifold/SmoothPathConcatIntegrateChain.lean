/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathIntegrateConcat
import JacobianChallenge.Manifold.SmoothPathIntegral

set_option linter.unusedSectionVars false

/-! # `single (γ.concat δ)` integrates equal to `single γ + single δ`

Chain-level analogue of `SmoothPath.integrate_concat`: for any
compatible smooth paths `γ : SmoothPath I X` (with `γ.tgt = δ.src`)
and any smooth 1-form `om`,

```
SmoothChain.integrate (SmoothChain.single (γ.concat δ h)) om
  = SmoothChain.integrate (SmoothChain.single γ + SmoothChain.single δ) om.
```

In other words, the chain `single (γ.concat δ h) - single γ - single δ`
integrates to zero against ANY 1-form (not just closed ones), without
requiring a Smooth2Chain witness for stokesBoundary membership.

## Significance

This is the "integration-side" version of "concatenation = addition in
homology": at the level of pairings against 1-forms, concat-of-paths
and sum-of-singles are indistinguishable. The stronger statement that
the chain difference is in `stokesBoundaries` would require the smooth
2-simplex-bounding construction (a heavier classical-content chip),
but the integration-side identity is direct.

## What this file ships

* `integrate_single_concat_eq_single_add_single` — the chain-level
  concat-additive identity.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-- **Integration-side concat additivity.** For compatible smooth
paths `γ, δ` with `γ.tgt = δ.src` and any 1-form `om`,
`integrate (single (γ.concat δ h)) om = integrate (single γ + single δ) om`. -/
theorem integrate_single_concat_eq_single_add_single
    (γ δ : SmoothPath I X) (h : γ.tgt = δ.src)
    (om : SmoothOneForm I X) :
    SmoothChain.integrate (SmoothChain.single (γ.concat δ h)) om
      = SmoothChain.integrate
          (SmoothChain.single γ + SmoothChain.single δ) om := by
  rw [SmoothChain.integrate_add, SmoothChain.integrate_single,
      SmoothChain.integrate_single, SmoothChain.integrate_single,
      SmoothPath.integrate_concat]

end JacobianChallenge

end
