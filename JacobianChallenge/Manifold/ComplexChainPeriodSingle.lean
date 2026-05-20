/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiPath
import JacobianChallenge.Manifold.SmoothPathIntegral

set_option linter.unusedSectionVars false

/-! # Single-path `complexChainPeriod` identity

`complexChainPeriod c om` is defined as
`(SmoothChain.integrate c (realComponent om) + I * SmoothChain.integrate c (imagComponent om))`,
where the integrates return `ℝ` and are cast to `ℂ`. For
`c = SmoothChain.single γ`, `SmoothChain.integrate_single` simplifies
`SmoothChain.integrate (single γ) = γ.integrate`, so the chain
period reduces to a per-path expression.

## What ships

* `complexChainPeriod_single` — the explicit single-path identity.

Useful for downstream work expanding the period-vector sum
decomposition (`LevelSetChainPeriodVectorSum.lean`) into per-path
real integrals.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Topology Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Single-path complex chain period.**

For a smooth path `γ` and a holomorphic 1-form `om`:
`complexChainPeriod (single γ) om =
   γ.integrate (realComponent om) + I * γ.integrate (imagComponent om)`
(with the real integrals cast to `ℂ`). -/
@[simp] theorem complexChainPeriod_single
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) (om : HolomorphicOneForm X) :
    complexChainPeriod (SmoothChain.single γ) om
      = ((γ.integrate (realComponent om) : ℝ) : ℂ)
        + Complex.I * ((γ.integrate (imagComponent om) : ℝ) : ℂ) := by
  unfold complexChainPeriod
  rw [SmoothChain.integrate_single, SmoothChain.integrate_single]

end JacobianChallenge

end
