/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PrimitiveOnSmoothPathConnected
import JacobianChallenge.Manifold.SmoothPathIntegrateConst

set_option linter.unusedSectionVars false

/-! # Constant-loop period vanishing (unconditional)

The constant smooth loop `SmoothPath.const 𝓘(ℝ, ℂ) X x₀` has zero
complex period against any holomorphic 1-form: its velocity is zero,
so the integrand vanishes pointwise, hence the integral.

This is the simplest case of `LoopPeriodVanishes`. The general case
requires Stokes on a 2-cell.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **Constant-loop period vanishes.** The complex period of any
holomorphic 1-form along the constant smooth loop at `x₀` is zero. -/
@[simp] theorem complexChainPeriod_const_loop (x₀ : X)
    (om : HolomorphicOneForm X) :
    complexChainPeriod (SmoothChain.single (SmoothPath.const 𝓘(ℝ, ℂ) X x₀)) om
      = 0 := by
  unfold complexChainPeriod
  rw [SmoothChain.integrate_single, SmoothChain.integrate_single,
    SmoothPath.integrate_const, SmoothPath.integrate_const]
  push_cast
  ring

end JacobianChallenge

end
