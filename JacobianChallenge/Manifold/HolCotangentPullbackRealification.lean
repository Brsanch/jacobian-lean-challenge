/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicCotangentPullbackAt
import JacobianChallenge.Manifold.CotangentPullbackAt
import JacobianChallenge.Manifold.HolomorphicOneFormRealComponent
import JacobianChallenge.Manifold.MFDerivComplexToRealApply

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Realification compatibility for holomorphic cotangent pullback

For a ℂ-differentiable map `g : Y → X` between complex 1-manifolds at
a point `y : Y`, and a holomorphic 1-form `α : HolomorphicOneForm X`,
the **real part** of the holomorphic pullback agrees, at the
function-application level, with the realified pullback of the
**real component** of `α`:

  `(realPartCLM (holCotangentPullbackAt g y α)) w
     = (cotangentPullbackAt 𝓘(ℝ,ℂ) g y (realComponent α)) w`

for every tangent vector `w : ℂ`. The companion identity uses
`imagPartCLM` / `imagComponent`.

The substantive content is the mfderiv application identity from
`MFDerivComplexToRealApply.lean`:
`(mfderiv 𝓘(ℝ, ℂ) g y) w = (mfderiv 𝓘(ℂ, ℂ) g y) w` (as elements of `ℂ`).
The rest is unfolding the various `.comp` / `.toFun` / `realPartCLM`
operations at the function-application level.

This is the **per-summand** form. The full trace identity sums over the
fiber and is proven in a companion chip.

## Why the apply-level statement

The typed statement
`realPartCLM (holCotangentPullbackAt g y α) = cotangentPullbackAt ...`
trips `LinearMap.CompatibleSMul` / `IsScalarTower` synth failures
because `CotangentSpace 𝓘(ℂ, ℂ) y` has only `Module ℂ` (and not the
`Module ℝ` needed for `restrictScalars`, since `TangentSpace` is not
reducible). At the apply-level the source `TangentSpace _ y` only
appears as the function's argument, sidestepping the synth issue.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Manifold Topology ContDiff

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-- **Apply-level value of `realPartCLM` on a `ℂ →L[ℂ] ℂ` map.** For
`φ : ℂ →L[ℂ] ℂ` and `w : ℂ`, `(realPartCLM φ) w = Complex.re (φ w)`. -/
private theorem realPartCLM_apply_value (φ : ℂ →L[ℂ] ℂ) (w : ℂ) :
    (realPartCLM φ) w = Complex.re (φ w) := by
  rw [realPartCLM_apply]
  rfl

/-- **Apply-level value of `imagPartCLM` on a `ℂ →L[ℂ] ℂ` map.** -/
private theorem imagPartCLM_apply_value (φ : ℂ →L[ℂ] ℂ) (w : ℂ) :
    (imagPartCLM φ) w = Complex.im (φ w) := by
  rw [imagPartCLM_apply]
  rfl

/-- **Per-summand realification compatibility (apply level).**

For ℂ-differentiable `g : Y → X` at `y`, every tangent vector `w : ℂ`,
and holomorphic 1-form `α : HolomorphicOneForm X`:

  `(realPartCLM (holCotangentPullbackAt g y α)) w
      = (cotangentPullbackAt 𝓘(ℝ,ℂ) g y (realComponent α)) w`

Both sides are values in `ℝ`. Proof reduces to the mfderiv
application identity `mfderiv_complex_to_real_apply`. -/
theorem realPartCLM_holCotangentPullbackAt_apply
    {g : Y → X} {y : Y}
    (hg : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g y)
    (α : HolomorphicOneForm X) (w : ℂ) :
    (realPartCLM (holCotangentPullbackAt g y α)) w
      = Complex.re ((α.eval (g y)) ((mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) g y) w)) := by
  rw [holCotangentPullbackAt_apply, realPartCLM_apply_value]
  -- LHS: Complex.re ( (α.toFun (g y) .comp mfderiv 𝓘(ℂ,ℂ) g y) w )
  --    = Complex.re ( (α.eval (g y)) (mfderiv 𝓘(ℂ,ℂ) g y w) )   by `rfl` for `.comp` apply
  -- Goal: ... = Complex.re ( (α.eval (g y)) (mfderiv 𝓘(ℝ,ℂ) g y w) )
  -- Reduce to mfderiv_complex_to_real_apply hg w.
  show Complex.re ((α.eval (g y)) ((mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) g y) w))
    = Complex.re ((α.eval (g y)) ((mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) g y) w))
  congr 1
  congr 1
  exact (mfderiv_complex_to_real_apply hg w).symm

/-- **Companion: imagPartCLM identity (apply level).** -/
theorem imagPartCLM_holCotangentPullbackAt_apply
    {g : Y → X} {y : Y}
    (hg : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g y)
    (α : HolomorphicOneForm X) (w : ℂ) :
    (imagPartCLM (holCotangentPullbackAt g y α)) w
      = Complex.im ((α.eval (g y)) ((mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) g y) w)) := by
  rw [holCotangentPullbackAt_apply, imagPartCLM_apply_value]
  show Complex.im ((α.eval (g y)) ((mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) g y) w))
    = Complex.im ((α.eval (g y)) ((mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) g y) w))
  congr 1
  congr 1
  exact (mfderiv_complex_to_real_apply hg w).symm

end JacobianChallenge

end
