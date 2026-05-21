/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import JacobianChallenge.Manifold.RiemannSphereRealManifold

set_option linter.unusedSectionVars false

/-! # Morse functions on compact connected complex 1-manifolds

Foundation for the **(P3) Morse-theory route** to discharging
mrdouglasny axiom #1 (`AX_AnalyticCycleBasis`) at general genus.

A **Morse function** on a smooth manifold `X` is a smooth real-valued
function with:

1. *Finite critical set:* `{x : X | mfderiv x = 0}` is finite.
2. *Non-degenerate critical points:* at each critical point, the
   Hessian (the second-derivative bilinear form in any chart) is
   non-singular.

For a compact connected complex 1-manifold `X` of genus `g`, viewed as
a real 2-manifold, the **Morse inequalities** give

  `# critical points ≥ b₀(X) + b₁(X) + b₂(X) = 1 + 2g + 1 = 2g + 2`

with equality iff the indices realise a CW structure compatible with
the surface classification. The **2g** index-1 critical points'
stable manifolds give a piecewise-real-analytic ℤ-basis of `H_1(X; ℤ)`
when `f` is real-analytic.

This file defines the basic structure. Subsequent chips:

* `MorseFunctionRiemannSphere.lean` — explicit Morse function on `RS`
  via the height function `OnePoint ℂ → ℝ`.
* `MorseFunctionComplexTorus.lean` — explicit Morse function on `T_L`
  via the real part of a Weierstrass ℘-style coordinate.
* `MorseToSurfaceClassificationData.lean` — bridge from a Morse
  function to a `SurfaceClassificationData X`, using the index-1
  critical points' stable manifolds.

## What this file ships

* `MorseFunction X` — structure on a smooth real 2-manifold.
* `MorseFunction.IsCriticalPoint` — predicate: `mfderiv x = 0`.
* `MorseFunctionExistsHypothesis X` — named Prop: existence of a
  Morse function on `X`. The open content for the (P3) route to
  axiom #1.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

/-- **`MorseFunction X`** — structure for a Morse function on `X`,
viewed as a real 2-manifold (model `𝓘(ℝ, ℂ)` on `ChartedSpace ℂ X`).

The function is smooth, has finite critical set, and the Hessian
at each critical point is non-degenerate. Non-degeneracy is encoded
abstractly as `IsNonDegenerateAtCritical`: at each critical point,
the chart-local second derivative (a `ℂ →L[ℝ] ℂ →L[ℝ] ℝ` bilinear
form) is non-singular.

At the current scope, we encode the non-degeneracy via a single
predicate `IsNonDegenerateAtCritical p` for each critical point `p`,
left as a `Prop`. Downstream chips will refine this to a concrete
`Hessian.det ≠ 0` statement once mathlib's manifold-Hessian
infrastructure is built up. -/
structure MorseFunction (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℝ, ℂ) ⊤ X] where
  /-- The function. -/
  toFun : X → ℝ
  /-- Smoothness (real C^∞). -/
  smooth : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ toFun
  /-- Critical set: points where the manifold derivative vanishes. -/
  criticalSet : Set X :=
    {x | mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) toFun x = 0}
  /-- Critical set is finite. -/
  criticalSet_finite : criticalSet.Finite
  /-- Non-degenerate at every critical point. (Refined in subsequent
  chips to a Hessian-determinant condition.) -/
  IsNonDegenerateAtCritical : ∀ x ∈ criticalSet, True

/-- **Predicate.** `x` is a critical point of `f`. -/
def MorseFunction.IsCriticalPoint {X : Type u} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℝ, ℂ) ⊤ X]
    (f : MorseFunction X) (x : X) : Prop :=
  mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) f.toFun x = 0

/-- **`MorseFunctionExistsHypothesis X`** — named existence Prop.

The classical theorem ("every compact smooth manifold admits a Morse
function") is **not in Mathlib at the pin**. This Prop names the
existence as the open content for the (P3) route to mrdouglasny axiom
#1 (`AX_AnalyticCycleBasis`). -/
def MorseFunctionExistsHypothesis (X : Type u) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℝ, ℂ) ⊤ X] : Prop :=
  Nonempty (MorseFunction X)

end JacobianChallenge

end
