/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneForm
import Mathlib.Analysis.Complex.Basic

/-! # Pointwise real / imaginary split of a holomorphic 1-form

A holomorphic 1-form `om : HolomorphicOneForm X` evaluates at a point
`x : X` to a continuous `ℂ`-linear map on the cotangent fibre of type
`ℂ →L[ℂ] ℂ`. Restricting scalars from `ℂ` to `ℝ` and post-composing with
the real-linear projections `Complex.reCLM, Complex.imCLM : ℂ →L[ℝ] ℝ`
extracts two real-valued continuous `ℝ`-linear functionals

```
om.realPart x : ℂ →L[ℝ] ℝ
om.imagPart x : ℂ →L[ℝ] ℝ
```

satisfying the pointwise decomposition

```
om.eval x v = (om.realPart x v : ℂ) + Complex.I * (om.imagPart x v : ℂ).
```

This is the pointwise content of the realification needed by the
period-pairing chip. Bundling `realPart` and `imagPart` into bona-fide
`SmoothOneForm`s of the underlying real manifold (i.e. against
`𝓘(ℝ, ℂ)` rather than `𝓘(ℂ)`) requires a model-with-corners realification
of the chart structure on `X`, which is a separate engineering step and is
deliberately *not* attempted here. The pointwise split established below is
already enough to feed the period-pairing's real / imaginary integral split.

## Main definitions

* `HolomorphicOneForm.eval om x : ℂ →L[ℂ] ℂ` — pointwise value of `om`
  at `x`, exposing the `DFunLike` coercion of `ContMDiffSection` under a
  short, type-ascription-free name.
* `HolomorphicOneForm.realPart om x : ℂ →L[ℝ] ℝ` — real part of
  `om.eval x`, taken over the realified cotangent fibre.
* `HolomorphicOneForm.imagPart om x : ℂ →L[ℝ] ℝ` — imaginary part of
  `om.eval x`, taken over the realified cotangent fibre.

## Main theorem

* `HolomorphicOneForm.eval_eq` — the pointwise reconstruction
  `om.eval x v = om.realPart x v + Complex.I * om.imagPart x v`.

## Design notes

The cotangent fibre at `x` is `CotangentSpace 𝓘(ℂ) x = ℂ →L[ℂ] ℂ`. We use
`ContinuousLinearMap.restrictScalars ℝ` to reinterpret the value
`om.eval x : ℂ →L[ℂ] ℂ` as `ℂ →L[ℝ] ℂ`, then post-compose with
`Complex.reCLM` and `Complex.imCLM`. The reconstruction `eval_eq` is a
direct application of `Complex.re_add_im`.

We deliberately use `om` rather than the Greek letter as the binder for
the holomorphic 1-form; Lean 4.30 reserves the Greek omega as a
tactic-block token and rejects it as a `def`/`theorem` binder.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace HolomorphicOneForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Evaluation of a holomorphic 1-form at a point, with no detour through
the underlying `ContMDiffSection` type ascription. The fibre at `x` is
the complex cotangent fibre `ℂ →L[ℂ] ℂ` (i.e. `CotangentSpace 𝓘(ℂ) x`).

Concretely this is just the `DFunLike` coercion of the underlying
`ContMDiffSection`, packaged as a named function so that downstream
lemmas can talk about `om.eval x` without restating the full section
signature each time. -/
def eval (om : HolomorphicOneForm X) (x : X) : ℂ →L[ℂ] ℂ :=
  (om :
    ContMDiffSection (𝕜 := ℂ) (E := ℂ) (H := ℂ) (M := X)
      𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω (CotangentSpace 𝓘(ℂ) : X → Type _))
    x

/-- The real part of `om.eval x`, viewed as a continuous `ℝ`-linear
functional `ℂ →L[ℝ] ℝ`. Concretely: `om.realPart x v = (om.eval x v).re`. -/
def realPart (om : HolomorphicOneForm X) (x : X) : ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp ((om.eval x).restrictScalars ℝ)

/-- The imaginary part of `om.eval x`, viewed as a continuous `ℝ`-linear
functional `ℂ →L[ℝ] ℝ`. Concretely: `om.imagPart x v = (om.eval x v).im`. -/
def imagPart (om : HolomorphicOneForm X) (x : X) : ℂ →L[ℝ] ℝ :=
  Complex.imCLM.comp ((om.eval x).restrictScalars ℝ)

@[simp]
theorem realPart_apply (om : HolomorphicOneForm X) (x : X) (v : ℂ) :
    om.realPart x v = (om.eval x v).re := by
  simp [realPart, Complex.reCLM_apply]

@[simp]
theorem imagPart_apply (om : HolomorphicOneForm X) (x : X) (v : ℂ) :
    om.imagPart x v = (om.eval x v).im := by
  simp [imagPart, Complex.imCLM_apply]

/-- Pointwise reconstruction: a holomorphic 1-form's value at `x` applied
to `v : ℂ` decomposes as `realPart x v + I * imagPart x v`. -/
theorem eval_eq (om : HolomorphicOneForm X) (x : X) (v : ℂ) :
    om.eval x v =
      (om.realPart x v : ℂ) + Complex.I * (om.imagPart x v : ℂ) := by
  -- Reduce both sides to the underlying complex value `om.eval x v` and apply
  -- the `Complex.re_add_im` identity.
  have hre : (om.realPart x v : ℂ) = ((om.eval x v).re : ℂ) := by
    simp [realPart_apply]
  have him : (om.imagPart x v : ℂ) = ((om.eval x v).im : ℂ) := by
    simp [imagPart_apply]
  rw [hre, him]
  -- Goal: `om.eval x v = ((om.eval x v).re : ℂ) + I * ((om.eval x v).im : ℂ)`.
  have h := Complex.re_add_im (om.eval x v)
  linear_combination -h

end HolomorphicOneForm

end
