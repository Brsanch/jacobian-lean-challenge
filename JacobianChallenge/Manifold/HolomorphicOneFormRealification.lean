/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneForm
import Mathlib.Analysis.Complex.Basic

/-! # Pointwise real / imaginary split of a holomorphic 1-form

A holomorphic 1-form `ω : HolomorphicOneForm X` evaluates at a point `x : X`
to a continuous `ℂ`-linear map `ω x : ℂ →L[ℂ] ℂ` on the cotangent fibre.
Restricting scalars from `ℂ` to `ℝ` and post-composing with the real-linear
projections `Complex.reCLM, Complex.imCLM : ℂ →L[ℝ] ℝ` extracts two
real-valued continuous `ℝ`-linear functionals

```
ω.realPart x : ℂ →L[ℝ] ℝ
ω.imagPart x : ℂ →L[ℝ] ℝ
```

satisfying the pointwise decomposition

```
ω x v = (ω.realPart x v : ℂ) + Complex.I * (ω.imagPart x v : ℂ).
```

This is the pointwise content of the realification needed by the
period-pairing chip. Bundling `realPart` and `imagPart` into bona-fide
`SmoothOneForm`s of the underlying real manifold (i.e. against
`𝓘(ℝ, ℂ)` rather than `𝓘(ℂ)`) requires a model-with-corners realification
of the chart structure on `X`, which is a separate engineering step and is
deliberately *not* attempted here. The pointwise split established below is
already enough to feed the period-pairing's real / imaginary integral split.

## Main definitions

* `HolomorphicOneForm.realPart ω x : ℂ →L[ℝ] ℝ` — real part of `ω x`,
  taken over the realified cotangent fibre.
* `HolomorphicOneForm.imagPart ω x : ℂ →L[ℝ] ℝ` — imaginary part of `ω x`,
  taken over the realified cotangent fibre.

## Main theorem

* `HolomorphicOneForm.eval_eq` — the pointwise reconstruction
  `ω x v = ω.realPart x v + Complex.I * ω.imagPart x v`.

## Design notes

The cotangent fibre at `x` is `CotangentSpace 𝓘(ℂ) x = ℂ →L[ℂ] ℂ`. We use
`ContinuousLinearMap.restrictScalars ℝ` to reinterpret `ω x` as
`ℂ →L[ℝ] ℂ`, then post-compose with `Complex.reCLM` and `Complex.imCLM`.
The reconstruction `eval_eq` is a direct application of `Complex.re_add_im`
combined with `Complex.coe_algebraMap`-style coercions, all of which are
already in mathlib.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace HolomorphicOneForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The real part of `ω x`, viewed as a continuous `ℝ`-linear functional
`ℂ →L[ℝ] ℝ`. Concretely: `ω.realPart x v = (ω x v).re`. -/
def realPart (ω : HolomorphicOneForm X) (x : X) : ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp (((ω : ContMDiffSection (𝕜 := ℂ) (E := ℂ) (H := ℂ) (M := X)
    𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω (CotangentSpace 𝓘(ℂ) : X → Type _)) x).restrictScalars ℝ)

/-- The imaginary part of `ω x`, viewed as a continuous `ℝ`-linear
functional `ℂ →L[ℝ] ℝ`. Concretely: `ω.imagPart x v = (ω x v).im`. -/
def imagPart (ω : HolomorphicOneForm X) (x : X) : ℂ →L[ℝ] ℝ :=
  Complex.imCLM.comp (((ω : ContMDiffSection (𝕜 := ℂ) (E := ℂ) (H := ℂ) (M := X)
    𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω (CotangentSpace 𝓘(ℂ) : X → Type _)) x).restrictScalars ℝ)

@[simp]
theorem realPart_apply (ω : HolomorphicOneForm X) (x : X) (v : ℂ) :
    ω.realPart x v =
      ((ω : ContMDiffSection (𝕜 := ℂ) (E := ℂ) (H := ℂ) (M := X)
        𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω (CotangentSpace 𝓘(ℂ) : X → Type _)) x v).re := by
  simp [realPart, Complex.reCLM_apply]

@[simp]
theorem imagPart_apply (ω : HolomorphicOneForm X) (x : X) (v : ℂ) :
    ω.imagPart x v =
      ((ω : ContMDiffSection (𝕜 := ℂ) (E := ℂ) (H := ℂ) (M := X)
        𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω (CotangentSpace 𝓘(ℂ) : X → Type _)) x v).im := by
  simp [imagPart, Complex.imCLM_apply]

/-- Pointwise reconstruction: a holomorphic 1-form's value at `x` applied
to `v : ℂ` decomposes as `realPart x v + I * imagPart x v`. -/
theorem eval_eq (ω : HolomorphicOneForm X) (x : X) (v : ℂ) :
    ((ω : ContMDiffSection (𝕜 := ℂ) (E := ℂ) (H := ℂ) (M := X)
      𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω (CotangentSpace 𝓘(ℂ) : X → Type _)) x v) =
      (ω.realPart x v : ℂ) + Complex.I * (ω.imagPart x v : ℂ) := by
  set z : ℂ := ((ω : ContMDiffSection (𝕜 := ℂ) (E := ℂ) (H := ℂ) (M := X)
    𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω (CotangentSpace 𝓘(ℂ) : X → Type _)) x v) with hz
  have hre : (ω.realPart x v : ℂ) = (z.re : ℂ) := by
    simp [realPart_apply, hz]
  have him : (ω.imagPart x v : ℂ) = (z.im : ℂ) := by
    simp [imagPart_apply, hz]
  rw [hre, him]
  -- Goal: z = (z.re : ℂ) + I * (z.im : ℂ).
  -- Mathlib has `Complex.re_add_im : (z.re : ℂ) + z.im * I = z`; rearrange.
  have h := Complex.re_add_im z
  linear_combination -h

end HolomorphicOneForm

end
