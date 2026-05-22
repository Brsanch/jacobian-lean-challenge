/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Algebra.Module.LinearMap
import Mathlib.Analysis.Complex.Basic

set_option linter.unusedSectionVars false

/-! # Hand-rolled `HasFDerivAt`/`DifferentiableOn` bridge for `ℂ → ℂ`

Mathlib's `HasFDerivAt.restrictScalars` and friends require an
`IsScalarTower ℝ ℂ ℂ` typeclass instance that hits a known diamond
between `Complex.SMul.instSMulRealComplex` and `Algebra.id ℂ`-derived
SMul (documented in `HANDOFF_ITEM14.md`). This file ships a
**hand-rolled** bridge that bypasses the diamond by working at the
explicit `IsLittleO` level (which is base-field-agnostic).

The key observation: `HasFDerivAt f f' x` for `f : ℂ → ℂ`,
`f' : ℂ →L[ℂ] ℂ` is equivalent to the asymptotic
`(fun x' ↦ f x' - f x - f' (x' - x)) =o[𝓝 x] (fun x' ↦ x' - x)`
(via `HasFDerivAt.isLittleO` / `HasFDerivAt.of_isLittleO`). This
asymptotic is base-field-agnostic — the `IsLittleO` predicate
references topological structure, not the scalar field.

`ContinuousLinearMap.restrictScalars ℝ` for `f' : ℂ →L[ℂ] ℂ` requires
only `LinearMap.CompatibleSMul ℂ ℂ ℝ ℂ` (NOT `IsScalarTower`), which
synthesises cleanly. The composite gives the ℝ-side `HasFDerivAt`.

## What this file ships

* `HasFDerivAt.restrictScalarsComplex` —
  `HasFDerivAt f f' x → HasFDerivAt f (f'.restrictScalars ℝ) x`
  for `f : ℂ → ℂ`, `f' : ℂ →L[ℂ] ℂ`.
* `HasFDerivWithinAt.restrictScalarsComplex` — within-set version.
* `DifferentiableAt.restrictScalarsComplex` — exists-version.
* `DifferentiableWithinAt.restrictScalarsComplex` — within-set
  exists-version.
* `DifferentiableOn.restrictScalarsComplex` — set version.
* `Differentiable.restrictScalarsComplex` — total version.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Topology

namespace HasFDerivAt

/-- **ℂ → ℂ scalar-restriction of `HasFDerivAt`.** Bypasses the
mathlib `IsScalarTower ℝ ℂ ℂ` diamond by working at the
base-field-agnostic `IsLittleO` level. -/
theorem restrictScalarsComplex {f : ℂ → ℂ} {f' : ℂ →L[ℂ] ℂ} {x : ℂ}
    (h : HasFDerivAt f f' x) :
    HasFDerivAt f (f'.restrictScalars ℝ) x := by
  have h_io : (fun x' => f x' - f x - f' (x' - x)) =o[𝓝 x] (fun x' => x' - x) :=
    h.isLittleO
  refine HasFDerivAt.of_isLittleO ?_
  show (fun x' => f x' - f x - (f'.restrictScalars ℝ) (x' - x)) =o[𝓝 x] (fun x' => x' - x)
  convert h_io using 2

end HasFDerivAt

namespace HasFDerivWithinAt

/-- **ℂ → ℂ scalar-restriction of `HasFDerivWithinAt`** — within-set
analog of `HasFDerivAt.restrictScalarsComplex`. -/
theorem restrictScalarsComplex {f : ℂ → ℂ} {f' : ℂ →L[ℂ] ℂ} {s : Set ℂ}
    {x : ℂ} (h : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt f (f'.restrictScalars ℝ) s x := by
  have h_io : (fun x' => f x' - f x - f' (x' - x)) =o[𝓝[s] x] (fun x' => x' - x) :=
    h.isLittleO
  refine HasFDerivWithinAt.of_isLittleO ?_
  show (fun x' => f x' - f x - (f'.restrictScalars ℝ) (x' - x)) =o[𝓝[s] x] (fun x' => x' - x)
  convert h_io using 2

end HasFDerivWithinAt

namespace DifferentiableAt

/-- **ℂ → ℂ scalar-restriction of `DifferentiableAt`.** -/
theorem restrictScalarsComplex {f : ℂ → ℂ} {x : ℂ} (h : DifferentiableAt ℂ f x) :
    DifferentiableAt ℝ f x :=
  h.hasFDerivAt.restrictScalarsComplex.differentiableAt

end DifferentiableAt

namespace DifferentiableWithinAt

/-- **ℂ → ℂ scalar-restriction of `DifferentiableWithinAt`.** -/
theorem restrictScalarsComplex {f : ℂ → ℂ} {s : Set ℂ} {x : ℂ}
    (h : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℝ f s x :=
  h.hasFDerivWithinAt.restrictScalarsComplex.differentiableWithinAt

end DifferentiableWithinAt

namespace DifferentiableOn

/-- **ℂ → ℂ scalar-restriction of `DifferentiableOn`.** -/
theorem restrictScalarsComplex {f : ℂ → ℂ} {s : Set ℂ}
    (h : DifferentiableOn ℂ f s) : DifferentiableOn ℝ f s :=
  fun x hx => (h x hx).restrictScalarsComplex

end DifferentiableOn

namespace Differentiable

/-- **ℂ → ℂ scalar-restriction of `Differentiable`.** -/
theorem restrictScalarsComplex {f : ℂ → ℂ} (h : Differentiable ℂ f) :
    Differentiable ℝ f :=
  fun x => (h x).restrictScalarsComplex

end Differentiable

end
