/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import JacobianChallenge.Manifold.MorseFunction

set_option linter.unusedSectionVars false

/-! # Hessian and Morse non-degeneracy on complex 1-manifolds (Phase D-1)

The first concrete chip in Phase D (smooth Hurewicz at general genus)
of the item-5 closure plan. Upgrades the placeholder `MorseFunction X`
(`Manifold/MorseFunction.lean` line 90, `IsNonDegenerateAtCritical = True`)
with a *real* chart-local Hessian non-degeneracy condition.

## Strategy

For a smooth real-valued `f : X → ℝ` on a chart-`ℂ` real 2-manifold,
the **chart-local Hessian** at `x : X` is the second iterated Fréchet
derivative of the chart pullback `f ∘ (chartAt ℂ x).symm : ℂ → ℝ`
evaluated at `(chartAt ℂ x) x : ℂ`:

  `chartLocalHessianAt f x : (Fin 2 → ℂ) → ℝ`
   = `iteratedFDeriv ℝ 2 (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)`

Non-degeneracy is the standard bilinear-form notion: the map
`v ↦ (w ↦ H f x ![v, w])` from `ℂ` to `ℂ →L[ℝ] ℝ` is injective.

At a **critical point**, the Hessian is a chart-invariant tensor (well-
known classical fact); we do not prove chart-invariance here, leaving
that for a follow-up chip if needed.

## What this file ships

* `chartLocalHessianAt f x` — the second iterated Fréchet derivative of
  the chart pullback.
* `IsHessianNonDegenerateAt f x : Prop` — non-degeneracy as a bilinear
  form on `ℂ`.
* `IsMorseFunction f : Prop` — bundle of (smoothness + finite critical
  set + Hessian non-degeneracy at every critical point). This is the
  *real* Morse predicate Phase D will use, complementing the existing
  placeholder `MorseFunction X` structure.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℝ, ℂ) ⊤ X]

/-- **Chart-local Hessian at a point.** The second iterated Fréchet
derivative of `f ∘ (chartAt ℂ x).symm : ℂ → ℝ` evaluated at the chart
image `(chartAt ℂ x) x ∈ ℂ`.

This is a `ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℂ) ℝ` —
a continuous bilinear form on `ℂ` (viewed as a real 2-d vector space).
-/
noncomputable def chartLocalHessianAt (f : X → ℝ) (x : X) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℂ) ℝ :=
  iteratedFDeriv ℝ 2 (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)

/-- **Chart-local Hessian non-degeneracy at a point.** The bilinear
form `chartLocalHessianAt f x` is non-degenerate as a bilinear form on
`ℂ` (viewed as a real 2-d vector space): for every `v : ℂ`, if
`H(v, w) = 0` for all `w`, then `v = 0`.

This is the standard non-degeneracy condition for Morse critical
points. Defined in the chart `chartAt ℂ x` — at a critical point the
Hessian is chart-invariant (we do not formalise that here). -/
def IsHessianNonDegenerateAt (f : X → ℝ) (x : X) : Prop :=
  ∀ v : ℂ, (∀ w : ℂ, chartLocalHessianAt f x ![v, w] = 0) → v = 0

/-- **`IsMorseFunction f`** — the real Morse predicate: `f` is smooth,
has a finite critical set, and the Hessian is non-degenerate at every
critical point.

The companion to the existing placeholder `MorseFunction X` structure
(`Manifold/MorseFunction.lean` line 77), with the non-degeneracy
condition upgraded from `True` to a chart-local Hessian condition.

Phase D uses this predicate as the input to the CW decomposition: a
Morse function in this sense yields a CW structure on `X` with `# {x :
criticalSet | Morse-index(x) = k}` cells of dimension `k`. -/
structure IsMorseFunction (f : X → ℝ) : Prop where
  /-- Smoothness on the real 2-manifold. -/
  smooth : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ f
  /-- Critical set is finite. -/
  criticalSet_finite : {x : X | mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) f x = 0}.Finite
  /-- At every critical point, the chart-local Hessian is
  non-degenerate. -/
  hessian_nondeg :
    ∀ x : X, mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) f x = 0 → IsHessianNonDegenerateAt f x

/-- **Forgetful conversion.** Every `IsMorseFunction f` gives a
placeholder `MorseFunction X` structure (whose `IsNonDegenerateAtCritical`
is trivially `True`). -/
noncomputable def IsMorseFunction.toMorseFunction
    {f : X → ℝ} (h : IsMorseFunction f) : MorseFunction X where
  toFun := f
  smooth := h.smooth
  criticalSet_finite := h.criticalSet_finite
  IsNonDegenerateAtCritical := fun _ _ => trivial

/-- **`IsMorseFunctionExistsHypothesis X`** — the real Morse-function
existence Prop, stronger than the placeholder
`MorseFunctionExistsHypothesis X` (which only requires the placeholder
structure). This is the open content for Phase D's Morse-on-compact
existence theorem. -/
def IsMorseFunctionExistsHypothesis (X : Type u) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℝ, ℂ) ⊤ X] : Prop :=
  ∃ f : X → ℝ, IsMorseFunction f

/-- **`IsMorseFunctionExistsHypothesis` implies the placeholder
`MorseFunctionExistsHypothesis`.** -/
theorem morseFunctionExistsHypothesis_of_isMorseFunctionExistsHypothesis
    (h : IsMorseFunctionExistsHypothesis X) :
    MorseFunctionExistsHypothesis X := by
  obtain ⟨f, hf⟩ := h
  exact ⟨hf.toMorseFunction⟩

end JacobianChallenge

end
